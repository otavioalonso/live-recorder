#!/usr/bin/env python3
"""
streamrec - record a live stream from (almost) any web page, and keep going when it breaks.

Recording methods
  grab   : open the page in a headless browser, sniff the HLS/DASH playlist the player
           loads, and let ffmpeg copy it (original quality, very low CPU).
  screen : play the page in a real browser on a virtual display (Xvfb) and record the
           screen + audio with ffmpeg. Works for anything that plays (not DRM). Linux only.
  auto   : try grab; switch to screen if no playlist is found after --grab-tries attempts.

Reliability
  * Output is written as numbered parts: runNNN_PPP.ts. A crash/restart only starts a new
    run; parts already written are never touched. .ts stays playable if cut off.
  * grab: ffmpeg exit or no new data for --stall seconds -> re-open the page, get a fresh
    playlist URL (tokens expire) and start the next run. Repeats until --end.
  * screen: video currentTime not advancing for --stall seconds -> reload the page.
    ffmpeg itself is restarted if it dies.
  * Optional: upload finished parts as you go with rclone (--rclone remote:path).

Subcommands
  record URL ...   do the recording (see --help)
  probe  URL       test: report playlists found and whether a video plays
  login  URL       open a visible browser with the recorder's profile (log in, accept cookies)
  join   DIR       join all parts into one file
  schedule FILE    run every recording listed in a TOML schedule file (for a systemd service)
  list / add / remove / page   view and edit the schedule file from the command line
  web              phone page for the schedule (Tailscale/LAN only); or `schedule --web`
"""
import argparse
import datetime as dt
import fcntl
import html
import ipaddress
import json
import logging
import os
import re
import shutil
import signal
import subprocess
import sys
import threading
import time
from contextlib import contextmanager
from pathlib import Path
from urllib.parse import parse_qs, quote, urlparse

log = logging.getLogger("streamrec")
STOP = threading.Event()
KICK = threading.Event()  # wakes the scheduler loop early (schedule edited from the web page)
STATE_DIR = Path("~/.streamrec").expanduser()
STATUS = STATE_DIR / "status.json"
DEFAULT_SCHEDULE = "~/.config/streamrec/schedule.toml"
DEFAULT_DIR = "~/recordings"

PLAYLIST_URL = re.compile(r"\.(m3u8|mpd)(\?|#|$)", re.I)
PLAYLIST_CT = ("mpegurl", "dash+xml")
FWD_HEADERS = ("referer", "origin", "cookie", "authorization")

JS_VIDEOS = """() => Array.from(document.querySelectorAll('video')).map(v => {
  const r = v.getBoundingClientRect();
  return {area: r.width * r.height, t: v.currentTime, paused: v.paused, ready: v.readyState};
})"""

JS_FILL = """(el) => {
  const s = el.style, imp = 'important';
  s.setProperty('position', 'fixed', imp); s.setProperty('inset', '0', imp);
  s.setProperty('left', '0', imp); s.setProperty('top', '0', imp);
  s.setProperty('width', '100vw', imp); s.setProperty('height', '100vh', imp);
  s.setProperty('max-width', 'none', imp); s.setProperty('max-height', 'none', imp);
  s.setProperty('z-index', '2147483647', imp); s.setProperty('background', 'black', imp);
  s.setProperty('border', '0', imp); s.setProperty('margin', '0', imp);
  if (el.tagName === 'VIDEO') s.setProperty('object-fit', 'contain', imp);
  document.documentElement.style.setProperty('overflow', 'hidden', imp);
  document.documentElement.style.setProperty('cursor', 'none', imp);
}"""


# ----------------------------------------------------------------------------- helpers
def now():
    return dt.datetime.now().astimezone()


def parse_when(s, base=None):
    """'now', 'HH:MM' (next occurrence after base), or ISO 'YYYY-MM-DDTHH:MM[+09:00]'."""
    base = base or now()
    if s in (None, "now"):
        return now()
    m = re.fullmatch(r"(\d{1,2}):(\d{2})", s)
    if m:
        t = base.replace(hour=int(m[1]), minute=int(m[2]), second=0, microsecond=0)
        if t <= base - dt.timedelta(minutes=1):
            t += dt.timedelta(days=1)
        return t
    t = dt.datetime.fromisoformat(s)
    return t if t.tzinfo else t.astimezone()


def parse_duration(s):
    m = re.fullmatch(r"(?:(\d+)h)?(?:(\d+)m)?(?:(\d+)s)?", s.strip())
    if not m or not any(m.groups()):
        raise argparse.ArgumentTypeError(f"bad duration {s!r} (use e.g. 3h, 90m, 2h30m)")
    h, mi, se = (int(x or 0) for x in m.groups())
    return dt.timedelta(hours=h, minutes=mi, seconds=se)


def parse_part(s):
    """Part length: bare number = minutes (old style), or a duration like 30s, 2m, 1h."""
    secs = int(s) * 60 if s.strip().isdigit() else int(parse_duration(s).total_seconds())
    if secs < 10:
        raise argparse.ArgumentTypeError("part length must be at least 10s")
    return secs


def same_site(a, b):
    ha, hb = (urlparse(u).hostname or "" for u in (a, b))
    return ha.split(".")[-2:] == hb.split(".")[-2:]


def next_run(out):
    nums = [int(m[1]) for p in out.glob("run*_*.ts") if (m := re.match(r"run(\d+)_", p.name))]
    return max(nums, default=0) + 1


def newest_mtime(out, prefix):
    return max((p.stat().st_mtime for p in out.glob(f"{prefix}_*.ts")), default=0.0)


def start_ffmpeg(cmd, out):
    log.info("starting ffmpeg -> %s", cmd[-1])
    err = open(out / "ffmpeg.log", "ab")
    return subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=err)


def stop_ffmpeg(p):
    if p and p.poll() is None:
        p.send_signal(signal.SIGINT)  # lets ffmpeg close the current part cleanly
        try:
            p.wait(15)
        except subprocess.TimeoutExpired:
            p.kill()
            p.wait()


# ----------------------------------------------------------------------------- browser
class Browser:
    """Chromium that closes pop-up ad tabs and can find, start and maximise the video."""

    def __init__(self, a, display=None, sniff=False):
        from playwright.sync_api import sync_playwright

        self.a, self.page, self.found, self.sniff = a, None, [], sniff
        self._pw = sync_playwright().start()
        args = ["--autoplay-policy=no-user-gesture-required", "--no-first-run",
                "--disable-notifications", "--disable-blink-features=AutomationControlled"]
        kw = {"headless": display is None and not a.show, "args": args}
        if display:
            w, h = a.size.split("x")
            args += [f"--window-size={w},{h}", "--window-position=0,0", "--kiosk"]
            kw["env"] = {**os.environ, "DISPLAY": display, "PULSE_SINK": a.sink}
            kw["no_viewport"] = True
        else:
            kw["viewport"] = {"width": 1280, "height": 720}
            if not a.show:
                args.append("--mute-audio")
        if a.extension:  # e.g. an unpacked uBlock Origin Lite
            ext = str(Path(a.extension).expanduser().resolve())
            args += [f"--disable-extensions-except={ext}", f"--load-extension={ext}"]
            kw["channel"] = "chromium"  # new headless mode, which supports extensions
        profile = Path(a.profile).expanduser()
        profile.mkdir(parents=True, exist_ok=True)
        self.ctx = self._pw.chromium.launch_persistent_context(str(profile), **kw)
        self.ctx.on("page", self._on_new_page)
        if sniff:
            self.ctx.on("response", self._on_response)
        self.page = self.ctx.pages[0] if self.ctx.pages else self.ctx.new_page()
        self.home = None
        self.page.route("**/*", self._guard)

    def _guard(self, route):
        """Refuse ad redirects of the main tab to another site (they'd repeat on every reload)."""
        r = route.request
        try:
            if (self.home and r.is_navigation_request() and r.frame == self.page.main_frame
                    and not same_site(r.url, self.home)):
                log.info("blocked redirect to %s", r.url[:80])
                return route.fulfill(status=204, body="")
        except Exception:
            pass
        route.fallback()

    def _on_new_page(self, p):
        if self.page is not None and p is not self.page:
            log.info("closing pop-up tab %s", p.url[:80])
            try:
                p.close()
            except Exception:
                pass

    def _on_response(self, r):
        try:
            url = r.url
            if url.startswith(("data:", "blob:")) or r.status >= 400:
                return
            if any(f[0] == url for f in self.found):
                return
            ct = (r.headers.get("content-type") or "").lower()
            size = int(r.headers.get("content-length") or 0)
            hit = bool(PLAYLIST_URL.search(url)) or any(x in ct for x in PLAYLIST_CT)
            body = b""
            textish = (not ct) or any(x in ct for x in ("text", "json", "octet"))
            if (hit or textish) and 0 <= size < 300_000 and r.request.resource_type in (
                    "xhr", "fetch", "media", "other"):
                if size or "octet" not in ct:  # don't pull unknown-size binary bodies
                    try:
                        body = r.body()
                    except Exception:
                        body = b""
            if not hit:  # players that disguise the playlist as .txt/.json/.png
                hit = body.lstrip()[:7] == b"#EXTM3U"
            if not hit:
                return
            master = b"#EXT-X-STREAM-INF" in body
            self.found.append((url, r.request.all_headers(), master))
            log.info("found playlist%s: %s", " (master)" if master else "", url[:160])
        except Exception as e:
            log.debug("response handler: %s", e)

    def best_playlist(self):
        masters = [f for f in self.found if f[2]]
        return (masters or self.found)[0]

    def times(self):
        """[(currentTime, paused), ...] for all videos in all frames; None if browser is dead."""
        try:
            res = []
            for fr in self.page.frames:
                try:
                    res += [(v["t"], v["paused"]) for v in fr.evaluate(JS_VIDEOS) if v["area"] > 0]
                except Exception:
                    pass
            return res
        except Exception:
            return None

    def _largest_video(self):
        best = None
        for fr in self.page.frames:
            try:
                for i, v in enumerate(fr.evaluate(JS_VIDEOS)):
                    if v["area"] > 0 and (best is None or v["area"] > best[2]):
                        best = (fr, i, v["area"])
            except Exception:
                pass
        if best:
            els = best[0].query_selector_all("video")
            if best[1] < len(els):
                return best[0], els[best[1]]
        return None, None

    def click_video(self):
        _, el = self._largest_video()
        box = el.bounding_box() if el else None
        if not box:  # no <video> yet: click the biggest iframe, else the page centre
            frames = [b for f in self.page.query_selector_all("iframe") if (b := f.bounding_box())]
            box = max(frames, key=lambda b: b["width"] * b["height"], default=None)
        if box:
            x, y = box["x"] + box["width"] / 2, box["y"] + box["height"] / 2
        else:
            vp = self.page.viewport_size or {"width": 1280, "height": 720}
            x, y = vp["width"] / 2, vp["height"] / 2
        try:
            self.page.mouse.click(x, y)
        except Exception as e:
            log.debug("click failed: %s", e)

    def open_and_play(self, url, timeout):
        """Load the page and click until a video plays (or, when sniffing, a playlist shows up)."""
        self.home = None
        self.page.goto(url, wait_until="domcontentloaded", timeout=60_000)
        self.home = self.page.url  # after the site's own redirects
        deadline, last = time.time() + timeout, None
        while time.time() < deadline and not STOP.is_set():
            self.page.wait_for_timeout(3000)
            if not same_site(self.page.url, url):  # an ad hijacked the tab
                log.info("tab redirected to %s - going back", self.page.url[:80])
                self.page.goto(url, wait_until="domcontentloaded", timeout=60_000)
                continue
            if self.sniff and self.found:
                return True
            snap = self.times() or []
            if snap and last is not None and snap != last and any(not p for _, p in snap):
                return True
            if not snap or all(p for _, p in snap):
                self.click_video()
            last = snap
        return bool(self.found)

    def theater(self):
        """Make the video fill the window (fullscreen if allowed, CSS otherwise)."""
        fr, el = self._largest_video()
        if not el:
            return
        try:
            el.evaluate(JS_FILL)
            f = fr
            while f.parent_frame:  # also blow up every iframe the video sits in
                f.frame_element().evaluate(JS_FILL)
                f = f.parent_frame
        except Exception as e:
            log.debug("theater: %s", e)

    def close(self):
        for fn in (self.ctx.close, self._pw.stop):
            try:
                fn()
            except Exception:
                pass


# ----------------------------------------------------------------------------- grab mode
_HLS_HELP = None


def hls_input_opts(url):
    """ffmpeg refuses HLS with odd extensions (.txt playlists, .jpg/.png segments) unless told."""
    global _HLS_HELP
    if re.search(r"\.mpd(\?|#|$)", url, re.I):
        return []
    if _HLS_HELP is None:
        _HLS_HELP = subprocess.run(["ffmpeg", "-hide_banner", "-h", "demuxer=hls"],
                                   capture_output=True, text=True).stdout
    opts = ["-f", "hls", "-allowed_extensions", "ALL"]
    if "extension_picky" in _HLS_HELP:  # ffmpeg >= 7.1
        opts += ["-extension_picky", "0"]
    return opts


def grab_cmd(a, url, h, pattern):
    hdr = "".join(f"{k}: {v}\r\n" for k, v in h.items() if k.lower() in FWD_HEADERS)
    return ["ffmpeg", "-hide_banner", "-loglevel", "warning", "-nostdin",
            "-user_agent", h.get("user-agent", "Mozilla/5.0"),
            *(["-headers", hdr] if hdr else []),
            "-rw_timeout", "20000000",
            *hls_input_opts(url),
            "-i", url,
            "-c", "copy", "-f", "segment", "-segment_time", str(a.part),
            "-reset_timestamps", "1", "-segment_format", "mpegts", pattern]


def watch(proc, out, prefix, a, end):
    started = time.time()
    while True:
        if STOP.wait(5):
            return "stop"
        if proc.poll() is not None:
            return f"ffmpeg exited ({proc.returncode})"
        if now() >= end:
            return "end"
        if time.time() - max(newest_mtime(out, prefix), started) > a.stall:
            return f"stalled: no data for {a.stall}s"


def grab_session(a, out, end):
    b = Browser(a, sniff=True)
    ff = None
    try:
        b.open_and_play(a.url, a.find_timeout)
        b.page.wait_for_timeout(4000)  # let the master playlist / variants arrive
        if not b.found:  # e.g. the video plays, but not from HLS/DASH (mp4, MSE with odd URLs)
            return "no playlist found"
        url, headers, _ = b.best_playlist()
        if not a.keep_browser:
            b.close()
            b = None
        prefix = f"run{next_run(out):03d}"
        ff = start_ffmpeg(grab_cmd(a, url, headers, str(out / f"{prefix}_%03d.ts")), out)
        return watch(ff, out, prefix, a, end)
    finally:
        stop_ffmpeg(ff)
        if b:
            b.close()


# ----------------------------------------------------------------------------- screen mode
class Display:
    """Xvfb virtual screen + a PulseAudio null sink the browser plays into."""

    def __init__(self, a):
        self.num = f":{a.display}"
        self.x = subprocess.Popen(["Xvfb", self.num, "-screen", "0", f"{a.size}x24", "-nolisten", "tcp"],
                                  stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        time.sleep(2)
        if self.x.poll() is not None:
            raise RuntimeError(f"Xvfb failed on {self.num} (in use? try --display 98)")
        if subprocess.run(["pactl", "info"], capture_output=True).returncode != 0:
            subprocess.run(["pulseaudio", "--start", "--exit-idle-time=-1"], capture_output=True)
            time.sleep(1)
        sinks = subprocess.run(["pactl", "list", "short", "sinks"], capture_output=True, text=True).stdout
        if a.sink not in sinks:
            subprocess.run(["pactl", "load-module", "module-null-sink", f"sink_name={a.sink}"],
                           check=True, capture_output=True)

    def close(self):
        self.x.terminate()


def screen_cmd(a, display, pattern):
    v = ["-c:v", a.vcodec] + (["-preset", "veryfast", "-crf", str(a.crf)] if a.vcodec == "libx264" else [])
    return ["ffmpeg", "-hide_banner", "-loglevel", "warning", "-nostdin",
            "-thread_queue_size", "1024", "-f", "x11grab", "-draw_mouse", "0",
            "-framerate", str(a.fps), "-video_size", a.size, "-i", display,
            "-thread_queue_size", "1024", "-f", "pulse", "-i", f"{a.sink}.monitor",
            *v, "-pix_fmt", "yuv420p", "-g", str(a.fps * 2), "-c:a", "aac", "-b:a", "160k",
            "-f", "segment", "-segment_time", str(a.part),
            "-reset_timestamps", "1", "-segment_format", "mpegts", pattern]


def screen_session(a, out, end):
    d = Display(a)
    b = ff = None
    try:
        while not STOP.is_set() and now() < end:
            if b is None:
                b = Browser(a, display=d.num)
                if not b.open_and_play(a.url, a.find_timeout):
                    log.warning("video not playing yet; retrying in %ss", a.retry)
                    b.close()
                    b = None
                    STOP.wait(a.retry)
                    continue
                b.theater()
                last, last_change = b.times(), time.time()
                log.info("video playing")
            if ff is None or ff.poll() is not None:  # start only once something plays
                if ff:
                    log.warning("ffmpeg exited (%s) - starting a new run", ff.returncode)
                prefix = f"run{next_run(out):03d}"
                ff = start_ffmpeg(screen_cmd(a, d.num, str(out / f"{prefix}_%03d.ts")), out)
            if STOP.wait(10):
                break
            snap = b.times()
            if snap is None:
                log.warning("browser died - restarting it")
                b.close()
                b = None
                continue
            if snap != last and any(not p for _, p in snap):
                last_change = time.time()
            last = snap
            b.theater()  # players sometimes reset styles
            if time.time() - last_change > a.stall:
                log.warning("video frozen for %ss - reloading page", a.stall)
                b.close()
                b = None
        return "stop" if STOP.is_set() else "end"
    finally:
        stop_ffmpeg(ff)
        if b:
            b.close()
        d.close()


# ----------------------------------------------------------------------------- commands
def uploader(a, out):
    base = ["rclone", "copy", str(out), a.rclone, "--include", "*.ts"]
    while not STOP.wait(60):
        subprocess.run(base + ["--min-age", "2m"], capture_output=True)  # skip the part being written
    subprocess.run(base, capture_output=True)


TOOLS = {
    "ffmpeg": "ffmpeg",
    "Xvfb": "xorg-server-xvfb (Arch) / xvfb (Debian/Ubuntu)",
    "pactl": "libpulse (Arch) / pulseaudio-utils (Debian/Ubuntu)",
    "rclone": "rclone",
}


def missing_tools(mode, rclone):
    need = ["ffmpeg"] + (["Xvfb", "pactl"] if mode in ("screen", "auto") else []) + (["rclone"] if rclone else [])
    return [t for t in need if not shutil.which(t)]


def cmd_record(a):
    miss = missing_tools(a.mode, a.rclone)
    if miss:
        lines = "\n".join(f"  {t:7s} -> install {TOOLS[t]}" for t in miss)
        sys.exit(f"missing programs:\n{lines}"
                 + ("\n(auto mode needs Xvfb/pactl for its screen-recording fallback; "
                    "use --mode grab to skip them)" if a.mode == "auto" else ""))
    a.sink = f"streamrec{a.display}"
    start = parse_when(a.start)
    end = start + a.duration if a.duration else parse_when(a.end, base=start)
    if end <= now():
        sys.exit("end time is in the past")
    host = urlparse(a.url).hostname or "stream"
    out = Path(a.out or f"recordings/{start:%Y%m%d-%H%M}-{host}").expanduser()
    out.mkdir(parents=True, exist_ok=True)
    fh = logging.FileHandler(out / "recorder.log")
    fh.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(message)s"))
    log.addHandler(fh)
    log.info("recording %s  %s -> %s  into %s  (mode %s)", a.url, start, end, out, a.mode)

    wake = start - dt.timedelta(minutes=a.lead)
    if wake > now():
        log.info("waiting until %s", wake)
    while not STOP.is_set() and now() < wake:
        STOP.wait(min(30, (wake - now()).total_seconds()))

    up = None
    if a.rclone:
        up = threading.Thread(target=uploader, args=(a, out))
        up.start()

    mode, misses = a.mode, 0
    while not STOP.is_set() and now() < end:
        try:
            r = screen_session(a, out, end) if mode == "screen" else grab_session(a, out, end)
        except Exception as e:
            log.exception("session error")
            r = f"error: {e}"
        log.info("%s session ended: %s", mode, r)
        if r in ("end", "stop"):
            break
        if mode != "screen":
            misses = misses + 1 if r == "no playlist found" else 0
            if mode == "auto" and misses >= a.grab_tries:
                log.warning("no playlist after %d tries - switching to screen recording", misses)
                mode = "screen"
                continue
        STOP.wait(a.retry)

    STOP.set()
    if up:
        up.join()
    log.info("done. join the parts with:  %s join %s", sys.argv[0], out)


def cmd_probe(a):
    b = Browser(a, sniff=True)
    try:
        b.open_and_play(a.url, a.find_timeout)
        b.page.wait_for_timeout(5000)
        t = b.times()
        print("\nvideo elements (currentTime, paused):", t)
        if b.found:
            print("playlists found -> grab mode should work:")
            for url, _, master in b.found:
                print(("  [master] " if master else "  ") + url)
        else:
            print("no playlist found -> use --mode screen")
        if a.show:
            input("press Enter to close the browser...")
    finally:
        b.close()


def cmd_login(a):
    a.show = True
    b = Browser(a)
    try:
        b.page.goto(a.url)
        input("log in / accept cookies in the window, then press Enter here...")
    finally:
        b.close()


def cmd_join(a):
    d = Path(a.dir)
    parts = [p for p in sorted(d.glob("run*_*.ts")) if p.stat().st_size > 4096]  # skip empty stubs from instant crashes
    if not parts:
        sys.exit("no parts found")
    lst = d / "parts.txt"
    lst.write_text("".join("file '%s'\n" % str(p.resolve()).replace("'", "'\\''") for p in parts))
    out = a.output or str(d / "joined.mkv")
    if Path(out).exists():
        sys.exit(f"{out} already exists (move it away or pass -o)")
    r = subprocess.run(["ffmpeg", "-hide_banner", "-loglevel", "warning", "-nostdin", "-n", "-f", "concat",
                        "-safe", "0", "-i", str(lst), "-c", "copy", out])
    if r.returncode:
        sys.exit(f"ffmpeg failed (code {r.returncode})")
    print(f"joined {len(parts)} parts -> {out}")


# ----------------------------------------------------------------------------- scheduler
SCHED_ONLY = ("inhibit_sleep",)  # schedule keys handled here, not passed to `record`


def to_dt(v, base=None, what="time"):
    if isinstance(v, dt.datetime):
        return v if v.tzinfo else v.astimezone()
    if isinstance(v, dt.time):
        v = f"{v.hour}:{v.minute:02d}"
    if isinstance(v, str):
        if base is None and re.fullmatch(r"\d{1,2}:\d{2}", v.strip()):
            raise ValueError(f"{what} {v!r} needs a date, e.g. 2026-11-25T21:00")
        return parse_when(v.strip(), base=base)
    raise ValueError(f"bad {what}: {v!r}")


def load_schedule(path):
    import tomllib

    with open(path, "rb") as f:
        data = tomllib.load(f)
    return parse_schedule(data)


def parse_schedule(data):
    defaults = data.get("defaults", {})
    pages = {}
    for i, pg in enumerate(data.get("page", []), 1):
        if not isinstance(pg.get("name"), str) or not isinstance(pg.get("url"), str):
            raise ValueError(f"page #{i}: needs a name and a url")
        if pg["name"] in pages:
            raise ValueError(f"duplicate page name {pg['name']!r}")
        pages[pg["name"]] = pg["url"]
    jobs = {}
    for i, entry in enumerate(data.get("stream", []), 1):
        j = {**defaults, **entry}
        page = j.pop("page", None)
        if page is not None and "url" not in entry:
            if page not in pages:
                raise ValueError(f"stream #{i}: unknown page {page!r}")
            j["url"] = pages[page]
        if "url" not in j or "start" not in j or not ("end" in j or "duration" in j):
            raise ValueError(f"stream #{i}: needs url (or page), start, and end or duration")
        start = to_dt(j.pop("start"), what=f"stream #{i} start")
        if "end" in j:
            end = to_dt(j.pop("end"), base=start, what=f"stream #{i} end")
            j.pop("duration", None)
        else:
            end = start + parse_duration(str(j.pop("duration")))
        if end <= start:
            raise ValueError(f"stream #{i}: end is before start")
        url = j.pop("url")
        name = j.pop("name", None) or f"{start:%Y%m%d-%H%M}-{urlparse(url).hostname}"
        name = safe_name(name)
        if name in jobs:
            raise ValueError(f"duplicate stream name {name!r}")
        job = {"name": name, "url": url, "page": page, "start": start, "end": end, "opts": j,
               "index": i - 1}
        check_opts(job)
        jobs[name] = job
    return jobs


def safe_name(name):
    return re.sub(r"[^\w.-]+", "_", str(name)).strip("._") or "stream"


def record_argv(job, out, profile, display):
    """The `record` command line for a schedule entry (without the program itself)."""
    argv = ["record", job["url"], "--start", job["start"].isoformat(), "--end", job["end"].isoformat(),
            "--out", str(out), "--profile", str(profile), "--display", str(display)]
    for k, v in job["opts"].items():
        if k in SCHED_ONLY or k == "profile" or v is False:
            continue
        argv.append("--" + k.replace("_", "-"))
        if v is not True:
            argv.append(str(v))
    return argv


def check_opts(job):
    """Reject unknown/invalid record options now instead of letting the recorder crash-loop."""
    for k in job["opts"]:
        if k in ("start", "end", "duration", "out", "display", "help"):
            raise ValueError(f"stream {job['name']!r}: option {k!r} can't be set here")
    try:
        rp = build_parser().record
        rp.raise_errors = True
        rp.parse_args(record_argv(job, "x", "x", 99)[1:])
    except ArgError as e:
        raise ValueError(f"stream {job['name']!r}: {e}") from None
    if "lead" in job["opts"]:
        int(job["opts"]["lead"])


class Running:
    def __init__(self):
        self.proc = None
        self.display = None
        self.fails = 0
        self.next_try = 0.0
        self.done = False
        self.end = None
        self.launches = 0
        self.started = None
        self.last_exit = None


def kill_group(proc, name, timeout=60):
    if proc.poll() is not None:
        return
    log.info("[%s] stopping", name)
    try:
        os.killpg(proc.pid, signal.SIGTERM)
        proc.wait(timeout)
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        proc.wait()
    except ProcessLookupError:
        pass


def launch(job, rt, a, used_displays):
    name, o = job["name"], dict(job["opts"])
    out = Path(a.dir).expanduser() / name
    out.mkdir(parents=True, exist_ok=True)
    rt.display = next(d for d in range(99, 0, -1) if d not in used_displays)
    # each recording gets its own copy of the login profile (Chromium locks a profile)
    base_prof = Path(o.pop("profile", "~/.streamrec/profile")).expanduser()
    prof = Path("~/.streamrec/jobs").expanduser() / name / "profile"
    if not prof.exists() and base_prof.exists():
        shutil.copytree(base_prof, prof, ignore=shutil.ignore_patterns("Singleton*"), symlinks=True)
    cmd = [sys.executable, str(Path(__file__).resolve())] + record_argv(job, out, prof, rt.display)
    if o.get("inhibit_sleep") and shutil.which("systemd-inhibit"):
        cmd = ["systemd-inhibit", "--what=sleep:idle", "--who=streamrec", f"--why=recording {name}"] + cmd
    log.info("[%s] launching (until %s)", name, f"{job['end']:%Y-%m-%d %H:%M}")
    console = open(out / "console.log", "ab")
    rt.proc = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=console, stderr=console,
                               start_new_session=True)
    rt.launches += 1
    rt.started = time.time()


def write_status(state, a):
    """Scheduler -> status.json, read by `list` and the web page."""
    data = {"updated": time.time(), "pid": os.getpid(), "dir": str(Path(a.dir).expanduser()),
            "jobs": {n: {"running": bool(rt.proc and rt.proc.poll() is None), "launches": rt.launches,
                         "fails": rt.fails, "done": rt.done, "started": rt.started,
                         "last_exit": rt.last_exit, "next_try": rt.next_try}
                     for n, rt in state.items()}}
    try:
        STATUS.parent.mkdir(parents=True, exist_ok=True)
        tmp = STATUS.with_name(f".status.{os.getpid()}.tmp")
        tmp.write_text(json.dumps(data))
        os.replace(tmp, STATUS)
    except OSError as e:
        log.debug("status: %s", e)


def cmd_schedule(a):
    path = Path(a.file).expanduser()
    if a.check:
        jobs = load_schedule(path)
        t = now()
        for j in sorted(jobs.values(), key=lambda j: j["start"]):
            state = "past" if j["end"] < t else "LIVE" if j["start"] <= t else "upcoming"
            print(f"{state:9s} {j['name']}\n          {j['start']:%a %Y-%m-%d %H:%M} -> "
                  f"{j['end']:%a %Y-%m-%d %H:%M}  {j['url']}\n          options: {j['opts'] or '-'}")
        print(f"{len(jobs)} stream(s) OK")
        return

    if a.web:
        threading.Thread(target=serve_web, args=(a.web, path, Path(a.dir).expanduser()),
                         daemon=True).start()
    grace = dt.timedelta(minutes=2)
    jobs, state, warned = {}, {}, False
    log.info("scheduler started; watching %s, recordings go to %s", path, Path(a.dir).expanduser())
    while not STOP.is_set():
        try:
            jobs, warned = load_schedule(path), False
        except FileNotFoundError:
            if not warned:
                log.warning("schedule file %s not found (waiting for it)", path)
            jobs, warned = {}, True
        except Exception as e:  # keep the last good schedule on a typo
            log.error("schedule file error, keeping previous version: %s", e)
        t = now()

        for name, rt in list(state.items()):  # removed from the file -> stop it
            if name not in jobs:
                if rt.proc:
                    kill_group(rt.proc, name)
                del state[name]

        for name, j in jobs.items():
            rt = state.setdefault(name, Running())
            if rt.end != j["end"]:  # end time edited -> allowed to run again
                rt.end, rt.done = j["end"], False
            if rt.proc and rt.proc.poll() is not None:
                code, rt.proc = rt.proc.returncode, None
                rt.last_exit = code
                if t < j["end"] - dt.timedelta(seconds=30):
                    rt.fails += 1
                    wait = min(300, 10 * 2 ** (rt.fails - 1))
                    rt.next_try = time.time() + wait
                    log.warning("[%s] recorder exited early (code %s), restarting in %ss "
                                "- see %s/console.log", name, code, wait, name)
                else:
                    rt.done = True
                    log.info("[%s] finished", name)
            alive = rt.proc is not None
            if t > j["end"] + grace:
                if alive:
                    kill_group(rt.proc, name)
                    rt.proc = None
                rt.done = True
                continue
            lead = dt.timedelta(minutes=int(j["opts"].get("lead", 3)))
            if not alive and not rt.done and t >= j["start"] - lead and time.time() >= rt.next_try:
                used = {r.display for r in state.values() if r.proc}
                launch(j, rt, a, used)
        write_status(state, a)
        KICK.wait(15)
        KICK.clear()

    for name, rt in state.items():
        if rt.proc:
            kill_group(rt.proc, name)
    log.info("scheduler stopped")


# ----------------------------------------------------------------------------- schedule editing
# add/remove edit schedule.toml as text, so your comments and layout survive. Every edit is
# locked, validated with the same loader the scheduler uses, and swapped in atomically
# (the previous version is kept as schedule.toml.bak). Recordings on disk are never touched.
HEADER = re.compile(r"^[ \t]*(\[\[?)[ \t]*([\w.-]+)[ \t]*\]\]?[ \t]*(#.*)?$")


def toml_val(v):
    if isinstance(v, bool):
        return "true" if v else "false"
    if isinstance(v, int):
        return str(v)
    if isinstance(v, dt.datetime):  # written as local time, like a hand-written entry
        return v.astimezone().strftime("%Y-%m-%dT%H:%M:%S")
    v = str(v)
    if re.search(r"[\x00-\x1f\x7f]", v):
        raise ValueError(f"control characters not allowed: {v!r}")
    return json.dumps(v, ensure_ascii=False)  # a JSON string is a valid TOML basic string


def toml_block(table, fields):
    return f"[[{table}]]\n" + "".join(f"{k} = {toml_val(v)}\n" for k, v in fields.items() if v is not None)


def blocks(text, table):
    """(first_line, end_line) of each [[table]] block; trailing comments stay with the next block."""
    lines = text.splitlines(keepends=True)
    heads = [(i, m[1] == "[[" and m[2] == table) for i, ln in enumerate(lines) if (m := HEADER.match(ln))]
    out = []
    for n, (i, mine) in enumerate(heads):
        if not mine:
            continue
        end = heads[n + 1][0] if n + 1 < len(heads) else len(lines)
        while end > i + 1 and (not lines[end - 1].strip() or lines[end - 1].lstrip().startswith("#")):
            end -= 1
        out.append((i, end))
    return lines, out


def cut_block(text, table, index):
    lines, bl = blocks(text, table)
    i, end = bl[index]
    if i > 0 and not lines[i - 1].strip():  # take one blank line before it too
        i -= 1
    return "".join(lines[:i] + lines[end:])


def append_block(text, block):
    if text and not text.endswith("\n"):
        text += "\n"
    return text + ("\n" if text.strip() else "") + block


@contextmanager
def schedule_lock(path):
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path.with_name(path.name + ".lock"), "w") as lf:
        fcntl.flock(lf, fcntl.LOCK_EX)
        yield


def edit_schedule(path, fn):
    """fn(old_text) -> new_text; validated and swapped in atomically."""
    import tomllib

    path = Path(path).expanduser().resolve()
    with schedule_lock(path):
        old = path.read_text() if path.exists() else ""
        if old.strip():
            try:
                load_schedule(path)
            except Exception as e:
                raise ValueError(f"{path} has an error, fix it first: {e}") from None
        new = fn(old)
        parse_schedule(tomllib.loads(new))  # raises -> nothing is written
        tmp = path.with_name(f".{path.name}.{os.getpid()}.tmp")
        tmp.write_text(new)
        if old:
            shutil.copy2(path, path.with_name(path.name + ".bak"))
        os.replace(tmp, path)
    KICK.set()


def read_schedule(path):
    """(jobs, pages, error) - never raises, for list/web."""
    import tomllib

    path = Path(path).expanduser()
    try:
        data = tomllib.loads(path.read_text())
        pages = {p.get("name"): p.get("url") for p in data.get("page", [])}
        return parse_schedule(data), pages, None
    except FileNotFoundError:
        return {}, {}, None
    except Exception as e:
        return {}, {}, str(e)


def add_stream(path, start, url=None, page=None, end=None, duration=None, name=None, opts=None):
    """Add a [[stream]]; returns its name. start/end: datetime or anything parse_when takes."""
    if bool(url) == bool(page):
        raise ValueError("give either a URL or a saved page")
    if url and not re.match(r"https?://", url):
        raise ValueError(f"not an http(s) URL: {url!r}")
    start = start if isinstance(start, dt.datetime) else parse_when(str(start).strip())
    start = start.replace(second=0, microsecond=0)
    if end:
        end = end if isinstance(end, dt.datetime) else parse_when(str(end).strip(), base=start)
        duration = None
    elif duration:
        parse_duration(str(duration))
    else:
        raise ValueError("give an end time or a duration")
    stop = end or start + parse_duration(str(duration))
    if stop <= start:
        raise ValueError("end is before start")
    if stop <= now():
        raise ValueError("that ends in the past")
    holder = {}

    def fn(text):
        jobs, _, _ = read_schedule_text(text)
        base = safe_name(name or f"{start:%Y%m%d-%H%M}-{page or urlparse(url).hostname}")
        n, k = base, 2
        while n in jobs:
            if name:
                raise ValueError(f"there is already a stream called {n!r}")
            n, k = f"{base}-{k}", k + 1
        holder["name"] = n
        fields = {"name": n, "url": url, "page": page, "start": start, "end": end, "duration": duration}
        fields.update(opts or {})
        return append_block(text, toml_block("stream", fields))

    edit_schedule(path, fn)
    return holder["name"]


def read_schedule_text(text):
    import tomllib

    data = tomllib.loads(text) if text.strip() else {}
    return parse_schedule(data), {p["name"]: p["url"] for p in data.get("page", [])}, None


def remove_stream(path, name):
    def fn(text):
        jobs, _, _ = read_schedule_text(text)
        if name not in jobs:
            raise ValueError(f"no stream called {name!r}")
        return cut_block(text, "stream", jobs[name]["index"])

    edit_schedule(path, fn)


def add_page(path, name, url):
    name = str(name).strip()
    if not name:
        raise ValueError("a page needs a name")
    if not re.match(r"https?://", url or ""):
        raise ValueError(f"not an http(s) URL: {url!r}")

    def fn(text):
        if name in read_schedule_text(text)[1]:
            raise ValueError(f"there is already a page called {name!r}")
        return append_block(text, toml_block("page", {"name": name, "url": url}))

    edit_schedule(path, fn)


def remove_page(path, name):
    import tomllib

    def fn(text):
        data = tomllib.loads(text)
        names = [p.get("name") for p in data.get("page", [])]
        if name not in names:
            raise ValueError(f"no page called {name!r}")
        users = [j["name"] for j in parse_schedule(data).values() if j["page"] == name]
        if users:
            raise ValueError(f"page {name!r} is used by: {', '.join(users)}")
        return cut_block(text, "page", names.index(name))

    edit_schedule(path, fn)


# ----------------------------------------------------------------------------- status
def read_status():
    try:
        st = json.loads(STATUS.read_text())
    except (OSError, ValueError):
        return None
    st["alive"] = time.time() - st.get("updated", 0) < 60
    return st


def disk_info(out):
    parts = list(out.glob("run*_*.ts")) if out.is_dir() else []
    stats = [p.stat() for p in parts]
    runs = {p.name.split("_")[0] for p in parts}
    return {"parts": len(parts), "runs": len(runs), "bytes": sum(s.st_size for s in stats),
            "last": max((s.st_mtime for s in stats), default=None)}


def job_rows(path, rec_dir):
    """Everything list/web show: one dict per stream, sorted by start, plus the load error."""
    jobs, pages, err = read_schedule(path)
    st = read_status() or {"jobs": {}, "alive": False}
    rec_dir = Path(st.get("dir") or rec_dir).expanduser() if st.get("alive") else Path(rec_dir).expanduser()
    t = now()
    rows = []
    for j in sorted(jobs.values(), key=lambda j: j["start"]):
        s = st["jobs"].get(j["name"], {}) if st["alive"] else {}
        d = disk_info(rec_dir / j["name"])
        fresh = d["last"] and time.time() - d["last"] < 120
        if s.get("running"):
            state = ("recording" if fresh else "retrying" if s.get("fails", 0) >= 2
                     else "starting" if time.time() - (s.get("started") or 0) < 180 else "no data")
        elif j["end"] < t:
            state = "done" if d["parts"] else "missed"
        elif j["start"] - dt.timedelta(minutes=int(j["opts"].get("lead", 3))) <= t:
            state = "retrying" if s.get("fails") else "due"
        else:
            state = "upcoming"
        rows.append({**j, **d, "state": state, "launches": s.get("launches", 0),
                     "restarts": max(0, s.get("launches", 0) - 1), "last_exit": s.get("last_exit")})
    return rows, pages, err, st, rec_dir


def human_size(n):
    for unit in ("B", "KB", "MB", "GB"):
        if n < 1024 or unit == "GB":
            return f"{n:.0f} {unit}" if unit in ("B", "KB") else f"{n:.1f} {unit}"
        n /= 1024


def ago(ts):
    s = int(time.time() - ts)
    return f"{s}s ago" if s < 120 else f"{s // 60}m ago" if s < 7200 else f"{s // 3600}h ago"


# ----------------------------------------------------------------------------- CLI edits
def cmd_list(a):
    rows, pages, err, st, _ = job_rows(a.file, a.dir)
    if err:
        print(f"!! schedule file error (scheduler keeps the last good version): {err}")
    if not st["alive"]:
        print("!! scheduler is not running (no fresh status.json)")
    for r in rows:
        if r["end"] < now() - dt.timedelta(days=a.days) and not a.all:
            continue
        src = f"[{r['page']}] " if r["page"] else ""
        disk = f"{r['parts']} parts, {human_size(r['bytes'])}" if r["parts"] else "no parts yet"
        extra = f", {r['restarts']} restart{'s' * (r['restarts'] > 1)}" if r["restarts"] else ""
        print(f"{r['state']:9s} {r['name']}\n          {r['start']:%a %d %b %H:%M} -> {r['end']:%a %d %b %H:%M}"
              f"  {src}{r['url']}\n          {disk}{extra}"
              + (f"  last data {ago(r['last'])}" if r["last"] else ""))
    if pages and a.pages:
        print("pages:")
        for n, u in pages.items():
            print(f"  {n}: {u}")
    if not rows:
        print("no streams scheduled")


def kv_opts(items):
    opts = {}
    for it in items or []:
        k, sep, v = it.partition("=")
        if not sep:
            raise SystemExit(f"--set wants key=value, got {it!r}")
        v = v.strip()
        opts[k.strip().replace("-", "_")] = (True if v == "true" else False if v == "false"
                                             else int(v) if re.fullmatch(r"-?\d+", v) else v)
    return opts


def cmd_add(a):
    _, pages, _ = read_schedule(a.file)
    target = a.target
    url, page = (None, target) if target in pages else (target, None)
    if url and not re.match(r"https?://", url):
        sys.exit(f"{target!r} is not a URL or a saved page (pages: {', '.join(pages) or 'none'})")
    opts = kv_opts(a.set)
    if a.mode:
        opts["mode"] = a.mode
    if a.part:
        opts["part"] = a.part
    try:
        name = add_stream(a.file, a.start, url=url, page=page, end=a.end, duration=a.duration,
                          name=a.name, opts=opts)
    except (ValueError, argparse.ArgumentTypeError) as e:
        sys.exit(f"not added: {e}")
    print(f"added {name}")


def cmd_remove(a):
    try:
        remove_stream(a.file, a.name)
    except ValueError as e:
        sys.exit(str(e))
    print(f"removed {a.name} (its recordings stay on disk; a running recording stops within 15 s)")


def cmd_page(a):
    try:
        if a.action == "add":
            add_page(a.file, a.name, a.url)
        elif a.action == "remove":
            remove_page(a.file, a.name)
        else:
            for n, u in read_schedule(a.file)[1].items():
                print(f"{n}: {u}")
            return
    except ValueError as e:
        sys.exit(str(e))
    print("ok")


# ----------------------------------------------------------------------------- web page
# Small phone page for the schedule. Reach it over Tailscale only: it binds to the tailscale
# address by default and refuses clients from public IPs, so a port forward can't expose it.
ALLOWED_NETS = [ipaddress.ip_network(n) for n in (
    "127.0.0.0/8", "::1/128", "100.64.0.0/10", "fd7a:115c:a1e0::/48",  # loopback, tailscale
    "10.0.0.0/8", "172.16.0.0/12", "192.168.0.0/16", "fe80::/10", "fc00::/7")]  # LAN

CSS = """
:root{--bg:#f6f6f4;--card:#fff;--fg:#1c1c1a;--mute:#6b6b66;--line:#e2e2dd;--acc:#c2410c;
--ok:#15803d;--warn:#b45309;--bad:#b91c1c;--onacc:#fff;color-scheme:light dark}
@media (prefers-color-scheme:dark){:root{--bg:#121211;--card:#1d1d1b;--fg:#ececea;--mute:#9a9a94;
--line:#2f2f2c;--acc:#fb923c;--ok:#4ade80;--warn:#fbbf24;--bad:#f87171;--onacc:#1c1c1a}}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--fg);
font:16px/1.4 system-ui,-apple-system,sans-serif;padding:env(safe-area-inset-top) 0 40px}
main{max-width:640px;margin:0 auto;padding:12px 16px}
h1{font-size:20px;margin:8px 0 12px;display:flex;justify-content:space-between;align-items:baseline}
h1 small{font-size:13px;font-weight:400;color:var(--mute)}
h2{font-size:13px;text-transform:uppercase;letter-spacing:.06em;color:var(--mute);margin:22px 0 8px}
.card{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:12px 14px;margin:8px 0}
.row{display:flex;gap:10px;align-items:flex-start;justify-content:space-between}
.name{font-weight:600;word-break:break-all}.mute{color:var(--mute);font-size:14px}
.url{font-size:13px;color:var(--mute);word-break:break-all}
.pill{font-size:12px;font-weight:600;padding:2px 8px;border-radius:99px;border:1px solid currentColor;white-space:nowrap}
.recording{color:var(--ok)}.starting,.due,.retrying,.no{color:var(--warn)}.missed{color:var(--bad)}
.upcoming,.done{color:var(--mute)}
.err{background:var(--bad);color:#fff;border-radius:10px;padding:10px 14px;margin:8px 0}
.okmsg{background:var(--ok);color:var(--onacc);border-radius:10px;padding:10px 14px;margin:8px 0}
form.inline{margin:0}button{font:inherit;border-radius:10px;border:1px solid var(--line);
background:var(--card);color:var(--fg);padding:8px 12px}
button.del{color:var(--bad);font-size:14px;padding:4px 10px}button.go{background:var(--acc);
border-color:var(--acc);color:var(--onacc);font-weight:600;width:100%;padding:12px}
label{display:block;font-size:13px;color:var(--mute);margin:10px 0 4px}
input,select{font:inherit;width:100%;padding:10px;border-radius:10px;border:1px solid var(--line);
background:var(--bg);color:var(--fg);min-width:0}
.two{display:grid;grid-template-columns:minmax(0,1fr) minmax(0,1fr);gap:10px}
@media (max-width:480px){.two.when{grid-template-columns:minmax(0,1fr)}}
details summary{cursor:pointer;color:var(--mute);font-size:14px;margin-top:10px}
a{color:var(--acc)}
"""

ICON = """<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 100 100"><rect width="100" height="100"
rx="22" fill="#c2410c"/><circle cx="50" cy="50" r="22" fill="#fff"/></svg>"""

JS = """
const box=document.getElementById('jobs');
if(/[?&](url|page)=/.test(location.search))document.getElementById('add').scrollIntoView();
setInterval(()=>fetch('jobs').then(r=>r.ok&&r.text()).then(t=>{if(t)box.innerHTML=t}).catch(()=>{}),20000);
document.addEventListener('submit',e=>{const m=e.target.dataset.confirm;if(m&&!confirm(m))e.preventDefault()});
const s=document.getElementById('start'),en=document.getElementById('end');
s&&s.addEventListener('change',()=>{if(!s.value)return;const d=new Date(s.value);d.setHours(d.getHours()+2);
const p=n=>String(n).padStart(2,'0');en.value=`${d.getFullYear()}-${p(d.getMonth()+1)}-${p(d.getDate())}T${p(d.getHours())}:${p(d.getMinutes())}`});
"""


def e(s):
    return html.escape(str(s), quote=True)


def local_input(t):
    return t.strftime("%Y-%m-%dT%H:%M")


def fmt_span(a, b):
    same = a.date() == b.date()
    return f"{a:%a %d %b %H:%M} – {b:%H:%M}" if same else f"{a:%a %d %b %H:%M} – {b:%a %d %b %H:%M}"


def jobs_html(path, rec_dir):
    rows, pages, err, st, rec_dir = job_rows(path, rec_dir)
    out = []
    if err:
        out.append(f'<div class="err">Schedule file has an error, the scheduler keeps the last good '
                   f'version:<br>{e(err)}</div>')
    if not st["alive"]:
        out.append('<div class="err">The scheduler is not running, so nothing will record.</div>')
    t = now()
    groups = {"Live": [], "Upcoming": [], "Past": []}
    for r in rows:
        g = "Past" if r["end"] < t else "Live" if r["start"] - dt.timedelta(minutes=int(r["opts"].get("lead", 3))) <= t else "Upcoming"
        groups[g].append(r)
    groups["Past"].reverse()
    for g, rs in groups.items():
        if not rs:
            continue
        out.append(f"<h2>{g}</h2>")
        for r in rs[:30]:
            bits = []
            if r["parts"]:
                bits.append(f"{r['parts']} part{'s' * (r['parts'] != 1)} · {human_size(r['bytes'])}")
            if r["last"] and g != "Past":
                bits.append(f"last data {ago(r['last'])}")
            if r["restarts"]:
                bits.append(f"{r['restarts']} restart{'s' * (r['restarts'] > 1)}")
            if r["runs"] > 1:
                bits.append(f"{r['runs']} runs")
            mode = r["opts"].get("mode")
            if mode:
                bits.append(e(mode))
            src = f"<b>{e(r['page'])}</b> · " if r["page"] else ""
            live = r["end"] >= t and r["state"] != "upcoming"
            confirm = ("Stop this recording now and remove it? Parts already saved stay on disk."
                       if live else "Remove this entry? Recordings on disk are kept.")
            out.append(
                f'<div class="card"><div class="row"><div><div class="name">{e(r["name"])}</div>'
                f'<div class="mute">{fmt_span(r["start"], r["end"])}</div></div>'
                f'<span class="pill {e(r["state"].split()[0])}">{e(r["state"])}</span></div>'
                f'<div class="url">{src}{e(r["url"])}</div>'
                f'<div class="row" style="margin-top:6px;align-items:center"><div class="mute">'
                f'{" · ".join(bits)}{" · " if bits else ""}<a href="log/{quote(r["name"])}">log</a></div>'
                f'<form class="inline" method="post" action="remove" data-confirm="{e(confirm)}">'
                f'<input type="hidden" name="name" value="{e(r["name"])}">'
                f'<button class="del">{"Stop" if live else "Remove"}</button></form></div></div>')
    if not rows:
        out.append('<p class="mute">Nothing scheduled yet.</p>')
    return "".join(out)


def prefill_time(v, base=None):
    """For ?start=/?end= links: 'HH:MM', ISO date-time, or a unix timestamp. None if unreadable."""
    try:
        v = v.strip()
        t = dt.datetime.fromtimestamp(int(v)).astimezone() if v.isdigit() and len(v) >= 9 else parse_when(v, base=base)
        return t.replace(second=0, microsecond=0)
    except (ValueError, OverflowError, OSError):
        return None


def page_html(path, rec_dir, msg=None, err=None, pre=None):
    """pre: values for the add form, from a link like /?url=…&start=21:00&end=23:00&name=…"""
    pre = pre or {}
    _, pages, _ = read_schedule(path)
    start = (now() + dt.timedelta(minutes=10)).replace(second=0, microsecond=0)
    start += dt.timedelta(minutes=-start.minute % 5)
    start = prefill_time(pre["start"]) if pre.get("start") and prefill_time(pre["start"]) else start
    end = (pre.get("end") and prefill_time(pre["end"], base=start)) or start + dt.timedelta(hours=2)
    opts = "".join(f'<option value="{e(n)}"{" selected" if n == pre.get("page") else ""}>{e(n)}</option>' for n in pages)
    mode_opts = "".join(f'<option{" selected" if m == pre.get("mode") else ""}>{m}</option>' for m in ("auto", "grab", "screen"))
    if pre.get("url") or pre.get("page"):
        msg = msg or "Check the details and tap Schedule."
    page_list = "".join(
        f'<div class="card row" style="align-items:center"><div><div class="name">{e(n)}</div>'
        f'<div class="url">{e(u)}</div></div><form class="inline" method="post" action="page/remove" '
        f'data-confirm="Delete saved page {e(n)}?"><input type="hidden" name="name" value="{e(n)}">'
        f'<button class="del">Delete</button></form></div>' for n, u in pages.items())
    banner = (f'<div class="err">{e(err)}</div>' if err else "") + (f'<div class="okmsg">{e(msg)}</div>' if msg else "")
    return f"""<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<title>streamrec</title><link rel="manifest" href="manifest.webmanifest">
<link rel="icon" href="icon.svg"><link rel="apple-touch-icon" href="icon.svg">
<meta name="apple-mobile-web-app-capable" content="yes"><meta name="mobile-web-app-capable" content="yes">
<meta name="theme-color" content="#c2410c"><style>{CSS}</style></head><body><main>
<h1>streamrec <small>{now():%a %d %b %H:%M}</small></h1>{banner}
<div id="jobs">{jobs_html(path, rec_dir)}</div>
<h2>Add a recording</h2>
<form class="card" id="add" method="post" action="add">
{f'<label>Saved page</label><select name="page"><option value="">— use the URL below —</option>{opts}</select>' if pages else ''}
<label>URL</label><input name="url" type="url" inputmode="url" placeholder="https://…" autocomplete="off" value="{e(pre.get('url', ''))}">
<div class="two when"><div><label>Start</label><input id="start" name="start" type="datetime-local" required value="{local_input(start)}"></div>
<div><label>End</label><input id="end" name="end" type="datetime-local" value="{local_input(end)}"></div></div>
<details{' open' if any(pre.get(k) for k in ('name', 'mode', 'duration')) else ''}><summary>More options</summary>
<label>Name (folder)</label><input name="name" placeholder="automatic" autocomplete="off" value="{e(pre.get('name', ''))}">
<div class="two"><div><label>Mode</label><select name="mode"><option value="">default</option>{mode_opts}</select></div>
<div><label>Duration (instead of end)</label><input name="duration" placeholder="e.g. 2h30m" autocomplete="off" value="{e(pre.get('duration', ''))}"></div></div>
</details><div style="margin-top:14px"><button class="go">Schedule</button></div></form>
<h2>Saved pages</h2>{page_list}
<form class="card" method="post" action="page/add"><div class="two">
<div><label>Name</label><input name="name" required placeholder="channel 1" autocomplete="off"></div>
<div><label>URL</label><input name="url" type="url" required placeholder="https://…" autocomplete="off"></div></div>
<div style="margin-top:12px"><button>Save page</button></div></form>
<p class="mute">Removing an entry never deletes recordings. Files: {e(Path(rec_dir).expanduser())}</p>
</main><script>{JS}</script></body></html>"""


def tail(p, n=200):
    try:
        with open(p, "rb") as f:
            f.seek(0, 2)
            f.seek(max(0, f.tell() - 64_000))
            return b"\n".join(f.read().splitlines()[-n:]).decode(errors="replace")
    except OSError:
        return ""


def make_handler(path, rec_dir):
    from http.server import BaseHTTPRequestHandler

    class H(BaseHTTPRequestHandler):
        server_version = "streamrec"

        def log_message(self, fmt, *args):
            log.debug("web %s " + fmt, self.client_address[0], *args)

        def allowed(self):
            ip = ipaddress.ip_address(self.client_address[0].split("%")[0])
            if getattr(ip, "ipv4_mapped", None):
                ip = ip.ipv4_mapped
            if any(ip in n for n in ALLOWED_NETS if n.version == ip.version):
                return True
            log.warning("web: refused client %s (not tailscale/LAN)", ip)
            self.send(403, "forbidden\n", "text/plain")
            return False

        def send(self, code, body, ctype="text/html; charset=utf-8", extra=()):
            b = body.encode() if isinstance(body, str) else body
            self.send_response(code)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(b)))
            self.send_header("Cache-Control", "no-store")
            self.send_header("X-Frame-Options", "DENY")
            self.send_header("Referrer-Policy", "no-referrer")
            for k, v in extra:
                self.send_header(k, v)
            self.end_headers()
            self.wfile.write(b)

        def redirect(self, msg=None, err=None):
            q = "?" + "&".join(f"{k}={quote(v)}" for k, v in (("msg", msg), ("err", err)) if v) if msg or err else ""
            self.send(303, "", extra=[("Location", "./" + q)])

        def do_GET(self):
            if not self.allowed():
                return
            u = urlparse(self.path)
            q = {k: v[0] for k, v in parse_qs(u.query).items()}
            p = u.path.rstrip("/") or "/"
            if p == "/":
                pre = {k: q[k] for k in ("url", "page", "start", "end", "duration", "name", "mode") if q.get(k)}
                self.send(200, page_html(path, rec_dir, q.get("msg"), q.get("err"), pre))
            elif p == "/jobs":
                self.send(200, jobs_html(path, rec_dir))
            elif p == "/manifest.webmanifest":
                self.send(200, json.dumps({"name": "streamrec", "short_name": "streamrec", "start_url": "./",
                                           "display": "standalone", "background_color": "#121211",
                                           "theme_color": "#c2410c", "icons": [{"src": "icon.svg", "sizes": "any",
                                                                                "type": "image/svg+xml"}]}),
                          "application/manifest+json")
            elif p == "/icon.svg":
                self.send(200, ICON, "image/svg+xml")
            elif p.startswith("/log/"):
                from urllib.parse import unquote
                name = unquote(p[5:])
                st = read_status() or {}
                d = Path(st.get("dir") or rec_dir).expanduser()
                if name != safe_name(name) or not (d / name).is_dir():
                    return self.send(404, "no such recording\n", "text/plain; charset=utf-8")
                body = "\n\n".join(f"== {f} ==\n{tail(d / name / f)}" for f in
                                   ("recorder.log", "console.log", "ffmpeg.log") if (d / name / f).exists())
                self.send(200, body or "(no logs yet)\n", "text/plain; charset=utf-8")
            else:
                self.send(404, "not found\n", "text/plain")

        def do_POST(self):
            if not self.allowed():
                return
            origin = self.headers.get("Origin")  # basic CSRF guard: forms must come from this page
            if origin and origin != "null" and urlparse(origin).netloc != self.headers.get("Host"):
                return self.send(403, "bad origin\n", "text/plain")
            n = int(self.headers.get("Content-Length") or 0)
            if n > 20_000:
                return self.send(413, "too big\n", "text/plain")
            f = {k: v[0].strip() for k, v in parse_qs(self.rfile.read(n).decode()).items()}
            p = urlparse(self.path).path
            try:
                if p.endswith("/add") and not p.endswith("page/add"):
                    opts = {"mode": f["mode"]} if f.get("mode") in ("auto", "grab", "screen") else {}
                    name = add_stream(path, f.get("start", ""), url=f.get("url") if not f.get("page") else None,
                                      page=f.get("page") or None,
                                      end=None if f.get("duration") else f.get("end"),
                                      duration=f.get("duration") or None, name=f.get("name") or None, opts=opts)
                    return self.redirect(msg=f"Scheduled {name}")
                if p.endswith("page/add"):
                    add_page(path, f.get("name", ""), f.get("url", ""))
                    return self.redirect(msg=f"Saved page {f.get('name')}")
                if p.endswith("page/remove"):
                    remove_page(path, f.get("name", ""))
                    return self.redirect(msg=f"Deleted page {f.get('name')}")
                if p.endswith("/remove"):
                    remove_stream(path, f.get("name", ""))
                    return self.redirect(msg=f"Removed {f.get('name')}")
            except (ValueError, argparse.ArgumentTypeError) as ex:
                return self.redirect(err=str(ex))
            self.send(404, "not found\n", "text/plain")

    return H


def tailscale_ip():
    try:
        r = subprocess.run(["tailscale", "ip", "-4"], capture_output=True, text=True, timeout=10)
        return r.stdout.split()[0] if r.returncode == 0 and r.stdout.strip() else None
    except (OSError, subprocess.TimeoutExpired):
        return None


def parse_bind(bind):
    """'auto' (tailscale address), 'ADDR', 'ADDR:PORT' or '[v6]:PORT'; default port 8787."""
    bind = bind or "auto"
    host, port = bind, 8787
    if bind.startswith("[") or bind.count(":") == 1:
        host, _, p = bind.rpartition(":")
        port = int(p) if p.isdigit() else 8787
    host = host.strip("[]") or "auto"
    if host == "auto":
        host = tailscale_ip()
        if not host:
            raise SystemExit("couldn't get the tailscale address (is tailscale up?); "
                             "pass --bind ADDR:PORT, e.g. your LAN address or 127.0.0.1")
    if host in ("0.0.0.0", "::"):
        log.warning("web: listening on all interfaces; clients from public IPs are still refused")
    return host, port


def serve_web(bind, path, rec_dir, retry=True):
    """Serve until the process exits. Keeps retrying the bind (tailscale may come up after us)."""
    import socket
    from http.server import ThreadingHTTPServer

    warned = False
    while not STOP.is_set():
        try:
            host, port = parse_bind(bind)
            cls = type("Server", (ThreadingHTTPServer,), {
                "address_family": socket.AF_INET6 if ":" in host else socket.AF_INET, "daemon_threads": True})
            srv = cls((host, port), make_handler(Path(path).expanduser(), rec_dir))
        except (OSError, SystemExit, ValueError) as ex:
            if not retry:
                raise SystemExit(f"web: {ex}")
            if not warned:
                log.error("web: can't start (%s); retrying every 30 s", ex)
                warned = True
            STOP.wait(30)
            continue
        log.info("web page on http://%s/", f"[{host}]:{port}" if ":" in host else f"{host}:{port}")
        threading.Thread(target=lambda: (STOP.wait(), srv.shutdown()), daemon=True).start()
        srv.serve_forever()
        return


def cmd_web(a):
    serve_web(a.bind, a.file, Path(a.dir).expanduser(), retry=False)


class ArgError(Exception):
    pass


class Parser(argparse.ArgumentParser):
    raise_errors = False

    def error(self, message):
        if self.raise_errors:
            raise ArgError(message)
        super().error(message)


def build_parser():
    fmt = argparse.ArgumentDefaultsHelpFormatter
    p = Parser(description="Record a live stream from a web page.", formatter_class=fmt)
    sub = p.add_subparsers(dest="cmd", required=True)

    def browser_opts(sp):
        sp.add_argument("url")
        sp.add_argument("--profile", default="~/.streamrec/profile", help="browser profile (keeps logins)")
        sp.add_argument("--extension", help="unpacked extension dir to load, e.g. uBlock Origin Lite")
        sp.add_argument("--show", action="store_true", help="show the browser window (grab/probe)")
        sp.add_argument("--find-timeout", type=int, default=90, help="seconds to get the video going")

    def sched_file(sp):
        sp.add_argument("--file", default=DEFAULT_SCHEDULE, help="schedule file")
        sp.add_argument("--dir", default=DEFAULT_DIR, help="recordings folder")

    r = sub.add_parser("record", formatter_class=fmt)
    browser_opts(r)
    r.add_argument("--start", default="now", help="'now', 'HH:MM' or ISO datetime")
    g = r.add_mutually_exclusive_group(required=True)
    g.add_argument("--end", help="'HH:MM' or ISO datetime (pad it - the recorder keeps retrying until then)")
    g.add_argument("--duration", type=parse_duration, help="e.g. 3h, 2h30m")
    r.add_argument("--mode", choices=["auto", "grab", "screen"], default="auto")
    r.add_argument("--out", help="output dir (default recordings/<date>-<host>)")
    r.add_argument("--part", type=parse_part, default="30m", help="length of each part file, e.g. 30s, 5m, 30m")
    r.add_argument("--stall", type=int, default=60, help="seconds without progress before restarting")
    r.add_argument("--retry", type=int, default=15, help="seconds to wait between attempts")
    r.add_argument("--lead", type=int, default=3, help="minutes before --start to begin trying")
    r.add_argument("--grab-tries", type=int, default=3, help="auto: failed sniffs before screen mode")
    r.add_argument("--keep-browser", action="store_true", help="grab: keep page open while recording")
    r.add_argument("--rclone", help="upload parts as they finish, e.g. gdrive:streams")
    r.add_argument("--size", default="1920x1080", help="screen: virtual display size")
    r.add_argument("--fps", type=int, default=30, help="screen: frame rate")
    r.add_argument("--vcodec", default="libx264", help="screen: e.g. libx264, h264_vaapi, h264_qsv")
    r.add_argument("--crf", type=int, default=23, help="screen: libx264 quality (lower = better)")
    r.add_argument("--display", type=int, default=99, help="screen: Xvfb display number")
    r.set_defaults(fn=cmd_record)
    p.record = r

    pr = sub.add_parser("probe", help="test a page: find playlists / check playback")
    browser_opts(pr)
    pr.set_defaults(fn=cmd_probe)

    lg = sub.add_parser("login", help="open a visible browser with the recorder profile")
    browser_opts(lg)
    lg.set_defaults(fn=cmd_login)

    j = sub.add_parser("join", help="join parts into one file")
    j.add_argument("dir")
    j.add_argument("-o", "--output")
    j.set_defaults(fn=cmd_join)

    sc = sub.add_parser("schedule", help="run all recordings from a TOML schedule file")
    sc.add_argument("file", nargs="?", default=DEFAULT_SCHEDULE)
    sc.add_argument("--dir", default=DEFAULT_DIR, help="where each recording's folder goes")
    sc.add_argument("--check", action="store_true", help="validate the file and list the streams")
    sc.add_argument("--web", nargs="?", const="auto", metavar="ADDR[:PORT]",
                    help="also serve the web page ('auto' = this machine's tailscale address, port 8787)")
    sc.set_defaults(fn=cmd_schedule)

    ls = sub.add_parser("list", help="show scheduled streams and their status", formatter_class=fmt)
    sched_file(ls)
    ls.add_argument("--days", type=int, default=7, help="show finished streams from the last N days")
    ls.add_argument("--all", action="store_true", help="show every finished stream")
    ls.add_argument("--pages", action="store_true", help="also list saved pages")
    ls.set_defaults(fn=cmd_list)

    ad = sub.add_parser("add", help="add a stream to the schedule", formatter_class=fmt,
                        description="Add a [[stream]] entry. Comments and layout of the file are kept.")
    ad.add_argument("target", help="page URL, or the name of a saved page")
    ad.add_argument("--start", required=True, help="'now', 'HH:MM' (next occurrence) or 'YYYY-MM-DDTHH:MM'")
    g = ad.add_mutually_exclusive_group(required=True)
    g.add_argument("--end", help="'HH:MM' (after start) or 'YYYY-MM-DDTHH:MM'")
    g.add_argument("--duration", help="e.g. 2h, 2h30m")
    ad.add_argument("--name", help="folder name (default: <date>-<site or page>)")
    ad.add_argument("--mode", choices=["auto", "grab", "screen"])
    ad.add_argument("--part", help="part length, e.g. 5m")
    ad.add_argument("--set", action="append", metavar="KEY=VALUE", help="any other record option, e.g. lead=10")
    sched_file(ad)
    ad.set_defaults(fn=cmd_add)

    rm = sub.add_parser("remove", help="remove a stream from the schedule (files are kept)", formatter_class=fmt)
    rm.add_argument("name")
    sched_file(rm)
    rm.set_defaults(fn=cmd_remove)

    pg = sub.add_parser("page", help="saved stream pages: list | add NAME URL | remove NAME", formatter_class=fmt)
    pg.add_argument("action", choices=["list", "add", "remove"], nargs="?", default="list")
    pg.add_argument("name", nargs="?")
    pg.add_argument("url", nargs="?")
    sched_file(pg)
    pg.set_defaults(fn=cmd_page)

    w = sub.add_parser("web", help="serve the phone page (also: schedule --web)", formatter_class=fmt)
    w.add_argument("--bind", default="auto", help="ADDR[:PORT]; 'auto' = tailscale address, port 8787")
    sched_file(w)
    w.set_defaults(fn=cmd_web)
    return p


def main():
    p = build_parser()
    a = p.parse_args()
    if a.cmd == "page" and ((a.action == "add" and not (a.name and a.url)) or (a.action == "remove" and not a.name)):
        p.exit(2, "usage: page add NAME URL | page remove NAME\n")
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
    for s in (signal.SIGINT, signal.SIGTERM):
        signal.signal(s, lambda *_: (log.info("stopping..."), STOP.set(), KICK.set()))
    a.fn(a)


if __name__ == "__main__":
    main()
