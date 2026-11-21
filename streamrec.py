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
"""
import argparse
import datetime as dt
import logging
import os
import re
import shutil
import signal
import subprocess
import sys
import threading
import time
from pathlib import Path
from urllib.parse import urlparse

log = logging.getLogger("streamrec")
STOP = threading.Event()

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
        self.page.goto(url, wait_until="domcontentloaded", timeout=60_000)
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
def grab_cmd(a, url, h, pattern):
    hdr = "".join(f"{k}: {v}\r\n" for k, v in h.items() if k.lower() in FWD_HEADERS)
    return ["ffmpeg", "-hide_banner", "-loglevel", "warning", "-nostdin",
            "-user_agent", h.get("user-agent", "Mozilla/5.0"),
            *(["-headers", hdr] if hdr else []),
            "-rw_timeout", "20000000",
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
        if not b.open_and_play(a.url, a.find_timeout):
            return "no playlist found"
        b.page.wait_for_timeout(4000)  # let the master playlist / variants arrive
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
    subprocess.run(["ffmpeg", "-hide_banner", "-loglevel", "warning", "-f", "concat", "-safe", "0",
                    "-i", str(lst), "-c", "copy", out], check=True)
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
    defaults = data.get("defaults", {})
    jobs = {}
    for i, entry in enumerate(data.get("stream", []), 1):
        j = {**defaults, **entry}
        if "url" not in j or "start" not in j or not ("end" in j or "duration" in j):
            raise ValueError(f"stream #{i}: needs url, start, and end or duration")
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
        name = re.sub(r"[^\w.-]+", "_", str(name))
        if name in jobs:
            raise ValueError(f"duplicate stream name {name!r}")
        jobs[name] = {"name": name, "url": url, "start": start, "end": end, "opts": j}
    return jobs


class Running:
    def __init__(self):
        self.proc = None
        self.display = None
        self.fails = 0
        self.next_try = 0.0
        self.done = False
        self.end = None


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
    cmd = [sys.executable, str(Path(__file__).resolve()), "record", job["url"],
           "--start", job["start"].isoformat(), "--end", job["end"].isoformat(),
           "--out", str(out), "--profile", str(prof), "--display", str(rt.display)]
    for k, v in o.items():
        if k in SCHED_ONLY or v is False:
            continue
        cmd.append("--" + k.replace("_", "-"))
        if v is not True:
            cmd.append(str(v))
    if o.get("inhibit_sleep") and shutil.which("systemd-inhibit"):
        cmd = ["systemd-inhibit", "--what=sleep:idle", "--who=streamrec", f"--why=recording {name}"] + cmd
    log.info("[%s] launching (until %s)", name, f"{job['end']:%Y-%m-%d %H:%M}")
    console = open(out / "console.log", "ab")
    rt.proc = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=console, stderr=console,
                               start_new_session=True)


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
        STOP.wait(15)

    for name, rt in state.items():
        if rt.proc:
            kill_group(rt.proc, name)
    log.info("scheduler stopped")


def main():
    p = argparse.ArgumentParser(description="Record a live stream from a web page.",
                                formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)

    def browser_opts(sp):
        sp.add_argument("url")
        sp.add_argument("--profile", default="~/.streamrec/profile", help="browser profile (keeps logins)")
        sp.add_argument("--extension", help="unpacked extension dir to load, e.g. uBlock Origin Lite")
        sp.add_argument("--show", action="store_true", help="show the browser window (grab/probe)")
        sp.add_argument("--find-timeout", type=int, default=90, help="seconds to get the video going")

    r = sub.add_parser("record", formatter_class=argparse.ArgumentDefaultsHelpFormatter)
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
    sc.add_argument("file", nargs="?", default="~/.config/streamrec/schedule.toml")
    sc.add_argument("--dir", default="~/recordings", help="where each recording's folder goes")
    sc.add_argument("--check", action="store_true", help="validate the file and list the streams")
    sc.set_defaults(fn=cmd_schedule)

    a = p.parse_args()
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
    for s in (signal.SIGINT, signal.SIGTERM):
        signal.signal(s, lambda *_: (log.info("stopping..."), STOP.set()))
    a.fn(a)


if __name__ == "__main__":
    main()
