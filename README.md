# streamrec

Records a live stream from a web page. If the stream breaks, it saves what it has and starts again.

## Install

### Linux (Ubuntu or Debian), which covers the server and both recording modes

```bash
sudo apt install ffmpeg xvfb pulseaudio-utils rclone   # use pipewire-pulse or pulseaudio for audio
pip install playwright        # add --break-system-packages, or use a venv
playwright install --with-deps chromium
```

### macOS or Windows

Grab mode works if you have Python, ffmpeg and `pip install playwright && playwright install chromium`.
Screen mode needs Linux, so on a Mac run it in Docker:

```bash
docker build -t streamrec .
docker run --rm -v "$PWD/recordings:/home/rec/recordings" streamrec record URL --duration 2h
```

## Testing locally

```bash
python3 streamrec.py probe URL --show       # do this while a stream is live
```

The `probe` command opens the page, clicks through the ads until the video plays, and then tells you:
- whether it found a stream playlist. If it did, `--mode grab` will work, in original quality with almost no CPU.
- otherwise, that you need `--mode screen`.

The leaving-it-on default is `--mode auto`, which tries grab first and switches to screen recording if that fails.

Quick test recordings:

```bash
python3 streamrec.py record URL --duration 10m --part 2m          # parts every 2 min
python3 streamrec.py record URL --duration 10m --mode screen      # Linux / Docker
python3 streamrec.py join recordings/<folder>                     # -> joined.mkv
```

To test recovery, cut your network for a minute during a test recording, or kill the `ffmpeg` process.
A new `runNNN_*.ts` part should appear after it recovers.

## Real use

```bash
# start at 21:00, keep trying until 01:30, upload parts to Google Drive as they finish
python3 streamrec.py record URL --start 21:00 --end 01:30 --rclone gdrive:streams
```

- **Set a generous end time.** Until then the recorder keeps restarting whenever the stream drops, and it waits if the stream starts late.
- **Keep it running after you log out:** run it inside `tmux`, or use
  `systemd-run --user --unit=rec1 python3 /path/streamrec.py record URL --start ... --end ...`
- **Logins and cookie banners:** run `python3 streamrec.py login URL` once. The recorder reuses that browser profile.
- **Ad blocker (recommended for ad-heavy sites):** download uBlock Origin Lite, unzip it, and add
  `--extension /path/to/uBOLite`.
- **On an Intel mini PC:** `--vcodec h264_vaapi` makes screen mode use the hardware video encoder and frees up the CPU.
  You may also need ffmpeg's `-vaapi_device` option. Stick with libx264 until that's set up.

## Scheduling many streams (systemd)

A single always-on service reads a schedule file and runs each recording at its time.

```bash
mkdir -p ~/streamrec ~/.config/streamrec ~/.config/systemd/user
cp streamrec.py ~/streamrec/
cp schedule.example.toml ~/.config/streamrec/schedule.toml    # then edit it
cp streamrec.service ~/.config/systemd/user/
systemctl --user daemon-reload
systemctl --user enable --now streamrec
loginctl enable-linger $USER          # keep it running when you're logged out
```

Day-to-day use:
- Edit `~/.config/streamrec/schedule.toml` and save. The scheduler re-reads it every 15 s, so there's nothing to restart.
  Or use the commands below, or the web page.
- `python ~/streamrec/streamrec.py schedule --check` checks the file and lists upcoming streams.
- `streamrec list` shows each stream's status: upcoming, recording, retrying, done or missed, with parts, size and restarts.
- `journalctl --user -u streamrec -f` shows the scheduler's log: launches, restarts, finished recordings.
- Each recording gets its own folder under `~/recordings/<name>/`, with `recorder.log` and `console.log` inside.

How it behaves:
- **Start:** it launches each recording `lead` minutes before its start time.
- **Crashes:** if a recorder process dies before its end time, it's restarted. The wait between attempts starts at 10 s and grows to at most 5 min.
  The new run's parts go into the same folder, with the run number continuing.
- **End:** it stops each recording at its end time, and kills it if it's still running 2 minutes later.
- **Overlapping streams:** these work. Each one gets its own virtual display, audio output and copy of your login profile.
- **Errors in the file:** if you save the file with a typo, the scheduler keeps using the previous version and logs the error.
- **Removing a stream:** a running stream that you delete from the file is stopped.
- **Changing an end time:** if you extend a stream's end time after it finished, it records again.

### Editing the schedule from the command line

```bash
streamrec add https://example.com/live --start 2026-11-30T21:00 --end 23:30
streamrec add "channel 1" --start 21:00 --duration 2h --mode screen --set lead=10
streamrec remove 20261130-2100-example.com      # stops it if running; files stay on disk
streamrec page add "channel 1" https://example.net/live/1
streamrec page list
```

`add` takes a URL or the name of a saved page. `--start HH:MM` means the next time that clock time comes round,
and it's written to the file as a full date. Any `record` option can be given with `--set key=value`.

Every edit is checked with the same loader the scheduler uses before the file is replaced, so a bad option or a past
end time is refused instead of saved. Your comments and layout are kept, and the previous version is saved as
`schedule.toml.bak`. Removing an entry never deletes recordings.

### Web page (phone)

`streamrec schedule --web` (the systemd unit has this on) also serves a small page for the schedule, on this machine's
Tailscale address at port 8787. Open `http://<tailscale-ip>:8787/` on your phone and add it to the home screen.
Standalone: `streamrec web [--bind ADDR:PORT]`.

From the page you can see what's live, upcoming and past (state, parts, size, restarts, last data, logs),
schedule a URL or a saved page with date/time pickers, stop or remove entries, and manage saved pages.

Keep it private:
- **Don't port-forward it.** It has no login. It only answers clients on loopback, Tailscale (100.64.0.0/10) and private LAN
  addresses, and refuses public IPs even if something forwards a port to it.
- By default it binds to the Tailscale address only. If Tailscale isn't up yet it retries every 30 s.
  Use `--web 192.168.1.10:8787` to bind a LAN address instead.
- For HTTPS (and a full install prompt on Android), bind it to `--web 127.0.0.1:8787` and run
  `tailscale serve --bg 8787`, which makes it `https://<machine>.<tailnet>.ts.net/` inside your tailnet only.

## Output

```
recordings/20261121-2100-example.com/
  run001_000.ts  run001_001.ts  ...   # one run = one uninterrupted ffmpeg session
  run002_000.ts  ...                  # after a restart
  recorder.log   ffmpeg.log
```

Each `.ts` part plays on its own, even if it was cut off. `join` puts the parts together in order.
If the site switched stream quality between runs and `join` complains, play the parts separately or re-encode them.

## Limits

- **DRM:** in screen mode the video shows up black. Nothing in this setup can record it.
- **Gaps:** each restart loses a few seconds to tens of seconds. A live stream can't be rewound.
- **Screen mode and a stalled stream:** screen mode keeps recording whatever is on screen,
  so if the stream stays down for a long time you'll get a stretch of the player's waiting screen.
