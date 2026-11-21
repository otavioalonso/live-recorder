#!/usr/bin/env bash
# streamrec installer for Arch Linux.
#
#   ./install-arch.sh               install / update (keeps your schedule and recordings)
#   ./install-arch.sh --enable      ...and start the scheduler service now and at boot
#   ./install-arch.sh --uninstall   remove program + service (keeps schedule, profile, recordings)
#
# Run as your normal user from the folder containing streamrec.py; it uses sudo for pacman.
set -euo pipefail

NAME=streamrec
SRC_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
APP_DIR="$HOME/.local/share/$NAME"          # script + Python venv + Chromium
BIN="$HOME/.local/bin/$NAME"                # the `streamrec` command
CONF_DIR="$HOME/.config/$NAME"
SCHEDULE="$CONF_DIR/schedule.toml"
REC_DIR="$HOME/recordings"
UNIT_DIR="$HOME/.config/systemd/user"
UNIT="$UNIT_DIR/$NAME.service"

PACKAGES=(python ffmpeg xorg-server-xvfb libpulse rclone
          nss at-spi2-core libxkbcommon alsa-lib libxcomposite libxdamage libxrandr mesa)

ENABLE=0 UNINSTALL=0 SKIP_PACMAN=0
for arg in "$@"; do
  case "$arg" in
    --enable) ENABLE=1 ;;
    --uninstall) UNINSTALL=1 ;;
    --skip-pacman) SKIP_PACMAN=1 ;;
    -h|--help) sed -n '2,8p' "$0"; exit 0 ;;
    *) echo "unknown option: $arg" >&2; exit 1 ;;
  esac
done

say()  { printf '\033[1;32m==>\033[0m %s\n' "$*"; }
warn() { printf '\033[1;33m==> warning:\033[0m %s\n' "$*"; }
die()  { printf '\033[1;31m==> error:\033[0m %s\n' "$*" >&2; exit 1; }
have_user_systemd() { systemctl --user show-environment >/dev/null 2>&1; }

[[ $EUID -ne 0 ]] || die "run this as your normal user, not root (it calls sudo itself)"

# ------------------------------------------------------------------ uninstall
if (( UNINSTALL )); then
  if have_user_systemd; then
    systemctl --user disable --now "$NAME.service" 2>/dev/null || true
  fi
  rm -f "$UNIT" "$BIN"
  rm -rf "$APP_DIR"
  have_user_systemd && systemctl --user daemon-reload || true
  say "removed. kept: $CONF_DIR, ~/.streamrec (browser profile), $REC_DIR"
  exit 0
fi

# ------------------------------------------------------------------ install
[[ -f "$SRC_DIR/streamrec.py" ]] || die "streamrec.py not found next to this installer"

if (( ! SKIP_PACMAN )); then
  command -v pacman >/dev/null || die "pacman not found - this installer is for Arch (use --skip-pacman to skip)"
  say "installing system packages (sudo)"
  sudo pacman -S --needed --noconfirm "${PACKAGES[@]}"
fi

say "setting up Python environment in $APP_DIR"
mkdir -p "$APP_DIR"
[[ -x "$APP_DIR/venv/bin/python" ]] || python -m venv "$APP_DIR/venv"
"$APP_DIR/venv/bin/pip" install --quiet --upgrade pip playwright

say "downloading Playwright's Chromium (Playwright may warn Arch isn't 'officially supported' - that's fine)"
PLAYWRIGHT_BROWSERS_PATH="$APP_DIR/browsers" "$APP_DIR/venv/bin/playwright" install chromium

install -m 755 "$SRC_DIR/streamrec.py" "$APP_DIR/streamrec.py"

say "creating command $BIN"
mkdir -p "$(dirname "$BIN")"
cat > "$BIN" <<EOF
#!/bin/sh
export PLAYWRIGHT_BROWSERS_PATH="$APP_DIR/browsers"
exec "$APP_DIR/venv/bin/python" "$APP_DIR/streamrec.py" "\$@"
EOF
chmod 755 "$BIN"

mkdir -p "$CONF_DIR" "$REC_DIR"
if [[ ! -f "$SCHEDULE" ]]; then
  if [[ -f "$SRC_DIR/schedule.example.toml" ]]; then
    cp "$SRC_DIR/schedule.example.toml" "$SCHEDULE"
  else
    printf '[defaults]\nmode = "auto"\npart = "5m"\n\n# [[stream]]\n# url = "https://..."\n# start = 2026-12-01T21:00:00\n# end = 2026-12-01T23:00:00\n' > "$SCHEDULE"
  fi
  say "created schedule file $SCHEDULE (example entries - edit them)"
else
  say "keeping existing schedule file $SCHEDULE"
fi

say "installing systemd user service $UNIT"
mkdir -p "$UNIT_DIR"
cat > "$UNIT" <<EOF
[Unit]
Description=$NAME scheduler (records streams listed in $SCHEDULE)

[Service]
# --web: phone page on the tailscale address, port 8787 (retries until tailscale is up)
ExecStart=$BIN schedule $SCHEDULE --dir $REC_DIR --web
Restart=always
RestartSec=10
KillMode=mixed
TimeoutStopSec=90

[Install]
WantedBy=default.target
EOF

if have_user_systemd; then
  systemctl --user daemon-reload
  if (( ENABLE )); then
    systemctl --user enable --now "$NAME.service"
    if [[ "$(loginctl show-user "$USER" -p Linger --value 2>/dev/null)" != "yes" ]]; then
      say "enabling linger so the service runs while you're logged out (may ask for your password)"
      loginctl enable-linger "$USER" || warn "could not enable linger; run: loginctl enable-linger $USER"
    fi
  fi
else
  warn "no systemd user session found - service installed but not reloaded/started"
fi

# ------------------------------------------------------------------ checks
command -v pactl >/dev/null && pactl info >/dev/null 2>&1 \
  || warn "no audio server running - screen mode needs one: sudo pacman -S pipewire pipewire-pulse wireplumber"
case ":$PATH:" in *":$HOME/.local/bin:"*) ;; *)
  warn "$HOME/.local/bin is not in your PATH - add it, or call $BIN directly" ;;
esac
"$BIN" schedule "$SCHEDULE" --check >/dev/null 2>&1 \
  || warn "schedule file has errors: run '$NAME schedule --check'"

TS_IP=$(tailscale ip -4 2>/dev/null | head -1 || true)
cat <<EOF

$(say "done")
  test a page:     $NAME probe URL --show
  quick test:      $NAME record URL --duration 5m --part 1m
  edit schedule:   \$EDITOR $SCHEDULE      (check: $NAME schedule --check)
  or:              $NAME add URL --start 21:00 --duration 2h   ($NAME list / remove / page)
  phone page:      http://${TS_IP:-<tailscale-ip>}:8787/
  service:         systemctl --user $( ((ENABLE)) && echo status || echo "enable --now") $NAME
  service log:     journalctl --user -u $NAME -f
  recordings:      $REC_DIR/<name>/        (join: $NAME join DIR)
EOF
