#!/bin/bash
# IRB timing - install (or reinstall) on a Raspberry Pi.
# In the Pi's Terminal:
#   curl -fsSL https://raw.githubusercontent.com/Lifesavingequipment/official-app/main/pi_install.sh | bash
# Safe to run again: results and settings in ~/IRB_timing/timing_data are never touched.
set -e
URL="${IRB_UPDATE_URL:-https://raw.githubusercontent.com/Lifesavingequipment/official-app/main/}"
DIR="${IRB_DIR:-$HOME/IRB_timing}"
ME="$(id -un)"
say() { printf '\n\033[1;34m== %s\033[0m\n' "$*"; }
ask() {   # ask a yes/no question even when this script is piped from curl
    local a=""
    if [ -n "$IRB_ANSWER" ]; then a="$IRB_ANSWER"; elif [ -r /dev/tty ]; then read -r -p "$1 [Y/n] " a < /dev/tty || a=""; fi
    case "$a" in n|N|no|No) return 1;; *) return 0;; esac
}

say "1/5  Installing what the app needs (a minute or two)"
sudo apt-get update -qq
sudo apt-get install -y -qq python3 python3-serial curl
sudo usermod -aG dialout "$ME"          # lets the app talk to the Pico over USB

say "2/5  Downloading the app into $DIR"
mkdir -p "$DIR/Old"
cd "$DIR"
t=$(date +%s)
curl -fsSL "${URL}VERSION.json?t=$t" -o VERSION.json.new
curl -fsSL "${URL}officials_app.py?t=$t" -o officials_app.py.new
want=$(python3 -c "import json;print(json.load(open('VERSION.json.new'))['sha256'])")
got=$(sha256sum officials_app.py.new | cut -d' ' -f1)
if [ "$want" != "$got" ]; then
    rm -f officials_app.py.new VERSION.json.new
    echo "The download was damaged - nothing was changed. Check the internet and run this again."
    exit 1
fi
[ -f officials_app.py ] && cp officials_app.py "Old/officials_app_$(date +%Y%m%d_%H%M)_before_install.py"
mv officials_app.py.new officials_app.py
ver=$(python3 -c "import json;print(json.load(open('VERSION.json.new'))['app'])")
rm -f VERSION.json.new
curl -fsSL "${URL}main.py?t=$t" -o pico_main.py || true      # spare copy of the timing box program
echo "App v$ver downloaded and checked."

say "3/5  Starting the app automatically whenever the Pi is on"
sudo tee /etc/systemd/system/irb-timing.service > /dev/null <<EOF
[Unit]
Description=IRB timing app
After=network-online.target
Wants=network-online.target

[Service]
User=$ME
SupplementaryGroups=dialout
WorkingDirectory=$DIR
Environment=IRB_LAUNCHER=1
Environment=PYTHONUNBUFFERED=1
ExecStart=/usr/bin/python3 $DIR/officials_app.py
Restart=always
RestartSec=2

[Install]
WantedBy=multi-user.target
EOF
sudo systemctl daemon-reload
sudo systemctl enable irb-timing.service > /dev/null 2>&1
sudo systemctl restart irb-timing.service

say "4/5  The Pi's own screen"
if ask "Open the timing screen full-screen on this Pi's monitor every time it starts?"; then
    B=$(command -v chromium-browser || command -v chromium || true)
    if [ -z "$B" ]; then sudo apt-get install -y -qq chromium-browser || sudo apt-get install -y -qq chromium; B=$(command -v chromium-browser || command -v chromium); fi
    mkdir -p "$HOME/.config/autostart"
    cat > "$HOME/.config/autostart/irb-screen.desktop" <<EOF
[Desktop Entry]
Type=Application
Name=IRB timing screen
Exec=sh -c 'sleep 6; exec $B --kiosk --noerrdialogs --disable-infobars --no-first-run --password-store=basic --check-for-update-interval=31536000 http://localhost:8080'
X-GNOME-Autostart-enabled=true
EOF
    command -v raspi-config > /dev/null && sudo raspi-config nonint do_blanking 1 || true   # screen never goes blank
    echo "Done. To leave full-screen: Alt+F4.  To turn it off: delete ~/.config/autostart/irb-screen.desktop"
else
    rm -f "$HOME/.config/autostart/irb-screen.desktop"
    echo "Skipped - open a browser at http://localhost:8080 when you want it."
fi
# a desktop icon, either way
if [ -d "$HOME/Desktop" ]; then
    B=$(command -v chromium-browser || command -v chromium || true)
    if [ -n "$B" ]; then        # --password-store=basic: no "Choose password for new keyring" box
        cat > "$HOME/Desktop/IRB-timing.desktop" <<EOF
[Desktop Entry]
Type=Application
Name=IRB timing
Exec=$B --password-store=basic --no-first-run http://localhost:8080
Icon=web-browser
Terminal=false
EOF
        chmod +x "$HOME/Desktop/IRB-timing.desktop"
    else
        cat > "$HOME/Desktop/IRB-timing.desktop" <<EOF
[Desktop Entry]
Type=Link
Name=IRB timing
URL=http://localhost:8080
Icon=web-browser
EOF
    fi
fi

say "5/5  Checking"
ok=""
for i in $(seq 1 20); do
    if curl -fs http://localhost:8080/api/state > /dev/null 2>&1; then ok=1; break; fi
    sleep 1
done
IP=$(hostname -I 2>/dev/null | awk '{print $1}')
if [ -n "$ok" ]; then
    echo "The app is running:  on this Pi  http://localhost:8080"
    [ -n "$IP" ] && echo "                     phones/tablets on the same Wi-Fi  http://$IP:8080"
    echo
    echo "Restart the Pi once now (sudo reboot) so everything starts by itself."
else
    echo "The app didn't answer yet. See what it says with:  journalctl -u irb-timing -n 30"
fi
