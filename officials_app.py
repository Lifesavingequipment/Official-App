#!/usr/bin/env python3
"""
IRB finish timing - officials' app  v1.2

Runs on the laptop now and on the Raspberry Pi 5 later (same file, no edits).
- Finds the Pico on USB by itself (close Thonny first - only one program can use the Pico).
- Shows a simple officials' screen in a web browser:
    this computer:      http://localhost:8080
    tablet / phone:     http://<this computer's address>:8080  (same Wi-Fi; address printed at start)
- Can load the heat draw (crew names and lanes) from a public LiveHeats event.
- Keeps its own copy of every result and officials' change in the timing_data folder
  (second copy - the Pico keeps its own rolling copy too).

Needs: Python 3.8+ and pyserial   (install once:  pip install pyserial)
Start:  python officials_app.py
"""

import json, os, re, sys, threading, time, socket, csv, io, urllib.request, urllib.parse, secrets, math, shutil, glob, hashlib, base64, zipfile, platform, subprocess
from collections import deque
from datetime import datetime, timedelta
from http.server import ThreadingHTTPServer, BaseHTTPRequestHandler

try:
    import serial
    import serial.tools.list_ports
except ImportError:
    print("pyserial is not installed. Run:  pip install pyserial   then start this again.")
    input("Press Enter to close...")
    sys.exit(1)

APP_VERSION = "1.6.1"
HTTP_PORT = 8080
PICO_PORT = None          # None = find the Pico automatically. Or e.g. "COM10" / "/dev/ttyACM0"
PICO_VID = 0x2E8A         # Raspberry Pi USB vendor ID

BASE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(BASE, "timing_data")
os.makedirs(DATA, exist_ok=True)
HIST_FILE = os.path.join(DATA, "history.jsonl")
SETTINGS_FILE = os.path.join(DATA, "settings.json")
DRAW_FILE = os.path.join(DATA, "liveheats_draw.json")
FLAGS_FILE = os.path.join(DATA, "race_flags.json")
ROLES_FILE = os.path.join(DATA, "crew_roles.json")     # roles team managers set where LiveHeats had none
PROGRAM_FILE = os.path.join(DATA, "program.json")       # the running order of heats for the day
TEMPLATES_FILE = os.path.join(DATA, "templates.json")   # saved programs to reuse     # which races are confirmed / entered in LiveHeats
LIVEHEATS_API = "https://liveheats.com/api/graphql"
# where updates come from (the club's GitHub repository). Only the Master can install one.
UPDATE_URL = os.environ.get("IRB_UPDATE_URL", "https://raw.githubusercontent.com/Lifesavingequipment/official-app/main/")
# with a key (a read-only GitHub token) updates come through the GitHub API instead, which also works for a private repository
UPDATE_API = os.environ.get("IRB_UPDATE_API", "https://api.github.com/repos/Lifesavingequipment/Official-App/contents/")
UPD_KEY = {"v": ""}
OLD_DIR = os.path.join(BASE, "Old")

# IRB events and their usual number of legs (SLSA Surf Sports Manual, 38th ed.)
EVENTS = [
    {"id": "", "name": "Not set", "legs": 0},
    {"id": "tube", "name": "Rescue Tube", "legs": 1},
    {"id": "rescue", "name": "Rescue", "legs": 1},
    {"id": "mass", "name": "Mass Rescue", "legs": 2},
    {"id": "teams", "name": "Teams Rescue", "legs": 2},
    {"id": "relay", "name": "Relay", "legs": 4},
]

DEFAULT_EVENTS = [dict(e) for e in EVENTS]
LOGO_FILE = os.path.join(DATA, "logo.png")
BRAND = {"club": "", "event": ""}            # shown on the screens, join card and guides
OWNER = {"pin": "", "open_until": 0.0}      # owner lock for hire kits: updates and advanced settings
SETUP = {"done": True}                       # False = show the Get started steps (fresh install, new event)
DEFAULT_KIT = ("Laptop and charger\nTiming box (Pico) with USB cable\nLane buttons and cables\nStarter SET and GO buttons\n"
               "FINISH button and cable\nBattery and charger\nWi-Fi router and power\nTV or screen cable (optional)\n"
               "Printed join cards and role guides\nUSB stick with an IRB_backup folder")
KIT = {"text": DEFAULT_KIT}
FIREWALL = {"state": None, "busy": False}    # Windows only: is the rule that lets phones in there?
FW_RULE = "IRB_timing_app"

lock = threading.Lock()
S = {
    "connected": False, "port": None, "fw": None, "lanes": [], "min_leg_s": 15,
    "state": "UNKNOWN", "race": 0, "faults": [], "go_at": None,
    "live": {}, "results": None, "at_prompt": False,
    "event": "", "race_event": None, "app_start": False,
    "heat": None, "race_heat": None,      # chosen LiveHeats heat; race_heat is fixed at GO
    "ties": False, "has_test": False,     # Pico v2.7 features
    "test": False, "test_seen": [], "last_test": None, "faults_racing": False,
    "test_count": {}, "test_last": None, "test_clash": [],             # every press during the button test
    "beat": False, "batt": None, "batt_at": None,   # Pico v2.8 features
    "race_go_wall": None,                            # computer clock time of GO (for video)
    "practice": False, "backup": None,
}
last_rx = 0.0             # when the Pico last sent anything
# Access levels. The timing computer itself is always Master. An official's phone asks for access
# with their name, shows a 3-digit code, and the Master approves it with a level. Everything ends
# when the Master closes the event (or overnight). Team Manager and Results screen need nothing.
ROLES = ("master", "admin", "starter", "marshal")
ROLE_NAME = {"master": "Timing desk", "admin": "Referee", "starter": "Starter", "marshal": "Marshal", "viewer": "Viewer"}
PINS = {"master": ""}     # optional PIN for a backup Master phone ("" = off)
officials = {}            # device token -> {"name", "role", "since", "seen"}
requests_ = {}            # device token -> {"name", "code", "at"} waiting for the Master
regulars = {}             # lower-case name -> {"name", "role"}: officials the Master remembers
NET = {"ssid": "", "pass": "", "addr": ""}   # Wi-Fi for the join card; addr overrides the app address
access_day = [""]         # the day the approvals belong to
REQUEST_MINS = 10
flags = {}                # "race" -> {"confirmed": time, "entered": time}
raced = {}                # LiveHeats heat id -> race number it was run as
clash_skip = [None, 0.0]  # button whose next press belongs to a together-press
draw = None               # LiveHeats draw (compact), kept on disk for use without internet
last_go_sent = 0.0        # guards against a double-tap on GO turning into a recall
messages = deque(maxlen=40)
history = []              # list of result dicts (every version), oldest first
ser = None


# ---------------- chosen event (remembered between restarts) ----------------
def find_event(event_id):
    for e in EVENTS:
        if e["id"] == event_id:
            return e
    return None


def apply_events(lst):
    out = [dict(DEFAULT_EVENTS[0])]
    for e in lst or []:
        if isinstance(e, dict) and re.match(r"^[\w]{1,12}$", str(e.get("id", ""))) and str(e.get("name", "")).strip():
            out.append({"id": str(e["id"]), "name": str(e["name"]).strip()[:30], "legs": max(1, min(8, int(e.get("legs") or 1)))})
    if len(out) > 1:
        EVENTS[:] = out


def load_settings():
    global draw
    SETUP["done"] = os.path.exists(SETTINGS_FILE)       # a fresh install starts with the Get started steps
    try:
        with open(SETTINGS_FILE, encoding="utf-8") as fh:
            s = json.load(fh)
        SETUP["done"] = bool(s.get("setup_done", True))
        for k in BRAND:
            BRAND[k] = str((s.get("brand") or {}).get(k, ""))[:40]
        if re.match(r"^\d{4,8}$", str(s.get("owner_pin", ""))):
            OWNER["pin"] = str(s["owner_pin"])
        if isinstance(s.get("events"), list):
            apply_events(s["events"])
        if isinstance(s.get("upd_key"), str):
            UPD_KEY["v"] = s["upd_key"][:300]
        if isinstance(s.get("kit"), str) and s["kit"].strip():
            KIT["text"] = s["kit"][:2000]
        if find_event(s.get("event", "")):
            S["event"] = s.get("event", "")
        if isinstance(s.get("heat"), dict):
            S["heat"] = s["heat"]
        mp = str(s.get("master_pin", ""))
        if re.match(r"^\d{4,8}$", mp):
            PINS["master"] = mp
        if s.get("access_day") == today():             # approvals don't carry over to another day
            access_day[0] = s["access_day"]
            officials.update({k: v for k, v in (s.get("officials") or {}).items()
                              if isinstance(v, dict) and v.get("role") in ROLES})
        regulars.update({k: v for k, v in (s.get("regulars") or {}).items() if isinstance(v, dict) and v.get("role") in ROLES})
        for k in NET:
            NET[k] = str((s.get("net") or {}).get(k, ""))[:64]
        if isinstance(s.get("last_test"), dict):
            S["last_test"] = s["last_test"]
    except (OSError, ValueError, AttributeError):
        pass
    try:
        with open(FLAGS_FILE, encoding="utf-8") as fh:
            flags.update(json.load(fh))
    except (OSError, ValueError):
        pass
    try:
        with open(DRAW_FILE, encoding="utf-8") as fh:
            draw = json.load(fh)
    except (OSError, ValueError):
        draw = None


def save_settings():
    try:
        with open(SETTINGS_FILE, "w", encoding="utf-8") as fh:
            json.dump({"event": S["event"], "heat": S["heat"], "master_pin": PINS["master"], "officials": officials,
                       "access_day": access_day[0], "regulars": regulars, "net": NET, "last_test": S["last_test"],
                       "setup_done": SETUP["done"], "brand": BRAND, "owner_pin": OWNER["pin"], "events": EVENTS[1:],
                       "kit": KIT["text"], "upd_key": UPD_KEY["v"]}, fh)
    except OSError:
        pass                    # still used for this session


def today():
    return datetime.now().strftime("%Y-%m-%d")


def access_check():
    # overnight, every approval ends (in case nobody pressed Close event)
    if access_day[0] != today():
        if officials or requests_:
            officials.clear()
            requests_.clear()
            save_settings()
        access_day[0] = today()
    for k in [k for k, v in requests_.items() if time.time() - v["at"] > REQUEST_MINS * 60]:
        del requests_[k]


def lan_ip():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("10.255.255.255", 1))          # picks the Wi-Fi address; nothing is sent
        ip = s.getsockname()[0]
        s.close()
        return ip
    except OSError:
        return "127.0.0.1"


def app_url():
    a = NET["addr"].strip() or lan_ip() or "127.0.0.1"
    if not a.startswith("http"):
        a = "http://" + a
    if not re.search(r":\d+$", a.split("//", 1)[1].split("/")[0]) and HTTP_PORT != 80:
        a += ":%d" % HTTP_PORT
    return a.rstrip("/") + "/"


def tid(tok):
    return tok[:10]


def find_tok(i, pool):
    return next((k for k in pool if tid(k) == str(i)), None)


def ask_access(tok, name):
    name = re.sub(r"\s+", " ", str(name or "")).strip()[:30]
    if len(name) < 2:
        return "Type your name"
    if tok in officials:
        return "ok"
    if tok not in requests_ and len(requests_) >= 30:
        return "Too many people waiting - ask the timing desk"
    used = {v["code"] for k, v in requests_.items() if k != tok}
    code = (requests_.get(tok) or {}).get("code")
    while not code or code in used:
        code = "%03d" % secrets.randbelow(1000)
    requests_[tok] = {"name": name, "code": code, "at": time.time()}
    return "ok"


def officials_action(d):
    # Master only: approve / decline requests, change or remove officials, close the event, settings
    if "approve" in d or "decline" in d:
        k = find_tok(d.get("approve", d.get("decline")), requests_)
        if not k:
            return "That request has gone (it was cancelled or timed out)"
        rq = requests_.pop(k)
        if "approve" in d:
            role = str(d.get("role", ""))
            if role not in ("admin", "starter", "marshal"):
                return "Choose Referee, Starter or Marshal"
            officials[k] = {"name": rq["name"], "role": role, "since": time.time(), "seen": time.time()}
            access_day[0] = today()
            if d.get("remember"):
                regulars[rq["name"].lower()] = {"name": rq["name"], "role": role}
    elif "set_role" in d:
        k = find_tok(d["set_role"], officials)
        role = str(d.get("role", ""))
        if not k or role not in ("admin", "starter", "marshal"):
            return "not allowed"
        officials[k]["role"] = role
        if officials[k]["name"].lower() in regulars:
            regulars[officials[k]["name"].lower()]["role"] = role
    elif "remove" in d:
        if not officials.pop(find_tok(d["remove"], officials) or "", None):
            return "Already removed"
    elif "remember" in d:
        k = find_tok(d["remember"], officials)
        if not k:
            return "not allowed"
        o = officials[k]
        if d.get("on"):
            regulars[o["name"].lower()] = {"name": o["name"], "role": o["role"]}
        else:
            regulars.pop(o["name"].lower(), None)
    elif "forget" in d:
        regulars.pop(str(d["forget"]).lower(), None)
    elif d.get("close"):
        officials.clear()
        requests_.clear()
    elif "net" in d:
        n = d["net"] or {}
        ssid, pw, addr = (str(n.get(k, "")).strip()[:64] for k in ("ssid", "pass", "addr"))
        if addr != NET["addr"] and not owner_ok():
            return OWNER_MSG
        if pw and len(pw) < 8:
            return "Wi-Fi passwords are at least 8 characters"
        if addr and not re.match(r"^(https?://)?[\w.\-]+(:\d+)?/?$", addr):
            return "Address like 192.168.1.20"
        NET.update(ssid=ssid, **{"pass": pw, "addr": addr})
    elif "master_pin" in d:
        if not owner_ok():
            return OWNER_MSG
        v = str(d["master_pin"]).strip()
        if v and not re.match(r"^\d{4,8}$", v):
            return "Use 4 to 8 digits, or leave empty to turn it off"
        PINS["master"] = v
        for k in [k for k, o in officials.items() if o["role"] == "master"]:
            del officials[k]
    else:
        return "not allowed"
    save_settings()
    return "ok"


def access_view(role, tok):
    d = {"join": {"ssid": NET["ssid"], "pass": NET["pass"], "url": app_url()}}
    if tok in requests_:
        d["me"] = {"name": requests_[tok]["name"], "code": requests_[tok]["code"]}
    elif tok in officials:
        d["me"] = {"name": officials[tok]["name"]}
    if role == "master":
        now = time.time()
        d["access"] = {
            "requests": [{"id": tid(k), "name": v["name"], "code": v["code"], "mins": int((now - v["at"]) // 60),
                          "usual": (regulars.get(v["name"].lower()) or {}).get("role")}
                         for k, v in sorted(requests_.items(), key=lambda x: x[1]["at"])],
            "officials": [{"id": tid(k), "name": v["name"], "role": v["role"], "mins": int((now - v.get("seen", 0)) // 60),
                           "regular": v["name"].lower() in regulars, "me": k == tok}
                          for k, v in sorted(officials.items(), key=lambda x: x[1]["name"].lower())],
            "regulars": sorted(regulars.values(), key=lambda x: x["name"].lower()),
            "master_pin": PINS["master"], "net": dict(NET), "auto_url": "http://%s:%d/" % (lan_ip() or "127.0.0.1", HTTP_PORT)}
    return d


ADMIN_CMDS = re.compile(r"^(j|p|ok|place|dq|dnf|clear|legs|tie)\b")
STARTER_CMDS = ("set", "go", "f", "test on", "test off", "j")


role_fix = {}            # "crew|person" (lower case) -> "Driver" | "Crew" | "Patient"


def load_roles():
    try:
        with open(ROLES_FILE, encoding="utf-8") as fh:
            role_fix.update({k: v for k, v in json.load(fh).items() if v in ("Driver", "Crew", "Patient")})
    except (OSError, ValueError):
        pass


def set_role(d):
    crew = re.sub(r"\s+", " ", str(d.get("crew") or "")).strip()[:80]
    person = re.sub(r"\s+", " ", str(d.get("person") or "")).strip()[:60]
    role = str(d.get("role") or "")
    if not crew or not person or role not in ("Driver", "Crew", "Patient", ""):
        return "not allowed"
    with lock:
        k = (crew + "|" + person).lower()
        if role:
            role_fix[k] = role
        else:
            role_fix.pop(k, None)
        if len(role_fix) > 3000:
            return "Too many roles saved"
        try:
            with open(ROLES_FILE, "w", encoding="utf-8") as fh:
                json.dump(role_fix, fh)
        except OSError:
            pass
    return "ok"


# ---------------- updates (from GitHub, Master only) ----------------
UPD = {"latest": None, "notes": [], "checked": None, "msg": "", "busy": False}


def vtuple(v):
    return tuple(int(x) for x in re.findall(r"\d+", str(v or "0"))[:4]) or (0,)


def fetch_url(name, timeout=20):
    if UPD_KEY["v"]:
        req = urllib.request.Request(UPDATE_API + name + "?ref=main",
                                     headers={"User-Agent": "IRB-timing-app/" + APP_VERSION, "Authorization": "Bearer " + UPD_KEY["v"],
                                              "Accept": "application/vnd.github.raw", "X-GitHub-Api-Version": "2022-11-28",
                                              "Cache-Control": "no-cache"})
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return r.read()
    req = urllib.request.Request(UPDATE_URL + name + "?t=%d" % time.time(),
                                 headers={"User-Agent": "IRB-timing-app/" + APP_VERSION, "Cache-Control": "no-cache"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read()


def upd_error(e):
    code = getattr(e, "code", None)
    if code in (401, 403) and UPD_KEY["v"]:
        return "The updates key was refused - it may have expired. The owner adds a new one under Setup › Advanced › Updates key."
    if code == 404:
        return ("Updates not found - check the updates key can read the repository." if UPD_KEY["v"] else
                "Updates not found - if the repository is private, the owner adds an updates key under Setup › Advanced.")
    return "Couldn't check for updates - is this computer on the internet? (%s)" % str(e)[:80]


def key_action(d):
    # owner only: the read-only GitHub key for a private repository ("" = none)
    if not owner_ok():
        return OWNER_MSG
    v = str(d.get("key") or "").strip()
    if v and not re.match(r"^(github_pat_|ghp_)[A-Za-z0-9_]{20,250}$", v):
        return "That doesn't look like a GitHub key - it starts with github_pat_"
    old = UPD_KEY["v"]
    UPD_KEY["v"] = v
    if v:
        update_check()
        if UPD["msg"]:
            UPD_KEY["v"] = old
            return UPD["msg"]
    save_settings()
    return "ok"


def update_check():
    try:
        info = json.loads(fetch_url("VERSION.json").decode("utf-8"))
    except Exception as e:
        UPD.update(msg=upd_error(e), checked=datetime.now().strftime("%H:%M"))
        return UPD
    UPD.update(latest=str(info.get("app") or ""), notes=[str(n)[:200] for n in (info.get("notes") or [])][:12],
               sha=str(info.get("sha256") or ""), pico=str(info.get("pico") or ""),
               checked=datetime.now().strftime("%H:%M"), msg="")
    return UPD


def backups():
    return sorted(glob.glob(os.path.join(OLD_DIR, "officials_app_*.py")), reverse=True)


def swap_in(code, label):
    # check the new program is whole, keep a copy of this one, then put the new one in place
    try:
        compile(code, "officials_app.py", "exec")
    except SyntaxError as e:
        return "That version is damaged (line %s) - not installed" % e.lineno
    me = os.path.abspath(__file__)
    os.makedirs(OLD_DIR, exist_ok=True)
    stamp = datetime.now().strftime("%Y%m%d-%H%M%S")
    shutil.copy2(me, os.path.join(OLD_DIR, "officials_app_%s_v%s.py" % (stamp, APP_VERSION)))
    tmp = me + ".new"
    with open(tmp, "w", encoding="utf-8", newline="\n") as fh:
        fh.write(code)
    os.replace(tmp, me)
    note("Program %s by the timing desk - restarting" % label)
    return "ok"


def restart_soon():
    # give the screen a moment to hear "ok", then start the new version
    def go():
        time.sleep(1.5)
        STOPPING.set()                             # the Pico link closes its own port...
        PORT_FREE.wait(4)                          # ...and we wait for that (at most 4 s)
        time.sleep(0.5)
        if os.environ.get("IRB_LAUNCHER"):          # IRB_start.bat / the Pi service start us again
            os._exit(3)
        os.execv(sys.executable, [sys.executable, os.path.abspath(__file__)] + sys.argv[1:])
    threading.Thread(target=go, daemon=True).start()


def update_action(d):
    if (d.get("install") or d.get("rollback")) and not owner_ok():
        return OWNER_MSG
    if S["state"] in ("ARMED", "RACING"):
        return "Not during a race - update between races or after racing"
    if UPD["busy"]:
        return "Already updating"
    if d.get("check"):
        update_check()
        return UPD["msg"] or "ok"
    if d.get("install"):
        UPD["busy"] = True
        try:
            info = update_check()
            if info["msg"]:
                return info["msg"]
            if vtuple(info["latest"]) <= vtuple(APP_VERSION) and not d.get("again"):
                return "You already have the newest version (v%s)" % APP_VERSION
            raw = fetch_url("officials_app.py", timeout=60)
            if info.get("sha") and hashlib.sha256(raw).hexdigest() != info["sha"]:
                return "The download didn't match - GitHub may still be updating. Try again in a few minutes."
            code = raw.decode("utf-8")
            if ('APP_VERSION = "%s"' % info["latest"]) not in code:
                return "The download didn't match - GitHub may still be updating. Try again in a few minutes."
            r = swap_in(code, "updated to v%s" % info["latest"])
            if r == "ok":
                restart_soon()
            return r
        except Exception as e:
            return "Update failed - nothing was changed. " + upd_error(e)
        finally:
            UPD["busy"] = False
    if d.get("rollback"):
        b = backups()
        if not b:
            return "No earlier version saved on this computer"
        with open(b[0], encoding="utf-8") as fh:
            code = fh.read()
        r = swap_in(code, "put back to " + os.path.basename(b[0]))
        if r == "ok":
            os.remove(b[0])                         # it's now the live one (this version was saved instead)
            restart_soon()
        return r
    return "not allowed"


# ---------------- new event: put today's data away and start clean ----------------
EVENTS_DIR = os.path.join(DATA, "past_events")


def past_events():
    try:
        return sorted((d for d in os.listdir(EVENTS_DIR) if os.path.isdir(os.path.join(EVENTS_DIR, d))), reverse=True)[:20]
    except OSError:
        return []


def new_event(d):
    global draw
    if S["state"] in ("ARMED", "RACING") or S["test"]:
        return "Not during a race or button test"
    with lock:
        name = re.sub(r"[^\w\- ]", "", str(d.get("name") or (draw or {}).get("name") or "event")).strip()[:50] or "event"
        folder = os.path.join(EVENTS_DIR, "%s %s" % (datetime.now().strftime("%Y-%m-%d %H%M"), name))
        os.makedirs(folder, exist_ok=True)
        # keep everything from this event: results (also as a spreadsheet), program, LiveHeats ticks, draw, roles, Pico log
        if history:
            with open(os.path.join(folder, "results.csv"), "w", encoding="utf-8", newline="") as fh:
                fh.write(history_csv())
        for f in (HIST_FILE, FLAGS_FILE, PROGRAM_FILE, DRAW_FILE, ROLES_FILE):
            if os.path.exists(f):
                shutil.copy2(f, folder)
        for f in glob.glob(os.path.join(DATA, "pico_log_*.txt")):
            shutil.copy2(f, folder)
        # start clean (settings, Wi-Fi, templates and remembered officials stay)
        history.clear(); flags.clear(); raced.clear(); checkin.clear(); sent.clear(); role_fix.clear()
        program.update({"mode": None, "items": [], "lh_sig": "", "ver": program.get("ver", 0) + 1, "manual": [], "seq": 0,
                        "last_block": [], "breaks": {}, "timing": {}})
        officials.clear(); requests_.clear()
        SETUP["done"] = False                       # the Get started steps show again for the next event
        BRAND["event"] = ""
        S.update(heat=None, race_heat=None, results=None, race_event=None, event="")
        for f in (HIST_FILE, FLAGS_FILE, ROLES_FILE):
            try:
                os.remove(f)
            except OSError:
                pass
        if not d.get("keep_draw"):
            draw = None
            try:
                os.remove(DRAW_FILE)
            except OSError:
                pass
        save_program()
        save_settings()
    note("New event started - the last one is saved in %s" % folder)
    return "ok:" + os.path.basename(folder)


def update_view():
    b = backups()
    prev = re.search(r"_v([\d.]+)\.py$", b[0]) if b else None
    return {"current": APP_VERSION, "latest": UPD["latest"], "notes": UPD["notes"], "checked": UPD["checked"],
            "msg": UPD["msg"], "newer": bool(UPD["latest"]) and vtuple(UPD["latest"]) > vtuple(APP_VERSION),
            "prev": (prev.group(1) if prev else ("earlier" if b else None))}


# ---------------- hire kits: owner lock, branding, events, Windows firewall, packs ----------------
OWNER_MSG = "Locked by the owner – unlock with the owner PIN (System › Setup)"


def owner_ok():
    return not OWNER["pin"] or time.time() < OWNER["open_until"]


def owner_action(d):
    if "pin" in d:                                   # unlock for 20 minutes
        if OWNER["pin"] and str(d["pin"]) == OWNER["pin"]:
            OWNER["open_until"] = time.time() + 20 * 60
            return "ok"
        time.sleep(1)
        return "Wrong owner PIN"
    if d.get("lock"):
        OWNER["open_until"] = 0.0
        return "ok"
    if "set_pin" in d:
        if not owner_ok():
            return OWNER_MSG
        v = str(d["set_pin"]).strip()
        if v and not re.match(r"^\d{4,8}$", v):
            return "Use 4 to 8 digits, or leave empty to turn the lock off"
        OWNER["pin"] = v
        OWNER["open_until"] = time.time() + 20 * 60 if v else 0.0
        save_settings()
        return "ok"
    if "kit" in d:
        if not owner_ok():
            return OWNER_MSG
        KIT["text"] = str(d["kit"]).strip()[:2000] or DEFAULT_KIT
        save_settings()
        return "ok"
    return "not allowed"


def brand_action(d):
    if "logo" in d:
        v = str(d["logo"] or "")
        if not v:
            try:
                os.remove(LOGO_FILE)
            except OSError:
                pass
            return "ok"
        m = re.match(r"^data:image/png;base64,([A-Za-z0-9+/=]+)$", v)
        if not m or len(v) > 400000:
            return "Use a smaller picture (PNG or JPG)"
        os.makedirs(DATA, exist_ok=True)
        with open(LOGO_FILE, "wb") as fh:
            fh.write(base64.b64decode(m.group(1)))
        return "ok"
    for k in BRAND:
        if k in d:
            BRAND[k] = re.sub(r"\s+", " ", str(d[k] or "")).strip()[:40]
    if "setup_done" in d:
        SETUP["done"] = bool(d["setup_done"])
    save_settings()
    return "ok"


def events_action(d):
    if S["state"] in ("ARMED", "RACING"):
        return "Not during a race"
    name = re.sub(r"\s+", " ", str(d.get("name") or "")).strip()[:30]
    try:
        legs = int(d.get("legs") or 0)
    except (TypeError, ValueError):
        legs = 0
    if d.get("reset"):
        EVENTS[:] = [dict(e) for e in DEFAULT_EVENTS]
    elif d.get("add"):
        if len(name) < 2 or not 1 <= legs <= 8:
            return "Type a name and choose 1 to 8 legs"
        if any(e["name"].lower() == name.lower() for e in EVENTS):
            return "There's already an event called " + name
        n = 1
        while any(e["id"] == "c%d" % n for e in EVENTS):
            n += 1
        EVENTS.append({"id": "c%d" % n, "name": name, "legs": legs})
    elif d.get("edit"):
        e = find_event(str(d["edit"]))
        if not e or not e["id"] or len(name) < 2 or not 1 <= legs <= 8:
            return "Type a name and choose 1 to 8 legs"
        e.update(name=name, legs=legs)
    elif d.get("remove"):
        e = find_event(str(d["remove"]))
        if not e or not e["id"]:
            return "not allowed"
        if len(EVENTS) <= 2:
            return "Keep at least one event"
        EVENTS.remove(e)
        if S["event"] == e["id"]:
            S["event"] = ""
    else:
        return "not allowed"
    save_settings()
    return "ok"


NO_WINDOW = 0x08000000 if os.name == "nt" else 0


def firewall_check():
    # Windows only: is there a rule letting phones reach this app? (None = not Windows / can't tell)
    if os.name != "nt":
        return None
    try:
        for name in (FW_RULE, "IRB timing app"):
            r = subprocess.run(["netsh", "advfirewall", "firewall", "show", "rule", "name=" + name],
                               capture_output=True, timeout=10, creationflags=NO_WINDOW)
            if r.returncode == 0:
                FIREWALL["state"] = True
                return True
        FIREWALL["state"] = False
    except Exception:
        FIREWALL["state"] = None
    return FIREWALL["state"]


def firewall_allow():
    # asks Windows (a Yes/No prompt on this computer) to add the rule; runs in the background
    if os.name != "nt":
        return "Only needed on Windows"
    if FIREWALL["busy"]:
        return "Already asking – answer Yes on the Windows prompt"
    def go():
        FIREWALL["busy"] = True
        try:
            ps = ("Start-Process -FilePath netsh -Verb RunAs -WindowStyle Hidden -Wait -ArgumentList "
                  "'advfirewall firewall add rule name=%s dir=in action=allow protocol=TCP localport=%d'" % (FW_RULE, HTTP_PORT))
            subprocess.run(["powershell", "-NoProfile", "-ExecutionPolicy", "Bypass", "-Command", ps],
                           capture_output=True, timeout=180, creationflags=NO_WINDOW)
        except Exception as e:
            note("Couldn't add the firewall rule: %s" % str(e)[:80])
        finally:
            firewall_check()
            FIREWALL["busy"] = False
    threading.Thread(target=go, daemon=True).start()
    return "ok"


def zip_bytes(files, extra=None):
    buf = io.BytesIO()
    with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as z:
        for f in files:
            if os.path.isfile(f):
                z.write(f, os.path.basename(f))
        for name, text in (extra or {}).items():
            z.writestr(name, text)
    return buf.getvalue()


def event_pack(name):
    # one saved event (or today's, name "") as a zip the hirer takes home
    if name:
        if name not in past_events():
            return None
        folder = os.path.join(EVENTS_DIR, name)
        return zip_bytes(sorted(glob.glob(os.path.join(folder, "*"))))
    with lock:
        csv_text = history_csv() if history else ""
    return zip_bytes([HIST_FILE, FLAGS_FILE, PROGRAM_FILE], {"results.csv": csv_text} if csv_text else None)


def diagnostics():
    # everything needed to work out a problem, with passwords and PINs left out
    with lock:
        try:
            with open(SETTINGS_FILE, encoding="utf-8") as fh:
                s = json.load(fh)
        except (OSError, ValueError):
            s = {}
        for k in ("master_pin", "owner_pin", "upd_key"):
            if s.get(k):
                s[k] = "(set)"
        if isinstance(s.get("net"), dict) and s["net"].get("pass"):
            s["net"]["pass"] = "(set)"
        info = ["IRB timing problem report", "Made: %s" % datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                "App: v%s   Pico program: v%s   Python %s   %s" % (APP_VERSION, S["fw"], platform.python_version(), platform.platform()),
                "Pico: %s on %s   state %s   race %s   lanes %s   faults %s" % ("connected" if S["connected"] else "NOT connected", S["port"],
                                                                              S["state"], S["race"], S["lanes"], S["faults"]),
                "Battery: %s V   Firewall rule: %s   App address: %s" % (S["batt"], FIREWALL["state"], app_url()),
                "Update: %s" % json.dumps(update_view()), "Officials: %d   Requests: %d" % (len(officials), len(requests_)),
                "", "Recent messages:"] + ["  ".join(str(x) for x in (m if isinstance(m, (list, tuple)) else [m])) for m in list(messages)]
    logs = sorted(glob.glob(os.path.join(DATA, "pico_log_*.txt")))[-3:]
    return zip_bytes([HIST_FILE, FLAGS_FILE, PROGRAM_FILE] + logs,
                     {"report.txt": "\n".join(info), "settings.json": json.dumps(s, indent=1)})


def allowed(role, path, data):
    """None if this level may do it, else the reason shown on screen"""
    if role == "master":
        return None
    who = ROLE_NAME.get(role, "Viewer")
    if role == "viewer":
        return "View only - ask the timing desk for access"
    cmd = str(data.get("cmd", "")).strip().lower()
    if path.startswith("/api/marshal"):
        return None if role in ("admin", "marshal") else "Only the Marshal or Referee can check crews in"
    if role == "admin":
        if path.startswith("/api/cmd"):
            return None if ADMIN_CMDS.match(cmd) else "SET, GO and FINISH are for the Starter"
        if any(path.startswith(p) for p in ("/api/confirm", "/api/note", "/api/entered", "/api/draw/load",
                                             "/api/program", "/api/heat", "/api/event", "/api/template")):
            return None
        return "Only the timing desk can do that"
    if role == "starter":
        if path.startswith("/api/cmd"):
            return None if cmd in STARTER_CMDS else "Only the Referee can change results"
        if path.startswith("/api/heat") and data.get("next") and len([k for k in data if k not in ("who", "next")]) == 0:
            return None if prog_on() else "The Referee chooses the heats when there's no program"
        return "%s can't do that - ask the Referee" % who
    return "%s can't do that" % who


def set_event(event_id):
    if not find_event(event_id):
        return "not allowed"
    with lock:
        S["event"] = event_id
        save_settings()
    return "ok"


def save_flags():
    try:
        with open(FLAGS_FILE, "w", encoding="utf-8") as fh:
            json.dump(flags, fh)
    except OSError:
        pass


def is_confirmed(race):
    return bool(flags.get(str(race), {}).get("confirmed"))


def confirm_results(race, undo, who="?"):
    with lock:
        res = S["results"]
        if not res or res.get("race") != race:
            return "Those results aren't on screen any more"
        f = flags.setdefault(str(race), {})
        if undo:
            f.pop("confirmed", None)
        else:
            f["confirmed"] = datetime.now().strftime("%H:%M:%S")
        f.setdefault("log", []).append([datetime.now().strftime("%H:%M:%S"), who, "reopened" if undo else "results final"])
        save_flags()
        h = res.get("heat")
        move_on = (not undo and h and S["heat"] and S["heat"].get("heat_id") == h.get("heat_id"))
    if move_on:
        select_heat({"next": True})        # results final -> the next heat is ready
    return "ok"


def save_note(race, text, who):
    with lock:
        f = flags.setdefault(str(race), {})
        f["note"] = str(text or "").strip()[:500]
        f["note_by"] = str(who or "?")[:30]
        save_flags()
    return "ok"


def mark_entered(race, undo):
    with lock:
        f = flags.setdefault(str(race), {})
        if undo:
            f.pop("entered", None)
        else:
            f["entered"] = datetime.now().strftime("%Y-%m-%d %H:%M")
        save_flags()
    return "ok"


def entry_queue():
    # finished races (latest version) not yet ticked off as entered in LiveHeats, oldest first
    out = []
    for r in sorted(history_summary(), key=lambda r: r.get("race") or 0):
        f = flags.get(str(r.get("race")), {})
        if not f.get("entered"):
            rec = dict(r)
            rec["confirmed"] = bool(f.get("confirmed"))
            out.append(rec)
    return out[-60:]


# ---------------- LiveHeats draw (read-only, public events) ----------------
DRAW_QUERY = """query($id: ID!){ event(id:$id){ id name %s eventDivisions { id division { name }
  heats { id round roundPosition position scheduledTime competitors { position teamName athlete { name } MEMBERS } } } } }"""
MEMBERS_SEL = "teamMembers { order teamRoleName athlete { name } }"    # driver, crew, patients (public fields only)
_sched_sel = None


def schedule_selection():
    # LiveHeats keeps its running order in Event.fullSchedule. Its shape isn't documented, so ask the
    # API what it looks like once and request every plain field (heat ids are then found in order).
    global _sched_sel
    if _sched_sel is not None:
        return _sched_sel
    _sched_sel = ""
    try:
        def ask(q, v=None):
            body = json.dumps({"query": q, "variables": v or {}}).encode()
            req = urllib.request.Request(LIVEHEATS_API, body, {"Content-Type": "application/json",
                                                               "User-Agent": "IRB-timing-app/" + APP_VERSION})
            with urllib.request.urlopen(req, timeout=20) as r:
                return json.loads(r.read().decode("utf-8"))
        tq = """query($n:String!){ __type(name:$n){ fields { name args { name }
                type { kind name ofType { kind name ofType { kind name ofType { kind name } } } } } } }"""

        def base(ty):
            while ty and ty.get("ofType"):
                ty = ty["ofType"]
            return ty or {}

        def fields(name):
            r = ask(tq, {"n": name})
            return ((r.get("data") or {}).get("__type") or {}).get("fields") or []

        def sel(name, depth):
            parts = []
            for f in fields(name):
                if f.get("args"):
                    continue
                b = base(f["type"])
                if b.get("kind") in ("SCALAR", "ENUM"):
                    parts.append(f["name"])
                elif b.get("kind") == "OBJECT" and depth > 0:
                    sub = sel(b["name"], depth - 1)
                    if sub:
                        parts.append("%s { %s }" % (f["name"], sub))
            return " ".join(parts)

        fs = next((f for f in fields("Event") if f["name"] == "fullSchedule"), None)
        if fs:
            b = base(fs["type"])
            if b.get("kind") in ("SCALAR", "ENUM"):
                _sched_sel = "fullSchedule"
            elif b.get("kind") == "OBJECT":
                inner = sel(b["name"], 2)
                if inner:
                    _sched_sel = "fullSchedule { %s }" % inner
    except Exception as e:
        print("LiveHeats schedule not available:", e)
    return _sched_sel


def schedule_order(ev, heat_ids):
    # heat ids in the order they appear in LiveHeats' fullSchedule (any structure), else by scheduled time
    found = []

    def walk(x):
        if isinstance(x, dict):
            for k in ("heatId", "id"):
                v = x.get(k)
                if v is not None and str(v) in heat_ids and str(v) not in found:
                    found.append(str(v))
            for v in x.values():
                walk(v)
        elif isinstance(x, list):
            for v in x:
                walk(v)
        elif isinstance(x, str) and x.strip().startswith(("{", "[")):
            try:
                walk(json.loads(x))
            except ValueError:
                pass
    walk(ev.get("fullSchedule"))
    if found:
        return found, "LiveHeats schedule"
    timed = []
    for dv in ev.get("eventDivisions") or []:
        for h in dv.get("heats") or []:
            if h.get("scheduledTime"):
                timed.append((h["scheduledTime"], str(h.get("id"))))
    if timed:
        return [i for _, i in sorted(timed)], "LiveHeats heat times"
    return [], ""


def event_for(division_name):
    n = division_name.lower()
    for e in EVENTS:
        if e["id"].startswith("c") and e["name"].lower() in n:
            return e["id"]
    for key, eid in (("mass rescue", "mass"), ("teams rescue", "teams"), ("tube rescue", "tube"),
                     ("relay", "relay"), ("rescue", "rescue")):
        if key in n:
            return eid
    return ""


def compact_draw(ev):
    divs = []
    for dv in ev.get("eventDivisions") or []:
        dname = (dv.get("division") or {}).get("name") or "Division"
        heats = []
        for h in sorted(dv.get("heats") or [], key=lambda h: (h.get("roundPosition") or 0, h.get("position") or 0)):
            crews, clubs, members = [], {}, {}
            for c in sorted(h.get("competitors") or [], key=lambda c: c.get("position") or 0):
                ppl = [[(x.get("athlete") or {}).get("name") or "", x.get("teamRoleName") or ""]
                       for x in sorted(c.get("teamMembers") or [], key=lambda x: x.get("order") if x.get("order") is not None else 99)
                       if (x.get("athlete") or {}).get("name")]
                if ppl:
                    members[str((c.get("position") or 0) + 1)] = ppl     # [[name, "Driver"|"Crew"|"Patient"|""], ...]
                nm = (c.get("athlete") or {}).get("name") or c.get("teamName") or "?"
                if nm.endswith(" - " + dname):
                    nm = nm[:-len(" - " + dname)]
                crews.append([(c.get("position") or 0) + 1, nm])     # LiveHeats slot 0 = lane 1
                if c.get("teamName"):
                    clubs[str((c.get("position") or 0) + 1)] = c["teamName"]
            heats.append({"id": str(h.get("id")), "round": h.get("round") or "",
                          "no": (h.get("position") or 0) + 1, "time": h.get("scheduledTime"), "crews": crews,
                          "clubs": clubs, "members": members})
        if heats:
            divs.append({"id": str(dv.get("id")), "name": dname, "event": event_for(dname), "heats": heats})
    ids = set(h["id"] for d in divs for h in d["heats"])
    order, src = schedule_order(ev, ids)
    return {"id": str(ev.get("id")), "name": ev.get("name") or "", "divisions": divs,
            "schedule": order, "schedule_src": src,
            "loaded_at": datetime.now().strftime("%Y-%m-%d %H:%M")}


def load_draw(link):
    global draw
    m = re.search(r"(\d{3,})", link or "")
    if not m:
        return "Paste the LiveHeats event link, e.g. https://www.liveheats.com/events/505147"

    def fetch(q):
        body = json.dumps({"query": q, "variables": {"id": m.group(1)}}).encode()
        req = urllib.request.Request(LIVEHEATS_API, body, {"Content-Type": "application/json",
                                                           "User-Agent": "IRB-timing-app/" + APP_VERSION})
        with urllib.request.urlopen(req, timeout=40) as r:
            return json.loads(r.read().decode("utf-8"))
    ev = None
    sched = schedule_selection()
    # most to least: names of the people in each crew + schedule, then without each part LiveHeats refuses
    tries = [(sched, MEMBERS_SEL), ("", MEMBERS_SEL), (sched, ""), ("", "")]
    seen = set()
    for k, (s, mem) in enumerate(tries):
        q = (DRAW_QUERY % s).replace("MEMBERS", mem)
        if q in seen:
            continue
        seen.add(q)
        try:
            reply = fetch(q)
        except Exception as e:
            if k == 0:
                return "Couldn't reach LiveHeats - is this computer on the internet? (%s)" % e
            continue
        ev = (reply.get("data") or {}).get("event")
        if ev:
            break
    if not ev:
        return "LiveHeats didn't return that event. Check the link (the event must be public)."
    d = compact_draw(ev)
    if not d["divisions"]:
        return "That event has no heats drawn yet."
    with lock:
        draw = d
        cur = S["heat"]
        if cur:
            for dv in d["divisions"]:
                for h in dv["heats"]:
                    if h["id"] == cur.get("heat_id"):
                        new = heat_info(dv, h)            # crews may have been filled in since
                        for a, b in cur.get("swaps") or []:   # keep any lane swaps the officials made
                            a, b = str(a), str(b)
                            ca, cb = new["crews"].pop(a, None), new["crews"].pop(b, None)
                            if ca:
                                new["crews"][b] = ca
                            if cb:
                                new["crews"][a] = cb
                        if cur.get("swaps"):
                            new["swaps"] = cur["swaps"]
                        S["heat"] = new
            save_settings()
        try:
            with open(DRAW_FILE, "w", encoding="utf-8") as fh:
                json.dump(d, fh)
        except OSError:
            pass
    return "ok"


reloading = False


def auto_reload():
    # after each FINISH: fetch the latest draw in the background. A race that has run keeps
    # the crews it had at GO, so this only changes the heats still to come.
    global reloading
    if reloading or not draw:
        return
    reloading = True
    try:
        r = load_draw("https://www.liveheats.com/events/" + draw["id"])
        with lock:
            messages.append([datetime.now().strftime("%H:%M:%S"),
                             "Draw updated from LiveHeats" if r == "ok"
                             else "Draw not updated (no internet?) - using the saved draw"])
    finally:
        reloading = False


program = {"mode": None, "items": [], "lh_sig": "", "ver": 0, "manual": [], "seq": 0, "last_block": [],
           "breaks": {}, "timing": {}}
checkin = {}              # heat id -> {"lane": "present" | "scratched"} from the marshals
sent = {}                 # heat id -> {"at", "who", "missing": [lanes]} once the Marshal sends the patients out
templates = {}            # name -> saved program
# manual: divisions typed in on the Program tab, same shape as LiveHeats divisions:
#   {"id": "m1", "name": "Open Male Rescue Tube", "event": "tube", "manual": true,
#    "heats": [{"id": "m1-3", "round": "Round 1", "no": 1, "time": null, "crews": [[lane, name], ...]}]}
# mode: None = not decided yet, "on" = follow the program, "off" = choose heats one at a time


def load_templates():
    try:
        with open(TEMPLATES_FILE, encoding="utf-8") as fh:
            templates.update(json.load(fh))
    except (OSError, ValueError):
        pass


def save_templates():
    try:
        with open(TEMPLATES_FILE, "w", encoding="utf-8") as fh:
            json.dump(templates, fh)
    except OSError:
        pass


def load_program():
    try:
        with open(PROGRAM_FILE, encoding="utf-8") as fh:
            p = json.load(fh)
        if isinstance(p, dict) and isinstance(p.get("items"), list):
            program.update({k: p[k] for k in ("mode", "items", "lh_sig", "manual", "seq", "last_block",
                                               "breaks", "timing") if k in p})
            checkin.update(p.get("checkin") or {})
            sent.update(p.get("sent") or {})
            program["required"] = int(p.get("required") or 2) if str(p.get("required") or 2) in ("2", "3") else 2
    except (OSError, ValueError):
        pass


def save_program():
    program["ver"] += 1
    try:
        with open(PROGRAM_FILE, "w", encoding="utf-8") as fh:
            d = {k: program[k] for k in ("mode", "items", "lh_sig", "manual", "seq", "last_block", "breaks", "timing")}
            d["checkin"] = checkin
            d["sent"] = sent
            d["required"] = program.get("required", 2)
            json.dump(d, fh)
    except OSError:
        pass


def all_divisions():
    # LiveHeats divisions plus the ones typed in here
    return list((draw or {}).get("divisions", [])) + list(program["manual"])


def have_heats():
    return bool(draw) or any(d["heats"] for d in program["manual"])


def create_heats(c):
    # add typed-in heats: event, division name, round, how many; returns the new heat ids
    ev = find_event(str(c.get("event") or ""))
    if str(c.get("event")) == "other":
        oname = re.sub(r"\s+", " ", str(c.get("event_name") or "")).strip()[:40]
        if not oname:
            return None, "Type the event name"
        ev = {"id": "other", "name": oname, "legs": 0}
    div = re.sub(r"\s+", " ", str(c.get("div") or "")).strip()[:40]
    rnd = re.sub(r"\s+", " ", str(c.get("round") or "Round 1")).strip()[:30] or "Round 1"
    try:
        n = int(c.get("heats") or 1)
    except (TypeError, ValueError):
        n = 0
    if not ev or not ev["id"]:
        return None, "Choose the event"
    if not div:
        return None, "Choose the age group and Male / Female / Mixed"
    if not 1 <= n <= 30:
        return None, "Number of heats must be 1 to 30"
    name = ("%s %s" % (div, ev["name"])).strip()
    dv = next((d for d in program["manual"] if d["name"].lower() == name.lower()), None)
    if not dv:
        program["seq"] += 1
        # an "other" event has no set number of legs - the Pico works it out from the presses
        dv = {"id": "m%d" % program["seq"], "name": name, "event": ev["id"] if ev["id"] != "other" else "",
              "manual": True, "heats": []}
        program["manual"].append(dv)
    start = max([h["no"] for h in dv["heats"] if h["round"].lower() == rnd.lower()] or [0])
    ids = []
    for k in range(n):
        program["seq"] += 1
        h = {"id": "%s-%d" % (dv["id"], program["seq"]), "round": rnd, "no": start + k + 1, "time": None, "crews": []}
        dv["heats"].append(h)
        ids.append(h["id"])
    return ids, "ok"


def heat_lookup(hid):
    for dv in all_divisions():
        for h in dv["heats"]:
            if h["id"] == hid:
                return dv, h
    return None, None


def prog_on():
    return program["mode"] == "on" and bool(program["items"])


def prog_after(cur_id, n=None):
    # heats still to run after the current one, in program order (raced heats are skipped)
    items = program["items"]
    start = items.index(cur_id) + 1 if cur_id in items else 0
    out = [i for i in items[start:] if i not in raced and i != cur_id and i not in program["breaks"]]
    return out if n is None else out[:n]


def program_sync():
    # With a program on, the program decides the heat: always the first heat not raced yet.
    # Runs on every screen refresh, so the next heat is ready as soon as a race finishes,
    # and follows Admin's changes to the order. Never changes while armed or racing.
    if not prog_on() or S["state"] in ("ARMED", "RACING"):
        return
    nxt = next((i for i in program["items"] if i not in raced and i not in program["breaks"] and heat_lookup(i)[1]), None)
    cur = (S["heat"] or {}).get("heat_id")
    if nxt == cur:
        return
    if nxt is None:
        if cur and cur in raced:
            S["heat"] = None
            save_settings()
        return
    dv, h = heat_lookup(nxt)
    S["heat"] = heat_info(dv, h)
    if dv["event"] or dv.get("manual"):
        S["event"] = dv["event"]
    save_settings()


def out_order():
    # for each heat whose patients are on the water: the heats still to race ahead of it
    its = [i for i in program["items"] if i not in program["breaks"] and i not in raced]
    return {h: tuple(its[:its.index(h)]) for h in sent if h in its and h not in raced}, \
        [h for h in sent if h not in raced and h not in its]


def program_action(d):
    with lock:
        before, before_items = out_order()[0], list(program["items"])
        r = _program_action(d)
        if r == "ok" and not d.get("force"):
            after, gone = out_order()
            moved = [h for h in before if after.get(h) != before[h]]
            if moved:
                program["items"] = before_items            # put it back and ask first
                save_program()
                return ("PATIENTS:Patients for %s are already on the water. This change would %s, so the wrong patients "
                        "could be out. Do it anyway?" % (heat_name(moved[0]), "take that heat out of the program"
                                                         if moved[0] not in program["items"] or moved[0] in gone
                                                         else "change the heats before it"))
        return r


def _program_action(d):
    if True:
        ids = [str(x) for x in (d.get("ids") or [])]
        items = program["items"]
        if d.get("mode") in ("on", "off"):
            program["mode"] = d["mode"]
            if d["mode"] == "on" and not items:
                program["mode"] = None
                save_program()
                return "The program is empty - add heats first"
        elif d.get("import"):
            sched = (draw or {}).get("schedule") or []
            if not sched:
                return "This LiveHeats event has no schedule - build the program here instead"
            done = [i for i in items if i in raced]            # heats already run stay at the top
            program["items"] = done + [i for i in sched if i not in done]
            program["lh_sig"] = ",".join(sched)
            program["mode"] = "on"
        elif d.get("create"):
            new, msg = create_heats(d["create"])
            if not new:
                return msg
            block = [i for i in program["last_block"] if i in items and i not in raced]
            if d["create"].get("alternate") and block:
                # interleave the new heats with the heats added last (gives crews a rest)
                pos = items.index(block[0])
                for i in block:
                    items.remove(i)
                mixed = []
                for k in range(max(len(block), len(new))):
                    mixed += ([block[k]] if k < len(block) else []) + ([new[k]] if k < len(new) else [])
                program["items"] = items[:pos] + mixed + items[pos:]
            else:
                program["items"] = items + new
            program["last_block"] = new
            if program["mode"] is None:
                program["mode"] = "on"
        elif d.get("add_break"):
            b = d["add_break"]
            program["seq"] += 1
            bid = "brk-%d" % program["seq"]
            until = str(b.get("until") or "").strip()
            if until and not re.match(r"^\d{1,2}:\d{2}$", until):
                return "Time like 12:30"
            try:
                mins = int(b.get("mins") or 0)
            except (TypeError, ValueError):
                return "Minutes must be a number"
            program["breaks"][bid] = {"label": re.sub(r"\s+", " ", str(b.get("label") or "Break")).strip()[:40] or "Break",
                                      "until": until or None, "mins": mins}
            cur = (S["heat"] or {}).get("heat_id")
            if b.get("after_current") and cur in items:
                items.insert(items.index(cur) + 1, bid)
            else:
                items.append(bid)
        elif d.get("timing") is not None:
            tm = d["timing"] or {}
            st_ = str(tm.get("start") or "").strip()
            if st_ and not re.match(r"^\d{1,2}:\d{2}$", st_):
                return "Start time like 09:00"
            try:
                mins = int(tm.get("mins") or 4)
            except (TypeError, ValueError):
                return "Minutes must be a number"
            if not 1 <= mins <= 60:
                return "Minutes per heat must be 1 to 60"
            program["timing"] = {"start": st_ or None, "mins": mins}
        elif d.get("next_round"):
            nr = d["next_round"]
            rnd = re.sub(r"\s+", " ", str(nr.get("round") or "")).strip()[:30]
            try:
                n = int(nr.get("heats") or 1)
            except (TypeError, ValueError):
                n = 0
            block = [i for i in program["last_block"] if heat_lookup(i)[1]]
            if not block:
                return "Add a round first - the next round follows the heats you added last"
            divs = []
            for i in block:
                dv, h = heat_lookup(i)
                if dv["id"] not in [x[0]["id"] for x in divs]:
                    divs.append((dv, h["round"]))
            groups = []
            for dv, cur_round in divs:
                if dv.get("manual"):
                    if not rnd or not 1 <= n <= 30:
                        return "Choose the round and number of heats"
                    groups.append([manual_heat(dv["name"], dv.get("event") or "", rnd) for _ in range(n)])
                else:
                    rounds = []
                    for h in dv["heats"]:
                        if h["round"] not in rounds:
                            rounds.append(h["round"])
                    k = rounds.index(cur_round) + 1 if cur_round in rounds else len(rounds)
                    if k >= len(rounds):
                        return "%s has no round after %s in LiveHeats" % (dv["name"], cur_round)
                    groups.append([h["id"] for h in dv["heats"] if h["round"] == rounds[k]])
            new = []
            for k in range(max(len(g) for g in groups)):
                new += [g[k] for g in groups if k < len(g) and g[k] not in items and g[k] not in new]
            program["items"] = items + new
            program["last_block"] = new
        elif d.get("progress"):
            r = progress_round(d["progress"])
            if not r.startswith("ok"):
                return r
            save_program()
            return r
        elif d.get("crews"):
            # crew names for a typed-in heat: {"heat": id, "crews": {"1": "name", ...}}
            c = d["crews"]
            dv, h = heat_lookup(str(c.get("heat")))
            if not h or not dv.get("manual"):
                return "Crew names can only be typed for heats added here"
            h["crews"] = sorted([[int(k), re.sub(r"\s+", " ", str(v)).strip()[:60]]
                                 for k, v in (c.get("crews") or {}).items()
                                 if str(k).isdigit() and 1 <= int(k) <= 20 and str(v).strip()])
            if S["heat"] and S["heat"].get("heat_id") == h["id"]:
                S["heat"] = heat_info(dv, h)          # the chosen heat shows the new names at once
                save_settings()
        elif d.get("delete"):
            hid = str(d["delete"])
            if hid in sent and hid not in raced and not d.get("force"):
                return "PATIENTS:Patients for %s are already on the water. Delete it anyway?" % heat_name(hid)
            dv, h = heat_lookup(hid)
            if not h or not dv.get("manual"):
                return "Only heats added here can be deleted - remove LiveHeats heats from the program instead"
            if hid in raced:
                return "That heat has been raced - it can't be deleted"
            dv["heats"].remove(h)
            if hid in items:
                items.remove(hid)
            program["manual"] = [x for x in program["manual"] if x["heats"]]
        elif d.get("add"):
            at = d.get("at")
            new = []
            for i in ids:
                if i not in items and i not in new and heat_lookup(i)[1]:
                    new.append(i)
            if not new:
                return "Those heats are already in the program"
            if isinstance(at, int) and 0 <= at <= len(items):
                program["items"] = items[:at] + new + items[at:]
            else:
                program["items"] = items + new
            if program["mode"] is None:
                program["mode"] = "on"
        elif d.get("move"):
            hid, to = str(d["move"]), d.get("to")
            if hid not in items or not isinstance(to, int):
                return "not allowed"
            items.remove(hid)
            items.insert(max(0, min(to, len(items))), hid)
        elif d.get("next_up"):
            # run this heat straight after the current one
            hid = str(d["next_up"])
            cur = (S["heat"] or {}).get("heat_id")
            if hid in items:
                items.remove(hid)
            pos = items.index(cur) + 1 if cur in items else 0
            while pos < len(items) and items[pos] in raced:
                pos += 1
            items.insert(pos, hid)
        elif d.get("remove"):
            hid = str(d["remove"])
            if hid in items:
                items.remove(hid)
            program["breaks"].pop(hid, None)
        elif d.get("clear"):
            program["items"] = [i for i in items if i in raced] if d.get("keep_done") else []
        else:
            return "not allowed"
        save_program()
    return "ok"


def manual_heat(full_name, event_id, rnd, no=None):
    # a typed-in heat in the division called full_name (created if needed); returns its id
    dv = next((d for d in program["manual"] if d["name"].lower() == full_name.lower()), None)
    if not dv:
        program["seq"] += 1
        dv = {"id": "m%d" % program["seq"], "name": full_name, "event": event_id, "manual": True, "heats": []}
        program["manual"].append(dv)
    if no is None:
        no = max([h["no"] for h in dv["heats"] if h["round"].lower() == rnd.lower()] or [0]) + 1
    old = next((h for h in dv["heats"] if h["round"].lower() == rnd.lower() and h["no"] == no), None)
    if old:
        return old["id"]
    program["seq"] += 1
    h = {"id": "%s-%d" % (dv["id"], program["seq"]), "round": rnd, "no": no, "time": None, "crews": []}
    dv["heats"].append(h)
    return h["id"]


def next_break():
    # a break straight after the current heat (shown on the Results screen instead of the next heat)
    cur = ((S["race_heat"] if S["state"] == "RACING" else S["heat"]) or {}).get("heat_id")
    items = program["items"]
    if program["mode"] != "on" or cur not in items:
        return None
    for i in items[items.index(cur) + 1:]:
        if i in program["breaks"]:
            b = dict(program["breaks"][i])
            b["id"] = i
            return b
        if i not in raced:
            return None
    return None


def hm_today(hm):
    try:
        h, m = [int(x) for x in str(hm).split(":")[:2]]
        return datetime.now().replace(hour=h, minute=m, second=0, microsecond=0)
    except (ValueError, TypeError):
        return None


def est_times():
    # planned and expected start time for every program item (needs a start time, or LiveHeats times)
    out = {}
    tm = program.get("timing") or {}
    mins = max(1, int(tm.get("mins") or 4))
    t = hm_today(tm.get("start")) if tm.get("start") else None
    for hid in program["items"]:
        if hid in program["breaks"]:
            b = program["breaks"][hid]
            if t:
                out[hid] = {"plan": t.strftime("%H:%M")}
                until = hm_today(b.get("until")) if b.get("until") else None
                t = max(t, until) if until else t + timedelta(minutes=int(b.get("mins") or 0))
            continue
        dv, h = heat_lookup(hid)
        lt = None
        if h and h.get("time"):
            try:
                lt = datetime.fromisoformat(h["time"].replace("Z", "+00:00")).astimezone().replace(tzinfo=None)
            except ValueError:
                lt = None
        plan = lt or t
        if plan:
            out[hid] = {"plan": plan.strftime("%H:%M"), "_p": plan}
            t = plan + timedelta(minutes=mins)
    # expected: nothing still to run can start earlier than now + one heat slot per heat before it
    cur = ((S["race_heat"] if S["state"] == "RACING" else S["heat"]) or {}).get("heat_id")
    items = program["items"]
    if cur in items:
        now = datetime.now()
        k = 0 if S["state"] in ("IDLE", "ARMED") else 1
        for hid in items[items.index(cur):]:
            if hid in raced and hid != cur:
                continue
            if hid in program["breaks"]:
                b = program["breaks"][hid]
                until = hm_today(b.get("until")) if b.get("until") else None
                now = max(now + timedelta(minutes=k * mins), until) if until else now + timedelta(minutes=k * mins + int(b.get("mins") or 0))
                k = 0
                if hid in out:
                    out[hid]["exp"] = now.strftime("%H:%M")
                continue
            e = now + timedelta(minutes=k * mins)
            p = out.get(hid, {}).get("_p")
            if p:
                out[hid]["exp"] = max(e, p).strftime("%H:%M")
            k += 1
    for v in out.values():
        v.pop("_p", None)
    return out


def club_list():
    names = set()
    for dv in all_divisions():
        for h in dv["heats"]:
            names.update(v for v in (h.get("clubs") or {}).values() if v)
            if dv.get("manual"):
                names.update(n for _, n in h["crews"] if n)
    return sorted(names, key=str.lower)


def club_match(club, heat_rec, lane):
    c = club.strip().lower()
    if not c:
        return False
    cl = ((heat_rec.get("clubs") or {}).get(str(lane)) or "").lower()
    cn = ((heat_rec.get("crews") or {}).get(str(lane)) or "").lower()
    return cl == c or c in cn


def team_view(club):
    # a team manager's view: their crews' heats still to come, and their results so far
    times = est_times()
    up = []
    if prog_on():
        order = [i for i in program["items"] if i not in program["breaks"] and i not in raced]
    else:
        order = [h["id"] for dv in all_divisions() for h in dv["heats"] if h["id"] not in raced]
    cur = ((S["race_heat"] if S["state"] == "RACING" else S["heat"]) or {}).get("heat_id")
    for pos, hid in enumerate(order):
        dv, h = heat_lookup(hid)
        if not h:
            continue
        hi = heat_info(dv, h)
        for lane, name in sorted(hi["crews"].items(), key=lambda x: int(x[0])):
            if club_match(club, hi, lane):
                away = pos - order.index(cur) if (prog_on() and cur in order) else None
                if hid in sent:
                    pat = "sent"
                elif away is not None and away <= 5:
                    pat = "now"
                elif away is not None:
                    rt = times.get(order[pos - 5]) or {}
                    pat = rt.get("exp") or rt.get("plan") or ""
                else:
                    pat = ""
                up.append({"heat": hi, "lane": int(lane), "crew": name, "now": hid == cur, "patients": pat,
                           "away": pos - order.index(cur) if (prog_on() and cur in order) else None,
                           "time": (times.get(hid) or {}).get("exp") or (times.get(hid) or {}).get("plan"),
                           "check": checkin.get(hid, {}).get(lane)})
    res = []
    for r in sorted(history_summary(), key=lambda r: r.get("race") or 0, reverse=True):
        ht = r.get("heat") or {}
        for row in r.get("rows", []):
            if club_match(club, ht, row["lane"]):
                res.append({"race": r.get("race"), "heat": ht, "lane": row["lane"], "crew": (ht.get("crews") or {}).get(str(row["lane"])),
                            "place": row.get("place"), "t_us": row.get("t_us"), "status": row.get("status"),
                            "final": is_confirmed(r.get("race")), "tie": row["lane"] in (r.get("ties") or [])})
    return {"club": club, "upcoming": up[:40], "results": res[:60]}


def heat_name(hid):
    dv, h = heat_lookup(hid)
    return "%s %s Heat %s" % (dv["name"], h["round"], h["no"]) if h else "that heat"


def marshal_check(d):
    if "required" in d:                      # how many heats of patients sit in marshalling
        if str(d["required"]) not in ("2", "3"):
            return "not allowed"
        with lock:
            program["required"] = int(d["required"])
            save_program()
        return "ok"
    if "sent" in d:                          # the Marshal has sent this heat's patients out on the water
        hid = str(d.get("heat", ""))
        with lock:
            dv, h = heat_lookup(hid)
            if not h:
                return "Heat not found"
            if d["sent"]:
                ck = checkin.get(hid, {})
                lanes = [str(l) for l, _ in h["crews"]] or [str(l) for l in S["lanes"]]
                sent[hid] = {"at": datetime.now().strftime("%H:%M"), "who": str(d.get("who") or "")[:30],
                             "missing": [l for l in lanes if not ck.get(l)]}
            else:
                sent.pop(hid, None)
            save_program()
        return "ok"
    hid, lane, status = str(d.get("heat", "")), str(d.get("lane", "")), str(d.get("status", ""))
    if not lane.isdigit() or status not in ("present", "scratched", ""):
        return "not allowed"
    with lock:
        c = checkin.setdefault(hid, {})
        if status:
            c[lane] = status
        else:
            c.pop(lane, None)
        save_program()
    return "ok"


CENTRE_OUT = [5, 4, 6, 3, 7, 2, 8, 1, 9, 10]


def progress_round(p):
    # typed-in heats only: fill the next round's lanes from the results (a draft for the officials to check)
    div_id, frm, to = str(p.get("div", "")), str(p.get("from", "")), str(p.get("to", ""))
    try:
        top, fast, per = int(p.get("top") or 0), int(p.get("fastest") or 0), int(p.get("per") or 9)
    except (TypeError, ValueError):
        return "Numbers only, please"
    dv = next((d for d in program["manual"] if d["id"] == div_id), None)
    if not dv:
        return "Choose a division added here (LiveHeats does its own progression)"
    src = [h for h in dv["heats"] if h["round"] == frm]
    dst = sorted([h for h in dv["heats"] if h["round"] == to], key=lambda h: h["no"])
    if not src or not dst:
        return "Add the %s heats first" % (to if src else frm)
    if not 1 <= per <= 10:
        return "Crews per heat must be 1 to 10"
    latest = {r.get("race"): r for r in history_summary()}
    rows, missing = [], []
    for h in src:
        rec = latest.get(raced.get(h["id"]))
        if not rec:
            missing.append("Heat %d" % h["no"])
            continue
        crews = (rec.get("heat") or {}).get("crews") or {}
        for row in rec.get("rows", []):
            if row.get("place"):
                rows.append({"heat": h["no"], "place": row["place"], "t": row.get("t_us"),
                             "crew": crews.get(str(row["lane"])) or "Heat %d lane %d" % (h["no"], row["lane"])})
    if missing:
        return "Not raced yet: " + ", ".join(missing)
    q = [r for r in rows if r["place"] <= top]
    rest = sorted([r for r in rows if r["place"] > top and r["t"] is not None], key=lambda r: r["t"])
    q += rest[:fast]
    if not q:
        return "No crews qualify with those numbers"
    if len(q) > per * len(dst):
        return "%d crews qualify but %d heats x %d crews only fit %d" % (len(q), len(dst), per, per * len(dst))
    # seed: best place first, then fastest time; snake across the heats; centre lanes first
    q.sort(key=lambda r: (r["place"], r["t"] if r["t"] is not None else 1e18))
    heats = [[] for _ in dst]
    for i, r in enumerate(q):
        rnd, pos = divmod(i, len(dst))
        heats[pos if rnd % 2 == 0 else len(dst) - 1 - pos].append(r["crew"])
    lanes = [l for l in CENTRE_OUT if l <= per]
    for h, crews in zip(dst, heats):
        h["crews"] = sorted([[lanes[i], c] for i, c in enumerate(crews)])
        if S["heat"] and S["heat"].get("heat_id") == h["id"]:
            S["heat"] = heat_info(dv, h)          # the chosen heat shows the new crews at once
            save_settings()
    return "ok:%d crews placed into %d heat%s" % (len(q), len(dst), "" if len(dst) == 1 else "s")


def template_action(d):
    with lock:
        name = re.sub(r"\s+", " ", str(d.get("name") or "")).strip()[:40]
        if d.get("save"):
            if not name:
                return "Give the template a name"
            items = []
            for hid in program["items"]:
                if hid in program["breaks"]:
                    b = program["breaks"][hid]
                    items.append({"break": b.get("label"), "until": b.get("until"), "mins": b.get("mins")})
                    continue
                dv, h = heat_lookup(hid)
                if h:
                    items.append({"div": dv["name"], "event": dv.get("event") or "", "round": h["round"], "no": h["no"]})
            templates[name] = {"items": items, "timing": program.get("timing") or {}}
            save_templates()
            return "ok"
        if d.get("delete"):
            templates.pop(name, None)
            save_templates()
            return "ok"
        if d.get("load"):
            tp = templates.get(name)
            if not tp:
                return "Template not found"
            done = [i for i in program["items"] if i in raced or (i in sent and i not in program["breaks"])]
            new = []
            for it in tp["items"]:
                if it.get("break") is not None:
                    program["seq"] += 1
                    bid = "brk-%d" % program["seq"]
                    program["breaks"][bid] = {"label": it.get("break") or "Break", "until": it.get("until"), "mins": it.get("mins")}
                    new.append(bid)
                    continue
                # a LiveHeats heat with the same division, round and number if the draw has one; else typed in
                hid = None
                for dv in (draw or {}).get("divisions", []):
                    if dv["name"].lower() == str(it["div"]).lower():
                        hid = next((h["id"] for h in dv["heats"] if h["round"] == it["round"] and h["no"] == it["no"]), None)
                if not hid:
                    hid = manual_heat(it["div"], it.get("event") or "", it["round"], it["no"])
                if hid not in done and hid not in new:
                    new.append(hid)
            program["items"] = done + new
            program["timing"] = dict(tp.get("timing") or {})
            program["mode"] = "on"
            save_program()
            return "ok"
    return "not allowed"


def program_list():
    out = []
    cur = (S["race_heat"] if S["state"] == "RACING" else S["heat"]) or {}
    nxt = prog_after(cur.get("heat_id"), 2) if program["items"] else []
    times = est_times()
    for i, hid in enumerate(program["items"]):
        if hid in program["breaks"]:
            b = program["breaks"][hid]
            out.append({"id": hid, "brk": True, "label": b.get("label"), "until": b.get("until"), "mins": b.get("mins"),
                        "est": times.get(hid)})
            continue
        dv, h = heat_lookup(hid)
        out.append({"id": hid, "div": dv["name"] if dv else None, "div_id": dv["id"] if dv else None,
                    "round": h["round"] if h else None, "no": h["no"] if h else None,
                    "time": h.get("time") if h else None, "crews": len(h["crews"]) if h else 0,
                    "raced": raced.get(hid), "missing": not h,
                    "now": hid == cur.get("heat_id"), "next": nxt.index(hid) + 1 if hid in nxt else 0,
                    "est": times.get(hid), "checkin": checkin.get(hid, {})})
    for o in out:
        dv, _ = heat_lookup(o["id"])
        o["manual"] = bool(dv and dv.get("manual"))
    return {"mode": program["mode"], "items": out, "ver": program["ver"], "have_heats": have_heats(),
            "timing": program.get("timing") or {}, "templates": sorted(templates),
            "lh": bool((draw or {}).get("schedule")), "lh_src": (draw or {}).get("schedule_src", "")}


def program_summary():
    cur = (S["race_heat"] if S["state"] == "RACING" else S["heat"]) or {}
    left = len(prog_after(cur.get("heat_id"))) if program["items"] else 0
    sched = (draw or {}).get("schedule") or []
    behind = None
    if cur.get("heat_id"):
        dv, h = heat_lookup(cur["heat_id"])
        if h and h.get("time"):
            try:
                when = datetime.fromisoformat(h["time"].replace("Z", "+00:00"))
                behind = round((datetime.now(when.tzinfo) - when).total_seconds() / 60)
            except ValueError:
                behind = None
    if behind is None and cur.get("heat_id") and (program.get("timing") or {}).get("start") and cur["heat_id"] not in raced:
        p = (est_times().get(cur["heat_id"]) or {}).get("plan")
        if p:
            behind = round((datetime.now() - hm_today(p)).total_seconds() / 60)
    return {"mode": program["mode"], "total": len(program["items"]), "left": left, "ver": program["ver"],
            "manual": sum(len(d["heats"]) for d in program["manual"]),
            "warn": program["mode"] == "on" and left < 2,
            "lh": bool(sched), "lh_changed": bool(program["lh_sig"] and sched and ",".join(sched) != program["lh_sig"]),
            "behind": behind}


def heat_info(dv, h):
    return {"div_id": dv["id"], "div": dv["name"], "heat_id": h["id"], "round": h["round"], "no": h["no"],
            "crews": {str(lane): name for lane, name in h["crews"]}, "clubs": dict(h.get("clubs") or {}),
            "members": dict(h.get("members") or {})}


def select_heat(data):
    """data: {div, heat} to choose, {next: true} for the following heat, {clear: true} for none"""
    with lock:
        if prog_on() and not data.get("swap"):
            # the program decides the order; Admin changes it on the Program tab
            program_sync()
            return "ok" if data.get("next") else "The program decides the heat - change the order on the Program tab"
        if data.get("clear"):
            S["heat"] = None
            save_settings()
            return "ok"
        if data.get("swap"):
            # move a crew to another lane (e.g. a broken button): swaps the two lanes' crews
            if S["state"] == "RACING":
                return "Swap lanes between races"
            if not S["heat"]:
                return "Choose a heat first"
            try:
                a, b = [str(int(x)) for x in data["swap"]]
            except (TypeError, ValueError):
                return "not allowed"
            h = dict(S["heat"])
            for key in ("crews", "clubs", "members"):          # the crew's club and people move with it
                m = dict(h.get(key) or {})
                ca, cb = m.pop(a, None), m.pop(b, None)
                if ca:
                    m[b] = ca
                if cb:
                    m[a] = cb
                h[key] = m
            h["swaps"] = (h.get("swaps") or []) + [[int(a), int(b)]]
            S["heat"] = h
            save_settings()
            return "ok"
        if not have_heats():
            return "No heats yet - load the LiveHeats draw or add heats on the Program tab"
        if data.get("next") and prog_on():
            nxt = prog_after((S["heat"] or {}).get("heat_id"), 1)
            if not nxt:
                return "No more heats in the program - add more on the Program tab"
            dv, h = heat_lookup(nxt[0])
            if not h:
                return "That heat is no longer in the LiveHeats draw - check the Program tab"
            S["heat"] = heat_info(dv, h)
            if dv["event"] or dv.get("manual"):
                S["event"] = dv["event"]           # a typed-in "Other" event clears it (legs from presses)
            save_settings()
            return "ok"
        div_id = str(data.get("div") or (S["heat"] or {}).get("div_id") or "")
        dv = next((x for x in all_divisions() if x["id"] == div_id), None)
        if not dv:
            return "Division not found"
        if data.get("next"):
            cur = (S["heat"] or {}).get("heat_id")
            ids = [h["id"] for h in dv["heats"]]
            if cur not in ids:
                return "Choose a heat first"
            if ids.index(cur) + 1 >= len(ids):
                return "That was the last heat in this division"
            h = dv["heats"][ids.index(cur) + 1]
        else:
            h = next((x for x in dv["heats"] if x["id"] == str(data.get("heat"))), None)
            if not h:
                return "Heat not found in the loaded draw"
        S["heat"] = heat_info(dv, h)
        if dv["event"] or dv.get("manual"):
            S["event"] = dv["event"]           # the division says which event it is       # the division says which event it is
        save_settings()
    return "ok"


def upcoming(n=2):
    # the heat on now (or next up) and the heats after it in the same division
    now = S["race_heat"] if S["state"] == "RACING" else S["heat"]
    nxt = []
    if prog_on():
        for hid in prog_after((now or {}).get("heat_id"), n):
            dv, h = heat_lookup(hid)
            if h:
                nxt.append(heat_info(dv, h))
        return now, nxt
    if now:
        dv = next((x for x in all_divisions() if x["id"] == now.get("div_id")), None)
        if dv:
            ids = [h["id"] for h in dv["heats"]]
            if now.get("heat_id") in ids:
                for h in dv["heats"][ids.index(now["heat_id"]) + 1:][:n]:
                    nxt.append(heat_info(dv, h))
    return now, nxt


def draw_info():
    if not draw:
        return None
    return {"id": draw["id"], "name": draw["name"], "loaded_at": draw.get("loaded_at"),
            "divisions": len(draw["divisions"]), "heats": sum(len(d["heats"]) for d in draw["divisions"])}


# ---------------- history (the app's own copy) ----------------
def load_history():
    if not os.path.exists(HIST_FILE):
        return
    with open(HIST_FILE, encoding="utf-8") as fh:
        for ln in fh:
            ln = ln.strip()
            if ln:
                try:
                    history.append(json.loads(ln))
                    note_raced(history[-1])
                except ValueError:
                    pass


def backup_targets():
    # only sticks that have a folder called IRB_backup at the top (so nothing else is touched)
    if os.name == "nt":
        found = []
        for letter in "DEFGHIJKLMNOPQRSTUVWXYZ":
            p = letter + ":\\IRB_backup"
            if os.path.isdir(p):
                found.append(p)
        return found
    return [p for pat in ("/media/*/IRB_backup", "/media/*/*/IRB_backup", "/mnt/*/IRB_backup")
            for p in glob.glob(pat) if os.path.isdir(p)]


def backup():
    try:
        dests = backup_targets()
        if not dests:
            with lock:
                S["backup"] = {"ok": False, "msg": "No backup stick found"}
            return
        for dst in dests:
            out = os.path.join(dst, "timing_data")
            os.makedirs(out, exist_ok=True)
            for f in os.listdir(DATA):
                src = os.path.join(DATA, f)
                if os.path.isfile(src):
                    shutil.copy2(src, os.path.join(out, f))
        with lock:
            S["backup"] = {"ok": True, "at": datetime.now().strftime("%H:%M:%S"), "where": ", ".join(dests)}
    except OSError as e:
        with lock:
            S["backup"] = {"ok": False, "msg": "Backup failed: %s" % e}


def note_raced(d):
    h = d.get("heat")
    if h and h.get("heat_id"):
        raced[h["heat_id"]] = d.get("race")


def save_result(d):
    key = (d.get("race"), d.get("version"))
    for h in reversed(history):
        if (h.get("race"), h.get("version")) == key:
            if h.get("rows") == d.get("rows") and h.get("changes") == d.get("changes"):
                return          # already have this exact result (re-sent)
            break
    rec = dict(d)
    rec["saved_at"] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    history.append(rec)
    with open(HIST_FILE, "a", encoding="utf-8") as fh:
        fh.write(json.dumps(rec) + "\n")


def log_raw(line):
    name = os.path.join(DATA, "pico_log_%s.txt" % datetime.now().strftime("%Y-%m-%d"))
    with open(name, "a", encoding="utf-8") as fh:
        fh.write("%s  %s\n" % (datetime.now().strftime("%H:%M:%S.%f")[:-3], line))


def fmt_s(us):
    return "" if us is None else "%d.%06d" % (us // 1_000_000, us % 1_000_000)


def history_csv():
    latest = {}
    for h in history:
        latest[h.get("race")] = max(latest.get(h.get("race"), -1), h.get("version", 0))
    out = io.StringIO()
    w = csv.writer(out)
    w.writerow(["saved_at", "race", "event", "division", "round", "heat", "version", "final", "legs", "lane", "crew", "place",
                "time_s", "status", "dq_code", "presses_s", "officials_changes", "changes_by", "note", "video_go"])
    for h in history:
        ch = "; ".join("lane %s %s" % (k, v) for k, v in sorted(h.get("changes", {}).items()))
        if h.get("legs_set"):
            ch = ("legs set to %d; " % h["legs_set"]) + ch
        final = "yes" if latest.get(h.get("race")) == h.get("version") else "no"
        ht = h.get("heat") or {}
        crews = ht.get("crews") or {}
        fl = flags.get(str(h.get("race")), {})
        by = "; ".join("%s %s: %s" % tuple(x) for x in fl.get("log", []))
        go = datetime.fromtimestamp(h["go_wall"]).strftime("%H:%M:%S.%f")[:-3] if h.get("go_wall") else ""
        for r in h.get("rows", []):
            w.writerow([h.get("saved_at"), h.get("race"), h.get("event") or "", ht.get("div", ""), ht.get("round", ""),
                        ht.get("no", ""), h.get("version"), final, h.get("legs"),
                        r.get("lane"), crews.get(str(r.get("lane")), ""), r.get("place") or "", fmt_s(r.get("t_us")), r.get("status"),
                        fl.get("dq", {}).get(str(r.get("lane")), "") if r.get("status") == "DQ" else "",
                        ";".join(fmt_s(x) for x in r.get("presses_us", [])), ch, by, fl.get("note", ""), go])
    return out.getvalue()


# ---------------- Pico link ----------------
def find_port():
    if PICO_PORT:
        return PICO_PORT
    for p in serial.tools.list_ports.comports():
        if p.vid == PICO_VID:
            return p.device
    return None


def handle_line(line):
    log_raw(line)
    if not line.startswith("@"):
        if line.strip():
            messages.append([datetime.now().strftime("%H:%M:%S"), line])
        S["at_prompt"] = line.startswith(">>>")
        return
    try:
        d = json.loads(line[1:])
    except ValueError:
        return
    ev = d.get("ev")
    S["at_prompt"] = False
    if ev == "hello":
        S["fw"] = d.get("fw")
        S["lanes"] = d.get("lanes", [])
        S["race"] = d.get("race", 0)
        S["min_leg_s"] = d.get("min_leg_s", 15)
        S["app_start"] = bool(d.get("app_start"))
        S["ties"] = bool(d.get("ties"))
        S["has_test"] = bool(d.get("test"))
        S["beat"] = bool(d.get("beat"))
        if d.get("clock") and ser:
            try:                    # give the Pico the real date and time for its history file
                ser.write(("clock %s\r\n" % datetime.now().strftime("%Y %m %d %H %M %S")).encode())
            except (serial.SerialException, OSError):
                pass
    elif ev == "state":
        new = d.get("state")
        if new == "RACING" and S["state"] != "RACING":
            S["go_at"] = time.time()
            S["live"] = {}
            S["race_event"] = find_event(S["event"])   # the event is fixed at GO
            S["race_heat"] = S["heat"]                 # and so is the heat
            S["race_go_wall"] = S["go_at"]
        if new == "DONE" and S["state"] == "RACING" and draw:
            threading.Thread(target=auto_reload, daemon=True).start()
        if new in ("ARMED", "IDLE"):
            S["live"] = {}
        if new == "ARMED":
            S["results"] = None
        S["state"] = new
        S["race"] = d.get("race", S["race"])
    elif ev == "running":
        S["go_at"] = time.time() - d.get("elapsed_us", 0) / 1e6
        S["race_go_wall"] = S["race_go_wall"] or S["go_at"]
        S["live"] = {k: list(v) for k, v in d.get("hits", {}).items()}
    elif ev == "hit":
        S["live"].setdefault(str(d["lane"]), []).append(d["t_us"])
    elif ev == "faults":
        S["faults"] = d.get("list", [])
        S["faults_racing"] = bool(d.get("racing"))
    elif ev == "test":
        on = bool(d.get("on"))
        if on and not S["test"]:
            S["test_seen"] = []
            S["test_count"] = {}
            S["test_last"] = None
            S["test_clash"] = []
        if S["test"] and not on:
            need = ["Lane %d" % l for l in S["lanes"]] + ["SET", "GO", "FINISH"]
            S["last_test"] = {"date": datetime.now().strftime("%Y-%m-%d"), "at": datetime.now().strftime("%H:%M"),
                              "seen": list(S["test_seen"]), "missing": [x for x in need if x not in S["test_seen"]],
                              "clash": ["%s + %s%s" % (c["a"], c["b"], "" if c["status"] == "fault" else " (not re-checked)")
                                        for c in S["test_clash"]]}
            save_settings()
        S["test"] = on
    elif ev == "input":
        if S["test"]:
            name = d.get("name")
            if name not in S["test_seen"]:
                S["test_seen"].append(name)
            S["test_count"][name] = S["test_count"].get(name, 0) + 1
            S["test_last"] = name
            if clash_skip[0] == name and time.time() - clash_skip[1] < 1:
                clash_skip[0] = None          # this press was the second half of a together-press
            else:
                # a press on its own: a "suspect" pair clears once both its buttons have worked alone
                for c in S["test_clash"]:
                    if c["status"] == "suspect" and name in (c["a"], c["b"]) and name not in c["clean"]:
                        c["clean"].append(name)
                S["test_clash"] = [c for c in S["test_clash"]
                                   if not (c["status"] == "suspect" and len(c["clean"]) == 2)]
    elif ev == "clash":
        if S["test"]:
            a, b = d.get("a"), d.get("b")
            clash_skip[0], clash_skip[1] = b, time.time()
            c = next((x for x in S["test_clash"] if {x["a"], x["b"]} == {a, b}), None)
            if c:
                c["status"] = "fault"         # together again: real wiring fault, stays for this test
                c["times"] += 1
                c["ms"] = d.get("ms")
            else:
                S["test_clash"] = (S["test_clash"] + [{"a": a, "b": b, "ms": d.get("ms"), "times": 1,
                                                       "status": "suspect", "clean": []}])[-10:]
    elif ev == "batt":
        S["batt"] = d.get("v")
        S["batt_at"] = time.time()
    elif ev == "recall":
        messages.append([datetime.now().strftime("%H:%M:%S"), "RECALL - race cancelled"])
    elif ev == "results":
        ev_info = S["race_event"] or find_event(S["event"])
        if ev_info and ev_info["legs"]:
            d["event"] = ev_info["name"]
            d["event_legs"] = ev_info["legs"]
        heat = S["race_heat"] or S["heat"]
        if heat:
            d["heat"] = heat
        if S["race_go_wall"]:
            d["go_wall"] = round(S["race_go_wall"], 3)
        if S["practice"]:
            d["practice"] = True               # practice: shown, never saved or queued
            S["results"] = d
            return
        S["results"] = d
        save_result(d)
        note_raced(d)
        threading.Thread(target=backup, daemon=True).start()


def safe_handle(line):
    # A bad line or a full disk must never stop the link to the Pico.
    global last_rx
    last_rx = time.time()
    try:
        with lock:
            handle_line(line)
    except Exception as e:
        print("Problem handling a Pico message:", e)


def note(text):
    print(text)
    with lock:
        messages.append([datetime.now().strftime("%H:%M:%S"), text])


STOPPING = threading.Event()      # set before a restart: the Pico link closes its own port, then says so
PORT_FREE = threading.Event()


def serial_loop():
    # never stops for good: anything unexpected is noted and the link starts again
    while not STOPPING.is_set():
        try:
            serial_loop_once()
        except Exception as e:
            with lock:
                S["connected"] = False
            note("Pico link restarted after an error: %s" % str(e)[:120])
            time.sleep(2)
    PORT_FREE.set()


def serial_loop_once():
    global ser, last_rx
    told = None               # last problem printed, so it isn't repeated every 2 s
    busy_since = None
    while not STOPPING.is_set():
        port = find_port()
        if not port:
            with lock:
                S["connected"] = False
                S["port"] = None
            if told != "none":
                note("Waiting for the Pico - plug it in by USB.")
                told = "none"
            time.sleep(2)
            continue
        s = None
        opened = False
        try:
            s = serial.Serial(port, 115200, timeout=0.2, write_timeout=1)
            opened = True
            with lock:
                ser = s
                S["connected"] = True
                S["port"] = port
            note("Connected to Pico on %s" % port)
            last_rx = time.time()
            told = None
            busy_since = None
            s.write(b"j\r\n")           # ask for full status
            buf = b""
            while not STOPPING.is_set():
                chunk = s.read(512)
                if chunk:
                    buf += chunk
                    while b"\n" in buf:
                        ln, buf = buf.split(b"\n", 1)
                        safe_handle(ln.decode("utf-8", "ignore").rstrip("\r"))
                elif buf.startswith(b">>>"):
                    safe_handle(buf.decode("utf-8", "ignore"))
                    buf = b""
        except (serial.SerialException, OSError) as e:
            msg = str(e)
            with lock:
                S["connected"] = False
                ser = None
            if opened:
                # it was working, so the cable was pulled or the Pico reset
                note("Pico unplugged or reset - reconnecting...")
                told = "lost"
            elif "Access is denied" in msg or "busy" in msg.lower() or "PermissionError" in msg:
                # Windows also says this for a moment while a Pico is being plugged in
                busy_since = busy_since or time.time()
                if told not in ("busy", "lost", "stuck"):
                    note("Pico port is in use - close Thonny.")
                    told = "busy"
                elif told == "busy" and time.time() - busy_since > 10:
                    note("Pico port still in use - unplug the Pico's USB, wait 3 seconds and plug it back in.")
                    told = "stuck"
            elif told != "other":
                note("Can't open the Pico port: %s" % msg)
                told = "other"
        finally:
            # Windows keeps a port locked until it is closed, so always let go of it.
            if s is not None:
                with lock:
                    if ser is s:
                        ser = None
                try:
                    s.close()
                except Exception:
                    pass
        if not STOPPING.is_set():
            time.sleep(2)


ADJUST = re.compile(r"^(ok|place|dq|dnf|clear|legs|tie)\b")
CMD_OK = re.compile(r"^(f|j|p|set|go|test on|test off|tie \d+|ok \d+|place \d+ \d+|dq \d+|dnf \d+|clear|clear \d+|legs \d+)$")


def send_cmd(cmd, expect=None, who="", code=""):
    cmd = cmd.strip().lower()
    with lock:
        s = ser
        state = S["state"]
    if not s:
        return "Pico not connected"
    global last_go_sent
    # A hold started on "Cancel" must not end a race that has since started, and a
    # SET or GO tapped on an out-of-date screen must not do the wrong thing.
    if expect and state not in str(expect).split("|"):
        return "Race state changed - nothing was sent"
    if cmd in ("set", "go") and not expect:
        return "not allowed"
    with lock:
        res = S["results"]
        locked = bool(res and is_confirmed(res.get("race")))
    if locked and ADJUST.match(cmd):
        return "Results are confirmed - press Reopen to change them"
    if cmd == "go" and expect == "ARMED":
        # a second tap (or a slow Wi-Fi retry) must never become a recall
        if time.time() - last_go_sent < 6:
            return "GO already sent"
        last_go_sent = time.time()
    try:
        if cmd == "restart":
            for b in (b"\x03", b"\x03", b"\x04"):    # stop, then soft reboot -> main.py runs again
                s.write(b)
                time.sleep(0.2)
            return "ok"
        if not CMD_OK.match(cmd):
            return "not allowed"
        s.write((cmd + "\r\n").encode())
    except (serial.SerialException, OSError):
        return "Pico not connected"
    if ADJUST.match(cmd):
        with lock:
            res = S["results"]
            if res:
                f = flags.setdefault(str(res.get("race")), {})
                code = str(code or "").strip()[:60]
                w = cmd.split()
                codes = f.setdefault("dq", {})
                if w[0] == "clear" and len(w) == 1:
                    codes.clear()                     # undo all -> no DQ codes left
                elif w[0] == "dq" and code:
                    codes[w[1]] = code
                elif len(w) > 1 and w[0] in ("dq", "ok", "dnf", "place", "clear"):
                    codes.pop(w[1], None)             # lane changed again -> old code no longer applies
                f.setdefault("log", []).append([datetime.now().strftime("%H:%M:%S"), str(who or "?")[:30],
                                                cmd + (" (%s)" % code if cmd.startswith("dq ") and code else "")])
                save_flags()
    return "ok"


# ---------------- web server ----------------
def snapshot(role="master", local=True, tok=None):
    official = role in ("master", "admin")
    # built into text while locked, so the Pico thread can't change it half way through
    with lock:
        program_sync()
        d = {k: S[k] for k in ("connected", "port", "fw", "lanes", "state", "race", "faults", "live",
                               "results", "at_prompt", "min_leg_s", "event", "race_event", "app_start",
                               "heat", "race_heat")}
        d["draw"] = draw_info()
        for k in ("ties", "has_test", "test", "test_seen", "last_test", "faults_racing"):
            d[k] = S[k]
        d["raced"] = raced
        d["confirmed"] = bool(S["results"] and is_confirmed(S["results"].get("race")))
        d["queue_n"] = len([1 for r in history_summary() if not flags.get(str(r.get("race")), {}).get("entered")])
        d["today"] = datetime.now().strftime("%Y-%m-%d")
        for k in ("test_count", "test_last", "test_clash", "beat", "batt", "practice", "backup"):
            d[k] = S[k]
        d["silent"] = bool(S["connected"] and S["beat"] and time.time() - last_rx > 7)
        d["batt_old"] = bool(S["batt_at"] and time.time() - S["batt_at"] > 60)
        res = S["results"]
        d["res_flags"] = flags.get(str(res.get("race")), {}) if res else {}
        now, nxt = upcoming()
        d["now_heat"], d["next_heats"] = now, nxt
        d["program"] = program_summary()
        d["official"] = official
        d["role"] = role
        d["can_start"] = role in ("master", "starter")
        d["local"] = local
        d.update(access_view(role, tok))
        d["role_fix"] = role_fix
        d["brand"] = dict(BRAND, logo=int(os.path.getmtime(LOGO_FILE)) if os.path.exists(LOGO_FILE) else 0)
        if role == "master":
            d["update"] = update_view()
            d["past_events"] = past_events()
            d["setup_done"] = SETUP["done"]
            d["owner"] = {"set": bool(OWNER["pin"]), "open": bool(OWNER["pin"]) and owner_ok(),
                          "mins": max(0, int((OWNER["open_until"] - time.time()) // 60) + 1) if OWNER["pin"] and owner_ok() else 0}
            d["firewall"] = {"state": FIREWALL["state"], "busy": FIREWALL["busy"]}
            d["kit"] = KIT["text"]
            d["upd_key"] = bool(UPD_KEY["v"])
        hs = [x for x in (S["heat"], S["race_heat"], (S["results"] or {}).get("heat")) + tuple(nxt) if x]
        d["checkin"] = {x["heat_id"]: checkin.get(x["heat_id"], {}) for x in hs if x.get("heat_id")}
        d["sent"] = {x["heat_id"]: sent[x["heat_id"]] for x in hs if x.get("heat_id") in sent}
        d["next_break"] = next_break()
        d["elapsed"] = (time.time() - S["go_at"]) if (S["state"] == "RACING" and S["go_at"]) else None
        d["messages"] = list(messages)[-20:]
        d["app"] = APP_VERSION
        d["events"] = EVENTS
        return json.dumps(d)


def history_summary():
    latest = {}
    for h in history:
        latest[h.get("race")] = h
    out = []
    for k in sorted(latest, key=lambda r: r or 0, reverse=True)[:100]:
        rec = dict(latest[k])
        rec["flags"] = flags.get(str(k), {})
        out.append(rec)
    return out


class H(BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def is_local(self):
        ip = self.client_address[0]
        return ip in ("127.0.0.1", "::1") or ip.startswith("::ffff:127.")

    def token(self):
        m = re.search(r"irb_token=([0-9a-f]+)", self.headers.get("Cookie", ""))
        return m.group(1) if m else None

    def role(self):
        # the timing computer itself is Master; phones by the level the Master approved them for
        if self.is_local():
            return "master"
        with lock:
            access_check()
            o = officials.get(self.token())
            if not o:
                return "viewer"
            o["seen"] = time.time()
            return o["role"]

    def is_official(self):
        return self.role() in ("master", "admin")

    def send(self, code, body, ctype="application/json", extra=None):
        if isinstance(body, str):
            body = body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Cache-Control", "no-store")
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        if self.path in ("/", "/index.html"):
            self.send(200, PAGE, "text/html; charset=utf-8")
        elif self.path.startswith("/api/state"):
            self.send(200, snapshot(self.role(), self.is_local(), self.token()))
        elif self.path.startswith("/api/queue"):
            with lock:
                body = json.dumps(entry_queue())
            self.send(200, body)
        elif self.path.startswith("/api/program"):
            with lock:
                body = json.dumps(program_list())
            self.send(200, body)
        elif self.path.startswith("/api/upcoming"):
            with lock:
                now, nxt = upcoming(10)
                hs = [h for h in ([now] if now else []) + nxt
                      if S["state"] == "RACING" and h is now or h.get("heat_id") not in raced][:10]   # the marshal only needs heats still to race
                body = json.dumps({"heats": hs, "checkin": {h["heat_id"]: checkin.get(h["heat_id"], {}) for h in hs},
                                   "sent": {h["heat_id"]: sent[h["heat_id"]] for h in hs if h["heat_id"] in sent},
                                   "required": program.get("required", 2), "times": est_times()})
            self.send(200, body)
        elif self.path.startswith("/api/team"):
            q = urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query)
            with lock:
                body = json.dumps(team_view((q.get("club") or [""])[0]))
            self.send(200, body)
        elif self.path.startswith("/api/clubs"):
            with lock:
                body = json.dumps(club_list())
            self.send(200, body)
        elif self.path.startswith("/api/templates"):
            with lock:
                body = json.dumps(sorted(templates))
            self.send(200, body)
        elif self.path.startswith("/api/history"):
            with lock:
                body = json.dumps(history_summary())
            self.send(200, body)
        elif self.path.startswith("/api/draw"):
            with lock:
                d = dict(draw or {})
                d["divisions"] = all_divisions()       # typed-in heats are listed after LiveHeats ones
                d["loaded_at"] = "%s/%s" % ((draw or {}).get("loaded_at"), program["ver"])
                body = json.dumps(d)
            self.send(200, body)
        elif self.path.startswith("/logo"):
            try:
                with open(LOGO_FILE, "rb") as fh:
                    self.send(200, fh.read(), "image/png")
            except OSError:
                self.send(404, '{"error":"no logo"}')
        elif self.path.startswith("/event_pack.zip") or self.path.startswith("/diagnostics.zip"):
            if self.role() != "master":
                self.send(403, '{"error":"Timing desk only"}')
                return
            stamp = datetime.now().strftime("%Y-%m-%d_%H%M")
            if self.path.startswith("/diagnostics"):
                body, fname = diagnostics(), "IRB_problem_report_%s.zip" % stamp
            else:
                q = urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query)
                name = (q.get("e") or [""])[0]
                body = event_pack(name)
                fname = "IRB_results_%s.zip" % (re.sub(r"[^\w\-]+", "_", name) if name else "today_" + stamp)
            if body is None:
                self.send(404, '{"error":"not found"}')
            else:
                self.send(200, body, "application/zip", {"Content-Disposition": 'attachment; filename="%s"' % fname})
        elif self.path.startswith("/history.csv"):
            with lock:
                body = history_csv()
            name = "race_history_%s.csv" % datetime.now().strftime("%Y-%m-%d")
            self.send(200, body, "text/csv; charset=utf-8",
                      {"Content-Disposition": 'attachment; filename="%s"' % name})
        else:
            self.send(404, '{"error":"not found"}')

    def do_POST(self):
        n = int(self.headers.get("Content-Length", 0) or 0)
        try:
            data = json.loads(self.rfile.read(n) or b"{}")
            if not isinstance(data, dict):
                data = {}
        except ValueError:
            data = {}
        cookie = lambda tok: {"Set-Cookie": "irb_token=%s; Max-Age=31536000; Path=/; SameSite=Strict" % tok}
        if self.path.startswith("/api/new_event"):        # Master: put today's event away and start clean
            r = new_event(data) if self.role() == "master" else "Only the timing desk can start a new event"
            self.send(200, json.dumps({"result": r}))
            return
        for route, fn in (("/api/owner", owner_action), ("/api/brand", brand_action), ("/api/events", events_action)):
            if self.path.startswith(route):
                if self.role() != "master":
                    r = "Only the timing desk can do that"
                else:
                    with lock:
                        r = fn(data)
                self.send(200, json.dumps({"result": r}))
                return
        if self.path.startswith("/api/updkey"):
            r = key_action(data) if self.role() == "master" else "Only the timing desk can do that"
            self.send(200, json.dumps({"result": r}))
            return
        if self.path.startswith("/api/firewall"):
            r = firewall_allow() if self.role() == "master" else "Only the timing desk can do that"
            self.send(200, json.dumps({"result": r}))
            return
        if self.path.startswith("/api/diagnostics"):      # problem report onto the backup stick
            if self.role() != "master":
                self.send(200, json.dumps({"result": "Only the timing desk can do that"}))
                return
            dests = backup_targets()
            if not dests:
                self.send(200, json.dumps({"result": "No USB stick with an IRB_backup folder – use Download instead"}))
                return
            body = diagnostics()
            for dst in dests:
                with open(os.path.join(dst, "IRB_problem_report_%s.zip" % datetime.now().strftime("%Y-%m-%d_%H%M")), "wb") as fh:
                    fh.write(body)
            self.send(200, json.dumps({"result": "ok"}))
            return
        if self.path.startswith("/api/update"):           # Master: check / install / roll back
            r = update_action(data) if self.role() == "master" else "Only the timing desk can update the program"
            self.send(200, json.dumps({"result": r}))
            return
        if self.path.startswith("/api/role"):            # a team manager fills in a role LiveHeats didn't have
            self.send(200, json.dumps({"result": set_role(data)}))
            return
        if self.path.startswith("/api/request"):        # an official asks for access (no login needed)
            tok = self.token() or secrets.token_hex(12)
            with lock:
                access_check()
                r = ask_access(tok, data.get("name"))
                code = (requests_.get(tok) or {}).get("code")
            self.send(200, json.dumps({"result": r, "code": code}), extra=cookie(tok))
            return
        if self.path.startswith("/api/unlock"):         # backup Master phone, only if a Master PIN is set
            pin = str(data.get("pin", ""))
            if not PINS["master"] or pin != PINS["master"]:
                time.sleep(1)
                self.send(200, json.dumps({"result": "Wrong PIN" if PINS["master"] else "The second timing desk phone PIN is turned off"}))
                return
            tok = self.token() or secrets.token_hex(12)
            with lock:
                requests_.pop(tok, None)
                officials[tok] = {"name": str(data.get("name") or "Timing desk phone")[:30], "role": "master", "since": time.time(), "seen": time.time()}
                access_day[0] = today()
                save_settings()
            self.send(200, json.dumps({"result": "ok", "role": "master"}), extra=cookie(tok))
            return
        if self.path.startswith("/api/lock"):           # log out, or cancel a request
            with lock:
                officials.pop(self.token(), None)
                requests_.pop(self.token(), None)
                save_settings()
            self.send(200, json.dumps({"result": "ok"}))
            return
        if str(data.get("cmd", "")).strip().lower() == "restart" and (self.role() != "master" or not owner_ok()):
            self.send(200, json.dumps({"result": "Only the timing desk can restart the timing program" if self.role() != "master" else OWNER_MSG}))
            return
        why = allowed(self.role(), self.path, data)
        if why:
            self.send(200, json.dumps({"result": why}))
            return
        o = officials.get(self.token()) if not self.is_local() else None
        if o:
            data["who"] = o["name"]                     # changes are logged under the approved name
        if self.path.startswith("/api/officials"):
            if self.role() != "master":
                r = "Only the timing desk can do that"
            else:
                with lock:
                    r = officials_action(data)
            self.send(200, json.dumps({"result": r}))
        elif self.path.startswith("/api/marshal"):
            self.send(200, json.dumps({"result": marshal_check(data)}))
        elif self.path.startswith("/api/template"):
            self.send(200, json.dumps({"result": template_action(data)}))
        elif self.path.startswith("/api/confirm"):
            self.send(200, json.dumps({"result": confirm_results(data.get("race"), bool(data.get("undo")), str(data.get("who") or "?"))}))
        elif self.path.startswith("/api/note"):
            self.send(200, json.dumps({"result": save_note(data.get("race"), data.get("text"), data.get("who"))}))
        elif self.path.startswith("/api/practice"):
            with lock:
                S["practice"] = bool(data.get("on"))
            self.send(200, json.dumps({"result": "ok"}))
        elif self.path.startswith("/api/backup"):
            backup()
            with lock:
                b = S["backup"] or {}
            self.send(200, json.dumps({"result": "ok" if b.get("ok") else b.get("msg", "Backup failed")}))
        elif self.path.startswith("/api/entered"):
            self.send(200, json.dumps({"result": mark_entered(data.get("race"), bool(data.get("undo")))}))
        elif self.path.startswith("/api/cmd"):
            self.send(200, json.dumps({"result": send_cmd(str(data.get("cmd", "")), data.get("expect"),
                                                          data.get("who"), data.get("code"))}))
        elif self.path.startswith("/api/draw/load"):
            self.send(200, json.dumps({"result": load_draw(str(data.get("url", "")))}))
        elif self.path.startswith("/api/program"):
            self.send(200, json.dumps({"result": program_action(data)}))
        elif self.path.startswith("/api/heat"):
            self.send(200, json.dumps({"result": select_heat(data)}))
        elif self.path.startswith("/api/event"):
            self.send(200, json.dumps({"result": set_event(str(data.get("id", "")))}))
        else:
            self.send(404, '{"error":"not found"}')


def lan_ip():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("10.255.255.255", 1))     # no data is sent
        ip = s.getsockname()[0]
        s.close()
        return ip
    except OSError:
        return None


PAGE = r"""<!doctype html>
<html lang="en"><head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Race Officials</title>
<style>
:root{
/* Beach look: always light and high contrast - dark screens are unreadable in sun glare.
   Every text colour below is at least 6:1 against white (most over 7:1). */
--bg:#e9edf1;--card:#ffffff;--ink:#07121c;--mute:#2f3d4b;--line:#8e9cab;--soft:#d9e3ee;
--blue:#0a4f99;--green:#086434;--amber:#854600;--red:#b0151c;--idle:#24384c;color-scheme:light}
[hidden]{display:none!important}
*{box-sizing:border-box}html,body{margin:0;background:var(--bg);color:var(--ink);
font:500 17px/1.4 system-ui,-apple-system,"Segoe UI",Roboto,sans-serif}
header{display:flex;gap:6px;padding:10px 12px;background:var(--card);border-bottom:2px solid var(--line);
position:sticky;top:0;z-index:5;overflow-x:auto}
.tab{flex:1;min-width:84px;padding:14px 8px;border:0;border-radius:10px;background:transparent;color:var(--ink);
font:700 17px system-ui;cursor:pointer}
.tab.on{background:var(--blue);color:#fff}
main{max-width:980px;margin:0 auto;padding:14px 16px 120px}
.banner{border-radius:14px;padding:18px 20px;color:#fff;display:flex;justify-content:space-between;
align-items:center;gap:12px;flex-wrap:wrap}
.banner .big{font-size:30px;font-weight:800;letter-spacing:.3px}
.banner .clock{font:800 44px ui-monospace,Consolas,monospace}
.b-idle{background:var(--idle)}.b-armed{background:var(--amber)}.b-racing{background:var(--green)}
.b-off{background:var(--red)}.b-done{background:var(--blue)}
.sub{font-size:16px;font-weight:600}
.grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(150px,1fr));gap:10px;margin-top:14px}
.lane{background:var(--card);border:2px solid var(--line);border-radius:12px;padding:12px}
.lane.hit{border-width:3px}
.lane .n{font-weight:800;font-size:20px}.lane .p{color:var(--mute);font-size:15px;font-weight:600}
.lane .t{font:700 20px ui-monospace,Consolas,monospace;margin-top:4px}
.lane.hit{border-color:var(--green)}
.card{background:var(--card);border:2px solid var(--line);border-radius:12px;padding:14px;margin-top:14px}
h2{font-size:20px;margin:0 0 8px}
.mute{color:var(--mute)}
table{width:100%;border-collapse:collapse}
th,td{text-align:left;padding:12px 8px;border-bottom:1px solid var(--line);vertical-align:top}
th{font-size:14px;color:var(--mute);font-weight:700}
td.tm{font:700 18px ui-monospace,Consolas,monospace;white-space:nowrap}
tr.tap{cursor:pointer}tr.tap:hover{background:var(--soft)}
.split{font:600 14px ui-monospace,Consolas,monospace;color:var(--mute)}
.tag{display:inline-block;padding:3px 10px;border-radius:99px;font-size:13px;font-weight:800;background:var(--soft);color:var(--ink)}
/* status tags are solid colour with white text so they read at a glance in sun */
.t-INCOMPLETE,.t-DNF{background:var(--amber);color:#fff}.t-DQ{background:var(--red);color:#fff}
.t-PLACED,.t-ACCEPTED{background:var(--blue);color:#fff}.t-TIMED{background:var(--green);color:#fff}
.warn{background:#ffe7a1;color:#2e1d00;border:2px solid #a86d00;border-radius:10px;padding:10px 12px;margin-top:10px;font-weight:700}
.btn{border:2px solid var(--line);border-radius:12px;padding:16px 18px;font:700 18px system-ui;cursor:pointer;
background:var(--soft);color:var(--ink);min-height:56px}
.btn.pri{background:var(--blue);border-color:var(--blue);color:#fff}.btn.red{background:var(--red);border-color:var(--red);color:#fff}
.btn:disabled{opacity:.45;cursor:default}
.btn:focus-visible,.tab:focus-visible{outline:3px solid var(--ink);outline-offset:2px}
.row{display:flex;gap:10px;flex-wrap:wrap;margin-top:10px}
.hold{position:relative;overflow:hidden;width:100%;font-size:22px;padding:22px;background:var(--red);border-color:var(--red);color:#fff;
touch-action:none;user-select:none;-webkit-user-select:none;-webkit-touch-callout:none}
.close{display:inline-block;margin-top:4px;padding:3px 9px;border-radius:99px;font:700 13px system-ui;background:var(--red);color:#fff}
.gap{font:700 15px ui-monospace,Consolas,monospace;color:var(--mute)}
.ev small{display:block;font-weight:600;font-size:14px}
@media (min-width:900px){.btn.ev{min-height:44px;padding:6px 10px;font-size:15px}.btn.ev small{font-size:12px}}
.start{display:flex;gap:10px;margin-top:14px}
.start .btn{flex:1;font-size:26px;padding:26px 12px;min-height:84px}
.btn.amber{background:var(--amber);border-color:var(--amber);color:#fff}.btn.green{background:var(--green);border-color:var(--green);color:#fff}
.btn.sm{min-height:40px;padding:8px 14px;font-size:15px}
.confirm{border:3px solid var(--red)}
td.ed{text-align:right;width:1%}
.sheet{max-height:85vh;overflow:auto}
.crew{font-size:15px;font-weight:600;margin-top:2px;overflow-wrap:break-word}
.lane .crew{display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden}
.close{margin-left:6px}.gap{display:inline}
td .tag{margin-top:4px}
@media (min-width:900px){.narrowonly{display:none}
 td .crew{display:inline;margin-left:8px}
 td.cr{width:42%}
 /* side column: smaller buttons and boxes so everything fits one screen */
 .cols>div:last-child .card .btn:not(.hold):not(.pri[style]){min-height:40px;padding:6px 12px;font-size:15px}
 .cols>div:last-child .card .row{gap:8px;margin-top:8px}
 .cols>div:last-child .warn,.cols>div:last-child .bad-warn{padding:8px 10px;font-size:15px}
 .cols>div:last-child .card{padding:10px 12px}
 .cols>div:last-child p{margin:6px 0}
 td.ed .btn.sm{min-height:30px;padding:3px 12px}
 #results .split,#results .gap{font-size:13px}
 #results td.cr{font-size:15px}
 th,td{padding:4px 8px}
 td.ed .btn.sm{min-height:34px;padding:6px 12px}
 td .tag{margin:0 0 0 8px}td.tm .tag{vertical-align:2px}}
@media (max-width:899px){.wideonly{display:none}}
/* tablet landscape: leg splits move into Edit so all crews fit one screen */
@media (min-width:900px) and (max-width:1199px){#results td.tm .split{display:none}}
@media (min-width:900px){.sysgrid{display:grid;grid-template-columns:repeat(auto-fill,minmax(380px,1fr));gap:12px;align-items:start;align-content:start}
 .sysgrid .card{margin:0}.sysnav{max-width:420px}}
.heatbtns{display:grid;grid-template-columns:repeat(auto-fill,minmax(96px,1fr));gap:8px;margin:6px 0 12px}
select,input[type=text]{font:500 17px system-ui;padding:12px;border-radius:10px;border:2px solid var(--line);
background:var(--card);color:var(--ink);width:100%}
.others{font-size:15px;color:var(--mute);margin-top:8px}
/* layout: one column on phones; two columns on PC/tablet so a tab fits one screen */
.cols{display:grid;gap:12px;margin-top:12px}
.cols>div{display:flex;flex-direction:column;gap:12px;min-width:0}
.cols .card,.cols .grid,.cols .start,.cols .warn,.cols .others{margin-top:0}
.cols .grid{grid-template-columns:repeat(var(--lc,2),minmax(0,1fr))}
.cols p.mute{margin:0}
@media (min-width:900px){
 main{max-width:1500px;padding-top:12px;padding-bottom:24px}
 .cols{grid-template-columns:minmax(0,1fr) minmax(290px,28%);align-items:start}
 .banner{padding:12px 18px}.banner .big{font-size:26px}.banner .clock{font-size:40px}
 .card{padding:12px 14px}h2{font-size:18px;margin-bottom:6px}
 .btn{padding:12px 14px;min-height:48px;font-size:16px}
 .start .btn{min-height:72px;padding:16px 12px}
 .lane{padding:10px 12px}
 th,td{padding:8px 8px}
 .hold{padding:18px}
 .ev small{font-size:13px}
 header .tab{padding:10px 8px}
 /* PC / tablet: the page itself never scrolls; each column fits the screen */
 html,body{height:100%}
 body{display:flex;flex-direction:column;overflow:hidden}
 header{flex:none}
 main{flex:1;min-height:0;width:100%;overflow:hidden;padding-bottom:12px}
 main>section{height:100%;overflow:auto}
 main>section:has(>.cols){overflow:hidden}
 .cols{height:calc(100% - 12px);align-items:stretch}
 .cols>div{overflow:auto;min-height:0;padding-bottom:4px}
 .msgs{max-height:none;height:220px}
 td.tm>div{display:inline;margin-left:10px}
 td.tm .split{display:inline;margin-left:10px}
 td{vertical-align:middle}
 th,td{padding:5px 8px}td.tm{font-size:17px}
 .lane .n{font-size:18px}.lane .t{font-size:18px;margin-top:2px}
 .lane .crew{-webkit-line-clamp:3;font-size:14px}
 .cols>div,.cols{gap:10px}
}
.ctl{display:flex;flex-direction:column;gap:12px}.ctl:empty{display:none}
.start .btn small{display:block;font-size:15px;font-weight:700;margin-top:4px;overflow-wrap:anywhere}
.btn.allin{background:var(--green);border-color:var(--green);color:#fff;animation:pulse 1.2s ease-in-out infinite}
@keyframes pulse{50%{filter:brightness(1.18)}}
@media (prefers-reduced-motion:reduce){.btn.allin{animation:none}}
.bad-warn{background:var(--red);color:#fff;border-radius:10px;padding:10px 12px;font-weight:700}
.tick{color:var(--green);font-weight:800}
.heatbtns .btn.done{background:#c5d3c9;border-color:var(--green)}
.undo{position:fixed;left:50%;transform:translateX(-50%);bottom:calc(20px + env(safe-area-inset-bottom,0px));z-index:21;
background:var(--ink);color:var(--bg);border-radius:12px;padding:8px 8px 8px 16px;display:none;align-items:center;gap:12px;
box-shadow:0 6px 24px rgba(0,0,0,.3);max-width:calc(100vw - 32px)}
.undo.on{display:flex}.undo .btn{background:#fff;color:var(--ink);border-color:#fff;min-height:40px;padding:8px 14px}
.qrow{border-bottom:2px solid var(--line);padding:10px 0;display:flex;gap:10px;align-items:center;justify-content:space-between;flex-wrap:wrap}
.qrow .places{font-size:15px;color:var(--mute);margin-top:2px}
.entnav{display:flex;align-items:center;justify-content:space-between;gap:8px;font-weight:700;margin-bottom:6px}
.enthd{border-left:6px solid var(--blue);padding:4px 0 4px 10px;margin:4px 0}
.entdiv{font:800 21px/1.2 system-ui}.entrnd{font:800 19px system-ui;color:var(--blue)}
.entt{margin-top:4px}
.entt .er{display:grid;grid-template-columns:64px 62px minmax(0,1fr);gap:8px;align-items:center;padding:9px 2px;border-bottom:1px solid var(--soft)}
.entt .ep{font:900 21px system-ui;white-space:nowrap}.entt .el{color:var(--mute);font-weight:700;font-size:15px;white-space:nowrap}
.entt .ec{font:700 18px/1.25 system-ui;overflow-wrap:anywhere;min-width:0}.entt .ec small{display:block;color:var(--mute);font:600 14px ui-monospace,Consolas,monospace}
.entt .er.out .ep{color:var(--red);font-size:15px;white-space:normal;line-height:1.1}.entt .er.out .ec{color:var(--mute)}
.entbtn{flex:1 1 220px;font-size:19px;padding:14px}
.badge{display:inline-block;min-width:20px;padding:0 6px;border-radius:99px;background:var(--amber);color:#fff;font-size:12px;line-height:20px;margin-left:4px}
.tests{display:grid;grid-template-columns:repeat(auto-fill,minmax(132px,1fr));gap:8px;margin:8px 0}
.tests div{white-space:nowrap;border:2px solid var(--line);border-radius:10px;padding:8px 10px;font-weight:700}
.tests div.ok{border-color:var(--green);color:var(--green)}
.tests div.flash{animation:flash .7s ease-out}
.tests div.ok{background:#dcefe3}
@keyframes flash{0%{background:var(--green);color:#fff;transform:scale(1.06)}100%{background:transparent}}
.tests div{display:flex;justify-content:space-between;gap:6px;align-items:baseline}
.tests div small{font-weight:700;color:var(--mute)}
.lastpress{font-size:22px;font-weight:800;margin:6px 0}
.vid{font:600 13px ui-monospace,Consolas,monospace;color:var(--mute)}
textarea{font:500 16px system-ui;padding:10px;border-radius:10px;border:2px solid var(--line);background:var(--card);color:var(--ink);width:100%;min-height:70px}
.practice{background:#5b3fa0;color:#fff;border-radius:10px;padding:10px 12px;font-weight:700}
.log{font-size:14px;color:var(--mute);margin-top:6px}
/* Results screen (#board) for a TV or a tablet in the marshalling area */
body.board header,body.board #nextbar{display:none}
.qbtn{flex:0 0 auto;width:38px;height:38px;align-self:center;border-radius:50%;border:2px solid var(--line);background:#fff;color:var(--blue);font:900 20px system-ui;cursor:pointer}
#nextbar{display:flex;align-items:center;gap:10px;max-width:980px;margin:10px auto 0;padding:10px 14px;background:#e3edf9;border:2px solid var(--blue);border-radius:12px;font-weight:700}
#nextbar[hidden]{display:none}
@media (max-width:1010px){#nextbar{margin:10px 12px 0}}
#nextbar .nx{flex:0 0 auto;background:var(--blue);color:#fff;border-radius:99px;padding:2px 10px;font:800 13px system-ui;letter-spacing:.5px}
#nextbar .nt{flex:1;min-width:0}#nextbar .btn{flex:0 0 auto}
#nextbar.calm{background:#fff;border-color:var(--line);font-weight:600}#nextbar.calm .nx{background:var(--idle)}
.rst{display:inline-flex;gap:4px;flex-wrap:wrap;vertical-align:middle}
.rst i{font:800 normal 12px system-ui;border-radius:99px;padding:2px 9px;border:2px solid var(--line);color:var(--mute);background:#fff;white-space:nowrap}
.rst i.on{background:var(--green);border-color:var(--green);color:#fff}
.sysnav{display:flex;gap:8px;margin-bottom:10px}.sysnav .btn{flex:1;padding:8px 12px}
.syscols>div>.card:first-child{margin-top:0}
@media (min-width:900px){.syscols{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:12px;align-items:start}
  .syscols>div{display:grid;gap:12px;align-content:start}.syscols .card{margin:0}}
.slist{max-width:1100px;margin:0 auto;padding:4px 16px}
.srow{display:grid;grid-template-columns:190px minmax(0,1fr) auto;gap:4px 14px;align-items:center;padding:5px 0;min-height:44px;border-bottom:1px solid var(--soft)}
.slist>.srow:last-child,.sadv>.srow:last-child{border-bottom:0}
.srow .sn{font-weight:800}.srow .ss{min-width:0;overflow-wrap:anywhere}.srow .sb{display:flex;gap:8px;justify-content:flex-end;flex-wrap:wrap}
.srow .sb .btn{padding:5px 12px;min-height:36px;font-size:15px}.srow.hi{background:#e3edf9;margin:0 -16px;padding:8px 16px}
.srow .sin{display:flex;gap:8px;flex-wrap:wrap}.srow .sin input{flex:1 1 150px;padding:5px 10px;min-height:36px}
.snotes{margin:4px 0 0;padding-left:18px;font-size:14px}.okb{color:var(--blue)}
.sadv{border-top:2px solid var(--line);margin-top:2px;padding-left:12px;background:#f7f9fb;margin:0 -16px;padding:0 16px}
.rchip{display:inline-flex;gap:6px;align-items:center;margin:2px 6px 2px 0}
@media (max-width:700px){.srow{grid-template-columns:1fr auto}.srow .ss{grid-column:1/-1;grid-row:2}}
.advh{all:unset;display:flex;justify-content:space-between;align-items:center;width:100%;cursor:pointer}.advh span{color:var(--blue);font-weight:700}
.advs{border-top:1px solid var(--soft);padding:10px 0 4px;margin-top:8px}
.chk1{display:flex;gap:10px;align-items:center;padding:9px 0;border-bottom:1px solid var(--soft)}
.chk1 .mk{flex:0 0 30px;height:30px;border-radius:50%;display:flex;align-items:center;justify-content:center;font:900 16px system-ui;color:#fff;background:var(--amber)}
.chk1.ok .mk{background:var(--green)}.chk1.opt .mk{background:#8e9cab}.chk1.ok.opt .mk{background:var(--green)}
.chk1 .tx{flex:1;min-width:0;font-weight:700}.chk1 .tx small{display:block;font-weight:500;color:var(--mute)}
.ready{background:var(--green);color:#fff;border-radius:12px;padding:12px 14px;font:800 20px system-ui;margin-top:10px;text-align:center}
.notready{background:#fff4d6;border:2px solid var(--amber);border-radius:12px;padding:10px 14px;font-weight:700;margin-top:10px}
.morew{align-self:flex-start}
.helpl{margin:0;padding-left:20px}.helpl li{margin:8px 0}
.home{max-width:560px;margin:0 auto;display:grid;gap:14px;padding-top:4vh}
.home h1{margin:0 0 6px;font-size:30px;text-align:center}
.hbtn{display:block;width:100%;text-align:left;padding:20px;border-radius:14px;border:2px solid var(--line);background:#fff;color:var(--ink);font:inherit;font-size:24px;font-weight:800;text-decoration:none;cursor:pointer}
.hbtn small{display:block;font-size:16px;font-weight:500;color:var(--mute);margin-top:4px}
.hbtn.pri{border-color:var(--blue)}
.bigcode{font:900 72px/1 ui-monospace,Menlo,Consolas,monospace;letter-spacing:12px;text-align:center;margin:10px 0}
.req{border:2px solid var(--amber,#b26b00);border-radius:12px;padding:10px 12px;margin:8px 0;background:#fff8e6}
.req .code{font:900 24px ui-monospace,Menlo,Consolas,monospace;letter-spacing:3px;margin-left:8px}
.ofrow{display:flex;align-items:center;gap:8px;padding:8px 0;border-bottom:1px solid var(--line);flex-wrap:wrap}
.ofrow .nm{flex:1 1 140px;font-weight:700}
.dot{display:inline-block;width:10px;height:10px;border-radius:50%;margin-right:4px;background:#0a7a3a}.dot.off{background:#aab}
.qrs{display:flex;gap:18px;flex-wrap:wrap;justify-content:center}
.qrs>div{text-align:center;font-weight:800}.qrs svg{display:block;margin:6px auto;border:1px solid var(--line)}
.qrs .mute{font-weight:500;font-size:14px;word-break:break-all;max-width:200px}
.bqr{position:fixed;right:10px;bottom:10px;display:flex;gap:10px;background:#fff;border:2px solid var(--line);border-radius:12px;padding:8px;z-index:5}
.bqr>div{text-align:center;font-weight:800;font-size:1.6vh;line-height:1.2}.bqr svg{width:13vh;height:13vh;display:block;margin:0 auto 4px}
.homebtn{position:fixed;left:10px;bottom:10px;z-index:5}
.mwrap{max-width:720px;margin:0 auto}
.mb{--u:min(1vh,.62vw);display:grid;gap:calc(1.4*var(--u))}
.mb .mbtop{display:flex;justify-content:space-between;align-items:center;gap:12px;flex-wrap:wrap;font-weight:800;font-size:clamp(16px,calc(2.4*var(--u)),26px)}
.mb .mbclock{font:900 clamp(22px,calc(4*var(--u)),44px) ui-monospace,Consolas,monospace}
.mb .mbstart{background:var(--idle);color:#fff;border-radius:12px;padding:calc(.6*var(--u)) 1.2vw;font-size:clamp(15px,calc(2.4*var(--u)),26px);font-weight:700}
.mb .mbmain{display:grid;grid-template-columns:3fr 2fr;gap:calc(1.4*var(--u)) 1.4vw;align-items:start}
@media (max-width:900px){.mb .mbmain{grid-template-columns:1fr}}
.mb .mbnow{background:#fff;border:4px solid var(--amber);border-radius:16px;padding:calc(1.4*var(--u)) 1.2vw}
.mb .mbtag{display:inline-block;background:var(--amber);color:#fff;font:900 clamp(18px,calc(3*var(--u)),34px) system-ui;border-radius:10px;padding:calc(.3*var(--u)) 1vw;letter-spacing:1px}
.mb .mbh{font:800 clamp(20px,calc(3.6*var(--u)),42px)/1.15 system-ui;margin:calc(.6*var(--u)) 0}
.mb .mbm{color:var(--mute);font-weight:700;font-size:clamp(14px,calc(2.2*var(--u)),24px)}
.mb .mbl{display:grid;grid-template-columns:auto 1fr auto;align-items:center;gap:calc(.4*var(--u)) 1vw;margin-top:calc(1*var(--u))}
.mb .mbl>b{font:900 clamp(20px,calc(3.8*var(--u)),44px) system-ui;width:1.6em;height:1.6em;border-radius:50%;background:var(--idle);color:#fff;display:flex;align-items:center;justify-content:center;font-size:clamp(16px,calc(2.8*var(--u)),32px)}
.mb .mbl>span{font:700 clamp(17px,calc(3.2*var(--u)),38px)/1.15 system-ui;overflow-wrap:anywhere;padding:calc(.5*var(--u)) 0;border-bottom:1px solid var(--soft)}
.mb .mbl>i{font:800 normal clamp(13px,calc(2.2*var(--u)),24px) system-ui;border-radius:99px;padding:calc(.3*var(--u)) .8vw;white-space:nowrap;text-align:center}
.mb .st-in{background:var(--green);color:#fff}.mb .st-out{background:var(--red);color:#fff}.mb .st-wait{background:#fff4d6;color:var(--amber);border:2px solid var(--amber)}
.mb .scr>span{text-decoration:line-through;color:#6b2226}
.mb .mbside{display:grid;gap:calc(1.4*var(--u))}
.mb .mbcard{background:#fff;border:2px solid var(--line);border-radius:14px;padding:calc(1.2*var(--u)) 1vw}
.mb .mbcard .mbl>span{font-size:clamp(14px,calc(2.2*var(--u)),24px)}.mb .mbcard .mbl>b{font-size:clamp(13px,calc(1.9*var(--u)),22px)}.mb .mbcard .mbl>i{font-size:clamp(11px,calc(1.6*var(--u)),18px)}
.mb .mbs{display:grid;grid-template-columns:1fr 1fr;gap:calc(.3*var(--u)) 1vw;margin-top:calc(.8*var(--u))}
.mb .mbs>div{display:flex;gap:.5vw;align-items:baseline;font:600 clamp(13px,calc(2*var(--u)),22px)/1.2 system-ui;min-width:0}
.mb .mbs b{flex:0 0 1.5em;text-align:right;color:var(--mute)}.mb .mbs span{min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.mb .mbs i{font-style:normal;font-weight:900}.mb .mbs .present i{color:var(--green)}.mb .mbs .scratched span{text-decoration:line-through;color:#6b2226}.mb .mbs .scratched i{color:var(--red)}
.bqr.inl{position:static;justify-content:center;align-self:start}
.mb .mbgrid{display:grid;grid-template-columns:1fr auto;gap:calc(1.4*var(--u)) 1.4vw;align-items:start}
@media (max-width:1000px){.mb .mbgrid{grid-template-columns:1fr}.mb .mbaside{display:none}}
.mb .mbrows{display:grid;gap:calc(1*var(--u))}
.mb .mbrow{display:flex;gap:1vw;align-items:center;background:#fff;border:2px solid var(--line);border-radius:12px;padding:calc(.8*var(--u)) 1vw;font:700 clamp(14px,calc(2.3*var(--u)),26px)/1.2 system-ui}
.mb .mbrow .lab{flex:1;min-width:0}.mb .mbrow .lab small{color:var(--mute);font-weight:600}
.mb .tg{flex:0 0 auto;border-radius:99px;padding:calc(.3*var(--u)) .9vw;font:900 clamp(12px,calc(2*var(--u)),22px) system-ui;letter-spacing:.5px;color:#fff}
.mb .tg.race{background:var(--idle)}.mb .tg.closed{background:#5d6b78}.mb .tg.req{background:var(--amber)}.mb .tg.now{background:var(--red)}.mb .tg.next{background:#fff;color:var(--ink);border:2px solid var(--line)}
.mb .mbbig{background:#fff;border:4px solid var(--amber);border-radius:16px;padding:calc(1.2*var(--u)) 1.2vw}
.mb .mbbig.late{border-color:var(--red)}
.mb .mbbig .hd{display:flex;gap:1vw;align-items:center;flex-wrap:wrap;font:800 clamp(18px,calc(3.2*var(--u)),38px)/1.15 system-ui}
.mb .mbbig .mbl{grid-template-columns:auto 1fr auto auto 1fr auto}
@media (max-width:699px){.mb .mbbig .mbl{grid-template-columns:auto 1fr auto}}
.mb .mbbig .mbl{gap:calc(.2*var(--u)) .8vw;margin-top:calc(.6*var(--u))}
.mb .mbbig .mbl>span{font-size:clamp(15px,calc(2.5*var(--u)),30px);padding:calc(.25*var(--u)) 0;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.mb .mbbig .mbl>b{font-size:clamp(13px,calc(2*var(--u)),24px)}.mb .mbbig .mbl>i{font-size:clamp(11px,calc(1.6*var(--u)),19px);padding:calc(.2*var(--u)) .6vw}
.mb .mbbig .hd{font-size:clamp(17px,calc(2.8*var(--u)),34px)}.mb .mbbig{padding:calc(.8*var(--u)) 1vw}
.mb .st-none{visibility:hidden}
.mb .mbrow{padding:calc(.5*var(--u)) 1vw}
@media (max-width:699px){.mb .mbbig .mbl>span{white-space:normal}}
.mb .mbaside{display:grid;gap:calc(1.4*var(--u));width:clamp(200px,20vw,340px)}
.mb .mbnote{background:var(--blue);color:#fff;border-radius:14px;padding:calc(1.2*var(--u)) 1vw;font:800 clamp(15px,calc(2.4*var(--u)),28px)/1.25 system-ui}
.mb .mbaside .bqr.inl{flex-direction:column;align-items:center}
.mb .mbbreak{background:#fff4d6;border:3px solid var(--amber);border-radius:14px;padding:calc(1.2*var(--u)) 1vw;font:800 clamp(18px,calc(3*var(--u)),34px) system-ui}
.mpick{display:flex;gap:8px;overflow-x:auto;padding:2px 2px 10px;-webkit-overflow-scrolling:touch}
.mpick button{flex:0 0 auto;min-width:96px;border:2px solid var(--line);background:#fff;border-radius:12px;padding:6px 10px;font:800 17px system-ui;color:var(--ink);text-align:left;line-height:1.15}
.mpick button small{display:block;font-weight:600;font-size:12px;color:var(--mute)}
.mpick button b{display:block;font-size:14px;color:var(--blue)}
.mpick button.on{border-color:var(--blue);background:var(--blue);color:#fff}.mpick button.on small,.mpick button.on b{color:#fff}
.mpick button.done b{color:var(--green)}.mpick button.on.done b{color:#c8f5d8}
.mcard{padding:12px}
.mhead{display:flex;justify-content:space-between;gap:10px;align-items:flex-start}
.mdiv{font:800 20px/1.2 system-ui}.mmeta{color:var(--mute);font-weight:600;font-size:15px}
.mcount{flex:0 0 auto;font:800 15px system-ui;background:var(--amber);color:#fff;border-radius:99px;padding:5px 11px}.mcount.all{background:var(--green)}
.mbar{display:flex;height:8px;border-radius:9px;background:var(--soft);overflow:hidden;margin-top:10px}.mbar i{background:var(--green)}.mbar i.x{background:var(--red)}
.mlane{display:flex;align-items:stretch;gap:6px;margin-top:6px}
.mtap{flex:1;display:flex;align-items:center;gap:10px;min-height:52px;padding:6px 8px;border:2px solid var(--line);border-radius:12px;background:#fff;color:var(--ink);text-align:left;font:inherit;cursor:pointer}
.mno{flex:0 0 38px;height:38px;border-radius:50%;background:var(--idle);color:#fff;font:900 19px system-ui;display:flex;align-items:center;justify-content:center}
.mtick{display:none}.mlane.present .mtick{display:block;flex:0 0 24px;margin-left:auto;font:900 24px system-ui;color:var(--green);text-align:center}
.mnm{font:700 17px/1.2 system-ui;min-width:0;overflow-wrap:anywhere}.mnm small{display:block;font:600 13px system-ui;color:var(--mute);margin-top:2px}
.mscr{flex:0 0 auto;align-self:center;width:50px;height:48px;border:1.5px solid var(--line);border-radius:10px;background:#fff;color:var(--mute);font:800 17px/1 system-ui;cursor:pointer;padding:4px 0}
.mscr small{display:block;font:600 10px system-ui;margin-top:3px}
.rolefix{margin-top:6px;padding:8px 10px;border:2px solid var(--red);border-radius:10px;background:#fde8e8;font-size:14px}
.rolefix>b{color:var(--red)}.rfrow{display:flex;gap:6px;align-items:center;flex-wrap:wrap;margin-top:6px}.rfrow span{flex:1 1 120px;font-weight:700}
.mlane.present .mtap{border-color:var(--green);background:#e3f6ea}.mlane.present .mno{background:var(--green)}
.mlane.present .mnm small{color:var(--green)}
.mlane.scratched .mtap{border-color:var(--red);background:#fde8e8}.mlane.scratched .mno{background:var(--red)}
.mpat{display:block;font:600 14px/1.25 system-ui;color:var(--blue);margin-top:1px}
.mlane.scratched .mpat{text-decoration:line-through;color:#6b2226}
.mb .mbp{font-style:normal;font-weight:600;color:var(--blue)}
.mb.tight .mbbig .mbl>span{font-size:clamp(13px,calc(2.05*var(--u)),26px);padding:calc(.1*var(--u)) 0}.mb.tight .mbbig .mbl>b{font-size:clamp(12px,calc(1.7*var(--u)),22px)}
.mb.tight .mbbig .hd{font-size:clamp(15px,calc(2.3*var(--u)),30px)}.mb.tight .mbbig{padding:calc(.5*var(--u)) 1vw}.mb.tight .mbrows{gap:calc(.6*var(--u))}
.mb.tight .mbbig .mbm{font-size:clamp(12px,calc(1.8*var(--u)),22px)}.mb.tight .mbrow{padding:calc(.3*var(--u)) 1vw}
.tmppl{color:var(--ink)!important;margin-top:3px}.tmppl b{color:var(--mute);font-weight:700}
.mlane.scratched .nmx{text-decoration:line-through;color:#6b2226}.mlane.scratched .mnm small{color:var(--red);font-weight:800}
.mpick button .mpd{max-width:150px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.mcount.sent{background:var(--blue)}
.msend{width:100%;margin-top:12px;font-size:20px;padding:16px}
.msent{display:flex;flex-wrap:wrap;gap:8px;align-items:center;justify-content:space-between;margin-top:12px;padding:10px 12px;border-radius:12px;background:#e3edf9;border:2px solid var(--blue)}
.msent span{flex:1 1 100%;color:var(--red);font-weight:700;order:3}
.mlane.scratched .mscr{background:#fff;border-color:var(--red);color:var(--red)}
@media (max-width:700px){.bqr{display:none}}
#printcard{display:none}
a.btn{text-decoration:none;display:inline-block}
@media print{html,body{background:#fff!important}body>*{display:none!important}#printcard{display:block!important;padding:10mm}
  #printcard .pc{border:2px dashed #888;padding:8mm;text-align:center;font-family:sans-serif}#printcard h1{margin:0 0 4mm}
  #printcard .qrs svg{width:70mm;height:70mm}}
body.board main{max-width:none}
.bd{display:grid;gap:12px}
.bd .top{display:flex;gap:10px;align-items:center;justify-content:space-between;flex-wrap:wrap}
.bd .now{font-size:clamp(20px,min(2.4vw,4vh),34px);font-weight:800;min-width:0;text-wrap:balance;flex:1 1 300px}
.bd .pill{border-radius:99px;padding:6px 14px;font-weight:800;color:#fff;white-space:nowrap;font-size:clamp(16px,1.8vw,24px)}
.bd .pill.racing{background:var(--green)}.bd .pill.armed{background:var(--amber)}.bd .pill.done{background:var(--blue)}
.bd .pill #clock{font-family:ui-monospace,Consolas,monospace}
.bd .lanes{display:grid;grid-template-columns:repeat(auto-fill,minmax(220px,1fr));gap:10px}
.bd .ln{background:var(--card);border:2px solid var(--line);border-radius:12px;padding:.5em .7em;font-size:clamp(15px,min(1.6vw,2.8vh),22px);
display:grid;grid-template-columns:auto 1fr;column-gap:10px;align-items:baseline}
.bd .ln b{font-size:1.25em}
.bd .ln .t{grid-column:2;font:800 1.2em ui-monospace,Consolas,monospace;margin-top:2px}
.bd .ln.empty{opacity:.6}
.bd .sec{font-size:clamp(15px,1.4vw,19px);font-weight:800;text-transform:uppercase;letter-spacing:.06em;color:var(--mute);margin-top:4px}
.bd .res{display:grid;gap:5px}
.bd .rr{display:grid;grid-template-columns:2.6em 2.4em minmax(0,1fr) auto;gap:10px;align-items:baseline;background:var(--card);
border:2px solid var(--line);border-radius:10px;padding:.25em .7em;line-height:1.25;font-size:clamp(16px,min(1.8vw,2.9vh),28px)}
.bd .rr .pl{font-weight:900;font-size:1.1em}.bd .rr .lnno{color:var(--mute);font-weight:800}
.bd .rr .tm{font:800 1em ui-monospace,Consolas,monospace;white-space:nowrap}
.bd .rr.first{border-color:var(--green);border-width:3px}
.bd .pill.final{background:var(--green)}.bd .pill.prov{background:var(--amber)}
@media (min-width:900px){.bd .two{display:grid;grid-template-columns:minmax(0,1.4fr) minmax(0,1fr);gap:14px;align-items:start}}
.bd .next .card div{padding:2px 0}
@media (max-width:599px){
 body.board main{padding-top:8px}
 .bd{gap:10px}.bd .now{font-size:20px}
 .bd .lanes{grid-template-columns:1fr;gap:4px}
 .bd .ln{padding:6px 10px;font-size:16px;border-width:1px;border-radius:8px;grid-template-columns:28px 1fr auto}
 .bd .ln b{font-size:17px}
 .bd .ln .t{grid-column:3;font-size:15px;margin:0}
 .bd .next{grid-template-columns:1fr}.bd .next .card{padding:10px 12px;font-size:15px}
 .bd .rr{grid-template-columns:2.2em 2em minmax(0,1fr) auto;padding:6px 10px;font-size:16px;gap:6px;border-width:1px}
 .bd .rr.first{border-width:2px}
}
.bd .next{display:grid;grid-template-columns:repeat(auto-fit,minmax(280px,1fr));gap:12px}
.bd .next .card{margin:0;font-size:clamp(15px,1.4vw,19px)}
.bd .card{font-size:clamp(15px,min(1.4vw,2.5vh),20px)}
.tests div.clash{border-color:var(--red);color:var(--red)}
.tests div.sus{border-color:var(--amber);color:var(--amber);background:#fdebc8}
.tests div.clash{background:#f8d5d6}
/* program (running order) */
.prow{display:grid;grid-template-columns:2.2em minmax(0,1fr) auto;gap:10px;align-items:center;padding:8px 6px;border-bottom:2px solid var(--line);cursor:pointer}
.prow:hover{background:var(--soft)}
.prow .pn{font-weight:800;color:var(--mute)}
.prow .pl{font-weight:700;overflow-wrap:anywhere}.prow .ps{font-size:14px;color:var(--mute)}
.prow.done{opacity:.6}.prow.now{background:#dcefe3;border-left:6px solid var(--green)}
.chip{display:inline-block;padding:2px 9px;border-radius:99px;font-size:13px;font-weight:800;color:#fff;white-space:nowrap}
.chip.now{background:var(--green)}.chip.next{background:var(--blue)}.chip.done{background:var(--mute)}.chip.gone{background:var(--red)}
.choice{display:grid;gap:10px}.choice .btn{text-align:left;width:100%}
.choice .btn small{display:block;font-weight:600;font-size:14px;margin-top:2px}
.heatbtns .btn.picked{background:var(--blue);border-color:var(--blue);color:#fff}
.lane.scr{border-style:dashed;background:#f2f2f2}.lane .scrt{color:var(--red);font-weight:800;font-size:14px}
.lane .chk{color:var(--green);font-weight:800;font-size:13px}
.mrow{display:grid;grid-template-columns:3.6em minmax(0,1fr) auto;gap:8px;align-items:center;padding:6px 0;border-bottom:1px solid var(--line)}
.mrow .btn{min-height:42px;padding:6px 10px;font-size:15px}
.btn.ok-on{background:var(--green);border-color:var(--green);color:#fff}.btn.scr-on{background:var(--red);border-color:var(--red);color:#fff}
.prow.brk{background:#fff4d6}.prow .tm2{font:700 15px ui-monospace,Consolas,monospace;color:var(--ink)}
.tmv{display:grid;gap:12px;max-width:900px;margin:0 auto}
.tmv .hit{border-left:6px solid var(--blue)}
.lvl{display:grid;grid-template-columns:6.5em minmax(0,1fr) auto;gap:8px;align-items:center;margin-top:8px}
.viewonly{background:var(--soft);border-radius:12px;padding:14px;display:flex;gap:12px;align-items:center;justify-content:space-between;flex-wrap:wrap}
.ctl>.card,.ctl>.start{margin-top:0}
/* phone/narrow: one column, with SET/GO/FINISH straight under the status banner */
@media (max-width:899px){
 .cols>div{display:contents}
 .cols>div>*{order:2;min-width:0}
 .cols .top{order:0}.cols .ctl{order:1}
}
@media (max-width:599px){
 header{padding:6px 8px;gap:4px}
 .tab{min-width:0;padding:10px 1px;font-size:13.5px;white-space:nowrap}
 .qbtn{width:30px;height:30px;font-size:16px;border-width:1.5px}
 header.six{flex-wrap:wrap;overflow:visible}header.six .tab{flex:1 1 28%;padding:8px 2px;font-size:14px}
 #nextbar{padding:8px 10px;gap:8px;font-size:15px}
 .tab .badge{min-width:15px;line-height:15px;font-size:10px;padding:0 3px;margin-left:2px;vertical-align:1px}
 main{padding-top:10px}
 .banner{padding:12px 14px}.banner .big{font-size:22px}.banner .clock{font-size:32px}.sub{font-size:14px}
 .cols .grid{grid-template-columns:repeat(2,minmax(0,1fr));gap:8px}
 .lane{padding:8px 10px}.lane .n{font-size:16px}.lane .p{font-size:13px}.lane .t{font-size:17px;margin-top:2px}
 .crew{font-size:13px}
 .card{padding:12px}h2{font-size:17px}
 .btn{padding:12px 12px;min-height:48px;font-size:16px}
 .start .btn{font-size:22px;min-height:64px;padding:14px 10px}
 .hold{font-size:19px;padding:16px}
 .ev small{font-size:12px}
 th,td{padding:10px 6px}td.tm{font-size:16px}
 /* results as stacked rows: place | crew + time underneath | Edit - nothing wider than the screen */
 #results table,#results tbody,#history table,#history tbody{display:block}
 #results tr:has(th),#history tr:has(th){display:none}
 #results tr,#history tr{display:grid;grid-template-columns:28px minmax(0,1fr) auto;column-gap:8px;row-gap:2px;
  padding:10px 0;border-bottom:1px solid var(--line);align-items:start}
 #results td,#history td{border:0;padding:0;min-width:0}
 #results td:nth-child(1),#history td:nth-child(1){grid-row:1/3;font-size:20px;padding-top:1px}
 #results td:nth-child(2),#history td:nth-child(2){grid-column:2;font-size:14px;color:var(--mute)}
 #results td .crew,#history td .crew{display:inline;margin-left:6px;color:var(--ink);font-size:15px}
 #results td.tm,#history td.tm{grid-column:2;white-space:normal;font-size:18px}
 #results td.tm>div,#history td.tm>div{display:inline;margin-left:8px}
 #results td.tm .split,#history td.tm .split{display:block;margin-left:0}
 .split{overflow-wrap:anywhere;font-size:13px}
 #results td.ed{grid-column:3;grid-row:1/3;align-self:center;width:auto}
}

/* ================= fit every screen: phone, tablet, laptop, TV ================= */
.ofrow .ofs{font-size:14px;white-space:nowrap}
.mlanes{display:block}
/* phones: bigger targets for wet fingers, nothing under 13px */
@media (max-width:599px){
 header.six .tab{padding:11px 2px}.tab{padding:12px 1px}
 .qbtn{width:38px;height:38px;font-size:18px}
 .mpick button small{font-size:13px}.rst i{font-size:13px;padding:2px 8px}
 .ofrow{flex-wrap:nowrap}.ofrow .nm{flex:1 1 0;min-width:0;overflow-wrap:anywhere}.ofrow .ofc{display:none}
 .mb .mbl>i,.mb .mbbig .mbl>i{font-size:13px}
}
/* tablets held upright: use the width – two columns where a phone has one */
@media (min-width:600px) and (max-width:899px){
 main{padding-bottom:40px}
 th,td{padding:7px 8px}td{vertical-align:middle}
 td .crew{display:inline;margin-left:8px}td.tm>div,td.tm .split{display:inline;margin-left:10px}
 .entt{columns:2;column-gap:22px}.entt .er{break-inside:avoid}
 .syscols{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:12px;align-items:start}
 .syscols>div{display:grid;gap:12px;align-content:start;min-width:0}.syscols .card{margin:0}
 .cols .grid{grid-template-columns:repeat(5,minmax(0,1fr));gap:8px}
 .lane{padding:8px 10px}.lane .n{font-size:17px}.lane .t{font-size:17px}
 .mlanes{display:grid;grid-template-columns:1fr 1fr;grid-template-rows:repeat(var(--mr,5),auto);grid-auto-flow:column;gap:0 10px}
 .mwrap{max-width:none}
 .ofrow{flex-wrap:nowrap}.ofrow .nm{flex:1 1 0;min-width:0;overflow-wrap:anywhere}.ofrow .ofc{display:none}
}
/* laptops, tablets on their side, TVs */
@media (min-width:900px){
 .mwrap{max-width:1180px}
 .mlanes{display:grid;grid-template-columns:1fr 1fr;grid-template-rows:repeat(var(--mr,5),auto);grid-auto-flow:column;gap:0 12px}
 .mlane{margin-top:5px}.mtap{min-height:46px;padding:4px 8px}.mscr{height:44px}
 .msend{margin-top:8px;padding:10px;min-height:48px}.mcard{padding:10px 12px}.mpick{padding-bottom:6px}
 .entt{columns:2;column-gap:28px}.entt .er{break-inside:avoid;padding:6px 2px}
 .ofrow{flex-wrap:nowrap;padding:5px 0}.ofrow .nm{flex:1 1 0;min-width:0;overflow-wrap:anywhere}
 .ofrow .btn.sm{min-height:34px;padding:4px 10px;font-size:14px}
 .chk1{padding:6px 0}.chk1 .mk{flex-basis:26px;height:26px;font-size:14px}.chk1 .tx small{font-size:14px}
 .qrs{gap:12px}.syscols .card p{margin:6px 0}
}
@media (min-width:900px) and (max-width:1399px){.ofrow .ofc{display:none}}
/* short screens (a laptop at 125-150% scaling): squeeze the chrome so the work fits */
@media (min-width:900px) and (max-height:820px){
 th,td{padding:3px 8px}td.ed .btn.sm{min-height:30px;padding:3px 12px}
 .cols>div,.cols{gap:8px}
}
@media (min-width:900px) and (max-height:700px){
 header{padding:5px 12px}header .tab{padding:7px 8px;font-size:16px}.qbtn{width:32px;height:32px;font-size:17px}
 #nextbar{margin-top:6px;padding:4px 12px;font-size:16px}#nextbar .btn{min-height:34px;padding:4px 12px}
 main{padding-top:8px;padding-bottom:6px}.cols{margin-top:8px;height:calc(100% - 8px)}
 .banner{padding:7px 14px}.banner .big{font-size:22px}.banner .clock{font-size:32px}.sub{font-size:15px}
 .card{padding:8px 12px}h2{font-size:17px;margin-bottom:4px}
 .lane{padding:6px 10px}.lane .n{font-size:17px}.lane .t{font-size:17px;margin-top:0}.lane .crew{-webkit-line-clamp:2}
 .start .btn{min-height:58px;padding:10px 12px;font-size:22px}
 .warn{padding:6px 10px;margin-top:6px}.vid{font-size:12.5px}
 .prow{padding:5px 6px}
 .mtap{min-height:40px}.mno{flex-basis:32px;height:32px;font-size:17px}.mscr{height:38px}.mlane{margin-top:4px}
 .mpick button{padding:3px 10px}.mhelp{display:none}.mbar{margin-top:6px}
 .sysnav{margin-bottom:8px}.sysnav .btn{min-height:38px;padding:4px 12px}
 .entt .er{padding:4px 2px}.entnav{margin-bottom:2px}.entbtn{padding:8px;min-height:44px}
}
@media (max-width:1000px){.mb .mbgrid{grid-template-columns:1fr}.mb .mbaside{display:none}}
/* big screens (desk monitor, TV used as the timing screen): everything 25% larger instead of a thin strip */
@media (min-width:1700px) and (min-height:900px){
 body:not(.board){zoom:1.25}
 body.board .tmv,body.board .home{zoom:1.3}
}
.hold i{position:absolute;left:0;top:0;bottom:0;width:0;background:rgba(255,255,255,.3)}
/* hire-kit additions: brand strip, Get started, battery bar, help fixes, events editor, in-app browser banner, guides */
.brand{display:flex;align-items:center;gap:10px;font-size:20px;line-height:1.15}.brand img{height:44px;width:auto;max-width:140px;object-fit:contain}
.brand small{display:block;font-size:15px;font-weight:600;color:var(--mute)}
.htitle{text-align:center}.htitle img{max-height:90px;max-width:70%;object-fit:contain}.htitle h1{margin:6px 0 2px}
.mb .mbb{display:flex;align-items:center;gap:8px}.mb .mbb img{height:1.4em;width:auto}
.wizwrap{max-width:860px;margin:0 auto}.wiz{margin-top:0}.wizhd{display:flex;justify-content:space-between;align-items:center;gap:10px;flex-wrap:wrap;margin-bottom:6px}
.wst{border-bottom:1px solid var(--soft)}.wst:last-of-type{border-bottom:0}
.wsh{all:unset;box-sizing:border-box;display:flex;gap:12px;align-items:center;width:100%;padding:10px 0;cursor:pointer}
.wsh .mk{flex:0 0 34px;height:34px;border-radius:50%;display:flex;align-items:center;justify-content:center;font:900 17px system-ui;color:#fff;background:var(--blue)}
.wst.wdone .mk{background:var(--green)}.wsh .tx{flex:1;min-width:0;font-weight:800;font-size:19px}.wsh .tx small{display:block;font-weight:500;font-size:15px;color:var(--mute)}
.wsh .chev{font-size:22px;color:var(--blue);font-weight:800}.wst.on{background:#f3f7fb;margin:0 -14px;padding:0 14px}
.wsb{padding:0 0 12px 46px}.wsb p{margin:4px 0 8px}.wform{display:flex;gap:8px;flex-wrap:wrap}.wform input{flex:1 1 200px}
.wsb .qrs svg{width:110px;height:110px}
@media (max-width:599px){.wsb{padding-left:0}}
@media (max-height:820px){.wsh{padding:6px 0}.wsh .mk{flex-basis:30px;height:30px}.wsh .tx{font-size:17px}.wsh .tx small{font-size:14px}}
.bbar{height:16px;border:2px solid var(--line);border-radius:8px;overflow:hidden;background:#fff;max-width:320px}.bbar i{display:block;height:100%}
.bbar.good i{background:var(--green)}.bbar.amb i{background:var(--amber)}.bbar.bad i{background:var(--red)}
details.fix{border-bottom:1px solid var(--soft);padding:8px 0}details.fix summary{font-weight:700}details.fix p{margin:6px 0 2px}
.evrow{display:flex;gap:8px;align-items:center;flex-wrap:wrap;padding:6px 0}.evrow input{flex:1 1 180px}.evrow select{padding:8px;font-size:17px}
#iab{position:sticky;top:0;z-index:30;background:#fff4d6;border-bottom:3px solid var(--amber);padding:10px 14px;display:grid;gap:4px}
#iab b{font-size:19px}
@media print{#printcard .guide{page-break-after:always;font-family:sans-serif;color:#000}#printcard .guide:last-child{page-break-after:auto}
  #printcard .gtop{display:flex;align-items:center;gap:4mm;font-size:13pt;font-weight:700;border-bottom:1px solid #888;padding-bottom:3mm}
  #printcard .gtop img{height:12mm}#printcard .guide h1{font-size:30pt;margin:6mm 0 0}#printcard .gsub{font-size:15pt;margin:1mm 0 5mm}
  #printcard .guide ol{font-size:15pt;line-height:1.45;padding-left:8mm}#printcard .guide li{margin-bottom:3mm}
  #printcard .gfoot{margin-top:8mm;font-size:11pt;color:#333}#printcard .gkit{width:100%;border-collapse:collapse;font-size:13pt}
  #printcard .gkit td,#printcard .gkit th{border:1px solid #888;padding:2mm 3mm;text-align:left}#printcard .gkit td+td,#printcard .gkit th+th{width:18mm;text-align:center}}
.hold span{position:relative}
.sheet{position:fixed;left:0;right:0;bottom:0;background:var(--card);border-top:3px solid var(--ink);
box-shadow:0 -8px 30px rgba(0,0,0,.2);padding:16px 16px 24px;z-index:9;display:none}
.sheet.on{display:block}.sheet .in{max-width:980px;margin:0 auto}
.places{display:flex;gap:8px;flex-wrap:wrap;margin-top:6px}.places .btn{min-width:56px}
.ok{color:var(--green);font-weight:700}.bad{color:var(--red);font-weight:700}
.msgs{font:14px ui-monospace,Consolas,monospace;max-height:320px;overflow:auto;white-space:pre-wrap}
.toast{position:fixed;left:50%;transform:translateX(-50%);bottom:20px;background:var(--ink);color:#fff;font-weight:700;
padding:12px 18px;border-radius:10px;display:none;z-index:20}
details{border-bottom:2px solid var(--line);padding:10px 0}summary{cursor:pointer;font-weight:700}
</style></head><body>
<header>
 <button class="tab on" data-t="race">Race</button>
 <button class="tab" data-t="results">Confirm</button>
 <button class="tab" data-t="program">Program<span id="pbadge"></span></button>
 <button class="tab" data-t="marshal" hidden>Marshal</button>
 <button class="tab" data-t="history">LiveHeats<span id="qbadge"></span></button>
 <button class="tab" data-t="system">System<span id="sbadge"></span></button>
 <button class="qbtn" id="helpbtn" onclick="openHelp()" aria-label="Help for this screen">?</button>
</header>
<div id="nextbar" hidden></div>
<main>
 <section id="race"></section>
 <section id="results" hidden></section>
 <section id="program" hidden></section>
 <section id="marshal" hidden></section>
 <section id="history" hidden></section>
 <section id="system" hidden></section>
</main>
<div class="sheet" id="sheet"><div class="in" id="sheetin"></div></div>
<div class="toast" id="toast"></div>
<div class="undo" id="undo"><span id="undotxt"></span><button class="btn" id="undobtn">Undo</button></div>
<script>/* QR codes made on this computer, no internet needed. qrcode-generator 1.4.4 */
// Copyright (c) 2009 Kazuhiko Arase
// Licensed under the MIT license:
var qrcode=function(){var t=function(t,r){var e=t,n=g[r],o=null,i=0,a=null,u=[],f={},c=function(t,r){o=function(t){for(var r=new Array(t),e=0;e<t;e+=1){r[e]=new Array(t);for(var n=0;n<t;n+=1)r[e][n]=null}return r}(i=4*e+17),l(0,0),l(i-7,0),l(0,i-7),s(),h(),d(t,r),e>=7&&v(t),null==a&&(a=p(e,n,u)),w(a,r)},l=function(t,r){for(var e=-1;e<=7;e+=1)if(!(t+e<=-1||i<=t+e))for(var n=-1;n<=7;n+=1)r+n<=-1||i<=r+n||(o[t+e][r+n]=0<=e&&e<=6&&(0==n||6==n)||0<=n&&n<=6&&(0==e||6==e)||2<=e&&e<=4&&2<=n&&n<=4)},h=function(){for(var t=8;t<i-8;t+=1)null==o[t][6]&&(o[t][6]=t%2==0);for(var r=8;r<i-8;r+=1)null==o[6][r]&&(o[6][r]=r%2==0)},s=function(){for(var t=B.getPatternPosition(e),r=0;r<t.length;r+=1)for(var n=0;n<t.length;n+=1){var i=t[r],a=t[n];if(null==o[i][a])for(var u=-2;u<=2;u+=1)for(var f=-2;f<=2;f+=1)o[i+u][a+f]=-2==u||2==u||-2==f||2==f||0==u&&0==f}},v=function(t){for(var r=B.getBCHTypeNumber(e),n=0;n<18;n+=1){var a=!t&&1==(r>>n&1);o[Math.floor(n/3)][n%3+i-8-3]=a}for(n=0;n<18;n+=1){a=!t&&1==(r>>n&1);o[n%3+i-8-3][Math.floor(n/3)]=a}},d=function(t,r){for(var e=n<<3|r,a=B.getBCHTypeInfo(e),u=0;u<15;u+=1){var f=!t&&1==(a>>u&1);u<6?o[u][8]=f:u<8?o[u+1][8]=f:o[i-15+u][8]=f}for(u=0;u<15;u+=1){f=!t&&1==(a>>u&1);u<8?o[8][i-u-1]=f:u<9?o[8][15-u-1+1]=f:o[8][15-u-1]=f}o[i-8][8]=!t},w=function(t,r){for(var e=-1,n=i-1,a=7,u=0,f=B.getMaskFunction(r),c=i-1;c>0;c-=2)for(6==c&&(c-=1);;){for(var g=0;g<2;g+=1)if(null==o[n][c-g]){var l=!1;u<t.length&&(l=1==(t[u]>>>a&1)),f(n,c-g)&&(l=!l),o[n][c-g]=l,-1==(a-=1)&&(u+=1,a=7)}if((n+=e)<0||i<=n){n-=e,e=-e;break}}},p=function(t,r,e){for(var n=A.getRSBlocks(t,r),o=b(),i=0;i<e.length;i+=1){var a=e[i];o.put(a.getMode(),4),o.put(a.getLength(),B.getLengthInBits(a.getMode(),t)),a.write(o)}var u=0;for(i=0;i<n.length;i+=1)u+=n[i].dataCount;if(o.getLengthInBits()>8*u)throw"code length overflow. ("+o.getLengthInBits()+">"+8*u+")";for(o.getLengthInBits()+4<=8*u&&o.put(0,4);o.getLengthInBits()%8!=0;)o.putBit(!1);for(;!(o.getLengthInBits()>=8*u||(o.put(236,8),o.getLengthInBits()>=8*u));)o.put(17,8);return function(t,r){for(var e=0,n=0,o=0,i=new Array(r.length),a=new Array(r.length),u=0;u<r.length;u+=1){var f=r[u].dataCount,c=r[u].totalCount-f;n=Math.max(n,f),o=Math.max(o,c),i[u]=new Array(f);for(var g=0;g<i[u].length;g+=1)i[u][g]=255&t.getBuffer()[g+e];e+=f;var l=B.getErrorCorrectPolynomial(c),h=k(i[u],l.getLength()-1).mod(l);for(a[u]=new Array(l.getLength()-1),g=0;g<a[u].length;g+=1){var s=g+h.getLength()-a[u].length;a[u][g]=s>=0?h.getAt(s):0}}var v=0;for(g=0;g<r.length;g+=1)v+=r[g].totalCount;var d=new Array(v),w=0;for(g=0;g<n;g+=1)for(u=0;u<r.length;u+=1)g<i[u].length&&(d[w]=i[u][g],w+=1);for(g=0;g<o;g+=1)for(u=0;u<r.length;u+=1)g<a[u].length&&(d[w]=a[u][g],w+=1);return d}(o,n)};f.addData=function(t,r){var e=null;switch(r=r||"Byte"){case"Numeric":e=M(t);break;case"Alphanumeric":e=x(t);break;case"Byte":e=m(t);break;case"Kanji":e=L(t);break;default:throw"mode:"+r}u.push(e),a=null},f.isDark=function(t,r){if(t<0||i<=t||r<0||i<=r)throw t+","+r;return o[t][r]},f.getModuleCount=function(){return i},f.make=function(){if(e<1){for(var t=1;t<40;t++){for(var r=A.getRSBlocks(t,n),o=b(),i=0;i<u.length;i++){var a=u[i];o.put(a.getMode(),4),o.put(a.getLength(),B.getLengthInBits(a.getMode(),t)),a.write(o)}var g=0;for(i=0;i<r.length;i++)g+=r[i].dataCount;if(o.getLengthInBits()<=8*g)break}e=t}c(!1,function(){for(var t=0,r=0,e=0;e<8;e+=1){c(!0,e);var n=B.getLostPoint(f);(0==e||t>n)&&(t=n,r=e)}return r}())},f.createTableTag=function(t,r){t=t||2;var e="";e+='<table style="',e+=" border-width: 0px; border-style: none;",e+=" border-collapse: collapse;",e+=" padding: 0px; margin: "+(r=void 0===r?4*t:r)+"px;",e+='">',e+="<tbody>";for(var n=0;n<f.getModuleCount();n+=1){e+="<tr>";for(var o=0;o<f.getModuleCount();o+=1)e+='<td style="',e+=" border-width: 0px; border-style: none;",e+=" border-collapse: collapse;",e+=" padding: 0px; margin: 0px;",e+=" width: "+t+"px;",e+=" height: "+t+"px;",e+=" background-color: ",e+=f.isDark(n,o)?"#000000":"#ffffff",e+=";",e+='"/>';e+="</tr>"}return e+="</tbody>",e+="</table>"},f.createSvgTag=function(t,r,e,n){var o={};"object"==typeof arguments[0]&&(t=(o=arguments[0]).cellSize,r=o.margin,e=o.alt,n=o.title),t=t||2,r=void 0===r?4*t:r,(e="string"==typeof e?{text:e}:e||{}).text=e.text||null,e.id=e.text?e.id||"qrcode-description":null,(n="string"==typeof n?{text:n}:n||{}).text=n.text||null,n.id=n.text?n.id||"qrcode-title":null;var i,a,u,c,g=f.getModuleCount()*t+2*r,l="";for(c="l"+t+",0 0,"+t+" -"+t+",0 0,-"+t+"z ",l+='<svg version="1.1" xmlns="http://www.w3.org/2000/svg"',l+=o.scalable?"":' width="'+g+'px" height="'+g+'px"',l+=' viewBox="0 0 '+g+" "+g+'" ',l+=' preserveAspectRatio="xMinYMin meet"',l+=n.text||e.text?' role="img" aria-labelledby="'+y([n.id,e.id].join(" ").trim())+'"':"",l+=">",l+=n.text?'<title id="'+y(n.id)+'">'+y(n.text)+"</title>":"",l+=e.text?'<description id="'+y(e.id)+'">'+y(e.text)+"</description>":"",l+='<rect width="100%" height="100%" fill="white" cx="0" cy="0"/>',l+='<path d="',a=0;a<f.getModuleCount();a+=1)for(u=a*t+r,i=0;i<f.getModuleCount();i+=1)f.isDark(a,i)&&(l+="M"+(i*t+r)+","+u+c);return l+='" stroke="transparent" fill="black"/>',l+="</svg>"},f.createDataURL=function(t,r){t=t||2,r=void 0===r?4*t:r;var e=f.getModuleCount()*t+2*r,n=r,o=e-r;return I(e,e,(function(r,e){if(n<=r&&r<o&&n<=e&&e<o){var i=Math.floor((r-n)/t),a=Math.floor((e-n)/t);return f.isDark(a,i)?0:1}return 1}))},f.createImgTag=function(t,r,e){t=t||2,r=void 0===r?4*t:r;var n=f.getModuleCount()*t+2*r,o="";return o+="<img",o+=' src="',o+=f.createDataURL(t,r),o+='"',o+=' width="',o+=n,o+='"',o+=' height="',o+=n,o+='"',e&&(o+=' alt="',o+=y(e),o+='"'),o+="/>"};var y=function(t){for(var r="",e=0;e<t.length;e+=1){var n=t.charAt(e);switch(n){case"<":r+="&lt;";break;case">":r+="&gt;";break;case"&":r+="&amp;";break;case'"':r+="&quot;";break;default:r+=n}}return r};return f.createASCII=function(t,r){if((t=t||1)<2)return function(t){t=void 0===t?2:t;var r,e,n,o,i,a=1*f.getModuleCount()+2*t,u=t,c=a-t,g={"██":"█","█ ":"▀"," █":"▄","  ":" "},l={"██":"▀","█ ":"▀"," █":" ","  ":" "},h="";for(r=0;r<a;r+=2){for(n=Math.floor((r-u)/1),o=Math.floor((r+1-u)/1),e=0;e<a;e+=1)i="█",u<=e&&e<c&&u<=r&&r<c&&f.isDark(n,Math.floor((e-u)/1))&&(i=" "),u<=e&&e<c&&u<=r+1&&r+1<c&&f.isDark(o,Math.floor((e-u)/1))?i+=" ":i+="█",h+=t<1&&r+1>=c?l[i]:g[i];h+="\n"}return a%2&&t>0?h.substring(0,h.length-a-1)+Array(a+1).join("▀"):h.substring(0,h.length-1)}(r);t-=1,r=void 0===r?2*t:r;var e,n,o,i,a=f.getModuleCount()*t+2*r,u=r,c=a-r,g=Array(t+1).join("██"),l=Array(t+1).join("  "),h="",s="";for(e=0;e<a;e+=1){for(o=Math.floor((e-u)/t),s="",n=0;n<a;n+=1)i=1,u<=n&&n<c&&u<=e&&e<c&&f.isDark(o,Math.floor((n-u)/t))&&(i=0),s+=i?g:l;for(o=0;o<t;o+=1)h+=s+"\n"}return h.substring(0,h.length-1)},f.renderTo2dContext=function(t,r){r=r||2;for(var e=f.getModuleCount(),n=0;n<e;n++)for(var o=0;o<e;o++)t.fillStyle=f.isDark(n,o)?"black":"white",t.fillRect(n*r,o*r,r,r)},f};t.stringToBytes=(t.stringToBytesFuncs={default:function(t){for(var r=[],e=0;e<t.length;e+=1){var n=t.charCodeAt(e);r.push(255&n)}return r}}).default,t.createStringToBytes=function(t,r){var e=function(){for(var e=S(t),n=function(){var t=e.read();if(-1==t)throw"eof";return t},o=0,i={};;){var a=e.read();if(-1==a)break;var u=n(),f=n()<<8|n();i[String.fromCharCode(a<<8|u)]=f,o+=1}if(o!=r)throw o+" != "+r;return i}(),n="?".charCodeAt(0);return function(t){for(var r=[],o=0;o<t.length;o+=1){var i=t.charCodeAt(o);if(i<128)r.push(i);else{var a=e[t.charAt(o)];"number"==typeof a?(255&a)==a?r.push(a):(r.push(a>>>8),r.push(255&a)):r.push(n)}}return r}};var r,e,n,o,i,a=1,u=2,f=4,c=8,g={L:1,M:0,Q:3,H:2},l=0,h=1,s=2,v=3,d=4,w=5,p=6,y=7,B=(r=[[],[6,18],[6,22],[6,26],[6,30],[6,34],[6,22,38],[6,24,42],[6,26,46],[6,28,50],[6,30,54],[6,32,58],[6,34,62],[6,26,46,66],[6,26,48,70],[6,26,50,74],[6,30,54,78],[6,30,56,82],[6,30,58,86],[6,34,62,90],[6,28,50,72,94],[6,26,50,74,98],[6,30,54,78,102],[6,28,54,80,106],[6,32,58,84,110],[6,30,58,86,114],[6,34,62,90,118],[6,26,50,74,98,122],[6,30,54,78,102,126],[6,26,52,78,104,130],[6,30,56,82,108,134],[6,34,60,86,112,138],[6,30,58,86,114,142],[6,34,62,90,118,146],[6,30,54,78,102,126,150],[6,24,50,76,102,128,154],[6,28,54,80,106,132,158],[6,32,58,84,110,136,162],[6,26,54,82,110,138,166],[6,30,58,86,114,142,170]],e=1335,n=7973,i=function(t){for(var r=0;0!=t;)r+=1,t>>>=1;return r},(o={}).getBCHTypeInfo=function(t){for(var r=t<<10;i(r)-i(e)>=0;)r^=e<<i(r)-i(e);return 21522^(t<<10|r)},o.getBCHTypeNumber=function(t){for(var r=t<<12;i(r)-i(n)>=0;)r^=n<<i(r)-i(n);return t<<12|r},o.getPatternPosition=function(t){return r[t-1]},o.getMaskFunction=function(t){switch(t){case l:return function(t,r){return(t+r)%2==0};case h:return function(t,r){return t%2==0};case s:return function(t,r){return r%3==0};case v:return function(t,r){return(t+r)%3==0};case d:return function(t,r){return(Math.floor(t/2)+Math.floor(r/3))%2==0};case w:return function(t,r){return t*r%2+t*r%3==0};case p:return function(t,r){return(t*r%2+t*r%3)%2==0};case y:return function(t,r){return(t*r%3+(t+r)%2)%2==0};default:throw"bad maskPattern:"+t}},o.getErrorCorrectPolynomial=function(t){for(var r=k([1],0),e=0;e<t;e+=1)r=r.multiply(k([1,C.gexp(e)],0));return r},o.getLengthInBits=function(t,r){if(1<=r&&r<10)switch(t){case a:return 10;case u:return 9;case f:case c:return 8;default:throw"mode:"+t}else if(r<27)switch(t){case a:return 12;case u:return 11;case f:return 16;case c:return 10;default:throw"mode:"+t}else{if(!(r<41))throw"type:"+r;switch(t){case a:return 14;case u:return 13;case f:return 16;case c:return 12;default:throw"mode:"+t}}},o.getLostPoint=function(t){for(var r=t.getModuleCount(),e=0,n=0;n<r;n+=1)for(var o=0;o<r;o+=1){for(var i=0,a=t.isDark(n,o),u=-1;u<=1;u+=1)if(!(n+u<0||r<=n+u))for(var f=-1;f<=1;f+=1)o+f<0||r<=o+f||0==u&&0==f||a==t.isDark(n+u,o+f)&&(i+=1);i>5&&(e+=3+i-5)}for(n=0;n<r-1;n+=1)for(o=0;o<r-1;o+=1){var c=0;t.isDark(n,o)&&(c+=1),t.isDark(n+1,o)&&(c+=1),t.isDark(n,o+1)&&(c+=1),t.isDark(n+1,o+1)&&(c+=1),0!=c&&4!=c||(e+=3)}for(n=0;n<r;n+=1)for(o=0;o<r-6;o+=1)t.isDark(n,o)&&!t.isDark(n,o+1)&&t.isDark(n,o+2)&&t.isDark(n,o+3)&&t.isDark(n,o+4)&&!t.isDark(n,o+5)&&t.isDark(n,o+6)&&(e+=40);for(o=0;o<r;o+=1)for(n=0;n<r-6;n+=1)t.isDark(n,o)&&!t.isDark(n+1,o)&&t.isDark(n+2,o)&&t.isDark(n+3,o)&&t.isDark(n+4,o)&&!t.isDark(n+5,o)&&t.isDark(n+6,o)&&(e+=40);var g=0;for(o=0;o<r;o+=1)for(n=0;n<r;n+=1)t.isDark(n,o)&&(g+=1);return e+=Math.abs(100*g/r/r-50)/5*10},o),C=function(){for(var t=new Array(256),r=new Array(256),e=0;e<8;e+=1)t[e]=1<<e;for(e=8;e<256;e+=1)t[e]=t[e-4]^t[e-5]^t[e-6]^t[e-8];for(e=0;e<255;e+=1)r[t[e]]=e;var n={glog:function(t){if(t<1)throw"glog("+t+")";return r[t]},gexp:function(r){for(;r<0;)r+=255;for(;r>=256;)r-=255;return t[r]}};return n}();function k(t,r){if(void 0===t.length)throw t.length+"/"+r;var e=function(){for(var e=0;e<t.length&&0==t[e];)e+=1;for(var n=new Array(t.length-e+r),o=0;o<t.length-e;o+=1)n[o]=t[o+e];return n}(),n={getAt:function(t){return e[t]},getLength:function(){return e.length},multiply:function(t){for(var r=new Array(n.getLength()+t.getLength()-1),e=0;e<n.getLength();e+=1)for(var o=0;o<t.getLength();o+=1)r[e+o]^=C.gexp(C.glog(n.getAt(e))+C.glog(t.getAt(o)));return k(r,0)},mod:function(t){if(n.getLength()-t.getLength()<0)return n;for(var r=C.glog(n.getAt(0))-C.glog(t.getAt(0)),e=new Array(n.getLength()),o=0;o<n.getLength();o+=1)e[o]=n.getAt(o);for(o=0;o<t.getLength();o+=1)e[o]^=C.gexp(C.glog(t.getAt(o))+r);return k(e,0).mod(t)}};return n}var A=function(){var t=[[1,26,19],[1,26,16],[1,26,13],[1,26,9],[1,44,34],[1,44,28],[1,44,22],[1,44,16],[1,70,55],[1,70,44],[2,35,17],[2,35,13],[1,100,80],[2,50,32],[2,50,24],[4,25,9],[1,134,108],[2,67,43],[2,33,15,2,34,16],[2,33,11,2,34,12],[2,86,68],[4,43,27],[4,43,19],[4,43,15],[2,98,78],[4,49,31],[2,32,14,4,33,15],[4,39,13,1,40,14],[2,121,97],[2,60,38,2,61,39],[4,40,18,2,41,19],[4,40,14,2,41,15],[2,146,116],[3,58,36,2,59,37],[4,36,16,4,37,17],[4,36,12,4,37,13],[2,86,68,2,87,69],[4,69,43,1,70,44],[6,43,19,2,44,20],[6,43,15,2,44,16],[4,101,81],[1,80,50,4,81,51],[4,50,22,4,51,23],[3,36,12,8,37,13],[2,116,92,2,117,93],[6,58,36,2,59,37],[4,46,20,6,47,21],[7,42,14,4,43,15],[4,133,107],[8,59,37,1,60,38],[8,44,20,4,45,21],[12,33,11,4,34,12],[3,145,115,1,146,116],[4,64,40,5,65,41],[11,36,16,5,37,17],[11,36,12,5,37,13],[5,109,87,1,110,88],[5,65,41,5,66,42],[5,54,24,7,55,25],[11,36,12,7,37,13],[5,122,98,1,123,99],[7,73,45,3,74,46],[15,43,19,2,44,20],[3,45,15,13,46,16],[1,135,107,5,136,108],[10,74,46,1,75,47],[1,50,22,15,51,23],[2,42,14,17,43,15],[5,150,120,1,151,121],[9,69,43,4,70,44],[17,50,22,1,51,23],[2,42,14,19,43,15],[3,141,113,4,142,114],[3,70,44,11,71,45],[17,47,21,4,48,22],[9,39,13,16,40,14],[3,135,107,5,136,108],[3,67,41,13,68,42],[15,54,24,5,55,25],[15,43,15,10,44,16],[4,144,116,4,145,117],[17,68,42],[17,50,22,6,51,23],[19,46,16,6,47,17],[2,139,111,7,140,112],[17,74,46],[7,54,24,16,55,25],[34,37,13],[4,151,121,5,152,122],[4,75,47,14,76,48],[11,54,24,14,55,25],[16,45,15,14,46,16],[6,147,117,4,148,118],[6,73,45,14,74,46],[11,54,24,16,55,25],[30,46,16,2,47,17],[8,132,106,4,133,107],[8,75,47,13,76,48],[7,54,24,22,55,25],[22,45,15,13,46,16],[10,142,114,2,143,115],[19,74,46,4,75,47],[28,50,22,6,51,23],[33,46,16,4,47,17],[8,152,122,4,153,123],[22,73,45,3,74,46],[8,53,23,26,54,24],[12,45,15,28,46,16],[3,147,117,10,148,118],[3,73,45,23,74,46],[4,54,24,31,55,25],[11,45,15,31,46,16],[7,146,116,7,147,117],[21,73,45,7,74,46],[1,53,23,37,54,24],[19,45,15,26,46,16],[5,145,115,10,146,116],[19,75,47,10,76,48],[15,54,24,25,55,25],[23,45,15,25,46,16],[13,145,115,3,146,116],[2,74,46,29,75,47],[42,54,24,1,55,25],[23,45,15,28,46,16],[17,145,115],[10,74,46,23,75,47],[10,54,24,35,55,25],[19,45,15,35,46,16],[17,145,115,1,146,116],[14,74,46,21,75,47],[29,54,24,19,55,25],[11,45,15,46,46,16],[13,145,115,6,146,116],[14,74,46,23,75,47],[44,54,24,7,55,25],[59,46,16,1,47,17],[12,151,121,7,152,122],[12,75,47,26,76,48],[39,54,24,14,55,25],[22,45,15,41,46,16],[6,151,121,14,152,122],[6,75,47,34,76,48],[46,54,24,10,55,25],[2,45,15,64,46,16],[17,152,122,4,153,123],[29,74,46,14,75,47],[49,54,24,10,55,25],[24,45,15,46,46,16],[4,152,122,18,153,123],[13,74,46,32,75,47],[48,54,24,14,55,25],[42,45,15,32,46,16],[20,147,117,4,148,118],[40,75,47,7,76,48],[43,54,24,22,55,25],[10,45,15,67,46,16],[19,148,118,6,149,119],[18,75,47,31,76,48],[34,54,24,34,55,25],[20,45,15,61,46,16]],r=function(t,r){var e={};return e.totalCount=t,e.dataCount=r,e},e={};return e.getRSBlocks=function(e,n){var o=function(r,e){switch(e){case g.L:return t[4*(r-1)+0];case g.M:return t[4*(r-1)+1];case g.Q:return t[4*(r-1)+2];case g.H:return t[4*(r-1)+3];default:return}}(e,n);if(void 0===o)throw"bad rs block @ typeNumber:"+e+"/errorCorrectionLevel:"+n;for(var i=o.length/3,a=[],u=0;u<i;u+=1)for(var f=o[3*u+0],c=o[3*u+1],l=o[3*u+2],h=0;h<f;h+=1)a.push(r(c,l));return a},e}(),b=function(){var t=[],r=0,e={getBuffer:function(){return t},getAt:function(r){var e=Math.floor(r/8);return 1==(t[e]>>>7-r%8&1)},put:function(t,r){for(var n=0;n<r;n+=1)e.putBit(1==(t>>>r-n-1&1))},getLengthInBits:function(){return r},putBit:function(e){var n=Math.floor(r/8);t.length<=n&&t.push(0),e&&(t[n]|=128>>>r%8),r+=1}};return e},M=function(t){var r=a,e=t,n={getMode:function(){return r},getLength:function(t){return e.length},write:function(t){for(var r=e,n=0;n+2<r.length;)t.put(o(r.substring(n,n+3)),10),n+=3;n<r.length&&(r.length-n==1?t.put(o(r.substring(n,n+1)),4):r.length-n==2&&t.put(o(r.substring(n,n+2)),7))}},o=function(t){for(var r=0,e=0;e<t.length;e+=1)r=10*r+i(t.charAt(e));return r},i=function(t){if("0"<=t&&t<="9")return t.charCodeAt(0)-"0".charCodeAt(0);throw"illegal char :"+t};return n},x=function(t){var r=u,e=t,n={getMode:function(){return r},getLength:function(t){return e.length},write:function(t){for(var r=e,n=0;n+1<r.length;)t.put(45*o(r.charAt(n))+o(r.charAt(n+1)),11),n+=2;n<r.length&&t.put(o(r.charAt(n)),6)}},o=function(t){if("0"<=t&&t<="9")return t.charCodeAt(0)-"0".charCodeAt(0);if("A"<=t&&t<="Z")return t.charCodeAt(0)-"A".charCodeAt(0)+10;switch(t){case" ":return 36;case"$":return 37;case"%":return 38;case"*":return 39;case"+":return 40;case"-":return 41;case".":return 42;case"/":return 43;case":":return 44;default:throw"illegal char :"+t}};return n},m=function(r){var e=f,n=t.stringToBytes(r),o={getMode:function(){return e},getLength:function(t){return n.length},write:function(t){for(var r=0;r<n.length;r+=1)t.put(n[r],8)}};return o},L=function(r){var e=c,n=t.stringToBytesFuncs.SJIS;if(!n)throw"sjis not supported.";!function(t,r){var e=n("友");if(2!=e.length||38726!=(e[0]<<8|e[1]))throw"sjis not supported."}();var o=n(r),i={getMode:function(){return e},getLength:function(t){return~~(o.length/2)},write:function(t){for(var r=o,e=0;e+1<r.length;){var n=(255&r[e])<<8|255&r[e+1];if(33088<=n&&n<=40956)n-=33088;else{if(!(57408<=n&&n<=60351))throw"illegal char at "+(e+1)+"/"+n;n-=49472}n=192*(n>>>8&255)+(255&n),t.put(n,13),e+=2}if(e<r.length)throw"illegal char at "+(e+1)}};return i},D=function(){var t=[],r={writeByte:function(r){t.push(255&r)},writeShort:function(t){r.writeByte(t),r.writeByte(t>>>8)},writeBytes:function(t,e,n){e=e||0,n=n||t.length;for(var o=0;o<n;o+=1)r.writeByte(t[o+e])},writeString:function(t){for(var e=0;e<t.length;e+=1)r.writeByte(t.charCodeAt(e))},toByteArray:function(){return t},toString:function(){var r="";r+="[";for(var e=0;e<t.length;e+=1)e>0&&(r+=","),r+=t[e];return r+="]"}};return r},S=function(t){var r=t,e=0,n=0,o=0,i={read:function(){for(;o<8;){if(e>=r.length){if(0==o)return-1;throw"unexpected end of file./"+o}var t=r.charAt(e);if(e+=1,"="==t)return o=0,-1;t.match(/^\s$/)||(n=n<<6|a(t.charCodeAt(0)),o+=6)}var i=n>>>o-8&255;return o-=8,i}},a=function(t){if(65<=t&&t<=90)return t-65;if(97<=t&&t<=122)return t-97+26;if(48<=t&&t<=57)return t-48+52;if(43==t)return 62;if(47==t)return 63;throw"c:"+t};return i},I=function(t,r,e){for(var n=function(t,r){var e=t,n=r,o=new Array(t*r),i={setPixel:function(t,r,n){o[r*e+t]=n},write:function(t){t.writeString("GIF87a"),t.writeShort(e),t.writeShort(n),t.writeByte(128),t.writeByte(0),t.writeByte(0),t.writeByte(0),t.writeByte(0),t.writeByte(0),t.writeByte(255),t.writeByte(255),t.writeByte(255),t.writeString(","),t.writeShort(0),t.writeShort(0),t.writeShort(e),t.writeShort(n),t.writeByte(0);var r=a(2);t.writeByte(2);for(var o=0;r.length-o>255;)t.writeByte(255),t.writeBytes(r,o,255),o+=255;t.writeByte(r.length-o),t.writeBytes(r,o,r.length-o),t.writeByte(0),t.writeString(";")}},a=function(t){for(var r=1<<t,e=1+(1<<t),n=t+1,i=u(),a=0;a<r;a+=1)i.add(String.fromCharCode(a));i.add(String.fromCharCode(r)),i.add(String.fromCharCode(e));var f,c,g,l=D(),h=(f=l,c=0,g=0,{write:function(t,r){if(t>>>r!=0)throw"length over";for(;c+r>=8;)f.writeByte(255&(t<<c|g)),r-=8-c,t>>>=8-c,g=0,c=0;g|=t<<c,c+=r},flush:function(){c>0&&f.writeByte(g)}});h.write(r,n);var s=0,v=String.fromCharCode(o[s]);for(s+=1;s<o.length;){var d=String.fromCharCode(o[s]);s+=1,i.contains(v+d)?v+=d:(h.write(i.indexOf(v),n),i.size()<4095&&(i.size()==1<<n&&(n+=1),i.add(v+d)),v=d)}return h.write(i.indexOf(v),n),h.write(e,n),h.flush(),l.toByteArray()},u=function(){var t={},r=0,e={add:function(n){if(e.contains(n))throw"dup key:"+n;t[n]=r,r+=1},size:function(){return r},indexOf:function(r){return t[r]},contains:function(r){return void 0!==t[r]}};return e};return i}(t,r),o=0;o<r;o+=1)for(var i=0;i<t;i+=1)n.setPixel(i,o,e(i,o));var a=D();n.write(a);for(var u=function(){var t=0,r=0,e=0,n="",o={},i=function(t){n+=String.fromCharCode(a(63&t))},a=function(t){if(t<0);else{if(t<26)return 65+t;if(t<52)return t-26+97;if(t<62)return t-52+48;if(62==t)return 43;if(63==t)return 47}throw"n:"+t};return o.writeByte=function(n){for(t=t<<8|255&n,r+=8,e+=1;r>=6;)i(t>>>r-6),r-=6},o.flush=function(){if(r>0&&(i(t<<6-r),t=0,r=0),e%3!=0)for(var o=3-e%3,a=0;a<o;a+=1)n+="="},o.toString=function(){return n},o}(),f=a.toByteArray(),c=0;c<f.length;c+=1)u.writeByte(f[c]);return u.flush(),"data:image/gif;base64,"+u};return t}();qrcode.stringToBytesFuncs["UTF-8"]=function(t){return function(t){for(var r=[],e=0;e<t.length;e++){var n=t.charCodeAt(e);n<128?r.push(n):n<2048?r.push(192|n>>6,128|63&n):n<55296||n>=57344?r.push(224|n>>12,128|n>>6&63,128|63&n):(e++,n=65536+((1023&n)<<10|1023&t.charCodeAt(e)),r.push(240|n>>18,128|n>>12&63,128|n>>6&63,128|63&n))}return r}(t)},function(t){"function"==typeof define&&define.amd?define([],t):"object"==typeof exports&&(module.exports=t())}((function(){return qrcode}));
qrcode.stringToBytes=qrcode.stringToBytesFuncs["UTF-8"];
</script>
<script>
let finishAsk=0, startBusy=false, drawData=null;
let wakeMsg="Keeping the screen on…", wake=null;
async function keepAwake(){
  if(!("wakeLock" in navigator)){ wakeMsg="This browser can't keep the screen on here – set the tablet's screen timeout to Never (or the longest) in its settings."; return; }
  try{ wake=await navigator.wakeLock.request("screen"); wakeMsg="The screen stays on while this page is open.";
    wake.addEventListener("release",()=>{ wake=null; }); }
  catch(e){ wakeMsg="The screen may turn off – set the tablet's screen timeout to Never (or the longest) in its settings."; }
}
document.addEventListener("visibilitychange",()=>{ if(document.visibilityState==="visible"&&!wake) keepAwake(); });
document.addEventListener("pointerdown",()=>{ if(!wake) keepAwake(); },{once:true});
keepAwake();
let st=null, linkDown=false, tab="race", sel=null, hist=[], histAt=0;
// phones that opened the link inside Messenger/Facebook/Instagram etc. often lose the connection: offer the real browser
function inAppBrowser(){ const ua=navigator.userAgent||""; return /FBAN|FBAV|FB_IAB|FBIOS|Instagram|Messenger|Line\/|Snapchat|TikTok|musical_ly|; wv\)/.test(ua); }
function copyLink(){ const i=document.createElement("input"); i.value=location.href; document.body.appendChild(i); i.select(); let ok=false;
  try{ ok=document.execCommand("copy"); }catch(e){} i.remove(); toast(ok?"Link copied – paste it into Chrome or Safari":"Copy this address: "+location.href); }
function iabBanner(){ if(!inAppBrowser()||document.getElementById("iab")) return; const and=/Android/i.test(navigator.userAgent), d=document.createElement("div"); d.id="iab";
  d.innerHTML=`<b>Open this in your phone's browser</b><span>You're inside another app (like Messenger), which can drop the connection to the timing desk.</span>
    <div class="row" style="margin-top:6px">${and?`<a class="btn pri" href="intent://${location.host}${location.pathname}${location.hash}#Intent;scheme=http;package=com.android.chrome;end">Open in Chrome</a>`:""}
    <button class="btn" onclick="copyLink()">Copy link</button><button class="btn" onclick="this.closest('#iab').remove()">Close</button></div>
    ${and?"":`<span class="mute">iPhone: tap the share button or ••• and choose Open in Safari.</span>`}<span class="mute" style="font-size:14px">${esc(location.host)}</span>`;
  document.body.prepend(d); }
document.addEventListener("DOMContentLoaded",iabBanner); setTimeout(iabBanner,50);
const TOO_CLOSE_US=10000;
const $=id=>document.getElementById(id);
const esc=s=>String(s).replace(/[&<>"]/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;"}[c]));
function ft(us){ if(us==null) return "—"; const ms=Math.floor(us/1000), m=Math.floor(ms/60000),
  s=Math.floor(ms/1000)%60, r=ms%1000; return (m?m+":"+String(s).padStart(2,"0"):s)+"."+String(r).padStart(3,"0"); }
function clock(sec){ const m=Math.floor(sec/60), s=Math.floor(sec%60), t=Math.floor(sec*10)%10;
  return m+":"+String(s).padStart(2,"0")+"."+t; }
function toast(t){ const e=$("toast"); e.textContent=t; e.style.display="block"; clearTimeout(e._t);
  e._t=setTimeout(()=>e.style.display="none",2500); }
function myName(){ try{ return localStorage.getItem("irb_name")||""; }catch(e){ return ""; } }
function setMyName(v){ try{ localStorage.setItem("irb_name",v.trim()); }catch(e){} }
async function post(url,data){ try{ const r=await fetch(url,{method:"POST",headers:{"Content-Type":"application/json"},
  body:JSON.stringify(Object.assign({who:myName()||(st&&st.local?"Timing computer":"?")},data))}); const j=await r.json(); if(j.result!=="ok") toast(j.result); }catch(e){ toast("No link to the timing computer"); } }
function cmd(c,expect){ return post("/api/cmd",{cmd:c,expect:expect}); }
let evOpen=false;
function setEvent(id){ evOpen=false; if(st){ st.event=id; lastKey=""; render(); } post("/api/event",{id:id}); }
document.querySelectorAll(".tab").forEach(b=>b.onclick=()=>{ tab=b.dataset.t;
  document.querySelectorAll(".tab").forEach(x=>x.classList.toggle("on",x===b));
  ["race","results","program","marshal","history","system"].forEach(s=>$(s).hidden=(s!==tab)); closeSheet(); lastKey=""; render(); });
const TABS={master:["race","results","program","marshal","history","system"],admin:["race","results","program","history","system"],
  starter:["race","system"],marshal:["marshal","system"],viewer:["race"]};
let tabRole="";
let justLogged=false;
function applyTabs(){
  // each access level sees only its own tabs; Master and Admin reach the Marshal screen from System
  const role=st&&st.role||"viewer", ok=TABS[role]||TABS.viewer;
  if(role===tabRole) return; tabRole=role;
  document.querySelectorAll(".tab").forEach(b=>b.hidden=!ok.includes(b.dataset.t));
  document.querySelector("header").classList.toggle("six",ok.length>5);
  if(justLogged){ justLogged=false; goTab(ok[0]); return; }
  if(!ok.includes(tab)&&!(tab==="marshal"&&(role==="master"||role==="admin"))) goTab(ok[0]);
}

function heatLabel(h){ return h?`${h.div} · ${h.round} · Heat ${h.no}`:""; }
function shownHeat(){
  if(st.state==="DONE"&&st.results) return st.results.heat||null;
  if(st.state==="RACING") return st.race_heat||st.heat;
  return st.heat;
}
function crewOf(h,l){ return h&&h.crews?h.crews[String(l)]||"":""; }
function checkOf(h,l){ return h&&st&&st.checkin&&st.checkin[h.heat_id]?st.checkin[h.heat_id][String(l)]||"":""; }
function eventName(e){ return e&&e.legs?" · "+e.name:""; }
function chosenEvent(){ return st.events.find(e=>e.id===st.event); }
function banner(){
  if(linkDown||!st) return `<div class="banner b-off"><div><div class="big">No link to the timing computer</div>
    <div class="sub">Check this device is on the timing Wi-Fi. The timing box keeps timing and saving while the link is down.</div></div></div>`;
  if(!st.connected) return `<div class="banner b-off"><div><div class="big">Timing box not connected</div>
    <div class="sub">Plug the timing box's USB cable into this computer. Close Thonny if it is open.</div></div></div>`;
  if(st.at_prompt) return `<div class="banner b-off"><div><div class="big">Timing program stopped</div>
    <div class="sub">Go to System and press Restart timing program.</div></div></div>`;
  const s=st.state, r=st.race;
  if(s==="RACING") return `<div class="banner b-racing"><div><div class="big">RACING</div>
    <div class="sub">Race ${r+1}${st.race_heat?" · "+esc(heatLabel(st.race_heat)):eventName(st.race_event)}</div></div><div class="clock" id="clock">${clock(st.elapsed||0)}</div></div>`;
  if(s==="ARMED") return `<div class="banner b-armed"><div><div class="big">SET – waiting for GO</div>
    <div class="sub">Race ${r+1}${st.heat?" · "+esc(heatLabel(st.heat)):eventName(chosenEvent())}</div></div></div>`;
  if(s==="DONE") return `<div class="banner b-done"><div><div class="big">Race ${r} finished</div>
    <div class="sub">${st.confirmed?"Results confirmed. Press SET for the next race.":"Check the result on the Confirm tab, then press Confirm results."}</div></div></div>`;
  return `<div class="banner b-idle"><div><div class="big">Ready – press SET</div>
    <div class="sub">${r?("Last race: "+r):"No races yet"}</div></div></div>`;
}
let wizOpen=null, joinDone=false;
function wizSteps(){
  const pg=st.program||{}, lt=st.last_test, b=st.brand||{}, j=st.join||{}, fw=(st.firewall||{}).state;
  return [
    {k:"box",title:"Timing box",ok:st.connected&&!st.faults.length,
     status:!st.connected?"Not connected":st.faults.length?"Check wiring: "+st.faults.join(", "):"Connected · wiring OK",
     body:()=>!st.connected?`<p>Plug the timing box's USB cable into this computer. If Thonny is open, close it. The app finds the box by itself.</p>`
       :st.faults.length?`<p>These look unplugged or held down: <b>${esc(st.faults.join(", "))}</b>. Check those cables.</p>`:`<p class="ok">All good – nothing to do.</p>`},
    {k:"club",opt:true,title:"Club and event",ok:!!b.club,status:b.club?b.club+(b.event?" · "+b.event:""):"Shown on the screens and join card",
     body:()=>`<div class="wform"><input type="text" id="bclub" value="${esc(b.club||"")}" placeholder="Club name, e.g. Kurrawa SLSC" maxlength="40">
       <input type="text" id="bevent" value="${esc(b.event||"")}" placeholder="Event, e.g. Club IRB Carnival" maxlength="40"></div>
       <div class="row" style="align-items:center"><button class="btn pri" onclick="saveBrand()">Save</button>
       <label class="btn">${b.logo?"Change logo":"Add logo (optional)"}<input type="file" accept="image/*" style="display:none" onchange="logoPick(this)"></label>
       ${b.logo?`<img src="/logo?v=${b.logo}" alt="" style="height:44px"><button class="btn sm" onclick="brandDo({logo:''},'Logo removed')">Remove logo</button>`:""}</div>`},
    {k:"heats",title:"How heats are run",ok:pg.mode!=null,status:pg.mode==="on"?"Program on":pg.mode==="off"?"No program – heats chosen by hand":"Not chosen yet",
     body:()=>`<div class="choice"><button class="btn" onclick="${st.draw?"goTab('program')":"openLoad()"}">Use LiveHeats<small>${st.draw?"Draw loaded – choose its schedule on the Program tab":"Load the event's draw from LiveHeats (needs internet)"}</small></button>
       <button class="btn" onclick="goTab('program')">Build our own program<small>Type in the events, rounds and heats</small></button>
       <button class="btn" onclick="progDo({mode:'off'},'No program – choose heats one at a time')">No program<small>Pick each heat by hand before SET</small></button></div>`},
    {k:"phones",opt:true,title:"Phones",ok:!!j.ssid&&fw!==false,status:(j.ssid?"Wi-Fi: "+j.ssid:"Wi-Fi not added")+(fw===false?" · Windows is blocking phones":""),
     body:()=>`<p class="mute" style="margin-top:0">The Wi-Fi officials join – it goes on the join card as a QR code.</p>
       <div class="wform"><input type="text" id="wssid" value="${esc(((st.access||{}).net||{}).ssid||"")}" placeholder="Wi-Fi name"><input type="text" id="wpass" value="${esc(((st.access||{}).net||{}).pass||"")}" placeholder="Wi-Fi password"></div>
       <div class="row"><button class="btn pri" onclick="offDo({net:{ssid:$('wssid').value,pass:$('wpass').value,addr:a_addr()}},'Saved')">Save Wi-Fi</button></div>${fwBlock()}`},
    {k:"test",title:"Button test",ok:!!(lt&&lt.date===st.today&&!lt.missing.length&&!(lt.clash||[]).length),
     status:st.test?"Running now":lt&&lt.date===st.today?((lt.missing.length||(lt.clash||[]).length)?testProblems()+" – fix and test again":"All buttons worked"):"Not done today",
     body:()=>st.test?`<p>Press every button – each lane, SET, GO, and hold FINISH for 1 second. Then end the test.</p><div class="row"><button class="btn pri" onclick="sysView='today';goTab('system')">Show the test</button></div>`
       :`<p>Someone at the water presses every button while you watch the screen. It's the only way to find a broken FINISH cable.</p>
       <div class="row"><button class="btn pri" ${st.connected&&(st.state==="IDLE"||st.state==="DONE")?"":"disabled"} onclick="cmd('test on').then(()=>{sysView='today';goTab('system')})">Start button test</button></div>`},
    {k:"card",opt:true,title:"Join card",ok:joinDone,status:joinDone?"Done":"Print it, or save the picture to share",
     body:()=>`${joinCodes(110)}<div class="row"><button class="btn pri" onclick="joinDone=true;printCard();lastKey='';render()">Print</button><button class="btn" onclick="joinDone=true;downloadCard();lastKey='';render()">Download</button></div>`}];
}
function fwBlock(){ const f=st.firewall||{};
  if(f.state!==false) return f.state===true?`<p class="ok" style="margin:6px 0 0">Windows lets phones connect.</p>`:"";
  return `<div class="warn" style="margin-top:8px"><b>Windows is blocking phones.</b> ${f.busy?"Answer <b>Yes</b> on the Windows prompt on this computer…":"Press Allow phones, then answer Yes on the Windows prompt."}
    ${f.busy?"":`<div class="row" style="margin-top:6px"><button class="btn pri" onclick="post('/api/firewall',{}).then(()=>toast('Answer Yes on the Windows prompt'))">Allow phones</button></div>`}</div>`; }
function wizard(){
  const S_=wizSteps(), need=S_.filter(x=>!x.opt), done=S_.filter(x=>x.ok).length;
  let open=wizOpen; if(!open||!S_.find(x=>x.k===open)) open=(S_.find(x=>!x.ok)||{}).k;
  let h=`<div class="card wiz"><div class="wizhd"><div><h2 style="margin:0">Get started</h2><div class="mute">${done} of ${S_.length} done · steps marked optional can wait</div></div>${brandBar()}</div>`;
  S_.forEach((x,i)=>{ const on=x.k===open;
    h+=`<div class="wst ${x.ok?"wdone":""} ${on?"on":""}"><button class="wsh" onclick="wizOpen='${x.k}';lastKey='';render()"><span class="mk">${x.ok?"✓":i+1}</span>
      <span class="tx">${esc(x.title)}${x.opt?` <span class="mute" style="font-weight:500">(optional)</span>`:""}<small>${esc(x.status)}</small></span><span class="chev">${on?"▾":"›"}</span></button>
      ${on?`<div class="wsb">${x.body()}</div>`:""}</div>`; });
  const ready=need.every(x=>x.ok);
  h+=`<div class="row" style="justify-content:space-between;align-items:center">${ready?`<span class="ok">Ready to race ✓</span>`:`<span class="mute">${need.filter(x=>!x.ok).length} must-do step${need.filter(x=>!x.ok).length===1?"":"s"} left</span>`}
    <span class="row" style="margin:0"><button class="btn ${ready?"pri":""}" onclick="brandDo({setup_done:true},${ready?"'Ready to race'":"'You can come back from System › Setup'"})">${ready?"Done – go to racing":"Skip for now"}</button></span></div></div>`;
  return h;
}
async function brandDo(d,ok){ try{ const j=await (await fetch("/api/brand",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify(d)})).json();
  toast(j.result==="ok"?ok:j.result); if(j.result==="ok"&&st){ if("setup_done" in d){ st.setup_done=d.setup_done; wizOpen=null; } } }catch(e){ toast("No link to the timing computer"); } lastKey=""; render(); }
function saveBrand(){ brandDo({club:$("bclub").value,event:$("bevent").value},"Saved"); }
function logoPick(inp){ const f=inp.files&&inp.files[0]; if(!f) return; const img=new Image(), url=URL.createObjectURL(f);
  img.onload=()=>{ const s=Math.min(1,400/Math.max(img.width,img.height)), c=document.createElement("canvas"); c.width=Math.max(1,Math.round(img.width*s)); c.height=Math.max(1,Math.round(img.height*s));
    c.getContext("2d").drawImage(img,0,0,c.width,c.height); URL.revokeObjectURL(url); brandDo({logo:c.toDataURL("image/png")},"Logo saved"); };
  img.onerror=()=>toast("That file isn't a picture this browser can read"); img.src=url; }
function renderRace(){
  if(st&&st.role==="master"&&st.setup_done===false&&st.state!=="ARMED"&&st.state!=="RACING"&&!st.test){ $("race").innerHTML=`<div class="wizwrap">${wizard()}</div>`; return; }
  let h=banner(), right="";
  if(st&&st.connected) h+=raceWarnings();
  h=`<div class="top" style="display:flex;flex-direction:column;gap:12px">${h}</div>`;
  if(st&&st.connected){
    const ht=shownHeat(), n=st.lanes.length;
    h+=`<div class="grid" style="--lc:${n<=5?n:Math.ceil(n/2)}">`;
    for(const l of st.lanes){
      let hits=(st.live[String(l)]||[]), txt="—", sub="No presses";
      if(st.state==="DONE"&&st.results){ const row=st.results.rows.find(x=>x.lane===l);
        if(row){ const eq=(st.results.ties||[]).includes(l)?"=":"";
          txt=row.place?ft(row.t_us):row.status; sub=row.place?"Place "+eq+row.place+(row.status!=="TIMED"?" · "+row.status:""):"No place"; } }
      else if(hits.length){ txt=ft(hits[hits.length-1]); sub=hits.length+" press"+(hits.length>1?"es":""); }
      const cn=crewOf(ht,l), mv=ht&&(ht.swaps||[]).filter(s=>s.includes(l)).length, ck=checkOf(ht,l);
      h+=`<div class="lane ${hits.length?"hit":""} ${ck==="scratched"?"scr":""}"><div class="n">Lane ${l}</div>${cn?`<div class="crew">${esc(cn)}</div>`:""}${mv?`<div class="p">lane changed</div>`:""}
        ${ck==="scratched"?`<div class="scrt">SCRATCHED</div>`:ck==="present"?`<div class="chk">✓ checked in</div>`:""}
        <div class="p">${esc(sub)}</div><div class="t">${esc(txt)}</div></div>`;
    }
    h+=`</div>`;
    if(ht){ const extra=Object.keys(ht.crews||{}).map(Number).filter(l=>!st.lanes.includes(l)).sort((a,b)=>a-b);
      if(extra.length) h+=`<div class="others">Not wired yet: ${extra.map(l=>"Lane "+l+" "+esc(ht.crews[String(l)])).join(" · ")}</div>`; }
    right+=`<div class="ctl">${controls()}</div>`;
    if(st.state!=="RACING") right+=heatCard();
    if(st.state!=="RACING"&&st.official&&st.heat&&!evOpen){
      // a chosen heat already sets the event, so just show it
      const ce=chosenEvent();
      right+=`<div class="card"><h2>Event</h2><div class="row" style="align-items:center;justify-content:space-between;margin-top:0">
        <span><b>${esc(ce&&ce.legs?ce.name:"Not set")}</b>${ce&&ce.legs?` · ${ce.legs} leg${ce.legs===1?"":"s"}`:""}</span>
        <button class="btn sm" onclick="evOpen=true;lastKey='';render()">Change</button></div></div>`;
    } else if(st.state!=="RACING"&&st.official){
      let ev=`<div class="card"><h2>Event for the next race</h2><div class="row">`;
      for(const e of st.events) ev+=`<button class="btn ev ${e.id===st.event?"pri":""}" onclick="setEvent('${e.id}')">${esc(e.name)}${
        e.legs?`<small>${e.legs} leg${e.legs===1?"":"s"}</small>`:""}</button>`;
      ev+=`</div></div>`;
      right+=ev;
    }
    right+=`<p class="mute">The starter's SET and GO buttons work too. A press under ${st.min_leg_s} s after a crew's last press is ignored.</p>`;
  }
  $("race").innerHTML=`<div class="cols"><div>${h}</div><div>${right}</div></div>`; wireControls();
}
function raceWarnings(){
  let h="", pre="";
  if(st.silent) h+=`<div class="bad-warn">Timing box not responding – check its USB cable. The last few seconds may not have been recorded here.</div>`;
  if(st.practice) pre+=`<div class="practice">PRACTICE MODE – races are not saved here or sent to the LiveHeats list.</div>`;
  if(st.batt!=null&&st.batt<24.0) h+=`<div class="${st.batt<23.0?"bad-warn":"warn"}">Battery: ${battWord(st.batt)[0].toLowerCase()} – before the next race.</div>`;
  if(st.faults.length&&st.state==="RACING"&&st.faults_racing)
    h+=`<div class="bad-warn">Cable fault during race: ${esc(st.faults.join(", "))}. That lane may have a false press – check its presses after the race.</div>`;
  else if(st.faults.length&&st.state!=="RACING")
    h+=`<div class="warn">Check wiring: ${esc(st.faults.join(", "))} (open circuit or button held)</div>`;
  const ht=shownHeat();
  if(ht&&(st.state==="RACING"||st.state==="DONE")){
    const empty=st.lanes.filter(l=>!crewOf(ht,l)&&(st.live[String(l)]||[]).length);
    const scr=st.lanes.filter(l=>checkOf(ht,l)==="scratched"&&(st.live[String(l)]||[]).length);
    if(scr.length) h+=`<div class="bad-warn">Press in ${scr.map(l=>"lane "+l).join(", ")} – that crew was scratched by the marshals. Judges to check.</div>`;
    if(empty.length) h+=`<div class="warn">Press in ${empty.map(l=>"lane "+l).join(", ")} – no crew is drawn in ${empty.length>1?"those lanes":"that lane"}. Wrong-lane press? Judges to check.</div>`;
  }
  const pg=st.program||{};
  if(pg.mode==="on"&&st.heat&&st.state!=="RACING"&&!(st.state==="DONE"&&st.results&&st.results.heat&&st.results.heat.heat_id===st.heat.heat_id)){
    const sd=(st.sent||{})[st.heat.heat_id];
    if(!sd) h+=`<div class="bad-warn">Patients for this heat have not been marked as sent by the Marshal. Check before SET.</div>`;
    else if(sd.missing&&sd.missing.length&&Object.keys((st.checkin||{})[st.heat.heat_id]||{}).length) h+=`<div class="warn">Patients sent, but lane ${sd.missing.join(", ")} ${sd.missing.length>1?"were":"was"} not checked in by the Marshal. Check before SET.</div>`;
  }
  if(pg.warn&&st.state!=="RACING")
    h+=`<div class="warn">Only ${pg.left} heat${pg.left===1?"":"s"} left in the program after this one. ${st.official?`<a href="#" onclick="goTab('program');return false">Add more on the Program tab</a>, or turn the program off.`:"Tell the Referee."}</div>`;
  else if(pg.mode==null&&st.official&&st.state!=="RACING")
    h+=`<div class="warn">How are heats being run today? <a href="#" onclick="goTab('program');return false">Set up the program</a> (or choose No program).</div>`;
  if(pg.lh_changed&&st.official&&st.state!=="RACING")
    h+=`<div class="warn">The LiveHeats schedule has changed. <a href="#" onclick="goTab('program');return false">Review it on the Program tab</a>.</div>`;
  if(st.test) h+=`<div class="warn">Button test running – see the System tab. SET and GO are off until the test ends.</div>`;
  else if(st.has_test&&st.state!=="RACING"&&(!st.last_test||st.last_test.date!==st.today))
    h+=`<div class="warn">Button test not done today. <a href="#" onclick="goTab('system');return false">Do it on the System tab</a>.</div>`;
  else if(st.last_test&&st.last_test.date===st.today&&(st.last_test.missing.length||(st.last_test.clash||[]).length)&&st.state!=="RACING")
    h+=`<div class="warn">Today's button test found ${testProblems()}. <a href="#" onclick="goTab('system');return false">See System</a>.</div>`;
  // serious (red) messages always show; of the reminders, one shows and the rest fold away
  const box=document.createElement("div"); box.innerHTML=h;
  const all=Array.from(box.children), red=all.filter(x=>x.classList.contains("bad-warn")), amb=all.filter(x=>!x.classList.contains("bad-warn"));
  const show=red.concat(red.length?[]:amb.slice(0,1)), fold=amb.slice(red.length?0:1);
  let out=pre+show.map(x=>x.outerHTML).join("");
  if(fold.length) out+=(warnOpen?fold.map(x=>x.outerHTML).join(""):"")+`<button class="btn sm morew" onclick="warnOpen=!warnOpen;lastKey='';render()">${warnOpen?"Hide":"+ "+fold.length+" more check"+(fold.length===1?"":"s")}</button>`;
  return out;
}
let warnOpen=false;

// ---------- help: a few lines on what each screen is for ----------
const HELP={
  race:["This is where races are started and finished.","SET arms the race, GO starts the clock, FINISH (asks twice) ends it. The beach buttons do the same.",
    "The lane cards show each crew's presses as they come in.","Red messages must be checked before SET. Amber ones are reminders."],
  results:["Shows the race that just finished.","Tap Edit on a crew to accept, place, DQ or DNF them.","When the judges agree, press Confirm results. That locks the result.",
    "Every race goes Raced → Confirmed → Entered (in LiveHeats)."],
  program:["The running order for the day. Races follow this order by themselves.","Tap a heat to move it, run it next, add crew names or remove it.",
    "Add heats and Add break are the everyday buttons. More has next round, times, templates and the rest."],
  history:["Top card: races still to be typed into LiveHeats, one at a time. Press Entered when done.","Below: every race saved today. Tap one to see its full result."],
  marshal:["Pick a heat along the top.","Tap a crew when its patients arrive. Tap again to undo. Scratch is the button on the right.",
    "Press Patients sent when that heat's patients go out on the water."],
  system:["Today: the start-of-day checks, who has access, the button test, the screens and the join card.","Setup: things you set once per carnival – Wi-Fi, LiveHeats draw, backup, practice mode."]};
const FIXES=[
  ["Timing box not connected","Check the USB cable at both ends. Close Thonny if it's open. Unplug the cable, wait 5 seconds, plug it back in – the app finds the box by itself."],
  ["A phone can't open the app","The phone must be on the timing Wi-Fi, not mobile data. Scan the join card (Wi-Fi first, then the app). If it opened inside Messenger or Facebook, open it in Chrome, Samsung Internet or Safari instead. On the timing computer: System › Setup › Phones › Allow phones."],
  ["A button press didn't show","Run the button test (System) and press that button. Check its cable is in the right socket. A press within a few seconds of the same crew's last press is ignored on purpose."],
  ["The wrong heat is on the start","With a program on, the program sets the order. The timing desk or Referee changes it on the Program tab (tap the heat › Run next)."],
  ["LiveHeats won't load","This computer needs internet just while loading. Copy the event link from the browser's address bar. The last draw loaded stays usable without internet."],
  ["A screen keeps going to sleep","Set the screen timeout to Never (or the longest) in that device's settings."],
  ["Still stuck","On the timing computer: System › Setup › Problem report › Download, and send the file to whoever you hired the kit from."]];
function openHelp(){
  const names={race:"Race",results:"Confirm",program:"Program",history:"LiveHeats",marshal:"Marshal",system:"System"};
  $("sheetin").innerHTML=`<h2>${names[tab]||"Help"} – what this screen is for</h2><ul class="helpl">${(HELP[tab]||[]).map(x=>`<li>${esc(x)}</li>`).join("")}</ul>
    <p class="mute">The blue <b>Next</b> bar at the top always shows the next thing to do.</p>
    <h2 style="margin-top:14px">Something not working?</h2>${FIXES.map(([q,a])=>`<details class="fix"><summary>${esc(q)}</summary><p>${esc(a)}</p></details>`).join("")}
    <div class="row"><button class="btn pri" onclick="closeSheet()">OK</button></div>`;
  $("sheet").classList.add("on");
}
// ---------- one status for every race: Raced → Confirmed → Entered ----------
function raceStatus(conf,ent){ return `<span class="rst"><i class="on">Raced ✓</i><i class="${conf?"on":""}">Confirmed${conf?" ✓":""}</i><i class="${ent?"on":""}">Entered${ent?" ✓":""}</i></span>`; }
// ---------- start-of-day checks (Master) ----------
function dayChecks(){
  const pg=st.program||{}, lt=st.last_test, a=st.access||{officials:[]}, c=[];
  c.push({ok:st.connected&&!st.faults.length,label:"Timing box connected",hint:!st.connected?"Plug the timing box's USB cable into this computer":st.faults.length?"Check wiring: "+st.faults.join(", "):"Wiring OK"});
  c.push({ok:pg.mode!=null,label:"Heats for today",hint:pg.mode==="on"?"Program on":pg.mode==="off"?"No program – heats chosen by hand":"Choose the program, or No program",btn:"Program",act:"goTab('program')"});
  if(st.has_test){ const today=lt&&lt.date===st.today, bad=today&&(lt.missing.length||(lt.clash||[]).length);
    c.push({ok:today&&!bad,label:"Button test",hint:st.test?"Running now – press every button, then end the test":!today?"Not done today – use the Button test card":bad?"Found problems – fix and test again":"Done today, all buttons working"}); }
  const ns=a.officials.filter(o=>o.role==="starter").length, nm=a.officials.filter(o=>o.role==="marshal").length, na=a.officials.filter(o=>o.role==="admin").length;
  c.push({opt:true,ok:a.officials.length>0,label:"Officials approved",hint:a.officials.length?`Starter ${ns} · Marshal ${nm} · Referee ${na}`:"None yet – they scan the join card and ask for access"});
  if(st.firewall&&st.firewall.state===false) c.push({opt:true,ok:false,label:"Phones can connect",hint:"Windows is blocking phones",btn:"Allow",act:"post('/api/firewall',{}).then(()=>toast('Answer Yes on the Windows prompt'))"});
  c.push({opt:true,ok:!!(st.join&&st.join.ssid),label:"Join card ready",hint:st.join&&st.join.ssid?"Wi-Fi: "+st.join.ssid:"Add the Wi-Fi name and password",btn:st.join&&st.join.ssid?"":"Setup",act:"sysView='setup';lastKey='';render()"});
  c.push({opt:true,ok:!!(st.backup&&st.backup.ok),label:"Backup stick",hint:st.backup?(st.backup.ok?"Copied to "+st.backup.where:st.backup.msg):"Not checked yet",btn:st.backup&&st.backup.ok?"":"Check",act:"post('/api/backup',{}).then(()=>{lastKey='';render()})"});
  return c;
}
function dayReady(){ return dayChecks().filter(x=>!x.opt).every(x=>x.ok); }
function racedToday(){ return !!(st.results||Object.keys(st.raced||{}).length); }
let dayOpen=null;
function dayCard(){
  const c=dayChecks(), need=c.filter(x=>!x.opt), ready=need.every(x=>x.ok), open=dayOpen==null?!(ready&&racedToday()):dayOpen;
  if(!open) return `<div class="card"><div class="row" style="margin:0;align-items:center;justify-content:space-between"><h2 style="margin:0"><span class="tick">✓</span> Start-of-day checks done</h2>
    <button class="btn sm" onclick="dayOpen=true;lastKey='';render()">Show</button></div></div>`;
  let h=`<div class="card"><h2>Start of day</h2>`;
  for(const x of c) h+=`<div class="chk1 ${x.ok?"ok":""} ${x.opt?"opt":""}"><span class="mk">${x.ok?"✓":x.opt?"–":"!"}</span>
    <span class="tx">${esc(x.label)}${x.opt?" <span class='mute' style='font-weight:500'>(optional)</span>":""}<small>${esc(x.hint)}</small></span>
    ${x.btn&&!x.ok?`<button class="btn sm" onclick="${x.act}">${x.btn}</button>`:""}</div>`;
  h+=ready?`<div class="ready">Ready to race ✓</div>`:`<div class="notready">${need.filter(x=>!x.ok).length} thing${need.filter(x=>!x.ok).length===1?"":"s"} to do before racing</div>`;
  if(ready&&racedToday()) h+=`<div class="row"><button class="btn sm" onclick="dayOpen=false;lastKey='';render()">Hide</button></div>`;
  return h+`</div>`;
}
// ---------- the one next thing to do ----------
function nextStep(){
  if(!st||linkDown) return null;
  const role=st.role, pg=st.program||{}, s=st.state;
  if(role==="viewer"||location.hash==="#board"||location.hash==="#team"||location.hash==="#marshalling") return null;
  if(role==="marshal"){
    if(!mUp||!mUp.heats.length) return {text:"No heats to marshal yet",calm:true};
    const sentOf=id=>(mUp.sent||{})[id], hs=mUp.heats;     // includes the heat on the start
    const late=hs.slice(0,3).find(x=>!sentOf(x.heat_id)), nx=late||hs.find(x=>!sentOf(x.heat_id));
    if(!nx) return {text:"All patients are sent for the heats coming up",calm:true};
    const ck=mUp.checkin[nx.heat_id]||{}, left=mLanes(nx).filter(([l])=>!ck[l]).length;
    return {text:late?`Send patients: Heat ${nx.no} · ${nx.div}`:left?`Check in patients: Heat ${nx.no} · ${left} to come`:`All here – send Heat ${nx.no} when it's time`,tab:"marshal",btn:"Heat "+nx.no,act:`mSel='${nx.heat_id}';mPicked=true`,same:mSel===nx.heat_id};
  }
  if(!st.connected) return {text:"Timing box not connected – plug its USB cable into this computer",tab:"system",btn:"System"};
  if(role==="master"&&st.setup_done===false&&s!=="ARMED"&&s!=="RACING"&&!st.test){ const w=wizSteps(); return {text:`Get started – ${w.filter(x=>x.ok).length} of ${w.length} steps done`,tab:"race",btn:"Get started"}; }
  if(role==="master"&&st.access&&st.access.requests.length) return {text:`${st.access.requests[0].name} is waiting for access${st.access.requests.length>1?" (+"+(st.access.requests.length-1)+" more)":""}`,tab:"system",btn:"Approve",act:"sysView='today'"};
  if(s==="RACING") return st.can_start?{text:"Racing – press FINISH when every crew is in",tab:"race",btn:"Race"}:{text:"Race in progress",calm:true};
  if(s==="ARMED") return st.can_start?{text:"Armed – press GO to start",tab:"race",btn:"Race"}:{text:"Race about to start",calm:true};
  if(st.test) return (role==="master"||role==="starter")?{text:"Button test running – press every button, then end the test",tab:"system",btn:"Test",act:"sysView='today'"}:null;
  if(st.official&&s==="DONE"&&st.results&&!st.confirmed&&!st.results.practice) return {text:`Race ${st.results.race} finished – check the result, then Confirm results`,tab:"results",btn:"Confirm"};
  if(role==="master"&&!racedToday()&&!dayReady()){ const n=dayChecks().filter(x=>!x.opt&&!x.ok).length; return {text:`Start of day – ${n} check${n===1?"":"s"} to do`,tab:"system",btn:"Checklist",act:"sysView='today'"}; }
  if(st.official&&pg.mode==null) return {text:"Choose how heats are run today",tab:"program",btn:"Program"};
  if(role==="admin"){
    if((st.queue_n||0)>0) return {text:`${st.queue_n} race${st.queue_n===1?"":"s"} to enter in LiveHeats`,tab:"history",btn:"Enter"};
    if(pg.warn) return {text:`Only ${pg.left} heat${pg.left===1?"":"s"} left in the program – add more`,tab:"program",btn:"Program"};
    return {text:"All up to date – waiting for the next race",calm:true};
  }
  if(role==="starter"&&st.has_test&&(!st.last_test||st.last_test.date!==st.today)) return {text:"Do the button test before the first race",tab:"system",btn:"Test"};
  if(st.faults.length) return {text:"Fix wiring before SET: "+st.faults.join(", "),tab:"system",btn:"System"};
  if(pg.mode==="on"&&!st.heat) return {text:"The program is finished"+(st.official?" – add more heats":" – tell the Referee"),tab:st.official?"program":"race",btn:st.official?"Program":"Race"};
  // small carnival with no Marshal approved: the Master does the marshalling too
  if(role==="master"&&pg.mode==="on"&&st.heat&&!(st.sent||{})[st.heat.heat_id]&&!((st.access||{}).officials||[]).some(o=>o.role==="marshal"))
    return {text:`Patients not marked as sent for Heat ${st.heat.no} – no Marshal is logged in`,tab:"marshal",btn:"Marshal",act:`mSel='${st.heat.heat_id}'`};
  const q=role==="master"&&(st.queue_n||0)>0?` · ${st.queue_n} to enter in LiveHeats`:"";
  return {text:`Ready – press SET${st.heat?" for "+heatLabel(st.heat):""}${q}`,tab:"race",btn:"Race"};
}
let nextKey="";
function drawNext(){
  const b=$("nextbar"), n=nextStep(); if(!b) return;
  const k=JSON.stringify([n,tab]); if(k===nextKey) return; nextKey=k;
  if(!n){ b.hidden=true; return; }
  const here=!n.tab||(n.tab===tab&&n.same!==false);
  b.hidden=false; b.className=n.calm?"calm":"";
  b.innerHTML=`<span class="nx">${n.calm?"OK":"NEXT"}</span><span class="nt">${esc(n.text)}</span>${here?"":`<button class="btn sm pri" id="nxgo">${esc(n.btn||"Go")} ›</button>`}`;
  const g=$("nxgo"); if(g) g.onclick=()=>{ if(n.act) (new Function(n.act))(); goTab(n.tab); lastKey=""; render(); };
}
function goTab(n){ const b=document.querySelector('.tab[data-t="'+n+'"]'); if(b) b.click(); }
const ROLE_NAME={master:"Timing desk",admin:"Referee",starter:"Starter",marshal:"Marshal",viewer:"Viewer"};
function setWarnings(){
  const w=[];
  const ph=st.program&&st.program.mode==="on";
  if(st.state==="DONE"&&st.results&&!st.confirmed) w.push(`Race ${st.results.race} results aren't confirmed yet.`);
  if((st.draw||ph)&&!st.heat) w.push("No heat chosen – lanes will show without crew names.");
  if(st.heat&&st.raced[st.heat.heat_id]!=null) w.push(`${heatLabel(st.heat)} was already raced (race ${st.raced[st.heat.heat_id]}).`);
  return w;
}
function allIn(){
  const legs=(st.race_event&&st.race_event.legs)||0, ht=st.race_heat;
  const crews=ht?st.lanes.filter(l=>crewOf(ht,l)):st.lanes;
  return legs>0&&crews.length>0&&crews.every(l=>(st.live[String(l)]||[]).length>=legs);
}
let setAsk=0;
function controls(){
  const s=st.state, app=st.app_start;
  let h="";
  if(!st.can_start) return st.role==="admin"?`<div class="viewonly"><div><b>Referee</b><div class="mute">SET, GO and FINISH are on the Starter's screen.</div></div></div>`
    :`<div class="viewonly"><div><b>View only</b><div class="mute">Officials: ask the timing desk for access.</div></div>
    <button class="btn pri" onclick="openRequest()">Officials</button></div>`;
  if(st.test) return "";
  if(st.at_prompt||(!app&&s!=="RACING"&&s!=="ARMED")){
    if(!app&&!st.at_prompt) h+=`<p class="mute">On-screen SET and GO need the Pico program v2.6 or later.</p>`;
    return h;
  }
  if(s==="IDLE"||s==="DONE"){
    if(st.faults.length) return h+`<div class="start"><button class="btn amber" disabled>SET – fix wiring first</button></div>`;
    const what=st.heat?heatLabel(st.heat):(chosenEvent()&&chosenEvent().legs?chosenEvent().name:"No heat or event chosen");
    const w=setWarnings();
    if(setAsk&&Date.now()-setAsk<15000&&w.length)
      return h+`<div class="card confirm"><h2>Check before SET</h2>${w.map(x=>`<p style="margin:6px 0">• ${esc(x)}</p>`).join("")}
        <div class="row"><button class="btn amber" id="bsetok">SET anyway</button><button class="btn" id="bsetno">Cancel</button></div></div>`;
    setAsk=0;
    return h+`<div class="start"><button class="btn amber" id="bset">SET<small>${esc(what)}</small></button></div>`;
  }
  if(s==="ARMED"){
    if(app) h+=`<div class="start"><button class="btn green" id="bgo">GO</button></div>`;
    return h+`<div class="card"><button class="btn hold" id="hold"><i></i><span>Hold to CANCEL (before GO)</span></button></div>`;
  }
  // RACING
  if(app&&(st.elapsed||0)<5) h+=`<div class="start"><button class="btn red" id="brecall">RECALL</button></div>`;
  if(finishAsk&&Date.now()-finishAsk<10000){
    const n=st.lanes.filter(l=>(st.live[String(l)]||[]).length).length;
    h+=`<div class="card confirm"><h2>Finish race ${st.race+1}?</h2>
      <p>${n} of ${st.lanes.length} crews have pressed. Crews still racing will show as incomplete.</p>
      <button class="btn hold" id="hold"><i></i><span>Hold to CONFIRM finish</span></button>
      <div class="row"><button class="btn" id="bkeep">Keep racing</button></div></div>`;
  } else {
    finishAsk=0;
    const all=allIn();
    h+=`<div class="card"><button class="btn ${all?"allin":"pri"}" id="bfin" style="width:100%;font-size:22px;min-height:64px">${all?"All crews in – FINISH race…":"FINISH race…"}</button>
      <div class="mute" style="margin-top:8px">${all?"Every crew has done the expected legs. ":""}Asks again before it finishes. The FINISH button on the beach still works.</div></div>`;
  }
  return h;
}
function heatCard(){
  if(st.program&&st.program.mode==="on"){       // the program decides the heat
    let h=`<div class="card"><h2>Heat for the next race</h2>`;
    h+=st.heat?`<div><b>${esc(st.heat.div)}</b></div><div class="mute">${esc(st.heat.round)} · Heat ${st.heat.no}</div>`
      :`<p class="warn">The program is finished – ${st.official?"add more heats on the Program tab":"the Referee adds more heats"}.</p>`;
    h+=`<p class="mute" style="margin:6px 0 0">Heats follow the program. ${st.official?"To change the order, use the Program tab.":"The Referee changes the order on the Program tab."}</p>`;
    if(st.official) h+=`<div class="row">${st.heat?`<button class="btn" onclick="openSwap()">Swap lanes</button>`:""}<button class="btn" onclick="goTab('program')">Program ›</button></div>`;
    return h+`</div>`;
  }
  if(!st.official){
    const pon=st.program&&st.program.mode==="on";
    let h=st.heat?`<div class="card"><h2>Heat for the next race</h2><div><b>${esc(st.heat.div)}</b></div><div class="mute">${esc(st.heat.round)} · Heat ${st.heat.no}</div>`
      :`<div class="card"><h2>Heat</h2><p class="mute">${st.role==="starter"?"The Referee chooses the heat.":"No heat chosen yet."}</p>`;
    if(st.role==="starter"&&pon) h+=`<div class="row"><button class="btn pri" onclick="post('/api/heat',{next:true})">Next in program ›</button></div>`;
    return h+`</div>`;
  }
  if(!st.draw&&!(st.program&&st.program.manual)) return `<div class="card"><h2>Heat</h2><p class="mute">Load a LiveHeats draw, or add heats on the Program tab, to show which heat is racing.</p>
    <div class="row"><button class="btn" onclick="openLoad()">Load LiveHeats draw</button><button class="btn" onclick="goTab('program')">Program</button></div></div>`;
  let h=`<div class="card"><h2>Heat for the next race</h2>`;
  h+=st.heat?`<div><b>${esc(st.heat.div)}</b></div><div class="mute">${esc(st.heat.round)} · Heat ${st.heat.no}</div>`
            :`<p class="mute">No heat chosen – lanes show without names.</p>`;
  h+=`<div class="row"><button class="btn pri" onclick="openHeats()">${st.heat?"Change heat":"Choose heat"}</button>`;
  if(st.heat) h+=`<button class="btn" onclick="post('/api/heat',{next:true})">${st.program&&st.program.mode==="on"?"Next in program ›":"Next heat ›"}</button><button class="btn" onclick="openSwap()">Swap lanes</button>`;
  return h+`</div></div>`;
}
async function reloadDraw(){
  const b=$("reload"); if(b){ b.disabled=true; b.textContent="Loading…"; }
  toast("Getting the latest draw from LiveHeats…");
  try{ const r=await fetch("/api/draw/load",{method:"POST",headers:{"Content-Type":"application/json"},
      body:JSON.stringify({url:"https://www.liveheats.com/events/"+st.draw.id})}); const j=await r.json();
    if(j.result==="ok"){ drawData=null; toast("Draw updated"); } else toast(j.result);
  }catch(e){ toast("No link to the timing computer"); }
  lastKey=""; render();
}
async function getDraw(){
  if(!drawData||drawData.loaded_at!==((st.draw&&st.draw.loaded_at)+"/"+(st.program&&st.program.ver))){
    try{ drawData=await (await fetch("/api/draw")).json(); }catch(e){ toast("No link to the timing computer"); return null; } }
  return drawData;
}
let pickDiv=null;
async function openHeats(){
  const d=await getDraw(); if(!d||!d.divisions) return;
  if(!pickDiv) pickDiv=(st.heat&&st.heat.div_id)||d.divisions[0].id;
  const dv=d.divisions.find(x=>x.id===pickDiv)||d.divisions[0];
  let h=`<h2>Choose heat</h2><div class="row" style="margin:0 0 10px">${st.draw?`<button class="btn sm" id="reload" onclick="closeSheet();reloadDraw()">Reload draw from LiveHeats</button>`:""}
    ${st.heat?`<button class="btn sm" onclick="closeSheet();post('/api/heat',{clear:true})">Clear heat (no names)</button>`:""}</div><select id="divsel">${d.divisions.map(x=>`<option value="${x.id}" ${x.id===dv.id?"selected":""}>${esc(x.name)}</option>`).join("")}</select>`;
  let round=null;
  for(const ht of dv.heats){
    if(ht.round!==round){ if(round!==null) h+=`</div>`; round=ht.round; h+=`<div style="margin-top:12px;font-weight:700">${esc(round)}</div><div class="heatbtns">`; }
    const on=st.heat&&st.heat.heat_id===ht.id, done=st.raced[ht.id]!=null;
    h+=`<button class="btn ${on?"pri":""} ${done?"done":""}" onclick="pickHeat('${dv.id}','${ht.id}')">${done?"✓ ":""}Heat ${ht.no}<small style="display:block;font-weight:500;font-size:13px">${
      done?"raced (race "+st.raced[ht.id]+")":ht.crews.length?ht.crews.length+" crews":"not drawn yet"}</small></button>`;
  }
  h+=`</div><div class="row"><button class="btn" onclick="closeSheet()">Close</button></div>`;
  $("sheetin").innerHTML=h; $("sheet").classList.add("on");
  $("divsel").onchange=e=>{ pickDiv=e.target.value; openHeats(); };
}
let swapFrom=null;
function openSwap(){
  const ht=st.heat, n=Math.max(10,...st.lanes,...Object.keys(ht.crews||{}).map(Number));
  let h=`<h2>Swap lanes</h2><p class="mute">${swapFrom?`Move lane ${swapFrom} (${esc(crewOf(ht,swapFrom)||"empty")}) to which lane? A crew already there swaps across.`
    :"Which crew is moving? (e.g. their lane's button is broken)"}</p><div class="heatbtns">`;
  for(let l=1;l<=n;l++) h+=`<button class="btn ${swapFrom===l?"pri":""}" onclick="swapPick(${l})">Lane ${l}<small style="display:block;font-weight:500;font-size:12px">${esc(crewOf(ht,l)||"empty")}</small></button>`;
  h+=`</div><div class="row"><button class="btn" onclick="swapFrom=null;closeSheet()">Cancel</button></div>`;
  $("sheetin").innerHTML=h; $("sheet").classList.add("on");
}
async function swapPick(l){
  if(!swapFrom){ swapFrom=l; openSwap(); return; }
  if(l===swapFrom){ swapFrom=null; openSwap(); return; }
  const a=swapFrom; swapFrom=null; closeSheet(); await post("/api/heat",{swap:[a,l]}); toast(`Lane ${a} and lane ${l} swapped`);
}
async function pickHeat(div,heat){ await post("/api/heat",{div:div,heat:heat}); closeSheet(); }
function openLoad(){
  let h=`<h2>Load LiveHeats draw</h2><p class="mute">Paste the event link. This computer needs internet for this step only –
    the draw is kept for use at the beach.</p><input type="text" id="lhurl" placeholder="https://www.liveheats.com/events/505147"
    value="${st.draw?"https://www.liveheats.com/events/"+esc(st.draw.id):""}">
    <div class="row"><button class="btn pri" id="lhgo">Load draw</button><button class="btn" onclick="closeSheet()">Close</button></div>
    <p class="mute" id="lhmsg"></p>`;
  $("sheetin").innerHTML=h; $("sheet").classList.add("on");
  $("lhgo").onclick=async()=>{ $("lhgo").disabled=true; $("lhmsg").textContent="Loading from LiveHeats…";
    try{ const r=await fetch("/api/draw/load",{method:"POST",headers:{"Content-Type":"application/json"},
        body:JSON.stringify({url:$("lhurl").value})}); const j=await r.json();
      if(j.result==="ok"){ drawData=null; pickDiv=null; closeSheet(); toast("Draw loaded"); } else { $("lhmsg").textContent=j.result; }
    }catch(e){ $("lhmsg").textContent="No link to the timing computer"; }
    $("lhgo").disabled=false; };
}
async function startCmd(c,expect){ if(startBusy) return; startBusy=true;
  document.querySelectorAll(".start .btn").forEach(b=>b.disabled=true);
  await cmd(c,expect); setTimeout(()=>{ startBusy=false; lastKey=""; render(); },800); }
function wireControls(){
  const on=(id,f)=>{ const b=$(id); if(b) b.onclick=f; };
  on("bset",()=>{ if(setWarnings().length){ setAsk=Date.now(); lastKey=""; render(); setTimeout(()=>{ lastKey=""; render(); },15100); }
    else startCmd("set","IDLE|DONE"); });
  on("bsetok",()=>{ setAsk=0; startCmd("set","IDLE|DONE"); });
  on("bsetno",()=>{ setAsk=0; lastKey=""; render(); });
  on("bgo",()=>startCmd("go","ARMED"));
  on("brecall",()=>startCmd("go","RACING"));
  on("bfin",()=>{ finishAsk=Date.now(); lastKey=""; render(); setTimeout(()=>{ lastKey=""; render(); },10100); });
  on("bkeep",()=>{ finishAsk=0; lastKey=""; render(); });
  wireHold();
}
let holdT=null, holding=false;
function wireHold(){ const b=$("hold"); if(!b) return; const bar=b.querySelector("i");
  const start=e=>{ e.preventDefault(); const want=st.state; holding=true; bar.style.transition="width 1s linear"; bar.style.width="100%";
    holdT=setTimeout(()=>{ holding=false; finishAsk=0; cmd("f",want); bar.style.transition="none"; bar.style.width="0"; },1000); };
  const stop=()=>{ holding=false; clearTimeout(holdT); bar.style.transition="none"; bar.style.width="0"; };
  b.onpointerdown=start; b.onpointerup=stop; b.onpointerleave=stop; b.onpointercancel=stop; b.oncontextmenu=e=>e.preventDefault(); }

function wall(go,us){ const d=new Date(go*1000+us/1000), p=(n,w)=>String(n).padStart(w||2,"0");
  return p(d.getHours())+":"+p(d.getMinutes())+":"+p(d.getSeconds())+"."+p(d.getMilliseconds(),3); }
function ranked(res){
  // same rule as the Pico: gaps run between timed crews; a crew placed by officials breaks the chain
  let prev=null;
  return res.rows.slice().sort((a,b)=>(a.place||99)-(b.place||99)||a.lane-b.lane).map(r=>{
    const counted=r.place&&r.status!=="PLACED"&&r.t_us!=null;
    const gap=(counted&&prev!=null)?r.t_us-prev:null;
    prev=counted?r.t_us:null;
    return Object.assign({},r,{gap:gap,tooClose:gap!=null&&gap<TOO_CLOSE_US});
  });
}
function resultsTable(res, tappable){
  let h=`<div style="overflow-x:auto"><table><tr><th>Place</th><th>Crew</th><th>Time</th>${tappable?"<th></th>":""}</tr>`;
  for(const r of ranked(res)){
    let splits=""; if(res.legs>1&&r.presses_us.length>=res.legs&&r.status==="TIMED"){ let last=0;
      splits=r.presses_us.slice(0,res.legs).map((t,i)=>{const x="Leg\u00a0"+(i+1)+"\u00a0"+ft(t-last); last=t; return x;}).join(" · "); }
    const ch=res.changes[String(r.lane)];
    const extra=r.presses_us.length>res.legs&&res.legs>0&&(r.status==="TIMED"||r.status==="ACCEPTED")?`<div class="split">CHECK: ${r.presses_us.length} presses, ${res.legs} used</div>`:"";
    const vid=res.go_wall&&r.t_us!=null&&r.tooClose?`<div class="vid">video ${wall(res.go_wall,r.t_us)}</div>`:"";
    const dqc=r.status==="DQ"&&res.flags&&(res.flags.dq||{})[String(r.lane)]?` · ${esc(res.flags.dq[String(r.lane)])}`:"";
    h+=`<tr class="${tappable?"tap":""}" data-lane="${r.lane}"><td><b>${r.place?((res.ties||[]).includes(r.lane)?"=":"")+r.place:""}</b></td><td class="cr"><span style="white-space:nowrap">Lane ${r.lane}</span>${crewOf(res.heat,r.lane)?`<div class="crew">${esc(crewOf(res.heat,r.lane))}</div>`:""}</td>
      <td class="tm">${ft(r.t_us)}${r.gap!=null?`<div><span class="gap">+${ft(r.gap)}</span>${r.tooClose?`<span class="close">TOO CLOSE</span>`:""}</div>`:""}${splits?`<div class="split">${splits}</div>`:""}${extra}${r.status!=="TIMED"?`<div><span class="tag t-${r.status}">${r.status}${dqc}</span></div>`:""}${vid}${ch?`<div class="split">officials: ${esc(ch)}</div>`:""}</td>${
      tappable?`<td class="ed"><button class="btn sm">Edit</button></td>`:""}</tr>`;
  }
  return h+`</table></div>`;
}
function renderResults(){
  const res=st&&st.results&&Object.assign({},st.results,{flags:st.res_flags||{}});
  if(!res){ $("results").innerHTML=`<div class="card"><h2>No results yet</h2><p class="mute">Results show here after FINISH.</p></div>`; return; }
  const live=st.state==="DONE"&&st.race===res.race&&st.connected&&st.official;
  const can=live&&!st.confirmed;
  const adj=Object.keys(res.changes).length||res.legs_set;
  let w="";
  let h=`<div class="card"><h2>Race ${res.race}${res.heat?" – "+esc(heatLabel(res.heat)):res.event?" – "+esc(res.event):""} – ${res.legs} leg${res.legs===1?"":"s"}</h2>
    ${res.practice?"":`<div style="margin:-2px 0 8px">${raceStatus(live?st.confirmed:!!(res.flags||{}).confirmed,!!(res.flags||{}).entered)}</div>`}
    ${res.practice?`<div class="practice" style="margin-bottom:8px">Practice race – not saved</div>`:""}
`;
  if(adj) w+=`<div class="warn">ADJUSTED BY OFFICIALS</div>`;
  if(can&&res.event_legs&&res.legs>0&&res.legs!==res.event_legs)
    w+=`<div class="warn">${esc(res.event)} is normally ${res.event_legs} leg${res.event_legs===1?"":"s"}, but the presses worked out as ${res.legs}.
      <div class="row"><button class="btn pri" onclick="cmd('legs ${res.event_legs}')">Set race to ${res.event_legs} leg${res.event_legs===1?"":"s"}</button></div></div>`;
  const close=ranked(res).filter(r=>r.tooClose).length;
  if(close) w+=`<div class="warn">Finish under 0.010 s apart – judges to review before confirming places.</div>`;
  const counts=res.rows.map(r=>r.presses_us.length).filter(n=>n>0);
  const inc=res.rows.filter(r=>r.status==="INCOMPLETE").length;
  // one warning, not two: incomplete crews are the usual reason press counts differ
  if(inc&&can) w+=`<div class="warn">${inc} crew${inc>1?"s":""} incomplete (fewer presses) – referee check, then Edit to accept or place them.</div>`;
  else if(counts.length&&Math.min(...counts)!==Math.max(...counts)) w+=`<div class="warn">Crews have different press counts – referee check.</div>`;
  h+=`<div class="narrowonly">${w}</div>`+resultsTable(res, can);
  h+=can?`<p class="mute narrowonly" style="margin-bottom:0">Press Edit to accept, place, DQ or DNF a crew.</p>`
    :live?`<p class="mute">Confirmed – press Reopen results to change anything.</p>`
    :!st.official?`<p class="mute">View only.</p>`:`<p class="mute">Adjustments are only possible straight after FINISH, before the next SET.</p>`;
  h+=`</div>`;
  let right="";
  if(live) right+=st.confirmed?`<div class="card"><h2><span class="tick">✓</span> Results confirmed</h2>
      <p class="mute">Locked. Next heat is ready. Reopen only if a change is still needed.</p>
      <div class="row"><button class="btn" onclick="post('/api/confirm',{race:${res.race},undo:true})">Reopen results</button></div></div>`
    :`<div class="card"><button class="btn pri" style="width:100%;font-size:20px;min-height:64px" onclick="post('/api/confirm',{race:${res.race}})">Confirm results ✓</button>
      <p class="mute" style="margin:8px 0 0">When the judges agree. Locks results and moves to the next heat.</p>
      ${myName()?"":`<div class="log">Tip: add your name on the System tab so changes show who made them.</div>`}</div>`;
  if(w) right+=`<div class="wideonly" style="display:flex;flex-direction:column;gap:12px">${w}</div>`;
  const fl=res.flags||{};
  if(live) right+=`<div class="card"><div class="row" style="margin:0;align-items:center;justify-content:space-between"><h2 style="margin:0">Race note</h2>
      <button class="btn sm" onclick="openNote(${res.race})">${fl.note?"Edit note":"Add note"}</button></div>
      ${fl.note?`<p style="margin:6px 0 0">${esc(fl.note)}</p>`:""}${fl.note_by?`<div class="log">Saved by ${esc(fl.note_by)}</div>`:""}</div>`;
  else if(fl.note) right+=`<div class="card"><h2>Race note</h2><p>${esc(fl.note)}</p></div>`;
  if((fl.log||[]).length) right+=`<div class="card"><h2>Changes</h2>${fl.log.map(x=>`<div class="log">${esc(x[0])} ${esc(x[1])}: ${esc(x[2])}</div>`).join("")}</div>`;
  if(can){
    right+=`<div class="card"><h2 style="margin:0">Number of legs</h2><div class="mute" style="font-size:14px">From the presses. Change only if most crews missed a press.</div><div class="row">`;
    for(let n=1;n<=4;n++) right+=`<button class="btn ${n===res.legs?"pri":""}" onclick="cmd('legs ${n}')">${n}</button>`;
    right+=`</div><div class="row"><button class="btn" onclick="askYes('Undo every change made to this race, including the number of legs?',()=>cmd('clear'),'Yes, undo all')">Undo ALL changes (whole race)</button></div></div>`;
  }
  $("results").innerHTML=`<div class="cols"><div>${h}</div><div>${right}</div></div>`;
  if(can) document.querySelectorAll("#results tr.tap").forEach(tr=>tr.onclick=()=>openSheet(+tr.dataset.lane));
}
function openSheet(l){ sel=l; const n=st.lanes.length; const row=st.results.rows.find(x=>x.lane===l);
  const ch=st.results.changes[String(l)];
  const cn=crewOf(st.results.heat,l);
  const vt=(row&&row.presses_us.length?`<p class="vid">Presses: ${row.presses_us.map((x,i)=>"#"+(i+1)+" "+ft(x)).join(" · ")}</p>`:"")+
    (st.results.go_wall&&row&&row.t_us!=null?`<p class="vid">Video: finish at ${wall(st.results.go_wall,row.t_us)} (GO ${wall(st.results.go_wall,0)})</p>`:"");
  let h=`<h2>Edit lane ${l}${cn?" – "+esc(cn):""} – ${row?row.status:""}</h2>${vt}${ch?`<p class="mute">Current change: ${esc(ch)}</p>`:""}<div class="row">
    <button class="btn pri" onclick="act('ok ${l}')">Accept – missed a press</button>
    <button class="btn" onclick="act('dnf ${l}')">DNF</button>
    <button class="btn red" onclick="askDq(${l})">DQ…</button></div>
    ${st.ties&&row&&row.place>1&&!(st.results.ties||[]).includes(l)?`<div class="row"><button class="btn" onclick="act('tie ${l}')">Dead heat with the crew ahead (equal place)</button></div>`:""}
    <div style="margin-top:12px" class="mute">Move to place (no time needed):</div><div class="places">`;
  for(let p=1;p<=n;p++) h+=`<button class="btn" onclick="act('place ${l} ${p}')">${p}</button>`;
  h+=`</div><div class="row">${ch?`<button class="btn" onclick="act('clear ${l}')">Undo lane ${l}'s change only</button>`:""}
    <button class="btn" onclick="closeSheet()">Close</button></div>`;
  $("sheetin").innerHTML=h; $("sheet").classList.add("on"); }
function undoFor(l){
  // the command that puts lane l back how it was before this change
  const ch=(st.results.changes||{})[String(l)];
  if(!ch||ch.includes(",")||ch==="dead heat") return "clear "+l;
  if(ch.startsWith("place ")) return "place "+l+" "+ch.slice(6);
  return ch+" "+l;
}
const ACT_TXT={ok:"accepted",dq:"DQ",dnf:"DNF",place:"moved",tie:"dead heat",clear:"change undone"};
function recentCodes(){ try{ return JSON.parse(localStorage.getItem("irb_dq")||"[]"); }catch(e){ return []; } }
function askDq(l){
  const cn=crewOf(st.results.heat,l);
  $("sheetin").innerHTML=`<h2>DQ lane ${l}${cn?" – "+esc(cn):""}</h2><p class="mute">DQ code or reason (from the Surf Sports Manual)</p>
    <input type="text" id="dqcode" list="dqlist" placeholder="e.g. code and short reason"><datalist id="dqlist">${recentCodes().map(c=>`<option value="${esc(c)}">`).join("")}</datalist>
    <div class="row"><button class="btn red" id="dqgo">Confirm DQ</button><button class="btn" onclick="closeSheet()">Cancel</button></div>`;
  $("sheet").classList.add("on"); $("dqcode").focus();
  $("dqgo").onclick=()=>{ const c=$("dqcode").value.trim();
    if(c){ try{ localStorage.setItem("irb_dq",JSON.stringify([c].concat(recentCodes().filter(x=>x!==c)).slice(0,12))); }catch(e){} }
    act("dq "+l,c); };
}
function openNote(race){
  const fl=st.res_flags||{};
  $("sheetin").innerHTML=`<h2>Race ${race} note</h2><textarea id="note" placeholder="e.g. Lane 3 protest – dismissed">${esc(fl.note||"")}</textarea>
    <div class="row"><button class="btn pri" id="notego">Save note</button><button class="btn" onclick="closeSheet()">Cancel</button></div>`;
  $("sheet").classList.add("on"); $("note").focus();
  $("notego").onclick=()=>{ saveNote(race); closeSheet(); };
}
async function saveNote(race){ await post("/api/note",{race:race,text:$("note").value}); toast("Note saved"); }
async function act(c,code){
  const w=c.split(" "), l=+w[1], back=undoFor(l), cn=crewOf(st.results.heat,l);
  closeSheet(); await post("/api/cmd",{cmd:c,code:code||""});
  if(w[0]!=="clear") showUndo(`Lane ${l}${cn?" "+cn:""} – ${ACT_TXT[w[0]]}${w[0]==="place"?" to "+w[2]:""}`, back);
}
let undoT=null;
function showUndo(text,back,fn){ const u=$("undo"); $("undotxt").textContent=text; u.classList.add("on");
  $("undobtn").onclick=()=>{ u.classList.remove("on"); if(fn) fn(); else cmd(back); };
  clearTimeout(undoT); undoT=setTimeout(()=>u.classList.remove("on"),7000); }
function closeSheet(){ sel=null; $("sheet").classList.remove("on"); }
let yesFn=null;
function askYes(q,fn,yes,red){ yesFn=fn;
  $("sheetin").innerHTML=`<h2>${esc(q)}</h2><div class="row"><button class="btn ${red===false?"pri":"red"}" id="yesgo">${esc(yes||"Yes")}</button><button class="btn" onclick="closeSheet()">Cancel</button></div>`;
  $("sheet").classList.add("on"); $("yesgo").onclick=()=>{ const f=yesFn; yesFn=null; closeSheet(); if(f) f(); }; }

// ---------- Program: the running order of heats for the day ----------
let prog=null, progAt=0, progVer=-1, progSeen="", addDiv=null, altDiv="", picked=[];
function progState(){ return st?JSON.stringify([st.program&&st.program.ver,st.heat&&st.heat.heat_id,st.state,Object.keys(st.raced||{}).length]):""; }
async function loadProg(){ try{ const k=progState(); prog=await (await fetch("/api/program")).json(); progAt=Date.now(); progVer=prog.ver; progSeen=k; }catch(e){} }
function hl(x){ return `${x.div} · ${x.round} · Heat ${x.no}`; }
function hhmm(iso){ try{ const d=new Date(iso); return String(d.getHours()).padStart(2,"0")+":"+String(d.getMinutes()).padStart(2,"0"); }catch(e){ return ""; } }
async function progDo(data,msg){
  let j; try{ j=await (await fetch("/api/program",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify(Object.assign({who:myName()},data))})).json(); }
  catch(e){ toast("No link to the timing computer"); return; }
  if(j.result.startsWith("PATIENTS:")){ closeSheet();
    $("sheetin").innerHTML=`<h2>Patients already out</h2><p>${esc(j.result.slice(9))}</p><p class="mute">Check with the Marshal first.</p>
      <div class="row"><button class="btn red" id="pfgo">Do it anyway</button><button class="btn" onclick="closeSheet()">Cancel</button></div>`;
    $("sheet").classList.add("on"); $("pfgo").onclick=()=>{ closeSheet(); progDo(Object.assign({},data,{force:true}),msg); }; return; }
  if(j.result!=="ok"&&!j.result.startsWith("ok:")) toast(j.result); else if(msg) toast(msg);
  await loadProg(); lastKey=""; render(); }
let progMore=false;
function renderProgram(){
  if(!st) return;
  if(!prog){ $("program").innerHTML=`<div class="card mute">Loading…</div>`; return; }
  const p=prog, pg=st.program||{}, off=!st.official;
  let left="", right="";
  // --- setup: how will heats be run today? ---
  if(p.mode==null&&!off){
    right+=`<div class="card"><h2>How will heats be run today?</h2><div class="choice">
      ${st.draw?`<button class="btn ${p.lh?"pri":""}" ${p.lh?"":"disabled"} onclick="progDo({import:true},'Program loaded from LiveHeats')">Use the LiveHeats schedule
        <small>${p.lh?esc(p.lh_src)+" – you can still change it during the day":"This event has no schedule in LiveHeats"}</small></button>`
       :`<button class="btn" onclick="openLoad()">Use LiveHeats<small>Load the event's draw (and schedule, if it has one) from LiveHeats</small></button>`}
      <button class="btn ${p.lh?"":"pri"}" onclick="openAdd()">Build our own program<small>${st.draw?"From the LiveHeats heats, or type heats in":"Type in the events, rounds and heats – no LiveHeats needed"}</small></button>
      ${(p.templates||[]).length?`<button class="btn" onclick="openTemplates()">Load a saved template<small>${esc(p.templates.join(", "))}</small></button>`:""}
      <button class="btn" onclick="progDo({mode:'off'},'No program – choose heats one at a time')">No program<small>Choose each heat by hand on the Race tab</small></button>
    </div></div>`;
  } else {
    const n=p.items.length, done=p.items.filter(x=>x.raced!=null).length;
    let s=`<div class="card"><h2>${p.mode==="on"?"Program on":"No program"}</h2>`;
    s+=p.mode==="on"?`<p style="margin:4px 0">${n} heats · ${done} raced · ${pg.left} to go after the current heat</p>`
      :`<p class="mute" style="margin:4px 0">Heats are chosen one at a time. ${n?"The program below is kept but not followed.":""}</p>`;
    if(pg.behind!=null&&Math.abs(pg.behind)>=2&&p.mode==="on") s+=`<p class="${pg.behind>0?"bad":"ok"}" style="margin:4px 0">Running ${Math.abs(pg.behind)} min ${pg.behind>0?"behind":"ahead of"} schedule</p>`;
    if(pg.warn) s+=`<div class="warn">Fewer than 2 heats left after this one – add more below, or turn the program off.</div>`;
    if(pg.lh_changed&&!off) s+=`<div class="warn">The LiveHeats schedule has changed since it was loaded.
      <div class="row"><button class="btn sm" onclick="progDo({import:true},'Program updated from LiveHeats')">Use the new LiveHeats order</button></div>
      <div class="log">Heats already raced stay at the top. Your own changes to the rest are replaced.</div></div>`;
    if(!off){
      s+=`<div class="row"><button class="btn pri" onclick="openAdd()">Add heats</button><button class="btn" onclick="openBreak()">Add break</button>
        <button class="btn" id="pmore" onclick="progMore=!progMore;lastKey='';render()">${progMore?"Less ▴":"More ▾"}</button></div>`;
      s+=`<div class="row" ${progMore?"":"hidden"}><button class="btn" onclick="openNextRound()">Next round</button>
        <button class="btn" onclick="openTimes()">Times</button><button class="btn" onclick="openTemplates()">Templates</button>
        ${(prog.items||[]).some(x=>x.manual)?`<button class="btn" onclick="openProgress()">Fill next round from results</button>`:""}`;
      if(p.lh) s+=`<button class="btn" onclick="askYes('Replace the program with the LiveHeats schedule? Heats already raced stay.',()=>progDo({import:true},'Program loaded from LiveHeats'),'Yes, replace',false)">Load LiveHeats schedule</button>`;
      s+=p.mode==="on"?`<button class="btn" onclick="progDo({mode:'off'},'Program off')">Turn program off</button>`
        :`<button class="btn" onclick="progDo({mode:'on'},'Program on')">Turn program on</button>`;
      if(n) s+=`<button class="btn" onclick="askYes('Remove every heat not yet raced from the program?',()=>progDo({clear:true,keep_done:true},'Program cleared'),'Yes, remove them')">Clear unraced</button>`;
      s+=`</div>`;
    }
    right+=s+`<p class="mute" style="margin:8px 0 0">Tap a heat to run it next, move it or remove it. Races follow this order by themselves.</p></div>`;
  }
  // --- the list ---
  if(p.items.length){
    left+=`<div class="card"><h2>Running order</h2>`;
    p.items.forEach((x,i)=>{
      if(x.brk){ left+=`<div class="prow brk" data-i="${i}"><span class="pn">${i+1}</span><div><div class="pl">${esc(x.label)}</div>
        <div class="ps">${x.est&&x.est.plan?x.est.plan+" · ":""}${x.until?"racing resumes "+esc(x.until):x.mins?x.mins+" min":""}</div></div><span class="chip done">break</span></div>`; return; }
      const tt=x.est?(x.est.exp&&x.est.exp!==x.est.plan&&x.raced==null?`<span class="tm2">${x.est.exp}</span> <span class="mute" style="text-decoration:line-through">${x.est.plan}</span> · `
        :x.est.plan?`<span class="tm2">${x.est.plan}</span> · `:""):"";
      const ck=x.checkin||{}, nin=Object.values(ck).filter(v=>v==="present").length, nout=Object.values(ck).filter(v=>v==="scratched").length;
      const chip=x.missing?`<span class="chip gone">not in draw</span>`:x.raced!=null?`<span class="chip done">✓ race ${x.raced}</span>`
        :x.now?`<span class="chip now">ON NOW</span>`:x.next===1?`<span class="chip next">NEXT</span>`:x.next===2?`<span class="chip next">THEN</span>`:"";
      left+=`<div class="prow ${x.raced!=null?"done":""} ${x.now?"now":""}" data-i="${i}"><span class="pn">${i+1}</span>
        <div><div class="pl">${x.missing?"Heat no longer in LiveHeats":esc(hl(x))}</div>
        <div class="ps">${tt||(x.time?hhmm(x.time)+" · ":"")}${x.crews?x.crews+" crews":x.manual?"no crew names":"not drawn yet"}${x.manual?" · added here":""}${nin||nout?` · ${nin} in${nout?", "+nout+" out":""}`:""}</div></div>${chip}</div>`;
    });
    left+=`</div>`;
  } else if(p.mode!=null) left+=`<div class="card"><h2>Running order</h2><p class="mute">No heats in the program yet.</p></div>`;
  $("program").innerHTML=`<div class="cols"><div>${left||right}</div><div>${left?right:""}</div></div>`;
  if(!off) document.querySelectorAll("#program .prow").forEach(r=>r.onclick=()=>progSheet(+r.dataset.i));
}
function progSheet(i){
  const x=prog.items[i], n=prog.items.length;
  if(x.brk){ $("sheetin").innerHTML=`<h2>${esc(x.label)}</h2><p class="mute">Position ${i+1} of ${n}</p><div class="row">
      <button class="btn" ${i?"":"disabled"} onclick="closeSheet();progDo({move:'${x.id}',to:${i-1}})">Move up</button>
      <button class="btn" ${i<n-1?"":"disabled"} onclick="closeSheet();progDo({move:'${x.id}',to:${i+1}})">Move down</button>
      <button class="btn red" onclick="closeSheet();progDo({remove:'${x.id}'},'Break removed')">Remove</button><button class="btn" onclick="closeSheet()">Close</button></div>`;
    $("sheet").classList.add("on"); return; }
  $("sheetin").innerHTML=`<h2>${x.missing?"Heat no longer in LiveHeats":esc(hl(x))}</h2>
    <p class="mute">Position ${i+1} of ${n}${x.raced!=null?" · raced as race "+x.raced:""}</p>
    ${x.manual&&x.raced==null?`<div class="row"><button class="btn" onclick="openCrews('${x.id}')">Crew names…</button>
      <button class="btn" onclick="closeSheet();progDo({delete:'${x.id}'},'Heat deleted')">Delete heat</button></div>`:""}
    <div class="row">${x.missing||x.raced!=null?"":`<button class="btn pri" onclick="closeSheet();post('/api/heat',{div:'${x.div_id}',heat:'${x.id}'}).then(()=>{loadProg();toast('Heat chosen for the next race')})">Run this heat now</button>
      <button class="btn" onclick="closeSheet();progDo({next_up:'${x.id}'},'Runs after the current heat')">Run it next</button>`}
      <button class="btn" ${i?"":"disabled"} onclick="closeSheet();progDo({move:'${x.id}',to:${i-1}})">Move up</button>
      <button class="btn" ${i<n-1?"":"disabled"} onclick="closeSheet();progDo({move:'${x.id}',to:${i+1}})">Move down</button></div>
    <div class="row"><input type="text" id="moveto" inputmode="numeric" placeholder="Move to position…" style="max-width:200px">
      <button class="btn" onclick="const v=parseInt($('moveto').value);if(v>0){closeSheet();progDo({move:'${x.id}',to:v-1})}">Move</button></div>
    <div class="row"><button class="btn red" onclick="closeSheet();progDo({remove:'${x.id}'},'Removed from the program')">Remove from program</button>
      <button class="btn" onclick="closeSheet()">Close</button></div>`;
  $("sheet").classList.add("on");
}
let addMode=null, typed={event:"",evname:"",age:"",agetext:"",gender:"",round:"Round 1",heats:"",alternate:false};
async function openAdd(){
  if(addMode==null) addMode=st.draw?"lh":"type";
  if(addMode==="type"||!st.draw) return openType();
  const d=await getDraw(); if(!d||!d.divisions) return;
  if(!addDiv) addDiv=(st.heat&&st.heat.div_id)||d.divisions[0].id;
  const dv=d.divisions.find(x=>x.id===addDiv)||d.divisions[0];
  const inProg=new Set((prog&&prog.items||[]).map(x=>x.id));
  const opts=(sel,none)=>(none?`<option value="">${none}</option>`:"")+d.divisions.map(x=>`<option value="${x.id}" ${x.id===sel?"selected":""}>${esc(x.name)}</option>`).join("");
  let h=`<h2>Add heats to the program</h2>${addTabs()}
    <div class="row" style="margin-top:0"><select id="adddiv" style="flex:1 1 260px">${opts(dv.id)}</select>
    <select id="altdiv" style="flex:1 1 260px"><option value="">Don't alternate</option>${d.divisions.filter(x=>x.id!==dv.id).map(x=>`<option value="${x.id}" ${x.id===altDiv?"selected":""}>Alternate with ${esc(x.name)}</option>`).join("")}</select></div>
    <p class="mute" style="margin:6px 0">${altDiv?"Whole rounds alternate heat by heat with the second division (gives crews a rest).":"Tap heats to pick them, or add a whole round. Pick a second division to alternate heats between two divisions."}</p>`;
  const rounds=[...new Set(dv.heats.map(x=>x.round))];
  for(const r of rounds){
    const hs=dv.heats.filter(x=>x.round===r);
    h+=`<div class="row" style="align-items:center;justify-content:space-between;margin-top:12px"><b>${esc(r)}</b>
      <button class="btn sm" onclick="addRound('${esc(r)}')">Add whole round${altDiv?" (alternating)":""}</button></div><div class="heatbtns">`;
    for(const x of hs){ const inn=inProg.has(x.id), pk=picked.includes(x.id);
      h+=`<button class="btn ${pk?"picked":""}" ${inn?"disabled":""} onclick="pickToggle('${x.id}')">Heat ${x.no}<small style="display:block;font-weight:500;font-size:12px">${inn?"in program":x.crews.length?x.crews.length+" crews":"not drawn yet"}</small></button>`; }
    h+=`</div>`;
  }
  h+=`<div class="row"><button class="btn pri" ${picked.length?"":"disabled"} onclick="addPicked()">Add ${picked.length||""} picked heat${picked.length===1?"":"s"}</button>
    <button class="btn" onclick="picked=[];closeSheet()">Close</button></div>`;
  $("sheetin").innerHTML=h; $("sheet").classList.add("on");
  $("adddiv").onchange=e=>{ addDiv=e.target.value; if(altDiv===addDiv) altDiv=""; openAdd(); };
  $("altdiv").onchange=e=>{ altDiv=e.target.value; openAdd(); };
}
function addTabs(){
  return st.draw?`<div class="row" style="margin:0 0 10px"><button class="btn sm ${addMode==="lh"?"pri":""}" onclick="addMode='lh';openAdd()">From LiveHeats</button>
    <button class="btn sm ${addMode==="type"?"pri":""}" onclick="addMode='type';openAdd()">Type in heats</button></div>`:"";
}
function typedDiv(T){
  // e.g. "Open Male", "Masters 40+ Female", "U19 Mixed"
  const age=T.age==="Masters"?("Masters "+T.agetext.trim()).trim():T.age==="Other"?T.agetext.trim():T.age;
  return (age+" "+T.gender).trim();
}
function chips(list,cur,set){ return list.map(v=>`<button class="btn sm ${cur===v?"pri":""}" onclick="${set}='${v}';openType()">${v}</button>`).join(""); }
function openType(){
  const T=typed, evs=st.events.filter(e=>e.legs);
  const ageBox=T.age==="Masters"||T.age==="Other";
  let h=`<h2>Add heats to the program</h2>${addTabs()}
    <div class="mute" style="margin-bottom:4px">Event</div><div class="row" style="margin-top:0">${evs.map(e=>`<button class="btn sm ${T.event===e.id?"pri":""}" onclick="typed.event='${e.id}';openType()">${esc(e.name)}</button>`).join("")}
      <button class="btn sm ${T.event==="other"?"pri":""}" onclick="typed.event='other';openType()">Other</button></div>
    ${T.event==="other"?`<input type="text" id="tevname" value="${esc(T.evname)}" placeholder="Event name, e.g. Board Rescue" oninput="typed.evname=this.value" style="margin-top:8px">
      <div class="log">Legs for an Other event are worked out from the presses.</div>`:""}
    <div class="mute" style="margin:10px 0 4px">Age group</div><div class="row" style="margin-top:0">${chips(["U19","U23","Open","Masters","Other"],T.age,"typed.age")}</div>
    ${ageBox?`<input type="text" id="tage" value="${esc(T.agetext)}" placeholder="${T.age==="Masters"?"Masters age group, e.g. 40+ or 30-39":"Age group, e.g. U17"}" oninput="typed.agetext=this.value" style="margin-top:8px">`:""}
    <div class="mute" style="margin:10px 0 4px">Male / Female / Mixed</div><div class="row" style="margin-top:0">${chips(["Male","Female","Mixed"],T.gender,"typed.gender")}</div>
    <div class="mute" style="margin:10px 0 4px">Round</div><div class="row" style="margin-top:0">${chips(["Round 1","Round 2","Quarter final","Semi final","Final"],T.round,"typed.round")}</div>
    <div class="mute" style="margin:10px 0 4px">Number of heats</div>
    <input type="text" id="theats" inputmode="numeric" value="${esc(T.heats)}" placeholder="e.g. 4" style="max-width:140px" oninput="typed.heats=this.value">
    <label style="display:flex;gap:8px;align-items:center;margin-top:10px;font-weight:600"><input type="checkbox" id="talt" ${T.alternate?"checked":""} onchange="typed.alternate=this.checked" style="width:22px;height:22px">
      Alternate with the heats I added last</label>
    <p style="margin:10px 0 0;font-weight:700" id="tprev"></p>
    <p class="bad" id="tmsg" style="margin:6px 0 0"></p>
    <div class="row"><button class="btn pri" id="tgo">Add heats</button><button class="btn" onclick="closeSheet()">Close</button></div>`;
  $("sheetin").innerHTML=h; $("sheet").classList.add("on");
  const evName=()=>T.event==="other"?T.evname.trim():((st.events.find(e=>e.id===T.event)||{}).name||"");
  const preview=()=>{ const d=typedDiv(T), n=parseInt(T.heats)||0, en=evName();
    $("tprev").textContent=d&&en?`Adds: ${d} ${en} · ${T.round}${n?" · "+n+" heat"+(n===1?"":"s"):""}`:""; };
  ["tevname","tage","theats"].forEach(id=>{ const el=$(id); if(el) el.addEventListener("input",preview); }); preview();
  $("tgo").onclick=async()=>{
    // read what's on screen now
    if($("tevname")) T.evname=$("tevname").value; if($("tage")) T.agetext=$("tage").value;
    T.heats=$("theats").value.trim(); T.alternate=$("talt").checked;
    const miss=!T.event?"Choose the event":T.event==="other"&&!T.evname.trim()?"Type the event name":!T.age?"Choose the age group"
      :(T.age==="Other"&&!T.agetext.trim())?"Type the age group":!T.gender?"Choose Male, Female or Mixed":!(parseInt(T.heats)>0)?"Enter the number of heats":"";
    if(miss){ $("tmsg").textContent=miss; return; }
    $("tgo").disabled=true;
    const r=await (await fetch("/api/program",{method:"POST",headers:{"Content-Type":"application/json"},
      body:JSON.stringify({who:myName(),create:{event:T.event,event_name:T.evname,div:typedDiv(T),round:T.round,heats:T.heats,alternate:T.alternate}})})).json();
    if(r.result!=="ok"){ $("tmsg").textContent=r.result; $("tgo").disabled=false; return; }
    toast(`${T.heats} heat${T.heats==1?"":"s"} added: ${typedDiv(T)} ${evName()} · ${T.round}`);
    typed.heats=""; typed.alternate=false; drawData=null; await loadProg(); lastKey=""; render(); openType();
  };
}
function openCrews(id){
  const x=prog.items.find(i=>i.id===id); if(!x) return;
  getDraw().then(d=>{
    let h0=null; for(const dv of d.divisions) for(const hh of dv.heats) if(hh.id===id) h0=hh;
    const cur={}; (h0&&h0.crews||[]).forEach(([l,n])=>cur[l]=n);
    const n=Math.max(10,...st.lanes);
    let h=`<h2>Crew names – ${esc(hl(x))}</h2><p class="mute">Optional. Leave a lane empty if no crew is in it.</p><div style="display:grid;gap:6px">`;
    for(let l=1;l<=n;l++) h+=`<div class="row" style="margin:0;align-items:center;flex-wrap:nowrap"><b style="width:4.2em;flex:none">Lane ${l}</b>
      <input type="text" id="cn${l}" value="${esc(cur[l]||"")}" placeholder="Club or crew name"></div>`;
    h+=`</div><details style="border:0;padding:8px 0 0"><summary>Paste a list</summary><p class="mute" style="margin:6px 0">One crew per line, in lane order (lane 1 first). Blank lines leave a lane empty.</p>
      <textarea id="cnpaste" placeholder="Kurrawa Team A&#10;Noosa Heads Blue&#10;…"></textarea>
      <div class="row"><button class="btn" id="cnfill">Fill lanes from list</button></div></details>
      <div class="row"><button class="btn pri" id="cngo">Save names</button><button class="btn" onclick="closeSheet()">Cancel</button></div>`;
    $("sheetin").innerHTML=h; $("sheet").classList.add("on");
    $("cnfill").onclick=()=>{ const lines=$("cnpaste").value.replace(/\r/g,"").split("\n");
      while(lines.length&&!lines[lines.length-1].trim()) lines.pop();
      for(let l=1;l<=n;l++) $("cn"+l).value=(lines[l-1]||"").replace(/^\s*\d+[.)\-:]?\s+/,"").trim();
      toast("Lanes filled – check them, then Save names"); };
    $("cngo").onclick=async()=>{ const c={}; for(let l=1;l<=n;l++){ const v=$("cn"+l).value.trim(); if(v) c[l]=v; }
      closeSheet(); drawData=null; await progDo({crews:{heat:id,crews:c}},"Crew names saved"); };
  });
}
function sheet(h){ $("sheetin").innerHTML=h; $("sheet").classList.add("on"); }
async function progMsg(data,okText){
  try{ const j=await (await fetch("/api/program",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify(Object.assign({who:myName()},data))})).json();
    await loadProg(); drawData=null; lastKey=""; render();
    if(j.result==="ok"||j.result.startsWith("ok:")){ toast(j.result.startsWith("ok:")?j.result.slice(3):okText); return true; }
    toast(j.result); return false; }catch(e){ toast("No link to the timing computer"); return false; }
}
let nrRound="Final";
function openNextRound(){
  sheet(`<h2>Add the next round</h2><p class="mute">Adds the next round for the divisions you added last, alternating the same way.
    LiveHeats divisions use their next round from the draw. For heats added here, choose the round and number of heats per division.</p>
    <div class="row" style="margin-top:0">${["Round 2","Quarter final","Semi final","Final"].map(r=>`<button class="btn sm ${nrRound===r?"pri":""}" onclick="nrRound='${r}';openNextRound()">${r}</button>`).join("")}</div>
    <div class="mute" style="margin:10px 0 4px">Heats per division</div><input type="text" id="nrn" inputmode="numeric" value="1" style="max-width:120px">
    <div class="row"><button class="btn pri" onclick="progMsg({next_round:{round:nrRound,heats:$('nrn').value}},'Next round added').then(ok=>{if(ok)closeSheet()})">Add next round</button>
    <button class="btn" onclick="closeSheet()">Close</button></div>`);
}
let brLabel="Lunch";
function openBreak(){
  sheet(`<h2>Add a break</h2><div class="row" style="margin-top:0">${["Lunch","Break","Presentation","Other"].map(r=>`<button class="btn sm ${brLabel===r?"pri":""}" onclick="brLabel='${r}';openBreak()">${r}</button>`).join("")}</div>
    ${brLabel==="Other"?`<input type="text" id="brname" placeholder="e.g. Rescue demo" style="margin-top:8px">`:""}
    <div class="row"><div><div class="mute">Racing resumes at</div><input type="text" id="bruntil" placeholder="12:30" style="max-width:120px"></div>
      <div><div class="mute">or minutes</div><input type="text" id="brmins" inputmode="numeric" placeholder="30" style="max-width:120px"></div></div>
    <div class="row"><button class="btn pri" onclick="addBreak(true)">Add after the current heat</button><button class="btn" onclick="addBreak(false)">Add at the end</button>
    <button class="btn" onclick="closeSheet()">Close</button></div>`);
}
function addBreak(after){ const label=brLabel==="Other"?($("brname").value.trim()||"Break"):brLabel;
  progMsg({add_break:{label:label,until:$("bruntil").value.trim(),mins:$("brmins").value.trim(),after_current:after}},label+" added").then(ok=>{if(ok)closeSheet()}); }
function openTimes(){
  const tm=prog.timing||{};
  sheet(`<h2>Times</h2><p class="mute">Gives every heat an expected time and shows when racing is behind. LiveHeats heat times are used where they exist.</p>
    <div class="row"><div><div class="mute">First heat at</div><input type="text" id="tmstart" value="${esc(tm.start||"")}" placeholder="09:00" style="max-width:120px"></div>
      <div><div class="mute">Minutes per heat</div><input type="text" id="tmmins" inputmode="numeric" value="${esc(tm.mins||4)}" style="max-width:120px"></div></div>
    <div class="row"><button class="btn pri" onclick="progMsg({timing:{start:$('tmstart').value.trim(),mins:$('tmmins').value.trim()}},'Times saved').then(ok=>{if(ok)closeSheet()})">Save</button>
    <button class="btn" onclick="progMsg({timing:{start:'',mins:$('tmmins').value.trim()||4}},'Times cleared').then(ok=>{if(ok)closeSheet()})">Clear start time</button>
    <button class="btn" onclick="closeSheet()">Close</button></div>`);
}
async function openTemplates(){
  if(!prog) await loadProg();
  const list=prog.templates||[];
  sheet(`<h2>Templates</h2><p class="mute">Save today's program to reuse – heats, breaks and times. Loading keeps heats already raced at the top.</p>
    ${list.length?list.map(n=>`<div class="row" style="align-items:center;justify-content:space-between"><b>${esc(n)}</b><span style="display:flex;gap:8px">
      <button class="btn sm pri" onclick="askYes('Replace the program with ${esc(n).replace(/'/g,"")}?',()=>progTpl({load:true,name:'${esc(n).replace(/'/g,"")}'},'Template loaded'),'Yes, load it',false)">Load</button>
      <button class="btn sm" onclick="askYes('Delete this template?',()=>progTpl({delete:true,name:'${esc(n).replace(/'/g,"")}'},'Template deleted'),'Yes, delete')">Delete</button></span></div>`).join(""):`<p class="mute">No templates saved yet.</p>`}
    ${(prog.items||[]).length?`<div class="row"><input type="text" id="tplname" placeholder="Name, e.g. Club carnival" style="flex:1 1 200px">
      <button class="btn" onclick="progTpl({save:true,name:$('tplname').value},'Template saved')">Save this program</button></div>`:""}
    <div class="row"><button class="btn" onclick="closeSheet()">Close</button></div>`);
}
async function progTpl(data,okText){
  try{ const j=await (await fetch("/api/template",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify(Object.assign({who:myName()},data))})).json();
    if(j.result!=="ok"){ toast(j.result); return; } toast(okText); closeSheet(); await loadProg(); drawData=null; lastKey=""; render(); }catch(e){ toast("No link to the timing computer"); }
}
let pgDiv=null;
async function openProgress(){
  const d=await getDraw(); if(!d) return;
  const divs=d.divisions.filter(x=>x.manual); if(!divs.length) return;
  if(!pgDiv||!divs.find(x=>x.id===pgDiv)) pgDiv=divs[0].id;
  const dv=divs.find(x=>x.id===pgDiv), rounds=[...new Set(dv.heats.map(h=>h.round))];
  const sel=(id,list,v)=>`<select id="${id}">${list.map(x=>`<option ${x===v?"selected":""}>${esc(x)}</option>`).join("")}</select>`;
  sheet(`<h2>Fill next round from results</h2><p class="mute">For heats added here. Takes the top crews from each heat, then the fastest of the rest,
    and seeds them across the next round's heats (best first, centre lanes first). It's a draft – check it against the Surf Sports Manual before racing.</p>
    <div class="mute">Division</div><select id="pgdiv" onchange="pgDiv=this.value;openProgress()">${divs.map(x=>`<option value="${x.id}" ${x.id===pgDiv?"selected":""}>${esc(x.name)}</option>`).join("")}</select>
    <div class="row"><div style="flex:1 1 140px"><div class="mute">From</div>${sel("pgfrom",rounds,rounds[0])}</div><div style="flex:1 1 140px"><div class="mute">Into</div>${sel("pgto",rounds,rounds[1]||rounds[0])}</div></div>
    <div class="row"><div><div class="mute">Top from each heat</div><input type="text" id="pgtop" inputmode="numeric" value="2" style="max-width:110px"></div>
      <div><div class="mute">Plus fastest others</div><input type="text" id="pgfast" inputmode="numeric" value="0" style="max-width:110px"></div>
      <div><div class="mute">Crews per heat</div><input type="text" id="pgper" inputmode="numeric" value="9" style="max-width:110px"></div></div>
    ${rounds.length<2?`<p class="warn">Add the next round's heats for this division first (Add heats or Next round).</p>`:""}
    <div class="row"><button class="btn pri" onclick="progMsg({progress:{div:pgDiv,from:$('pgfrom').value,to:$('pgto').value,top:$('pgtop').value,fastest:$('pgfast').value,per:$('pgper').value}},'Done').then(ok=>{if(ok)closeSheet()})">Fill lanes</button>
    <button class="btn" onclick="closeSheet()">Close</button></div>`);
}
function pickToggle(id){ picked=picked.includes(id)?picked.filter(x=>x!==id):picked.concat([id]); openAdd(); }
async function addPicked(){ const ids=picked; picked=[]; closeSheet(); await progDo({add:true,ids:ids},ids.length+" heat"+(ids.length===1?"":"s")+" added"); }
async function addRound(r){
  const d=drawData, dv=d.divisions.find(x=>x.id===addDiv), a=dv.heats.filter(x=>x.round===r).map(x=>x.id);
  let ids=a;
  if(altDiv){ const dv2=d.divisions.find(x=>x.id===altDiv);
    // same round of the second division (by name, else by position)
    const rounds2=[...new Set(dv2.heats.map(x=>x.round))], ri=[...new Set(dv.heats.map(x=>x.round))].indexOf(r);
    const r2=rounds2.includes(r)?r:rounds2[ri];
    const b=r2?dv2.heats.filter(x=>x.round===r2).map(x=>x.id):[];
    ids=[]; for(let i=0;i<Math.max(a.length,b.length);i++){ if(a[i]) ids.push(a[i]); if(b[i]) ids.push(b[i]); } }
  closeSheet(); await progDo({add:true,ids:ids},ids.length+" heats added");
}
// ---------- Marshal: next heats, tick crews present or scratched ----------
let mUp=null, mAt=0;
async function loadMarshal(){ try{ mUp=await (await fetch("/api/upcoming")).json(); mAt=Date.now(); }catch(e){} }
let mSel=null, mScrolled=null, mPicked=false;
async function mark(hid,lane,status){
  // show it straight away (phones on beach Wi-Fi can be slow), then save
  const ck=mUp.checkin[hid]=mUp.checkin[hid]||{}; if(status) ck[String(lane)]=status; else delete ck[String(lane)];
  lastKey=""; render(); if(navigator.vibrate) try{ navigator.vibrate(20); }catch(e){}
  await post("/api/marshal",{heat:hid,lane:lane,status:status});
  await loadMarshal(); lastKey=""; render(); }
async function mReq(n){ mUp.required=n; lastKey=""; render(); await post("/api/marshal",{required:n}); await loadMarshal(); lastKey=""; render(); }
async function doSend(hid,on){ mUp.sent=mUp.sent||{}; if(on) mUp.sent[hid]={at:"now",missing:[]}; else delete mUp.sent[hid]; lastKey=""; render();
  await post("/api/marshal",{heat:hid,sent:on}); await loadMarshal(); lastKey=""; render();
  if(on){ mPicked=false; const nx=mUp.heats.find(x=>!(mUp.sent||{})[x.heat_id]); if(nx){ mSel=nx.heat_id; lastKey=""; render(); }
    window.scrollTo({top:0,behavior:"smooth"}); document.scrollingElement&&(document.scrollingElement.scrollTop=0); const mn=document.querySelector("main"); if(mn) mn.scrollTop=0;      // back to the top, ready for the next heat
    showUndo("Patients sent",null,()=>doSend(hid,false)); } }
function sendPatients(hid,on){
  if(!on){ doSend(hid,false); return; }
  const ht=mUp.heats.find(x=>x.heat_id===hid), ck=mUp.checkin[hid]||{}, miss=mLanes(ht).filter(([l])=>!ck[l]).map(([l])=>l);
  if(!miss.length){ doSend(hid,true); return; }
  $("sheetin").innerHTML=`<h2>Send anyway?</h2><p>Not checked in: <b>lane ${miss.join(", ")}</b>.</p><p class="mute">Those lanes will be flagged on the Starter's screen.</p>
    <div class="row"><button class="btn pri" id="sendgo">Yes, patients sent</button><button class="btn" onclick="closeSheet()">Cancel</button></div>`;
  $("sheet").classList.add("on"); $("sendgo").onclick=()=>{ closeSheet(); doSend(hid,true); }; }
// people in a crew (from LiveHeats): patients for marshalling, everyone for team managers
function crewMembers(ht,l){ const crew=((ht&&ht.crews)||{})[String(l)]||"", fx=(st&&st.role_fix)||{};
  return (((ht&&ht.members)||{})[String(l)]||[]).map(x=>[x[0],x[1]||fx[(crew+"|"+x[0]).toLowerCase()]||""]); }
function pats(ht,l){ const m=crewMembers(ht,l); const p=m.filter(x=>x[1]==="Patient"), u=m.filter(x=>!x[1]);
  return p.map(x=>x[0]).concat(u.map(x=>x[0]+" (role not set)")); }
// a crew member with no role in LiveHeats: the team manager picks one (suggested from what's missing)
function roleFixer(ht,l){
  const m=crewMembers(ht,l), crew=(ht.crews||{})[String(l)]||"", miss=m.filter(x=>!x[1]); if(!miss.length) return "";
  const have=r=>m.filter(x=>x[1]===r).length, need=have("Driver")<1?"Driver":have("Crew")<1?"Crew":"Patient";
  const q=s=>esc(s).replace(/'/g,"&#39;").replace(/\\/g,"");
  return `<div class="rolefix"><b>Role not set in LiveHeats</b> – choose for the marshal:${miss.map(x=>`<div class="rfrow"><span>${esc(x[0])}</span>
    ${["Driver","Crew","Patient"].map(r=>`<button class="btn sm ${r===need?"pri":""}" onclick="setRole(this,'${q(crew)}','${q(x[0])}','${r}')">${r}</button>`).join("")}</div>`).join("")}
    <div class="mute" style="font-size:13px;margin-top:4px">Saved for today's timing only – please also fix it in LiveHeats.</div></div>`;
}
async function setRole(btn,crew,person,role){
  const tx=s=>{ const d=document.createElement("textarea"); d.innerHTML=s; return d.value; };
  await post("/api/role",{crew:tx(crew),person:tx(person),role:role}); if(st){ st.role_fix=st.role_fix||{}; st.role_fix[(tx(crew)+"|"+tx(person)).toLowerCase()]=role; }
  toast(tx(person)+" set as "+role); lastKey=""; render(); }
function crewPeople(ht,l){ const m=crewMembers(ht,l); if(!m.length) return "";
  const by=r=>m.filter(x=>x[1]===r).map(x=>esc(x[0])), parts=[];
  if(by("Driver").length) parts.push("<b>Driver</b> "+by("Driver").join(", "));
  if(by("Crew").length) parts.push("<b>Crew</b> "+by("Crew").join(", "));
  if(by("Patient").length) parts.push("<b>Patient"+(by("Patient").length>1?"s":"")+"</b> "+by("Patient").join(", "));
  const other=m.filter(x=>!["Driver","Crew","Patient"].includes(x[1])).map(x=>esc(x[0])+(x[1]?" ("+esc(x[1])+")":" (role not set)"));
  if(other.length) parts.push(other.join(", "));
  return parts.join(" · "); }
function shortName(n){ const role=n.endsWith(" (role not set)")?" (?)":""; n=n.replace(" (role not set)","");
  const p=n.trim().split(/\s+/); return (p.length>1?p[0]+" "+p[p.length-1][0]:p[0])+role; }
function mLanes(ht){ const crews=Object.entries(ht.crews||{}).sort((a,b)=>a[0]-b[0]); return crews.length?crews:st.lanes.map(l=>[String(l),""]); }
function renderMarshal(){
  if(!mUp){ $("marshal").innerHTML=`<div class="card mute">Loading…</div>`; return; }
  const can=st.role==="marshal"||st.official;
  if(!mUp.heats.length){ $("marshal").innerHTML=`<div class="card"><h2>Marshalling</h2><p class="mute">No heats coming up yet. Heats show here once the program is set up.</p>
    ${st.official?`<div class="row"><button class="btn pri" onclick="goTab('program')">Set up the program</button></div>`:""}</div>`; return; }
  const sentOf=id=>(mUp.sent||{})[id];
  if(!mPicked||!mUp.heats.some(x=>x.heat_id===mSel)) mSel=(mUp.heats.find(x=>!sentOf(x.heat_id))||mUp.heats[0]).heat_id;   // open on the first heat whose patients haven't gone
  const onStart=(st.heat||{}).heat_id;
  // heat picker: one heat on screen at a time
  let h=`<div class="mpick">${mUp.heats.map((ht,i)=>{ if(false) return ""; const ck=mUp.checkin[ht.heat_id]||{}, ln=mLanes(ht), n=ln.filter(([l])=>ck[l]).length;
    return `<button class="${ht.heat_id===mSel?"on":""} ${n===ln.length||sentOf(ht.heat_id)?"done":""}" onclick="mSel='${ht.heat_id}';mPicked=true;lastKey='';render()">
      <small>${ht.heat_id===onStart?"On the start":i===0||(i===1&&mUp.heats[0].heat_id===onStart)?"Next":"Then"}</small>Heat ${ht.no}<small class="mpd">${esc(ht.div)}</small><b>${sentOf(ht.heat_id)?"Sent ✓":n+"/"+ln.length}</b></button>`; }).join("")}</div>`;
  const ht=mUp.heats.find(x=>x.heat_id===mSel), ck=mUp.checkin[ht.heat_id]||{}, lanes=mLanes(ht);
  const inn=lanes.filter(([l])=>ck[l]==="present").length, out=lanes.filter(([l])=>ck[l]==="scratched").length, left=lanes.length-inn-out;
  const tm=mUp.times[ht.heat_id]||{}, when=tm.exp||tm.plan;
  h+=`<div class="card mcard"><div class="mhead"><div><div class="mdiv">${esc(ht.div)}</div><div class="mmeta">${esc(ht.round)} · Heat ${ht.no}${when?" · "+when:""}</div></div>
    ${sentOf(ht.heat_id)?`<div class="mcount sent">Sent ${esc(sentOf(ht.heat_id).at)}</div>`:`<div class="mcount ${left?"":"all"}">${left?left+" to come":"All here"}</div>`}</div>
    <div class="mbar"><i style="width:${100*inn/lanes.length}%"></i><i class="x" style="width:${100*out/lanes.length}%"></i></div>
    <div class="mmeta" style="margin:4px 0 6px">${inn} in${out?" · "+out+" scratched":""}${can?" · tap a crew when they arrive":""}</div>`;
  h+=`<div class="mlanes" style="--mr:${Math.ceil(lanes.length/2)}">`;
  for(const [l,c] of lanes){ const s=ck[l]||"";
    h+=`<div class="mlane ${s}"><button class="mtap" ${can?`onclick="mark('${ht.heat_id}',${l},'${s==="present"?"":"present"}')"`:"disabled"}>
        <span class="mno">${l}</span><span class="mnm"><span class="nmx">${esc(c||"Lane "+l)}</span>${pats(ht,l).length?`<span class="mpat">${esc(pats(ht,l).join(" · "))}</span>`:""}${s==="scratched"?`<small>SCRATCHED</small>`:""}</span>
        <span class="mtick">${s==="present"?"✓":""}</span></button>
      ${can?`<button class="mscr" aria-label="${s==="scratched"?"Undo scratch":"Scratch lane "+l}" onclick="mark('${ht.heat_id}',${l},'${s==="scratched"?"":"scratched"}')">${s==="scratched"?"Undo":"✕<small>Scratch</small>"}</button>`:""}</div>`; }
  h+=`</div>`;
  const sd=sentOf(ht.heat_id);
  if(can) h+=sd?`<div class="msent"><b>✓ Patients sent at ${esc(sd.at)}</b>${sd.missing&&sd.missing.length?`<span>Not checked in: lane ${sd.missing.join(", ")}</span>`:""}
      <button class="btn sm" onclick="sendPatients('${ht.heat_id}',false)">Undo</button></div>`
    :`<button class="btn pri msend" onclick="sendPatients('${ht.heat_id}',true)">Patients sent ›</button>`;
  h+=`</div><p class="mute mhelp" style="margin:8px 4px">Tap a crew again to undo. Press <b>Patients sent</b> when the heat's patients go out on the water – the heat then shows as closed on the marshalling screen.</p>`;
  if(can) h+=`<div class="row" style="margin:4px;align-items:center"><span class="mute">Heats of patients seated in marshalling:</span>
    ${[2,3].map(n=>`<button class="btn sm ${(mUp.required||2)===n?"pri":""}" onclick="mReq(${n})">${n}</button>`).join("")}</div>`;
  const old=document.querySelector(".mpick"), oldX=old?old.scrollLeft:0;
  $("marshal").innerHTML=`<div class="mwrap">${h}</div>`;
  const b=document.querySelector(".mpick .on"), p=document.querySelector(".mpick");
  if(b&&p){ if(mScrolled!==mSel){ mScrolled=mSel; p.scrollLeft=b.offsetLeft-p.offsetLeft-(p.clientWidth-b.clientWidth)/2; } else p.scrollLeft=oldX; }
}

// ---------- Marshalling screen (#marshalling): for a TV or tablet where crews report ----------
function mbLanes(ht,big){
  const ck=(mUp.checkin||{})[ht.heat_id]||{}, ln=mLanes(ht);
  return `<div class="mbl">${ln.map(([l,c])=>{ const s=ck[l]||"";
    return `<b class="${s==="present"?"st-in":s==="scratched"?"st-out":""}">${l}</b><span class="${s==="scratched"?"":""}"${s==="scratched"?' style="text-decoration:line-through;color:#6b2226"':""}>${esc(c||"Lane "+l)}${big&&pats(ht,l).length?`<em class="mbp"> – ${esc(pats(ht,l).map(shortName).join(", "))}</em>`:""}</span>
      <i class="${s==="present"?"st-in":s==="scratched"?"st-out":"st-none"}">${s==="present"?"✓ HERE":s==="scratched"?"SCRATCHED":""}</i>`; }).join("")}</div>`;
}
function mbSmall(ht){
  const ck=(mUp.checkin||{})[ht.heat_id]||{};
  return `<div class="mbs">${mLanes(ht).map(([l,c])=>{ const s=ck[l]||""; return `<div class="${s}"><b>${l}</b><span>${esc(c||"Lane "+l)}</span>${s==="present"?"<i>✓</i>":s==="scratched"?"<i>✗</i>":""}</div>`; }).join("")}</div>`;
}
function renderMBoard(){
  if(!mUp){ $("race").innerHTML=`<p class="mute">Loading…</p>`; return; }
  const hs=mUp.heats||[], R=mUp.required||2, sentOf=id=>(mUp.sent||{})[id];
  const onId=(st&&(st.state==="RACING"?st.race_heat:st.heat)||{}).heat_id, onStart=hs.find(x=>x.heat_id===onId), rest=hs.filter(x=>x.heat_id!==onId);
  const tm=id=>{ const x=(mUp.times||{})[id]||{}; return x.exp||x.plan||""; };
  const now=new Date(), clk=String(now.getHours()).padStart(2,"0")+":"+String(now.getMinutes()).padStart(2,"0");
  const lab=x=>`Heat ${x.no} <small>· ${esc(x.div)} · ${esc(x.round)}${tm(x.heat_id)?" · "+tm(x.heat_id):""}</small>`;
  const small=(x,tag,cls)=>`<div class="mbrow"><span class="tg ${cls}">${tag}</span><span class="lab">${lab(x)}</span></div>`;
  let rows="";
  if(onStart) rows+=small(onStart,st.state==="RACING"?"RACING":"ABOUT TO RACE","race")+(sentOf(onStart.heat_id)?"":`<div class="mbrow" style="border-color:var(--red);color:var(--red)">Patients for this heat have not been marked as sent</div>`);
  let req=0, nxt=0, big=0;
  rest.forEach((x,k)=>{
    if(req>=R&&nxt>=1) return;
    if(big>=3&&!sentOf(x.heat_id)){ if(nxt<1){ nxt++; rows+=small(x,"NEXT","next"); } req=R; return; }
    if(sentOf(x.heat_id)){ if(req===0) rows+=small(x,"CLOSED","closed"); else if(nxt<1){ rows+=small(x,"CLOSED","closed"); } return; }
    if(k<2||req<R){ const late=k<2, ck=(mUp.checkin||{})[x.heat_id]||{}, left=mLanes(x).filter(([l])=>!ck[l]).length; if(!late) req++; big++;
      rows+=`<div class="mbbig ${late?"late":""}"><div class="hd"><span class="tg ${late?"now":"req"}">${late?"SEND NOW":"REQUIRED"}</span><span>Heat ${x.no} · ${esc(x.div)}</span></div>
        <div class="mbm">${esc(x.round)}${tm(x.heat_id)?" · "+tm(x.heat_id):""} · ${left?left+" still to report":"all patients here"}</div>${mbLanes(x,true)}</div>`; return; }
    if(nxt<1){ nxt++; rows+=small(x,"NEXT","next"); }
  });
  if(!hs.length) rows=`<div class="mbbig"><div class="hd">No heats coming up yet</div></div>`;
  let h=`<div class="mb ${big>=3?"tight":""}"><div class="mbtop"><span class="mbb">${st&&st.brand&&st.brand.logo?`<img src="/logo?v=${st.brand.logo}" alt="">`:""}${st&&st.brand&&st.brand.club?esc(st.brand.club)+" · ":""}Marshalling – patients</span><span class="mbclock">${clk}</span></div>`;
  if(st&&st.next_break) h+=`<div class="mbbreak">Next: ${esc(st.next_break.label)}${st.next_break.until?" – racing resumes "+esc(st.next_break.until):st.next_break.mins?" – "+st.next_break.mins+" minutes":""}</div>`;
  h+=`<div class="mbgrid"><div class="mbrows">${rows}</div><div class="mbaside"><div class="mbnote">Patients: report to marshalling 5 races before your heat.</div>${boardQr().replace('class="bqr"','class="bqr inl"')}</div></div></div>`;
  $("race").innerHTML=h+homeBtn();
}

// ---------- Team Manager (#team): one club's heats and results, no PIN ----------
let tmData=null, tmAt=0, tmClubs=[];
function tmClub(){ try{ return localStorage.getItem("irb_club")||""; }catch(e){ return ""; } }
async function loadTeam(){ try{ if(!tmClubs.length) tmClubs=await (await fetch("/api/clubs")).json();
  const c=tmClub(); tmData=c?await (await fetch("/api/team?club="+encodeURIComponent(c))).json():null; tmAt=Date.now(); }catch(e){} }
let tmView="club";
function tmTabs(){ return `<div class="row" style="margin:0 0 4px">${[["club","My club"],["program","Program"],["results","All results"]].map(([k,n])=>
  `<button class="btn ${tmView===k?"pri":""}" onclick="tmView='${k}';tmAt=0;histAt=0;progAt=0;lastKey='';render();poke()">${n}</button>`).join("")}</div>`; }
function poke(){ if(tmView==="program") loadProg().then(()=>{lastKey="";render()}); else if(tmView==="results") loadHist().then(()=>{lastKey="";render()}); else loadTeam().then(()=>{lastKey="";render()}); }
function homeBtn(){ return st&&st.role==="viewer"&&!st.local?`<button class="btn homebtn" onclick="location.hash='';lastKey='';render()">‹ Home</button>`:""; }
function renderTeamProgram(){
  let h=`<div class="card" style="margin:0"><h2>Program</h2>`;
  const p=prog; if(!p||p.mode!=="on"||!(p.items||[]).length) return h+`<p class="mute">No program yet – heats are called one at a time.</p></div>`;
  for(const x of p.items){
    if(x.brk){ h+=`<div class="prow brk" style="cursor:default"><span class="tm2">${x.est&&x.est.plan||""}</span><div><div class="pl">${esc(x.label)}</div><div class="ps">${x.until?"racing resumes "+esc(x.until):x.mins?x.mins+" min":""}</div></div></div>`; continue; }
    const tm=x.est?(x.est.exp||x.est.plan):(x.time?hhmm(x.time):"");
    h+=`<div class="prow ${x.now?"now":""}" style="cursor:default"><span class="tm2">${tm||""}</span><div><div class="pl">${esc(x.label)}</div>
      <div class="ps">${x.crews?x.crews+" crews":"not drawn yet"}</div></div>${x.raced!=null?`<span class="chip done">raced</span>`:x.now?`<span class="chip now">ON NOW</span>`:""}</div>`; }
  return h+`</div>`;
}
function renderTeamResults(){
  let h=`<div class="card" style="margin:0"><h2>All results</h2>`;
  if(!(hist||[]).length) return h+`<p class="mute">No results yet.</p></div>`;
  for(const r of hist){ const pl=r.rows.filter(x=>x.place).sort((a,b)=>a.place-b.place), out=r.rows.filter(x=>!x.place&&x.status);
    h+=`<div style="padding:10px 0;border-bottom:1px solid var(--line)"><div style="display:flex;justify-content:space-between;gap:8px"><b>${esc(r.heat&&r.heat.div?heatLabel(r.heat):"Race "+r.race)}</b>
      <span class="chip ${(r.flags||{}).confirmed?"now":"next"}">${(r.flags||{}).confirmed?"Final":"Provisional"}</span></div>
      ${pl.map(x=>`<div style="display:flex;gap:10px"><span class="pn">${((r.ties||[]).includes(x.lane)?"=":"")+x.place}</span><span style="flex:1">${esc(crewOf(r.heat,x.lane)||"Lane "+x.lane)}</span><span class="tm2">${ft(x.t_us)}</span></div>`).join("")}
      ${out.length?`<div class="mute">${out.map(x=>esc(crewOf(r.heat,x.lane)||"Lane "+x.lane)+" "+x.status).join(" · ")}</div>`:""}</div>`; }
  return h+`</div>`;
}
function renderTeam(){
  const c=tmClub();
  if(tmView!=="club"){ $("race").innerHTML=`<div class="tmv">${brandBar()}${tmTabs()}${tmView==="program"?renderTeamProgram():renderTeamResults()}</div>${homeBtn()}`; return; }
  const typeIt=`<div class="row" style="margin-top:0"><input type="text" id="tmclub" list="tmlist" value="${esc(c)}" placeholder="Your club, e.g. Kurrawa" style="flex:1 1 220px">
    <datalist id="tmlist">${tmClubs.map(x=>`<option value="${esc(x)}">`).join("")}</datalist>
    <button class="btn pri" onclick="try{localStorage.setItem('irb_club',$('tmclub').value.trim())}catch(e){};tmAt=0;loadTeam().then(()=>{lastKey='';render()})">Show</button></div>`;
  let h=`<div class="tmv">${brandBar()}${tmTabs()}<div class="card" style="margin:0">${c&&tmClubs.length?`<div class="row" style="margin:0;align-items:center;justify-content:space-between"><h2 style="margin:0">${esc(c)}</h2>
    <button class="btn sm" onclick="try{localStorage.removeItem('irb_club')}catch(e){};tmData=null;lastKey='';render()">Change club</button></div>`
    :`<h2>Team Manager</h2>${tmClubs.length?"":typeIt}`}</div>`;
  const pick=x=>`try{localStorage.setItem('irb_club','${esc(x).replace(/'/g,"")}')}catch(e){};tmAt=0;tmData=null;loadTeam().then(()=>{lastKey='';render()})`;
  if(!c||!tmData){ if(tmClubs.length&&!c) h+=`<div class="card" style="margin:0"><h2>Tap your club</h2><div class="row" style="margin-top:0">${tmClubs.map(x=>
      `<button class="btn" onclick="${pick(x)}">${esc(x)}</button>`).join("")}</div></div>`; }
  if(!c){ $("race").innerHTML=h+`<p class="mute">Choose your club to see your crews' heats, lanes and results.</p></div>`+homeBtn(); return; }
  if(!tmData){ $("race").innerHTML=h+`<p class="mute">Loading…</p></div>`+homeBtn(); return; }
  h+=`<div class="card" style="margin:0"><h2>Coming up for ${esc(c)}</h2>`;
  if(!tmData.upcoming.length) h+=`<p class="mute">No heats coming up.</p>`;
  for(const u of tmData.upcoming) h+=`<div class="prow ${u.now?"now":""}" style="cursor:default"><span class="tm2">${u.time||""}</span>
    <div><div class="pl">${esc(u.crew)} – Lane ${u.lane}</div><div class="ps">${esc(heatLabel(u.heat))}${u.check==="present"?" · ✓ checked in":u.check==="scratched"?" · SCRATCHED":""}</div>
    ${crewPeople(u.heat,u.lane)?`<div class="ps tmppl">${crewPeople(u.heat,u.lane)}</div>`:""}${roleFixer(u.heat,u.lane)}
    ${u.patients?`<div class="ps" style="font-weight:800;color:${u.patients==="now"?"var(--red)":u.patients==="sent"?"var(--green)":"var(--ink)"}">Patients: ${u.patients==="now"?"report to marshalling now":u.patients==="sent"?"sent out":"report by "+esc(u.patients)}</div>`:""}</div>
    ${u.now?`<span class="chip now">ON NOW</span>`:u.away===1?`<span class="chip next">NEXT</span>`:u.away>1?`<span class="chip done">in ${u.away} heats</span>`:""}</div>`;
  h+=`</div><div class="card" style="margin:0"><h2>Results for ${esc(c)}</h2>`;
  if(!tmData.results.length) h+=`<p class="mute">No results yet.</p>`;
  for(const r of tmData.results) h+=`<div class="prow" style="cursor:default"><span class="pn">${r.place?(r.tie?"=":"")+r.place:"–"}</span>
    <div><div class="pl">${esc(r.crew||"Lane "+r.lane)}</div><div class="ps">${esc(r.heat&&r.heat.div?heatLabel(r.heat):"Race "+r.race)}</div></div>
    <span style="text-align:right"><span class="tm2">${r.place?ft(r.t_us):esc(r.status)}</span><br><span class="chip ${r.final?"now":"next"}">${r.final?"Final":"Provisional"}</span></span></div>`;
  $("race").innerHTML=h+`</div></div>`+homeBtn();
}
let queue=[];
async function loadHist(){ try{ hist=await (await fetch("/api/history")).json(); queue=await (await fetch("/api/queue")).json(); histAt=Date.now(); }catch(e){} }
let enterAsk=null;
function askEntered(race){
  const r=queue.find(x=>x.race===race); if(!r) return;
  $("sheetin").innerHTML=`<h2>Confirm entered?</h2><p>Race ${race}${r.heat?" · "+esc(heatLabel(r.heat)):""} has been entered in LiveHeats.</p>
    ${r.confirmed?"":`<p class="warn" style="margin:8px 0">These results were never confirmed on the Confirm tab.</p>`}
    <div class="row"><button class="btn pri" id="entyes">Yes, entered</button><button class="btn" onclick="closeSheet()">Cancel</button></div>`;
  $("sheet").classList.add("on");
  $("entyes").onclick=()=>{ closeSheet(); entered(race); };
}
async function entered(race,undo){
  await post("/api/entered",{race:race,undo:!!undo}); histAt=0; await loadHist(); lastKey=""; render();
  if(!undo) showUndo(`Race ${race} marked as entered in LiveHeats`, null, ()=>entered(race,true));
}
let entIdx=0, entBy=(()=>{ try{ return localStorage.getItem("irb_entby")||"place"; }catch(e){ return "place"; } })();
const ORD=n=>n+(n%100>=11&&n%100<=13?"th":["th","st","nd","rd"][n%10]||"th");
function entryCard(){
  let h=`<div class="card ent"><h2>To enter in LiveHeats${queue.length?` <span class="badge">${queue.length}</span>`:""}</h2>`;
  if(!queue.length) return h+`<p class="mute">All finished races are entered. ✓</p></div>`;
  if(entIdx>=queue.length) entIdx=queue.length-1;
  const r=queue[entIdx], ties=r.ties||[], dq=(r.flags||{}).dq||{};
  h+=`<div class="entnav"><button class="btn sm" ${entIdx?"":"disabled"} onclick="entIdx--;lastKey='';render()">‹</button>
    <span>Race ${r.race} · ${entIdx+1} of ${queue.length}</span><button class="btn sm" ${entIdx<queue.length-1?"":"disabled"} onclick="entIdx++;lastKey='';render()">›</button></div>`;
  h+=`<div class="enthd">${r.heat?`<div class="entdiv">${esc(r.heat.div)}</div><div class="entrnd">${esc(r.heat.round)} · Heat ${r.heat.no}</div>`:`<div class="entdiv">Race ${r.race}</div><div class="mute">No heat was chosen for this race</div>`}</div>`;
  h+=`<div style="margin:6px 0">${raceStatus(r.confirmed,false)}</div>`;
  if(!r.confirmed) h+=`<div class="warn" style="margin:8px 0">Not confirmed yet – check the result on the Confirm tab first. <a href="#" onclick="goTab('results');return false">Confirm ›</a></div>`;
  h+=`<div class="row" style="margin:8px 0 4px;align-items:center"><span class="mute">Order:</span>${[["place","By place"],["lane","By lane"]].map(([k,n])=>
    `<button class="btn sm ${entBy===k?"pri":""}" onclick="entBy='${k}';try{localStorage.setItem('irb_entby','${k}')}catch(e){};lastKey='';render()">${n}</button>`).join("")}</div>`;
  const rows=r.rows.slice().sort(entBy==="lane"?(a,b)=>a.lane-b.lane:(a,b)=>(a.place||99)-(b.place||99)||a.lane-b.lane);
  h+=`<div class="entt">${rows.map(x=>{ const st2=x.place?"":x.status==="DQ"?"DQ"+(dq[String(x.lane)]?" "+dq[String(x.lane)]:""):x.status==="DNF"?"DNF":x.status==="INCOMPLETE"?"Didn't finish":x.status||"No finish";
      const pl=`<span class="ep">${x.place?(ties.includes(x.lane)?"=":"")+ORD(x.place):esc(st2)}</span>`, ln=`<span class="el">Lane ${x.lane}</span>`;
      return `<div class="er ${x.place?"":"out"}">${entBy==="lane"?ln+pl:pl+ln}<span class="ec">${esc(crewOf(r.heat,x.lane)||"–")}${x.place&&x.t_us!=null?`<small>${ft(x.t_us)}</small>`:""}</span></div>`; }).join("")}</div>`;
  if(r.rows.some(x=>!x.place&&x.status==="INCOMPLETE")) h+=`<p class="mute" style="margin:6px 0 0">"Didn't finish" = not all legs were recorded. Check with the finish judges before entering.</p>`;
  h+=`<div class="row"><button class="btn pri entbtn" onclick="askEntered(${r.race})">Entered in LiveHeats ✓</button>
    ${st.draw?`<a class="btn" href="https://liveheats.com/events/${esc(st.draw.id)}" target="_blank" rel="noopener" style="text-decoration:none">Open LiveHeats</a>`:""}</div>`;
  return h+`</div>`;
}
function renderHistory(){
  const open=new Set(Array.from(document.querySelectorAll("#history details[open]")).map(d=>d.dataset.r));
  let h="";
  if(st&&st.official){
    h+=entryCard();
  }
  let right=`<div class="card"><h2>Race history</h2><p class="mute">Saved on this computer (the Pico keeps its own copy too).
    Shows the final version of each race.</p><div class="row"><a class="btn pri" href="/history.csv" style="text-decoration:none">Download all (CSV for Excel)</a></div></div>`;
  if(!hist.length) right+=`<div class="card mute">No races saved yet.</div>`;
  else{ right+=`<div class="card">`;
    for(const r of hist){ const top=r.rows.filter(x=>x.place).sort((a,b)=>a.place-b.place).slice(0,3)
        .map(x=>x.place+". "+(crewOf(r.heat,x.lane)||"Lane "+x.lane)).join("  ·  ");
      const adj=Object.keys(r.changes||{}).length||r.legs_set;
      right+=`<details data-r="${r.race}"><summary>Race ${r.race}${r.heat?" · "+esc(heatLabel(r.heat)):r.event?" · "+esc(r.event):""} · ${esc(r.saved_at)} · ${r.legs} leg${r.legs===1?"":"s"}${adj?" · adjusted":""}
        <div class="mute" style="font-weight:400">${esc(top||"no finishers")}</div><div style="margin-top:4px">${raceStatus(!!(r.flags&&r.flags.confirmed),!!(r.flags&&r.flags.entered))}</div></summary>${resultsTable(r,false)}${
        r.flags&&r.flags.note?`<p><b>Note:</b> ${esc(r.flags.note)}</p>`:""}${(r.flags&&r.flags.log||[]).map(x=>`<div class="log">${esc(x[0])} ${esc(x[1])}: ${esc(x[2])}</div>`).join("")}</details>`; }
    right+=`</div>`; }
  $("history").innerHTML=h?`<div class="cols"><div>${h}</div><div>${right}</div></div>`:right;
  document.querySelectorAll("#history details").forEach(d=>{ if(open.has(d.dataset.r)) d.open=true; });
}
// ---------- officials: request, approve, close event ----------
const LV=["starter","marshal","admin"];
function pinCard(){
  const role=st.role;
  if(role==="master"&&st.access) return officialsCard()+joinCard();
  if(role!=="viewer") return `<div class="card"><h2>This device: ${ROLE_NAME[role]}${st.me?" · "+esc(st.me.name):""}</h2>
    <p class="mute">Approved by the timing desk for today. Access ends when the timing desk closes the event.</p>
    <div class="row"><button class="btn" onclick="lockDevice()">Log out</button></div></div>`+joinCard();
  return `<div class="card"><h2>View only</h2><div class="row"><button class="btn pri" onclick="openRequest()">Officials – ask for access</button></div></div>`;
}
function officialsCard(){
  const a=st.access, n={starter:0,marshal:0,admin:0,master:0};
  a.officials.forEach(o=>n[o.role]=(n[o.role]||0)+1);
  let h=`<div class="card"><h2>Officials${a.requests.length?` <span class="badge">${a.requests.length}</span>`:""}</h2>`;
  for(const r of a.requests) h+=`<div class="req"><div><b style="font-size:20px">${esc(r.name)}</b><span class="code">${esc(r.code)}</span>
      <div class="mute">Check the code on their phone matches · asked ${r.mins?r.mins+" min ago":"just now"}${r.usual?" · usually "+ROLE_NAME[r.usual]:""}</div></div>
    <div class="row" style="margin-top:8px">${LV.map(l=>`<button class="btn ${r.usual===l?"pri":""}" onclick="approve('${r.id}','${l}')">${ROLE_NAME[l]}</button>`).join("")}
      <button class="btn red" onclick="offDo({decline:'${r.id}'},'Declined')">Decline</button></div>
    <label style="display:flex;gap:8px;align-items:center;margin-top:6px"><input type="checkbox" id="rem_${r.id}" ${r.usual?"checked":""} style="width:auto"> Remember ${esc(r.name)} for next time</label></div>`;
  if(!a.requests.length) h+=`<p class="mute" style="margin-top:0">Officials scan the join card and tap <b>Officials</b>. Requests show here.</p>`;
  h+=`<p style="font-weight:800;margin:10px 0 4px">${LV.map(l=>ROLE_NAME[l]+" "+n[l]).join(" · ")}${n.master?" · Timing desk phone "+n.master:""}</p>`;
  if(n.starter>2) h+=`<p class="warn">${n.starter} Starters approved – usually one plus a backup. Check this is right.</p>`;
  for(const o of a.officials) h+=`<div class="ofrow"><span class="nm">${esc(o.name)}${o.regular?" ★":""}</span><span class="chip ${o.role==="starter"?"now":"next"}">${ROLE_NAME[o.role]}</span>
    <span class="mute ofs"><span class="dot ${o.mins>=2?"off":""}"></span>${o.mins<2?"<span class='ofc'>connected</span>":"not seen "+(o.mins>=60?Math.floor(o.mins/60)+" h":o.mins+" min")}</span>
    <button class="btn sm" onclick="offSheet('${o.id}')">Change</button></div>`;
  if(a.officials.length) h+=`<div class="row"><button class="btn red" onclick="askClose()">Close event</button></div>`;
  h+=`</div>`;
  return h;
}
async function offDo(d,ok){ try{ const j=await (await fetch("/api/officials",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify(d)})).json();
  toast(j.result==="ok"?ok:j.result); }catch(e){ toast("No link to the timing computer"); } lastKey=""; }
function approve(id,l){ const c=$("rem_"+id); offDo({approve:id,role:l,remember:!!(c&&c.checked)},"Approved as "+ROLE_NAME[l]); }
function offSheet(id){ const o=st.access.officials.find(x=>x.id===id); if(!o) return;
  $("sheetin").innerHTML=`<h2>${esc(o.name)}</h2><p class="mute">Now: ${ROLE_NAME[o.role]}. Changes take effect on their phone straight away.</p>
    ${o.role==="master"?"":`<div class="row">${LV.map(l=>`<button class="btn ${o.role===l?"pri":""}" onclick="closeSheet();offDo({set_role:'${id}',role:'${l}'},'Changed to ${ROLE_NAME[l]}')">${ROLE_NAME[l]}</button>`).join("")}</div>
    <label style="display:flex;gap:8px;align-items:center;margin-top:10px"><input type="checkbox" ${o.regular?"checked":""} style="width:auto" onchange="offDo({remember:'${id}',on:this.checked},this.checked?'Remembered':'Forgotten')"> Remember for next time</label>`}
    <div class="row"><button class="btn red" onclick="closeSheet();offDo({remove:'${id}'},'Removed')">Remove access</button><button class="btn" onclick="closeSheet()">Close</button></div>`;
  $("sheet").classList.add("on"); }
function askClose(){
  const q=st.queue_n||0;
  $("sheetin").innerHTML=`<h2>Close the event?</h2><p>Everyone's access ends now – ${st.access.officials.length} official${st.access.officials.length===1?"":"s"}. Remembered names are kept for next time.</p>
    ${q?`<p class="warn">${q} race${q===1?" is":"s are"} not ticked off as entered in LiveHeats yet (LiveHeats tab).</p>`:""}
    <p class="mute">Results are saved on this computer. A USB backup is made after every race if a stick with an IRB_backup folder is plugged in.</p>
    <div class="row"><button class="btn red" onclick="closeSheet();offDo({close:true},'Event closed – all access removed')">Yes, close the event</button><button class="btn" onclick="closeSheet()">Cancel</button></div>`;
  $("sheet").classList.add("on"); }
// ---------- QR codes ----------
const qrCache={};
function qrSvg(text,px){ const k=text+"|"+px; if(qrCache[k]) return qrCache[k];
  const q=qrcode(0,"M"); q.addData(text,"Byte"); q.make(); const n=q.getModuleCount(), m=3; let d="";
  for(let r=0;r<n;r++) for(let c=0;c<n;c++) if(q.isDark(r,c)) d+=`M${c+m} ${r+m}h1v1h-1z`;
  return qrCache[k]=`<svg viewBox="0 0 ${n+2*m} ${n+2*m}" width="${px}" height="${px}" shape-rendering="crispEdges" role="img"><rect width="${n+2*m}" height="${n+2*m}" fill="#fff"/><path d="${d}" fill="#000"/></svg>`; }
function wifiText(j){ const e=s=>String(s).replace(/([\\;,:"])/g,"\\$1"); return `WIFI:T:${j.pass?"WPA":"nopass"};S:${e(j.ssid)};${j.pass?"P:"+e(j.pass)+";":""};`; }
function joinCodes(px){ const j=st.join||{}; let h=`<div class="qrs">`;
  if(j.ssid) h+=`<div>1. Wi-Fi${qrSvg(wifiText(j),px)}<div class="mute">${esc(j.ssid)}</div></div>`;
  return h+`<div>${j.ssid?"2. ":""}IRB Racing App${qrSvg(j.url,px)}<div class="mute">${esc(j.url)}</div></div></div>`; }
function joinCard(){
  const j=st.join||{};
  return `<div class="card"><h2>Join card</h2>
    ${j.ssid?"":`<p class="warn" style="margin-top:0">Add the Wi-Fi ${st.role==="master"?"under <b>Setup</b>":"– ask the timing desk"} for the Wi-Fi code.</p>`}
    ${joinCodes(st.role==="master"?130:180)}<div class="row"><button class="btn pri" onclick="downloadCard()">Download</button><button class="btn" onclick="printCard()">Print</button></div></div>`; }
function cardCanvas(){
  const j=st.join||{}, codes=(j.ssid?[["1. Wi-Fi",wifiText(j),j.ssid]]:[]).concat([[(j.ssid?"2. ":"")+"IRB Racing App",j.url,j.url]]);
  const W=codes.length*560+80, c=document.createElement("canvas"); c.width=W; c.height=760; const x=c.getContext("2d");
  x.fillStyle="#fff"; x.fillRect(0,0,W,760); x.fillStyle="#000"; x.textAlign="center";
  x.font="bold 54px sans-serif"; x.fillText(((st.brand||{}).club||"IRB Racing").slice(0,40),W/2,80);
  codes.forEach(([lab,txt,sub],i)=>{ const q=qrcode(0,"M"); q.addData(txt,"Byte"); q.make(); const n=q.getModuleCount(), s=Math.floor(460/n), ox=80+i*560+(480-n*s)/2, oy=150;
    for(let r=0;r<n;r++) for(let cc=0;cc<n;cc++) if(q.isDark(r,cc)) x.fillRect(ox+cc*s,oy+r*s,s,s);
    x.font="bold 40px sans-serif"; x.fillText(lab,80+i*560+240,135); x.font="28px sans-serif"; x.fillText(sub.length>34?sub.slice(0,34)+"…":sub,80+i*560+240,700); });
  return c; }
function downloadCard(){ try{ const a=document.createElement("a"); a.href=cardCanvas().toDataURL("image/png"); a.download="IRB-join-card.png"; document.body.appendChild(a); a.click(); a.remove(); }
  catch(e){ toast("Couldn't save the picture on this device"); } }
function printCard(){ let p=$("printcard"); if(!p){ p=document.createElement("div"); p.id="printcard"; document.body.appendChild(p); }
  const ttl=esc((st.brand||{}).club||"IRB Racing");
  p.innerHTML=`<div class="pc"><h1>${ttl}</h1>${joinCodes(260)}</div><div class="pc" style="margin-top:8mm"><h1>${ttl}</h1>${joinCodes(260)}</div>`;
  try{ window.print(); }catch(e){ toast("Printing isn't available here"); } }
function boardQr(){ const j=st&&st.join; if(!j||!j.url) return "";
  return `<div class="bqr">${j.ssid?`<div>${qrSvg(wifiText(j),120)}1. Wi-Fi</div>`:""}<div>${qrSvg(j.url,120)}${j.ssid?"2. ":""}Results on<br>your phone</div></div>`; }
// ---------- home screen for phones that aren't officials ----------
let wasWaiting=false;
function homeTitle(){ const b=(st&&st.brand)||{};
  return `<div class="htitle">${b.logo?`<img src="/logo?v=${b.logo}" alt="">`:""}<h1>${esc(b.club||"IRB Racing")}</h1>${b.event?`<div class="mute">${esc(b.event)}</div>`:b.club?`<div class="mute">IRB Racing</div>`:""}</div>`; }
function renderHome(){
  const me=st.me||{};
  if(me.code){ $("race").innerHTML=`<div class="home"><h1>Waiting for the timing desk</h1><div class="card" style="text-align:center">
      <p style="margin:0">Show this code to the timing desk</p><div class="bigcode">${esc(me.code)}</div><p class="mute" style="margin:0">${esc(me.name)} · your screen opens as soon as you're approved</p></div>
      <button class="btn" onclick="lockDevice()">Cancel request</button></div>`; return; }
  $("race").innerHTML=`<div class="home">${homeTitle()}
    <a class="hbtn pri" href="#team" onclick="tmView='club'">Team Manager<small>Your club's heats, lanes and results · the program · all results</small></a>
    <a class="hbtn" href="#board">Results<small>Live results and the next heat – for a screen or your phone</small></a>
    <button class="hbtn" onclick="openRequest()">Officials<small>Starter, Marshal, Referee – ask the timing desk for access</small></button></div>`;
}
function openRequest(){
  $("sheetin").innerHTML=`<h2>Officials</h2><p class="mute">Type your name and tap Request access. A code shows on your phone – show it at the timing desk.</p>
    <input type="text" id="rqname" value="${esc(myName())}" placeholder="Your name" autocomplete="name">
    <div class="row"><button class="btn pri" id="rqgo">Request access</button><button class="btn" onclick="closeSheet()">Cancel</button></div><p class="mute" id="rqmsg"></p>
    <p class="mute" style="font-size:14px;margin-bottom:0">Second timing desk phone with a PIN? <a href="#" onclick="openUnlock();return false">Use the PIN</a></p>`;
  $("sheet").classList.add("on"); $("rqname").focus();
  $("rqgo").onclick=async()=>{ const n=$("rqname").value.trim(); try{ const j=await (await fetch("/api/request",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({name:n})})).json();
    if(j.result!=="ok"){ $("rqmsg").textContent=j.result; return; } setMyName(n); closeSheet(); location.hash=""; if(st){ st.me={name:n,code:j.code}; } wasWaiting=true; lastKey=""; render(); }
    catch(e){ $("rqmsg").textContent="No link to the timing computer"; } };
}
function openUnlock(){
  $("sheetin").innerHTML=`<h2>Second timing desk phone</h2><p class="mute">Only if the timing desk has turned on a second timing desk phone PIN. Everyone else: use Officials and ask the timing desk.</p>
    <input type="text" id="pinin" inputmode="numeric" autocomplete="off" placeholder="PIN">
    <div class="row"><button class="btn pri" id="pingo">Log in</button><button class="btn" onclick="closeSheet()">Close</button></div><p class="mute" id="pinmsg"></p>
`;
  $("sheet").classList.add("on"); $("pinin").focus();
  $("pingo").onclick=async()=>{ try{ const j=await (await fetch("/api/unlock",{method:"POST",headers:{"Content-Type":"application/json"},
      body:JSON.stringify({pin:$("pinin").value})})).json();
    if(j.result==="ok"){ closeSheet(); toast("Logged in as "+ROLE_NAME[j.role]); tabRole=""; justLogged=true; } else $("pinmsg").textContent=j.result; }catch(e){ $("pinmsg").textContent="No link to the timing computer"; } };
}
async function lockDevice(){ await post("/api/lock",{}); wasWaiting=false; if(st) st.me=null; toast(st&&st.role!=="viewer"?"Logged out":"Request cancelled"); tabRole=""; location.hash=""; lastKey=""; render(); }
function testProblems(){ const lt=st.last_test||{missing:[],clash:[]}, n=lt.missing.length+(lt.clash||[]).length; return n+" problem"+(n===1?"":"s"); }
let ltOpen=false;
function testCard(){
  const need=st.lanes.map(l=>"Lane "+l).concat(["SET","GO","FINISH"]);
  if(st.test){
    const seen=st.test_seen||[], left=need.filter(x=>!seen.includes(x));
    const cnt=st.test_count||{}, cl=st.test_clash||[];
    const bad=new Set(cl.filter(c=>c.status==="fault").flatMap(c=>[c.a,c.b]));
    const sus=new Set(cl.filter(c=>c.status!=="fault").flatMap(c=>[c.a,c.b]));
    const ms=c=>(c.ms<1?"under 1":c.ms)+" ms apart";
    let clashTxt="";
    for(const c of cl.filter(c=>c.status==="fault"))
      clashTxt+=`<div class="bad-warn">Fault: ${esc(c.a)} and ${esc(c.b)} went off together ${c.times} times (${ms(c)}).
        Likely a short or crossed wires between them. Fix it, then end this test and start a new one.</div>`;
    for(const c of cl.filter(c=>c.status!=="fault")){
      const left=[c.a,c.b].filter(x=>!c.clean.includes(x));
      clashTxt+=`<div class="warn">Check: ${esc(c.a)} and ${esc(c.b)} went off together (${ms(c)}). It may have been two people pressing at once.
        Press ${left.map(esc).join(" and ")} on ${left.length>1?"their":"its"} own – if ${left.length>1?"both work":"it works"} separately, this clears.</div>`;
    }
    return `<div class="card confirm"><h2>Button test running</h2>${clashTxt}<p class="mute">Press each button (hold FINISH for 1 second). A box flashes every time its button is pressed, so you can check each button is wired to the right lane. Nothing will start.</p>
      <div class="lastpress">${st.test_last?"Last pressed: "+esc(st.test_last):"Press a button…"}</div>
      <div class="tests">${need.map(x=>`<div data-t="${esc(x)}" class="${bad.has(x)?"clash":sus.has(x)?"sus":seen.includes(x)?"ok":""}">${seen.includes(x)?"✓ ":""}${esc(x)}${cnt[x]?`<small>×${cnt[x]}</small>`:""}</div>`).join("")}</div>
      <p>${left.length?left.length+" still to press.":bad.size?"All buttons respond, but there is a wiring fault above.":sus.size?"All buttons respond – finish the check above.":"All buttons work."}</p>
      <div class="row"><button class="btn ${left.length?"":"pri"}" onclick="cmd('test off')">End test</button></div></div>`;
  }
  const lt=st.last_test, today=lt&&lt.date===st.today;
  return `<div class="card"><h2>Button test</h2><p class="mute">Every morning before racing – the only way to find a broken FINISH cable.</p>
    ${lt?(()=>{ const bad=lt.missing.length||(lt.clash||[]).length;
      return `<p class="${today&&!bad?"ok":"bad"}" style="margin-bottom:4px">${today?"Today":esc(lt.date)} ${esc(lt.at)} – ${bad?testProblems():"all buttons worked"}${today?"":" (not today)"}
        ${bad?`<button class="btn sm" style="margin-left:6px" onclick="ltOpen=!ltOpen;lastKey='';render()">${ltOpen?"Hide":"Show"}</button>`:""}</p>
      ${bad&&ltOpen?`<ul class="mute" style="margin:0 0 6px;padding-left:20px">${lt.missing.map(x=>`<li>${esc(x)} – no press seen</li>`).join("")}${(lt.clash||[]).map(x=>`<li>${esc(x)} – went off together</li>`).join("")}</ul>`:""}`; })():`<p class="bad">Not done yet.</p>`}
    <div class="row"><button class="btn pri" ${st.state==="IDLE"||st.state==="DONE"?"":"disabled"} onclick="cmd('test on')">Start button test</button></div></div>`;
}
let prevCounts={};
let sysView="today", updBusy=false;
function updateCard(){
  const u=st.update, racing=st.state==="ARMED"||st.state==="RACING";
  let h=`<div class="card"><h2>Updates</h2><p style="margin:0 0 6px">This computer has <b>v${esc(u.current)}</b>.</p>`;
  if(u.newer) h+=`<div class="req" style="border-color:var(--blue);background:#e3edf9"><b style="font-size:19px">New version v${esc(u.latest)} available</b>
      ${u.notes.length?`<ul style="margin:6px 0 0;padding-left:20px">${u.notes.map(n=>`<li>${esc(n)}</li>`).join("")}</ul>`:""}</div>`;
  else if(u.latest) h+=`<p class="ok" style="margin:6px 0">Up to date${u.checked?" – checked "+esc(u.checked):""}.</p>`;
  if(u.msg) h+=`<p class="warn">${esc(u.msg)}</p>`;
  if(racing) h+=`<p class="mute">Updates are paused while a race is armed or running.</p>`;
  h+=`<div class="row">${u.newer?`<button class="btn pri" ${racing||updBusy?"disabled":""} onclick="askUpdate()">Update to v${esc(u.latest)}</button>`:""}
    <button class="btn" ${updBusy?"disabled":""} onclick="updDo({check:true},'Checked')">Check for updates</button>
    ${u.prev?`<button class="btn" ${racing||updBusy?"disabled":""} onclick="askRollback()">Go back to ${u.prev==="earlier"?"the previous version":"v"+esc(u.prev)}</button>`:""}</div>
    <p class="mute" style="margin-bottom:0">Needs internet just while updating. The app restarts by itself in a few seconds – results, settings and officials stay.</p></div>`;
  return h;
}
async function updDo(d,ok){ updBusy=true; lastKey=""; render();
  try{ const j=await (await fetch("/api/update",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify(d)})).json();
    if(j.result==="ok"){ toast(ok); if(d.install||d.rollback) restartWait(); } else toast(j.result); }
  catch(e){ toast("No link to the timing computer"); }
  updBusy=false; lastKey=""; render(); }
function askUpdate(){ $("sheetin").innerHTML=`<h2>Update to v${esc(st.update.latest)}?</h2><p>The app downloads the new version, keeps a copy of this one, and restarts in a few seconds. Phones reconnect by themselves.</p>
  <div class="row"><button class="btn pri" onclick="closeSheet();updDo({install:true},'Updating – restarting…')">Yes, update now</button><button class="btn" onclick="closeSheet()">Cancel</button></div>`; $("sheet").classList.add("on"); }
function askRollback(){ $("sheetin").innerHTML=`<h2>Go back to the previous version?</h2><p>Only if the new version has a problem. The app restarts in a few seconds.</p>
  <div class="row"><button class="btn red" onclick="closeSheet();updDo({rollback:true},'Going back – restarting…')">Yes, go back</button><button class="btn" onclick="closeSheet()">Cancel</button></div>`; $("sheet").classList.add("on"); }
function restartWait(){ const was=st.app; let n=0; const iv=setInterval(async()=>{ n++;
    try{ const s=await (await fetch("/api/state",{cache:"no-store"})).json(); if(s.app!==was||n>40){ clearInterval(iv); location.reload(); } }catch(e){} },1000); }
const a_ssid=()=>(($("wssid")||{}).value??((st.access||{}).net||{}).ssid)||"", a_pass=()=>(($("wpass")||{}).value??((st.access||{}).net||{}).pass)||"",
  a_addr=()=>(($("waddr")||{}).value??((st.access||{}).net||{}).addr)||"";
function battWord(v){ return v<23?["Swap the battery now","bad"]:v<24?["Charge now","bad"]:v<24.6?["Charge soon","amb"]:["OK","good"]; }
function battCard(){ const v=st.batt, pc=Math.max(0,Math.min(100,Math.round((v-23)/(26.4-23)*100))), w=battWord(v);
  return `<div class="card"><h2>Battery</h2><div class="bbar ${w[1]}"><i style="width:${pc}%"></i></div>
    <p class="${w[1]==="good"?"ok":w[1]==="bad"?"bad":""}" style="margin:6px 0 0;font-size:20px;font-weight:800">${w[0]}</p>
    <p class="mute" style="margin:2px 0 0;font-size:14px">${v.toFixed(1)} V${st.batt_old?" · over a minute old":""}</p></div>`; }
function sysCols(a,b,c){ return `<div class="syscols"><div>${a}</div><div>${b}</div><div>${c}</div></div>`; }
let advOpen=false;
function askNewEvent(){
  const q=st.queue_n||0, unconf=st.state==="DONE"&&st.results&&!st.confirmed&&!st.results.practice;
  $("sheetin").innerHTML=`<h2>Start a new event?</h2>
    ${q?`<p class="bad-warn">${q} race${q===1?" is":"s are"} not ticked off as entered in LiveHeats. Do that first if you still need to.</p>`:""}
    ${unconf?`<p class="warn">The last race isn't confirmed yet.</p>`:""}
    <p>This saves today's results (with a spreadsheet), program and LiveHeats ticks in <b>timing_data › past_events</b>, then clears them from every screen. Approved officials are logged out.</p>
    <p class="mute">Kept: Wi-Fi, settings, templates, remembered officials. The Pico's race numbers carry on from where they are.</p>
    <div class="mute">Name for the saved event</div><input type="text" id="evname" value="${esc((st.draw&&st.draw.name)||"")}" placeholder="e.g. Club carnival">
    <label style="display:flex;gap:8px;align-items:center;margin-top:10px"><input type="checkbox" id="evkeep" style="width:auto"> Keep the LiveHeats draw (same event, another day)</label>
    <div class="row"><button class="btn red" id="evgo">Yes, start new event</button><button class="btn" onclick="closeSheet()">Cancel</button></div>`;
  $("sheet").classList.add("on");
  $("evgo").onclick=async()=>{ try{ const j=await (await fetch("/api/new_event",{method:"POST",headers:{"Content-Type":"application/json"},
      body:JSON.stringify({name:$("evname").value,keep_draw:$("evkeep").checked})})).json();
    closeSheet(); if(j.result.startsWith("ok:")){ wizOpen=null; joinDone=false; toast("New event started – the last one is saved as "+j.result.slice(3)); hist=[]; queue=[]; histAt=0; drawData=null; await loadProg(); await loadHist(); }
    else toast(j.result); }catch(e){ toast("No link to the timing computer"); } lastKey=""; render(); };
}
function brandSheet(){ const b=st.brand||{};
  sheet(`<h2>Club and event</h2><p class="mute">Shown on the Results and Marshalling screens, the home page, the join card and the guides.</p>
    <div class="wform"><input type="text" id="bclub" value="${esc(b.club||"")}" placeholder="Club name" maxlength="40"><input type="text" id="bevent" value="${esc(b.event||"")}" placeholder="Event name" maxlength="40"></div>
    <div class="row" style="align-items:center"><button class="btn pri" onclick="saveBrand();closeSheet()">Save</button>
    <label class="btn">${b.logo?"Change logo":"Add logo"}<input type="file" accept="image/*" style="display:none" onchange="logoPick(this);closeSheet()"></label>
    ${b.logo?`<button class="btn" onclick="brandDo({logo:''},'Logo removed');closeSheet()">Remove logo</button>`:""}<button class="btn" onclick="closeSheet()">Cancel</button></div>`); }
async function ownDo(d,ok){ try{ const j=await (await fetch("/api/owner",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify(d)})).json();
  if(j.result==="ok"){ toast(ok); closeSheet(); } else { const m=$("ownmsg"); if(m) m.textContent=j.result; else toast(j.result); } }catch(e){ toast("No link to the timing computer"); } lastKey=""; }
function ownerSheet(kind){
  sheet(kind==="open"?`<h2>Owner unlock</h2><p class="mute">For the kit owner. Unlocks updates and advanced settings for 20 minutes.</p>
      <input type="password" id="ownpin" inputmode="numeric" autocomplete="off" placeholder="Owner PIN"><div class="row"><button class="btn pri" onclick="ownDo({pin:$('ownpin').value},'Unlocked for 20 minutes')">Unlock</button><button class="btn" onclick="closeSheet()">Cancel</button></div><p class="bad" id="ownmsg"></p>`
    :`<h2>Owner PIN</h2><p class="mute">With a PIN set, only the owner can install updates, go back a version, change the app address or second timing desk phone, edit the hire kit list or restart the timing box. Everything else works as normal.</p>
      <input type="password" id="ownpin" inputmode="numeric" autocomplete="off" placeholder="4 to 8 digits (empty = lock off)"><div class="row"><button class="btn pri" onclick="ownDo({set_pin:$('ownpin').value},$('ownpin').value?'Owner PIN saved':'Owner lock off')">Save</button><button class="btn" onclick="closeSheet()">Cancel</button></div><p class="bad" id="ownmsg"></p>`);
  setTimeout(()=>{ const i=$("ownpin"); if(i) i.focus(); },50); }
async function keyDo(v){ try{ const j=await (await fetch("/api/updkey",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({key:v})})).json();
  if(j.result==="ok"){ toast(v?"Key saved – updates checked":"Key removed"); closeSheet(); } else { const m=$("keymsg"); if(m) m.textContent=j.result; else toast(j.result); } }
  catch(e){ toast("No link to the timing computer"); } lastKey=""; }
function keySheet(){ sheet(`<h2>Updates key</h2><p class="mute">A read-only GitHub key, so this computer can download updates from a private repository. Paste it once – it's saved on this computer and left out of problem reports.</p>
    <input type="password" id="keyin" autocomplete="off" placeholder="github_pat_…"><div class="row"><button class="btn pri" onclick="keyDo($('keyin').value.trim())">Save and test</button><button class="btn" onclick="closeSheet()">Cancel</button></div><p class="bad" id="keymsg"></p>`);
  setTimeout(()=>{ const i=$("keyin"); if(i) i.focus(); },50); }
function kitSheet(){ sheet(`<h2>Hire kit list</h2><p class="mute">One item per line. Printed as a checklist with the role guides.</p>
    <textarea id="kittxt" rows="10" style="width:100%">${esc(st.kit||"")}</textarea>
    <div class="row"><button class="btn pri" onclick="ownDo({kit:$('kittxt').value},'Saved')">Save</button><button class="btn" onclick="closeSheet()">Cancel</button></div><p class="bad" id="ownmsg"></p>`); }
function packSheet(){ sheet(`<h2>Saved events</h2><p class="mute">Each one saved by Start new event. Download it as a zip – the results open in Excel.</p>
    ${(st.past_events||[]).map(e=>`<div class="ofrow"><span class="nm">${esc(e)}</span><a class="btn sm" href="/event_pack.zip?e=${encodeURIComponent(e)}" download>Download</a></div>`).join("")}
    <div class="row"><button class="btn" onclick="closeSheet()">Close</button></div>`); }
async function evDo(d,ok){ try{ const j=await (await fetch("/api/events",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify(d)})).json();
  if(j.result!=="ok"){ toast(j.result); return; } toast(ok); const s=await (await fetch("/api/state")).json(); st=s; eventsSheet(); }catch(e){ toast("No link to the timing computer"); } lastKey=""; }
function legSel(id,v){ return `<select id="${id}">${[1,2,3,4,5,6,7,8].map(n=>`<option ${n===v?"selected":""}>${n}</option>`).join("")}</select>`; }
function eventsSheet(){ const ev=st.events.filter(e=>e.id);
  sheet(`<h2>Events</h2><p class="mute">The events you run and how many legs each has – the app uses the legs to know when every crew is in.</p>
    ${ev.map(e=>`<div class="evrow"><input type="text" id="en_${e.id}" value="${esc(e.name)}" maxlength="30">${legSel("el_"+e.id,e.legs)}<span class="mute">legs</span>
      <button class="btn sm" onclick="evDo({edit:'${e.id}',name:$('en_${e.id}').value,legs:+$('el_${e.id}').value},'Saved')">Save</button>
      <button class="btn sm" onclick="evDo({remove:'${e.id}'},'Removed')">Remove</button></div>`).join("")}
    <div class="evrow" style="border-top:2px solid var(--line);padding-top:10px"><input type="text" id="en_new" placeholder="New event name" maxlength="30">${legSel("el_new",1)}<span class="mute">legs</span>
      <button class="btn sm pri" onclick="evDo({add:true,name:$('en_new').value,legs:+$('el_new').value},'Added')">Add</button></div>
    <div class="row"><button class="btn" onclick="askYes('Put the events back to the standard IRB list?',()=>evDo({reset:true},'Standard events back'),'Yes, reset')">Standard IRB events</button><button class="btn pri" onclick="closeSheet()">Done</button></div>`); }
// ---------- printed guides: one page per job, plus the hire kit checklist ----------
const GUIDES=[
  ["Timing desk","This laptop. You run the day.",[
    "Turn on the Wi-Fi router. Plug the timing box into this laptop. The app opens by itself.",
    "Follow Get started on the Race tab: timing box, club name, how heats are run, Wi-Fi, button test, join card.",
    "Officials scan the join card and tap Officials. Their name and a 3-digit code show under System – check the code on their phone, then tap their job.",
    "Watch the blue Next bar at the top. It always shows the next thing to do.",
    "After each race, check the result on the Confirm tab and press Confirm results (or let the Referee do it).",
    "End of day: every race ticked on the LiveHeats tab, then System › Setup › Start new event. That saves everything.",
    "Something wrong? Press ? on any screen for fixes."]],
  ["Starter","SET, GO and FINISH.",[
    "Scan the join card: 1 for the Wi-Fi, 2 for the app. Tap Officials, type your name and show the code to the timing desk.",
    "Every morning, do the button test with the timing desk: press every lane, SET, GO, and hold FINISH for 1 second.",
    "Check the heat on your screen matches the crews on the start.",
    "SET arms the race. GO starts the clock. The handheld buttons do the same.",
    "Red messages must be checked before SET.",
    "When every crew is in, press FINISH (it asks twice)."]],
  ["Marshal","Patients in, patients out.",[
    "Scan the join card: 1 for the Wi-Fi, 2 for the app. Tap Officials, type your name and show the code to the timing desk.",
    "The heat at the top is the next one to marshal.",
    "Tap a crew when its patients arrive. Tap again to undo. Scratch is only for a crew that's out.",
    "When that heat's patients go out on the water, press Patients sent. The screen moves on to the next heat.",
    "Patients report 5 races before their heat. The Marshalling screen on the TV shows who is needed."]],
  ["Referee","Results and LiveHeats.",[
    "Scan the join card: 1 for the Wi-Fi, 2 for the app. Tap Officials, type your name and show the code to the timing desk.",
    "Confirm tab: after each race, check the places and times. Tap Edit on a crew to accept, move, DQ or DNF them.",
    "When the judges agree, press Confirm results. The screens then show the result as Final.",
    "LiveHeats tab: type each confirmed race into LiveHeats, then press Entered.",
    "Program tab: change the running order or add heats when needed."]]];
function printGuides(){ let p=$("printcard"); if(!p){ p=document.createElement("div"); p.id="printcard"; document.body.appendChild(p); }
  const b=st.brand||{}, top=`<div class="gtop">${b.logo?`<img src="/logo?v=${b.logo}" alt="">`:""}<span>${esc(b.club||"IRB Racing")}${b.event?" · "+esc(b.event):""}</span></div>`;
  p.innerHTML=GUIDES.map(([job,sub,steps])=>`<div class="guide">${top}<h1>${esc(job)}</h1><p class="gsub">${esc(sub)}</p><ol>${steps.map(s=>`<li>${esc(s)}</li>`).join("")}</ol>
      <p class="gfoot">Stuck? Ask the timing desk. App address: ${esc((st.join||{}).url||"")}</p></div>`).join("")
    +`<div class="guide">${top}<h1>Hire kit checklist</h1><p class="gsub">Tick each item out, and back in when you pack up.</p>
      <table class="gkit"><tr><th>Item</th><th>Out</th><th>Back</th></tr>${(st.kit||"").split("\n").map(x=>x.trim()).filter(Boolean).map(x=>`<tr><td>${esc(x)}</td><td>☐</td><td>☐</td></tr>`).join("")}</table>
      <h2>Packing up</h2><ol><li>Every race ticked on the LiveHeats tab.</li><li>System › Setup › Results to take home › Today – save the zip.</li>
      <li>System › Setup › Start new event.</li><li>Battery on charge. Everything back in the box.</li></ol></div>`;
  try{ window.print(); }catch(e){ toast("Printing isn't available here"); } }
function renderSystem(){
  if(!st){ $("system").innerHTML=""; return; }
  const master=st.role==="master", setupOk=st.official;
  if(!setupOk) sysView="today";
  const items=st.lanes.map(l=>"Lane "+l).concat(["SET","GO"]);
  // timing box: connection + wiring in one card; the full table only when something's wrong
  const box=`<div class="card"><h2>Timing box</h2>${st.connected?`<p class="ok" style="margin:0">Connected</p>
      ${st.faults.length?`<table style="margin-top:6px">${items.map(i=>`<tr><td>${i}</td><td class="${st.faults.includes(i)?"bad":"ok"}">${st.faults.includes(i)?"FAULT – open circuit or held":"OK"}</td></tr>`).join("")}</table>`
        :`<p class="mute" style="margin:4px 0 0">Wiring OK: ${items.join(", ")}${st.state==="RACING"?" (checked again after the race)":""}. FINISH is checked by the button test.</p>`}`
      :`<p class="bad" style="margin:0">Not connected – plug the timing box's USB cable into this computer and close Thonny.</p>`}</div>`;
  const test=st.connected&&st.has_test&&(master||st.role==="starter")?testCard():"";
  const screens=`<div class="card"><h2>Screens <span class="mute" style="font-weight:500;font-size:14px">– read-only, no login</span></h2><div class="row" style="margin-top:0"><a class="btn" href="/#board" target="_blank" style="text-decoration:none">Results screen</a>
    <a class="btn" href="/#marshalling" target="_blank" style="text-decoration:none">Marshalling screen</a>
    <a class="btn" href="/#team" target="_blank" style="text-decoration:none">Team Manager</a>
    ${st.role==="admin"?`<button class="btn" onclick="goTab('marshal')">Marshal screen</button>`:""}
    ${master?`<button class="btn" onclick="printGuides()">Print role guides</button>`:""}</div></div>`;
  const batt=st.batt!=null?battCard():"";
  let h=setupOk?`<div class="sysnav"><button class="btn ${sysView==="today"?"pri":""}" onclick="sysView='today';lastKey='';render()">Today</button>
    <button class="btn ${sysView==="setup"?"pri":""}" onclick="sysView='setup';lastKey='';render()">Setup${master&&st.update&&st.update.newer?' <span class="badge">1</span>':""}</button></div>`:"";
  let c="";
  if(sysView==="today"){
    if(master&&st.access) c=sysCols(dayCard(), officialsCard()+test+screens, joinCard()+batt);
    else c=sysCols(box+test, pinCard(), (st.official?screens:"")+batt);
  } else {
    // Setup: one tidy list – a line per item, status in the middle, button on the right
    const a=st.access||{net:{ssid:"",pass:"",addr:""},auto_url:"",master_pin:"",regulars:[]};
    const racing=st.state==="ARMED"||st.state==="RACING";
    const row=(name,status,btns,cls)=>`<div class="srow ${cls||""}"><div class="sn">${name}</div><div class="ss">${status}</div><div class="sb">${btns||""}</div></div>`;
    let L="";
    const ownLocked=!!(st.owner&&st.owner.set&&!st.owner.open);
    if(master) L+=row("Get started", st.setup_done?`<span class="mute">The setup steps for a new carnival</span>`:`<b class="okb">Showing on the Race tab</b>`,
      st.setup_done?`<button class="btn" onclick="brandDo({setup_done:false},'Get started is on the Race tab');goTab('race')">Open</button>`:`<button class="btn" onclick="goTab('race')">Go there</button>`);
    if(master) L+=row("Club and event", (st.brand||{}).club?`<b>${esc(st.brand.club)}</b>${st.brand.event?`<span class="mute"> · ${esc(st.brand.event)}</span>`:""}${st.brand.logo?` <span class="mute">· logo</span>`:""}`:`<span class="mute">Not set – shown on the screens and join card</span>`,
      `<button class="btn" onclick="brandSheet()">Change</button>`);
    if(master&&st.update&&ownLocked){ const u=st.update;
      L+=row("Updates", `v${esc(u.current)}${u.newer?` · <b class="okb">v${esc(u.latest)} is out</b>`:""} · <span class="mute">the owner installs updates</span>`,
        `<button class="btn" onclick="ownerSheet('open')">Unlock</button>`); }
    else if(master&&st.update){ const u=st.update;
      L+=row("Updates", u.newer?`<b class="okb">New version v${esc(u.latest)} available</b>${u.notes.length?`<ul class="snotes">${u.notes.map(n=>`<li>${esc(n)}</li>`).join("")}</ul>`:""}`
          :`v${esc(u.current)}${u.latest?` · <span class="ok">up to date</span>${u.checked?" (checked "+esc(u.checked)+")":""}`:""}${u.msg?`<div class="warn" style="margin-top:4px">${esc(u.msg)}</div>`:""}`,
        (u.newer?`<button class="btn pri" ${racing||updBusy?"disabled":""} onclick="askUpdate()">Update</button>`:"")
        +`<button class="btn" ${updBusy?"disabled":""} onclick="updDo({check:true},'Checked')">Check</button>`
        +(u.prev?`<button class="btn" ${racing||updBusy?"disabled":""} onclick="askRollback()">Go back${u.prev!=="earlier"?" to v"+esc(u.prev):""}</button>`:""), u.newer?"hi":""); }
    L+=row("LiveHeats draw", st.draw?`<b>${esc(st.draw.name)}</b><span class="mute"> · ${st.draw.divisions} divisions · ${st.draw.heats} heats</span>`:`<span class="mute">None loaded – timing works without one</span>`,
      `<button class="btn" onclick="openLoad()">${st.draw?"Reload":"Load"}</button>`);
    if(master&&st.access) L+=row("Wi-Fi for join card", `<div class="sin"><input type="text" id="wssid" value="${esc(a.net.ssid)}" placeholder="Wi-Fi name">
        <input type="text" id="wpass" value="${esc(a.net.pass)}" placeholder="Password"></div>`,
      `<button class="btn" onclick="offDo({net:{ssid:$('wssid').value,pass:$('wpass').value,addr:a_addr()}},'Saved')">Save</button>`);
    L+=row("Backup", st.backup?`<span class="${st.backup.ok?"ok":"bad"}">${st.backup.ok?"Copied "+esc(st.backup.at):esc(st.backup.msg)}</span>`:`<span class="mute">USB stick with an <b>IRB_backup</b> folder</span>`,
      master?`<button class="btn" onclick="post('/api/backup',{}).then(()=>toast('Backup done'))">Back up now</button>`:"");
    if(master) L+=row("Practice mode", st.practice?`<b class="bad">ON – races aren't saved</b>`:`<span class="mute">Off · for training, races aren't saved</span>`,
      `<button class="btn ${st.practice?"pri":""}" onclick="post('/api/practice',{on:${!st.practice}})">${st.practice?"Turn off":"Turn on"}</button>`);
    L+=row("Timing box", st.connected?(st.faults.length?`<span class="bad">Wiring fault: ${esc(st.faults.join(", "))}</span>`
        :`<span class="ok">Connected · wiring OK</span>`):`<span class="bad">Not connected – plug its USB cable into this computer</span>`, "");
    if(master&&st.firewall&&st.firewall.state!=null) L+=row("Phones", st.firewall.state?`<span class="ok">Windows lets phones connect</span>`:`<span class="bad">Windows is blocking phones${st.firewall.busy?" – answer Yes on the Windows prompt":""}</span>`,
      st.firewall.state||st.firewall.busy?"":`<button class="btn pri" onclick="post('/api/firewall',{}).then(()=>toast('Answer Yes on the Windows prompt'))">Allow phones</button>`);
    L+=row("Events", `<span class="mute">${st.events.filter(e=>e.id).map(e=>esc(e.name)+" "+e.legs).join(" · ")}</span>`, master?`<button class="btn" onclick="eventsSheet()">Edit</button>`:"");
    if(master) L+=row("Results to take home", `<span class="mute">Results spreadsheet, program and race log as a zip file</span>`,
      `<a class="btn" href="/event_pack.zip" download>Today</a>${(st.past_events||[]).length?`<button class="btn" onclick="packSheet()">Saved events</button>`:""}`);
    if(master) L+=row("Problem report", `<span class="mute">If something went wrong, send this file to the kit owner – no passwords in it</span>`,
      `<a class="btn" href="/diagnostics.zip" download>Download</a><button class="btn" onclick="post('/api/diagnostics',{}).then(()=>toast('Checked the USB stick'))">Save to USB</button>`);
    if(master&&st.owner) L+=row("Owner lock", !st.owner.set?`<span class="mute">Off · set an owner PIN before hiring the kit out – it locks updates and advanced settings</span>`
        :st.owner.open?`<b class="okb">Unlocked</b><span class="mute"> · locks again in ${st.owner.mins} min</span>`:`<b>On</b><span class="mute"> · updates and advanced settings are locked</span>`,
      !st.owner.set?`<button class="btn" onclick="ownerSheet('set')">Set PIN</button>`:st.owner.open?`<button class="btn" onclick="ownDo({lock:true},'Locked')">Lock now</button><button class="btn" onclick="ownerSheet('set')">Change PIN</button>`
        :`<button class="btn" onclick="ownerSheet('open')">Unlock</button>`);
    if(master) L+=row("New event", (st.past_events||[]).length?`<span class="mute">Last saved: ${esc(st.past_events[0])}</span>`:`<span class="mute">Saves today, then clears for a fresh start</span>`,
      `<button class="btn red" ${racing?"disabled":""} onclick="askNewEvent()">Start new event</button>`);
    L+=row("Advanced", `<span class="mute">App address, second timing desk phone, your name, hire kit list, timing box messages, restart</span>`,
      `<button class="btn" onclick="advOpen=!advOpen;lastKey='';render()">${advOpen?"Hide ▴":"Show ▾"}</button>`);
    if(advOpen){
      let A="";
      if(master&&st.access&&ownLocked) A+=row("App address, second timing desk phone, restart", `<span class="mute">Locked by the owner</span>`, `<button class="btn" onclick="ownerSheet('open')">Unlock</button>`);
      if(master&&st.access&&!ownLocked) A+=row("App address", `<div class="sin"><input type="text" id="waddr" value="${esc(a.net.addr)}" placeholder="${esc(a.auto_url)}"></div>
          <div class="mute" style="font-size:13px">Empty = ${esc(a.auto_url)} · set it once the router gives this computer a fixed address</div>`,
          `<button class="btn" onclick="offDo({net:{ssid:a_ssid(),pass:a_pass(),addr:$('waddr').value}},'Saved')">Save</button>`)
        +row("Second timing desk phone", `<div class="sin"><input type="text" id="mpin" inputmode="numeric" value="${esc(a.master_pin)}" placeholder="off" style="max-width:140px"></div>
          <div class="mute" style="font-size:13px">A PIN that lets a phone do everything this computer can · empty = off</div>`, `<button class="btn" onclick="offDo({master_pin:$('mpin').value},'Saved')">Save</button>`)
        +(a.regulars&&a.regulars.length?row("Remembered officials", a.regulars.map(r=>`<span class="rchip">${esc(r.name)} · ${ROLE_NAME[r.role]}
          <button class="btn sm" onclick="offDo({forget:'${esc(r.name).replace(/'/g,"")}'},'Forgotten')">✕</button></span>`).join(" "),""):"");
      if(st.local||!st.me) A+=row("Your name", `<div class="sin"><input type="text" id="myname" value="${esc(myName())}" placeholder="Name or initials" style="max-width:200px"></div>`,
        `<button class="btn" onclick="setMyName($('myname').value);toast('Saved');lastKey='';render()">Save</button>`);
      A+=row("Screen", `<span class="mute">${wakeMsg}</span>`, "");
      if(st.connected) A+=row("Timing box messages", `<div class="msgs" style="max-height:120px;overflow:auto">${st.messages.map(m=>esc(m[0]+"  "+m[1])).join("\n")||"—"}</div>`, "");
      if(master) A+=row("Updates key", st.upd_key?`<span class="ok">Set</span><span class="mute"> · updates come from the private repository</span>`
          :`<span class="mute">Not set – only needed once the GitHub repository is private</span>`,
        ownLocked?"":`<button class="btn" onclick="keySheet()">${st.upd_key?"Change":"Add"}</button>${st.upd_key?`<button class="btn" onclick="askYes('Remove the updates key? Updates stop working if the repository is private.',()=>keyDo(''),'Yes, remove')">Remove</button>`:""}`);
      if(master) A+=row("Hire kit list", `<span class="mute">${esc((st.kit||"").split("\n").length)} items · printed with the role guides</span>`, ownLocked?"":`<button class="btn" onclick="kitSheet()">Edit</button>`);
      if(master&&st.connected&&!ownLocked) A+=row("Restart timing program", `<span class="mute">Only if the screen says the timing program stopped – clears any race in progress</span>`,
        `<button class="btn red" onclick="askYes('Restart the timing program in the timing box? Any race in progress is cleared.',()=>cmd('restart'),'Yes, restart')">Restart</button>`);
      A+=row("Versions", `App v${esc(st.app)} · timing box program v${esc(st.fw||"?")}${st.port?" on "+esc(st.port):""}`, "");
      L+=`<div class="sadv">${A}</div>`;
    }
    c=`<div class="card slist">${L}</div>`;
  }
  $("system").innerHTML=h+c;
  const cnt=st.test_count||{};
  if(st.test) document.querySelectorAll(".tests div").forEach(d=>{ const n=d.dataset.t;
    if((cnt[n]||0)>(prevCounts[n]||0)){ d.classList.remove("flash"); void d.offsetWidth; d.classList.add("flash"); } });
  prevCounts=Object.assign({},cnt);
}
let lastKey="";
function pageKey(){
  // redraw only when something shown has changed, so taps and open sections aren't lost
  if(!st) return JSON.stringify([tab,linkDown,tab==="history"?hist:0]);
  const k=[tab,linkDown,st.connected,st.at_prompt,st.state,st.race,st.faults,st.lanes];
  k.push(st.role,st.official,st.test,st.test_seen,st.last_test,st.test_clash,st.confirmed,st.silent,st.practice,st.batt,st.res_flags);
  if(tab==="race") k.push(st.setup_done,st.brand,st.firewall,st.join,wizOpen,joinDone,st.last_test,st.access&&st.access.net,st.sent,st.checkin,st.can_start,st.role,st.program,evOpen,st.live,st.results,st.event,st.race_event,st.min_leg_s,st.app_start,finishAsk,setAsk,st.heat,st.race_heat,st.draw,st.faults_racing,st.raced,
    st.state==="RACING"&&(st.elapsed||0)<5);
  else if(tab==="results") k.push(st.results);
  else if(tab==="history") k.push(hist,queue,enterAsk);
  else if(tab==="program") k.push(prog,st.program,st.draw,st.heat,st.raced);
  else if(tab==="marshal") k.push(mUp,st.heat,st.race_heat);
  else k.push(sysView,dayOpen,updBusy,advOpen,ltOpen,st.upd_key,st.brand,st.owner,st.firewall,st.events,st.kit,st.setup_done,st.past_events,st.update,st.program&&st.program.mode,st.raced,st.port,st.fw,st.messages,st.app,st.draw,st.access,st.join,st.me,wakeMsg,st.test_count,st.test_last,st.backup,st.batt_old);
  return JSON.stringify(k);
}
function brandBar(){ const b=(st&&st.brand)||{}; if(!b.club&&!b.event&&!b.logo) return "";
  return `<div class="brand">${b.logo?`<img src="/logo?v=${b.logo}" alt="">`:""}<span><b>${esc(b.club||"IRB Racing")}</b>${b.event?`<small>${esc(b.event)}</small>`:""}</span></div>`; }
function boardResults(res,title,final){
  // results in finishing order, big enough to read from the marshalling area
  let h=`<div class="top"><div class="now">${esc(title)}</div><span class="pill ${final?"final":"prov"}">${final?"Final":"Provisional"}</span></div><div class="res">`;
  for(const r of ranked(res)){
    const eq=(res.ties||[]).includes(r.lane)?"=":"", cn=crewOf(res.heat,r.lane);
    h+=`<div class="rr ${r.place===1?"first":""}"><span class="pl">${r.place?eq+r.place:"–"}</span><span class="lnno">L${r.lane}</span>
      <span>${esc(cn||"Lane "+r.lane)}</span><span class="tm">${r.place?ft(r.t_us):esc(r.status)}</span></div>`;
  }
  return h+`</div>`;
}
function boardStart(ht,label,pill){
  let h=`<div class="top"><div class="now">${esc(label)}${ht?": "+esc(heatLabel(ht)):""}</div>${pill||""}</div>`;
  if(!ht) return h+`<p class="mute" style="margin:0">Lanes fill in when the officials choose the heat.</p>`;
  h+=`<div class="lanes">`;
  const lanes=new Set(st.lanes.concat(Object.keys(ht.crews||{}).map(Number)));
  for(const l of [...lanes].sort((a,b)=>a-b)){
    const hs=st.state==="RACING"?(st.live[String(l)]||[]):[], cn=crewOf(ht,l), sc=checkOf(ht,l)==="scratched";
    h+=`<div class="ln ${cn&&!sc?"":"empty"}"><b>${l}</b><span>${esc(cn||"—")}${sc?" – scratched":""}</span>${hs.length?`<div class="t">${esc(ft(hs[hs.length-1]))}</div>`:""}</div>`;
  }
  return h+`</div>`;
}
function boardNext(ht){
  if(st&&st.next_break&&st.state!=="RACING"){ const b=st.next_break;
    return `<div class="card" style="margin:0;background:#fff4d6"><h2>Next: ${esc(b.label)}</h2><p style="margin:0;font-size:1.2em;font-weight:800">${b.until?"Racing resumes "+esc(b.until):b.mins?b.mins+" minutes":""}</p></div>`; }
  if(!ht) return "";
  return `<div class="card" style="margin:0"><h2>Next: ${esc(heatLabel(ht))}</h2>${
    Object.entries(ht.crews||{}).sort((a,b)=>a[0]-b[0]).map(([l,c])=>`<div><b>${l}</b> ${esc(c)}</div>`).join("")||`<p class="mute">Not drawn yet.</p>`}</div>`;
}
function renderBoard(){
  if(linkDown||!st.connected) { $("race").innerHTML=banner(); return; }
  const s=st.state;
  let h=`<div class="bd">${brandBar()}`;
  if(s==="DONE"&&st.results){
    // just finished: results first; then whichever heat is up next
    const res=st.results, nextHt=(st.heat&&(!res.heat||st.heat.heat_id!==res.heat.heat_id))?st.heat:(st.next_heats||[])[0];
    h+=`<div class="two"><div>${boardResults(res,res.heat?heatLabel(res.heat):"Race "+res.race,st.confirmed)}</div><div>${boardNext(nextHt)}</div></div>`;
  } else if(s==="RACING"){
    h+=`<div class="two"><div>${boardStart(st.race_heat||st.heat,"Racing",`<span class="pill racing">RACING <span id="clock">${clock(st.elapsed||0)}</span></span>`)}</div><div>${boardNext((st.next_heats||[])[0])}</div></div>`;
  } else {
    // between races: the heat on the start, then the last result
    const last=(hist||[])[0];
    h+=`<div class="two"><div>${boardStart(st.heat,"On the start",s==="ARMED"?`<span class="pill armed">SET</span>`:"")}</div><div style="display:grid;gap:12px">${
      last?`<div class="card" style="margin:0">${boardResults(last,"Last result: "+(last.heat?heatLabel(last.heat):"Race "+last.race),true).replace('class="pill final">Final','class="pill final">Final')}</div>`:""}${boardNext((st.next_heats||[])[0])}</div></div>`;
  }
  $("race").innerHTML=h+`</div>`+boardQr()+homeBtn();
}
function render(){
  if(location.hash==="#team"){ document.body.classList.add("board"); ["results","program","marshal","history","system"].forEach(x=>$(x).hidden=true); $("race").hidden=false;
    const k=JSON.stringify([tmView,tmView==="club"?tmData:tmView==="program"?prog:hist,tmClubs.length,linkDown,st&&st.role,st&&st.brand,tmClub()]); if(k!==lastKey){ lastKey=k; renderTeam(); } return; }
  if(location.hash==="#marshalling"){ document.body.classList.add("board"); ["results","program","marshal","history","system"].forEach(x=>$(x).hidden=true); $("race").hidden=false;
    const k=JSON.stringify([mUp,st&&st.brand,st&&st.next_break,st&&st.heat,st&&st.race_heat,st&&st.state,st&&st.join,linkDown,new Date().getMinutes()]); if(k!==lastKey){ lastKey=k; if(st) renderMBoard(); else $("race").innerHTML=banner(); } return; }
  if(location.hash==="#board"){ document.body.classList.add("board"); ["results","program","marshal","history","system"].forEach(x=>$(x).hidden=true); $("race").hidden=false;
    const k=JSON.stringify([st&&Object.assign({},st,{access:0,elapsed:0}),linkDown,hist]); if(k!==lastKey){ lastKey=k; if(st) renderBoard(); else $("race").innerHTML=banner(); } return; }
  if(st&&st.role==="viewer"&&!st.local){        // phones that aren't officials: the home screen
    document.body.classList.add("board"); ["results","program","marshal","history","system"].forEach(x=>$(x).hidden=true); $("race").hidden=false;
    if(wasWaiting&&!(st.me&&st.me.code)){ wasWaiting=false; toast("Request declined or timed out – ask the timing desk"); }
    if(st.me&&st.me.code) wasWaiting=true;
    const k=JSON.stringify(["home",st.me,linkDown,st.brand]); if(k!==lastKey){ lastKey=k; renderHome(); } return; }
  if(document.body.classList.contains("board")){ document.body.classList.remove("board"); tabRole="";
    ["race","results","program","marshal","history","system"].forEach(s=>$(s).hidden=(s!==tab)); lastKey=""; }
  if(st&&wasWaiting){ wasWaiting=false; justLogged=true; tabRole=""; toast("Approved – "+ROLE_NAME[st.role]); }
  if(st) applyTabs();
  drawNext();
  const sb=$("sbadge"); if(sb&&st){ const n=st.access?st.access.requests.length:0; sb.innerHTML=n?`<span class="badge">${n}</span>`:""; }
  const pb=$("pbadge"); if(pb&&st){ const w=st.program&&(st.program.warn||(st.program.mode==null&&st.official)); pb.innerHTML=w?`<span class="badge">!</span>`:""; }
  const qb=$("qbadge"); if(qb&&st){ const n=st.official?st.queue_n:0; qb.innerHTML=n?`<span class="badge">${n}</span>`:""; }
  const k=pageKey(); if(k===lastKey) return;
  const ae=document.activeElement;      // don't redraw under someone typing (note, name, PIN)
  if(ae&&(ae.tagName==="TEXTAREA"||ae.tagName==="INPUT")&&$(tab)&&$(tab).contains(ae)) return;
  lastKey=k;
  if(tab==="race") renderRace();
  else if(tab==="results") renderResults();
  else if(tab==="program") renderProgram();
  else if(tab==="marshal") renderMarshal();
  else if(tab==="history") renderHistory();
  else renderSystem();
}
async function poll(){
  const stop=new AbortController(), t=setTimeout(()=>stop.abort(),3000);
  try{ const r=await fetch("/api/state",{signal:stop.signal}); st=await r.json(); linkDown=false; }
  catch(e){ linkDown=true; }
  clearTimeout(t);
  if((tab==="history"||location.hash==="#board")&&Date.now()-histAt>3000) await loadHist();
  if(tab==="program"&&st&&(Date.now()-progAt>3000||progState()!==progSeen)) await loadProg();
  if((tab==="marshal"||location.hash==="#marshalling")&&st&&Date.now()-mAt>2500) await loadMarshal();
  if(location.hash==="#team"&&Date.now()-tmAt>5000){ tmAt=Date.now(); if(tmView==="program") await loadProg(); else if(tmView==="results") await loadHist(); else await loadTeam(); }
  if(!holding) render();
  const c=$("clock"); if(c&&st&&!linkDown) c.textContent=clock(st.elapsed||0);
  setTimeout(poll, tab==="race"&&st&&st.state==="RACING"?100:400);
}
poll();
</script></body></html>
"""


def main():
    load_history()
    load_settings()
    load_program()
    load_roles()
    load_templates()
    srv = None
    for _ in range(20):                    # after an update the old copy may need a moment to let go
        try:
            srv = ThreadingHTTPServer(("0.0.0.0", HTTP_PORT), H)
            break
        except OSError:
            time.sleep(0.5)
    if not srv:
        print("Port %d is already in use - is the app already running in another window?" % HTTP_PORT)
        if not os.environ.get("IRB_LAUNCHER"):
            input("Press Enter to close...")
        sys.exit(1)
    threading.Thread(target=update_check, daemon=True).start()       # quietly see if there's a newer version
    threading.Thread(target=firewall_check, daemon=True).start()     # Windows: can phones get in?
    ip = lan_ip()
    print("IRB officials' app v%s" % APP_VERSION)
    print("  On this computer:  http://localhost:%d" % HTTP_PORT)
    if ip:
        print("  On a tablet/phone on the same Wi-Fi:  http://%s:%d" % (ip, HTTP_PORT))
    print("  Results are saved in:", DATA)
    print("  Close Thonny so the app can talk to the Pico. Press Ctrl+C here to stop the app.")
    threading.Thread(target=serial_loop, daemon=True).start()
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        print("Stopped.")


if __name__ == "__main__":
    main()
