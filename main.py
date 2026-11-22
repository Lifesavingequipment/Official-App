# IRB Finish Timing - bench test v3.3
# v3.3: hold FINISH for 15 s between races (not in a race or button test) = clear the app's timing desk
#       PIN, so a kit with a forgotten PIN never needs opening. Three long beeps confirm it.
# v3.2: lane lights ignore button bounce (one light action per press, 1 s apart) and flash slower.
# v3.1: lane lights: off between races; a press before the race flashes that light twice (button check);
#       in the race a counted press turns it on for 10 s, a press while it's on flashes it off then on
#       for another 10 s. GO: siren and all lights on together for 1 s. FINISH: lights off, 2 beeps.
# v3.0: "minleg N" command - the app shortens the gap between a crew's presses for practice (1 s),
#       and puts it back to 15 s for racing. Always starts at 15 s.
# v2.9: a press only counts if its pin is still open 2 ms after the edge - short electrical
#       spikes (one lane's wire kicking another's) are ignored. Timing still uses the first edge.
# v2.8: the app sets the Pico's clock on connect
#       (clock Y M D h m s), so history dates are right without Thonny. A heartbeat
#       line every 3 s lets the app spot a dead link. Optional 24 V battery reading
#       on GP26 through a 100k/10k divider (set BATT_ENABLED = True once wired).
# v2.7: button test mode (test on / test off): every button just reports itself,
#       nothing arms or finishes. Dead heats: tie 3 = lane 3 equal place with the
#       crew ahead (next place skipped, SLSA 2.24). A lane cable that opens during a
#       race (held open over 2 s) is reported straight away.
# v2.6: SET and GO can also come from the officials' app (or typed: set / go).
#       The physical SET and GO buttons work exactly as before.
#       GO again within 5 s (button, app or typed) = RECALL, as before.
# v2.5: also sends machine-readable lines starting with @ (JSON) for the
#       officials' app on the laptop / Pi. Thonny users can ignore them.
#       Shell: j = send full status to the app.
# v2.4: race history saved on the Pico (rolling). Every finished race, every
#       officials' change and every recall is added to hist_NNNN.csv files.
#       50 races per file, newest 10 files kept (about 500 races); the oldest
#       file is deleted when full. Nothing is written during a race, so timing
#       is never disturbed. Download: Thonny > View > Files > right-click > Download.
#       Shell: log = list history files.
# v2.3: officials can adjust results after FINISH (type into the shell):
#       ok 2       accept lane 2 - missed a mid-race press, last press = finish
#       place 2 3  put lane 2 in 3rd place (no time needed)
#       dq 2 / dnf 2   disqualify / did not finish
#       legs 2     set the race to 2 legs (if the automatic count is wrong)
#       clear 2    remove changes for lane 2   (clear = remove all changes)
#       p          print results again
# v2.2: repeat hits inside 15 s re-blink the lane light (confirmation, not counted).
# v2.1: extended clock - races of any length (no 8.9 min timer limit).
# Raspberry Pi Pico H, MicroPython
#
# v2.0: automatic legs.
#   SET -> GO -> crews hit their button as many times as the race needs ->
#   official presses FINISH (hold 1 s). Every hit at least MIN_LEG (15 s) after
#   that crew's last hit (or after GO) counts as a leg. At FINISH the number of
#   legs is taken from what most crews did; crews short of it = INCOMPLETE.
#   SET is locked while a race is running, until FINISH is pressed.
#
# Works with jumper wires now and the DST-1R4P NPN opto board + NC buttons later.
#   Jumper test: lanes/SET/GO jumpered to GND = idle. Pull out = hit.
#   FINISH (pin 6): NOT jumpered at rest. Touch to GND for 1 s = FINISH.
#
# Pins:
#   GP2 lane 1, GP3 lane 2, GP4 SET, GP5 GO   (inputs, NC via opto board)
#   GP6 FINISH                               (input, NO straight to GND)
#   GP10 siren, GP11 lane 1 light, GP12 lane 2 light (outputs)
#
# Shell commands (type, then Enter): f = finish race, s = status, h = help, set, go
#   after FINISH: ok, place, dq, dnf, clear, p  (see v2.3 above)

from machine import Pin, ADC, RTC
import time, sys, uselect, array, micropython, os, json

micropython.alloc_emergency_exception_buf(100)

# ---------------- Settings ----------------
BOARD_NPN = True              # True: DST-1R4P (NPN) or jumper test. False: PNP board.
MIN_LEG_US = 15_000_000       # a hit only counts if 15 s after that crew's last hit / GO
MIN_LEG_RACING = MIN_LEG_US   # "minleg race" puts this back after practice
DEAD_HEAT_US = 10_000         # finishes closer than 10 ms flagged for review
BUTTON_DEBOUNCE_US = 300_000  # SET/GO ignore repeat edges within 0.3 s
CONFIRM_US = 2_000            # a press must still be open this long after its edge to count
CONFIRM_MAX_US = 30_000       # ...checked for up to this long (contact bounce), then it's ignored as a spike
RECALL_WINDOW_US = 5_000_000  # GO again within 5 s = recall
SET_TIMEOUT_MS = 60_000       # SET expires after 60 s without GO
REARM_MS = 200                # SET/GO must be steadily released before another press counts
FINISH_HOLD_MS = 1000         # FINISH must be held this long
PIN_RESET_MS = 15_000         # FINISH held this long between races = clear the app's timing desk PIN
MAX_RACE_MS = 1_200_000       # auto-finish after 20 min if FINISH is forgotten
HIT_BLINK_MS = 400            # lane light blinks off this long on each hit
LIGHT_HOLD_MS = 10_000        # in a race, a lane light stays on this long after a press
CHECK_FLASH_MS = 500          # before a race, a press flashes the light twice (on/off this long)
FLASH_OFF_MS = 700            # in a race, a press while the light is on: off this long, then on again
LIGHT_GAP_MS = 1000           # light ignores further edges from the same lane for this long (button bounce)
FAULT_CHECK_MS = 500
RACE_FAULT_MS = 2000          # lane input held open this long during a race = cable fault
TEST_TIMEOUT_MS = 300_000     # button test switches itself off after 5 min
BEAT_MS = 3000                # heartbeat to the app
BATT_ENABLED = False          # True once the battery divider is wired to GP26
BATT_PIN = 26                 # ADC0
BATT_DIVIDER = 11.0           # (100k + 10k) / 10k - adjust to match a multimeter
BATT_MS = 10_000              # read the battery every 10 s (not during a race)
HIST_RACES_PER_FILE = 50      # races per history file
HIST_MAX_FILES = 10           # files kept (oldest deleted) = about 500 races
HIST_MIN_FREE = 150_000       # also delete oldest files if free space drops below this

LANE_PINS = {1: 2, 2: 3}      # lane number : GPIO
SET_PIN = 4
GO_PIN = 5
FINISH_PIN = 6
SIREN_PIN = 10
LIGHT_PINS = {1: 11, 2: 12}
# ------------------------------------------

HIT = 1 if BOARD_NPN else 0
PULL = Pin.PULL_UP if BOARD_NPN else Pin.PULL_DOWN
TRIG = Pin.IRQ_RISING if BOARD_NPN else Pin.IRQ_FALLING

CODE_SET = 101
CODE_GO = 102

led = Pin("LED", Pin.OUT, value=0)
siren = Pin(SIREN_PIN, Pin.OUT, value=0)
lights = {n: Pin(p, Pin.OUT, value=0) for n, p in LIGHT_PINS.items()}

# ---- Interrupt event buffer (no memory allocation inside the interrupt) ----
BUF = 64
ev_code = array.array('i', [0] * BUF)
ev_time = array.array('I', [0] * BUF)
head = 0
tail = 0


def make_irq(code):
    def handler(pin):
        global head
        i = head % BUF
        ev_time[i] = time.ticks_us()
        ev_code[i] = code
        head += 1
    return handler


lane_in = {}
for lane, gp in LANE_PINS.items():
    p = Pin(gp, Pin.IN, PULL)
    p.irq(handler=make_irq(lane), trigger=TRIG, hard=True)
    lane_in[lane] = p

set_in = Pin(SET_PIN, Pin.IN, PULL)
set_in.irq(handler=make_irq(CODE_SET), trigger=TRIG, hard=True)
go_in = Pin(GO_PIN, Pin.IN, PULL)
go_in.irq(handler=make_irq(CODE_GO), trigger=TRIG, hard=True)
finish_in = Pin(FINISH_PIN, Pin.IN, Pin.PULL_UP)   # pressed = 0

# ---------------- Helpers ----------------


def fmt(us):
    if us < 0:
        return "-" + fmt(-us)
    return "%d.%06d" % (us // 1_000_000, us % 1_000_000)


def set_lights(v):
    light_seq.clear()                 # anything switched on purpose cancels the lane timers
    for l in lights.values():
        l.value(v)


light_seq = {}      # lane -> [(at_ms, 0/1), ...] steps still to do (non-blocking light timers)
light_last = {}     # lane -> when its light last reacted to a press


def light_bounce(lane):
    # True if this edge is the same press bouncing (or a press too soon after the last one)
    now = time.ticks_ms()
    if lane in light_last and time.ticks_diff(now, light_last[lane]) < LIGHT_GAP_MS:
        return True
    light_last[lane] = now
    return False


def light_plan(lane, steps):
    # steps: [(ms from now, 0/1), ...] - the first one usually at 0
    now = time.ticks_ms()
    light_seq[lane] = [(time.ticks_add(now, ms), v) for ms, v in steps]
    run_lights(now)


def run_lights(now):
    for lane in list(light_seq):
        seq = light_seq[lane]
        while seq and time.ticks_diff(now, seq[0][0]) >= 0:
            lights[lane].value(seq.pop(0)[1])
        if not seq:
            del light_seq[lane]


def lane_light_hit(lane):
    # in a race: on for 10 s; if it's already on, flash off then on for another 10 s
    if lane not in lights or light_bounce(lane):
        return
    if lights[lane].value():
        light_plan(lane, [(0, 0), (FLASH_OFF_MS, 1), (FLASH_OFF_MS + LIGHT_HOLD_MS, 0)])
    else:
        light_plan(lane, [(0, 1), (LIGHT_HOLD_MS, 0)])


def lane_light_check(lane):
    # before or after a race: two quick flashes to show the button and light work
    if lane not in lights or lane in light_seq or light_bounce(lane):
        return
    f = CHECK_FLASH_MS
    light_plan(lane, [(0, 1), (f, 0), (2 * f, 1), (3 * f, 0)])


def beep(on_ms, off_ms, count, flash=False):
    for _ in range(count):
        siren.on()
        if flash:
            set_lights(1)
        time.sleep_ms(on_ms)
        siren.off()
        if flash:
            set_lights(0)
        time.sleep_ms(off_ms)


def go_signal():
    # siren and every lane light on together for 1 s (also the camera sync), then off
    siren.on()
    set_lights(1)
    time.sleep_ms(1000)
    set_lights(0)
    siren.off()


def faults():
    bad = []
    for lane, p in lane_in.items():
        if p.value() == HIT:
            bad.append("Lane %d" % lane)
    if set_in.value() == HIT:
        bad.append("SET")
    if go_in.value() == HIT:
        bad.append("GO")
    return bad


def show_help():
    print("SET -> GO -> crews hit button each leg -> FINISH (hold 1 s).")
    print("Hits under %d s after a crew's last hit are ignored." % (MIN_LEG_US // 1_000_000))
    print("Shell: f = finish race, s = status, h = help  (then Enter)")
    print("       set / go = SET and GO without the buttons (go again within 5 s = recall)")
    print("After FINISH, officials can adjust:")
    print("  ok 2       lane 2 missed a mid-race press - use their last press as finish")
    print("  place 2 3  put lane 2 in 3rd place (no time needed)")
    print("  dq 2       disqualify lane 2      dnf 2   lane 2 did not finish")
    print("  legs 2     race was 2 legs (if the automatic leg count is wrong)")
    print("  clear 2    undo changes for lane 2 (clear = undo all)    p = print results")
    print("  tie 3      dead heat: lane 3 gets the same place as the crew ahead")
    print("test on / test off = button test (each button reports itself, nothing starts)")
    print("clock Y M D h m s = set the clock (the officials' app does this itself)")
    print("log = list saved history files (download them from Thonny's Files view)")
    print("Jumper test: lanes/SET/GO jumpered to GND = idle, pull out = hit.")
    print("FINISH: touch pin 6 to GND for 1 s.")


# ---- Extended microsecond clock ----
# ticks_us wraps every ~17.9 min; this keeps a never-wrapping count so races
# of any length time correctly. Event stamps are converted as they are read.
clk_raw = time.ticks_us()
clk_ext = 0


def clock_now():
    global clk_raw, clk_ext
    r = time.ticks_us()
    clk_ext += time.ticks_diff(r, clk_raw)
    clk_raw = r
    return clk_ext


def to_ext(raw):
    # raw IRQ stamp (from the last few seconds) -> extended clock
    return clk_ext + time.ticks_diff(raw, clk_raw)


# ---------------- Messages for the officials' app ----------------
# One line each: @ followed by JSON. Times are whole microseconds (integers),
# because the Pico's floats are not precise enough for long races.
def emit(d):
    print("@" + json.dumps(d))


def announce():
    emit({"ev": "state", "state": state, "race": race_no})


def place_map(order):
    # place for each crew in finishing order; a tied crew shares the place of the crew
    # ahead and the next place is skipped (1, 2, 2, 4)
    pm = {}
    for i, lane in enumerate(order):
        pm[lane] = pm[order[i - 1]] if (i and lane in ties) else i + 1
    return pm


def results_data():
    legs = race_legs()
    order = final_order(legs) if (legs or adj) else []
    pm = place_map(order)
    rows = []
    for lane in sorted(hits):
        ft = finish_time(lane, legs) if lane in order else None
        rows.append({"lane": lane,
                     "place": pm.get(lane),
                     "t_us": ft,
                     "status": lane_status(lane, order, legs),
                     "presses_us": [x - t0 for x in hits[lane]]})
    ch = {}
    for lane, a in adj.items():
        ch[str(lane)] = ("place %d" % a[1]) if isinstance(a, tuple) else a
    for lane in ties:
        k = str(lane)
        ch[k] = (ch[k] + ", dead heat") if k in ch else "dead heat"
    return {"ev": "results", "race": race_no, "version": version, "legs": legs,
            "legs_set": legs_set, "rows": rows, "changes": ch, "ties": sorted(ties)}


def emit_all():
    emit({"ev": "hello", "fw": "3.3", "pin_reset": True, "lanes": sorted(LANE_PINS), "race": race_no,
          "min_leg_s": MIN_LEG_US // 1_000_000, "minleg_cmd": True, "app_start": True, "ties": True, "test": True,
          "clock": True, "beat": True, "batt": BATT_ENABLED})
    emit({"ev": "test", "on": test_mode})
    announce()
    emit({"ev": "faults", "list": faults()})
    if state == "RACING":
        emit({"ev": "running", "elapsed_us": clock_now() - t0,
              "hits": {str(l): [x - t0 for x in h] for l, h in hits.items()}})
    if state == "DONE":
        emit(results_data())


# ---------------- Race history (rolling, on the Pico's flash) ----------------
# CSV columns: race,version,date_time,type,lane,place,time_s,status,presses_s,note
#   type RACE   = one per race (note: legs and how it ended), version 0
#   type RESULT = one per lane; version 0 = timing as recorded,
#                 1, 2... = full results again after each officials' change
#   type CHANGE = the officials' command that made that version
# For a race, the RESULT rows with the highest version are the final result.
# The date/time is real only if Thonny set the Pico's clock (it does on connect).
HIST_HEAD = "race,version,date_time,type,lane,place,time_s,status,presses_s,note\n"


def hist_files():
    out = []
    for f in os.listdir():
        if f.startswith("hist_") and f.endswith(".csv"):
            try:
                out.append(int(f[5:-4]))
            except ValueError:
                pass
    out.sort()
    return out


def hist_name(i):
    return "hist_%04d.csv" % i


def hist_last_race():
    files = hist_files()
    if not files:
        return 0
    last = 0
    try:
        with open(hist_name(files[-1])) as fh:
            for ln in fh:
                c = ln.split(",", 1)[0]
                if c.isdigit():
                    last = int(c)
    except OSError:
        pass
    if last == 0:
        last = (files[-1] - 1) * HIST_RACES_PER_FILE
    return last


def free_bytes():
    st = os.statvfs("/")
    return st[0] * st[3]


def stamp():
    y, mo, d, h, mi, sec = time.localtime()[:6]
    return "%04d-%02d-%02d %02d:%02d:%02d" % (y, mo, d, h, mi, sec)


def hist_write(rows):
    # rows: list of lists (already in column order). Never called while RACING.
    try:
        idx = (race_no - 1) // HIST_RACES_PER_FILE + 1
        name = hist_name(idx)
        files = hist_files()
        new = idx not in files
        if new:
            for old in files:
                if old <= idx - HIST_MAX_FILES:
                    os.remove(hist_name(old))
            files = hist_files()
            while free_bytes() < HIST_MIN_FREE and files and files[0] != idx:
                os.remove(hist_name(files.pop(0)))
        with open(name, "a") as fh:
            if new:
                fh.write(HIST_HEAD)
            for r in rows:
                fh.write(",".join(str(x) for x in r) + "\n")
    except OSError as e:
        print("HISTORY NOT SAVED (", e, ") - copy results from the shell.")


def lane_status(lane, order, legs):
    a = adj.get(lane)
    n = len(hits[lane])
    if lane in order:
        if isinstance(a, tuple):
            return "PLACED"
        if a == "ok" and n < legs:
            return "ACCEPTED"
        return "TIMED"
    if a == "dq":
        return "DQ"
    if a == "dnf" or n == 0:
        return "DNF"
    return "INCOMPLETE"


def hist_results(version, change=None):
    legs = race_legs()
    order = final_order(legs) if (legs or adj) else []
    ts = stamp()
    rows = []
    if version == 0:
        rows.append([race_no, 0, ts, "RACE", "", "", "", "", "",
                     "%d legs; %s" % (legs, end_reason)])
    else:
        rows.append([race_no, version, ts, "CHANGE", "", "", "", "", "", change])
    pm = place_map(order)
    for lane in sorted(hits):
        place = pm.get(lane, "")
        ft = finish_time(lane, legs) if lane in order else None
        presses = ";".join(fmt(x - t0) for x in hits[lane])
        rows.append([race_no, version, ts, "RESULT", lane, place,
                     fmt(ft) if ft is not None else "",
                     lane_status(lane, order, legs), presses, ""])
    hist_write(rows)


def show_log():
    files = hist_files()
    if not files:
        print("No history saved yet.")
    for i in files:
        print("  %s   %d bytes" % (hist_name(i), os.stat(hist_name(i))[6]))
    print("Last race number: %d.  Free space: %d KB" % (race_no, free_bytes() // 1024))
    print("Download: Thonny > View > Files > right-click the file > Download")


# ---------------- Race state ----------------
state = "IDLE"      # IDLE, ARMED, RACING, DONE
armed_at_ms = 0
go_at_ms = 0
t0 = 0
hits = {lane: [] for lane in LANE_PINS}
legs_set = 0        # officials' leg count (0 = automatic)
race_no = hist_last_race()   # carries on from the saved history
version = 0         # officials' change count for the current race
end_reason = ""
adj = {}            # officials' changes: lane -> "ok" | "dq" | "dnf" | ("place", n)
ties = set()        # lanes given an equal place with the crew ahead (dead heat)
test_mode = False   # button test: inputs only report themselves
test_until = 0
test_last = {}      # input name -> ticks_ms of last report (ignores bounce)
held_since = {}     # lane -> ticks_ms its input went open during a race
race_faults = []    # lanes reported as cable faults this race
last_set_us = -10_000_000
last_go_us = -10_000_000
last_fault_report = None
set_ready = True
go_ready = True
set_idle_since = None
go_idle_since = None
finish_down_since = None
finish_fired = False
finish_down_state = None      # race state when FINISH went down (a reset must start between races)
reset_fired = False


def reset_race():
    global hits, adj, legs_set, ties, race_faults, held_since
    hits = {lane: [] for lane in LANE_PINS}
    adj = {}
    ties = set()
    legs_set = 0
    race_faults = []
    held_since = {}
    set_lights(0)
    siren.off()


def race_legs():
    # officials' setting, else most common hit count among crews that hit; ties -> higher
    if legs_set:
        return legs_set
    counts = [len(h) for h in hits.values() if h]
    if not counts:
        return 0
    best, best_n = 0, -1
    for c in counts:
        n = counts.count(c)
        if n > best_n or (n == best_n and c > best):
            best, best_n = c, n
    return best


def finish_time(lane, legs):
    # elapsed finish time from presses, or None if no usable finish press
    h = hits[lane]
    a = adj.get(lane)
    if legs and len(h) >= legs:
        return h[legs - 1] - t0
    if a == "ok" and h:
        return h[-1] - t0
    return None


def final_order(legs):
    # 1. crews with a usable time, sorted by time (officials' "place" crews left out)
    timed = []
    for lane in hits:
        a = adj.get(lane)
        if a in ("dq", "dnf") or isinstance(a, tuple):
            continue
        if (legs and len(hits[lane]) >= legs) or (a == "ok" and hits[lane]):
            timed.append((finish_time(lane, legs), lane))
    timed.sort()
    order = [lane for _, lane in timed]
    # 2. insert crews placed by officials at their place
    placed = sorted((a[1], lane) for lane, a in adj.items() if isinstance(a, tuple))
    for n, lane in placed:
        order.insert(min(n - 1, len(order)), lane)
    return order


def print_results():
    legs = race_legs()
    if legs == 0 and not adj:
        print("----- RESULTS -----")
        print("No hits recorded. All lanes DNF.")
        print("  (officials can still type: place <lane> <place>)")
        print("-------------------")
        print("Press SET for the next race.")
        return

    head = "RESULTS (%d leg%s)" % (legs, "" if legs == 1 else "s")
    if adj or legs_set:
        head += " - ADJUSTED BY OFFICIALS"
    print("----- %s -----" % head)
    order = final_order(legs)
    pm = place_map(order)
    prev = None
    for lane in order:
        place = pm[lane]
        a = adj.get(lane)
        is_placed = isinstance(a, tuple)
        total = finish_time(lane, legs)
        if total is None:
            print("%d.  Lane %d   no time   (placed by officials)" % (place, lane))
            prev = None
            continue
        line = "%d.  Lane %d   %s s" % (place, lane, fmt(total))
        if lane in ties and lane != order[0]:
            line += "   DEAD HEAT (officials)"
        if is_placed:
            line += "   (placed by officials)"
        elif prev is not None:
            gap = total - prev
            line += "   +%s s" % fmt(gap)
            if gap < DEAD_HEAT_US:
                line += "   <<< TOO CLOSE - REVIEW"
        print(line)
        n = len(hits[lane])
        if a == "ok" and n < legs:
            print("      accepted by officials - %d of %d presses, no splits" % (n, legs))
        elif legs > 1:
            times = [x - t0 for x in hits[lane][:legs]]
            parts = []
            last = 0
            for i, tt in enumerate(times, 1):
                parts.append("leg %d %s" % (i, fmt(tt - last)))
                last = tt
            print("      " + "   ".join(parts))
        if n > legs:
            print("      CHECK: %d hits recorded, only %d used" % (n, legs))
        prev = None if is_placed else total

    for lane in sorted(hits):
        if lane in order:
            continue
        a = adj.get(lane)
        n = len(hits[lane])
        if a == "dq":
            print("    Lane %d   DQ (officials)" % lane)
        elif a == "dnf":
            print("    Lane %d   DNF (officials)" % lane)
        elif n == 0:
            print("    Lane %d   DNF" % lane)
        else:
            print("    Lane %d   INCOMPLETE - %d of %d legs   (officials: ok %d  or  place %d <place>)"
                  % (lane, n, legs, lane, lane))

    counts = [len(h) for h in hits.values() if h]
    if counts and min(counts) != max(counts):
        print("NOTE: crews have different hit counts - referee check.")
    if adj or legs_set:
        print("Officials' changes:")
        if legs_set:
            print("  Race set to %d leg%s" % (legs_set, "" if legs_set == 1 else "s"))
        for lane in sorted(adj):
            a = adj[lane]
            if a == "ok":
                txt = "accepted - missed a press, last press used as finish"
            elif a == "dq":
                txt = "disqualified"
            elif a == "dnf":
                txt = "did not finish"
            else:
                txt = "placed %d" % a[1]
            print("  Lane %d: %s" % (lane, txt))
    print("-------------------")
    print("Press SET for the next race.")


def set_test(on):
    global test_mode, test_until
    if on and state not in ("IDLE", "DONE"):
        print("Button test only between races.")
        return
    test_mode = on
    test_until = time.ticks_add(time.ticks_ms(), TEST_TIMEOUT_MS)
    set_lights(1 if on else 0)
    print("BUTTON TEST ON - press each button once. Nothing will start." if on else "Button test off.")
    emit({"ev": "test", "on": on})


TEST_CLASH_US = 250_000       # two different buttons this close together in the test = wiring problem
test_prev = None              # (name, time) of the last button seen in the test


def test_input(name, lane=None, t=None):
    global test_prev
    if t is None:
        t = clock_now()
    # two different inputs going off together: a short, crossed wires or a shared cable fault
    if test_prev and test_prev[0] != name and t - test_prev[1] < TEST_CLASH_US:
        gap = (t - test_prev[1]) // 1000
        print("TEST PROBLEM: %s and %s went off %d ms apart - check for a short or crossed wires"
              % (test_prev[0], name, gap))
        emit({"ev": "clash", "a": test_prev[0], "b": name, "ms": gap})
    test_prev = (name, t)
    now = time.ticks_ms()
    if time.ticks_diff(now, test_last.get(name, now - 10_000)) < 300:
        return
    test_last[name] = now
    print("TEST: %s OK" % name)
    emit({"ev": "input", "name": name})
    if lane in lights:                     # test: lights stay on; a press blinks it off
        light_plan(lane, [(0, 0), (HIT_BLINK_MS, 1)])


def set_clock(w):
    try:
        y, mo, d, h, mi, s = [int(x) for x in w[1:7]]
        RTC().datetime((y, mo, d, 0, h, mi, s, 0))
        print("Clock set:", stamp())
    except (ValueError, IndexError):
        print("Use: clock 2026 11 10 14 30 00")


batt_adc = ADC(BATT_PIN) if BATT_ENABLED else None


def read_batt():
    # average a few readings; volts at the battery
    tot = 0
    for _ in range(8):
        tot += batt_adc.read_u16()
    return round(tot / 8 / 65535 * 3.3 * BATT_DIVIDER, 2)


def command(line):
    global adj, legs_set, version, ties, MIN_LEG_US
    w = line.strip().lower().split()
    if not w:
        return
    c = w[0]
    if c == "test":
        set_test(len(w) > 1 and w[1] == "on")
        return
    if c == "clock":
        set_clock(w)
        return
    if c == "minleg":                       # gap between a crew's counted presses, in seconds
        try:
            MIN_LEG_US = MIN_LEG_RACING if w[1] == "race" else max(1, min(60, int(w[1]))) * 1_000_000
        except (IndexError, ValueError):
            print("Give seconds, e.g.  minleg 1   (or  minleg race  for the racing gap)")
            return
        n = MIN_LEG_US // 1_000_000
        print("Presses under %d s after a crew's last press are ignored." % n)
        emit({"ev": "minleg", "s": n if MIN_LEG_US >= 1_000_000 else 1})
        return
    if test_mode and c in ("f", "r", "set", "go"):
        print("Button test is running - type  test off  first.")
        return
    if c in ("f", "r"):
        finish_race()
        return
    if c == "s":
        status()
        return
    if c == "h":
        show_help()
        return
    if c == "log":
        show_log()
        return
    if c == "j":
        emit_all()
        return
    if c == "set":
        handle_set(clock_now(), app=True)
        return
    if c == "go":
        handle_go(clock_now(), app=True)
        return
    if c not in ("ok", "place", "dq", "dnf", "clear", "p", "legs", "tie"):
        print("Unknown command '%s'. Type h for help." % line.strip())
        return
    if state != "DONE":
        print("Adjustments are only possible after FINISH.")
        return
    if c == "p":
        print_results()
        emit(results_data())
        return
    before = (dict(adj), legs_set, set(ties))
    if c == "legs":
        try:
            n = int(w[1])
        except (IndexError, ValueError):
            print("Give the number of legs, e.g.  legs 2")
            return
        if n < 1 or n > 10:
            print("Legs must be 1 to 10.")
            return
        legs_set = n
        changed(line, before)
        return
    if c == "clear" and len(w) == 1:
        adj = {}
        ties = set()
        legs_set = 0
        print("All officials' changes removed.")
        changed(line, before)
        return
    try:
        lane = int(w[1])
    except (IndexError, ValueError):
        print("Give a lane number, e.g.  %s 2" % c)
        return
    if lane not in hits:
        print("No lane %d." % lane)
        return
    if c == "clear":
        adj.pop(lane, None)
        ties.discard(lane)
        print("Lane %d changes removed." % lane)
    elif c == "tie":
        order = final_order(race_legs())
        if lane not in order or order.index(lane) == 0:
            print("Lane %d has no crew ahead of it to tie with." % lane)
            return
        ties.add(lane)
    elif c == "ok":
        if not hits[lane]:
            print("Lane %d has no presses to use. Use:  place %d <place>" % (lane, lane))
            return
        adj[lane] = "ok"
    elif c == "place":
        try:
            n = int(w[2])
        except (IndexError, ValueError):
            print("Give lane and place, e.g.  place 2 3")
            return
        if n < 1 or n > len(hits):
            print("Place must be 1 to %d." % len(hits))
            return
        adj[lane] = ("place", n)
    else:
        adj[lane] = c          # "dq" or "dnf"
    changed(line, before)


def changed(line, before):
    global version
    print_results()
    if (adj, legs_set, ties) == before:
        return
    version += 1
    emit(results_data())
    hist_results(version, line.strip().lower())
    print("(change saved to history for race %d)" % race_no)


def status():
    print("State:", state)
    f = faults()
    print("Faults:", ", ".join(f) if f else "none")
    for lane, p in lane_in.items():
        print("  Lane %d pin %d (%s), hits this race: %d" % (
            lane, p.value(), "HIT/OPEN" if p.value() == HIT else "idle", len(hits[lane])))
    print("  SET pin %d, GO pin %d, FINISH pin %d (%s)" % (
        set_in.value(), go_in.value(), finish_in.value(),
        "pressed" if finish_in.value() == 0 else "not pressed"))


def handle_set(t, app=False):
    # app=True: from the officials' app / shell, so no button bounce to ignore
    global state, armed_at_ms, last_set_us, set_ready
    if not app and (not set_ready or t - last_set_us < BUTTON_DEBOUNCE_US):
        return
    last_set_us = t
    if not app:
        set_ready = False
    if state == "RACING":
        print("SET locked - race running. Press FINISH first.")
        return
    if state == "ARMED":
        return
    f = [x for x in faults() if x != "SET"]
    if f:
        print("START BLOCKED - fault on:", ", ".join(f))
        return
    reset_race()
    state = "ARMED"
    armed_at_ms = time.ticks_ms()
    led.on()
    print("SET - race armed. Waiting for GO.")
    announce()
    beep(150, 150, 3)


def handle_go(t, app=False):
    global state, t0, go_at_ms, last_go_us, go_ready, race_no, last_fault_report
    if not app and (not go_ready or t - last_go_us < BUTTON_DEBOUNCE_US):
        return
    last_go_us = t
    if not app:
        go_ready = False
    if state == "ARMED":
        t0 = t
        go_at_ms = time.ticks_ms()
        state = "RACING"
        print("GO!  (race clock started)")
        announce()
        go_signal()
    elif state == "RACING" and t - t0 < RECALL_WINDOW_US:
        print("RECALL - race cancelled.")
        beep(100, 100, 6, flash=True)
        race_no += 1
        hist_write([[race_no, 0, stamp(), "RACE", "", "", "", "RECALL", "",
                     "recalled %s s after GO - not raced" % fmt(t - t0)]])
        reset_race()
        state = "IDLE"
        last_fault_report = None
        led.off()
        emit({"ev": "recall", "race": race_no})
        announce()
    elif state in ("IDLE", "DONE"):
        print("GO ignored - press SET first.")


def handle_lane(lane, t):
    if state != "RACING":
        lane_light_check(lane)            # before / after a race: flash to show it works
        return
    prev = hits[lane][-1] if hits[lane] else t0
    if t - prev < MIN_LEG_US:
        # under 15 s since last hit / GO: not counted.
        # If this crew already has a counted hit, flash again as confirmation.
        if hits[lane]:
            lane_light_hit(lane)
        return
    hits[lane].append(t)
    n = len(hits[lane])
    emit({"ev": "hit", "lane": lane, "n": n, "t_us": t - t0})
    el = t - t0
    if n == 1:
        print("Lane %d hit 1   %s s" % (lane, fmt(el)))
    else:
        leg = t - prev
        print("Lane %d hit %d   %s s   (leg %d: %s s)" % (lane, n, fmt(el), n, fmt(leg)))
    # light: on for 10 s (or flash off/on if it's still on), so the crew sees each hit register
    lane_light_hit(lane)


def finish_race(reason="Race finished by official."):
    global state, race_no, version, end_reason, last_fault_report
    if state == "RACING":
        last_fault_report = None      # report the wiring state again after every race
        state = "DONE"
        led.off()
        set_lights(0)                     # race over: lights off, two beeps
        beep(200, 200, 2)
        race_no += 1
        version = 0
        end_reason = "auto-finished 20 min" if "auto" in reason else "finished by official"
        print("Race %d. %s" % (race_no, reason))
        print_results()
        hist_results(0)
        print("(saved to history as race %d)" % race_no)
        announce()
        emit(results_data())
    elif state == "ARMED":
        state = "IDLE"
        led.off()
        reset_race()
        print("Cancelled before GO. Press SET to arm a race.")
        announce()
    else:
        print("No race running. Press SET to arm a race.")


# ---------------- Main loop ----------------
poller = uselect.poll()
poller.register(sys.stdin, uselect.POLLIN)

print("IRB finish timing - bench test v3.3 (legs, adjustments, history, app link, test, ties, clock)")
print("History: last saved race %d. Type log to see files." % race_no)
emit_all()
print("Board:", "NPN (hit = pin goes HIGH)" if BOARD_NPN else "PNP (hit = pin goes LOW)")
show_help()
status()

pending = []        # edges being checked (press or spike?)
spikes = {}         # input code -> spikes ignored since the last report
last_spike_report = time.ticks_ms()
last_check = time.ticks_ms()
last_blink = time.ticks_ms()
last_beat = time.ticks_ms()
last_batt = time.ticks_ms() - BATT_MS
line = ""

while True:
    # 1. process interrupt events in order (stamps converted to extended clock)
    clock_now()
    # every edge is checked on its own: it counts if its pin is seen open 2 ms or more after the edge,
    # and is dropped as a spike if that hasn't happened within 30 ms. Then they're handled in order.
    while tail != head:
        i = tail % BUF
        pending.append([ev_code[i], ev_time[i], 0])     # code, edge time, 0 = checking / 1 = press / 2 = spike
        tail += 1
    if pending:
        now_us = time.ticks_us()
        for e in pending:
            if e[2] == 0:
                p = set_in if e[0] == CODE_SET else go_in if e[0] == CODE_GO else lane_in.get(e[0])
                age = time.ticks_diff(now_us, e[1])
                if p is None or (age >= CONFIRM_US and p.value() == HIT):
                    e[2] = 1
                elif age >= CONFIRM_MAX_US:
                    e[2] = 2
    while pending and pending[0][2]:
        code, raw, ok = pending.pop(0)
        if ok == 2:
            spikes[code] = spikes.get(code, 0) + 1
            continue
        t = to_ext(raw)
        if test_mode:
            if code == CODE_SET:
                test_input("SET", None, t)
            elif code == CODE_GO:
                test_input("GO", None, t)
            else:
                test_input("Lane %d" % code, code, t)
            continue
        if code == CODE_SET:
            handle_set(t)
        elif code == CODE_GO:
            handle_go(t)
        else:
            handle_lane(code, t)

    now = time.ticks_ms()

    # 2. re-arm SET/GO only after a steady release (ignores release bounce)
    if set_in.value() != HIT:
        if set_idle_since is None:
            set_idle_since = now
        elif not set_ready and time.ticks_diff(now, set_idle_since) >= REARM_MS:
            set_ready = True
    else:
        set_idle_since = None

    if go_in.value() != HIT:
        if go_idle_since is None:
            go_idle_since = now
        elif not go_ready and time.ticks_diff(now, go_idle_since) >= REARM_MS:
            go_ready = True
    else:
        go_idle_since = None

    # 3. FINISH button: must be held FINISH_HOLD_MS
    if finish_in.value() == 0:
        if finish_down_since is None:
            finish_down_since = now
            finish_down_state = state
        elif not finish_fired and time.ticks_diff(now, finish_down_since) >= FINISH_HOLD_MS:
            finish_fired = True
            if test_mode:
                test_input("FINISH")
            else:
                finish_race()
        if (not reset_fired and not test_mode and finish_down_since is not None
                and finish_down_state in ("IDLE", "DONE") and state in ("IDLE", "DONE")
                and time.ticks_diff(now, finish_down_since) >= PIN_RESET_MS):
            reset_fired = True
            emit({"ev": "pin_reset"})
            print("Timing desk PIN cleared from the timing box - the next phone to open the app sets a new one.")
            beep(600, 300, 3)
    else:
        finish_down_since = None
        finish_fired = False
        reset_fired = False

    # 4. lane light timers (10 s holds, flashes)
    if light_seq:
        run_lights(now)

    # 5. timeouts
    if state == "ARMED" and time.ticks_diff(now, armed_at_ms) > SET_TIMEOUT_MS:
        state = "IDLE"
        led.off()
        print("SET timed out - press SET again.")
        announce()
    if state == "RACING" and time.ticks_diff(now, go_at_ms) > MAX_RACE_MS:
        finish_race("Race auto-finished - 20 minute limit (FINISH not pressed).")

    # 5b. button test switches itself off
    if test_mode and time.ticks_diff(now, test_until) > 0:
        set_test(False)

    # 5c. lane cable opening during a race (only reads pins - no flash writes)
    if state == "RACING":
        for lane, p in lane_in.items():
            if p.value() == HIT:
                if lane not in held_since:
                    held_since[lane] = now
                elif lane not in race_faults and time.ticks_diff(now, held_since[lane]) >= RACE_FAULT_MS:
                    race_faults.append(lane)
                    print("FAULT DURING RACE: Lane %d open over %d s - cable or button. Check its presses."
                          % (lane, RACE_FAULT_MS // 1000))
                    emit({"ev": "faults", "list": ["Lane %d" % x for x in race_faults], "racing": True})
            else:
                held_since.pop(lane, None)

    # 6. fault monitor while not racing
    if state in ("IDLE", "DONE") and time.ticks_diff(now, last_check) > FAULT_CHECK_MS:
        last_check = now
        f = faults()
        if f != last_fault_report:
            if f:
                print("FAULT:", ", ".join(f))
            else:
                print("All inputs OK.")
            last_fault_report = f
            emit({"ev": "faults", "list": f})

    # 6b. heartbeat to the app, and the battery between races
    if time.ticks_diff(now, last_beat) >= BEAT_MS:
        last_beat = now
        print('@{"ev":"beat"}')
    if batt_adc and state != "RACING" and time.ticks_diff(now, last_batt) >= BATT_MS:
        last_batt = now
        emit({"ev": "batt", "v": read_batt()})

    # 6c. say (at most every 10 s) when spikes were ignored - a sign of noisy wiring
    if spikes and time.ticks_diff(now, last_spike_report) >= 10_000:
        last_spike_report = now
        names = {CODE_SET: "SET", CODE_GO: "GO"}
        print("Ignored electrical spikes (not presses): " +
              ", ".join("%s x%d" % (names.get(c, "Lane %d" % c), n) for c, n in sorted(spikes.items())))
        spikes.clear()

    # 7. heartbeat LED while idle (slow blink = running)
    if state in ("IDLE", "DONE") and time.ticks_diff(now, last_blink) > 500:
        last_blink = now
        led.toggle()

    # 8. typed commands
    while poller.poll(0):
        c = sys.stdin.read(1)
        if c in ("\r", "\n"):
            if line:
                command(line)
            line = ""
        elif len(line) < 40:
            line += c

    time.sleep_ms(1)
