#!/usr/bin/env python3
"""
LiveHeats schedule peek - saves how LiveHeats stores an event's running order (fullSchedule),
so the officials' app can read it. Read-only: it changes nothing on LiveHeats.

Run:   python liveheats_schedule_peek.py https://www.liveheats.com/events/505147
Makes: liveheats_schedule_<event>.json in the same folder (send that file to Claude).
Best with an event that has a schedule set up in LiveHeats. No extra installs needed.
"""
import json, re, sys, os, urllib.request, urllib.error

API = "https://liveheats.com/api/graphql"


def ask(query, variables=None):
    body = json.dumps({"query": query, "variables": variables or {}}).encode()
    req = urllib.request.Request(API, body, {"Content-Type": "application/json", "User-Agent": "IRB-timing-app"})
    try:
        with urllib.request.urlopen(req, timeout=30) as r:
            return json.loads(r.read().decode())
    except urllib.error.HTTPError as e:
        return {"http_error": e.code, "body": e.read().decode("utf-8", "ignore")[:2000]}
    except Exception as e:
        return {"error": str(e)}


TQ = """query($n:String!){ __type(name:$n){ name kind fields { name args { name }
        type { kind name ofType { kind name ofType { kind name ofType { kind name } } } } } } }"""


def base(t):
    while t and t.get("ofType"):
        t = t["ofType"]
    return t or {}


def main():
    arg = sys.argv[1] if len(sys.argv) > 1 else input("LiveHeats event link: ")
    m = re.search(r"(\d+)", arg)
    if not m:
        print("No event number found in:", arg)
        return
    eid = m.group(1)
    out = {"event_id": eid, "types": {}}
    print("Reading how LiveHeats stores schedules...")
    ev_type = (ask(TQ, {"n": "Event"}).get("data") or {}).get("__type") or {}
    fs = next((f for f in ev_type.get("fields") or [] if f["name"] == "fullSchedule"), None)
    out["fullSchedule_field"] = fs
    sel = "fullSchedule"
    if fs and base(fs["type"]).get("kind") == "OBJECT":
        def build(name, depth):
            t = (ask(TQ, {"n": name}).get("data") or {}).get("__type") or {}
            out["types"][name] = [f["name"] for f in t.get("fields") or []]
            parts = []
            for f in t.get("fields") or []:
                if f.get("args"):
                    continue
                b = base(f["type"])
                if b.get("kind") in ("SCALAR", "ENUM"):
                    parts.append(f["name"])
                elif b.get("kind") == "OBJECT" and depth > 0:
                    s = build(b["name"], depth - 1)
                    if s:
                        parts.append("%s { %s }" % (f["name"], s))
            return " ".join(parts)
        sel = "fullSchedule { %s }" % build(base(fs["type"])["name"], 3)
    out["query"] = sel
    print("Reading event %s schedule..." % eid)
    out["reply"] = ask("""query($id: ID!){ event(id:$id){ id name currentScheduleIndex %s
        eventDivisions { id division { name } heats { id round position scheduledTime } } } }""" % sel, {"id": eid})
    name = "liveheats_schedule_%s.json" % eid
    with open(name, "w", encoding="utf-8") as fh:
        json.dump(out, fh, indent=1)
    ev = ((out["reply"].get("data") or {}).get("event")) or {}
    if ev:
        has = ev.get("fullSchedule") not in (None, "", [], {})
        print("OK: %s - schedule %s." % (ev.get("name"), "found" if has else "is empty for this event"))
    else:
        print("Couldn't read the event:", str(out["reply"])[:300])
    print("Saved:", os.path.abspath(name), " <- send this file to Claude")


if __name__ == "__main__":
    main()
    if os.name == "nt" and len(sys.argv) < 2:
        input("Press Enter to close...")
