#!/usr/bin/env python3
"""
LiveHeats peek - saves one public event's heats and crews to a file, so the
officials' app can be taught to read them. Read-only: it changes nothing on LiveHeats.

Run:   python liveheats_peek.py https://www.liveheats.com/events/505147
Makes: liveheats_<event>.json  in the same folder (send that file to Claude).
No extra installs needed.
"""
import json, re, sys, os, urllib.request, urllib.error

API = "https://liveheats.com/api/graphql"


def ask(query, variables=None):
    body = json.dumps({"query": query, "variables": variables or {}}).encode()
    req = urllib.request.Request(API, body, {"Content-Type": "application/json",
                                             "User-Agent": "IRB-timing-app/0.3"})
    try:
        with urllib.request.urlopen(req, timeout=30) as r:
            return json.loads(r.read().decode())
    except urllib.error.HTTPError as e:
        return {"http_error": e.code, "body": e.read().decode("utf-8", "ignore")[:2000]}
    except Exception as e:
        return {"error": str(e)}


def base(t):
    while t and t.get("ofType"):
        t = t["ofType"]
    return t or {}


def fields_of(type_name):
    q = """query($n:String!){ __type(name:$n){ name fields { name args { name type { kind } }
           type { kind name ofType { kind name ofType { kind name ofType { kind name } } } } } } }"""
    r = ask(q, {"n": type_name})
    t = (r.get("data") or {}).get("__type") or {}
    return t.get("fields") or [], r


def simple(type_name, depth=1):
    """scalar fields of a type, plus id/name of linked objects (no arguments needed)"""
    fl, _ = fields_of(type_name)
    parts = []
    for f in fl:
        if any(a for a in f.get("args", [])):
            continue
        b = base(f["type"])
        if b.get("kind") in ("SCALAR", "ENUM"):
            parts.append(f["name"])
        elif b.get("kind") == "OBJECT" and depth > 0:
            sub = [x["name"] for x in fields_of(b["name"])[0]
                   if x["name"] in ("id", "name", "firstName", "lastName")
                   and base(x["type"]).get("kind") == "SCALAR"]
            if sub:
                parts.append("%s { %s }" % (f["name"], " ".join(sub)))
    return " ".join(parts)


def main():
    arg = sys.argv[1] if len(sys.argv) > 1 else input("LiveHeats event link: ")
    m = re.search(r"(\d+)", arg)
    if not m:
        print("No event number found in:", arg)
        return
    eid = m.group(1)
    out = {"event_id": eid}
    print("Reading the LiveHeats layout...")
    for tn in ("Event", "EventDivision", "Heat", "Competitor", "HeatResult", "Division"):
        out["type_" + tn] = [f["name"] for f in fields_of(tn)[0]]

    competitor = simple("Competitor") or "id"
    division = "id status division { id name }" if "division" in out["type_EventDivision"] else "id status"
    full = """query($id: ID!){ event(id:$id){ id name date status
      eventDivisions { %s heats { id round roundPosition position scheduledTime startTime endTime
        competitors { %s } } } } }""" % (division, competitor)
    print("Reading event %s..." % eid)
    r = ask(full, {"id": eid})
    if r.get("errors") or not (r.get("data") or {}).get("event"):
        out["full_attempt"] = {"query": full, "reply": r}
        print("Full read had problems - trying a simpler one...")
        r = ask("""query($id: ID!){ event(id:$id){ id name date status
          eventDivisions { id status heats { id round roundPosition position competitors { id } } } } }""",
                {"id": eid})
    out["query"] = full
    out["reply"] = r

    name = "liveheats_%s.json" % eid
    with open(name, "w", encoding="utf-8") as fh:
        json.dump(out, fh, indent=1)
    ev = (r.get("data") or {}).get("event")
    if ev:
        divs = ev.get("eventDivisions") or []
        heats = sum(len(d.get("heats") or []) for d in divs)
        print("OK: %s (%s) - %d divisions, %d heats." % (ev.get("name"), ev.get("date"), len(divs), heats))
    else:
        print("Couldn't read the event:", str(r)[:300])
    print("Saved:", os.path.abspath(name), " <- send this file to Claude")


if __name__ == "__main__":
    main()
    if os.name == "nt" and len(sys.argv) < 2:
        input("Press Enter to close...")
