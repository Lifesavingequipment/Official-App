#!/usr/bin/env python3
"""
LiveHeats team members peek - checks whether LiveHeats shares the names of the
people in each crew (driver, crew, patients), so the app can show them.
Read-only: it changes nothing on LiveHeats.

Run:   python liveheats_members_peek.py https://www.liveheats.com/events/505147
Makes: liveheats_members_<event>.json in the same folder (send that file to Claude).
No extra installs needed.
"""
import json, re, sys, os, urllib.request, urllib.error

API = "https://liveheats.com/api/graphql"


def ask(query, variables=None):
    body = json.dumps({"query": query, "variables": variables or {}}).encode()
    req = urllib.request.Request(API, body, {"Content-Type": "application/json",
                                             "User-Agent": "IRB-timing-app/1.3"})
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
    q = """query($n:String!){ __type(name:$n){ name fields { name args { name }
           type { kind name ofType { kind name ofType { kind name ofType { kind name } } } } } } }"""
    r = ask(q, {"n": type_name})
    t = (r.get("data") or {}).get("__type") or {}
    return t.get("fields") or []


def selection(type_name, depth):
    """every plain field of a type, and (one level down) the plain fields of linked objects"""
    parts = []
    for f in fields_of(type_name):
        if f.get("args"):
            continue
        b = base(f["type"])
        if b.get("kind") in ("SCALAR", "ENUM"):
            parts.append(f["name"])
        elif b.get("kind") == "OBJECT" and depth > 0 and b.get("name") not in ("Competitor", "Heat", "Event", "EventDivision"):
            sub = selection(b["name"], depth - 1)
            if sub:
                parts.append("%s { %s }" % (f["name"], sub))
    return " ".join(parts)


def main():
    arg = sys.argv[1] if len(sys.argv) > 1 else input("LiveHeats event link: ")
    m = re.search(r"(\d+)", arg)
    if not m:
        print("No event number found in:", arg)
        return
    eid = m.group(1)
    out = {"event_id": eid}

    # 1. what type is Competitor.teamMembers, and what's in it?
    comp = fields_of("Competitor")
    tm = next((f for f in comp if f["name"] == "teamMembers"), None)
    tm_type = base(tm["type"]).get("name") if tm else None
    out["team_member_type"] = tm_type
    out["team_member_fields"] = [f["name"] for f in fields_of(tm_type)] if tm_type else []
    print("Team member record type:", tm_type)
    print("Its fields:", ", ".join(out["team_member_fields"]) or "(none found)")
    if not tm_type:
        print("LiveHeats doesn't list team members for crews.")
    else:
        sel = selection(tm_type, 2) or "id"
        out["team_member_query"] = sel
        q = """query($id: ID!){ event(id:$id){ id name eventDivisions { division { name }
                 heats { id round position competitors { teamName athlete { name } teamMembers { %s } } } } } }""" % sel
        print("Reading event %s..." % eid)
        r = ask(q, {"id": eid})
        if r.get("errors") or not (r.get("data") or {}).get("event"):
            out["first_try"] = {"query": q, "reply": {"errors": r.get("errors"), "http_error": r.get("http_error"), "body": r.get("body")}}
            print("First read had problems:", str(r.get("errors") or r.get("body") or r)[:300])
            print("Trying with names, roles and order...")
            q = """query($id: ID!){ event(id:$id){ id name eventDivisions { division { name }
                     heats { id round position competitors { teamName teamMembers { id order teamRoleId teamRoleName athlete { id name } } } } } } }"""
            r = ask(q, {"id": eid})
        if r.get("errors") or not (r.get("data") or {}).get("event"):
            out["second_try"] = {"query": q, "reply": {"errors": r.get("errors"), "http_error": r.get("http_error"), "body": r.get("body")}}
            print("Second read had problems:", str(r.get("errors") or r.get("body") or r)[:300])
            print("Trying with ids and names only...")
            q = """query($id: ID!){ event(id:$id){ id name eventDivisions { division { name }
                     heats { id round position competitors { teamName teamMembers { id athlete { id name } } } } } } }"""
            r = ask(q, {"id": eid})
        out["query"] = q
        # keep the file small: the first 3 heats of each division are plenty
        ev = (r.get("data") or {}).get("event")
        if ev:
            for d in ev.get("eventDivisions") or []:
                d["heats"] = (d.get("heats") or [])[:3]
        out["reply"] = r
        # show a sample on screen
        shown = 0
        for d in (ev or {}).get("eventDivisions") or []:
            for h in d.get("heats") or []:
                for c in h.get("competitors") or []:
                    if shown < 3 and c.get("teamMembers"):
                        print("\n%s - %s" % ((d.get("division") or {}).get("name"), c.get("teamName")))
                        for mbr in c["teamMembers"]:
                            print("   ", json.dumps(mbr)[:160])
                        shown += 1

    name = "liveheats_members_%s.json" % eid
    with open(name, "w", encoding="utf-8") as fh:
        json.dump(out, fh, indent=1)
    print("\nSaved:", os.path.abspath(name), " <- send this file to Claude")


if __name__ == "__main__":
    main()
    if os.name == "nt" and len(sys.argv) < 2:
        input("Press Enter to close...")
