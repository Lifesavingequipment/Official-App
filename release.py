#!/usr/bin/env python3
"""Run before pushing a new version: writes VERSION.json (version, checksum, what's new).
   python release.py "What changed" "Another change"
The officials' app reads VERSION.json to offer the update, and checks the checksum before installing."""
import hashlib, json, re, sys, os
here = os.path.dirname(os.path.abspath(__file__))
app = open(os.path.join(here, "officials_app.py"), "rb").read()
ver = re.search(rb'APP_VERSION = "([^"]+)"', app).group(1).decode()
pico = re.search(rb'"fw": "([^"]+)"', open(os.path.join(here, "main.py"), "rb").read()).group(1).decode()
notes = sys.argv[1:] or ["Improvements and fixes"]
json.dump({"app": ver, "pico": pico, "sha256": hashlib.sha256(app).hexdigest(), "notes": notes},
          open(os.path.join(here, "VERSION.json"), "w"), indent=1)
print("VERSION.json: app v%s, Pico v%s" % (ver, pico))
