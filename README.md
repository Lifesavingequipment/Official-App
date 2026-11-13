# IRB finish timing – officials' app

Finish timing for IRB racing at surf lifesaving carnivals.
A Raspberry Pi Pico reads the beach buttons; a laptop (later a Raspberry Pi) runs the officials' app,
which phones and tablets open over the beach Wi-Fi.

| File | Goes on | What it is |
|---|---|---|
| `officials_app.py` | timing computer | The officials' app (web page on port 8080) |
| `main.py` | the Pico (save with Thonny) | Reads the buttons and keeps the times |
| `IRB_start.bat` | timing computer | Double-click to start the app (restarts it after an update) |
| `IRB_update.bat` | timing computer | Manual update from a downloaded file (backup method) |
| `liveheats_*_peek.py` | timing computer | Read-only checks of what LiveHeats shares |
| `VERSION.json` | – | Tells the app the newest version (made by `release.py`) |

## Updating
On the timing computer (Master): **System › Setup › Updates › Update**. The app downloads the newest
`officials_app.py` from this repository, checks it, keeps the old one in `Old\`, and restarts.
It won't update while a race is armed or running. **Go back** puts the previous version back.

## Releasing a new version
1. Change `officials_app.py` and raise `APP_VERSION`.
2. `python release.py "What changed"` – writes `VERSION.json`.
3. Commit and push to `main`.

Race results, names and settings live in `timing_data\` on the timing computer and are never uploaded here.
