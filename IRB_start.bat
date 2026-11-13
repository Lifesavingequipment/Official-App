@echo off
rem IRB timing - start the officials' app (double-click this file).
rem Keep this file in the same folder as officials_app.py.
title IRB timing app
cd /d "%~dp0"
set IRB_LAUNCHER=1
echo Starting the IRB timing app...
echo (Close Thonny first. Close this window to stop the app.)
echo.
:run
python officials_app.py
if %errorlevel%==3 (
  echo.
  echo Restarting with the new version...
  echo.
  goto run
)
echo.
echo The app has stopped. If there's an error above, send it to Claude.
pause
