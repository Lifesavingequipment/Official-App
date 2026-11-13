@echo off
rem IRB timing - install a new officials_app.py from Downloads and restart (double-click this file).
rem Keep this file in the same folder as officials_app.py.
setlocal
cd /d "%~dp0"
set "DL=%USERPROFILE%\Downloads"

rem the newest officials_app*.py in Downloads (Windows may name it "officials_app (1).py")
set "NEW="
for /f "delims=" %%F in ('dir /b /a-d /o:-d "%DL%\officials_app*.py" 2^>nul') do if not defined NEW set "NEW=%%F"
if not defined NEW (
  echo No new officials_app.py found in your Downloads folder.
  echo Starting the app you already have...
  goto start
)
echo Found: %DL%\%NEW%

rem make sure the new file isn't damaged before using it
python -m py_compile "%DL%\%NEW%"
if errorlevel 1 (
  echo.
  echo That file looks damaged - NOT installed. Download it again from Claude.
  pause
  exit /b 1
)

rem stop the running app (if any) so the Pico's port is free
taskkill /fi "WINDOWTITLE eq IRB timing app*" /t /f >nul 2>&1
timeout /t 2 /nobreak >nul

rem keep the old version in the Old folder, with the date and time
for /f %%i in ('powershell -NoProfile -Command "Get-Date -Format yyyyMMdd-HHmm"') do set "TS=%%i"
if not exist "Old" mkdir "Old"
if exist "officials_app.py" copy /y "officials_app.py" "Old\officials_app_%TS%.py" >nul

rem install the new one, and move the download away so it isn't used twice
copy /y "%DL%\%NEW%" "officials_app.py" >nul
move /y "%DL%\%NEW%" "Old\downloaded_%TS%.py" >nul
echo Installed. The old version is saved in the Old folder as officials_app_%TS%.py
echo.

:start
rem the new window starts in this folder
start "" "%~dp0IRB_start.bat"
echo The app is starting in its own window. You can close this one.
timeout /t 5 >nul
