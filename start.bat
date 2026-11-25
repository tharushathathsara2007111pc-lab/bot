@echo off
setlocal EnableExtensions
title MPM Unified WhatsApp Bot
color 0A
REM keep the whole window green: libraries must not add their own colours
set "NO_COLOR=1"
set "FORCE_COLOR=0"
set "NPM_CONFIG_COLOR=false"
REM tells the bot that this window restarts it (used by the ,restart command)
set "MPM_SUPERVISED=1"
cd /d "%~dp0"

set "RUNTIME=%~dp0runtime"

echo ==========================================
echo       MPM DOWNLOADER WHATSAPP BOT
echo ==========================================

if exist "%RUNTIME%\node\node.exe" set "PATH=%RUNTIME%\node;%PATH%"
if exist "%~dp0aria2\aria2c.exe" set "PATH=%~dp0aria2;%PATH%"

REM ------------------------------------------------------------
REM 1) Setup + auto update (Node.js, bot packages, aria2).
REM    Shows download progress. If it fails or you are offline,
REM    the bot still starts with what is already installed.
REM ------------------------------------------------------------
if exist "%~dp0update.ps1" goto :run_updater
echo [Setup] update.ps1 not found - skipping auto update.
goto :after_update
:run_updater
powershell -NoProfile -ExecutionPolicy Bypass -File "%~dp0update.ps1"
:after_update

REM the updater may have installed or updated the portable Node.js / aria2
if exist "%RUNTIME%\node\node.exe" set "PATH=%RUNTIME%\node;%PATH%"
if exist "%~dp0aria2\aria2c.exe" set "PATH=%~dp0aria2;%PATH%"

REM ------------------------------------------------------------
REM WinRAR (used to send files over 2 GB as RAR parts).
REM Installed automatically when missing. If it fails, the bot still starts.
REM ------------------------------------------------------------
if exist "%~dp0winrar\Rar.exe" set "PATH=%~dp0winrar;%PATH%"
where rar >nul 2>nul
if not errorlevel 1 goto :rar_ok
if exist "%ProgramFiles%\WinRAR\Rar.exe" goto :rar_ok
if exist "%ProgramFiles(x86)%\WinRAR\Rar.exe" goto :rar_ok
if exist "%~dp0install-winrar.ps1" powershell -NoProfile -ExecutionPolicy Bypass -File "%~dp0install-winrar.ps1"
if exist "%~dp0winrar\Rar.exe" set "PATH=%~dp0winrar;%PATH%"
:rar_ok

where node >nul 2>nul
if errorlevel 1 goto :node_fail
node -e "const v=process.versions.node.split('.').map(Number); process.exit((v[0]>18||(v[0]===18&&v[1]>=17))?0:1)" >nul 2>nul
if errorlevel 1 goto :node_fail
for /f "delims=" %%v in ('node -v') do echo Node.js %%v

REM ------------------------------------------------------------
REM 2) npm packages (also repairs an empty / broken node_modules)
REM ------------------------------------------------------------
:deps_check
set "MISSING_DEP="
for %%D in (@whiskeysockets\baileys cheerio axios adm-zip pino qrcode-terminal dotenv) do if not exist "node_modules\%%D\package.json" set "MISSING_DEP=%%D"
if not defined MISSING_DEP goto :deps_ok
if defined DEPS_TRIED goto :npm_fail
echo.
echo [Setup] Missing package: %MISSING_DEP%
echo [Setup] Installing bot packages, this may take 1-3 minutes...
call npm install --no-audit --no-fund
if errorlevel 1 goto :npm_fail
set "DEPS_TRIED=1"
goto :deps_check
:deps_ok
set "DEPS_TRIED="

REM ------------------------------------------------------------
REM 3) .env  (created from .env.example when it does not exist)
REM ------------------------------------------------------------
if exist ".env" goto :env_ok
if not exist ".env.example" goto :env_ok
copy /y ".env.example" ".env" >nul
echo [Setup] Created .env from .env.example
:env_ok
echo.

:RUN
echo [%date% %time%] Starting bot >> bot.log
node --max-old-space-size=3072 index.js
set "EXITCODE=%errorlevel%"
echo [%date% %time%] Bot stopped, exit code %EXITCODE% >> bot.log
echo.
echo Bot stopped with exit code %EXITCODE%. Restarting in 5 seconds... close this window to stop.
timeout /t 5 /nobreak >nul
REM re-check the packages on every restart, so a missing one is installed instead of crashing again
goto :deps_check

:node_fail
echo.
echo ERROR: Node.js could not be installed automatically. Check your internet connection and try again,
echo or install Node.js 20 LTS manually from https://nodejs.org and run this file again.
pause
exit /b 1

:npm_fail
echo.
echo ERROR: Bot packages could not be installed (still missing: %MISSING_DEP%).
echo Check your internet connection and try again. If it keeps failing,
echo delete the "node_modules" folder and run this file again.
pause
exit /b 1
