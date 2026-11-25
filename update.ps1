# MPM Unified WhatsApp Bot - setup + auto update helper (called by start.bat)
param(
  [string]$Task = "Update",
  [int]$ParentPid = 0
)

$ErrorActionPreference = "Continue"
try { [Net.ServicePointManager]::SecurityProtocol = [Net.SecurityProtocolType]::Tls12 } catch {}
$root = Split-Path -Parent $MyInvocation.MyCommand.Path
Set-Location $root
$runtime = Join-Path $root "runtime"

# ---------------------------------------------------------------------------
# Background mode: keep Windows awake while the bot window is open
# ---------------------------------------------------------------------------
if ($Task -eq "KeepAwake") {
  Add-Type -MemberDefinition '[DllImport("kernel32.dll")] public static extern uint SetThreadExecutionState(uint f);' -Name KeepAwakeApi -Namespace MpmBot
  while ($true) {
    if ($ParentPid -gt 0 -and -not (Get-Process -Id $ParentPid -ErrorAction SilentlyContinue)) { break }
    # ES_CONTINUOUS | ES_SYSTEM_REQUIRED
    [void][MpmBot.KeepAwakeApi]::SetThreadExecutionState([uint32]2147483649)
    Start-Sleep -Seconds 30
  }
  exit 0
}

function Say($text, $color = "Green") { Write-Host $text -ForegroundColor $color }

# ---------------------------------------------------------------------------
# 1) Turn off QuickEdit (clicking inside the CMD window pauses the bot and drops WhatsApp)
# ---------------------------------------------------------------------------
function Disable-QuickEdit {
  try {
    Add-Type -MemberDefinition @'
[DllImport("kernel32.dll")] public static extern IntPtr GetStdHandle(int n);
[DllImport("kernel32.dll")] public static extern bool GetConsoleMode(IntPtr h, out uint m);
[DllImport("kernel32.dll")] public static extern bool SetConsoleMode(IntPtr h, uint m);
'@ -Name ConsoleApi -Namespace MpmBot -ErrorAction Stop
    $h = [MpmBot.ConsoleApi]::GetStdHandle(-10)
    $m = [uint32]0
    if ([MpmBot.ConsoleApi]::GetConsoleMode($h, [ref]$m)) {
      $m = ($m -bor 0x80) -band (-bnot 0x40)
      [void][MpmBot.ConsoleApi]::SetConsoleMode($h, [uint32]$m)
      Say "[Setup] QuickEdit disabled - clicking in this window no longer freezes the bot." "DarkGreen"
    }
  } catch {}
}

# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------
function Get-File($url, $out) {
  $curl = Join-Path $env:SystemRoot "System32\curl.exe"
  if (Test-Path $curl) {
    & $curl -L --fail --retry 3 --connect-timeout 15 --progress-bar -o $out $url
    return (($LASTEXITCODE -eq 0) -and (Test-Path $out))
  }
  try {
    $ProgressPreference = "Continue"
    Invoke-WebRequest -UseBasicParsing -Uri $url -OutFile $out
    return (Test-Path $out)
  } catch {
    Say ("[Update] Download failed: " + $_.Exception.Message) "Yellow"
    return $false
  }
}

function Get-NodeVersion($exe) {
  try {
    $v = (& $exe -v 2>$null)
    if ($v) { return ([string]$v).Trim().TrimStart("v") }
  } catch {}
  return $null
}

function Compare-Ver($a, $b) {   # returns -1, 0, 1
  try { return ([version]$a).CompareTo([version]$b) } catch { return 0 }
}

function Get-LatestNode20 {
  try {
    $j = Invoke-RestMethod -UseBasicParsing -Uri "https://nodejs.org/dist/index.json" -TimeoutSec 15
    $v = ($j | Where-Object { $_.version -like "v20.*" } | Select-Object -First 1).version
    if ($v) { return $v }
  } catch {}
  return $null
}

function Install-PortableNode($ver) {
  if (-not (Test-Path $runtime)) { New-Item -ItemType Directory -Force -Path $runtime | Out-Null }
  $zip = Join-Path $runtime "node.zip"
  $tmp = Join-Path $runtime "node_tmp"
  $dest = Join-Path $runtime "node"
  $old = Join-Path $runtime "node_old"
  $url = "https://nodejs.org/dist/$ver/node-$ver-win-x64.zip"
  Say "[Node.js] Downloading $ver (about 30 MB)..." "Cyan"
  if (-not (Get-File $url $zip)) { return $false }
  Say "[Node.js] Extracting..." "Cyan"
  if (Test-Path $tmp) { Remove-Item $tmp -Recurse -Force -ErrorAction SilentlyContinue }
  $pp = $ProgressPreference; $ProgressPreference = "SilentlyContinue"
  try { Expand-Archive -LiteralPath $zip -DestinationPath $tmp -Force } catch { Say ("[Node.js] Extract failed: " + $_.Exception.Message) "Yellow"; $ProgressPreference = $pp; return $false }
  $ProgressPreference = $pp
  $inner = Get-ChildItem $tmp -Directory | Select-Object -First 1
  if (-not $inner -or -not (Test-Path (Join-Path $inner.FullName "node.exe"))) { return $false }
  if (Test-Path $old) { Remove-Item $old -Recurse -Force -ErrorAction SilentlyContinue }
  if (Test-Path $dest) { Rename-Item $dest "node_old" -ErrorAction SilentlyContinue }
  Move-Item $inner.FullName $dest
  if (-not (Test-Path (Join-Path $dest "node.exe"))) {
    if (Test-Path $old) { Rename-Item $old "node" -ErrorAction SilentlyContinue }
    return $false
  }
  Remove-Item $zip -Force -ErrorAction SilentlyContinue
  Remove-Item $tmp -Recurse -Force -ErrorAction SilentlyContinue
  Remove-Item $old -Recurse -Force -ErrorAction SilentlyContinue
  return $true
}

# ---------------------------------------------------------------------------
Say "==========================================" "Green"
Say "   MPM BOT - setup and update check" "Green"
Say "==========================================" "Green"

Disable-QuickEdit

# keep the PC awake while this window is open
try {
  $parent = (Get-CimInstance Win32_Process -Filter "ProcessId=$PID").ParentProcessId
  if ($parent) {
    Start-Process -WindowStyle Hidden -FilePath "powershell.exe" -ArgumentList @("-NoProfile","-ExecutionPolicy","Bypass","-File","`"$PSCommandPath`"","-Task","KeepAwake","-ParentPid","$parent") | Out-Null
    Say "[Setup] Sleep prevention on while the bot window is open." "DarkGreen"
  }
} catch {}

# ---------------------------------------------------------------------------
# 2) Node.js
# ---------------------------------------------------------------------------
$portableNode = Join-Path $runtime "node\node.exe"
$sysNodeCmd = Get-Command node -ErrorAction SilentlyContinue
$nodeExe = $null
if (Test-Path $portableNode) { $nodeExe = $portableNode }
elseif ($sysNodeCmd) { $nodeExe = $sysNodeCmd.Source }

$curVer = $null
if ($nodeExe) { $curVer = Get-NodeVersion $nodeExe }
$isPortable = (Test-Path $portableNode)
$needNode = $true
if ($curVer) {
  $needNode = ((Compare-Ver $curVer "18.17.0") -lt 0) -and (-not $isPortable)
}

if (-not $curVer -or $needNode) {
  Say "[Node.js] Node.js 18.17+ not found - installing a portable copy (no admin needed)..." "Yellow"
  $latest = Get-LatestNode20
  if (-not $latest) { $latest = "v20.18.0" }
  if (Install-PortableNode $latest) { Say "[Node.js] Installed $latest." "Green" }
  else { Say "[Node.js] Could not install Node.js automatically. Install Node 20 LTS from https://nodejs.org" "Red" }
}
elseif ($isPortable) {
  $latest = Get-LatestNode20
  if ($latest) {
    $latestPlain = $latest.TrimStart("v")
    if ((Compare-Ver $curVer $latestPlain) -lt 0) {
      Say "[Node.js] Update available: v$curVer -> $latest" "Cyan"
      if (Install-PortableNode $latest) { Say "[Node.js] Updated to $latest." "Green" }
      else { Say "[Node.js] Update failed - keeping v$curVer." "Yellow" }
    } else { Say "[Node.js] v$curVer is up to date." "Green" }
  } else { Say "[Node.js] v$curVer (could not check for updates - offline?)." "Yellow" }
}
else {
  Say "[Node.js] Using system Node.js v$curVer." "Green"
}

# make sure npm below uses the portable node when it exists
if (Test-Path (Join-Path $runtime "node\node.exe")) { $env:PATH = (Join-Path $runtime "node") + ";" + $env:PATH }

# ---------------------------------------------------------------------------
# 3) npm packages (Baileys etc.) - stays inside the same major version
# ---------------------------------------------------------------------------
$pkgFile = Join-Path $root "package.json"
$lockFile = Join-Path $root "package-lock.json"
if ((Test-Path $pkgFile) -and (Get-Command npm -ErrorAction SilentlyContinue)) {
  Say "" 
  Say "[Packages] Checking for updates (WhatsApp library and others)..." "Cyan"

  Copy-Item $pkgFile "$pkgFile.bak" -Force
  if (Test-Path $lockFile) { Copy-Item $lockFile "$lockFile.bak" -Force }

  # allow safe 6.x updates of Baileys (an exact pin like "6.7.24" never updates)
  try {
    $txt = Get-Content -Raw $pkgFile
    $new = [regex]::Replace($txt, '("@whiskeysockets/baileys"\s*:\s*")(6\.\d+\.\d+")', '$1^$2')
    if ($new -ne $txt) { Set-Content -Path $pkgFile -Value $new -NoNewline -Encoding UTF8 }
  } catch {}

  if (Test-Path (Join-Path $root "node_modules")) {
    & npm outdated --no-audit --no-fund
  }

  & npm update --no-audit --no-fund
  if ($LASTEXITCODE -ne 0) {
    Say "[Packages] Update failed - restoring the previous package list." "Yellow"
    Copy-Item "$pkgFile.bak" $pkgFile -Force
    if (Test-Path "$lockFile.bak") { Copy-Item "$lockFile.bak" $lockFile -Force }
    & npm install --no-audit --no-fund
  } else {
    Say "[Packages] Up to date." "Green"
    $bv = $null
    try { $bv = (Get-Content -Raw (Join-Path $root "node_modules\@whiskeysockets\baileys\package.json") | ConvertFrom-Json).version } catch {}
    if ($bv) { Say "[Packages] WhatsApp library (Baileys) version: $bv" "Green" }
  }
}

# ---------------------------------------------------------------------------
# 4) aria2 (torrent / magnet downloads)
# ---------------------------------------------------------------------------
$ariaExe = Join-Path $root "aria2\aria2c.exe"
if (-not (Test-Path $ariaExe) -and -not (Get-Command aria2c -ErrorAction SilentlyContinue)) {
  $ver = "1.37.0"
  Say ""
  Say "[aria2] Not found - downloading aria2 $ver (used by ,torrent and ,magnet)..." "Cyan"
  if (-not (Test-Path $runtime)) { New-Item -ItemType Directory -Force -Path $runtime | Out-Null }
  $zip = Join-Path $runtime "aria2.zip"
  $tmp = Join-Path $runtime "aria2tmp"
  $url = "https://github.com/aria2/aria2/releases/download/release-$ver/aria2-$ver-win-64bit-build1.zip"
  if (Get-File $url $zip) {
    $pp = $ProgressPreference; $ProgressPreference = "SilentlyContinue"
    try {
      Expand-Archive -LiteralPath $zip -DestinationPath $tmp -Force
      $f = Get-ChildItem -Path $tmp -Recurse -Filter aria2c.exe | Select-Object -First 1
      New-Item -ItemType Directory -Force -Path (Join-Path $root "aria2") | Out-Null
      Copy-Item $f.FullName $ariaExe -Force
      Say "[aria2] Installed." "Green"
    } catch { Say ("[aria2] Install failed: " + $_.Exception.Message) "Yellow" }
    $ProgressPreference = $pp
    Remove-Item $zip -Force -ErrorAction SilentlyContinue
    Remove-Item $tmp -Recurse -Force -ErrorAction SilentlyContinue
  } else {
    Say "[aria2] Could not download. The bot still runs, but ,torrent and ,magnet will not work." "Yellow"
  }
}

Say ""
Say "[Setup] Done. Starting the bot..." "Green"
exit 0
