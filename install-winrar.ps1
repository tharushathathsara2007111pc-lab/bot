# Installs WinRAR automatically when it is missing (needed to send files over 2 GB as RAR parts).
# Called by start.bat. It never stops the bot from starting, even if the install fails.
$ErrorActionPreference = 'Stop'
$root = Split-Path -Parent $MyInvocation.MyCommand.Path
$dest = Join-Path $root 'winrar'
$flag = Join-Path $root 'winrar-install.failed'

function Test-Rar {
  (Test-Path (Join-Path $dest 'Rar.exe')) -or
  (Test-Path (Join-Path $env:ProgramFiles 'WinRAR\Rar.exe')) -or
  (Test-Path (Join-Path ${env:ProgramFiles(x86)} 'WinRAR\Rar.exe'))
}

if (Test-Rar) { exit 0 }
if (Test-Path $flag) {
  Write-Host '[WinRAR] An earlier automatic install failed. Delete winrar-install.failed to try again.'
  Write-Host '[WinRAR] Meanwhile big files are split with 7-Zip or a plain split.'
  exit 0
}

Write-Host '[WinRAR] Not found - installing it (needed to send files over 2 GB as RAR parts)...'
try {
  [Net.ServicePointManager]::SecurityProtocol = [Net.SecurityProtocolType]::Tls12
  $ProgressPreference = 'SilentlyContinue'

  # 1) newest version number from rarlab.com, 2) fallback to a known version
  $url = $null
  try {
    $page = (Invoke-WebRequest -UseBasicParsing 'https://www.rarlab.com/download.htm' -TimeoutSec 30).Content
    $best = [regex]::Matches($page, 'rar/winrar-x64-(\d+)\.exe') |
      Sort-Object { [int]$_.Groups[1].Value } -Descending | Select-Object -First 1
    if ($best) { $url = 'https://www.rarlab.com/' + $best.Value }
  } catch { }
  if (-not $url) { $url = 'https://www.rarlab.com/rar/winrar-x64-713.exe' }

  $setup = Join-Path $env:TEMP 'winrar-setup.exe'
  Write-Host "[WinRAR] Downloading $url"
  Invoke-WebRequest -UseBasicParsing $url -OutFile $setup -TimeoutSec 900

  Write-Host '[WinRAR] Installing silently into the bot folder...'
  Start-Process -FilePath $setup -ArgumentList '/S', "/D=$dest" -Wait
  if (-not (Test-Path (Join-Path $dest 'Rar.exe'))) {
    Write-Host '[WinRAR] Trying the normal install (Windows may ask for permission)...'
    Start-Process -FilePath $setup -ArgumentList '/S' -Verb RunAs -Wait
  }
  Remove-Item $setup -Force -ErrorAction SilentlyContinue

  if (Test-Rar) { Write-Host '[WinRAR] Installed OK.' }
  else { throw 'Rar.exe was not found after the install.' }
} catch {
  Write-Host ('[WinRAR] Could not install automatically: ' + $_.Exception.Message)
  Set-Content -Path $flag -Value 'failed'
}
exit 0
