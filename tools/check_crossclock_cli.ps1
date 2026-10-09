# tools/check_crossclock_cli.ps1 -- CLI text-level regression pin for
# examples/hdl/21-crossclock.typort.
#
# WHY THIS EXISTS
#   tests/L13_namespace/hdl_check_graph_tests.rs::examples_21_crossclock_expected_warnings
#   already asserts the expected warning set, but it does so IN-PROCESS through
#   run_with_prelude. That is not an empty assertion (round 2 showed in-process
#   and CLI agree on a clean HEAD), so this script is deliberate hardening: it
#   pins the same claim at the CLI text level, which is what a user and the L3
#   harness actually see. It is NOT a substitute for the cargo test.
#
# WHAT IT ASSERTS
#   * `HDL038` appears exactly -ExpectHdl038 times (default 2) -- the two binary
#     FIFO pointer chains;
#   * `HDL036`, `HDL037` and `HDL039` appear zero times (no mixed-domain comb
#     signal, every crossing is synchronized, no mid-stage read);
#   * the two reported chains are the expected ones (`wrPtrSync1` to clkB and
#     `rdPtrSync1` to clkA);
#   * the run produced no `error:` line.
#
# WHY IT PRINTS A FINGERPRINT
#   This is a warning-SET check, so the binary that produced it is part of the
#   evidence. The script always prints the DUT path, size, mtime and sha256, and
#   `-RequireSha256` lets a caller pin the exact artifact. (Round 2/3 lesson: a
#   file NAME is not provenance.)
#
# USAGE
#   powershell -ExecutionPolicy Bypass -File tools/check_crossclock_cli.ps1
#   ... -Exe target\prelude_scratch\r3_base_typort.exe
#   ... -RequireSha256 9844617D...     # fail if the DUT is not that artifact
#
# EXIT CODES: 0 = warning set matches; 3 = mismatch; 2 = usage/environment.
#
# ASCII-ONLY SOURCE, ON PURPOSE (PowerShell 5.1 reads .ps1 as ANSI).
[CmdletBinding()]
param(
    [string]$Example = "examples/hdl/21-crossclock.typort",
    [string]$Exe = "",
    [int]$ExpectHdl038 = 2,
    [string]$RequireSha256 = "",
    [int]$TimeoutSec = 300,
    [string]$OutDir = "",
    [switch]$Quiet
)

$ErrorActionPreference = "Continue"
. (Join-Path $PSScriptRoot "BoundedProcess.ps1")

$root = Split-Path -Parent $PSScriptRoot
Set-Location $root

if (-not $OutDir) { $OutDir = Join-Path $root "target/crossclock_cli_logs" }
New-Item -ItemType Directory -Force -Path $OutDir | Out-Null

# Resolve the DUT: explicit -Exe wins, else the top-level build, else the freshly
# linked deps product (cargo writes the real artifact there first).
function Resolve-Bin {
    param([string]$Name, [string]$Explicit)
    if ($Explicit) {
        if (Test-Path $Explicit) { return (Resolve-Path $Explicit).Path }
        return $null
    }
    foreach ($cand in @("target/debug/$Name", "target/debug/deps/$Name")) {
        $p = Join-Path $root $cand
        if (Test-Path $p) { return (Resolve-Path $p).Path }
    }
    return $null
}

$exePath = Resolve-Bin -Name "typort.exe" -Explicit $Exe
if (-not $exePath) {
    Write-Host "!! typort.exe not found (looked in target/debug and target/debug/deps)"
    exit 2
}
if (-not (Test-Path $Example)) {
    Write-Host "!! example not found: $Example"
    exit 2
}

$item = Get-Item $exePath
$sha = (Get-FileHash $exePath -Algorithm SHA256).Hash
Write-Host ("== DUT  {0}" -f $exePath)
Write-Host ("== DUT  size={0} mtime={1} sha256={2}" -f $item.Length, $item.LastWriteTime.ToString("yyyy-MM-dd HH:mm:ss"), $sha)
if ($RequireSha256) {
    if ($sha -ne $RequireSha256.ToUpper()) {
        Write-Host ("!! DUT sha256 mismatch: wanted {0}, got {1}" -f $RequireSha256.ToUpper(), $sha)
        exit 2
    }
    Write-Host "== DUT  sha256 matches -RequireSha256"
}

$res = Invoke-BoundedProcess -FilePath $exePath `
    -Arguments @("check", $Example, "--max-infer-ms", "20000") `
    -WorkingDirectory $root -TimeoutSec $TimeoutSec
$text = ($res.Stdout + "`n" + $res.Stderr)

$log = Join-Path $OutDir ("crossclock_cli_" + $sha.Substring(0, 8) + ".log")
$text -split "`n" | Set-Content -Path $log -Encoding UTF8

if ($res.TimedOut) { Write-Host "!! TIMEOUT after ${TimeoutSec}s"; exit 3 }
if ($res.MemExceeded) { Write-Host "!! MEM-LIMIT"; exit 3 }

$lines = @($text -split "`n")
$warnLines = @($lines | Where-Object { $_ -match "warning: \[hdl\]" })
$errCount = @($lines | Where-Object { $_ -match "error:" }).Count

function Count-Code {
    param([string[]]$Lines, [string]$Code)
    return @($Lines | Where-Object { $_ -match ("warning: \[hdl\]\[warning\] " + $Code + " ") }).Count
}

$c038 = Count-Code -Lines $lines -Code "HDL038"
$c036 = Count-Code -Lines $lines -Code "HDL036"
$c037 = Count-Code -Lines $lines -Code "HDL037"
$c039 = Count-Code -Lines $lines -Code "HDL039"

if (-not $Quiet) {
    Write-Host "== warnings (verbatim):"
    if ($warnLines.Count -eq 0) { Write-Host "   (none)" }
    $warnLines | ForEach-Object { Write-Host ("   " + $_.Trim()) }
}

$problems = @()
if ($errCount -ne 0) { $problems += "found $errCount 'error:' line(s)" }
if ($c038 -ne $ExpectHdl038) { $problems += "HDL038 count $c038, expected $ExpectHdl038" }
if ($c036 -ne 0) { $problems += "HDL036 count $c036, expected 0" }
if ($c037 -ne 0) { $problems += "HDL037 count $c037, expected 0" }
if ($c039 -ne 0) { $problems += "HDL039 count $c039, expected 0" }
$joined = ($lines -join "`n")
if ($joined -notmatch "wrPtrSync1") { $problems += "expected chain 'wrPtrSync1' not reported" }
if ($joined -notmatch "rdPtrSync1") { $problems += "expected chain 'rdPtrSync1' not reported" }

Write-Host ("== codes: HDL038={0} HDL036={1} HDL037={2} HDL039={3}  errors={4}  hdl-warning-lines={5}" -f `
    $c038, $c036, $c037, $c039, $errCount, $warnLines.Count)
Write-Host "== log: $log"

if ($problems.Count -gt 0) {
    Write-Host "== MISMATCH:"
    $problems | ForEach-Object { Write-Host ("   - " + $_) }
    exit 3
}
Write-Host ("== OK: warning set is HDL038 x{0}, no HDL036/HDL037/HDL039" -f $ExpectHdl038)
exit 0
