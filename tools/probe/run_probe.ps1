# tools/probe/run_probe.ps1 -- bounded l13bench probe wrapper.
#
# WHY A WRAPPER AT ALL
#   l13bench has no self-termination guard on the engine: a probe that makes the
#   elaborator diverge runs forever and can grow to several GB (round 1 measured
#   a 13.8 GB process). A bare `l13bench --file x.typort` therefore pins a CPU
#   and a chunk of RAM, and on Windows it also holds target/debug/l13bench.exe
#   open so that every other teammate's `cargo build` fails with
#   `failed to remove file ... (os error 5)`. This wrapper enforces an external
#   wall-clock timeout and a memory ceiling, and it always kills the child.
#
# WHY THE JUDGE IS CALIBRATED BEFORE EVERY RUN
#   Round 1 shipped a judge that scanned only stderr for the failure marker.
#   l13bench prints its [diag] lines -- including the failure marker -- to
#   STDOUT, so that judge returned PASS for EVERY probe, including deliberately
#   broken ones. Two rounds of "evidence" were silently bogus before anyone
#   noticed. This wrapper therefore refuses to report a verdict unless a known-
#   FAILING sample still reads DECL-FAIL and a known-PASSING sample still reads
#   PASS through the very same code path. Calibration costs about 1.5s.
#   Pass -NoCalibrate only inside a tight batch loop, and say so when reporting.
#
# VERDICTS
#   PASS                both engines elaborated every decl (no failure marker)
#   DECL-FAIL           a first-failing decl was reported by an engine
#   PRELUDE-PARSE-FAIL  `prelude PARSE-FAILED` (the builtin prelude is broken)
#   USER-PARSE-FAIL     `parse failed:` for the probe file itself
#   TIMEOUT             killed at -TimeoutSec (engine did not terminate)
#   MEM-LIMIT           killed after exceeding -MemGB working set
#   NO-OUTPUT           no [diag] line and no other marker: nothing to judge
#   INCONCLUSIVE        output present but unclassifiable -- READ THE RAW TAIL
#   JUDGE-BROKEN        calibration failed; the verdict above would be worthless
#
# EXIT CODES
#   0 PASS | 3 non-PASS verdict | 2 usage/environment error | 4 JUDGE-BROKEN
#
# USAGE
#   powershell -ExecutionPolicy Bypass -File tools/probe/run_probe.ps1 -File target/x.typort
#   ... -File target/x.typort -Mode hdl -TimeoutSec 90 -MemGB 6
#   ... -Calibrate                 # only prove the judge still discriminates
#   ... -Exe target/mybin/l13bench.exe   # per-owner copy (see tools/README.md)
#
# NOTE: --with-prelude core|hdl does NOT include show.typort, so `.show` probes
# always fail here. Use tools/probe/run_check.ps1 for show-dependent probes.
#
# ASCII-ONLY SOURCE, ON PURPOSE: PowerShell 5.1 reads .ps1 as ANSI, so non-ASCII
# comments mojibake and can swallow the next line. The Chinese markers below are
# built from codepoints. All logs are read back with -Encoding UTF8.
[CmdletBinding()]
param(
    [string]$File = "",
    [ValidateSet("core", "hdl", "none")][string]$Mode = "core",
    [int]$TimeoutSec = 60,
    [double]$MemGB = 4.0,
    [int]$Tail = 40,
    [string]$Exe = "",
    [string]$LogDir = "",
    [switch]$Calibrate,
    [switch]$NoCalibrate
)

$ErrorActionPreference = "Continue"
. (Join-Path (Split-Path -Parent $PSScriptRoot) "BoundedProcess.ps1")
$root = Split-Path -Parent (Split-Path -Parent $PSScriptRoot)
Set-Location $root

# Markers built from codepoints so this file stays pure ASCII:
#   $M_FAIL = "shou ge shi bai" (first failure), $M_ALL = "quan bu", $M_PASS = "tong guo"
$M_FAIL = [string]([char]0x9996 + [char]0x4E2A + [char]0x5931 + [char]0x8D25)
$M_ALL  = [string]([char]0x5168 + [char]0x90E8)
$M_PASS = [string]([char]0x901A + [char]0x8FC7)
$M_PRELUDE_PARSE_FAILED = "prelude PARSE-FAILED"

if (-not $LogDir) { $LogDir = Join-Path $root "target/probe_logs" }
New-Item -ItemType Directory -Force -Path $LogDir | Out-Null
$calibDir = Join-Path $PSScriptRoot "calib"

# Resolve the binary. The top-level path is the normal one; target/debug/deps/
# <bin>.exe is where cargo puts the freshly linked product before it tries the
# "uplift copy" into target/debug/ -- that copy is what fails while a probe holds
# the exe. Falling back to deps/ keeps the wrapper usable during a lock storm.
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

# Run one probe under the bounds, merge both streams as UTF-8, classify.
function Invoke-BoundedProbe {
    param(
        [string]$ExePath,
        [string]$ProbeFile,
        [string]$PreludeMode,
        [int]$LimitSec,
        [double]$LimitGB
    )
    $env:L13BENCH_DIAG = "1"
    $res = Invoke-BoundedProcess -FilePath $ExePath `
        -Arguments @("--file", $ProbeFile, "--with-prelude", $PreludeMode, "--rounds", "1") `
        -WorkingDirectory $root -TimeoutSec $LimitSec -MemLimitGB $LimitGB

    # The runner reaps the child and reports how it ended, so a non-zero exit
    # with no [diag] output can be told apart from a clean empty run.
    $killed = ""
    if ($res.TimedOut) { $killed = "TIMEOUT" }
    elseif ($res.MemExceeded) { $killed = "MEM-LIMIT" }
    $exited = $res.Exited
    $exitCode = $res.ExitCode
    $secs = $res.Secs

    $outLines = @($res.Stdout -split "`r?`n")
    $errLines = @($res.Stderr -split "`r?`n")
    $text = ($res.Stdout + "`n" + $res.Stderr)
    $errText = $res.Stderr
    $hasDiag = [bool]($text -match "\[diag\]")

    $verdict = ""
    if ($killed -ne "") {
        $verdict = $killed
    } elseif ($text.Trim().Length -eq 0) {
        if ((-not $exited) -or ($exitCode -ne $null -and $exitCode -ne 0)) { $verdict = "EXTERNAL-KILL(exit=$exitCode)" }
        else { $verdict = "NO-OUTPUT" }
    } elseif ($errText -match [regex]::Escape($M_PRELUDE_PARSE_FAILED)) {
        $verdict = "PRELUDE-PARSE-FAIL"
    } elseif ($text.Contains($M_FAIL)) {
        $verdict = "DECL-FAIL"
    } elseif ($text -match "parse failed") {
        $verdict = "USER-PARSE-FAIL"
    } else {
        $twinOk = [bool]($text -match ("\[diag\].*twin " + [regex]::Escape($M_ALL) + " \d+ decls " + [regex]::Escape($M_PASS)))
        $basicOk = [bool]($text -match ("\[diag\].*basic " + [regex]::Escape($M_ALL) + " \d+ decls " + [regex]::Escape($M_PASS)))
        if ($twinOk -and $basicOk) { $verdict = "PASS" }
        elseif (-not $hasDiag) {
            if ((-not $exited) -or ($exitCode -ne $null -and $exitCode -ne 0)) { $verdict = "EXTERNAL-KILL(exit=$exitCode)" }
            else { $verdict = "NO-OUTPUT" }
        }
        else { $verdict = "INCONCLUSIVE" }
    }

    return [pscustomobject]@{
        Verdict = $verdict; Secs = $secs; PeakGB = $res.PeakGB
        Text = $text; Lines = @($res.AllLines)
        Exited = $exited; ExitCode = $exitCode
        StartError = $res.StartError
    }
}

# Calibrate the judge itself: a deliberately broken probe MUST read DECL-FAIL and
# a trivially valid probe MUST read PASS. Anything else means the classification
# above cannot be trusted, and every verdict it produces is worthless.
#
# Two failures are told apart:
#   judge-mismatch  classifiable but WRONG output -> the judge is broken; stop.
#   no-evidence     no classifiable output at all (killed by a peer's build.ps1,
#                   timeout, memory ceiling) -> retry; a busy machine is not a bug.
function Invoke-Calibration {
    param([string]$ExePath, [int]$Attempts = 3)
    $rows = @()
    $failSample = Join-Path $calibDir "fail_decl.typort"
    $passSample = Join-Path $calibDir "pass_decl.typort"
    if (-not (Test-Path $failSample) -or -not (Test-Path $passSample)) {
        Write-Host "!! calibration samples missing under $calibDir"
        return [pscustomobject]@{ Ok = $false; Reason = "samples-missing"; Rows = @() }
    }
    $expect = @(
        @{ Path = $failSample; Want = "DECL-FAIL" },
        @{ Path = $passSample; Want = "PASS" }
    )
    $ok = $true
    $reason = "ok"
    foreach ($e in $expect) {
        $matched = $false
        for ($i = 1; $i -le $Attempts; $i++) {
            $r = Invoke-BoundedProbe -ExePath $ExePath -ProbeFile $e.Path -PreludeMode "core" -LimitSec 60 -LimitGB 3.0
            $good = ($r.Verdict -eq $e.Want)
            $noEvidence = [bool]($r.Verdict -match "^(NO-OUTPUT|EXTERNAL-KILL|TIMEOUT|MEM-LIMIT)")
            $rows += [pscustomobject]@{
                Sample = (Split-Path -Leaf $e.Path); Want = $e.Want
                Got = $r.Verdict; Good = $good; Secs = $r.Secs
            }
            Write-Host ("   [calib] {0,-18} want={1,-10} got={2,-12} {3} ({4}s)" -f `
                (Split-Path -Leaf $e.Path), $e.Want, $r.Verdict, $(if ($good) { "OK" } else { "MISMATCH" }), $r.Secs)
            if ($good) { $matched = $true; break }
            if ($noEvidence -and $i -lt $Attempts) {
                Write-Host ("   [calib] no evidence (verdict $($r.Verdict)) -- retrying sample ($i/$Attempts)")
                continue
            }
            if (-not $noEvidence) {
                Write-Host "   [calib] classifiable but WRONG -- the judge itself is broken"
                $reason = "judge-mismatch"
            } else {
                Write-Host "   [calib] no usable evidence after $Attempts attempts (machine kept killing the child)"
                $reason = "no-evidence"
            }
            break
        }
        if (-not $matched) { $ok = $false }
    }
    return [pscustomobject]@{ Ok = $ok; Reason = $reason; Rows = $rows }
}

$exePath = Resolve-Bin -Name "l13bench.exe" -Explicit $Exe
if (-not $exePath) {
    Write-Host "!! l13bench.exe not found (looked in target/debug and target/debug/deps); build first"
    exit 2
}
Write-Host "== exe: $exePath  ($((Get-Item $exePath).LastWriteTime))"

if ($Calibrate) {
    Write-Host "== judge calibration (expect DECL-FAIL then PASS)"
    $c = Invoke-Calibration -ExePath $exePath
    if ($c.Ok) { Write-Host "== calibration OK -- judge discriminates"; exit 0 }
    Write-Host "== calibration FAILED ($($c.Reason)) -- judge cannot be trusted (JUDGE-BROKEN)"
    exit 4
}

if (-not $File) {
    Write-Host "!! -File is required (or use -Calibrate)"
    exit 2
}
if (-not (Test-Path $File)) {
    Write-Host "!! probe file not found: $File"
    exit 2
}
$probePath = (Resolve-Path $File).Path

if (-not $NoCalibrate) {
    $c = Invoke-Calibration -ExePath $exePath
    if (-not $c.Ok) {
        if ($c.Reason -eq "judge-mismatch") {
            Write-Host "== JUDGE-BROKEN: calibration produced classifiable but WRONG output; refusing to report a verdict"
        } else {
            Write-Host "== JUDGE-UNVERIFIED ($($c.Reason)): no usable calibration evidence; refusing to report a verdict"
            Write-Host "== the machine kept killing the child (a peer's build.ps1 kills running typort/l13bench on the exe lock)"
        }
        Write-Host "== re-run with -Calibrate for detail, or fix the judge before trusting any probe result"
        exit 4
    }
} else {
    Write-Host "== -NoCalibrate: judge NOT verified this run (report this caveat)"
}

$r = Invoke-BoundedProbe -ExePath $exePath -ProbeFile $probePath -PreludeMode $Mode `
     -LimitSec $TimeoutSec -LimitGB $MemGB

$log = Join-Path $LogDir ("probe_" + [System.IO.Path]::GetFileNameWithoutExtension($probePath) + "_" + $Mode + ".log")
$r.Lines | Set-Content -Path $log -Encoding UTF8

Write-Host ("== run_probe [{0}] {1}s peakWS={2}GB -> {3}" -f $Mode, $r.Secs, $r.PeakGB, $r.Verdict)
Write-Host "== log: $log"
$r.Lines | Select-Object -Last $Tail
if ($r.Verdict -eq "INCONCLUSIVE") {
    Write-Host "== INCONCLUSIVE: read the raw tail above; do NOT record this as a pass"
}
if ($r.Verdict -ne "PASS") { exit 3 }
exit 0
