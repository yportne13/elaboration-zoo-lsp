# tools/probe/run_check.ps1 -- bounded `typort check` wrapper (full prelude,
# including show.typort, ~37s per run).
#
# WHEN TO USE THIS INSTEAD OF run_probe.ps1
#   run_probe.ps1 drives l13bench, whose --with-prelude core|hdl deliberately
#   EXCLUDES show.typort. Any probe that prints `.show` therefore fails there --
#   that is a harness limitation, not a probe bug. `typort check` loads the whole
#   prelude (show included) and is the right tool for those probes.
#
# WHY THE BOUNDS ARE MANDATORY
#   `typort check` exits 0 even when the source has errors, so the exit code
#   carries no information and the wrapper must judge the text. It is also the
#   only guard against a diverging elaboration: --max-infer-ms bounds inference
#   but not elaboration, and round 1 saw `typort check` processes outlive their
#   20s budget by minutes while holding target/debug/typort.exe open. Hence the
#   external wall-clock timeout and memory ceiling here.
#
# VERDICTS
#   PASS          no `error:` line, and every println probe produced a value note
#   ERRORS(n)     n lines contained `error:`
#   NO-OUTPUT     a probe with println decls produced zero value notes, or the
#                 whole run produced nothing -- truncated/killed, NOT a pass
#   TIMEOUT / MEM-LIMIT   killed by the external guard
#   INCONCLUSIVE  output present but unclassifiable -- read the raw tail
#   JUDGE-BROKEN  calibration failed; the verdict would be worthless
#
# EXIT CODES
#   0 PASS | 3 non-PASS verdict | 2 usage/environment error | 4 JUDGE-BROKEN
#
# USAGE
#   powershell -ExecutionPolicy Bypass -File tools/probe/run_check.ps1 -File target/x.typort
#   ... -TimeoutSec 300 -MemGB 8 -MaxInferMs 20000
#   ... -Calibrate
#   ... -NoCalibrate        # batch loops only; report the caveat
#
# ASCII-ONLY SOURCE, ON PURPOSE: PowerShell 5.1 reads .ps1 as ANSI, so non-ASCII
# comments mojibake and can swallow the next line.
[CmdletBinding()]
param(
    [string]$File = "",
    [int]$TimeoutSec = 180,
    [double]$MemGB = 6.0,
    [int]$MaxInferMs = 20000,
    [int]$Tail = 60,
    [string]$Exe = "",
    [string]$LogDir = "",
    [switch]$Calibrate,
    [switch]$NoCalibrate
)

$ErrorActionPreference = "Continue"
. (Join-Path (Split-Path -Parent $PSScriptRoot) "BoundedProcess.ps1")
$root = Split-Path -Parent (Split-Path -Parent $PSScriptRoot)
Set-Location $root

if (-not $LogDir) { $LogDir = Join-Path $root "target/probe_logs" }
New-Item -ItemType Directory -Force -Path $LogDir | Out-Null
$calibDir = Join-Path $PSScriptRoot "calib"

# Top-level binary first, target/debug/deps/<bin>.exe as the fallback: cargo
# links the real product there and only then attempts the "uplift copy" into
# target/debug/, which fails while another probe holds the exe open.
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

# Count occurrences of a pattern in a string array, safely.
function Count-Matches {
    param([string[]]$Lines, [string]$Pattern)
    $n = 0
    foreach ($l in $Lines) { if ($l -match $Pattern) { $n++ } }
    return $n
}

function Invoke-BoundedCheck {
    param([string]$ExePath, [string]$ProbeFile, [int]$LimitSec, [double]$LimitGB, [int]$InferMs)
    $res = Invoke-BoundedProcess -FilePath $ExePath `
        -Arguments @("check", $ProbeFile, "--max-infer-ms", "$InferMs") `
        -WorkingDirectory $root -TimeoutSec $LimitSec -MemLimitGB $LimitGB

    # The runner reaps the child and reports its real exit code. `typort check`
    # exits 0 on success, so a non-zero exit with no diagnostics means something
    # outside this wrapper terminated it -- a teammate's build.ps1 kills every
    # running `typort` when it hits the exe lock, which under load truncates a
    # legitimate run. That must not masquerade as "no output from the probe".
    $killed = ""
    if ($res.TimedOut) { $killed = "TIMEOUT" }
    elseif ($res.MemExceeded) { $killed = "MEM-LIMIT" }
    $exited = $res.Exited
    $exitCode = $res.ExitCode
    $secs = $res.Secs

    $lines = @($res.AllLines)

    # typort writes diagnostics to stderr; scanning both streams can only find
    # MORE errors, never fewer, so it is the safe direction.
    $errCount = Count-Matches -Lines $lines -Pattern "error:"
    $noteCount = Count-Matches -Lines $lines -Pattern "note:"
    $printlnCount = 0
    if ($ProbeFile -and (Test-Path $ProbeFile)) {
        $printlnCount = @(Select-String -Path $ProbeFile -Pattern "println" -Encoding UTF8 -ErrorAction SilentlyContinue).Count
    }

    $verdict = ""
    if ($res.StartError) {
        $verdict = "START-FAILED($($res.StartError))"
    } elseif ($killed -ne "") {
        $verdict = $killed
    } elseif ($errCount -gt 0) {
        $verdict = "ERRORS($errCount)"
    } elseif ((-not $exited) -or ($exitCode -ne $null -and $exitCode -ne 0)) {
        $verdict = "EXTERNAL-KILL(exit=$exitCode)"
    } elseif ($lines.Count -eq 0 -or (($lines -join "").Trim().Length -eq 0)) {
        $verdict = "NO-OUTPUT"
    } elseif ($printlnCount -gt 0 -and $noteCount -eq 0) {
        # A truncated run looks exactly like this; never call it a pass.
        $verdict = "NO-OUTPUT(println=$printlnCount, notes=0)"
    } else {
        $verdict = "PASS"
    }

    return [pscustomobject]@{
        Verdict = $verdict; Secs = $secs; PeakGB = $res.PeakGB
        ErrCount = $errCount; NoteCount = $noteCount; PrintlnCount = $printlnCount
        Exited = $exited; ExitCode = $exitCode
        Lines = $lines
    }
}

# Calibration: a probe with a real type error MUST read ERRORS, a valid probe
# MUST read PASS. Without this, a judge that silently stopped matching `error:`
# would report PASS for everything (that is exactly how round 1 produced two
# rounds of bogus "passing" evidence).
#
# Two different failures are distinguished:
#   judge-mismatch  the sample produced classifiable output, but the WRONG class
#                   -> the judge is broken; stop immediately.
#   no-evidence     the sample produced no classifiable output at all (killed by
#                   a peer's build.ps1, timeout, memory ceiling). Retry a few
#                   times; a busy machine must not be reported as a judge bug.
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
        @{ Path = $failSample; Want = "ERRORS" },
        @{ Path = $passSample; Want = "PASS" }
    )
    $ok = $true
    $reason = "ok"
    foreach ($e in $expect) {
        $matched = $false
        for ($i = 1; $i -le $Attempts; $i++) {
            $r = Invoke-BoundedCheck -ExePath $ExePath -ProbeFile $e.Path -LimitSec 120 -LimitGB 4.0 -InferMs 20000
            # ERRORS(n) matches by prefix so the count stays visible.
            $good = ($r.Verdict -eq $e.Want) -or ($e.Want -eq "ERRORS" -and $r.Verdict -like "ERRORS(*")
            $noEvidence = [bool]($r.Verdict -match "^(NO-OUTPUT|EXTERNAL-KILL|TIMEOUT|MEM-LIMIT)")
            $rows += [pscustomobject]@{ Sample = (Split-Path -Leaf $e.Path); Want = $e.Want; Got = $r.Verdict; Good = $good }
            Write-Host ("   [calib] {0,-18} want={1,-10} got={2,-18} {3} ({4}s)" -f `
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

$exePath = Resolve-Bin -Name "typort.exe" -Explicit $Exe
if (-not $exePath) {
    Write-Host "!! typort.exe not found (looked in target/debug and target/debug/deps); build first"
    exit 2
}
Write-Host "== exe: $exePath  ($((Get-Item $exePath).LastWriteTime))"

if ($Calibrate) {
    Write-Host "== judge calibration (expect ERRORS then PASS)"
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
            Write-Host "== JUDGE-UNVERIFIED ($($c.Reason)): could not get usable calibration evidence; refusing to report a verdict"
            Write-Host "== the machine kept killing the child (a peer's build.ps1 kills running typort/l13bench on the exe lock)"
        }
        exit 4
    }
} else {
    Write-Host "== -NoCalibrate: judge NOT verified this run (report this caveat)"
}

$r = Invoke-BoundedCheck -ExePath $exePath -ProbeFile $probePath -LimitSec $TimeoutSec -LimitGB $MemGB -InferMs $MaxInferMs

$log = Join-Path $LogDir ("check_" + [System.IO.Path]::GetFileNameWithoutExtension($probePath) + ".log")
$r.Lines | Set-Content -Path $log -Encoding UTF8

Write-Host ("== run_check {0}s peakWS={1}GB -> {2}  (error lines={3}, note value lines={4}, println={5})" -f `
    $r.Secs, $r.PeakGB, $r.Verdict, $r.ErrCount, $r.NoteCount, $r.PrintlnCount)
Write-Host "== log: $log"
$r.Lines | Select-Object -Last $Tail
if ($r.Verdict -ne "PASS") { exit 3 }
exit 0
