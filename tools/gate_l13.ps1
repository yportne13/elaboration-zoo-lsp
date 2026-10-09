# tools/gate_l13.ps1 -- Windows-native mirror of tools/gate_l13.sh
#
# WHY THIS FILE EXISTS
#   This development host is Windows + PowerShell 5.1. The repo's bash gate
#   (tools/gate_l13.sh) cannot run here: WSL bash on this machine has no cargo,
#   so the .sh gate is unusable for day-to-day work. This script is the Windows
#   equivalent and must stay behaviourally in sync with gate_l13.sh.
#
# SUITES (same four as the .sh gate)
#   lib      cargo test --lib L13_namespace::
#   parity   cargo test --test l13_fast_parity -- --skip L13_namespace::
#            The skip is not a coverage loss: tests/l13_fast_parity.rs re-compiles
#            all of src/L13_namespace/mod.rs via #[path], so the L13 tests would
#            otherwise run a second time. They already ran in the lib suite.
#            Use -Full to drop the skip (parity/normalisation work, release gate).
#   twin     cargo test --test twin_engine_tests        (skip with -SkipTwin)
#   hdl042   cargo test --test hdl042_engine_tests
#
# USAGE
#   powershell -ExecutionPolicy Bypass -File tools/gate_l13.ps1
#   powershell -ExecutionPolicy Bypass -File tools/gate_l13.ps1 -Label myname
#   ... -SkipTwin            # ~80s saved; do NOT skip when touching LSP wiring
#   ... -Full                # full parity (no --skip)
#   ... -CargoTargetDir D:\t # passed straight to cargo; logs go under D:\t
#   ... -CargoArgs --release,--quiet
#   ... -Suites hdl042       # run only some suites (quick smoke / re-check)
#   ... -OutDir target/gate_myname
#   ... -MinLib 600 -MinTwin 30   # raise the per-suite minimum counts
#   ... -MinFreeGB 5              # warn earlier about a filling disk
#   ... -HardMinFreeGB 1          # refuse to start below 1 GB free
#   ... -KillStaleSec 90          # kill probes idle >90s before each suite
#
# EXIT CODE: 0 when every suite passed, 1 when any suite failed (non-zero).
#
# A SUITE ONLY PASSES IF IT ACTUALLY RAN TESTS
#   cargo exits 0 when a filter matches nothing, so a mistyped filter (lowercase
#   `l13` matches no test path) or a wrong --skip would otherwise be certified as
#   a pass. Each suite must therefore produce a `test result:` line with
#   `passed > 0`; a zero-test run is reported as NO-TESTS and fails the gate.
#   tools/gate_l13.sh documents the same trap in its header.
#
# NUMBERS COME FROM THE `test result:` LINES
#   On failure the gate prints the parsed `N passed / M failed` counts and the
#   full `test result:` lines, then a TRUNCATED list of failure messages
#   (clearly labelled). Read the counts, never the truncated list, when
#   quantifying a failure.
#
# PER-SUITE MINIMUM COUNTS
#   `passed > 0` alone is too weak: a suite filtered down to a single test would
#   still pass. Each suite therefore also has a minimum (-MinLib / -MinParity /
#   -MinTwin / -MinHdl042) and reports BELOW-MIN when it is not met, distinct
#   from NO-TESTS (nothing ran at all). The defaults are deliberately
#   CONSERVATIVE FLOOR VALUES, not the exact counts of any one round: the
#   baseline moves (round 2's (F) work took lib from 606 to 608), and a gate
#   that hard-codes today's number turns every legitimate test addition into a
#   false failure. Raise them with the parameters for a stricter local check.
#
# DISK SPACE IS A BUILD PREREQUISITE
#   A nearly full disk is a SECOND candidate cause for the classic
#   `LNK1104: cannot open file ...` / `failed to remove file ... (os error 5)`
#   failures, alongside "a running probe holds the .exe open". The gate prints
#   the free space on the target drive up front, warns below -MinFreeGB
#   (default 2 GB), and exits 2 below -HardMinFreeGB (default 0.5 GB), where a
#   build cannot succeed anyway.
#   MAINTENANCE (confirm before deleting anything):
#     * target/debug/incremental is pure cache -- safe to clear, rebuilds slower.
#     * stale build directories (e.g. an abandoned CARGO_TARGET_DIR) can be huge.
#       Verify no process references them and that nothing in the repo points at
#       them before removing. target/bbwd and target/bbwt were removed after 11
#       days untouched and a repo-wide search found no reference.
#     * never clear target/debug/deps/*.exe that a running probe is using, and
#       never clear the whole target/ while teammates are mid-build.
#
# ASCII-ONLY SOURCE, ON PURPOSE
#   PowerShell 5.1 reads .ps1 files as ANSI unless they carry a BOM. Non-ASCII
#   comments get mojibake'd and can silently swallow the following line -- that
#   already broke a round-1 helper once. Keep every byte of this file ASCII.
#   Logs are UTF-8 and are read with -Encoding UTF8 for the same reason.
#
# NOTE ON ExitCode (why this file does not use Start-Process)
#   A PowerShell 5.1 `Start-Process -PassThru` object with redirected streams
#   does NOT report a usable ExitCode -- it comes back empty even after the
#   process exits, so a passing suite can be counted as a failure and vice
#   versa. All suites run through tools/BoundedProcess.ps1, which uses the .NET
#   Process API and also enforces the per-suite timeout.
#
# CARGO "UPLIFT COPY" PITFALL (see tools/README.md)
#   cargo links the new binary into target/debug/deps/<bin>.exe and then tries to
#   replace target/debug/<bin>.exe. On Windows that replacement fails with
#   `failed to remove file ... (os error 5)` while any probe still holds the exe
#   open -- which makes a perfectly good build look like a compile failure.
#   Each suite is therefore retried once when the log carries that signature.
#   -KillStaleSec N additionally kills probe processes older than N seconds
#   first; it defaults to 0 (never kill anything).
[CmdletBinding()]
param(
    [string]$Label = "gate",
    [string[]]$Suites = @("lib", "parity", "twin", "hdl042"),
    [switch]$SkipTwin,
    [switch]$Full,
    [string]$CargoTargetDir = "",
    [string[]]$CargoArgs = @(),
    [string]$OutDir = "",
    [int]$TimeoutSec = 3600,
    [int]$RetryWaitSec = 20,
    [int]$KillStaleSec = 0,
    [int]$MinLib = 500,
    [int]$MinParity = 15,
    [int]$MinTwin = 27,
    [int]$MinHdl042 = 2,
    [double]$MinFreeGB = 2.0,
    [double]$HardMinFreeGB = 0.5,
    [switch]$Quiet
)

$ErrorActionPreference = "Continue"
. (Join-Path $PSScriptRoot "BoundedProcess.ps1")

# --- locate the repo root from this script's own path (tools/..) -------------
$root = Split-Path -Parent $PSScriptRoot
Set-Location $root

if (-not (Get-Command cargo -ErrorAction SilentlyContinue)) {
    Write-Host "!! cargo not found on PATH -- cannot run the gate"
    exit 2
}

if ($CargoTargetDir) { $env:CARGO_TARGET_DIR = $CargoTargetDir }
$baseDir = if ($CargoTargetDir) { $CargoTargetDir } else { Join-Path $root "target" }
if (-not $OutDir) { $OutDir = Join-Path $baseDir "gate_l13_logs" }
New-Item -ItemType Directory -Force -Path $OutDir | Out-Null

# --- disk precheck: the target drive needs room to link ----------------------
# See the DISK SPACE note in the header. A full disk produces the same
# `failed to remove file ... (os error 5)` / LNK1104 signatures as a locked exe,
# so it is worth ruling out before blaming a probe.
$targetPath = $baseDir
if (-not [System.IO.Path]::IsPathRooted($targetPath)) { $targetPath = Join-Path $root $targetPath }
$targetRoot = [System.IO.Path]::GetPathRoot($targetPath)
$freeGB = $null
try {
    if ($targetRoot) {
        $drv = New-Object System.IO.DriveInfo($targetRoot)
        $freeGB = $drv.AvailableFreeSpace / 1GB
    }
} catch { $freeGB = $null }

if ($null -ne $freeGB) {
    $freeRounded = [math]::Round($freeGB, 2)
    Write-Host ("== disk: {0} GB free on {1} (warn below {2} GB, hard stop below {3} GB)" -f `
        $freeRounded, $targetRoot, $MinFreeGB, $HardMinFreeGB)
    if ($freeGB -lt $HardMinFreeGB) {
        Write-Host ("!! {0} GB free on {1}: below the {2} GB hard floor -- a build cannot succeed here." -f `
            $freeRounded, $targetRoot, $HardMinFreeGB)
        Write-Host "!! free space first; see the DISK SPACE note in this script's header."
        exit 2
    } elseif ($freeGB -lt $MinFreeGB) {
        Write-Host ("!! WARNING: only {0} GB free on {1} (threshold {2} GB)." -f $freeRounded, $targetRoot, $MinFreeGB)
        Write-Host "!! A full disk can also cause 'failed to remove file ... (os error 5)' / LNK1104,"
        Write-Host "!! not only a probe holding the exe open. See the DISK SPACE note in the header."
    }
} else {
    Write-Host "== disk: could not determine free space for $baseDir (precheck skipped)"
}

# Per-suite minimum test counts (see PER-SUITE MINIMUM COUNTS in the header).
function Get-MinForSuite {
    param([string]$Name)
    switch ($Name) {
        "lib"    { return $MinLib }
        "parity" { return $MinParity }
        "twin"   { return $MinTwin }
        "hdl042" { return $MinHdl042 }
        default  { return 0 }
    }
}

# --- suite table: name -> cargo argv ----------------------------------------
# The --skip is a libtest argument, so it must come after `--`.
$skipArgs = @("--", "--skip", "L13_namespace::")
if ($Full) {
    Write-Host "== -Full: parity runs WITHOUT the L13 skip"
    $skipArgs = @()
}

$table = @()
$table += [pscustomobject]@{ Name = "lib";     Argv = @("test", "--lib", "L13_namespace::") + $CargoArgs }
$table += [pscustomobject]@{ Name = "parity";  Argv = @("test", "--test", "l13_fast_parity") + $CargoArgs + $skipArgs }
$table += [pscustomobject]@{ Name = "twin";    Argv = @("test", "--test", "twin_engine_tests") + $CargoArgs }
$table += [pscustomobject]@{ Name = "hdl042";  Argv = @("test", "--test", "hdl042_engine_tests") + $CargoArgs }

$selected = @()
foreach ($s in $table) {
    if ($Suites -contains $s.Name) { $selected += $s }
}
if ($SkipTwin -and ($selected | Where-Object { $_.Name -eq "twin" })) {
    Write-Host "== -SkipTwin: twin_engine_tests skipped (LSP wiring NOT covered this run)"
    $selected = @($selected | Where-Object { $_.Name -ne "twin" })
}
if ($selected.Count -eq 0) {
    Write-Host "!! no suite selected; known suites: lib parity twin hdl042"
    exit 2
}

function Test-ExeLock {
    param([string]$Path)
    if (-not (Test-Path $Path)) { return $false }
    $lines = Get-Content -Path $Path -Encoding UTF8 -ErrorAction SilentlyContinue
    return [bool]($lines | Select-String -Pattern "failed to remove file|os error 5" -ErrorAction SilentlyContinue | Select-Object -First 1)
}

function Stop-StaleProbes {
    param([int]$OlderThanSec)
    if ($OlderThanSec -le 0) { return }
    $killed = 0
    foreach ($pr in @(Get-Process -Name l13bench, typort, elaboration-zoo-lsp -ErrorAction SilentlyContinue)) {
        $age = -1
        try { $age = ((Get-Date) - $pr.StartTime).TotalSeconds } catch { $age = 9999 }
        if ($age -gt $OlderThanSec) {
            Stop-Process -Id $pr.Id -Force -ErrorAction SilentlyContinue
            $killed++
        }
    }
    if ($killed -gt 0) { Write-Host "      (killed $killed stale probe process(es) older than ${OlderThanSec}s)" }
}

# Invoke one cargo suite with a hard timeout and UTF-8 logs. Returns a row.
function Invoke-Suite {
    param([string]$Name, [string[]]$Argv)

    $log = Join-Path $OutDir "$Label-$Name.log"
    $sw = [System.Diagnostics.Stopwatch]::StartNew()
    if (-not $Quiet) { Write-Host "==> [$Name] cargo $($Argv -join ' ')" }

    if ($KillStaleSec -gt 0) { Stop-StaleProbes -OlderThanSec $KillStaleSec }

    $attempt = 0
    $exit = $null
    $timedOut = $false
    while ($true) {
        $attempt++
        $res = Invoke-BoundedProcess -FilePath "cargo" -Arguments $Argv `
            -WorkingDirectory $root -TimeoutSec $TimeoutSec
        $timedOut = $res.TimedOut

        if ($res.StartError) {
            $exit = -1
        } elseif ($timedOut) {
            $exit = 124
        } else {
            $exit = $res.ExitCode
        }
        # cargo writes UTF-8; store the merged streams as UTF-8 so later
        # -Encoding UTF8 reads cannot mojibake them.
        $res.AllLines | Set-Content -Path $log -Encoding UTF8

        # Retry once when the only problem is a locked exe (see header).
        if ($exit -ne 0 -and -not $timedOut -and $attempt -eq 1 -and (Test-ExeLock -Path $log)) {
            Write-Host "      [exe locked by a running probe -- retry in ${RetryWaitSec}s]"
            Start-Sleep -Seconds $RetryWaitSec
            continue
        }
        break
    }
    $sw.Stop()
    $secs = [math]::Round($sw.Elapsed.TotalSeconds, 1)

    $lines = Get-Content -Path $log -Encoding UTF8 -ErrorAction SilentlyContinue
    $results = @()
    foreach ($h in ($lines | Select-String -Pattern "^test result:" -ErrorAction SilentlyContinue)) {
        $results += $h.Line.Trim()
    }

    # Count what actually ran. A ZERO-TEST run is the classic silent pass: a
    # mistyped filter (lowercase `l13` matches nothing) or a wrong --skip makes
    # cargo exit 0 having executed no tests at all -- tools/gate_l13.sh calls
    # this out in its own header. So a suite is only OK when the log contains at
    # least one `test result:` line AND that at least one test passed;
    # otherwise the suite is failed, so this gate can never certify a run that
    # executed nothing.
    $passedTotal = 0
    $failedTotal = 0
    foreach ($line in $results) {
        $m = [regex]::Match($line, "(\d+)\s+passed")
        if ($m.Success) { $passedTotal += [int]$m.Groups[1].Value }
        $m2 = [regex]::Match($line, "(\d+)\s+failed")
        if ($m2.Success) { $failedTotal += [int]$m2.Groups[1].Value }
    }
    $counts = "$passedTotal passed / $failedTotal failed"
    $noTests = (($results.Count -eq 0) -or ($passedTotal -le 0))

    # Per-suite minimum (see PER-SUITE MINIMUM COUNTS in the header). Distinct
    # from NO-TESTS: here tests did run, just far too few -- the signature of a
    # filter that silently matched almost nothing.
    $minExpected = Get-MinForSuite -Name $Name
    $belowMin = ($passedTotal -lt $minExpected)

    # Fallback: if the runner could not read an exit code, decide from the log
    # instead of treating "unknown" as failure. Only a clean set of passing
    # result lines counts; any compile error or FAILED keeps it a failure.
    if ($null -eq $exit -and -not $timedOut) {
        $bad = [bool]($lines | Select-String -Pattern "^error|FAILED|panicked at" -ErrorAction SilentlyContinue | Select-Object -First 1)
        if (-not $noTests -and -not $bad) {
            $exit = 0
            Write-Host "      [exit code unavailable; log has only passing 'test result' lines -- treated as pass]"
        } else {
            $exit = -1
            Write-Host "      [exit code unavailable and log does not prove success -- treated as failure]"
        }
    }
    if ($res.StartError) { Write-Host "      [could not start cargo: $($res.StartError)]" }

    if ($noTests -and -not $timedOut -and $exit -eq 0) {
        $exit = -1
        Write-Host "    [$Name NO-TESTS: exit=0 but the log has no passing 'test result:' line -- treated as FAILURE]"
        Write-Host "      (result lines=$($results.Count), $counts; check the filter and --skip of the suite definition)"
    } elseif ($belowMin -and -not $timedOut -and $exit -eq 0) {
        $exit = -1
        Write-Host "    [$Name BELOW-MIN: $passedTotal passed but the minimum for this suite is $minExpected -- treated as FAILURE]"
        Write-Host "      (tests did run, far too few; check the filter/--skip, or raise -Min$($Name) if the baseline really shrank)"
    }

    if ($exit -eq 0 -and -not $timedOut) {
        Write-Host "    [$Name ok: ${secs}s] $passedTotal/$minExpected passed (min) / $failedTotal failed | $($results -join ' | ')"
    } else {
        if ($timedOut) {
            Write-Host "    [$Name TIMEOUT after ${TimeoutSec}s -- log: $log]"
        } elseif ($noTests) {
            Write-Host "    [$Name FAILED (NO-TESTS) exit=$exit, ${secs}s] $passedTotal/$minExpected passed (min) / $failedTotal failed -- log: $log"
        } elseif ($belowMin) {
            Write-Host "    [$Name FAILED (BELOW-MIN) exit=$exit, ${secs}s] $passedTotal/$minExpected passed (min) / $failedTotal failed -- log: $log"
        } else {
            Write-Host "    [$Name FAILED exit=$exit, ${secs}s] $passedTotal/$minExpected passed (min) / $failedTotal failed -- log: $log"
        }
        # Authoritative counts are the `test result:` lines printed here; the
        # FAILED/panic list after them is deliberately TRUNCATED, so never read
        # a number out of it.
        $results | ForEach-Object { Write-Host "      $_" }
        $maxLines = 40
        $failedLines = @($lines | Select-String -Pattern "^error|FAILED|panicked at" -ErrorAction SilentlyContinue)
        $shown = [math]::Min($maxLines, $failedLines.Count)
        Write-Host "      (failure list: first $shown of $($failedLines.Count) matching lines -- counts above are authoritative)"
        $failedLines | Select-Object -First $maxLines | ForEach-Object { Write-Host ("      " + $_.Line.Trim()) }
    }

    return [pscustomobject]@{
        Name = $Name; Exit = $exit; Secs = $secs; Log = $log
        Results = $results; TimedOut = $timedOut
        Passed = $passedTotal; Failed = $failedTotal; NoTests = $noTests
        Min = $minExpected; BelowMin = $belowMin
    }
}

$t0 = Get-Date
$rows = @()
foreach ($s in $selected) { $rows += Invoke-Suite -Name $s.Name -Argv $s.Argv }

$fail = @($rows | Where-Object { $_.Exit -ne 0 }).Count
$total = [math]::Round(((Get-Date) - $t0).TotalSeconds, 1)
Write-Host ""
Write-Host "== gate_l13[$Label]: total ${total}s, fail=$fail, logs: $OutDir"
foreach ($r in $rows) {
    $flag = ""
    if ($r.NoTests) { $flag = "  [NO TESTS EXECUTED]" }
    elseif ($r.BelowMin) { $flag = "  [BELOW-MIN]" }
    Write-Host ("   {0,-8} exit={1,-4} {2,7}s  {3}/{4} passed (min) / {5} failed{6}" -f `
        $r.Name, $r.Exit, $r.Secs, $r.Passed, $r.Min, $r.Failed, $flag)
}

# A fail=0 only certifies the suites that RAN. Without this line, `-SkipTwin` (or
# a -Suites subset) reads as a full green gate. Name what was left out, so a
# partial run can never be mistaken for full coverage.
$ranNames = @($rows | ForEach-Object { $_.Name })
$notRun = @($table | Where-Object { $ranNames -notcontains $_.Name } | ForEach-Object { $_.Name })
if ($notRun.Count -gt 0) {
    Write-Host ("   NOT RUN: {0}  (fail=0 covers only the suites above)" -f ($notRun -join ", "))
} else {
    Write-Host "   NOT RUN: none (all four suites ran)"
}
if ($fail -gt 0) { exit 1 }
exit 0
