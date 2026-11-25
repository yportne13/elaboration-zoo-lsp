# L13 oracle check: run after any L13 kernel change to confirm behaviour has not drifted.
#
# Usage: powershell -NoProfile -ExecutionPolicy Bypass -File tools/l13_oracle_check.ps1 [-TargetDir target_b13] [-SkipLib]
#
# Checks against the frozen baseline in docs/inheritance/l13-oracle/:
#   1. examples/*.typort output (timing lines normalized) equals out_*.txt byte for byte
#   2. L13 lib test-name set matches l13_lib_tests.txt exactly (no loss, no additions)
#
# Why this exists: during the 2026-11-25 B-route work, zombie typort processes held
# target/release/typort.exe so cargo build silently failed; two rounds ran a stale
# binary and reached wrong conclusions. This script makes binary freshness and
# output comparison part of the process instead of memory.

param(
    [string]$TargetDir = 'target_b13',
    [switch]$SkipLib
)

$ErrorActionPreference = 'Stop'
$root = Split-Path -Parent $PSScriptRoot
$oracle = Join-Path $root 'docs/inheritance/l13-oracle'
$env:CARGO_TARGET_DIR = Join-Path $root $TargetDir
$bin = Join-Path $env:CARGO_TARGET_DIR 'release/typort.exe'
$fail = 0
$TIMING_TAG = '[LOG log] TIMING'

function Step($msg) { Write-Host ('[oracle] ' + $msg) }

function Norm($text) {
    $lines = ($text -replace "`r`n", "`n") -split "`n"
    $out = foreach ($l in $lines) {
        if ($l -match '^\[LOG log\] [a-z_]+ [0-9.]+$') { $TIMING_TAG } else { $l }
    }
    return ($out -join "`n")
}

# Step 0: clear zombie processes (stack overflow leaves 0-thread residues that lock the binary)
# Zombie cleanup is best-effort: some residues cannot be killed (Access denied)
# and merely keep the OLD binary locked. We build into $TargetDir, so they do not
# block the build; only the freshness assertion below matters.
$ErrorActionPreference = 'Continue'
Get-Process -ErrorAction SilentlyContinue |
    Where-Object { $_.ProcessName -match 'typort|elaboration_zoo' } |
    ForEach-Object { try { taskkill /F /T /PID $_.Id 2>&1 | Out-Null } catch { } }
Start-Sleep -Milliseconds 500
$ErrorActionPreference = 'Stop'

# Step 1: build + freshness assertion
Step 'build typort...'
# Warnings go to stderr; PowerShell surfaces every stderr line as an error record,
# which is fatal under ErrorActionPreference=Stop. Run through cmd /c so only the
# exit code matters.
$buildLog = Join-Path $env:CARGO_TARGET_DIR 'build_oracle.log'
cmd /c ('cargo build --release --bin typort > "' + $buildLog + '" 2>&1')
if ($LASTEXITCODE -ne 0) {
    Write-Host 'FAIL: cargo build failed (binary likely locked)' -ForegroundColor Red
    exit 1
}
if (-not (Test-Path $bin)) { Write-Host 'FAIL: binary missing' -ForegroundColor Red; exit 1 }
$binTime = (Get-Item $bin).LastWriteTime
$srcTime = (Get-ChildItem (Join-Path $root 'src') -Recurse -Filter *.rs |
    Sort-Object LastWriteTime -Descending | Select-Object -First 1).LastWriteTime
if ($binTime -lt $srcTime) {
    Write-Host ('FAIL: binary ' + $binTime.ToString('HH:mm:ss') + ' older than source ' + $srcTime.ToString('HH:mm:ss')) -ForegroundColor Red
    exit 1
}
Step ('binary ok: ' + $binTime.ToString('HH:mm:ss') + ' newer than src ' + $srcTime.ToString('HH:mm:ss'))

# Step 2: examples comparison
Step 'compare examples...'
$tmp = Join-Path $env:CARGO_TARGET_DIR 'oracle_tmp'
New-Item -ItemType Directory -Force -Path $tmp | Out-Null
foreach ($f in Get-ChildItem (Join-Path $root 'examples') -Filter *.typort) {
    $out = Join-Path $tmp ($f.BaseName + '.txt')
    $argLine = '"' + $bin + '" check "' + $f.FullName + '" > "' + $out + '" 2>&1'
    cmd /c $argLine | Out-Null
    $a = Norm (Get-Content $out -Raw)
    $refFile = Join-Path $oracle ('out_' + $f.BaseName + '.txt')
    $b = Norm (Get-Content $refFile -Raw)
    if ($a -eq $b) {
        Step ('ok   ' + $f.Name)
    } else {
        Write-Host ('FAIL ' + $f.Name + ': output drifted') -ForegroundColor Red
        $fail = $fail + 1
    }
}

# Step 3: test-name set comparison
Step 'compare test names...'
$listLog = Join-Path $env:CARGO_TARGET_DIR 'list_oracle.log'
cmd /c ('cargo test --release --lib L13_namespace:: -- --list > "' + $listLog + '" 2>&1')
$live = (Select-String ': test$' -Path $listLog | ForEach-Object { $_.Line })
$want = Get-Content (Join-Path $oracle 'l13_lib_tests.txt')
$missing = $want | Where-Object { $live -notcontains $_ }
$added = $live | Where-Object { $want -notcontains $_ }
if ($missing) {
    Write-Host ('FAIL: ' + $missing.Count + ' tests missing') -ForegroundColor Red
    $missing | ForEach-Object { Write-Host ('  - ' + $_) }
    $fail = $fail + 1
}
if ($added) {
    Write-Host ('FAIL: ' + $added.Count + ' new tests (update oracle if intended)') -ForegroundColor Red
    $added | ForEach-Object { Write-Host ('  + ' + $_) }
    $fail = $fail + 1
}
if ((-not $missing) -and (-not $added)) { Step ('ok   ' + $live.Count + ' test names match') }

# Step 4: full lib (optional, slow)
if (-not $SkipLib) {
    Step 'run L13 lib...'
    $testLog = Join-Path $env:CARGO_TARGET_DIR 'test_oracle.log'
    cmd /c ('cargo test --release --lib L13_namespace:: -- --test-threads=1 > "' + $testLog + '" 2>&1')
    Select-String 'test result:' -Path $testLog | ForEach-Object { Step $_.Line }
    if ($LASTEXITCODE -ne 0) {
        Write-Host 'FAIL: lib failures' -ForegroundColor Red
        $fail = $fail + 1
    }
}

if ($fail -eq 0) {
    Write-Host '[oracle] PASS' -ForegroundColor Green
    exit 0
} else {
    Write-Host ('[oracle] ' + $fail + ' failed checks') -ForegroundColor Red
    exit 1
}
