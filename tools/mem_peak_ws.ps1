# Peak Working Set measurement for the L02-L13 benches: run one impl in an
# isolated process, poll PeakWorkingSet64 (monotonic; the last read before
# exit is the peak), take the min over N runs.
#
# NOTE: keep this file ASCII-only. Windows PowerShell 5.1 reads BOM-less
# UTF-8 files as ANSI, and mojibake in comments can silently break parsing.
#
# Usage:
#   & tools/mem_peak_ws.ps1 -Impl fast_ss -BenchRounds 50
#   & tools/mem_peak_ws.ps1 -Impl fast    -BenchRounds 50
#   & tools/mem_peak_ws.ps1 -Impl basic   -BenchRounds 1
param(
    [string]$Impl = "fast_ss",
    [int]$Runs = 3,
    [int]$BenchRounds = 50,
    [int]$TimeoutSec = 240
)

$bench = @{
    L02 = "l02bench"; L03 = "l03bench"; L04 = "l04bench"; L05 = "l05bench"
    L06 = "l06bench"; L07 = "l07bench"; L08 = "l08bench"; L09 = "l09bench"
    L10 = "l10bench"; L11 = "l11bench"; L12 = "l12bench"; L13 = "l13bench"
}
# (chapter, workload, max-k) -- k aligned with docs/bench-matrix-2026-09-20.md
$cases = @(
    @("L02", "church", 11), @("L02", "conv", 11), @("L02", "conv_dup", 11), @("L02", "dup", 11), @("L02", "dup_deep", 11),
    @("L03", "church", 11), @("L03", "conv", 11), @("L03", "conv_dup", 11), @("L03", "chain", 11), @("L03", "solve", 11), @("L03", "dup", 11), @("L03", "dup_deep", 11),
    @("L04", "church", 11), @("L04", "implicit", 9), @("L04", "conv", 11), @("L04", "conv_dup", 11), @("L04", "chain", 11), @("L04", "solve", 11), @("L04", "dup", 11), @("L04", "dup_deep", 11),
    @("L05", "church", 11), @("L05", "implicit", 9), @("L05", "prune", 9), @("L05", "conv", 11), @("L05", "conv_dup", 11), @("L05", "chain", 11), @("L05", "solve", 11), @("L05", "dup", 11), @("L05", "dup_deep", 11),
    @("L06", "church", 11), @("L06", "implicit", 9), @("L06", "prune", 9), @("L06", "solve", 11), @("L06", "strchain", 11), @("L06", "global", 11),
    @("L07", "church", 11), @("L07", "strchain", 11), @("L07", "global", 11), @("L07", "match", 11), @("L07", "enum", 9),
    @("L08", "church", 11), @("L08", "strchain", 11), @("L08", "global", 11), @("L08", "match", 11), @("L08", "enum", 9), @("L08", "struct", 11),
    @("L09", "church", 11), @("L09", "strchain", 11), @("L09", "match", 11), @("L09", "enum", 9), @("L09", "struct", 11), @("L09", "universe", 11),
    @("L10", "church", 11), @("L10", "strchain", 11), @("L10", "match", 11), @("L10", "struct", 11), @("L10", "universe", 11), @("L10", "traitchain", 9),
    @("L11", "church", 11), @("L11", "natadd", 11), @("L11", "strchain", 11), @("L11", "match", 11), @("L11", "struct", 11), @("L11", "macro", 11), @("L11", "universe", 11), @("L11", "traitchain", 11),
    @("L12", "church", 11), @("L12", "natadd", 11), @("L12", "strchain", 11), @("L12", "match", 11), @("L12", "struct", 11), @("L12", "traitchain", 11), @("L12", "universe", 11), @("L12", "macro", 11),
    @("L13", "church", 11), @("L13", "natadd", 11), @("L13", "gadt", 9), @("L13", "strchain", 11), @("L13", "match", 11), @("L13", "enum", 9), @("L13", "struct", 11), @("L13", "moduletree", 9), @("L13", "prelude-core", 0)
)
# Reference-side O(n^2) / multi-GB cells: peak WS left to the deterministic
# allocation counters (l02l05mem / l06l13mem); measuring them here costs
# minutes and GBs per cell for no extra signal.
$skipBasic = @(
    "L02|conv_dup", "L02|dup_deep",
    "L03|chain", "L04|chain", "L05|chain", "L05|implicit",
    "L05|prune", "L06|prune", "L06|strchain", "L06|global",
    "L07|strchain", "L07|global", "L08|strchain", "L08|global", "L08|struct",
    "L09|strchain", "L09|struct", "L10|strchain", "L10|struct", "L10|traitchain",
    "L11|strchain", "L11|struct", "L11|macro", "L11|universe", "L11|traitchain",
    "L12|strchain", "L12|struct", "L12|traitchain", "L12|universe", "L12|macro"
)

function Measure-PeakWs {
    param([string]$Bin, [string]$BenchArgs)
    $psi = New-Object System.Diagnostics.ProcessStartInfo
    $psi.FileName = ".\target\release\$Bin.exe"
    $psi.Arguments = $BenchArgs
    $psi.UseShellExecute = $false
    $psi.RedirectStandardOutput = $true
    $psi.RedirectStandardError = $true
    $psi.WorkingDirectory = (Get-Location).Path
    $p = [System.Diagnostics.Process]::Start($psi)
    $peak = 0L
    while (-not $p.HasExited) {
        try {
            $p.Refresh()
            if ($p.PeakWorkingSet64 -gt $peak) { $peak = $p.PeakWorkingSet64 }
        } catch { }
        Start-Sleep -Milliseconds 2
    }
    $p.WaitForExit()
    try {
        $p.Refresh()
        if ($p.PeakWorkingSet64 -gt $peak) { $peak = $p.PeakWorkingSet64 }
    } catch { }
    return $peak
}

"chapter workload        impl      k   peakWS(MB) min-of-$Runs (bench --rounds $BenchRounds)"
foreach ($case in $cases) {
    $ch = $case[0]; $w = $case[1]; $k = $case[2]
    if ($Impl -eq "basic" -and ($skipBasic -contains "$ch|$w")) { continue }
    $bin = $bench[$ch]
    if ($k -eq 0) {
        # prelude-core: no k sweep
        $args = "--workload $w --only $Impl --rounds $BenchRounds"
    } else {
        $args = "--workload $w --max-k $k --only $Impl --rounds $BenchRounds"
    }
    $best = [double]::PositiveInfinity
    for ($i = 0; $i -lt $Runs; $i++) {
        $peak = Measure-PeakWs -Bin $bin -BenchArgs $args
        $mb = $peak / 1MB
        if ($mb -lt $best) { $best = $mb }
    }
    $kk = if ($k -eq 0) { "-" } else { "$k" }
    "{0,-7} {1,-13} {2,-9} {3,3} {4,10:N1}" -f $ch, $w, $Impl, $kk, $best
}
