# tools/run_crosslayer_ref.ps1 - L07-L13 reference-engine cross-layer benchmark
# (strict same-file corpus + same-family synthetic workloads).
#
# Purpose: measure ONLY the reference engines (`basic` axis) of L07-L13 on the
# release binaries built from the current HEAD, so the numbers can be compared
# across layers.
#
# Loads (same protocol as docs/bench-crosslayer-ref-2026-11-11.md):
#   1. common - 6 files under tools/bench_corpus/common/ that L07-L13 all accept.
#               L07-L12: realbench --only basic (basic = reference bench_check_nf;
#               L11/L12 basic = reference full `run`, i.e. parse+pretty+stdout).
#               L13:     l13bench --file <f> --with-prelude none --only basic.
#   2. synth  - same-family synthetic workloads of each layer's own bench bin.
#               Only families the layer supports; k follows the cross-layer
#               convention (match/church/natadd/strchain=11, enum=9,
#               struct/universe/macro=10).
#   3. real   - appendix: each layer's own real corpus (comparable within a
#               layer, NOT across layers); L13 real prelude/examples workloads.
#
# Timing: min-of-rounds per config, process isolation, serial. The whole suite
# is repeated `Passes` times with alternating layer order (even passes reversed)
# to cancel measurement-window drift; the report takes min across passes.
#
# Usage:
#   cargo build --release --bin realbench --bin l07bench ... --bin l13bench
#   powershell -ExecutionPolicy Bypass -File tools/run_crosslayer_ref.ps1
#   powershell -File tools/run_crosslayer_ref.ps1 -Passes 1 -Tag smoke
#
# Output: target/bench_real/ref_<Tag>/pass<N>_*.txt (UTF-8) + console summary.
param(
    [string]$OutDir = "",
    [int]$Passes = 3,
    [int]$PassStart = 1,
    [string]$Tag = "2026-11-12",
    [int]$RoundsCommon = 5,
    [int]$RoundsSynth = 5,
    [int]$RoundsReal = 3,
    [switch]$SkipCommon,
    [switch]$SkipSynth,
    [switch]$SkipReal
)

$ErrorActionPreference = "Stop"
$Root = Split-Path -Parent $PSScriptRoot
Set-Location $Root
if (-not $OutDir) { $OutDir = "target/bench_real/ref_$Tag" }
New-Item -ItemType Directory -Force $OutDir | Out-Null

$Realbench = Join-Path $Root "target\release\realbench.exe"
$L13bench = Join-Path $Root "target\release\l13bench.exe"
foreach ($exePath in @($Realbench, $L13bench)) {
    if (-not (Test-Path $exePath)) { throw "missing $exePath ; run cargo build --release --bins first" }
}

function Save-Utf8Log([string]$Path, [string]$Text) {
    $enc = New-Object System.Text.UTF8Encoding($false)
    [System.IO.File]::WriteAllText($Path, $Text, $enc)
}

function Invoke-Bench([string]$Log, [string]$Exe, [string[]]$BenchArgs) {
    $text = (& $Exe @BenchArgs 2>&1 | Out-String)
    if ($LASTEXITCODE -ne 0) { throw "$([System.IO.Path]::GetFileName($Exe)) $($BenchArgs -join ' ') exit $LASTEXITCODE" }
    Save-Utf8Log $Log $text
    return $text
}

# ---- workload matrix -------------------------------------------------------
$CommonFiles = @(Get-ChildItem (Join-Path $Root "tools\bench_corpus\common") -File -Filter *.typort |
    Sort-Object Name | ForEach-Object { $_.FullName })

$Synth = [ordered]@{
    L07 = @(
        @{ w = "match"; k = 11 }, @{ w = "church"; k = 11 }, @{ w = "natadd"; k = 11 },
        @{ w = "strchain"; k = 11 }, @{ w = "enum"; k = 9 }
    )
    L08 = @(
        @{ w = "match"; k = 11 }, @{ w = "church"; k = 11 }, @{ w = "natadd"; k = 11 },
        @{ w = "strchain"; k = 11 }, @{ w = "enum"; k = 9 }, @{ w = "struct"; k = 10 }
    )
    L09 = @(
        @{ w = "match"; k = 11 }, @{ w = "church"; k = 11 }, @{ w = "natadd"; k = 11 },
        @{ w = "strchain"; k = 11 }, @{ w = "enum"; k = 9 }, @{ w = "struct"; k = 10 },
        @{ w = "universe"; k = 10 }
    )
    L10 = @(
        @{ w = "match"; k = 11 }, @{ w = "church"; k = 11 }, @{ w = "natadd"; k = 11 },
        @{ w = "strchain"; k = 11 }, @{ w = "struct"; k = 10 }, @{ w = "universe"; k = 10 }
    )
    L11 = @(
        @{ w = "match"; k = 11 }, @{ w = "church"; k = 11 }, @{ w = "natadd"; k = 11 },
        @{ w = "strchain"; k = 11 }, @{ w = "struct"; k = 10 }, @{ w = "universe"; k = 10 },
        @{ w = "macro"; k = 10 }
    )
    L12 = @(
        @{ w = "match"; k = 11 }, @{ w = "church"; k = 11 }, @{ w = "natadd"; k = 11 },
        @{ w = "strchain"; k = 11 }, @{ w = "struct"; k = 10 }, @{ w = "universe"; k = 10 },
        @{ w = "macro"; k = 10 }
    )
    L13 = @(
        @{ w = "match"; k = 11 }, @{ w = "church"; k = 11 }, @{ w = "natadd"; k = 11 },
        @{ w = "strchain"; k = 11 }, @{ w = "enum"; k = 9 }, @{ w = "struct"; k = 10 },
        @{ w = "universe"; k = 10 }, @{ w = "macro"; k = 10 }
    )
}

$RealLayer = @("L07", "L08", "L09", "L10", "L11", "L12")
$Order = @($Synth.Keys)          # L07..L13
$Start = Get-Date

for ($p = $PassStart; $p -lt ($PassStart + $Passes); $p++) {
    $rev = @($Order)
    [array]::Reverse($rev)
    $layers = if ($p % 2 -eq 1) { $Order } else { $rev }
    Write-Host ""
    Write-Host "===== PASS $p/$Passes (order: $($layers -join ',')) ====="

    if (-not $SkipCommon) {
        foreach ($layer in $layers) {
            if ($layer -eq "L13") {
                foreach ($f in $CommonFiles) {
                    $name = [System.IO.Path]::GetFileNameWithoutExtension($f)
                    $log = Join-Path $OutDir ("pass{0}_common_L13_{1}.txt" -f $p, $name)
                    Write-Host "  common $layer $name"
                    Invoke-Bench $log $L13bench @("--file", $f, "--with-prelude", "none", "--rounds", "$RoundsCommon", "--only", "basic") | Out-Null
                }
            }
            else {
                $log = Join-Path $OutDir ("pass{0}_common_{1}.txt" -f $p, $layer)
                Write-Host "  common $layer"
                Invoke-Bench $log $Realbench @("--layer", $layer, "--corpus", "tools\bench_corpus\common", "--rounds", "$RoundsCommon", "--only", "basic") | Out-Null
            }
        }
    }

    if (-not $SkipSynth) {
        $exeMap = @{}
        foreach ($l in $Order) { $exeMap[$l] = Join-Path $Root ("target\release\{0}bench.exe" -f $l.ToLower()) }
        foreach ($layer in $layers) {
            foreach ($item in $Synth[$layer]) {
                $w = $item.w
                $k = $item.k
                $log = Join-Path $OutDir ("pass{0}_synth_{1}_{2}_k{3}.txt" -f $p, $layer, $w, $k)
                Write-Host "  synth $layer $w k=$k"
                if ($layer -eq "L13") {
                    Invoke-Bench $log $L13bench @("--workload", $w, "--max-k", "$k", "--rounds", "$RoundsSynth", "--only", "basic") | Out-Null
                }
                else {
                    Invoke-Bench $log $exeMap[$layer] @("--workload", $w, "--max-k", "$k", "--rounds", "$RoundsSynth", "--only", "basic") | Out-Null
                }
            }
        }
    }

    if (-not $SkipReal) {
        foreach ($layer in $layers) {
            if ($layer -eq "L13") {
                foreach ($w in @("prelude-core", "prelude-hdl", "examples-hdl")) {
                    $log = Join-Path $OutDir ("pass{0}_real_L13_{1}.txt" -f $p, $w)
                    Write-Host "  real L13 $w"
                    Invoke-Bench $log $L13bench @("--workload", $w, "--rounds", "$RoundsReal", "--only", "basic") | Out-Null
                }
            }
            elseif ($RealLayer -contains $layer) {
                $log = Join-Path $OutDir ("pass{0}_real_{1}.txt" -f $p, $layer)
                Write-Host "  real $layer"
                Invoke-Bench $log $Realbench @("--layer", $layer, "--corpus", "tools\bench_corpus\$layer", "--rounds", "$RoundsReal", "--only", "basic") | Out-Null
            }
        }
    }
}

$elapsed = (Get-Date) - $Start
Write-Host ""
Write-Host ("DONE in {0:n1}s -> {1}" -f $elapsed.TotalSeconds, (Join-Path $Root $OutDir))
$count = @(Get-ChildItem (Join-Path $Root $OutDir) -File).Count
Write-Host ("  {0} log files" -f $count)
