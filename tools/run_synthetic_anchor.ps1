# tools/run_synthetic_anchor.ps1 -- synthetic workload anchors at the same HEAD
# binaries, for the "real corpus vs synthetic generator" contrast in the report.
# Each layer runs 1-2 representative workloads (k=10/11, rounds 2-3).
# Logs are written explicitly as UTF-8 (Tee-Object default differs across PS versions).
param(
    [string]$OutDir = "target/bench_real",
    [int]$Rounds = 2
)
$ErrorActionPreference = "Stop"
$Root = Split-Path -Parent $PSScriptRoot
Set-Location $Root
New-Item -ItemType Directory -Force $OutDir | Out-Null

function Invoke-Bench([string]$Name, [string]$Exe, [string[]]$BenchArgs) {
    $Log = Join-Path $OutDir "synthetic_$Name.txt"
    Write-Host "== $Name -> $Log"
    $text = (& (Join-Path $Root "target\release\$Exe") @BenchArgs 2>&1 | Out-String)
    [System.IO.File]::WriteAllText($Log, $text, [System.Text.UTF8Encoding]::new($false))
    ($text -split "`r?`n" | Where-Object { $_ -match '^k=' }) | Write-Host
}

Invoke-Bench "L07_match" "l07bench.exe" @("--workload", "match", "--max-k", "11", "--rounds", "$Rounds", "--only", "basic,fast,fast_ss")
Invoke-Bench "L07_enum" "l07bench.exe" @("--workload", "enum", "--rounds", "$Rounds", "--only", "basic,fast,fast_ss")
Invoke-Bench "L08_struct" "l08bench.exe" @("--workload", "struct", "--max-k", "10", "--rounds", "$Rounds", "--only", "basic,fast,fast_ss")
Invoke-Bench "L08_match" "l08bench.exe" @("--workload", "match", "--max-k", "11", "--rounds", "$Rounds", "--only", "basic,fast,fast_ss")
Invoke-Bench "L09_universe" "l09bench.exe" @("--workload", "universe", "--max-k", "10", "--rounds", "$Rounds", "--only", "basic,fast,fast_ss")
Invoke-Bench "L09_match" "l09bench.exe" @("--workload", "match", "--max-k", "11", "--rounds", "$Rounds", "--only", "basic,fast,fast_ss")
Invoke-Bench "L10_struct" "l10bench.exe" @("--workload", "struct", "--max-k", "10", "--rounds", "$Rounds", "--only", "basic,fast,fast_ss")
Invoke-Bench "L10_match" "l10bench.exe" @("--workload", "match", "--max-k", "11", "--rounds", "$Rounds", "--only", "basic,fast,fast_ss")
Invoke-Bench "L11_macro" "l11bench.exe" @("--workload", "macro", "--max-k", "10", "--rounds", "$Rounds", "--only", "basic,fast_run,fast,fast_ss")
Invoke-Bench "L11_match" "l11bench.exe" @("--workload", "match", "--max-k", "11", "--rounds", "$Rounds", "--only", "basic,fast_run,fast,fast_ss")
Invoke-Bench "L12_macro" "l12bench.exe" @("--workload", "macro", "--max-k", "10", "--rounds", "$Rounds", "--only", "basic,fast_run,fast,fast_ss")
Invoke-Bench "L12_match" "l12bench.exe" @("--workload", "match", "--max-k", "11", "--rounds", "$Rounds", "--only", "basic,fast_run,fast,fast_ss")
