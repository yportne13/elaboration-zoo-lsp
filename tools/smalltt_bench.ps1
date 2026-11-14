# smallttbench 一键测量（三组口径，curated sizes；默认约 10-15 分钟）
#   .\tools\smalltt_bench.ps1                    # 全量
#   .\tools\smalltt_bench.ps1 -Only default     # 只跑默认 fuel（as-is 上限）
#   .\tools\smalltt_bench.ps1 -Only fuel        # 只跑放大 fuel（smalltt 规模）
#   .\tools\smalltt_bench.ps1 -Only stlc        # 只跑 stlc 吞吐族
# 日志：target/smalltt_bench/<timestamp>/*.csv（CASE/SKIP 行），汇总：
#   python tools/smalltt_bench_report.py --dir <dir>
param(
  [string]$Only = "all",
  [string]$OutDir = "",
  [int]$Fuel = 20000000,
  [int]$StackMb = 8192
)
$ErrorActionPreference = "Continue"
$root = Split-Path -Parent $PSScriptRoot
Set-Location $root
$exe = Join-Path $root "target\release\smallttbench.exe"
if (-not (Test-Path $exe)) { throw "missing $exe; run: cargo build --release --bin smallttbench" }
if ($OutDir -eq "") { $OutDir = Join-Path $root ("target\smalltt_bench\" + (Get-Date -Format "yyyyMMdd-HHmmss")) }
New-Item -ItemType Directory -Force -Path $OutDir | Out-Null
& { "bench=smallttbench"; "cpu=" + (Get-CimInstance Win32_Processor).Name; "mem_gb=" + [math]::Round((Get-CimInstance Win32_ComputerSystem).TotalPhysicalMemory/1GB,1); "fuel=" + $Fuel; "stack_mb=" + $StackMb; (Get-Date -Format o) } | Out-File -Encoding utf8 (Join-Path $OutDir "env.txt")

function Run-One([string]$tag, [string]$layer, [string]$case, [int]$rounds, [string]$axes, [bool]$useFuel, [string]$sizes) {
  if ($useFuel) {
    $env:TYPORT_UNIFY_FUEL = [string]$Fuel
    $env:SMALLTTBENCH_STACK_MB = [string]$StackMb
  } else {
    Remove-Item Env:TYPORT_UNIFY_FUEL -ErrorAction SilentlyContinue
    Remove-Item Env:SMALLTTBENCH_STACK_MB -ErrorAction SilentlyContinue
  }
  $a = @("--layer", $layer, "--case", $case, "--rounds", $rounds, "--only", $axes)
  if ($sizes -ne "") { $a += @("--sizes", $sizes) }
  $log = Join-Path $OutDir (("{0}_{1}.csv" -f $tag, $layer))
  $sw = [Diagnostics.Stopwatch]::StartNew()
  & $exe @a 2>&1 | Out-File -Encoding utf8 -Append $log
  $sw.Stop()
  Write-Output ("{0,-16} {1,-4} {2,7:N1}s" -f $tag, $layer, $sw.Elapsed.TotalSeconds)
}

# ── 1) 默认 fuel：as-is 可行性 + 上限（conv 大 size 会 SKIP；nf 不受 fuel 限制）──
if ($Only -eq "all" -or $Only -eq "default") {
  foreach ($l in @("L07","L08","L09","L10")) {
    Run-One "default_elab" $l "natconv,treeconv,treeconvm" 5 "ref,twin" $false "1k,2k,3k,4k,5k,10k,10,11,12,15,18"
    Run-One "default_asy"  $l "idtest,vectest,pairtest" 3 "ref,twin" $false ""
    Run-One "default_nf"   $l "forcetree,nftree" 3 "ref_nf,twin_nf" $false "10,12,14,15,18,20"
  }
}
# ── 2) 放大 fuel：smalltt 规模（只 ref/twin，conv 族）──
if ($Only -eq "all" -or $Only -eq "fuel") {
  foreach ($l in @("L07","L08","L09","L10")) {
    Run-One "fuel_nat"  $l "natconv" 3 "ref,twin" $true "5k,10k,100k"
    Run-One "fuel_nat1M" $l "natconv" 1 "ref,twin" $true "1M"
    Run-One "fuel_tree" $l "treeconv,treeconvm" 2 "ref,twin" $true "15,18"
  }
}
# ── 3) stlc 吞吐族（type-in-type 层；L09/L10 不可直译）──
if ($Only -eq "all" -or $Only -eq "stlc") {
  foreach ($l in @("L07","L08")) {
    Run-One "stlc" $l "stlc,stlcs,stlcl" 2 "ref,twin" $false ""
  }
}
Write-Output ("DONE " + $OutDir)
