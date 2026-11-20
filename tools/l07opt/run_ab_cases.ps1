# Measure one smallttbench + l07bench binary on the L07 case set (elab / nf / synthetic).
param(
  [Parameter(Mandatory=$true)][string]$Exe,
  [Parameter(Mandatory=$true)][string]$Tag,
  [Parameter(Mandatory=$true)][string]$OutDir,
  [int]$Rounds = 2,
  [int]$MaxK = 11,
  [switch]$SkipSynth
)
$ErrorActionPreference = 'Continue'
New-Item -ItemType Directory -Force -Path $OutDir | Out-Null
$env:TYPORT_UNIFY_FUEL = '40000000'
$env:SMALLTTBENCH_STACK_MB = '8192'
$sizes = '1k,10k,100k,1M,10,11,12,15,18,20,40,8,80,96,192,1,240,960'
& $Exe --layer L07 --case natconv,treeconv,treeconvm,idtest,pairtest,vectest,stlc,stlcs,stlcl --sizes $sizes --rounds $Rounds --only ref 2>&1 | Out-File -Encoding utf8 (Join-Path $OutDir ('elab_' + $Tag + '.csv'))
& $Exe --layer L07 --case forcetree,nftree --sizes 15,18,20 --rounds $Rounds --only ref_nf 2>&1 | Out-File -Encoding utf8 (Join-Path $OutDir ('nf_' + $Tag + '.csv'))
& $Exe --layer L07 --case forcetree,nftree --sizes 15,18,20 --rounds $Rounds --only ref 2>&1 | Out-File -Encoding utf8 (Join-Path $OutDir ('nfcheck_' + $Tag + '.csv'))
# 单点分配计数（分析模式）
$env:SMALLTTBENCH_ALLOC = '1'
& $Exe --layer L07 --case natconv,pairtest,stlc --sizes 1M,20,80 --rounds 1 --only ref 2>&1 | Out-File -Encoding utf8 (Join-Path $OutDir ('alloc_' + $Tag + '.csv'))
Remove-Item Env:SMALLTTBENCH_ALLOC -ErrorAction SilentlyContinue
if (-not $SkipSynth) {
  $bench = Join-Path (Split-Path $Exe -Parent) 'l07bench.exe'
  if (Test-Path $bench) {
    & $bench --workload all --max-k $MaxK --rounds 3 --only basic 2>&1 | Out-File -Encoding utf8 (Join-Path $OutDir ('synth_' + $Tag + '.txt'))
  } else {
    Write-Output ('missing l07bench.exe next to ' + $Exe)
  }
}
Remove-Item Env:TYPORT_UNIFY_FUEL -ErrorAction SilentlyContinue
Remove-Item Env:SMALLTTBENCH_STACK_MB -ErrorAction SilentlyContinue
Write-Output ('done ' + $Tag)
