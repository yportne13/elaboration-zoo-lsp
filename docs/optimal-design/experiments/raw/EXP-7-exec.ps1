# EXP-7 串行执行器 v2：直接运行 release 测试二进制（避开 Start-Process 的 NO_PROXY 环境块 bug）
$ErrorActionPreference = 'Continue'
$root = 'F:\projects\hermes\elaboration-zoo-lsp'
$raw  = Join-Path $root 'docs/optimal-design/experiments/raw'
$deps = 'C:\ezl-target\release\deps'
$plan = @(
  @{ n='lib-L07';            exe='elaboration_zoo_lsp'; args=@('L07_sum_type','--test-threads=1') },
  @{ n='lib-L08';            exe='elaboration_zoo_lsp'; args=@('L08_product_type','--test-threads=1') },
  @{ n='l07_blackbox';       exe='l07_blackbox';        args=@('--test-threads=1') },
  @{ n='l07_blackbox_v2';    exe='l07_blackbox_v2';     args=@('--test-threads=1') },
  @{ n='l07_blackbox_v3';    exe='l07_blackbox_v3';     args=@('--test-threads=1') },
  @{ n='l07_fast_parity';    exe='l07_fast_parity';     args=@('--test-threads=1') },
  @{ n='l08_blackbox';       exe='l08_blackbox';        args=@('--test-threads=1') },
  @{ n='l08_blackbox_v2';    exe='l08_blackbox_v2';     args=@('--test-threads=1') },
  @{ n='l08_fast_parity';    exe='l08_fast_parity';     args=@('--test-threads=1') },
  @{ n='l09_fast_parity';    exe='l09_fast_parity';     args=@('--test-threads=1') },
  @{ n='l10_fast_parity';    exe='l10_fast_parity';     args=@('--test-threads=1') },
  @{ n='l11_fast_parity';    exe='l11_fast_parity';     args=@('--test-threads=1') },
  @{ n='l12_fast_parity';    exe='l12_fast_parity';     args=@('--test-threads=1') },
  @{ n='l13_fast_parity';    exe='l13_fast_parity';     args=@('--test-threads=1') },
  @{ n='lib-L13';            exe='elaboration_zoo_lsp'; args=@('L13_namespace','--test-threads=1') },
  @{ n='known_bug_pins';     exe='known_bug_pins';      args=@('--test-threads=1') },
  @{ n='lean_oracle_parity'; exe='lean_oracle_parity';  args=@(); env=@{LEAN_ORACLE='1'} }
)
$csv = Join-Path $raw 'EXP-7-summary.csv'
'name,exit,passed,failed,ignored,secs,result' | Set-Content $csv -Encoding utf8
Push-Location $root
foreach ($item in $plan) {
  $name = $item['n']
  $exe = Get-ChildItem (Join-Path $deps ($item['exe'] + '-*.exe')) -ErrorAction SilentlyContinue | Sort-Object LastWriteTime -Descending | Select-Object -First 1
  if (-not $exe) { Add-Content $csv "$name,99,0,0,0,0,EXE_NOT_FOUND"; "MISSING $name"; continue }
  $a = @($item['args'])
  $envs = $item['env']
  if ($envs) { foreach ($k in @($envs.Keys)) { Set-Item -Path "env:$k" -Value $envs[$k] } }
  $log = Join-Path $raw ("EXP-7-{0}.txt" -f $name)
  "===== START $name  $((Get-Date).ToString('HH:mm:ss'))  exe=$($exe.Name)  args=$($a -join ' ') env=$($(if($envs){($envs.Keys | ForEach-Object { "$_=$($envs[$_])" }) -join ' '}else{''}))" | Tee-Object -FilePath $log
  $t0 = Get-Date
  & $exe.FullName @a 2>&1 | Tee-Object -FilePath $log -Append
  $code = $LASTEXITCODE
  $secs = [math]::Round(((Get-Date) - $t0).TotalSeconds, 1)
  if ($envs) { foreach ($k in @($envs.Keys)) { Remove-Item -Path "env:$k" -ErrorAction SilentlyContinue } }
  $text = Get-Content $log -Raw -ErrorAction SilentlyContinue
  $m = [regex]::Matches($text, 'test result: (\w+)\. (\d+) passed; (\d+) failed; (\d+) ignored')
  if ($m.Count -gt 0) {
    $last = $m[$m.Count-1]
    $res = "passed=$($last.Groups[2].Value) failed=$($last.Groups[3].Value) ignored=$($last.Groups[4].Value)"
    $passed=$last.Groups[2].Value; $failed=$last.Groups[3].Value; $ignored=$last.Groups[4].Value
  } else { $res = 'NO_RESULT_LINE'; $passed=''; $failed=''; $ignored='' }
  Add-Content $csv ("{0},{1},{2},{3},{4},{5},{6}" -f $name,$code,$passed,$failed,$ignored,$secs,$res) -Encoding utf8
  "RESULT $name exit=$code wall=${secs}s $res"
}
Pop-Location
"DONE_ALL $(Get-Date -Format 'HH:mm:ss')"
