# EXP-7 收尾：先做 D4 独立复核复跑（安静窗口），再跑 LSP 4 套件 + lib L09–L12 过滤
$ErrorActionPreference = 'Continue'
$root = 'F:\projects\hermes\elaboration-zoo-lsp'
$raw  = Join-Path $root 'docs/optimal-design/experiments/raw'
$b    = 'C:\ezl-target\release'
Set-Location $root

function RunLog($name, $exeName, $arglist) {
  $log = Join-Path $raw ("EXP-7-{0}.txt" -f $name)
  $t0 = Get-Date
  "===== START $name  $($t0.ToString('HH:mm:ss'))  exe=$exeName  args=$($arglist -join ' ')" | Tee-Object -FilePath $log
  & (Join-Path $b $exeName) @arglist 2>&1 | Tee-Object -FilePath $log -Append
  $code = $LASTEXITCODE
  $secs = [math]::Round(((Get-Date) - $t0).TotalSeconds, 1)
  $text = Get-Content $log -Raw -ErrorAction SilentlyContinue
  $m = [regex]::Matches($text, 'test result: (\w+)\. (\d+) passed; (\d+) failed; (\d+) ignored')
  if ($m.Count -gt 0) {
    $last = $m[$m.Count-1]
    $res = "passed=$($last.Groups[2].Value) failed=$($last.Groups[3].Value) ignored=$($last.Groups[4].Value)"
  } else { $res = 'NO_RESULT_LINE' }
  "RESULT $name exit=$code wall=${secs}s $res"
}

# ---------- A. D4 独立复核复跑（同命令、正确参数；安静窗口先跑） ----------
RunLog 'review2-exp1-church4000' 'l01bench.exe' @('--max-church','4000','--rounds','3','--workload','church','--only','bump_spine_iter_ss,naive')
RunLog 'review2-exp3-l07-match'  'l07bench.exe' @('--workload','match','--max-k','11','--rounds','3')
$t0 = Get-Date
$logT = Join-Path $raw 'EXP-7-review2-exp6-typort-alu.txt'
"### typort check examples/alu.typort" | Tee-Object -FilePath $logT
& (Join-Path $b 'typort.exe') check examples/alu.typort 2>&1 | Tee-Object -FilePath $logT -Append | Select-Object -Last 3
"RESULT review2-exp6-typort exit=$LASTEXITCODE wall=$([math]::Round(((Get-Date)-$t0).TotalSeconds,2))s"
RunLog 'review2-exp5-l10-traitchain' 'l06l13mem.exe' @('--chapter','L10','--workload','traitchain','--k','9','--rounds','3')

# ---------- B. 剩余套件：LSP 4 + lib L09–L12 ----------
$csv = Join-Path $raw 'EXP-7-summary2.csv'
'name,exit,passed,failed,ignored,secs,result' | Set-Content $csv -Encoding utf8
$plan = @(
  @{ n='lsp-namespace_tests'; exe='namespace_tests';  args=@('--test-threads=1') },
  @{ n='lsp-hover_tests';     exe='hover_tests';      args=@('--test-threads=1') },
  @{ n='lsp-completion_tests';exe='completion_tests'; args=@('--test-threads=1') },
  @{ n='lsp-cross_file_tests';exe='cross_file_tests'; args=@('--test-threads=1') },
  @{ n='lib-L09'; exe='elaboration_zoo_lsp'; args=@('L09_mltt','--test-threads=1') },
  @{ n='lib-L10'; exe='elaboration_zoo_lsp'; args=@('L10_typeclass','--test-threads=1') },
  @{ n='lib-L11'; exe='elaboration_zoo_lsp'; args=@('L11_macro','--test-threads=1') },
  @{ n='lib-L12'; exe='elaboration_zoo_lsp'; args=@('L12_canonical','--test-threads=1') }
)
foreach ($item in $plan) {
  $name = $item['n']
  $exe = Get-ChildItem (Join-Path 'C:\ezl-target\release\deps' ($item['exe'] + '-*.exe')) | Sort-Object LastWriteTime -Descending | Select-Object -First 1
  $a = @($item['args'])
  $log = Join-Path $raw ("EXP-7-{0}.txt" -f $name)
  $t0 = Get-Date
  "===== START $name $($t0.ToString('HH:mm:ss')) exe=$($exe.Name)" | Tee-Object -FilePath $log
  & $exe.FullName @a 2>&1 | Tee-Object -FilePath $log -Append
  $code = $LASTEXITCODE
  $secs = [math]::Round(((Get-Date) - $t0).TotalSeconds, 1)
  $text = Get-Content $log -Raw
  $m = [regex]::Matches($text, 'test result: (\w+)\. (\d+) passed; (\d+) failed; (\d+) ignored')
  if ($m.Count -gt 0) { $last=$m[$m.Count-1]; $res="passed=$($last.Groups[2].Value) failed=$($last.Groups[3].Value) ignored=$($last.Groups[4].Value)" } else { $res='NO_RESULT_LINE' }
  Add-Content $csv ("{0},{1},{2},{3},{4}" -f $name,$code,$secs,$res,'') -Encoding utf8
  "RESULT $name exit=$code wall=${secs}s $res"
}
"ALL_DONE $(Get-Date -Format 'HH:mm:ss')"
