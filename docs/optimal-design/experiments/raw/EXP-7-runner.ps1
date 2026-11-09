# EXP-7 测试执行 runner（只被 analyst-l09 / EXP-7 使用；结果追加到 raw/EXP-7-summary.csv）
# 用法：
#   pwsh -NoProfile -File docs/optimal-design/experiments/raw/EXP-7-runner.ps1 -Name l07_blackbox -Mode test [-Threads 1] [-Env @{LEAN_ORACLE='1'}]
#   pwsh -NoProfile -File docs/optimal-design/experiments/raw/EXP-7-runner.ps1 -Name "lib-L07" -Mode lib -Filter L07_sum_type -Threads 1
# 产物：raw/EXP-7-<Name>.txt（完整输出）；raw/EXP-7-summary.csv（每行一条：name,exit,passed,failed,ignored,secs,result_line）
param(
  [Parameter(Mandatory=$true)][string]$Name,
  [Parameter(Mandatory=$true)][ValidateSet('test','lib','bin')][string]$Mode,
  [string]$Filter = '',
  [int]$Threads = 0,
  [hashtable]$Env = @{},
  [switch]$NoBuild
)
$ErrorActionPreference = 'Continue'
$root = 'F:\projects\hermes\elaboration-zoo-lsp'
$raw  = Join-Path $root 'docs/optimal-design/experiments/raw'
$env:CARGO_TARGET_DIR = 'C:\ezl-target'
$env:CARGO_TERM_COLOR = 'never'
$env:RUST_BACKTRACE = '1'
foreach ($k in $Env.Keys) { Set-Item -Path "env:$k" -Value $Env[$k] }

$argsList = @('test','--release')
if ($Mode -eq 'lib') { $argsList += '--lib' }
elseif ($Mode -eq 'test') { $argsList += @('--test', $Name) }
else { $argsList += @('--bin', $Name) }
if ($NoBuild) { $argsList += '--no-fail-fast' }
if ($Filter -ne '') { $argsList += @('--', $Filter) } else { $argsList += @('--') }
if ($Threads -gt 0) { $argsList += "--test-threads=$Threads" }

$log = Join-Path $raw ("EXP-7-{0}.txt" -f $Name)
$start = Get-Date
"# EXP-7 run: name=$Name mode=$Mode filter=$Filter threads=$Threads env=$($Env | ConvertTo-Json -Compress)" | Out-File -FilePath $log -Encoding utf8
"# start=$($start.ToString('yyyy-MM-dd HH:mm:ss')) cwd=$root target=$env:CARGO_TARGET_DIR" | Out-File -FilePath $log -Append -Encoding utf8
"# command: cargo $($argsList -join ' ')" | Out-File -FilePath $log -Append -Encoding utf8

Push-Location $root
& cargo @argsList 2>&1 | Tee-Object -FilePath $log -Append
$code = $LASTEXITCODE
Pop-Location
$secs = [math]::Round(((Get-Date) - $start).TotalSeconds, 1)

$text = Get-Content $log -Raw -ErrorAction SilentlyContinue
$m = [regex]::Matches($text, 'test result: (\w+)\. (\d+) passed; (\d+) failed; (\d+) ignored')
if ($m.Count -gt 0) {
  $last = $m[$m.Count-1]
  $passed = $last.Groups[2].Value; $failed = $last.Groups[3].Value; $ignored = $last.Groups[4].Value
  $result = "passed=$passed failed=$failed ignored=$ignored"
} else {
  $passed=''; $failed=''; $ignored=''; $result = 'NO_RESULT_LINE'
}
$line = "{0},{1},{2},{3},{4},{5},{6},{7}" -f $Name, $code, $passed, $failed, $ignored, $secs, $Mode, $result
Add-Content -Path (Join-Path $raw 'EXP-7-summary.csv') -Value $line -Encoding utf8
"SUMMARY: $line  (wall ${secs}s, exit=$code)"
if ($failed -ne '' -and [int]$failed -gt 0) { "FAILED_TESTS:"; Select-String -Path $log -Pattern '^failures:|^    [A-Za-z0-9_:]+$' | Select-Object -First 40 | ForEach-Object { $_.Line } }
exit $code
