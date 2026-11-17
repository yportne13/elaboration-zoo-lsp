# L13 重定基基线快照（增量、可断点续跑、单次有上限）。
#
# 背景：l13bench --file 对 hdl prelude 示例单次就要数秒；一次性跑 32 个会把
# 长任务/内存压力带进 DSH（2026-11-17 教训）。本脚本默认每次最多处理 8 个
# 文件、逐行落盘，Ctrl-C/中断后重跑会跳过已完成项（按 Path 去重）。
# 基线表列：Path / Mode / Verdict / Sha256（Verdict = l13bench 判定行，计时丢弃）。
param(
  [string]$Out = "tools/l13_baseline_2026-11-17.tsv",
  [int]$Max = 8
)
$tools = $PSScriptRoot
$root = Split-Path -Parent $tools
$bench = Join-Path $root "target/release/l13bench.exe"
$table = Join-Path $root $Out
if (-not (Test-Path $bench)) { throw "l13bench 未构建：cargo build --release --bin l13bench" }
$done = @{}
if (Test-Path $table) {
  Import-Csv $table -Delimiter "`t" | ForEach-Object { $done[$_.Path] = $true }
} else {
  Set-Content -Path $table -Value "Path`tMode`tVerdict`tSha256" -Encoding UTF8
}
$examples = Get-ChildItem (Join-Path $root "examples") -Recurse -Filter *.typort | Sort-Object FullName
$pending = @($examples | Where-Object {
  $rel = $_.FullName.Substring($root.Length + 1).Replace("\", "/")
  -not $done.ContainsKey($rel)
})
Write-Output ("pending: {0} / total: {1} (max this run: {2})" -f $pending.Count, $examples.Count, $Max)
$n = 0
foreach ($f in $pending) {
  if ($n -ge $Max) { break }
  $rel = $f.FullName.Substring($root.Length + 1).Replace("\", "/")
  $mode = if ($rel -like "examples/hdl/*") { "hdl" } else { "core" }
  $out = & $bench --file $f.FullName --with-prelude $mode --rounds 1 2>&1 | Out-String
  $verdict = ($out -split "`n" | Where-Object { $_ -match "^-- |BOTH|DIFF" } | Select-Object -First 1)
  if ($null -eq $verdict) { $verdict = "NO-VERDICT" } else { $verdict = $verdict.Trim() }
  $sha = [Security.Cryptography.SHA256]::Create()
  $hash = [BitConverter]::ToString($sha.ComputeHash([Text.Encoding]::UTF8.GetBytes($verdict))).Replace("-", "")
  Add-Content -Path $table -Value ($rel + "`t" + $mode + "`t" + $verdict + "`t" + $hash) -Encoding UTF8
  $n++
  Write-Output ("[{0}] {1} :: {2}" -f $n, $rel, $verdict)
}
$after = Import-Csv $table -Delimiter "`t"
Write-Output ("done this run: {0}; recorded: {1} / {2}; remaining: {3}" -f $n, $after.Count, $examples.Count, ($examples.Count - $after.Count))
if ($after.Count -lt $examples.Count) { Write-Output "再跑一次即可继续（每次最多 $Max 个）。" }