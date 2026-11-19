# L13 重定基基线快照（增量、可断点续跑、单次有上限）。
#
# 背景：l13bench --file 对 hdl prelude 示例单次就要数秒；一次性跑 32 个会把
# 长任务/内存压力带进 DSH（2026-11-17 教训）。本脚本默认每次最多处理 8 个
# 文件、逐行落盘，Ctrl-C/中断后重跑会跳过已完成项（按 Path 去重）。
# 基线表列：Path / Mode / Verdict / Sha256（Verdict = l13bench 判定行，计时丢弃）。
#
# -Mode：all（默认）/ core / hdl。**hdl 模式当前是内存炸弹**（2026-11-19 实测
# examples/hdl/10-bundle.typort 单例 CPU >7 分钟、RSS 峰值约 9.7 GB，见
# docs/l13-baseline-2026-11-17.md §5），批量补 hdl 行前先做内存治理。
param(
  [string]$Out = "tools/l13_baseline_2026-11-17.tsv",
  [int]$Max = 8,
  [ValidateSet("all", "core", "hdl")] [string]$Mode = "all"
)
# l13bench 的判定行含中文（BOTH-FAILED 文案）；显式固定控制台解码为 UTF-8，
# 否则 PS 5.1 按 ANSI 解码会写出乱码文案（2026-11-17 首批 alu 行即此残留）。
try { [Console]::OutputEncoding = New-Object System.Text.UTF8Encoding($false) } catch { }
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
$examples = @(Get-ChildItem (Join-Path $root "examples") -Recurse -Filter *.typort | Sort-Object FullName)
if ($Mode -ne "all") {
  $examples = @($examples | Where-Object {
    $rel = $_.FullName.Substring($root.Length + 1).Replace("\", "/")
    $isHdl = $rel -like "examples/hdl/*"
    if ($Mode -eq "hdl") { $isHdl } else { -not $isHdl }
  })
}
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
  # 用 LF + 无 BOM 追加：与表既有风格一致（.gitattributes eol=lf），且避开
  # PS 5.1 `Add-Content -Encoding UTF8` 在新建文件时写 BOM 的行为。
  $enc = New-Object System.Text.UTF8Encoding($false)
  [IO.File]::AppendAllText($table, ($rel + "`t" + $mode + "`t" + $verdict + "`t" + $hash + "`n"), $enc)
  $n++
  Write-Output ("[{0}] {1} :: {2}" -f $n, $rel, $verdict)
}
$after = @(Import-Csv $table -Delimiter "`t")
$doneAfter = @{}
$after | ForEach-Object { $doneAfter[$_.Path] = $true }
$left = @($examples | Where-Object {
  $rel = $_.FullName.Substring($root.Length + 1).Replace("\", "/")
  -not $doneAfter.ContainsKey($rel)
})
Write-Output ("done this run: {0}; table rows: {1}; in-scope: {2}; in-scope remaining: {3}" -f $n, $after.Count, $examples.Count, $left.Count)
if ($left.Count -gt 0) { Write-Output ("再跑一次即可继续（每次最多 " + $Max + " 个）。") }