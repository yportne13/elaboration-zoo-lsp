# 基准"看门狗"运行器：给任意长任务加墙钟上限与 RSS 上限，并回报峰值。
#
# 为什么存在：`l13bench --with-prelude hdl` 在本机可吃掉 2.4GB（正常 prelude）
# 到 >12GB（bundle 示例）内存，裸跑会把整机拖垮（2026-11-19 两次机器级事故）。
# 任何需要"跑一次但可能爆"的命令都走这里。
#
# 用法：
#   & ./tools/bench_watchdog.ps1 -Exe target\release\l13bench.exe `
#       -ArgList @('--file','examples/hdl/10-bundle.typort','--with-prelude','hdl','--rounds','1') `
#       -TimeoutSec 300 -CapMB 12000
#
# 输出：一行 `WATCHDOG elapsed_s=… peak_rss_mb=… killed=… exit=…` + stdout/stderr 尾部。

param(
  [Parameter(Mandatory=$true)][string]$Exe,
  [string[]]$ArgList = @(),
  [int]$TimeoutSec = 60,
  [int]$CapMB = 4000
)
$tag = [guid]::NewGuid().ToString('N').Substring(0,8)
$out = Join-Path $env:TEMP ("wd-$tag.out.txt")
$err = Join-Path $env:TEMP ("wd-$tag.err.txt")
$p = Start-Process -FilePath $Exe -ArgumentList $ArgList -NoNewWindow -PassThru -RedirectStandardOutput $out -RedirectStandardError $err
$sw = [Diagnostics.Stopwatch]::StartNew()
$peak = 0
$killed = $false
while (-not $p.HasExited) {
  Start-Sleep -Milliseconds 400
  try {
    $p.Refresh()
    $mb = [int]($p.WorkingSet64 / 1MB)
    if ($mb -gt $peak) { $peak = $mb }
    if ($mb -gt $CapMB -or $sw.Elapsed.TotalSeconds -gt $TimeoutSec) { try { $p.Kill() } catch { }; $killed = $true; break }
  } catch { break }
}
try { $p.WaitForExit(5000) | Out-Null } catch { }
$sw.Stop()
"WATCHDOG elapsed_s=$([math]::Round($sw.Elapsed.TotalSeconds,1)) peak_rss_mb=$peak killed=$killed exit=$($p.ExitCode)"
"--- stdout tail ---"
Get-Content $out -Tail 6 -ErrorAction SilentlyContinue
"--- stderr tail ---"
Get-Content $err -Tail 4 -ErrorAction SilentlyContinue
Remove-Item $out, $err -ErrorAction SilentlyContinue
