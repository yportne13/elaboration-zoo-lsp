param(
  [Parameter(Mandatory=$true)][string]$Exe,
  [string[]]$ArgList = @(),
  [int]$TimeoutSec = 60,
  [int]$CapMB = 4000
)
# 人读摘要走 Write-Host（不进管道），结果对象走 Write-Output：调用方用
# `$r = & 脚本` 拿到的是对象，而不是多行字符串（PS 5.1 下数组有时会被拍平成
# 空格分隔的单串，2026-11-20 基线采集踩过这个坑）。
$tag = [guid]::NewGuid().ToString('N').Substring(0,8)
$outFile = Join-Path $env:TEMP ('wd-' + $tag + '.out.txt')
$errFile = Join-Path $env:TEMP ('wd-' + $tag + '.err.txt')
$p = Start-Process -FilePath $Exe -ArgumentList $ArgList -NoNewWindow -PassThru -RedirectStandardOutput $outFile -RedirectStandardError $errFile
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
$lines = @()
if (Test-Path $outFile) { $lines = @(Get-Content $outFile -Encoding UTF8 -ErrorAction SilentlyContinue) }
$errLines = @()
if (Test-Path $errFile) { $errLines = @(Get-Content $errFile -Encoding UTF8 -ErrorAction SilentlyContinue) }
Remove-Item $outFile, $errFile -ErrorAction SilentlyContinue

$verdict = ($lines | Where-Object { $_ -match '^-- .*\.typort' } | Select-Object -First 1)
if ($verdict) { $verdict = $verdict.Trim() } else { $verdict = $null }

Write-Host ('WATCHDOG elapsed_s={0} peak_rss_mb={1} killed={2} exit={3}' -f [math]::Round($sw.Elapsed.TotalSeconds,1), $peak, $killed, $p.ExitCode)
if ($verdict) { Write-Host ('  ' + $verdict) }
$lines | Select-Object -Last 4 | ForEach-Object { Write-Host ('  | ' + $_) }
if ($errLines.Count -gt 0) { Write-Host ('  stderr: ' + ($errLines | Select-Object -Last 1)) }

[pscustomobject]@{
  Verdict    = $verdict
  ElapsedSec = [math]::Round($sw.Elapsed.TotalSeconds,1)
  PeakMB     = $peak
  Killed     = $killed
  ExitCode   = $p.ExitCode
  Lines      = $lines
}
