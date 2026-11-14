# 同机跑 smalltt 官方基准：每个 .stt 文件一个进程，:l 首载 + :r 热重载 Rounds-1 次。
# 依赖 PATH 中的 cabal / ghc-<GhcVersion>（GHCup 默认 C:\ghcup\bin；见 README §1）。
# 用法：
#   powershell -File run-smalltt-bench.ps1 -SmallttDir F:\_ref\smalltt -OutDir F:\_ref\smalltt-bench -Rounds 3
param(
  [Parameter(Mandatory=$true)][string]$SmallttDir,
  [string]$OutDir = "",
  [int]$Rounds = 3,
  [string]$GhcVersion = "9.4.8",
  [string]$Cabal = "cabal"
)
$ErrorActionPreference = "Continue"
$SmallttDir = (Resolve-Path $SmallttDir).Path
if ($OutDir -eq "") { $OutDir = Join-Path (Split-Path -Parent $SmallttDir) "smalltt-bench" }
New-Item -ItemType Directory -Force -Path $OutDir | Out-Null
Push-Location $SmallttDir
try {
  $exe = (& $Cabal list-bin -w ("ghc-" + $GhcVersion) exe:smalltt) | Select-Object -Last 1
  if (-not (Test-Path $exe)) { throw ("smalltt.exe not found: " + $exe) }
  Write-Output ("exe=" + $exe)
  "exe=$exe" | Out-File -Encoding utf8 (Join-Path $OutDir "env.txt")
  "cpu=" + (Get-CimInstance Win32_Processor).Name | Out-File -Encoding utf8 -Append (Join-Path $OutDir "env.txt")
  "rounds=$Rounds" | Out-File -Encoding utf8 -Append (Join-Path $OutDir "env.txt")
  "date=" + (Get-Date -Format o) | Out-File -Encoding utf8 -Append (Join-Path $OutDir "env.txt")

  $files = @(
    'bench/conv_eval.stt',
    'bench/asymptotics.stt',
    'bench/stlc.stt',
    'bench/stlc5k.stt',
    'bench/stlc10k.stt',
    'bench/stlc_lessimpl5k.stt',
    'bench/stlc_lessimpl10k.stt',
    'bench/stlc_small.stt',
    'bench/stlc_small5k.stt',
    'bench/stlc_small10k.stt'
  )
  foreach ($f in $files) {
    $name = [IO.Path]::GetFileNameWithoutExtension($f)
    $log = Join-Path $OutDir ($name + ".log")
    $lines = @(':l ' + $f)
    for ($i = 1; $i -lt $Rounds; $i++) { $lines += ':r' }
    $lines += ':q'
    $sw = [Diagnostics.Stopwatch]::StartNew()
    ($lines -join ([char]10)) | & $exe 2>&1 | Out-File -Encoding utf8 $log
    $sw.Stop()
    Write-Output ('{0,-24} {1,7:N2}s' -f $name, $sw.Elapsed.TotalSeconds)
  }
  Write-Output "DONE"
} finally {
  Pop-Location
}
