# tools/run_realistic_bench.ps1 — L07–L12 真实语料基准一键复现
#
# 前置：cargo build --release --bin realbench
# 语料：tools/bench_corpus/L07 … L12（每个目录内的 *.typort 都是经 realbench
#       语义闸门验证过的真实程序；来源见各目录 MANIFEST.md）
#
# 用法（Windows PowerShell 5.1 与 pwsh 7 均可）：
#   powershell -ExecutionPolicy Bypass -File tools/run_realistic_bench.ps1
#   pwsh -File tools/run_realistic_bench.ps1 -Layers L07,L10 -Rounds 9
#   pwsh -File tools/run_realistic_bench.ps1 -ValidateOnly
#
# 日志一律显式写 UTF-8（不依赖 Tee-Object 的版本相关默认编码），
# 汇总脚本 tools/bench_real_report.py 按 UTF-8 读取。
param(
    [string]$Layers = "L07,L08,L09,L10,L11,L12",
    [int]$Rounds = 5,
    [int]$Repeat = 1,
    [string]$OutDir = "target/bench_real",
    [switch]$ValidateOnly,
    # 整目录 basic 总时间 < TargetUs 时自动放大 repeat 重跑（短语料稳定化）
    [int]$AutoRepeatTargetUs = 5000
)

$ErrorActionPreference = "Stop"
$Root = Split-Path -Parent $PSScriptRoot
Set-Location $Root
New-Item -ItemType Directory -Force $OutDir | Out-Null

$Exe = Join-Path $Root "target\release\realbench.exe"
if (-not (Test-Path $Exe)) {
    throw "缺少 $Exe，先跑: cargo build --release --bin realbench"
}

function Save-Utf8Log([string]$Path, [string]$Text) {
    [System.IO.File]::WriteAllText($Path, $Text, [System.Text.UTF8Encoding]::new($false))
}

function Get-TotalBasicUs([string]$Text) {
    $line = $Text -split "`r?`n" | Where-Object { $_ -match '^TOTAL,' } | Select-Object -Last 1
    if (-not $line) { return 0 }
    $f = $line.Split(',')
    # TOTAL,layer,n,rounds,repeat,basic,fast_run,fast,fast_ss
    return [int64]$f[5]
}

foreach ($Layer in $Layers.Split(',')) {
    $Layer = $Layer.Trim()
    if (-not $Layer) { continue }
    $Corpus = Join-Path $Root "tools\bench_corpus\$Layer"
    if (-not (Test-Path $Corpus)) {
        Write-Host "MISSING corpus: $Corpus"
        continue
    }
    $Log = Join-Path $OutDir "realbench_$Layer.txt"
    $Args = @("--layer", $Layer, "--corpus", $Corpus)
    if ($ValidateOnly) {
        $Args += @("--validate")
    } else {
        $Args += @("--rounds", "$Rounds", "--repeat", "$Repeat")
    }
    Write-Host "== realbench $Layer -> $Log"
    $text = (& $Exe @Args 2>&1 | Out-String)
    if ($LASTEXITCODE -ne 0) { throw "realbench $Layer 退出码 $LASTEXITCODE" }
    if (-not $ValidateOnly -and $AutoRepeatTargetUs -gt 0) {
        $basic = Get-TotalBasicUs $text
        if ($basic -gt 0 -and $basic -lt $AutoRepeatTargetUs) {
            $auto = [math]::Min(20, [math]::Ceiling($AutoRepeatTargetUs / [double]$basic))
            if ($auto -gt $Repeat) {
                Write-Host "   (basic total=${basic}us < ${AutoRepeatTargetUs}us -> repeat=$auto 重跑)"
                $Args2 = @("--layer", $Layer, "--corpus", $Corpus, "--rounds", "$Rounds", "--repeat", "$auto")
                $text = (& $Exe @Args2 2>&1 | Out-String)
                if ($LASTEXITCODE -ne 0) { throw "realbench $Layer (repeat=$auto) 退出码 $LASTEXITCODE" }
            }
        }
    }
    Save-Utf8Log $Log $text
    ($text -split "`r?`n" | Where-Object { $_ -match '^(SUMMARY|TOTAL)' }) | Write-Host
}
