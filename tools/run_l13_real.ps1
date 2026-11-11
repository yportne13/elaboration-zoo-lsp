# tools/run_l13_real.ps1 — L13 真实负载基准（prelude / examples / 逐文件 / CLI 墙钟）
#
# 前置：cargo build --release --bin l13bench --bin typort
# 说明：L13 是产品层，真实语料就是仓库自带的 prelude（36 个 .typort）与
#       examples（32 个 .typort）；本脚本跑三组：
#       1) 全量 workload：prelude-core / prelude-hdl / examples-hdl
#       2) 逐文件 sweep：core 组（--with-prelude core）与 HDL 组（--with-prelude hdl）
#       3) typort check CLI 墙钟（生产入口，含 prelude 装载）
# 每个进程隔离、轮级 min/median（l13bench 内置）；日志显式写 UTF-8。
param(
    [string]$OutDir = "target/bench_real",
    [int]$CoreRounds = 3,
    [int]$HdlRounds = 2,
    [int]$FileCoreRounds = 2,
    [int]$FileHdlRounds = 1
)

$ErrorActionPreference = "Stop"
$Root = Split-Path -Parent $PSScriptRoot
Set-Location $Root
New-Item -ItemType Directory -Force $OutDir | Out-Null

$Bench = Join-Path $Root "target\release\l13bench.exe"
$Cli = Join-Path $Root "target\release\typort.exe"
if (-not (Test-Path $Bench)) { throw "缺少 $Bench，先跑: cargo build --release --bin l13bench" }

function Save-Utf8Log([string]$Path, [string]$Text) {
    [System.IO.File]::WriteAllText($Path, $Text, [System.Text.UTF8Encoding]::new($false))
}

# 1) 全量真实 workload
foreach ($W in @(
        @{ Name = "prelude-core"; Rounds = $CoreRounds },
        @{ Name = "prelude-hdl"; Rounds = $HdlRounds },
        @{ Name = "examples-hdl"; Rounds = $HdlRounds }
    )) {
    $Log = Join-Path $OutDir "l13_workload_$($W.Name).txt"
    Write-Host "== l13bench --workload $($W.Name) -> $Log"
    $text = (& $Bench --workload $W.Name --rounds $W.Rounds --only basic,fast,fast_ss 2>&1 | Out-String)
    Save-Utf8Log $Log $text
    ($text -split "`r?`n" | Where-Object { $_ -match '^(-- |\s+(basic|fast|fast_ss))' }) | Write-Host
}

# 2) 逐文件 sweep
$CoreFiles = @(
    "examples/adder_proof.typort",
    "examples/theorem_proving.typort",
    "examples/typeclass_complex.typort"
)
$Log = Join-Path $OutDir "l13_file_core.txt"
Write-Host "== l13bench --file core sweep -> $Log"
$all = ""
foreach ($F in $CoreFiles) {
    $all += "### $F`n"
    $all += (& $Bench --file $F --with-prelude core --rounds $FileCoreRounds --only basic,fast,fast_ss 2>&1 | Out-String)
}
Save-Utf8Log $Log $all

$HdlFiles = @(
    "examples/alu.typort",
    "examples/hdl_ops.typort",
    "examples/hdl/01-basics.typort",
    "examples/hdl/09-hierarchy.typort",
    "examples/hdl/10-bundle.typort",
    "examples/hdl/13-adder-tree.typort",
    "examples/hdl/20-misc.typort",
    "examples/hdl/27-blackbox.typort"
)
$Log = Join-Path $OutDir "l13_file_hdl.txt"
Write-Host "== l13bench --file hdl sweep -> $Log"
$all = ""
foreach ($F in $HdlFiles) {
    $all += "### $F`n"
    $all += (& $Bench --file $F --with-prelude hdl --rounds $FileHdlRounds --only basic,fast,fast_ss 2>&1 | Out-String)
}
Save-Utf8Log $Log $all

# 3) typort check CLI 墙钟（生产入口；单次，含 prelude 装载）
if (Test-Path $Cli) {
    $Log = Join-Path $OutDir "l13_typort_check.txt"
    Write-Host "== typort check wall clock -> $Log"
    $lines = ""
    foreach ($F in @(
            "examples/alu.typort",
            "examples/adder_proof.typort",
            "examples/typeclass_complex.typort"
        )) {
        $sw = [System.Diagnostics.Stopwatch]::StartNew()
        & $Cli check $F *> $null
        $code = $LASTEXITCODE
        $sw.Stop()
        $line = "CHECK,$F,$([math]::Round($sw.Elapsed.TotalMilliseconds, 1))ms,exit=$code"
        $lines += "$line`n"
        Write-Host "   $line"
    }
    Save-Utf8Log $Log $lines
} else {
    Write-Host "SKIP typort check: 缺少 $Cli"
}
