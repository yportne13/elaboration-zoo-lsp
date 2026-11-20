# L07 参考版改进的分步 A/B 基准

配合 `docs/smalltt-opt-techniques-analysis-2026-11-20.md` 的分阶段改造（Phase A/B/C），
每一步都用本目录脚本测同一套用例，量化收益并检查回归。

## 流程

1. 保存基线二进制（master 构建，一次即可）：

```powershell
git worktree add C:\ezl-base master
cd C:\ezl-base; cargo build --release --bin smallttbench --bin l07bench
copy target\release\smallttbench.exe <base>\smallttbench.exe
copy target\release\l07bench.exe     <base>\l07bench.exe
```

2. 当前分支构建后跑两遍（同一安静窗口、串行）：

```powershell
powershell -File tools\l07opt\run_ab_cases.ps1 -Exe <base>\smallttbench.exe -Tag base -OutDir target\l07opt
powershell -File tools\l07opt\run_ab_cases.ps1 -Exe target\release\smallttbench.exe -Tag new -OutDir target\l07opt
python tools\l07opt\summarize_ab.py --dir target\l07opt
```

3. 门禁（每一步都必须全绿）：

```powershell
cargo test --release --lib -- L07_sum_type
cargo test --release --test l07_fast_parity
cargo test --release --test l07_blackbox --test l07_blackbox_v2 --test l07_blackbox_v3
target\release\realbench.exe --layer L07 --corpus tools\bench_corpus\L07 --validate
```

## 口径

- `ref` / `ref_nf` 各 2 轮取 min；大转换用 `TYPORT_UNIFY_FUEL=40000000` +
  `SMALLTTBENCH_STACK_MB=8192`（基准专用，默认行为不变）。
- nf 用例的 nf-only = `ref_nf − ref_check`（与 smalltt `[nftime]` 同口径）。
- `alloc_*.csv` 用 `SMALLTTBENCH_ALLOC=1` 采单轮分配计数/字节，只作归因，不计时。
- `synth_*.txt` 是 `l07bench --workload all --max-k 11 --rounds 3 --only basic`。