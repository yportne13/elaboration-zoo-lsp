# 分支最终性能测试（2026-11-10）

- 基线：master `3093b62e`（`C:\ezl-perf-bin\base` 的 bench 二进制）
- 对比：`feat/all-layers-hardening` @ `b836ab01`（当前分支）
- 本机：Windows；安静窗口；每项 A/B/B/A 交错、3 轮（L13 prelude-hdl 2 轮），取 min/median
- 参数：reference 统一 `--only basic`；k/r 见 workload 列；L07/L08 的 twin 用 `--only fast_ss`
- 原始数据：`C:\ezl-perf-bin\final-perf.csv`、`final-perf-fast.csv`

## 1. 参考版（basic）主矩阵

| 层 | workload | master | branch | 比值 |
|---|---|---:|---:|---:|
| L07 | church k10 | 1.333 ms | 0.719 ms | **0.539×** |
| L07 | strchain k11 | 9.012 ms | 8.049 ms | 0.893× |
| L07 | match k13 | 0.133 ms | 0.109 ms | 0.820× |
| L07 | natadd k10 | 2.544 ms | 1.688 ms | **0.664×（1.51×）** |
| L08 | church k10 | 1.584 ms | 0.723 ms | **0.456×** |
| L08 | strchain k11 | 124.612 ms | 7.845 ms | **0.063×（15.9×）** |
| L08 | global k10 | 37.145 ms | 6.342 ms | **0.171×（5.9×）** |
| L08 | struct k10 | 37.182 ms | 5.385 ms | **0.145×（6.9×）** |
| L08 | match k13 | 0.162 ms | 0.099 ms | 0.611× |
| L08 | natadd k10 | 3.779 ms | 1.478 ms | **0.391×（2.56×）** |
| L09 | church k10 | 1.565 ms | 1.227 ms | 0.784× |
| L09 | strchain k10 | 16.406 ms | 15.837 ms | 0.965× |
| L09 | match k13 | 0.166 ms | 0.127 ms | 0.765× |
| L09 | universe k10 | 2.389 ms | 2.285 ms | 0.956× |
| L09 | enum k10 | 0.714 ms | 0.659 ms | 0.923× |
| L09 | natadd k10 | 3.737 ms | 1.851 ms | **0.495×（2.02×）** |
| L10 | church k10 | 0.728 ms | 0.743 ms | 1.021× |
| L10 | strchain k10 | 15.282 ms | 15.108 ms | 0.989× |
| L10 | match k13 | 0.101 ms | 0.100 ms | 0.990× |
| L10 | universe k10 | 2.459 ms | 2.422 ms | 0.985× |
| L10 | struct k10 | 42.816 ms | 42.628 ms | 0.996× |
| L10 | natadd k10 | 0.960 ms | 0.954 ms | 0.994× |
| L11 | church k10 | 0.816 ms | 0.776 ms | 0.951× |
| L11 | macro k10 | 167.812 ms | 12.371 ms | **0.074×（13.6×）** |
| L11 | struct k10 | 161.173 ms | 14.126 ms | **0.088×（11.4×）** |
| L11 | natadd k11 | 1.872 ms | 1.693 ms | 0.904× |
| L11 | strchain k10 | 163.715 ms | 11.506 ms | **0.070×（14.2×）** |
| L12 | natadd k11 | 1.669 ms | 1.480 ms | 0.887× |
| L12 | strchain k10 | 145.035 ms | 10.332 ms | **0.071×（14.0×）** |
| L12 | macro k10 | 148.429 ms | 11.215 ms | **0.076×（13.2×）** |
| L12 | church k10 | 0.808 ms | 0.781 ms | 0.967× |
| L13 | prelude-core | 53.057 ms | 41.542 ms | **0.783×** |
| L13 | prelude-hdl | 4995.976 ms | 4599.692 ms | 0.921× |
| L13 | match k11 | 0.203 ms | 0.143 ms | **0.704×** |
| L13 | church k10 | 1.256 ms | 1.114 ms | 0.887× |
| L13 | enum k10 | 0.486 ms | 0.336 ms | **0.691×** |

## 2. fast_ss（L07/L08 twin）

| 层 | workload | master | branch | 比值 |
|---|---|---:|---:|---:|
| L07 | church k10 | 0.133 ms | 0.132 ms | 0.992× |
| L07 | strchain k10 | 2.262 ms | 2.198 ms | 0.972× |
| L07 | global k10 | 3.619 ms | 3.464 ms | 0.957× |
| L07 | natadd k10 | 0.421 ms | 0.398 ms | 0.945× |
| L08 | church k10 | 0.131 ms | 0.132 ms | 1.008× |
| L08 | strchain k11 | 2.721 ms | 2.956 ms | 1.086×（med 0.969，噪声） |
| L08 | global k10 | 2.818 ms | 2.757 ms | 0.978× |
| L08 | natadd k10 | 0.392 ms | 0.403 ms | 1.028× |
| L08 | struct k10 | 2.019 ms | 2.009 ms | 0.995× |

## 3. 结论

- **L08 是最大赢家**：strchain **15.9×**、struct **6.9×**、global **5.9×**、
  natadd **2.56×**、church 2.19×、match 1.64×。
- **L11**：macro 13.6×、struct 11.4×、strchain 14.2×；其他负载小幅。
- **L07**：Val Rc 后 church 1.85×、natadd 1.51×、match 1.22×、strchain 1.12×（浅语料；深作用域收益另见 deep 报告）。
- **L09**：Val Rc 后 natadd **2.02×**、match 1.31×、church 1.28×、enum 1.08×；strchain/universe 小增益。
  （L09 Tm Rc 尝试为负结果：natadd/church 变快但 strchain +24%，已整笔回退，见 L09-TM-RC 报告。）
- **L10**：本轮没有实质改动，全部在 ±2% 内（符合预期）。
- **L12**：修复 hover/completion 观察表钉住 decl Rc 后，strchain **14.0×**、macro **13.2×**、natadd 1.13×、church 1.03×；此前“k10 没有收益”是漏搬观察表闸造成的 O(D²) 回归假象。
- **L13**：prelude-core 1.28×、match 1.41×、enum 1.45×、church 1.13×、
  prelude-hdl 1.09×（prelude-hdl 绝对值 ~5s，主要受真实 prelude 负载支配）。
- **twin fast_ss**：全部在 ±3% 噪声内（L08 strchain 的 min 1.086× 与 median 0.969×
  方向相反，判为抖动），没有回归。
- 本轮没有 >5% 的稳定回归项。

## 4. 备注

- 小于 1ms 的项（match/church/enum/twin fast）受计时抖动影响较大，表中保留 min 以对齐
  前面各轮的 A/B 口径；median 结论同向。
- L10 的 `enum`、L10 traitchain 在 master/分支上存在已知 bench 失败或超慢，不纳入矩阵。
- L09 的本轮数字包含 value-layer Rc 化（33a08764）；L12 包含 hover/completion 观察表门控（aa60c424）。
- 性能矩阵只测 bench；功能门禁此前已全绿（全量 lib 994 passed，L07/L08 parity/blackbox、
  L09/L10 parity、L11/L12 parity 均通过）。
