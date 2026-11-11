# L07–L13 参考版跨层对比（严格同一用例，2026-11-11）

> 问题：**先不看孪生版**，只比参考版，在「完全相同的用例」上 L07–L13 之间差距多大？
>
> 口径：`basic`（参考版），每配置 min-of-rounds；环境与主报告相同（Windows/release、HEAD `d0bd1bff`）。
> 原始数据：`target/bench_real/crosslayer_common_L*.txt`、`target/bench_real/crosslayer_synth.txt`。

## 0. 结论

1. **严格同一文件（6 个，含 798-decl 阶梯）**：参考版总耗时 L10 42.7 ms < L12 49.5 < L11 54.7 < L13 64.2 ≈ L07 68.8 ≈ L08 70.4 < **L09 115.2 ms（1.68× L07）**。差距几乎全来自 800-decl 顶层 def 阶梯；50/200 decls 档各层在 1.0–1.7× 内。
2. **同族合成负载**：最大层间差距在「顶层 def 链」——`strchain k=11`（4096 defs）L07/L08 8.9/9.6 ms，L09–L12 **52–66 ms（慢 5.5–7.4×）**，L13 18.4 ms（慢 2.1×）；其次是 `struct k=10`（L08 5.6 vs L09/L10 45–53 ms）与 `universe k=10`（L09/L10 2.4–2.5 vs L11/L12 22–24 ms，后者含 parse+pretty 口径）。
3. **跨层差距不是单调递增**：L09 是参考版最慢的层（宇宙机制 + 顶层 def 登记成本），L10 最快，L13 与 L07 基本持平；L11/L12 介于中间。
4. 主要归因（[推断]，需按层单独 profile 核实）：L07/L08 前几轮已做结构/COW、值层 Rc 等优化；L09–L12 参考版在顶层 def 链/实例合成上仍有 O(D²) 行为；L13 有自己的 COW/观察面门控等优化，但作为产品层即使 `--with-prelude none` 也比 L07 重。

## 1. 严格同一文件（6 个文件，L07–L13 全部通过）

文件集见 `tools/bench_corpus/common/MANIFEST.md`：3 个最小词法/互递归用例 + 50/200/800 decls 三档同形态阶梯。

| 文件 | L07 | L08 | L09 | L10 | L11 | L12 | L13 |
|---|---:|---:|---:|---:|---:|---:|---:|
| ex_block_comments.typort | 0.021 | 0.019 | 0.018 | 0.016 | 0.031 | 0.028 | 0.021 |
| ex_even_odd.typort | 0.044 | 0.042 | 0.037 | 0.031 | 0.059 | 0.058 | 0.051 |
| ex_line_comments.typort | 0.016 | 0.015 | 0.012 | 0.010 | 0.023 | 0.023 | 0.022 |
| ladder_l07_small.typort（48 decls） | 0.412 | 0.406 | 0.523 | 0.279 | 0.563 | 0.510 | 0.497 |
| ladder_l07_medium.typort（198） | 4.240 | 4.255 | 7.063 | 2.794 | 4.069 | 3.636 | 4.272 |
| ladder_l07_large.typort（798） | 64.062 | 65.635 | **107.595** | 39.618 | 49.962 | 45.285 | 59.311 |
| **合计 (ms)** | **68.795** | **70.372** | **115.248** | **42.748** | **54.707** | **49.540** | **64.174** |
| **相对 L07** | 1.00× | 1.02× | **1.68×** | **0.62×** | 0.80× | 0.72× | 0.93× |

单位 ms，min-of-3。L11/L12 的 `basic` 是全流程 `run`（含 parse+pretty+stdout），其余层为 parse 外 `bench_check_nf`；本组文件 nf ≤ 1406 节点、源码 ≤ 37 KB，口径差估计 <5%。

## 2. 同族合成负载（各层最大 k 行，rounds=1，参考版 basic）

| 负载 (k) | L07 | L08 | L09 | L10 | L11 | L12 | L13 |
|---|---:|---:|---:|---:|---:|---:|---:|
| match k=11 | 0.097 | 0.090 | 0.112 | 0.089 | 0.174* | 0.291* | 0.156 |
| church k=11 | 1.609 | 1.476 | 2.403 | 1.416 | 1.447* | 1.451* | 2.145 |
| natadd k=11 | 3.754 | 3.016 | 4.339 | 1.937 | 1.727* | 1.546* | 2.564 |
| strchain k=11 | 8.857 | 9.640 | **65.604** | **60.543** | 52.365* | 52.777* | 18.426 |
| enum k=9 | 0.179 | 0.167 | 0.658 | — | — | — | 0.413 |
| struct k=10 | — | 5.634 | **52.719** | **44.923** | 20.431* | 20.767* | 19.703 |
| universe k=10 | — | — | 2.506 | 2.381 | **22.396*** | **23.902*** | 3.351 |
| macro k=10 | — | — | — | — | 18.011* | 21.921* | 17.704 |

- `*`：L11/L12 参考版没有 `bench_check_nf`，`basic` = 全流程 `run`（含 parse+pretty+stdout），与其它层 parse 外口径不同；小负载里口径差可能占相当比例（尤其 universe：pretty 大值可能占大头）。**数量级可信，逐格对比请以严格同文件表为主。**
- `—`：L10/L11/L12 的 `enum` 参考版在既有 bench 中不可测（已知失败），L07/L08/L09 无 struct/universe/macro 负载，L10 无 macro。
- 各层生成器是「同族同 k」而非逐字节相同（与 `docs/bench-matrix-2026-09-20.md` 的跨层口径一致）。

## 3. 读法与局限

- **看形态，不只看单点**：match/church/natadd 这类小负载各层差 ≤2.7×；一旦到「顶层 def 多」的形态（strchain 4096 defs、800-decl 阶梯），L09–L12 参考版比 L07/L08 慢 5–7×，L13 慢约 2×。这与主报告里「L09 参考版在 801-decl 文件上 O(D²)」的发现同向。
- **L09 的两面性**：小负载 match/enum/church 上比 L07 慢（0.112/0.658/2.4 vs 0.097/0.179/1.6），大 def 链上更慢（1.68× 总耗时）——宇宙机制与顶层 def 登记是主要嫌疑。
- **L10 最快**（0.62× L07 总耗时；natadd 1.94 vs 3.75）——与主报告 PERF-FINAL 里 L10「本轮无实质改动但基座便宜」一致。
- **L13 的定位**：同一文件上与 L07 基本持平（0.93×），在 strchain/struct 上明显好于 L09–L12（18.4 vs 52–66 ms；19.7 vs 20–53 ms），但作为产品层在 match/church 小负载上比 L07 慢（0.156 vs 0.097；2.145 vs 1.609）。
- 单窗口、小负载 ±5–10% 噪声；L11/L12 的绝对值和口径相关，**不要跨 harness 直接比**。

## 4. 复现

```powershell
# 严格同一文件（6 个）：
#   L07–L12：realbench --layer L0X --corpus tools\bench_corpus\common --rounds 3 --only basic
#   L13：    l13bench --file <file> --with-prelude none --rounds 3 --only basic
# 同族合成负载：
#   l07bench..l12bench --workload <match|church|natadd|strchain|enum|struct|universe|macro> \
#       --max-k <11|10|9> --rounds 1 --only basic
#   l13bench --workload <同上> --max-k <...> --rounds 1 --only basic
```

原始日志：`target/bench_real/crosslayer_common_L07..L13.txt`、`target/bench_real/crosslayer_synth.txt`。
