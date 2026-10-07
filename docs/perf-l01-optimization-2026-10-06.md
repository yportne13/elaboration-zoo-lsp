# L01 性能优化空间评估（2026-10-06）

**问题**：L01（`src/L01_nbe`，NBE 22 变体研究层）的性能还有没有优化空间？

**本报告**：Lead 汇总，四份子报告 + 312 个 raw 证据文件支撑：

| 子报告 | 内容 |
|---|---|
| [00-baseline.md](perf-l01/00-baseline.md) | 本机（aarch64/Android/Termux）基线矩阵 + 噪声界 + 与 readme 的对照 |
| [01-hotpath.md](perf-l01/01-hotpath.md) | 热点路径逐段走查 + 15 条候选 C1–C15 + 封顶轴 |
| [02-experiments.md](perf-l01/02-experiments.md) | 定向 A/B 实验（影子副本）+ 机制级动态计数 + 跨树对照 |
| [03-verification.md](perf-l01/03-verification.md) | 独立对抗性复核（复跑 + 抽查 + 过度声称审计） |

所有计时都在本机进行（`taskset -c 7` = Cortex-X2，keep-alive 保频，独占锁，
指标 `med_of_min`）。**readme 中的数字来自 Windows x64，不是本机事实**，本报告
引用时一律标注。

---

## 0. 结论

### 0.1 三层回答

**第一层 · 对产品：优化空间 ≈ 0（结构决定，不是性能结论）。**
L01 没有生产足迹：`src/lib.rs` 不声明 `L01_nbe`（只声明 L02–L13），仓库里唯一
引用它的是独立基准二进制（`src/bin/l01bench.rs:25` 用 `#[path]` 直编），
`typort`/LSP 不链接它。所以**改 L01 不会让任何交付物变快**。

更关键的是：L01 配方里被本轮证实有效的两条机制（`W::ApplyKnown`、
`ChainWrap(0)` 消除；有效范围见 0.1 第二层），**L02–L13 全链 12 层以及
`bench_head`/`bench_pre` 早已实现**；全仓 grep 只有 L01 没有。换句话说，L01
作为"配方源头"落后于自己的后代一代，但这个落后在生产侧没有任何代价。

**第二层 · 作为研究/基准产物：有确定的空间，但已封顶到常数级。**

- **可确证收益（跨批 + 跨实现独立复现）**：
  - 一次性口径的 `Spine` 预保留 4096→16384：`church_pair` n=4000 **−7.4%**、
    n=8000 **−10.3%**（批 1，同批空对照 p95 ≤3.1%，同批 `_ss` 对照 0.00% 证明
    只影响一次性口径）；独立复核（task-5，自写驱动、A/B/A_copy 三臂轮转）
    复现为 **−7.50% / −10.37%**（该批空对照 p95 1.25%/0.61%）。零语义风险，
    一行改动。
  - 岔路密集的合成形状 `clo_chain` 上的 `ApplyKnown`：**−29…−38%**
    （机制收益上限，需新增负载类型才测得到）。
  - ~~`parigot_add n=10` −6.6%~~ → **未复现（按预注册指标不可判定），但很可能是真实的
    ~7%**：复核两批测得 −0.58%（空对照 p95 17.90%）与 −6.50%（p95 16.06%），
    `med_of_min` 规则下均判未判定。原解释"重负载 ⇒ 空对照自然小"被推翻——同一
    case 四个批次的地板是 0.23% / 22.17% / 17.90% / 16.06%，**3/4 批次 ≥16%**。
    但对照之下有一条更干净的信号：**配对比（`paired_ratio_med`）在四个批次上
    一致为 0.927–0.934，而同字节对照臂为 1.000**——配对统计消掉了批内频率漂移，
    说明效应很可能真实存在。**本报告的处理：记为"疑似 ~7%，本机 `med_of_min`
    无法稳定判定"，不作为已确证收益，也不作为否定。**
- **机制级上界（估计，非"测不出来"）**：默认负载 `church_pair` 每次 normalize
  只有 `fork_h0 = 2` 次 β 岔路、eval 主循环 37 步，**两者都与 n 无关**（硬事实，
  逐事件核过；工作量在 `ChainWrap` 的 2n 次 spine push 与 quote 上）。按合成
  形状标定的 ~3.5 ns/被删迭代，收益上界落在 **10⁻²% 量级**（该标定是估计，
  故不称"证明"）。`dup`/`church_mul` 同理（<0.4%）。
  `exponential` 是另一种性质：**`fork_h0 = 0`，机制一次都不执行**。
- **零效果**：`ChainRun` 判据外提（4 个规模全 0.00%）。
- **已封顶、不必重试**：`bump_spine_slim`/`native_clo`/`compiled`/
  `bump_spine_memo_inline`/`bytes_flat_value`（readme 实测否决）；
  本轮静态审计另判死 3 条：恒假回灌守卫（不在热内层，预期≈0）、
  打包字位宽（2-bit 已无余量）、`#[inline]` 提示（LTO+CGU=1 自行决定，预期≈0–2%）。

**第三层 · 真正没被收割的是两处"结构/口径"空间，且都不在现有基准的可见范围内。**

1. **非右链形状上的迭代固定税**：本机实测递归版 `bump_spine` 在
   `parigot_add n=10` 上比迭代版快 **1.42×**、`exponential n=20` 快 1.14×
   （readme Windows 记 1.9×/2.0×；本机差距更小但方向一致）。要收割需要
   递归/迭代混合 fast path（高难度、两套语义必须逐字等价）。**但该形状同时是
   memo 的主场**（`parigot_add n=10`：memo 0.305 ms vs 非 memo 最快 103.0 ms
   = **337×**；`exponential n=20`：0.006 ms vs 12.57 ms），所以这条的实际价值窄。
2. **计时口径把输出侧成本全部排除**：`l01bench` 只计 `normalize`；入参
   import/编码、结果 `export`、正确性断言都在窗口外，大 n 段甚至用
   `mem::forget` 泄漏结果树以规避百万层 `Box` 的递归析构。而
   `bump_arena::export`（`src/L01_nbe/bump_arena.rs:163-169`）是**逐节点
   `Box::new` 的递归转换**——真实 LSP 消费必须付这笔钱。**现有全部结论
   （含 readme 的消融阶梯）都看不到它**；这是唯一"可能比 eval/quote 更大"的
   未测量轴。

### 0.2 最大瓶颈是测量能力，不是想法

本机 `walt` governor 有离散档位，短基准下**单次 rep 的 min 是撞运气的统计量**：

| 口径 | 跨批离散度 |
|---|---|
| min-of-7（无保频） | 20.0% / 最大 22.1% |
| min-of-7（保频） | 17.7% / 最大 24.7% |
| **保频 + 每 rep min 取中位数** | **0.9% / 最大 2.9%** ✅ |

Null A/B（同一二进制奇偶半分组，比中位数）：7 reps/侧 p95 假阳 **14.6%**、
max 18.2%；21 reps/侧 p95 中位 2.6%（n=8000 轻量变体最坏 14.8%）。

**而本轮候选优化的预期量级多在 3–15%**。结论：本机**结构上无法判定**大部分
微优化——不是"没测出收益"，是"测力不足以判定"。要在 L01 上继续做可信的性能
决策，先解决测量环境（更安静的宿主机 / 允许 `perf_event_open` 的内核；
Lead 实测本机 PMU 被拒 EACCES，无确定性硬件计数器可用）。

---

## 1. 评估对象与边界

- L01 = `src/L01_nbe`：纯 lambda 演算（de Bruijn）NBE（eval + quote），
  22 个表示/策略变体 + 2 条稳态测量行。公共设施 `term.rs`/`persistent_list.rs`/
  `bench.rs`。基准二进制 `l01bench`（release = LTO + `codegen-units=1` +
  mimalloc 全局分配器）。
- **生产推荐路径**（readme「怎么选」）：`bump_spine_iter`（一次性口径）+
  `bump_spine_iter_ss`（`Machine` 稳态口径，长驻进程的真实成本口径）；
  对照 `bump_spine`（递归，非右链形状反超）。
- **变体形态冻结**：本轮**没有改动主仓库任何源码**（`src/**`、`Cargo.toml`
  零改动，已多次核实）。所有改源码的实验都在工作区外的影子副本
  `/tmp/l01-exp` 进行。理由：readme 的消融表与实测数字锚定在既有变体形态上，
  原地改动作废其基准叙事（`docs/review-continuity/a1-r1.md:80` 同结论）。
  若要让改动落地，正确形态是**新增变体文件**（如 `bump_spine_iter_ak.rs`）
  而不是原地改推荐路径。

## 2. 本机基线要点（完整表见 [00-baseline.md](perf-l01/00-baseline.md)）

`med_ms`（keep-alive + 每 rep min 的中位数），`taskset -c 7`：

| 变体 | n=4000 | 相对 | n=8000 | 相对 |
|---|---|---|---|---|
| `bump_spine_iter_ss` | **0.069** | 1.00× | **0.140** | 1.00× |
| `bump_spine_iter` | 0.078 | 1.13× | 0.159 | 1.14× |
| `bump_spine_memo` | 0.079 | 1.14× | 0.161 | 1.15× |
| `bump_spine_slim` | 0.104 | 1.51× | 0.203 | 1.45× |
| `bump_spine` | 0.113 | 1.64× | 0.232 | 1.66× |
| `bump_tree` | 0.194 | 2.81× | 0.391 | 2.79× |
| `cek_bump` / `bump_iter` | 0.237 | 3.43× | 0.48 | 3.4× |

- 复制强制：`dup_pair` 4000 memo 比 iter 快 1.9×、`dup_deep` 3.7×（readme 1.8×/3.6×，成立）。
- 共享形状：`parigot_add n=10` memo 0.305 ms vs 非 memo 最快 103.0 ms（337×）；
  `exponential n=20` memo 0.006 ms vs 12.57 ms。
- 深 n（64000）：`_ss` 0.966 / `iter` 1.402 / `slim` 1.628 / `cek_bump` 4.610 /
  `bump_iter` 5.425 / `cek` 30.76。
- **与 readme（Windows x64）的冲突（本机复现结果）**：
  ① readme「`slim` 在 64k 反超 `iter`」**本机不成立**（1.628 vs 1.402 仍慢）；
  ② **`bump_tree` 本机反超 `cek_bump`/`bump_iter`**（0.194/0.391 vs 0.237/0.482），
  readme 里 `tree` 更慢——排序反转；
  ③ memo 的线性税本机 ~1%（readme +8%，本机读不出）；
  ④ `bump_spine` 相对迭代版只慢 1.64×（readme 2.5–3.5×）。
  → **readme 的绝对倍率与部分交叉点不可迁移到 aarch64/mimalloc 组合**；
  第一梯队排序与 memo 的量级收益可迁移。

## 3. 优化空间逐轴判定

判定规则：同批交错、指标 `med_of_min`、每侧 ≥21 reps、以**同批空对照 p95**
为地板；`|ratio−1| ≤ p95` 判"未判定"。

| # | 轴 | 落点 | 实测 | 判定 |
|---|---|---|---|---|
| 1 | `ApplyKnown`+`ChainWrap(0)`（L02 已实现，L01 独缺） | `bump_spine_iter.rs:41/83/94/109/123`（影子树） | 合成 `clo_chain` −29.4/−34.6/−37.8%；`parigot_add 10` 批 1 −6.6%，复核两批 −0.58%/−6.50%（空对照 p95 16–18%）→ 未判定，但配对比四批一致 0.927–0.934（疑似真实）；`church_pair`/`dup`/`church_mul` 全 UNDECIDED 且机制上界 <0.4%；`exponential` 机制不执行 | **机制有效（合成岔路密集形状 −29…−38% 可测）；现成负载无已确证收益，`parigot` 疑似 ~7% 未判定** |
| 2 | 一次性 `Spine` 预保留 4096→16384 | `bump_spine_iter.rs:354` | 4000 −7.4%、8000 −10.3%（批 1）；复核 −7.50%/−10.37%（p95 1.25%/0.61%） | **WIN ~7–10%（已跨批 + 跨实现独立复现，高置信度）** |
| 3 | 一次性 `vals` 预保留 + 复用 | `bump_spine_iter.rs:357-365` | 4000 −5.0%（压线）、8000 −1.8% | **未判定（边缘）** |
| 4 | `ChainRun` 判据外提 | `bump_spine_iter.rs:256` | 4 规模全 0.00% | **零效果**（LLVM 本就 unswitch） |
| 5 | 恒假回灌守卫（`:214`/`:274`） | 同上 | — | **预期≈0，不建议实验**（不在热内层） |
| 6 | 打包字/tag 位宽 | `bump_spine.rs:34-68` | — | **预期≈0**（2-bit 已无余量） |
| 7 | `#[inline]`/dispatch 形态 | `:51`/`:159` | — | **预期≈0–2%**，负收益风险（icache） |
| 8 | SoA spine（第三条轴） | `Spine`/`Entry` | 未测 | 预期 n≤8000 或负、n≥64k 0–20%；需重写 push/索引语义 |
| 9 | 混合递归 fast path（非右链形状） | eval/quote | 递归版已实测反超 1.14–1.42× | **空间真实但窄**（同形状 memo 337–2095× 更优） |
| 10 | 编译期选项（环境轴，非算法） | `Cargo.toml`/`RUSTFLAGS` | 未测 | `target-cpu` 0–5%、`panic=abort` 0–2%、PGO 5–15% |
| 11 | **输出侧 `export`/析构**（不在计时窗内） | `bump_arena.rs:163-169` | 未测 | **唯一可能大于 eval/quote 的未测量轴**；需新增计时口 |

## 4. 结论与建议

**如果目标是产品性能**：不要在 L01 上投入。L01 不进产品，其配方已被 L02–L13
超越；要看性能请直接看 L13（`src/L13_namespace/bump_spine_iter/eval.rs`，已含
`ApplyKnown`/`ChainWrap(0)`）。

**如果目标是 L01 作为研究产物的可信度**，按性价比排序：

1. **`Spine` 预保留**（一行、零语义风险、~7–10% @一次性口径）：建议作为
   **新变体**落地，并补一条 readme 注记；不要原地改 `bump_spine_iter`。
2. **`ApplyKnown`+`ChainWrap(0)` 回移**：只在"岔路密集"形状上有可测的机制收益
   （合成形状 −29…−38%）；**L01 现有负载上没有任何一条收益通过复核**。若要做，
   按新变体落地，并**在 bench 里加 `clo_chain(k)` 合成负载**——否则 L01 的默认
   负载（`church_pair`）永远测不出这条机制，这正是它 12 轮未被衡量的原因。
3. **补输出侧计时口**（`export` + 析构）：这是现有基准的结构性盲区，也是唯一
   可能改变"哪条配方更快"结论的未测轴。
4. **不要做**：恒假守卫、tag 位宽、`#[inline]`、`ChainRun` 外提、
   已被 readme 否决的五条轴。
5. **先修测量环境**：本机（walt + 无 PMU）不足以判定 3–15% 的优化。要么换
   宿主机，要么在 L01 的 bench 里内建"同批空对照 + 中位数 + keep-alive"三件套
   （`tools/perf-l01/` 已实现，可复用）。

## 5. 复核状态与局限

- **独立复核**：[03-verification.md](perf-l01/03-verification.md)。复核员自写驱动
  （不复用实验方的脚本）、A/B/A_copy 三臂轮转、锁内计时：
  - `Spine` 预保留（§3 第 2 行）：**成立**。复核批 4000 −7.50% / 8000 −10.37%，
    同批空对照 p95 1.25%/0.61%，同字节对照臂 0.00%，paired 0.9250/0.8963 与原文
    0.9259/0.8970 重合；增量与 memcpy 字节比 288/96=3.0 自洽。
  - `ApplyKnown` 的 `parigot_add n=10` 收益：**未复现**（−0.58% / p95 17.90%；
    第二批 −6.50% / p95 16.06%，均未判定）。实验方已据此把 `02-experiments.md`
    判定统一改为"未复现"，撤回"重负载例外"解释（见该文档 §9 勘误）。
    唯一保留的正向线索是配对比四批一致 0.927–0.934，已按"疑似、不作数"处理。
  - `church_pair` 的机制级上界：计数方法、钩子位置、`removed_steps` 逐事件算术
    全部核实通过（复核员用 raw DIAG 重算 26 行、0 差异；结构恒等式 26 行全成立），
    但 ns→百分比的外推余量只有 ~2.6–4×，故"**可证明**"降级为"**机制级上界估计**"。
  - 数字抽查：`00-baseline.md` 抽 7 项**全部复现**；`02-experiments.md` 抽 9 项，
    1 处不符（§4.1 的 exp2a `_ss` 8000 实为 +0.72%，已由实验方勘误）。
  - 正确性：独立副本 6 个源码状态（baseline/exp1/exp2a/exp2b/exp3a/diag）全部
    `cargo test --release --bin l01bench` **79 passed / 0 failed**；主树
    `src/**`、`Cargo.toml` 零改动。
  - **Lead 终检**：在未改动的主树上重跑
    `cargo test --release --bin l01bench` → **79 passed / 0 failed，exit 0**
    （2026-10-06）；`git status -- src/ Cargo.toml` 为空；无残留锁/进程。
  - 遗留文档缺陷（不影响结论）：`02-experiments.md` §8 未记录
    `diag_hooks.patch` 必须先打 `synth_workload.patch`；部分 raw `summary.tsv`
    的自动 verdict 列与正文判定矛盾（**以正文为准**，正文是对的）。
- **机制计数不是性能数字**：`D2_diag` 变体挂了 `AtomicU64` 计数器，会改变热
  路径成本，只用于"机制发生次数"证据（`raw/exp-diag/percase.tsv`）。
- **规模上限**：深 n 只到 64000；readme 的 128k/256k/512k 交叉点未复测，
  不能外推。
- **未测变体**：readme 中被否决的 `rpn_owned`/`native_clo`/`compiled`/字节码族
  本轮未复测，本机没有本报告级别的基线。
- **绝对值的时效性**：全部数字属于同一 campaign（2026-10-06）；跨天/session 的
  绝对值不可直接比较（governor 档位状态不同），只有同批相对值可用。

## 6. 可复现性

```bash
# 基线（自动加锁 + keep-alive 保频）
tools/perf-l01/run_bench.sh --max-church 8000 --reps 7 --rounds 3 \
    --only bump_spine_iter,bump_spine_iter_ss,bump_spine --workload church
# 噪声界 / null A/B
python3 tools/perf-l01/noise_report.py          # 见 00-baseline.md §3
# 实验（影子副本，不在主树）
#   /tmp/l01-exp/{patches,ab.py,build_locked.sh,diag_analyze.py}
```

raw 证据：`docs/perf-l01/raw/`（312 个文件；含 `verify-*` 4 组复核原始数据）。
