# L07 其余优化项逐项实测（L13 参考版清单 → L07，2026-11-09）

> 承接 [L07-upgrade-bench-2026-11-09.md](L07-upgrade-bench-2026-11-09.md)。
> 本轮基线 = `master` @ `c2fffd3f`（COW 已落地）。后续已把实测有效的 FxHash 落地为
> `72f12101`。所有实验跑在 scratch worktree `C:\ezl-l07opt`（基线 COW 版本，`CARGO_TARGET_DIR=
> C:\ezl-target-l07opt`），release、同机、每档 5 轮 min；FxHash/eval 另做 2×（3 轮 min）交错
> A/B（正序 + 反序）以消除顺序偏差。原始日志见 `experiments/l07-opt-items/`。

## 0. 结果速览

| 项 | L07 现状 | 本轮动作 | 结果 | 决定 |
|---|---|---|---|---|
| decl 表就地 COW | 本轮已改 | 落地 + 门禁 | strchain k13 **32.9×**、global k13 **24.7×** | **已落地** `c2fffd3f` |
| **FxHashMap**（decl/src_names/mutable/simpl_cache） | std HashMap（SipHash） | 实现 + 交错 A/B | **global −5.8..−8.3%、strchain −1.6..−7.7%、match −5.5..−8.6%、enum −4.3..−5.4%、church ~0** | **已落地** `72f12101` |
| 求值快路径（eval_aux SumCase/ctor-name） | L07 force 已是叶子 | 实现 + 交错 A/B | 无一致收益（±5% 噪声） | 不落地 |
| simpl_decl 缓存 | **已存在**（按 `Decls::ver`） | 关闭缓存对照 | 无一致方向（±5–14%，被运行漂移淹没） | 保留，非新杠杆 |
| force 的 Sum 叶子 | **已存在**（`t => t`） | 恢复"force Sum 参数"对照 | 无可测变化（这些负载的 Sum 参数本来就是 WHNF） | 保留，无需改 |
| eval_aux 的"只 force 非构造子头" | L07 force(SumCase) 是叶子，本来省 | 同 eval 快路径 | 0 | N/A |
| 其它 L13 清单项 | L07 无对应结构 | 逐项核对（§2） | 全部 N/A，理由逐条给出 | 不抄 |

## 1. 本轮真正落地的两项

### 1.1 decl 表就地 COW（`c2fffd3f`，上一份报告的主测量）

`Cxt::decl_insert_mut(&mut self)` + `Infer::infer_owned(Cxt, Decl)`；旧 `infer(&Cxt)` 保留为
浅克隆包装。效果（同批测量）：strchain k13 **1977.0→60.0ms（32.9×）**、global k13
**1955.1→79.3ms（24.7×）**；church/match/enum/natadd 0–7%（这些负载 def 数少）。
门禁：L07 lib 70 passed；blackbox v1/v2/v3 + l07_fast_parity 全绿；l07bench 节点数断言通过。

### 1.2 FxHashMap（`72f12101`）

把参考版 `Decls.map`、`src_names`、`mutable_map`、`simpl_cache` 从 std `HashMap`（SipHash）
换成 `rustc_hash::FxHashMap`（孪生早就是 FxHashMap）。**交错 A/B（正序 2 次 + 反序 2 次，
每次 3 轮 min，取各方向最小，表内为反序结果；正序同向）**：

| 负载 | k=11 base→fx | Δ | k=13 base→fx | Δ |
|---|---:|---:|---:|---:|
| global | 17.845 → 16.670 | **−6.6%** | 78.196 → 72.583 | **−7.2%** |
| strchain | 9.250 → 8.699 | **−6.0%** | 58.197 → 57.258 | −1.6% |
| match | 0.146 → 0.138 | **−5.5%** | 0.169 → 0.155 | **−8.3%** |
| enum (k=9) | — | — | 0.278 → 0.263 | **−5.4%** |
| natadd | 5.193 → 5.078 | −2.2% | 28.928 → 30.143 | +4.2%（噪声） |
| church | 2.645 → 2.528 | −4.4% | 12.117 → 12.634 | +4.3%（噪声） |

正序 A/B 同向：global −7.9..−10.0%、strchain −6.0..−8.2%、match −4.5..−8.5%。
结论：**map 密集负载稳定 5–8%**，church（少 lookup）约 0。

## 2. 其余 L13 参考版优化项：逐项结论（为什么 L07 不适用）

| L13 清单项 | L07 对应物 | 判决 | 理由（代码/负载） |
|---|---|---|---|
| `scan_def_replay` memo | 无 | N/A | L07 没有 effect/replay 扫描（那是 L13 namespace/effect 设施） |
| `FORCE_MEMO` | `force(&self, decl, t: Val)` 按值 | 不抄 | L07 `Val` owned、无稳定 Rc 指针键；σ/VSub/fuel 使"同输入同输出"不成立；无 prelude 级共享图（L13 的 3.7× 全来自 prelude） |
| force 形状门控 | force 已是 6 臂小 match | 不适用 | 没有 L13 的 memo wrapper/哈希前置成本 |
| `Val::Sum` 叶子 | 已是默认 `t => t` | 保留 | 实测强制 force Sum 参数无可测变化（这些负载参数已 WHNF） |
| `simpl_decl` 缓存 | **已有** `simpl_decl_cached`（按 `ver`） | 保留 | 关闭缓存对照无一致退化（±5–14% 运行漂移）→ 在这些负载不是热点 |
| `unify` Call/Call 无-Flex 预检 | L07 无 `Val::Call` | N/A | Call 值只在 L12/L13 出现 |
| `trait_wrap` 惰性快照 / `head_index` | L07 无 trait/class | N/A | L10 才有 trait 世界 |
| `no_metas` visited-set | L07 无 `no_metas` | N/A | 该消费者是 L13 的 def-body 未解 meta 检查/hover |
| class Phase A 复用 | L07 无 class/`Raw::Tm` | N/A | L13 HDL class 专有 |
| `PRELUDE_CACHE` / `PreludeSlot/PreludePool` | 无 prelude | N/A | L07 源自包含；`Cxt::new` 只注册 builtin；测试不加载 prelude |
| `typ_pretty` / ctor_hover / owned observe | 无 LSP | N/A | 仅 L13 观察面有消费者 |
| decl 7 元组 / `Span<()>` | `DeclEntry { ty, val }` | N/A | 没有 span/pretty 槽可缩；改了只会增加语法层成本 |
| FxHash（decl 表） | std HashMap | **已落地** | 见 §1.2 |
| `SmolStr` 键 | 已是 SmolStr | 已满足 | — |
| Sum 臂 eval 记忆化 | 无 | 不抄 | L13 实测净损失（+5~+33%），已撤销 |
| `filter_accessible_constrs` 快照 | 无 | N/A | 该实现随 L13 逐臂重写已删 |
| quote/rename 迭代化 | **L07 本身就是源头**（P11） | 已满足 | 不是 L13 参考版的成果 |
| mimalloc / `[profile.test] opt-level=2` | 所有 bench bin 已挂载/全局 profile | 已满足 | 非 L07 单章项 |
| preprocess 单遍 | 共享前端，已是直接扫描 | 不计 | 不属于 L13 引擎优化，也无独立收益证据 |

## 3. 其余实测项的原始对比（供否决/保留依据）

**求值快路径（eval_aux）**：交错 A/B 中 chrch/match/strchain/global 的 eval/base 比在
−5%..+4% 之间来回（church k12/k13 的基线本身有 30–50% 运行漂移，反向证明不可作数）；
无一致方向 → 不落地。

**simpl_decl 缓存关闭**（单轮 5 次 min，基线 vs 关闭）：

| 负载 k=13 | 基线 | 关闭缓存 | Δ |
|---|---:|---:|---:|
| strchain | 61.570 | 60.236 | −2.2% |
| global | 77.596 | 78.120 | +0.7% |
| match | 0.165 | 0.169 | +2.4% |
| enum (k9) | 0.277 | 0.287 | +3.6% |
| natadd | 32.792 | 28.274 | −13.8%* |

\* 无一致方向，k12 同样 −10%，与 baseline 运行漂移同量级；不能据此说缓存有害。

**force Sum 恢复递归**（单轮 5 次 min）：strchain 61.570→59.060（−4.1%）、global
77.596→76.252（−1.7%）、match 0.165→0.170（+3%）、natadd 32.792→28.643（−12.6% 漂移；
无一致方向）→ 现有叶子臂在这些负载上没有可测收益，也没有可测成本。

## 4. 复现

```powershell
# 基线 = COW 版 master c2fffd3f；variants 在 scratch worktree
git worktree add --detach C:\ezl-l07opt c2fffd3f
# FxHash: cxt.rs 的 Decls/src_names + mod.rs 的 mutable_map/simpl_cache 换 FxHashMap
# simpl 缓存关闭: simpl_decl_cached 直接 Rc::new(simpl_decl(decl))
# force Sum 深: force 的 Val::Sum 臂强制参数值/类型
# eval 快路径: pattern_match.rs eval_aux / eval_aux_arm 的 L13 样式
CARGO_TARGET_DIR=C:\ezl-target-l07opt cargo build --release --bin l07bench
# 交错 A/B（本例）
C:\ezl-l07opt\l07bench-base.exe --workload all --max-k 13 --rounds 3 --only basic
C:\ezl-l07opt\l07bench-fx.exe   --workload all --max-k 13 --rounds 3 --only basic
```

原始日志：`docs/optimal-design/experiments/l07-opt-items/`（opt-baseline / opt-fxhash /
opt-no-simpl-cache / opt-force-sum-deep / opt-eval 及 interleaved 正反序）。

## 5. 一句话

**除 COW 外，L07 唯一值得落地的是 FxHashMap（map 密集负载 5–8%，零语义风险，已提交
`72f12101`）；eval 快路径、simpl 缓存、force Sum 叶子在 L07 上要么没有对应机制，要么无可测
收益。其余 L13 参考版优化项均绑定 L13 的 prelude/LSP/namespace/trait/effect 设施，L07 不应抄。**
