# L13 ← L12 继承对账（2026-11-25）

> 口径见 [计划书](../l08-l13-inheritance-refactor-plan.md) §2（D1–D5）。
> 账本：`docs/inheritance/L12_canonical-to-L13_namespace.tsv`。
> 说明：本文件是 **B0 侦察结论 + triage 草案**，不是完成报告。

## 0 结论：L13 是"架构级分叉"，不是"漏继承"

把继承链重定基到新 L12 后重跑账本：**903 条目 / identical 164 / missing 410 / line_keep 0.514**
（重构前 0.526，**没有实质变化**——因为 L13 相对 L12 的差距不在观察面层，而在**内核载体层**）。

用 `tmp/l13_classify.py` 对 301 项非孪生 missing 做同名全层搜索：

| 分类 | 项数 | 含义 |
|---|---:|---|
| RELOCATED（同名在 L13 其它位置存在） | 49 | 合并/移位，非缺口 |
| **ABSENT（全层找不到同名）** | **252** | 真正的继承缺口 |
| 其中 `tests.rs` 用例 | 88 | 被拆成 20+ 个 `*_tests.rs`（需案例对账，见 §3） |
| 其中代码 | 164 | 见 §1 |

## 1 164 项代码缺口的真实性质：两代内核

| 维度 | L12（继承链） | L13（生产层） |
|---|---|---|
| 名字 span | `VSpan`（`Rc<Span<String>>`） | `Span<SmolStr>` |
| `Val::Sum` | 3 元组 `(VSpan, Rc<Vec<..>>, Rc<Vec<VSpan>>)` | **4 元组** `(Span, SumParams, SumCases, bool)` |
| `Val::SumCase` | 3 字段（无 `is_trait`/`index`） | **5 字段**（+ `is_trait`、`index`） |
| Nat | 无原生表示（一元 `sumcase` 链） | **`Val::Nat(u64)`** 原生机 | 
| 精化载体 | **`Subst`/`VSub`/`frcs`**（σ 显式替换，dpm-nbe） | **`update_cxt`/`refresh`**（改写 env 槽） |
| 合一 fuel | `Cell<u32>` 共享池 + 顶层 reset | `burn_fuel` 结构化预算 |
| 剖析 | `prof::bump` 原子计数 | `FUNC_PROF` 计时器对 |

⇒ `frcs`/`Subst`/`prim_reduce`/`quote_arm`/`rename_arm`/`frame_new`/`walk_con`/`infer_owned` 等
**"missing" 全部是这套载体差异的下游**：不是函数被删了，而是被换成了另一套实现（`update_cxt` 家族、
`burn_fuel`、`FUNC_PROF`）。**同名搜索找不到，因为名字本身就是不同时代起的。**

## 2 三个可行路线（需要决策）

| 路线 | 内容 | 代价 | 风险 |
|---|---|---|---|
| **A. 登记制**（口径放宽） | 把 L13 的载体分叉登记为 `ARCH-DIVERGED`（D5 的扩展），只补齐**不冲突的继承面**：`observe.rs` 8 项、`surface.rs` 5 项、`pretty` 保护 6 项、`parser/lex` 1 项（约 20 项 / 250 行） | 1–2 天 | 用户口径"完全继承"在 L13 上打折扣；需明确批准 |
| **B. 载体升级**（部分） | 把 L12 的 `Subst`/`VSub`/`frcs` 移植进 L13（与 `update_cxt` 并存或替换） | 1–2 周 | 动的是 L13 生产内核（LSP/HDL 全依赖），`l13_fast_parity`(630) + hdl 全量 + examples 都要重跑；历史上"L13 独立维护"就是为回避这个 |
| **C. 整体重定基** | L13 完全以新 L12 为基线重建，再叠加全部生产增量 | 3–4 周 | 等于重写 L13；docs 里 2026-11-17 已评估并选择"不做" |

## 3 无论走哪条路线都要先做的（可立即执行）

1. **`tests.rs` 案例对账**（88 项）：把 L12 `tests.rs` 的每个 `#[test]` 名，在 `L13/*_tests.rs` 里逐一查在不在；
   缺失的**补测试**而不是补代码——这是纯增量、零风险；
2. **`observe.rs` / `surface.rs` / `pretty` 保护 / `parser/lex`**（约 20 项 / 250 行）：
   L13 的 `observe.rs` 已存在且部分实现（`peel_pi_collect`/`push_ctor_hover` 都在），只差
   `tm_has_unsolved_meta`/`drain_check_issues`/`local_binder_span`/`render_val` 等 8 项；
3. **`struct_eq.rs` 9 项**：侧分支 `feat/l13-sigma-carrier`（`475ea8ce`）已做架构级移植（+421 行），
   评估并入（该分支基于旧 L13，需要 rebase）。

## 4 建议

**先做 §3 的三项（零风险、可验证），再就 A/B 找用户决策。** 理由：
- §3 已能覆盖 252 项里的约 110 项（88 测试 + 20 observe/surface/pretty/lex）；
- 剩下的 164 项代码缺口**全部**落在载体层，改不改是**产品决策**，不是重构手速问题；
- 用户原话"严格确保完全继承"在 L13 上会遇到这条分叉线，必须显式确认口径。
