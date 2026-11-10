# L09 reference 值层 Rc 化（最小 Rc 核心）— 审计、A/B 与结论

- 工作树：`C:\ezl-wt-l09rc`，分支 `feat/l09-rc-values`，起点 `4357fb07`（master：all-layers hardening 合并）
- 构建/实验：`CARGO_TARGET_DIR=C:\ezl-target-l09rc`（F: 零构建）；**未 push、未改主工作树、未动 L07/L08/L10+ 与 twin**
- 提交：`33a08764` perf(l09): Rc-based value representation (cheap Val clones)
- 时间：2026-11-11 00:10–00:47（Asia/Shanghai），Windows / Ryzen 5 5600 / 34 GB

## 0. 结论（先给结论）

1. **最小 Rc 核心已落地且门禁全绿**：把 L09 reference 的 `Val` 递归子结构全部搬到 `Rc`（`Obj`/`Pi`/`Match`/`VSub` 子项 + `Sum`/`SumCase`/`Match` 的负载 Vec 全部 `Rc` 包裹），使 **`Val::clone()` 从"深拷子树 + 逐元素 String 分配"降为引用计数**。**不动 `Tm`、不动 `eval/force/v_app` 的签名与求值形状**（仍为 by-value `Val`），因此 diff 只有 5 个文件 +96/−93 行，语义等价。
2. **收益（同窗口交错，min of 3 trials，`--only basic`）**：`natadd k10` **2.480 → 1.876 ms（−24.4%）**；`match k13` **0.150 → 0.128 ms（−14.7%）**；`church k10` **1.286 → 1.195 ms（−7.0%）**；`strchain k10` 16.13 → 15.72 ms（−2.5%，噪声边缘）。L10 natadd k10 0.967 ms 不变（未动 L10）。
3. **与目标差距的变化**：L09/L10 的 natadd k10 差距由 **2.56× → 1.94×**（2.48/0.96 → 1.88/0.97）；剩余差距应在 `Tm` 的 `Box` 表示与 `Env/Spine = List<Val>` 的按值载荷（见 §7 剩余点）。
4. 门禁：`cargo check --all-targets` 0 error；L09 lib **10/10**、`l09_fast_parity` **39/39**；L10 lib **25/25**、`l10_fast_parity` **46/46**；L09 debug lib **10/10**；**全量 `cargo test --release --lib`：994 passed / 0 failed / 6 ignored**。
5. 这是"最小可编译 Rc 核心"而非完整 L10 表示迁移：`Tm` 仍是 `Box`（`Tm::Lam/App/Match` 等），`Env`/`Spine` 仍按值持有 `Val`，`MetaEntry::Solved` 仍存 `Val`。若要进一步收窄与 L10 的差距，下一阶段见 §7。

## 1. 审计：L09 vs L10 的表示映射（改前）

| 项 | L09（改前） | L10（参照） | 本轮处置 |
|---|---|---|---|
| `Tm` | `Box<Tm>` 子项（`Obj/Lam/App/AppPruning/Pi/Let/Sum typ/SumCase typ/Match scrutinee`） | `Rc<Tm>` 子项 | **未动**（剩余点） |
| `Val` 子项 | `Obj(Box<Val>)`、`Pi(Box<VTy>)`、`Match(Box<Val>)`、`VSub(Box<Val>)` | `Rc<Val>` | **已改 Rc** |
| `Val` 负载 | `Sum(…, Vec<…>, Vec<Span>)`、`SumCase{datas: Vec<…>}`、`Match(…, Vec<(PatternDetail, Tm)>)` 内联 Vec | `Vec`（元素 Rc）但 `Val` 以 `Rc` 传递 | **已改 `Rc<Vec<…>>`**（clone 变 O(1)） |
| `Env` | `List<Val>`（节点内联 Val） | `List<Rc<Val>>` | **未动**（剩余点） |
| `Spine` | `List<(Val, Icit)>` | `List<(Rc<Val>, Icit)>` | **未动**（剩余点） |
| `Closure` | `Closure(Env, Rc<Tm>)` | 同 | 无需改（`Tm` 已 Rc） |
| `eval` | `eval(env, tm: Tm) -> Val` + `eval_ref(&Tm) -> Val`（borrow 修复已在 master） | `eval(&Env, &Rc<Tm>) -> Rc<Val>` | 未动签名（Val 便宜后 by-value 可接受） |
| `force` / `frcs` | `force(Val) -> Val`、`frcs(&sub, Val)` | `force(&Rc<Val>) -> Rc<Val>` | 未动签名 |
| `v_app` / `v_app_sp` | `(Val, Val, Icit) -> Val` | `(&Rc<Val>, Rc<Val>, Icit) -> Rc<Val>` | 未动签名 |
| `closure_apply` | `(&Closure, Val) -> Val` | `(&Closure, Rc<Val>) -> Rc<Val>` | 未动签名 |
| `MetaEntry` | `Solved(Val, VTy)` / `Unsolved(VTy)`（`VTy = Val`） | `Solved(Rc<Val>, Rc<Tm>)` 形态 | **未动**（剩余点；`Val` 已便宜，clone 成本可接受） |
| `Infer.global` | `FxHashMap<Lvl, VTy>` | `FxHashMap<Lvl, Rc<Val>>` | **未动**（剩余点） |
| `EvalCtx/quote` | `quote(l, Val) -> Tm`；`quote_sp(l, Tm, Spine)` | `quote(l, &Rc<Val>) -> Rc<Tm>` | 未动 `Tm` 侧（剩余点） |

**为什么只改 `Val` 就够拿大头**：`Val::clone()` 出现在所有热读点——`eval_var` 的 `env.iter().nth(i).clone()`（每次变量求值）、`eval_aux` 的 `force(heads.clone())`（每次 match 选臂）、`frcs` 的槽位包裹/`rc_take`、`v_meta` 的 meta 解、`v_app` 的 spine 参数、`unify` 的值比较；改动前其中 `Obj/Pi/Match/VSub` 克隆深拷子树、`Sum/SumCase` 克隆整个 Vec（每个元素含一个 `Span<String>` = 一次 String 分配）。Rc 化后这些全部变成引用计数，而 `Val` 仍按值传递（不引入 L10 的 `&Rc<Val>` 签名大改）。

## 2. 改动清单（commit `33a08764`，+96/−93）

| 文件 | 改动 |
|---|---|
| `src/L09_mltt/mod.rs` | `Val` 枚举：`Obj(Rc<Val>)`、`Pi(Rc<VTy>)`、`Match(Rc<Val>, Env, Rc<Vec<(PatternDetail, Tm)>>)`、`VSub(Rc<Val>)`、`Sum(…, Rc<Vec<…>>, Rc<Vec<Span>>)`、`SumCase{datas: Rc<Vec<…>>}`。全部构造点 `Box::new`→`Rc::new`；`force/frcs/v_app/eval/eval_ref/quote` 中的 move-out 改为 `(*x).clone()`（Rc 克隆）或 `Rc::new(...)`；`Sum/SumCase` 的 `.into_iter()` 迭代改为 `.iter()` + 元素克隆；`eval_aux` 调用改 `&cases[..]`。 |
| `src/L09_mltt/unification.rs` | `rename` 的 `Obj/Pi/Sum/SumCase/Match` 臂按新类型适配（`rc_take` 传 `Rc` 克隆、`datas.iter()`、`cases.iter()` + `pat.clone()`）；`unify` 的 `(Pi,Pi)`/`(Match,Match)` 臂 `(**a).clone()` / `(**s1).clone()`。 |
| `src/L09_mltt/elaboration.rs` | `insert_go`/`insert_until_go`/`check` 的 `fresh_meta(..., (*a).clone())`、`Val::Pi(..., Rc::new(a), ...)`；`Raw::Obj` 的 `Sum/SumCase` 投影分支由 `.into_iter()` 改 `.iter()`；`infer` App 臂 `((*a).clone(), b_closure)`。 |
| `src/L09_mltt/pattern_match.rs` | `compile` 的 `Val::Sum(_,_,cases)` → `(*cases).clone()`；嵌套覆盖的 `cs.clone()` → `(**cs).clone()`。 |
| `src/L09_mltt/cxt.rs` | `Cxt::new` 的 `Val::Pi` 域 `Rc::new(Val::LiteralType)`；`subst_cxt` 的 `wrap` 改 `Val::VSub(Rc::new(...))`。 |

**语义等价论证**：只改变值的持有方式（Box/Vec → Rc），所有模式匹配/求值顺序/错误文案不变；`force`/`frcs` 的槽位纪律（只包裹不物化）不变；`Rc::try_unwrap` 兜底路径（`rc_take`）在共享时退化为 `Val::clone()`（现在 O(1)），语义与旧版一致。

## 3. A/B 数据（L09，同窗口交错 3 轮，min/median ms，`--only basic`）

| 负载 | k | rounds | 基线（改前 bin） | Rc 版 | 比值 | 判读 |
|---|---:|---:|---:|---:|---:|---|
| **natadd** | 10 | 5 | **2.480**（2.662/2.480/2.762） | **1.876**（1.876/1.946/2.010） | **0.756×（−24.4%）** | 明确收益 |
| match | 13 | 9 | **0.150**（0.151/0.150/0.151） | **0.128**（0.128/0.133/0.128） | 0.853×（−14.7%） | 明确收益 |
| church | 10 | 5 | **1.286**（1.288/1.314/1.286） | **1.195**（1.239/1.195/1.240） | 0.929×（−7.0%） | 收益 |
| strchain | 10 | 5 | **16.127**（16.127/16.256/16.339） | **15.719**（16.288/15.719/16.102） | 0.975×（−2.5%） | 噪声边缘 |
| L10 natadd（对照，未改） | 10 | 5 | 0.967 | 0.967（同 bin） | 1.00× | L10 未受影响 |

原始数据：`C:\ezl-target-l09rc\ab\{base-l09-*.txt,base-l10-natadd.txt,ab-rc.txt,phase2.txt}`。
说明：bench harness 只输出 min/median（无 max）；基线/新版二进制均在各自构建完成后静置测量，交错执行（base→rc→base→rc…）。

**与目标差距**：natadd k10 L09 vs L10 = 2.48/0.967 = 2.56× → 1.876/0.967 = **1.94×**；剩余差距与 `Tm`/`Env`/`Spine`/`MetaEntry` 的按值表示有关（§7）。

## 4. 门禁结果（HEAD `33a08764`）

| 门禁 | 结果 | 耗时（含构建） |
|---|---|---|
| `cargo check --all-targets` | **exit 0（0 error）** | 40.0 s |
| `cargo test --release --lib L09_mltt` | **10 passed / 0 failed** | 236.5 s（release LTO 首编） |
| `cargo test --release --test l09_fast_parity` | **39 passed / 0 failed** | 275.2 s（首编） |
| `cargo test --release --lib L10_typeclass` | **25 passed / 0 failed** | 1.0 s |
| `cargo test --release --test l10_fast_parity` | **46 passed / 0 failed** | 29.8 s |
| `cargo test --lib L09_mltt`（debug） | **10 passed / 0 failed** | 117 s |
| `cargo test --release --lib`（**全量**） | **994 passed / 0 failed / 6 ignored** | 73.8 s（release lib test 已编） |

说明：`l09_fast_parity` 通过 `#[path]` 把 L09 reference 再编进测试二进制（`39 = 29 本体 + 10 lib`），因此同时覆盖 reference↔twin 逐字节 parity 与 lib 单测；parity 全绿说明 twin 侧行为未受影响（本轮未改 twin）。

## 5. 未做项与剩余点（下一阶段候选）

| 剩余点 | 内容 | 预期/风险 |
|---|---|---|
| `Tm` Box → Rc | `Tm::Obj/Lam/App/AppPruning/Pi/Let/Sum/SumCase/Match` 子项全部 `Rc<Tm>`，`eval(&Rc<Tm>)->Rc<Val>`、`quote(l,&Rc<Val>)->Rc<Tm>`（L10 同形） | 收益可能最大（quote/rename/solve 的 Tm 深拷与 Box 分配），但波及 200+ 处、需重跑全部 parity；本轮预算内未做 |
| `Env`/`Spine` → `List<Rc<Val>>`、`List<(Rc<Val>, Icit)>` | 环境节点从内联 56B `Val` 变 8B 指针；`bind`/`prepend`/`iter` 全部适配 | 中等收益（分配体积/拷贝），~60–80 处；风险低但需再一轮编译迭代 |
| `MetaEntry::Solved(Val, VTy)` / `Infer.global: FxHashMap<Lvl, VTy>` | 改 `Rc<Val>` | 小收益（`Val` 已便宜） |
| `Sum`/`SumCase` 的 `Span<String>` 元素 | 改 `Span<Rc<str>>` 或整体共享 | 小收益，会改 pretty/错误文案路径，风险中等 |
| 编译期 `body.clone()`（`pattern_match.rs:243/326`） | 编译期每臂克隆 | 非运行期热路径，未做 |
| 内存/分配量化 | 未跑 `l06l13mem --chapter L09` A/B | 需 base/rc 两份 `l06l13mem` 二进制，本轮未做（时间） |

## 6. 未验证 / 风险

1. **平台**：Windows 10 / Ryzen 5 5600；未在 Linux CI 复测，未测峰值内存与分配次数。
2. **bench 口径**：min/median（无 max）；`strchain` 的 −2.5% 在噪声带内，不作为收益主张。`natadd`/`match`/`church` 收益在多轮交错中稳定复现。
3. **`Tm` 仍是 `Box`**：因此"完整 L09 Rc 化"未完成；本提交是任务允许的"最小可编译 Rc 核心"。若评审要求完整对齐 L10 表示，按 §5 继续。
4. **ABI/内存安全**：只把 `Box/Vec` 换成 `Rc`，无 unsafe、无别名风险；`Rc` 非线程安全与 L09 现状一致（L09 不在跨线程共享 `Infer`）。
5. **工作树干净**：源码改动已提交 `33a08764`（本报告另起一笔文档提交）；`git status --porcelain` 为空；未 push。

## 7. 复现

```powershell
$env:CARGO_TARGET_DIR='C:\ezl-target-l09rc'
# 构建与 A/B（基线二进制见 C:\ezl-target-l09rc\ab\l09bench-base.exe）
cargo build --release --bin l09bench
C:\ezl-target-l09rc\ab\l09bench-base.exe --workload natadd --max-k 10 --rounds 5 --only basic
C:\ezl-target-l09rc\release\l09bench.exe  --workload natadd --max-k 10 --rounds 5 --only basic
# 其余负载同理：church --max-k 10、match --max-k 13（rounds 9）、strchain --max-k 10
# 门禁
cargo check --all-targets
cargo test --release --lib L09_mltt ; cargo test --release --test l09_fast_parity
cargo test --release --lib L10_typeclass ; cargo test --release --test l10_fast_parity
cargo test --lib L09_mltt
cargo test --release --lib   # 全量
```
