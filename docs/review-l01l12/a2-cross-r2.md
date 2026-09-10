# A2 交叉审计 Round2 — A3 切片（`src/L07_sum_type/**`、`src/L09_mltt/**`、`tests/l07_*.rs`、`tests/l09_*.rs`）

> 只读审计：未改动 A3 任何文件。审计基于工作树**最终快照**（注意：审计期间观察到 A3 并发
> 补上了 L07/L09 `CloCell` 的 `#[repr(align(8))]`，后文以最终状态为准）。

## 1. 结论（verdict）

- P0: 0  P1: 0  P2: 0  P3: 2  needs-verify: 0
- A3 本轮两处行为修改（L09 `lvl2ix`=哨兵边界、`intersect_go`/`go_app_pruning`）与一处 A6
  语义修复（`prune_ty` 掩码反转）**均正确，且参考版 + 快版同步，未发现漏拷**。
- A1 对齐：`tag ∈ {1,4,7}`（Clo/Pi/XCell）在 L07/L09 全部有编译期断言；`XCell`/`CloCell`
  另有 `#[repr(align(8))]`，`PiCell` 含 `dom: V(u64)` 天然 ≥8。**完整**。
- 未决 P3：① L09 参考版 `pretty::go_ix` 越界仍 panic（历史行为，非本轮改动）；② 交叉建议
  （非缺陷）：L09 仅 `l09_fast_parity.rs` 一个黑盒 target，覆盖偏薄，但本轮新增探针已补关键路径。

## 2. 发现列表

### [P3] L09 参考版 `pretty::go_ix` 名字表不足仍 panic（历史行为，非 A3 引入）
- 位置：`src/L09_mltt/pretty.rs:48` `panic!("Variable index out of bounds")`
  （对照 L06 `src/L06_string/pretty.rs:45-47` 已退化为固定文案）。
- 证据：`go_ix` 在 `ns` 名字表短于 `ix` 时 `panic!`。本轮 A3 新实现的 `go_app_pruning`
  （`pretty.rs:56-115`）已刻意对短名字表退化 `@序号` 不 panic，但 `go_ix` 未同步。
- 机制/影响：与显示路径「绝不 panic」的既定方向（L06 注释、BRIEF §3.3）不一致；但属 L09
  原有形态，非本轮修改，且未见用户可达复现。
- 处置：**仅报告**（由 orchestrator 转 A3 决定是否对齐 L06）。

### [P3] L07/L09 黑盒覆盖偏薄（观察项）
- 位置：`tests/` 下 L09 仅 `l09_fast_parity.rs`（16 个 `#[test]`），无 `l09_blackbox*.rs`；
  L07 有 v1/v2/v3（49/53/46）。
- 证据：`ls tests/` 与 `grep -c '#\[test\]'`。A3 本轮已在该文件补 `parity_nonlinear_pruning_rev_mask`
  与 `parity_global_sentinel_self_ref` 两个探针（`tests/l09_fast_parity.rs:611-668`），覆盖了本轮
  两处行为修改。
- 处置：**仅报告**（覆盖建议，非缺陷）。

## 3. 逐项核验 A3 的行为修改（重点）

### 3.1 `lvl2ix` 边界 `>` → `>=`（正确，两版同步，无漏拷）
- 参考版：`src/L09_mltt/mod.rs:165` `if x.0 >= 1919810`（0 号全局 `global_idx+1919810` 恰为
  哨兵，用 `>` 会走 `l.0 - x.0 - 1` 下溢）。
- 参考版配套：`src/L09_mltt/unification.rs:252` `None => if x.0 < 1919810 { Err } else { Var }`
  ——`rename` 的 Rigid scope 判定把恰好等于哨兵者归为**全局**，与 `lvl2ix` 的 `>=` 同口径
  （旧 `<= 1919810` 会把 0 号全局误判为局部 → Err）。
- 快版同步 6 处：`bump_spine_iter.rs:1328,1479`（quote）、`2685,2730`（rename scope）、
  `4203`（change_n 的 lvl2ix）、`4316`（Raw::Var）。均 `>= GLOBAL_BASE`。
- 全仓 grep 核对：L09 内所有 `1919810/GLOBAL_BASE` 只剩 `>=`、`+1919810`、`-1919810`
  （eval/insert 方向），**无残留 `>`**；`pretty.rs:117` 本就用 `>=`。`eval`（`mod.rs:285`）
  `x.0 - 1919810` 与「global iff level ≥ BASE」一致。
- 结论：正确、完整、两版同判定。探针 `parity_global_sentinel_self_ref` 断言
  `def f : String = f` 打印 `recursive_0\n` 并跑 parity。

### 3.2 `intersect_go` `unreachable!()` → `None`（正确，与全层一致）
- 参考版：`src/L09_mltt/unification.rs:492` `_ => None`（长度失配 / 非 Rigid 头不再 panic）。
- 调用方 `intersect`（`:495+`）`None => unify_sp` 回落逐实参比较，与 L06
  `src/L06_string/unification.rs:429-430,440` 逐字同构；L07 `unification.rs:533`、L08
  `unification.rs:533` 亦为 `_ => None`（已逐一核实）。
- 快版：`intersect_bump`（`bump_spine_iter.rs:1769-1771`）`n1 != n2 => return false`，
  与参考版回落语义一致（失败而非 panic）。
- 结论：正确、两版同步。

### 3.3 `go_app_pruning` `todo!()` → 实现（正确，参考/快共享，无 parity 风险）
- 位置：`src/L09_mltt/pretty.rs:56-115`，由 `:197` `Tm::AppPruning(t, pr) => go_app_pruning(...)`
  调用。
- 与模板一致性：函数体与 L06 `src/L06_string/pretty.rs:54-113` **逐语句相同**（仅注释换行
  位置一处不同，`diff` 确认）。短名字表退化 `@序号` 不 panic。
- parity：L09 快版 `use super::pretty::pretty_tm;`（`bump_spine_iter.rs:59`），**共用**该参考
  pretty，故不存在快版独立实现分叉。触发路径（`infer_expr` 错误文案对未 quote 的推断项调
  `pretty_tm`，如 `_.foo` 的洞接收者）此前参考版 panic、现给文案；无 Ok 输出路径受影响。
- 结论：正确，无 panic 面残留。

### 3.4 A6 `prune_ty` 掩码反转（正确，两版同步）
- 参考版：`src/L09_mltt/unification.rs:124-140` 把 `Pruning`（头=最内层）反转为 `rev`
  （外→内），`prune_ty_go` 以 `rev.split_first()` 配对 Π 层；`Some(Some)` 走 rename-Π、
  `Some(None)` 走 skip、`None` 走 `rename`、其余 Err。两处 `//TODO:revPruning` 已删。
- 快版：`prune_ty_bump`（`bump_spine_iter.rs:3044`，反转在 `:3062` `mask_inner_first.iter().rev()`）
  同口径（注释亦声明）。
- 探针：`tests/l09_fast_parity.rs:611-658` `parity_nonlinear_pruning_rev_mask` 覆盖可解向
  （断言 Ok + parity）与拒绝向（codomain 依赖被剪层，断言 Err + parity）。设计合理。
- 结论：正确、两版同步，符合 ROUND2 §A6 要求。

### 3.5 A1 对齐（完整）
- 编码点仅 `tag 1/4/7`（`L07:175,187,200`；`L09:173,185,198`）。
- `XCell`：`#[repr(align(8))]`（L07:265 / L09:268）+ 断言（含 wasm32 注释）——正确。
- `CloCell`：`#[repr(align(8))]`（L07:390 / L09:406）+ 断言——正确（无 u64 字段，wasm32
  仅 4 对齐）。注：初次读取时该 repr 尚缺，A3 于审计期间并发补齐，最终快照已含。
- `PiCell`：含 `dom: V(u64)`，wasm32 上 `u64` 仍 align 8，断言通过；无 repr 必要。
- `EnvCons`：含 `val: V`，断言通过（防御性；不进 packed 字）。
- SAFETY 注释：`v_clo_of`/`v_pi_of`/`v_xcell_of` 均声明 tag 前提 + ≥8 对齐 + bump 生命期。
- 结论：A1 在 A3 切片完整落地。

## 4. 导入清理核验（避免 ROUND2 开篇的 `Either` 类误删）
- A3 删除的 use：L09 `elaboration.rs` 的 `HashMap`/`colored::Colorize`（仅出现在块注释 /
  行注释内：`:241`、`:426`、`:555` 均在 `/* */` 中——已核实）；L09 `mod.rs` 的
  `Pattern`/`Raw`/`DecisionTree`（`grep` 无使用，且无子模块 `super::Pattern`/`super::Raw`
  引用）；L09 `pattern_match.rs` 的 `ToSpan`；L07 `cxt.rs` 的 `Closure`（该文件无使用，
  兄弟模块只用 `super::PatternDetail`，不受影响）。
- `super::Either::Icit`（`pattern_match.rs:192,200`）在 mod.rs 的 `use ...::{Either, Icit}`
  保留后仍可用——orchestrator 的修复有效。
- 结论：无二次误删。

## 5. 需要 orchestrator 处置的事项

1. [P3→可选] L09 `pretty::go_ix`（`pretty.rs:48`）越界 panic 是否对齐 L06 的 `"Variable index
   out of bounds"` 文案退化（建议，非必须；属历史行为）。
2. 无编译/parity 阻塞项。L07 README 测试计数 40→46 已核实与
   `grep -c '#\[test\]' tests/l07_blackbox_v3.rs` 一致（46）。

## 6. 设计决定讨论（不属 bug）

- L09 参考版 `rename`/`eval` 对「env 未覆盖的局部层级」在 eval 侧无 `>=BASE` 守卫而直接
  `x - 1919810`（`mod.rs:285`）——依赖「局部 level 恒 < BASE」的不变式；本轮 A7 已把三个
  判界点统一为 `>=`，eval 的下标算式与之一致。若未来允许局部深度逼近 BASE 需重新评估，
  当前不可达。
