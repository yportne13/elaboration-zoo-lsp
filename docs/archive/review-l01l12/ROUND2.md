# ROUND 2 作业书（L01–L12）

> 前置：读 `BRIEF.md`。第 1 轮所有改动已集中 `cargo check` 通过、L02–L12 全量集成测试
> （23 target / ~1600 用例）**全绿**。本轮开始前 orchestrator 修了一个编译错：
> A3 误删 `src/L09_mltt/mod.rs` 的 `Either` 导入（`pattern_match.rs` 经 `super::Either` 依赖），
> 已恢复为 `use parser::syntax::{Either, Icit};`。教训：**`use` 是否 unused 要看子模块的
> `super::X` 引用**，不要只看本文件。

## A. 本轮确认的新问题（orchestrator 已独立核实，必须处理）

### A1【P0·wasm 目标 soundness】`XCell` 在 32 位目标对齐不足，packed tag 解码 UB
- `XCell` 定义为 `enum XCell<'a> { Lit(&'a str), Decl(&'a str) }`，**不含 u64 字段**；
  在 64 位目标 `align_of == 8`，但在 `wasm32`（`&str` = 8B/align 4）`align_of == 4`。
- packed 编码用 3 位 tag（`v_xcell` 写 `ptr | 7`，`v_xcell_of` 读 `v.0 & !7`）要求
  分配地址低 3 位为 0 → **32 位目标会清掉 bit2，解引用错误指针 = UB**。
- `Cargo.toml` 明确为 wasm 目标做条件依赖、vscode web 扩展要构建 wasm LSP 二进制，
  所以这不是纯理论问题。
- 出现位置（`enum XCell`）：`src/L06_string`、`L07_sum_type`、`L08_product_type`、
  `L09_mltt`、`L10_typeclass`、`L11_macro`、`L12_canonical` 的 `bump_spine_iter.rs`
  （`L13_namespace` 同款，属共享文件不在本次范围，只在报告里记）。
- **修法（最小且 64 位零行为变化）**：给每个 `XCell` 枚举加 `#[repr(align(8))]`，
  并在附近加一行编译期断言，例如：
  ```rust
  // wasm32 上 `&str` 仅 4 字节对齐，而 packed tag 用 `& !7` 解码，要求 ≥8 对齐。
  #[repr(align(8))]
  enum XCell<'a> { ... }
  const _: () = assert!(std::mem::align_of::<XCell<'static>>() >= 8);
  ```
  同时把 `CloCell`/`PiCell`/`EnvCons` 等**所有被 `ptr|tag` 编码的类型**都加同类编译期断言
  （它们含 `V(u64)` 通常已 ≥8，断言只是钉住不变式；若某类型断言不过，加 `#[repr(align(8))]`）。
  在 `v_xcell`/`v_xcell_of` 的 SAFETY 注释里点明"依赖 `XCell` ≥8 对齐（由 `repr(align(8))`
  保证，含 wasm32）"。

### A2【P1·parity/可达 panic】L11/L12 η 臂缺 applicability 守卫
- `src/L11_macro/unification.rs:644,650`、`src/L12_canonical/unification.rs:678,685`：
  η 臂对非 λ 侧无条件 `self.v_app(...)`，而非中性值走 `panic!("impossible apply")`
  （L11 `mod.rs:321`、L12 同形）。
- 触发链（A2 已给证据）：这两层的 `string_to_global_type` 取 decl **值**，
  `get_global` 类型是 `(x:String)->string_to_global_type x`；于是
  `def f : U -> U = x => x` + `def g : String = get_global "f"` 会让 `LiteralType ≡ λ`
  落 η 臂 → panic。L06 已用 `v_applicable` 修（见 `src/L06_string/unification.rs:476,481`
  与 `tests/l06_blackbox_v3.rs` 的 `bug1_eta_*` 组），L13 用 `is_appliable`，
  唯 L11/L12 漏改。
- **修法**：把 L06 的守卫移植到 L11/L12 参考版**与快版**（快版 `vapp1` 同形），
  两版同步；并加最小复现测试（放各自 blackbox/parity 文件，L06 的 `bug1_eta_*` 作模板）。

### A3【P1·parity/可达 panic】`intersect_go` 长度失配 `unreachable!()`
- L09、L10 本轮已修为 `_ => None`。**L11/L12 仍是 `unreachable!()`**：
  `src/L11_macro/unification.rs:587`、`src/L12_canonical/unification.rs:602`。
- **修法**：改成 `_ => None`（回落 `unify_sp` 失败），与 L05–L10 及各自快版
  （`intersect_bump` 对 `n1 != n2` 返回 false）一致。

### A4【P1·可达 panic】L11/L12 超大整数字面量 `parse::<u64>().unwrap()`
- `src/L11_macro/parser/mod.rs:506`、`src/L12_canonical/parser/mod.rs:549`。
- 触发：`def x = 99999999999999999999999999`（>`u64::MAX`）→ parse Err → panic。
- **修法**：parse 失败时推一条 `IError` 并退化为 `Raw::Hole`（或与现有语法错误同款处理），
  两副本同步；注意保持正常数字的既有输出。

### A5【P1·panic/parity】trait 求解 `.unwrap()`
- L11 参考版 `src/L11_macro/elaboration.rs:294` + 快版 `bump_spine_iter.rs:5324`：
  `solve_multi_trait(...).unwrap()`。L12 参考版已改为 `map_err(...)?`（返回 Err）。
- **修法**：L11 参考版+快版成对改为可恢复错误（对齐 L12 参考版口径，Err 文案一致）；
  两版必须同判定（都 Err）。
- 另：`src/L12_canonical/bump_spine_iter.rs:5401` 快版仍 `.unwrap()`，而参考版
  `elaboration.rs:313-314` 已返回 Err → 判定分叉。**修法**：快版改为与参考版同 Err 语义
  （或若确认属已剔除的缺陷家族，则把该偏差正式写进 `tests/l12_fast_parity.rs` 头部清单，
  不得默默存在）。优先尝试对齐。

### A6【P2·parity 风险】`prune_ty` 未反转 pruning 掩码
- L05–L08 已把掩码 `rev.reverse()`（外→内配对 Π 层），L09–L12 仍是旧移植
  (`//TODO:revPruning`)：`src/L09_mltt/unification.rs`、`L10_typeclass/unification.rs:99-121`、
  `L11_macro/unification.rs`、`L12_canonical/unification.rs`。
- **修法**：对照 `src/L08_product_type/unification.rs:148-152` 与各自快版
  `prune_ty_bump`（注释"掩码外→内配对 Π 层"，`mask_inner_first.iter().rev()`），
  把参考版改为一致。**这是行为变更**：必须补多层非线性 pruning 的 parity 用例证明
  两版在改后一致，且现有测试不回归。

### A7【P2·潜在 off-by-one】全局哨兵 `1919810/GLOBAL_BASE` 边界
- L09 本轮修了 `>` → `>=`（0 号全局自引用下溢）。**请核对 L10/L11/L12** 的
  `lvl2ix`/rename/quote/Raw::Var/update_cxt 边界与 eval 是否同口径
  （eval 用 `x - BASE` / `*i >= BASE`）。全仓 grep `1919810`、`GLOBAL_BASE`，
  以"全局 iff `level >= BASE`"为准。若发现同款下溢，修参考版+快版并加
  `def f : String = f` 类最小用例。

### A8【P0·用户可达栈溢出】自递归宏无展开深度上限（L11/L12）
- `src/L11_macro/parser/mod.rs`（展开后重 lex 再递归 `p_raw`/`p_decl`）、
  `src/L12_canonical/parser/mod.rs` 同形。触发：
  ```
  macro_rules m { () => { m } }
  def x = m
  ```
- **可行最小修法（不扩 MacroState 元组 arity）**：在模块内加
  ```rust
  thread_local! { static MACRO_DEPTH: std::cell::Cell<u32> = const { std::cell::Cell::new(0) }; }
  const MAX_MACRO_EXPANSION_DEPTH: u32 = 256; // 取值需远大于合法嵌套深度
  ```
  在**宏展开重解析**的递归调用点前：递增计数，若 `>= 上限` 则推一条 `IError`
  （如 "macro expansion too deep"）并返回错误/`Raw::Hole`，不进入递归；用 RAII guard
  在作用域结束递减（panic 展开也安全）。只在宏展开路径计数，普通解析不受影响。
  两副本同步；加探针测试：`macro_rules m { () => { m } } def x = m` 断言**不栈溢出**、
  返回解析错误而非 panic（`#[test]` 用 `std::thread::Builder` 小栈线程可稳定复现）。
- `L13_namespace` 同构副本属共享文件，本轮**不改**，在报告里记为已知残留。

### A9【P3·文档/测试】清理项
- `tests/l02_blackbox.rs:5` 注释引用不存在的 `tests/l03_review_probe.rs`。
- README/模块头的测试计数漂移：L02 `readme.md:34`、L03 `readme.md:49`、
  L07 `README.md:312`、L08 `README.md:217-233`、`tests/l08_fast_parity.rs:5-6` 头注释。
  以静态 `#[test]` 计数为准更新，或注明"含 ignored / 口径"。
- L08 README §8、L07 README §8 的数字请以 `rg -c '#\[test\]' tests/l08_* src/L08_product_type` 核准。

## B. 明确**不做**（本轮只记录，不盲改）

1. **Stacked Borrows 别名 UB**（L10/L11/L12 快版 `&mut *mach_ptr` 重入 `solve_multi_trait_ref`）：
   属语言级 UB，但修复需把整机重借改成不相交字段自由函数，是高风险大重构，且本环境无 Miri
   验证。**保留为已知 P0 记录**，在报告 §5 写清机制、触发条件、建议修法（不实施）。
2. **L10/L11 `Synth::unify` 无 occurs check 的旧求解器**：L12/L13 已重写为 `val_match`。
   移植是语义重写，风险高。本轮**写探针测试确认是否真的会选错实例**（见 §C），
   确认后在报告记录；不盲改实现。
3. **L09 `v_app` 对卡住 match 应用 panic**：L09 时代缺特性，测试注释已承认两版同崩。
   记录为已文档化限制；建议在模块头/README 正式标注。
4. **L09 `check_universe` 把 meta 解成 `U(0)`**、**canonical IDDFS 完备性 `basic_target_limit`**、
   **`Val::Flex` 等于一切**等：needs-verify，写探针测试判定，不盲改。
5. **跨层共享文件**（`src/list.rs`/`bimap.rs`/`parser_lib*.rs`/`L13_namespace/**`）：
   只报告，不改。

## C. 探针测试（本轮新增要求）

对每个 needs-verify 的核心项，在**自己拥有的** `tests/` 文件里加一个**可运行的最小探针**
（`#[test]` 或 `#[ignore]` 均可，但要有明确断言），由 orchestrator 集中运行裁决：

| 项 | 负责 | 探针应断言 |
|---|---|---|
| L10 Synth 假匹配 | A4 | 用报告里的 `Say`/`List[T]`/`def f[T](x:T)=x.say` 源，断言实际结果（若 Err 则 bug 不成立，需更正报告） |
| L11/L12 η 守卫修复 | A5 | 修复前 panic、修复后 Err 且参考/快版判定一致 |
| L11/L12 宏自递归 | A5 | 修复后不栈溢出、给解析错误 |
| L11/L12 u64 溢出 | A5 | 修复后给语法/解析错误而非 panic |
| L12 快版 `:5401` 分叉 | A5 | 参考/快版同判定 |
| L09 全局哨兵 | A3 | `def f : String = f` 两端一致、`println f` 输出 `recursive_0`（已修，补钉子） |
| XCell 对齐 | A2/A3/A4/A5 | 编译期断言即可；可另加 `assert_eq!(align_of::<XCell>(), 8)` 的 `#[test]` |
| L10 prune_ty rev | A4 | 多层非线性 pruning 的参考/快版 parity |

**注意**：探针若无法只靠静态推理给正确期望，先用占位断言（如只断言"不 panic"），
并在报告标注期望待 orchestrator 运行后回填。

## D. 轮转交叉审计（只读，写 `a<N>-cross-r2.md`）

A1→A2、A2→A3、A3→A4、A4→A5、A5→A1。重点：
- 上表修复是否真的两版同步、是否有遗漏的同类拷贝；
- 交叉读对方切片的 `git diff`（`git diff -- src/L0X`），找"改错/漏改/注释与代码不符"；
- 交叉发现**不得直接改对方文件**，写进报告，由 orchestrator 转交。

## E. 每 agent 的切片任务汇总

- **A1**（L01–L03）：A1/A9（自己部分）；核对 L01–L03 所有 packed 类型对齐断言；
  复核 L01 2 位 tag（`!3`）在 32 位下是否只需 ≥4 对齐且满足；交叉审计 A2。
- **A2**（L04–L06）：A1（L06 `XCell` + L04/L05 所有 tagged 类型断言）；
  A9；评估 L04/L05 η 守卫是否应补（有 L06 先例，倾向补，但需证明不改既有行为）；交叉审计 A3。
- **A3**（L07、L09）：A1（L07/L09 `XCell`）；A7（核对自己已修，防漏）；A6（L09 `prune_ty`）；
  交叉审计 A4。
- **A4**（L08、L10）：A1（L08/L10 `XCell`）；A6（L10 `prune_ty`）；A7（L10 哨兵）；
  C 表 L10 探针；交叉审计 A5。
- **A5**（L11、L12）：A1（L11/L12 `XCell`）；A2/A3/A4/A5/A6/A7/A8（L11/L12 全部）；
  C 表探针；交叉审计 A1。

## F. 报告与收敛

- 每 agent 写 `a<N>-r2.md`（BRIEF §7 格式）+ `a<N>-cross-r2.md`。
- 收敛判据仍按 BRIEF §2：自审 0 个 P0/P1/P2（P3 可列），交叉 0 个 P0/P1/P2，
  且 orchestrator 编译+测试全绿。
- 本轮结束时，**每条第一轮遗留的 P0/P1/P2 必须二选一**：已修（给 diff 摘要）或
  明确记为"经论证不修/需独立重构"并给出理由与建议。不允许悬空。
