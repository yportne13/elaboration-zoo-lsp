# L13 P1“双载体桥”设计草案（2026-11-17）

配套：`docs/l13-rebase-plan-2026-11-17.md`（P0–P5 总方案）、
`docs/l13-rebase-decision-2026-11-17.md`（决策与差异表）。

## 0. 目标与前提

- 目标（若执行 P1）：让 L13 的**核心机实现思路**对齐新 L12（decl 表、逐臂
  match、守卫/预算、prim、twin 结构），同时**保留 L13 产品层必需的专有面**：
  `update_cxt` 精化载体、原生 `u64` Nat、`Val::Call/OpCall`、package/import
  全限定键、prim 挂 decl 表、`eval_budget`/termination、LSP 观察面。
- 硬前提：现有 615 个层内测试与 630 个双 oracle 用例、HDL/prelude 语料是
  oracle；任何会改变这些行为的分支须先评审再改 oracle。

## 1. 为什么需要“桥”

L13 与 L12 有三处**不可逐行对贴**的表示/机制差：

1. **载体**：L13 `check_pm_final` 返回精化后的 `Cxt`（update_cxt 血统），
   L12 返回 `Rc<Subst>`（σ 血统）。审计已记录 L13 的 σ 五轮移植失败
   （prelude 21s、深 meta 解链栈溢出、GADT 覆盖误报），所以 P1 不得把 L13
   切到 σ；只能在“其余部分”对齐。
2. **值表示**：L12 参考版是 owned `Val` + `Rc<Tm>`；L13 参考版是 `Rc<Val>`
   全机。把 L13 翻成 owned `Val` 等于重写参考版全部签名与 1.2k 行 unify/
   quote 递归面，风险与收益不成比例。
3. **语法面**：L13 parser 包含 package/import/HDL/derive/错误恢复/手写优先级，
   与 L12 parser（严格 Err、无产品语法）不是同一套；不可整替。

因此 P1 的“对齐”应定义为**机制级对齐**而非表示级复制。

## 2. 桥的接口设计

### 2.1 载体桥（match 编译器边界）

- 保留 L13 `Infer::check_pm_final(..., ori) -> Result<(Tm, Cxt), Error>`；
- 在 pattern_match/elaboration 边界引入别名：
  `type Refinement = Cxt;`（L13 侧） ↔ `type Refinement = Rc<Subst>;`（L12 侧），
  使“臂特化结果如何注入分支体检查”的调用点在两侧同形；
- 分支体检查统一走 `subst_cxt(cxt, refn)` 概念：L13 的 `subst_cxt` 等价于
  refresh 后的 Cxt，L12 的是 σ 包裹。桥只保证**调用形状**一致，内部各自实现，
  不追求数据结构统一。

### 2.2 表示桥（`Rc<Val>` ↔ owned `Val`）

- 不在 L13 内混用两种表示；仅在新移植进来的**机制模块**（若从 L12 拷贝）
  的边界做 `Rc<Val>` ⇄ `Val` 适配（`rc_take`/`Rc::new`），与 L13 现有
  `rc_take` 口径一致；
- 任何从 L12 拷贝的递归内核（quote/rename/unify/force）若无法在 `Rc<Val>` 上
  低风险改写，则**不移植**，只移植表示无关的纯逻辑（预算、三档 UnifyKind、
  覆盖探测、prim 归约调度等）。

### 2.3 名字/语法桥

- decl 键：保留 L13 的 package 全限定键 + 裸名别名双轨；新 L12 的 `Decls`
  结构可作参照，但 L13 的 `cxt.rs`（1.4k 行、namespace/hover/completion 表）
  不替换；
- parser：保留 L13 parser；只把新 L11 宏基础设施（MacroState/展开/深度护栏）
  与 L13 的 prelude 宏库在**解析期接口**上合并（P2 再细做）。

## 3. P1 工作包（建议顺序）

| 包 | 内容 | 涉及文件（L13） | 门禁 |
|---|---|---|---|
| P1.1 | 冻结 oracle + 桥骨架（类型别名/注释/空实现），不改行为 | `elaboration.rs`、`pattern_match.rs` | 全量 615/630（专用窗口） |
| P1.2 | 覆盖探测/覆盖检查与 L12 对齐（值级结构探测、嵌套覆盖两段式） | `pattern_match.rs` | `test_pm_*` + gadt 语料 |
| P1.3 | 合一诊断三档（Absurd/Undecided/Fuel）与 match 比较预算对齐 | `unification.rs`、`mod.rs` | `l13_fast_parity` 相关子集 |
| P1.4 | prim/decl 表调度与 L12 对齐（仅调度形状，不换表示） | `cxt.rs`、`mod.rs`、`bump_spine_iter/prim.rs` | prelude/stdio/文件 IO 用例 |
| P1.5 | 双引擎对位检查（twin 侧同包同构改造） | `bump_spine_iter/*` | ref/twin parity |

**Do-first spike（建议只做这一个）**：P1.1 + P1.3 的一小段——在 L13 现有
`Rc<Val>` 上引入与新 L12 相同形状的 `unify_kind` 三档/预算命名与注释，
零行为变更，跑单层 lib 的 `unify` 相关小批测试。若这一步都无法在小批门禁上
稳定收敛，说明 P1 应当整体放弃（转“产品层维护模式”）。

## 4. 风险与退出条件

- 风险 1：`update_cxt` 与 σ 的语义差会让“对齐后的机制”在 L13 上出现新的
  GADT/精化回归；退出条件：任何 P1.2/P1.3 改动导致 615 中小批不可收敛。
- 风险 2：`Rc<Val>` 与 owned `Val` 的适配点泄漏到热路径，性能回退；退出条件：
  `l13bench` 代表负载回退 >10%（专用窗口测）。
- 风险 3：parser 产品面与宏基础设施合并引入解析回归；退出条件：
  `verilog_compat_tests`/prelude 宏用例失败。

## 5. 与“重跑窗口”的关系

P1 每一步都需要 L13 全量或近全量回归（615/630 级），属于重型测试；必须在
用户安排的专用窗口按“单包、限时、失败即停”执行。本轮（2026-11-17）不启动
P1 代码改动，只提交本设计草案。
