# A1 Cross-R2 — 只读交叉审计 A2 切片

审计范围（BRIEF §5 轮转：A1 → A2）：`src/L13_namespace/{unification,typeclass}.rs`、
`src/L13_namespace/bump_spine_iter/{unify,typeclass,observe,quote,rename,compact,force,eval,prim}.rs`、
`tests/l13_fast_parity.rs`。**本报告只读，未改 A2 任何文件**（BRIEF §5：交叉发现由 Lead 转交所有者）。

> 口径说明：(1) 审计时 A2 正在编辑 `unification.rs` / `typeclass.rs`，行号是本快照；
> 凡引用这两处我同时给出函数名。(2) 我**未看到 A2 的 R1 报告**，本报告可能与 A2 自审条目重叠；
> 重叠即互为交叉验证。(3) 无 Miri、未运行 cargo，unsafe 类只做静态刻画（BRIEF §6.7）。

## 1. 结论（verdict）

- 本切片本轮交叉发现：**P0: 1（会签，非新发现）  P1: 0  P2: 1  P3: 4  needs-verify: 4**
- 未发现"参考版修了、快版漏修"的新分叉；抽查的 panic/unreachable 大多两版同形。
- 唯一 P0 是 `FINAL.md` §3.1 已刻画的整机重借 SB 别名 UB：我独立复核后**会签**该刻画
  （A3 主查、A2 会签的分工不变）。

## 2. 发现列表

### [P0·会签] 快版整机重借：`flex_flex_bump` / `solve_side_bump` 的 use-after-invalidate
- 位置：`src/L13_namespace/bump_spine_iter/unify.rs:384`（函数 `flex_flex_bump`，头 `:337-357`）、
  `:1395`（函数 `solve_side_bump`，头 `:1378-1387`）。
- 证据：两个函数的形参把 `Machine` 的字段**拆成独立可变借用**
  （`spine: &mut Spine`、`work`、`vals`、`icits`、`metas: &mut Vec<MetaEntry>`、`mutable`、`ren`）
  **外加** `mach_ptr: *mut Machine`；随后
  ```rust
  unsafe { (&mut *mach_ptr).solve_multi_trait_ref(bump, cxt, fb, false).is_ok() }   // :384
  let tr = unsafe { (&mut *mach_ptr).solve_multi_trait_ref(bump, cxt, m, false) };   // :1395
  ```
  在这些字段借用**仍然存活**时重建整机 `&mut Machine`。严格 Stacked Borrows 下这次重建会
  invalidate 先前派生的字段引用，而调用帧返回后字段引用还要继续使用
  （如 `unify.rs:612-617` 的循环继续 `force`/`spine` 操作）⇒ use-after-invalidate。
  与 `FINAL.md` §3.1 的刻画一致（当时点名 `L10 bump_spine_iter.rs:3729/3739/3741-3753`、
  `L11 :2385/:2501/:2524`、`L12 :2436/:2552/:2575` 的同族位置）。
- 机制/影响：本环境无 Miri，无法确认是否被当前 rustc 的 SB/TB 规则实际判定为违规；
  若成立则是 P0 级 UB（只影响快版，但 LSP 默认走快版）。
- 处置：**仅报告/会签，未改**。修法（把 `solve_multi_trait_ref` 改成接收不相交字段的自由函数）
  属高风险重构，且 A2/A3 的 R1 改动正在同一文件上，不应交叉动手。建议单独立项 + CI 跑
  `MIRIFLAGS=-Zmiri-strict-provenance cargo miri test`。

### [P2·needs-verify] `vals_eq_ground` 把 `Val::Flex` 视为等于一切
- 位置：`src/L13_namespace/typeclass.rs:385-388`（`vals_eq_ground_impl` 的首臂
  `(Val::Flex(..), _) | (_, Val::Flex(..)) => true`），公开入口 `:381-383`。
- 证据：这是 `FINAL.md` §3.4 对 L12 的同款条目在 L13 的延续。L13 **已经**把同一函数的
  `Match` 臂硬化了（`:435-448`：比 case 表 + body 的 `Rc::ptr_eq`，注释自述"只比 scrutinee 与
  env 长度是不 sound 的"），但 Flex 臂保留"恒真"。
- 调用面（决定影响）：`val_match` 的"已绑定 rigid 的结构相等"检查（`:311-317`）与
  `nat_matches_chain_ground`（`:278-287`）都经 `vals_eq_ground`；`val_match` 自身首臂
  （`:298`）对 Flex 同样恒真——两处口径一致，所以这不是"某一份漏改"，而是**统一的放宽语义**。
- 机制/影响：理论上"目标侧是未解 meta（Flex）而实例模式已有绑定"时会判相等 ⇒ 可能选中结构上
  不匹配的实例（静默错误结果）。我**未能构造触发程序**（需要 flex 实例头 + 已绑定 rigid 的组合），
  故记 P2 + needs-verify。
- 处置：**仅报告**。请 A2 二选一：(a) 收紧为"Flex 不等于具体值"（须确认所有调用点都只喂 ground 值，
  否则会翻出新的失败）；(b) 在 `typeclass.rs` 文档里把该放宽正式记为已知偏差（含它为何不破坏
  `val_match` 的第一臂语义）。

### [P3·needs-verify] `new_subgoal` 对未注册 trait 名 `.unwrap()` → panic
- 位置：`src/L13_namespace/typeclass.rs:588`：`let instances = self.class_instances.get(&subgoal.name).unwrap().clone();`
- 机制/影响：subgoal 来自实例/默认方法的依赖（where 子句）。正常路径上每个被声明的 trait 都
  走过 `new_trait`，所以大概率"仅内部不可达"；但 `.unwrap_or_default()` 就能把它降级成
  "无实例 ⇒ 正常报 can't solve"，零语义风险。
- 处置：**仅报告**，请 A2 定性（我没有构造出依赖未注册 trait 的程序）。

### [P3·needs-verify] `panic!("Cannot resume with empty subgoals.")`
- 位置：`typeclass.rs:554`（`resume_stack` 弹出的 `ConsumerNode.subgoals` 为 nil 时）。
- 机制/影响：压栈侧只在仍有剩余子目标时压（`consume`，`:598-604` 起），构造上应不可达；
  记为内部不变式，未给出触发面。
- 处置：**仅报告**。

### [P3·needs-verify] `lams_go` 的 `unreachable!()`：Π 层数不足
- 位置：`src/L13_namespace/unification.rs:521`（`lams_go`，`:491-527`）。
- 证据：`l != l_prime` 时要求当前类型仍是 `Val::Pi`（两个 Π 臂 + `_ => unreachable!()`）。
  `prune_meta` 用 `self.lams(Lvl(pruning.len() as u32), decl, &mty, Tm::AppPruning(..))`
  —— 依赖不变式「pruning 长度 = meta 类型的 Π 深度」。快版同款同注释：
  `bump_spine_iter/rename.rs:883-885` `unreachable!(); // 类型 Π 层数不足（上游同款不可能）`。
- 机制/影响：**两版一致 ⇒ 不是分叉**；但"不可能"缺证明，而**值层**的同族错配在 L13 有优雅降级
  先例——参考版 `v_app_pruning` 第三臂注释"pruning 记录在比 eval 环境更深的上下文：缺的参数没有值，
  只应用 spine 的其余部分"（`mod.rs` 的 `v_app_pruning`）。既然值层承认会出现"pruning 比环境深"，
  类型层"pruning 比 Π 深"就值得一句不变式说明。
- 处置：**仅报告**（建议 A2 在 `prune_meta` 入口补 debug 断言或文档化该不变式）。

### 正面结论：快版 `vapp1` 与参考版 `v_app` 逐臂对齐（含 R1 修过的 stuck-Match）
- `bump_spine_iter/force.rs:54-59` 的模块注释逐臂声明与参考版 `v_app` 对齐；
  `:157-191` 的 `XCell::Match` 臂把应用 splice 进每个分支体（quote 实参后 `Tm::App`），
  与参考版 `v_app` 的 `Val::Match` 臂同款 —— 参考版 R1 修掉的
  "`(match x { … }) arg`（x rigid）用户可触发 panic"在快版**同样已修**，不是"修一漏一"。
- `force.rs:192/195` 的 `panic!("impossible apply")` 与参考版 `v_app` 末尾 catch-all 同形，
  两版同时不可达/同时 panic（未能证明绝对不可达：需要"卡住非函数值被应用"的形状，
  而 elaborate 期会先报 `can't unify expected: (x: ?N) → ?M x` 拦住，见 A1 `a1-r2.md` §2 撤回条）。

### 抽查的 `unreachable!()`（未逐条定性，供 A2 自审对照）
- `unify.rs:630`/`:634`：紧邻的 `matches!(v_xcell_of(..), XCell::Call{..})` 守卫使其构造上不可达 ✓。
- `unify.rs:1285`、`typeclass.rs:161`、`rename.rs:193`/`:259`/`:752`、`machine.rs:1642`/`:2279`：
  未逐条定性；`machine.rs:1796` 是参考版 `elaboration.rs:646` 的同款（fuel 耗尽窗口可解，
  见 A1 `a1-r2.md` §2 的 P2 条，建议两版一起决定）。

## 3. 本轮改动清单
无（交叉审计只读，遵守 BRIEF §5"交叉发现不得直接改别人的文件"）。

## 4. 需要 orchestrator 处置的事项
1. 把本报告 §2 的 P2（`vals_eq_ground` Flex 恒真）与三处 P3/needs-verify 转交 A2，由其在自己的
   R2 决定"改 / 文档化"。
2. P0 会签项：与 A3 的 §3.1 结论合并，作为"单独立项 + Miri"的输入（本次仍不修）。
3. `machine.rs:1796` 与参考版 `elaboration.rs:646` 应作为一个跨版条目一起决定（涉及 A2/A3 边界）。

## 5. 设计决定讨论（不属 bug）
- **`norm_err` 的归一化与 span 保真**：`tests/l13_fast_parity.rs:70-131` 把 `@ N`、`?N` 归一化，
  这是双实现 meta 序列/内部 span 不同的必要处理；但副作用是 **parity 层看不见错误 span 的漂移**
  （两边都把 span 抹平）。span 保真只能靠 `tests/hdl_check_locations.rs` 之类的专用断言。
  记为**覆盖缺口**（P3，非新问题；A7 面更相关）。建议在该文件头注释里写明这一局限
  （现有注释只说明"为什么要归一化"，未说明"归一化掩盖了什么"）。
- **双引擎证据链**：`l13_fast_parity` 的 Ok 逐字节比对 + `twin_engine_tests` 是快版正确性的主要
  钉；`Synth` 由两版共用（`bump_spine_iter/typeclass.rs:245` 调 `Synth::val_match`），
  所以实例匹配语义的修复天然两版同判 —— 这一共享结构值得在 README 里明确写成契约
  （我 R1 已核实 `val_match` 单向匹配两版一致）。
