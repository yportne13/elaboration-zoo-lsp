# L09_mltt —— MLTT 切片（`Type N` 分层宇宙）

在前章语言之上的**再定基层**：以 MLTT 教学章（宇宙层级 + 和类型 / match）
为基底重写内核，非逐行继承 L08 代码。继承面与已知分歧（跨章节连贯性评审
A4 登记，锚点见 `docs/review-continuity/a4-r1.md`、`a4-r2.md`）：

- **再定基层的替换面（A4-R2 补登记）**：L08 的 decl 表 → global 哨兵表
  （`1919810` 大下标，`Tm::Var` 的 `>=` 边界）；L08 的 meta 快照/回滚、
  pm_defs/pm_solvable 特化合一状态（无 pm 机制故无宿主，见下条 fuel 论证
  ②）；`Val::Match` 的 pending 实参（值层 splice，L09 卡住 match 不可再
  应用即其时代缺口面）。
- **保留的 L08/L07 特性**：struct 脱糖（单构造子 enum `{Name}.mk`）、
  `new`、值级投影与卡住投影、resilient parser、字符串字面量。
- **显示形态（A4-R3 定案）**：SumCase 打印为 L09-L13 的 **comma 血统**
  （`头名::分支名(实参, …)`；终点章锚点：`src/L13_namespace/legacy_tests.rs:604`、
  `src/L12_canonical/mod.rs:1479` 的 `Vec[Bool]::cons(1, …)`）。L08 的
  `.mk` 去重 + 实参空格连接是其**本地形态**，不随 L08→L09 继承
  （A4-R2 曾向 L08 对齐，终门禁证明方向反了，已回滚）；卡住 match 的
  显示保留 L09 时代的 `(unsolved match n)` 简形（刻意分歧，golden
  `golden_stuck_match_display` 锚定）。
- **时代缺口（刻意分歧，不修）**：
  1. 值层不支持"卡住 match 再被应用"（`v_app` panic；见 `mod.rs` 模块头；
     unify 的 η 臂已加 `v_applicable` 守卫，该路径改判 Err）；
  2. 无 L07/L08 的 unify/force fuel——**不适用，逐失控类论证**（A4-R2
     最终裁决；L08 fuel 的 6 个烧点 `L08/mod.rs:376/387/397/420/435/448`
     在 L09 均无同构触发面）：
     - ① meta 解链间接环（L08 solve 无跨 meta occurs check 才需 fuel 兜底，
       `L08/mod.rs:361-363`）→ L09 solve 经 `occ: Some(m)` 的 rename 做
       逐 meta occurs check，解链无环（`unification.rs:419-425`；快版
       `bump_spine_iter.rs:675-676` 注释同证）；
     - ② pm_defs 精化展开（`L08/mod.rs:387-390`）→ L09 无 pm_defs/
       pm_solvable（grep 0 命中）；
     - ③ Match 重选（`L08/mod.rs:394-413`）→ L09 force 只有 Flex 臂
       （`mod.rs:232-241`、`bump_spine_iter.rs:670-682`），卡住 match 恒
       卡住，pending splice 未继承；
     - ④ decl 展开（`L08/mod.rs:414-426`）→ 全局表存终值，递归自引用在
       def/enum 检查期预注册为卡住 Rigid 占位（`elaboration.rs:289/374`），
       值层无 unfold 算子；
     - ⑤ Prim 归约（`L08/mod.rs:434-444`）→ `Val::Prim` 为无 spine 裸
       标记，`v_app` 对它 panic，永无 Prim 头链（`bump_spine_iter.rs:25-27`）；
     - ⑥ unify 深度失控（`L08/unification.rs:581-593`，失控源是比较途中
       force 展开 decl 使结构度量增长）→ L09 比较两侧为已终值，unify
       递归结构性递减（Match 臂另有 `avoid_recursive` 全局→rigid 封口，
       `unification.rs:338-345`）。
     加 fuel 属不可触发的死护栏，且 L08 fuel 耗尽有可见行为
     （`(fuel exhausted)` 诊断 `L08/mod.rs:946-953`、unify fuel=0 判 Err），
     盲加有 Ok→Err 行为变更风险，违反 parity 约束；
  3. 无 L06–L08 的 builtin 注册表 / 可变全局 / 文件 IO（`get_global` 族）；
  4. 无 L07/L08 的 `struct_eq` 卡住 match 快路径（L09 的 unify(Match,Match)
     以 `avoid_recursive`（全局→rigid）防再展开，架构不同构）。
- 卡住 match unify 的分支体比较用 `avoid_recursive` 全局表封口（参考版
  `unification.rs` Match/Match 臂）。
