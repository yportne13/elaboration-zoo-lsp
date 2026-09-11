# L10_typeclass —— trait / typeclass 实例求解

在 L09 之上加 trait/typeclass：`trait` / `impl` 声明、接收者方法调用
（`trait_wrap`）、`outParam`、实例表 Prolog 求解（`typeclass.rs` 的
`Synth`；参考版与快版**共用同一 `Synth`**，实例匹配为单向一阶匹配
`match_typ(goal, pattern)`，与 L12/L13 的 `val_match` 同族——d4c05ea）。
继承面与已知分歧（跨章节连贯性评审 A4 登记，锚点见
`docs/review-continuity/a4-r1.md`）：

- **继承自 L09 的时代缺口（与 L09 相同，不修）**：无 unify/force fuel
  （不适用裁决与逐失控类论证见 `src/L09_mltt/README.md` 时代缺口第 2 条，
  六类失控面 L10 同构缺失；L10 自有的新失控类——实例求解的依赖子目标
  搜索——已由 `typeclass.rs:212-217` 的 effort≤1000 上限 + `:316-345`
  子目标答案缓存自带护栏，与 L08 fuel 无关）；无 builtin 注册表 / 可变
  全局 / 文件 IO；无 `struct_eq`；卡住 match 不可再应用（η 臂已加
  `v_applicable`/`vapp_ok` 守卫改判 Err）。
- **L10 相对 L09 的恢复项**：`unify` 补 `(Obj, Obj)` 合同臂（L08 血统）；
  `Val::to_typ` 的 Sum 参数槽对不可作类型的值（未解 meta）**刻意剔除**
  （`typeclass.rs` 内注释论证：实例登记侧 None 即 Err、trait_wrap 接收者
  路径依赖该剔除，勿改成整体 None；快版 `val_to_typ` 同款）。
- `Val::to_typ` 对 `LiteralType`/`LiteralIntro`/`Prim` 返回 `None`（可恢
  复，b7b4225）。
- **显示形态（A4-R3 定案）**：SumCase 打印为 L09-L13 的 **comma 血统**
  （`头名::分支名(实参, …)`；锚点见 `src/L09_mltt/README.md` 显示形态条
  与 `src/L13_namespace/legacy_tests.rs:604`）。L08 的空格格式是本地形态
  （A4-R2 的 L08 对齐已回滚）；卡住 match 显示保留 `(unsolved match …)`
  简形（同 L09，刻意分歧，l10 golden 锚定）。
