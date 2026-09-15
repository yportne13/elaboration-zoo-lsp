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

## 后续修复（2026-09-12）：参考版 Def 臂 eager nf+pretty 移除

`Decl::Def` 臂原先对每个 def 热心计算 `nf` + `pretty_tm` 填入
`DeclTm::Def { typ_pretty, body_pretty }`——两字段无任何消费方（`run` 只
取 `DeclTm::Println`），而 body 的完整规范化在大值负载上每 decl 一次
O(值大小)，church 翻倍负载实测 O(n²)（逐 decl 探针：k=13 单 decl
205ms / 最终 quote 仅 9.6ms），是 l10bench 参考版对孪生 162× 的全部来
源。两字段已删除；church basic k=13 199.4ms → 6.78ms（29.4×，×4.2/翻倍
→ ×2.0 恢复线性），对孪生倍率回落到 5.1×。L11（body 侧置空）/L13（整
段注释）同款处置的补齐；孪生侧名字/声明表 COW 同轮落地，详见
`docs/opt-name-table-cow-2026-09-12.md`。

## 精化载体移植（L07 显式替换重构回合，2026-09）

参考版 + 孪生版同批把模式精化从"上下文改写"改为"显式替换"（dpm-nbe
对齐），与 L07/L08 重构后逐一对齐：

- `unify_pm` 不再返回改写后的 `Cxt`，改为累积 `SpecSolve.acc`（持久化单链
  `Subst`/`SubstV`）；可解臂 `x := v` 解入 acc（`occurs` 只扫解值结构），
  入口 acc 非空时把方程两侧置于 σ 之下再解释；臂边界回滚 = Rc 指针赋值。
- `Cxt::update_cxt` / `Cxt::refresh` / `update_from` 删除；调用侧改用
  `subst_cxt`（env 槽 + src_names/`names.by_lvl` 类型包 `Val::VSub`/
  `XCell::VSub`，槽位布局不动）。`force` 新增 VSub 臂 → `frcs`（对齐
  dpm-nbe `frc`/`frcS`）：spine / Sum(SumCase) 槽只包裹不物化（保 invert
  可逆），被解 rigid 读点按应用序解析应用（带 `v_applicable`/`vapp_ok`
  守卫），卡住 match 的 scrutinee 单独推进后重选分支；`force_arg` 逐层解包
  VSub 供 `invert`/`prune_vflex` 的参数视角。
- **L10 定制**：(a) 可解集 = **任意裸 Rigid**（旧 `update_cxt` 语义，无 L07
  的 bind-slot 白名单），故 `SpecSolve` 无 `solvable` 字段；(b) **occurs 守卫
  不扫 Flex 的 spine**——L10 的元变量以全 scope 剪枝 spine 登记，spine 合法
  含当前方程的 rigid，旧机制无 occurs，扫 spine 会把 GADT 嵌套 match 的合法
  解误判成环（test5/test6/test_index/test0/test7 回归）；(c) `to_typ` 消费点
  改走 `force_deep`（Sum/SumCase 槽位一并推开），否则 trait 接收者类型经
  `val_to_typ` 掉参、实例匹配失配（`has no object`）；(d) 孪生 `subst_cxt`
  必须同步包裹 `names.by_lvl` 影子索引（`Raw::Var` 快路径经它取类型），只包
  `types` 链会丢外层精化。
- **交互点**：`unify_pm` 只服务模式方程路径；trait 实例求解走常规 `unify`
  （`solve_trait_ref`），不带 spec——实例求解过程中的合一**不会**获得特化解
  能力（与旧 `update_cxt` 只从 `unify_pm` 调用的边界一致）。
- 孪生 `bump_spine_iter` 无燃料池（模块注释：force 无燃料），`frcs` 的
  lookup 命中不做有界降级；`update_cxt`/`refresh`/`refresh_local`/
  `mention_cache`/`val_mentions_lvl_shallow` 整体删除。
- 验收：`--lib` 705 全绿；`l10_fast_parity` 32 全绿；移植前后基线快照
  （l10_fast_parity 全部源码字面量 + 生成器负载 + `examples/*.typort`，
  参考版与孪生版各 45 段）**逐字节一致**（0 diff）。
