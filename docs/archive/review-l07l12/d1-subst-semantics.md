# D1 显式替换重构的语义正确性（蓝本一致性） — L07–L12 只读评审

## 1. 结论（verdict）

- **P0: 0  P1: 0  P2: 1  P3: 4  needs-verify: 4**
- 覆盖范围与方法：
  - 精读了 L07 蓝本五文件的核心机制：`mod.rs`（`Subst`/`Subst::lookup_hit`/`mentions_level`/`extend`/`compose`/`wrap_sub`/`force`/`frcs`/`force_arg`/`v_app`/`val_mentions_lvl`）、`unification.rs`（`SpecSolve`/`unify` 的 spec 穿参与入口 acc 包裹）、`pattern_match.rs`（compile/walk_con/unify_indices/probe_accessible/eval_aux）、`cxt.rs`（`subst_cxt`/`bind_slots`）、`struct_eq.rs`。
  - 机械比对：`diff` L07↔L08 的 `cxt.rs`/`struct_eq.rs`/`pattern_match.rs`（逐字相同）/`unification.rs`（仅格式化 + L08 自有的 `(Obj,Obj)` 合同臂）/`mod.rs`（仅格式化 + 环境变量名/demo 文本）/`elaboration.rs`（仅 L08 record/struct 自有特性）；`diff` L07↔L08 孪生版（仅格式化与早退微重构）；L10↔L11↔L12 的 `unify_pm` 抽取比对（同形，仅 decl 穿参/Rc 约定差异）。
  - L09–L12 逐文件定点核对：`mod.rs` 的 Subst/force/frcs/v_app/val_mentions_lvl、`elaboration.rs` 的 `check_pm`/`check_pm_final`/`unify_pm`/`spec_refine`、`unification.rs` 的 spec 臂、`pattern_match.rs` 决策树叶子、`cxt.rs` 的 `subst_cxt`、L12 `canonical.rs` 读点。
  - 孪生版：L07 孪生精读（`SubstV`/`frcs`/`force_arg`/`subst_cxt`/unify spec 臂/臂边界回滚/编译器 probe），六层孪生的 `SubstV`/`SpecSolve`/`frcs`/`force_arg`/`subst_cxt`/fuel 池存在性 grep + 关键点抽读（含 dbe79cf 补齐的 L10/L11/L12 孪生燃料池）。
  - git 只读：`ccfcb87`（L09 移植）前后 diff、`2129975`（L11）/`58073dd`（L12）、`dbe79cf`（孪生燃料补齐），用于区分移植引入 vs 既有行为。
  - 未运行 cargo（按 BRIEF 硬约束）。

### 评审清单逐项结论

| # | 清单项 | 结论 |
|---|---|---|
| 1 | 旧机制清除 | **有残留（仅注释层）**。六个模块的活代码中 `unify_pm`(L07/L08)/`update_cxt`/`refresh`/`pm_defs`/`pm_solvable`/`pm_mark`/`pm_restore` 均 0 命中（grep 全部落在 `//`/`///` 注释、README、测试注释）。L09–L12 活代码中的 `unify_pm` 是**重建的同名函数**（解入 `SpecSolve.acc`，见 §4 设计决定）。陈旧注释见发现 [P3-3]。L09–L12 的 `Infer.global` 存活，但它是全局定义表（`Tm::Var` 大下标哨兵的名字解析表，eval 读点 `src/L09_mltt/mod.rs:648-651`），**不是精化载体**，符合移植计划"承载非精化职责则拆分/保留"的口径；BRIEF 中"Infer.global 应已不复存在"的表述过宽（见 §4）。 |
| 2 | Sub 语义 | **一致**。六层参考版的 `Subst` 均为持久化单链（L07 `mod.rs:199-325` ↔ L08 逐字 ↔ L09 `mod.rs:175-286` ↔ L10/L11/L12 同构；L12 为 `Rc<Val>` 值约定的适配版 `mod.rs:283-390`）；`lookup` 未命中回 `vvar(x)`（L07 `mod.rs:239-241`）；`extend` O(1) cons、链头=最新（右偏 union 语义由"沿链首个命中"实现，`lookup_hit` L07 `mod.rs:223-236`）；`compose(outer, inner)` 外层条目接链头=外层覆盖（L07 `mod.rs:307-324`）；`lookup_hit` 条件包裹（解值浅结构不引用已解层级时零分配直通，`mentions_level` 含闭包 env 槽/Match scrutinee+env+pending，不含闭包体）六层一致。均按设计文档 **§9 注记 4 的定稿口径**（链表+条件包裹），非早期 §3 的 FxHashMap 稿——报告口径以 §9+代码为准。孪生版 `SubstV`（L07 `bump_spine_iter.rs:322-401`）逐点同构。无各层自行发明变体。 |
| 3 | VSub 不变式 | **一致**。`force` 的 VSub 臂入口不烧 fuel、frcs 的 Rigid 臂 lookup 命中烧 1、耗尽回裸 rigid（L07 `mod.rs:519-524, 616-628`；L09 `mod.rs:452-456, 475-498`；L10/L11/L12 `burn_fuel` 同口径），孪生版同（L07 孪生 `bump_spine_iter.rs:1605-1608, 1721-1729`）。"force 后顶层非 VSub"由构造保持：frcs 各臂返回同型值/交回 force，`v_app` 的 VSub 臂先 force 再分发（L07 `mod.rs:977-984`、L09 `mod.rs:600-609`、L12 `mod.rs:880-887`）；quote 处另有防御臂（L09 `mod.rs:773-775`）与 rename 的 `VSub => Err` 防御臂（L07 `unification.rs:310`、L09 `unification.rs:261-263`、L10 `unification.rs:263-265`、L12 `unification.rs:277-279`）。包裹点（`wrap_sub` 全部消费点）与消耗点（force/frcs）配对核对无孤立包裹。发现 [P3-4]（L10–L12 缺入口 refuel）。 |
| 4 | SpecSolve/解的线程 | **一致（分层内）**。L07/L08：`unify(…, Option<&mut SpecSolve>)` 穿参、入口把方程两侧置于 `acc` 之下（`unification.rs:637-642`）、可解臂 `solvable.contains + 非 Flex + 浅 occurs` 后 `Subst::extend`（`unification.rs:678-705`）、臂边界 `self.sub = sub_snap`（`pattern_match.rs:158`）、probe = meta 快照+局部 σ+`meta_restore`（`pattern_match.rs:195-233`）、不可达 = `Walk::Unreachable` 定向报错（`pattern_match.rs:148-151`）。L09–L12：同一套以 `check_pm`/`check_pm_final`/`unify_pm`/`spec_refine` 形态落地（L09 `elaboration.rs:74-230`），决策树叶子做 `subst_cxt` + 期望类型 wrap+重锚（`pattern_match.rs:253-284`）。Absurd（第二方程）失败容忍一致；Absurd（第一方程）在叶子上的失败处理分层不一：L09 panic、L10–L12 优雅返回——见 needs-verify #1/#2。 |
| 5 | 浅 occurs 守卫 | **一致中有一处分层分歧（已文档化）**。`val_mentions_lvl` 只扫解值浅结构、不进闭包体（L07 `mod.rs:1247-1279`），环靠 frcs lookup 命中烧 fuel 兜底，六层同。分歧：L07/L08 扫 `Flex` 的 spine（`mod.rs:1253`），L09–L12 把 `Flex` 头整体视为不透明（L09 `mod.rs:328-334`，L10 README"定制(b)"明文）。该分歧是移植时的有意取舍（附误判场景论证），非错接；记入 §4。 |
| 6 | 槽位纪律 | **一致**。`subst_cxt` 只包 env 槽与 src_names（L09–L12 为 BiMap）类型，lvl/locals/pruning/decl 不动（L07 `cxt.rs:258-275`；L10 `cxt.rs:156-172`；L11 `cxt.rs:458-`；L12 `cxt.rs:316-`）；孪生版额外包 `names.by_lvl` 影子索引（L09 孪生 `bump_spine_iter.rs:5086-5110`），与 L10 README 定制(d)一致。frcs 对 spine/Sum/SumCase 槽只包裹不物化（L07 `mod.rs:635-683`、L09 `mod.rs:499-542`、孪生 L07 `bump_spine_iter.rs:1633-1716`）、Match scrutinee 单独推进、闭包 env 逐槽包裹——六层参考+孪生全部同构。`bind_slots` 解包 VSub 取 raw 层级（L07 `cxt.rs:283-299`、L09 `cxt.rs:180`）。未发现"捕获旧上下文的值过期/槽位错位"类残余：解不改写任何既有值，回滚=Rc 赋值，嵌套 match 经 `subst_cxt` 包裹后 `bind_slots`/`force_arg` 均逐层解包（L07 `mod.rs:487-501`）。 |
| 7 | 各层特性交互 | **无机制错接**。L08：积类型/record 仅扩展 `(Obj,Obj)` 合同臂与 struct 脱糖（`unification.rs:772-780`），精化机制与 L07 逐字同。L09：决策树编译保留，`check_pm(_final)` 在叶子产出 σ、`subst_cxt` 后查体；`checked_ret` 按臂下标复用（L13 2a0eb6e 同族注释），经布局推演（见 §3 needs-verify #3 的排查过程）确认通配臂在深层列被丢弃后各路径槽位数与运行时 `eval_aux` 的 prepend 数一致，未发现布局错接。L10：trait 实例求解走常规 `unify` 不带 spec（`elaboration.rs:113-118` 注释+代码），与旧 `update_cxt` 边界一致；`to_typ` 消费点走 `force_deep`（README 定制(c)）。L11：宏在 parser 层展开为 Raw（`parser/mod.rs:1064/1124/1187`），展开产物经与普通代码相同的 check_pm 路径，无独立机制可错接。L12：canonical 求解（`canonical.rs`）**发现一个读点遗漏**——见 [P2-1]。 |
| 8 | silently accept | **未找到可确证的构造性反例**。四个候选（L09 叶子 unwrap panic、L10–L12 叶子 Err 后缺臂、决策树覆盖假阳性、L09 Rigid≐Flex 丢弃方程）均静态推演到"需要探测/叶子判定分歧或极端语法形态才能触发"，且多数为**既有**（pre-port）行为而非本移植引入——降级为 needs-verify，见 §3。确证的反例一个都没有是不太寻常的诚实结论：显式替换重构本身的机制层（Subst/frcs/spec 线程/回滚）在六层内是干净且一致的。 |

## 2. 发现列表

### [P2] L12 canonical 求解读点未 force σ 包裹的 src_names 类型与 env 槽（影响面：L12 参考版，仅 LSP quickfix 路径）
- 位置：`src/L12_canonical/canonical.rs:60-94`（读点在 62-64、Pi 剥链在 84-94）；对照 `src/L12_canonical/cxt.rs:316-334`（`subst_cxt` 包裹 src_names 类型与 env 槽）。
- 证据：
  ```rust
  // canonical.rs:62-64 —— src_names 的类型 v 与 env 槽值 vtm 原样取出，未 force
  let (l, (_, v)) = &cxt.src_names.get(t).unwrap();
  let vtm = cxt.env.iter().nth((cxt.lvl - l.0 - 1).0 as usize).unwrap().clone();
  ...
  // canonical.rs:84 —— 直接按形态匹配，VSub 包裹的 Pi 剥不开
  while let Val::Pi(span, icit, dom, clos) = vt.as_ref() { ... }
  ```
  移植后，match 臂内的上下文经 `subst_cxt` 包裹（`cxt.rs:160`：`Rc::new(Val::VSub(v.clone(), sub.clone()))`），`iddfs/search` 的 `cxt` 正是出错点的 elaboration 上下文（`elaboration.rs:379` `t_tm.no_metas(self, &cxt.decl, cxt.lvl)` → `elaboration.rs:432` `infer.iddfs(&meta_cxt, …)`）。
- 机制/影响：候选 `t` 的类型若被 σ 包裹（臂上下文里的源码变量），`while let Val::Pi` 剥链失败 → 候选被按 0 实参应用 → `unify`（入口有 force，`unification.rs:665-666`）与 `check::<true>` 大概率失配 → 该 quickfix 候选漏报。旧机制下 `refresh` 把类型**物化**进 src_names，剥链总能看到裸 Pi——此读点遗漏是移植引入的。影响限于 LSP quickfix 建议完备性（`canonical.rs:22-23` 注明 iddfs 仅 LSP 重试闭包触达，`run`/`run_fast` 不经此路径），`check::<true>` 在 origin_cxt 复检保证不产生错误建议——即"良构解被漏报"，非静默错误结果。`vtm`（值）经 `v_app` 消费，L12 的 `v_app` 有 VSub 臂（`mod.rs:882-887`），不受影响。
- 处置建议：在 `search` 取出 `v`/`vtm` 后各加一次 `self.force(&cxt.decl, …)`（或对 `vt` 剥链前 force），与 L09 `filter_accessible_constrs` 对同类读点的处理（`pattern_match.rs:196-208`）对齐。

### [P3] L10–L12 的 `unify_pm` fallback 不穿 spec，与 L09 分层分歧（影响面：L10/L11/L12）
- 位置：`src/L10_typeclass/elaboration.rs:194`（`(_, _) => self.unify_catch(cxt, &t, &t_prime, t_span)`）；L11 `elaboration.rs:196-` 同；L12 同形。对照 L09 `elaboration.rs:196-197`：`self.unify(cxt.lvl, cxt, u.clone(), v.clone(), Some(spec))`。
- 证据：L10–L12 的 `SpecSolve` 无 `solvable` 字段（`elaboration.rs:21-23`），`unify_catch` 内部走无 spec 的 `unify`；L09 的 `unify` 有 spec 臂（`unification.rs:596-623`，白名单= `bind_slots`）。
- 机制/影响：方程头形态落入 fallback（如 Pi/Lam 头、或 fallback 内层 Sum 参数里的嵌套 bare rigid）时，L09 还能继续累积特化解，L10–L12 不能——跨层语义分歧（各层 parity 各自锁定，无跨层 oracle 能暴露）。模式方程以 Sum/SumCase/rigid 头为主，实际触发面窄。
- 处置建议：记录即可；若追求六层机制统一，L10–L12 的 fallback 可改为带 spec 的 `unify`（需同步其 `SpecSolve` 的白名单口径）。

### [P3] L10–L12 的 `check_pm`/`check_pm_final` 无入口 refuel，偏离 L07/L08/L09 燃料纪律（影响面：L10/L11/L12）
- 位置：L09 `elaboration.rs:84/114`（`self.meta_refuel()` 在两条方程前）；L07/L08 `pattern_match.rs:87`（compile 入口 `infer.meta_refuel()`）；L10/L11/L12 的 `check_pm`/`check_pm_final`（L10 `elaboration.rs:78-100` 等）与 `pattern_match.rs` 均 grep 不到 refuel——refuel 只在 `nf`/`unify_catch`（L10 `mod.rs:942/952`）与 L12 的 CANONICAL 合一入口/canonical 探测（`elaboration.rs:327`、`canonical.rs:112`）。
- 证据：L10 `unify_pm` 入口 `self.force(t)` 会烧 fuel（`mod.rs:483` 的 Flex 解链臂），而 check_pm 进入该 force 时池子是上一次 `unify_catch` 剩余量。
- 机制/影响：极端情形（前一次重负载合一几乎耗尽池子）下，模式方程入口的 force 有界降级提前触发 → 假未解/假不可达。触发需要池子恰好在本层入口前被掏空，概率低；且 fallback `unify_catch` 会立即充值，暴露窗口只在第一方程的入口 force。属纪律偏离而非已证缺陷。
- 处置建议：`check_pm`/`check_pm_final` 入口补一次 `refuel()`，与 L07/L08/L09 对齐（一行级改动，Err/Ok 行为仅在耗尽边界可见）。

### [P3] 陈旧注释/README：以"改写式精化仍在用"的口吻描述已删除的机制（影响面：L09/L10/L11 文档）
- 位置与证据：
  - `src/L09_mltt/bump_spine_iter.rs:4137-4145`：以现在时表述"本层起改走参考版 `Cxt::update_cxt`——精化就地改写 env 槽再 refresh 重锚定"，作为不移植 bind-prefix 快路径的理由。移植后 `update_cxt`/`refresh` 已删除（`cxt.rs:153-155` 注释明言"替代旧"），该理由与现状脱节（现 env 槽是 VSub 包裹值，"改读快照会拿到精化后的值"的论证需要按显式替换口径重写）。
  - `src/L09_mltt/bump_spine_iter.rs:3868-3869`：`Names::by_lvl` 文档仍写"refresh 的 get_by_key2_mut 目标……refresh 更新即生效"，`refresh` 已不存在（现为 `subst_cxt` 包裹）。
  - README 燃料声明与代码相反：`src/L09_mltt/README.md:24`（"无 L07/L08 的 unify/force fuel"）↔ `L09_mltt/mod.rs:416`（`UNIFY_FUEL: u32 = 4096`）；`src/L10_typeclass/README.md:68-70`（"孪生 bump_spine_iter 无燃料池……lookup 命中不做有界降级"）↔ `L10_typeclass/bump_spine_iter.rs:933-946, 1149-1196`（dbe79cf 补齐的池子与燃烧点）；`src/L11_macro/README.md:27-29`（"参考版与快版一致无燃料"）↔ `L11_macro/mod.rs:451` 与孪生 `:959-972`。
- 机制/影响：不改变行为；但 L09 孪生 4137 那段是**决策依据级**注释，会误导后续移植/评审（包括本轮各维度 agent）。README 燃料条属 D6 主责，此处因与燃料口径核对直接相关仅登记。
- 处置建议：更新三处注释与三条 README 陈旧声明（L09 README 的"逐失控类论证"②在显式替换移植后需按"frcs lookup 燃烧点"重写——其 ② 的"grep 0 命中"依据已失效）。

## 3. needs-verify 清单（验证方法）

1. **L09 决策树叶子的 `check_pm_final(...).unwrap()`（`src/L09_mltt/pattern_match.rs:253`；孪生同点 `.expect("check_pm_final 失败（参考版 unwrap）")` `bump_spine_iter.rs:6083-6084`）的触达性**。第一方程失败即 panic（用户可触发崩溃 → 若可达则为 P1）。静态分析：探测 `filter_accessible_constrs`（逐构造子 + Hole 实例化）先过滤不可达分支，但探测方程与叶子的整臂原始模式方程**不是同一条方程**（子模式带类型的 Raw vs 全 Hole），怀疑存在"探测过、叶子败"的 GADT 负载。该 unwrap 为 pre-port 既有（`git show ccfcb87~1` 的同位 `:250`），非移植引入。验证方法：L09 黑盒风格构造依赖子模式/索引字面量的攻击负载（如 `case circle(zero)` 搭配带索引的 scrutinee 类型、模式位置放类型不匹配的子项），外加 `--release`/debug 双构建（lvl2ix 断言差异）。
2. **L10–L12 叶子 `check_pm_final` Err → `return Ok(false)`（`src/L10_typeclass/pattern_match.rs` 叶子臂）后，`reachable` 已标记而 `pats` 未推**：该臂若真被运行时选中，`eval_aux` 缺臂 → 无臂命中路径。与 #1 同根（探测/叶子判定分歧），且 L10–L12 与 L09 在同一点上行为分层不一致（panic vs 静默缺臂）。验证方法：同 #1 负载跑 L10–L12；并在 eval 无臂命中时确认其失败形态（None → unwrap panic 或卡住）。
3. **决策树"空 pats 臂在深层列被丢弃"的覆盖假阳性（pre-existing，非移植引入）**：`src/L09_mltt/pattern_match.rs:420-435`（`_ => if *icit == Icit::Impl {…} else {None}`）会把 pats 已耗尽的通配臂从更深列的分支里丢掉——`match s { case circle(zero) => a; case _ => z }` 类负载中 `circle(succ(…))` 疑似被误报 Unmatched（运行时语义本可由通配臂承接；`compile` 把 warnings 升级为 Err，即良构程序被拒）。我在推演 [needs-verify #3 关联]通配臂复用布局时确认了丢弃逻辑的存在，但未构造出完整可编译触发例（L09 语法细节未逐一验证）。验证方法：L09/L10 语法写出上述两臂 match + 全构造子调用，观察是否报 Unmatched。
4. **L09 的 `unify_pm` 对 `Rigid ≐ Flex` 静默 `Ok(())`（`src/L09_mltt/elaboration.rs:148-158` + `spec_refine:219-221`），不把 meta 解到 rigid 上**；L07/L08 同形态会落 Flex 规则 `solve`（把 `?m := T` 钉住，`unification.rs:740-741`）。影响面是诊断质量（洞不被钉住、后续可能被无关约束解走），静态推演未找到能导致 ill-typed 项被接受的路径（模式位置的 Hole 运行时按通配处理）。验证方法：`def f[T](x: T) = match x { case ?h => … }` 类负载对比 L07/L09 的 `?N` 解与错误文案。

## 4. 设计决定讨论（不属 bug，只记录）

1. **可解集三层口径并存**：L07/L08 = bind-slot 白名单（`unification.rs:682` `s.solvable.contains(x)`）；L09 = 混合（`unify_pm` 自有臂接受任意 `x < cxt.lvl` 的裸 rigid（`elaboration.rs:148-158` + `spec_refine:222-224`），仅 fallback 的 `unify` 臂查白名单）；L10–L12 = 任意裸 rigid、无白名单（L10 README"定制(a)"明文，`SpecSolve` 无 `solvable` 字段）。三者均与各自旧机制（`pm_solve` vs `update_cxt`）的语义连续，移植计划"保留本层既有编译策略"可覆盖；若未来追求六层统一，这是最大的一处机制分叉。
2. **occurs 守卫的 Flex 口径**：L07/L08 扫 Flex spine、L09–L12 不透明（L09 `mod.rs:328-334` 附"meta 应用到变量是合法形"的论证）。两侧各有 fuel 兜底，均为有界降级而非静默错解；记录为分层取舍。
3. **`check_pm_final` 第二方程的两种等价形态**：L09 在**未改写** env 下求值 `ori_v`、由方程入口置于 acc 之下（惰性，`elaboration.rs:95-107`）；L10–L12 先 `subst_cxt` 出 `cxt2` 再求值（物化，L10/L11 `elaboration.rs` 同位）。语义等价（σ 推开时机不同），错误容忍（`let _ =` / `is_ok()`）一致。
4. **`unify_pm` 名字沿用**：移植计划要求删除 `unify_pm`，L09–L12 实际是"删除其上下文改写语义、保留函数名承载特化合一"。机制层面已对齐蓝本（解入 acc、入口 wrap、occurs、Flex 不精化），但**函数名+双轨形状**（自有臂 + fallback）与 L07"合一器只有一个"的纪律（README §1.2 纪律三、§6 第 2 行把"unify/unify_pm 双轨"列为旧问题）形成字面回退——语义上 L09 的 fallback 穿 spec、L10–L12 的 fallback 是失配兜底，不是旧双轨的复活，但命名易误导（见 [P3-1]）。
5. **`Infer.global` 的两义性**：L09–L12 的 `Infer.global` 是全局定义表（`Tm::Var(x>=1919810)` 哨兵的名字解析，A4-R2 登记的架构），与旧 L09 精化机制清单里的同名设施无关（pre-port 即如此，`git show ccfcb87~1` 证实）。BRIEF"删除清单"中 `Infer.global` 一项对 L09–L12 应理解为"删除其精化职责"——现无精化职责，保留正确。
6. **frcs 对"已解 rigid + 非空 spine"的解析应用**（设计 §9 注记 5，旧机制卡住的有意行为差异）：六层参考版（L07 `mod.rs:616-634` 带 `v_applicable` 守卫、L09 `mod.rs:480-498`、L10–L12 同）与孪生版（L07 孪生 `bump_spine_iter.rs:1730-1762` 带 `vapp_ok` 守卫）均已复刻，守卫集合随各层 `v_app` 的 panic 面收缩（L09 的 `v_applicable` 不含 Match——与其 `v_app` 对 Match panic 的时代缺口一致，`mod.rs:288-296`），口径自洽。
7. **燃料燃烧剖面**：L07/L08 = force 展开臂 + unify 递归入口 + frcs lookup 命中三处烧；L09 = 仅 frcs lookup（其 force Flex 解链无环有逐 meta occurs 论证，L09 README 时代缺口①，spec/`val_mentions_lvl` 为本回合新增代码）；L10–L12 = force Flex + unify 入口 + frcs lookup。六层"入口不烧、lookup 命中烧 1、耗尽回裸 rigid"的核心剖面一致；差异仅在 force Flex/unify 递归是否计费，均有各自的失控面论证。L10–L12 的入口充值缺口见 [P3-2]。

---

**verdict 摘要：P0: 0 P1: 0 P2: 1 P3: 4 needs-verify: 4**
