# D4 parity 与孪生/跨模块分叉 — L07–L12 只读评审

## 1. 结论（verdict）

- **P0: 0  P1: 0  P2: 2  P3: 3  needs-verify: 2**
- 覆盖范围与方法：
  - **层内 ref↔twin**：精读 L07 蓝本全部机制函数（`mod.rs` 的 `Subst`/`force`/`frcs`/`wrap_sp`/`frcs_env`/`quote`/`unify` 入口与 `SpecSolve` 穿参，`unification.rs` 特化臂，`pattern_match.rs` σ 线程；`bump_spine_iter.rs` 的 `SubstV`/`force`/`frcs`/`unify_iter`/`quote_iter`/`vapp1`/`vapp_ok`/`mentions_level`/`val_mentions_lvl`/燃料池），再按同名函数逐点核对其余五层的 ref 与 twin 对应物（`grep -n` 定位 + 函数级 `diff`）。
  - **跨层 diff 分类**：六层同名文件两两 `diff` 并统计变更行数；对 L07↔L08（近逐字拷贝对）全 hunk 逐一分类；对 `bump_spine_iter.rs` 做**注释剥离后**再 diff（663/2691/865 行代码级差异逐块归类）；`Subst` 块与 `frcs` 块按函数区间提取后 diff。
  - **修一份漏其他份**：`git log --since=2026-06-15` 逐层列出近 3 个月改动文件，对 `bbcf214`/`a5eb72b`/`7cfbb8e`/`295ea69`/`dbe79cf`/`5fc88c8` 等修复/移植提交逐项核对六层同步状态。
  - 读测试判据（`tests/l07~l12_fast_parity.rs` 的归一化口径）与三份必读文档（design doc §4/§9、l08-l13-refactor-plan、explicit-subst-refactor-status §3/§5）。
  - 未运行 cargo（遵守 BRIEF）。

### 机制点六层对照表（L07 蓝本 → 移植核对）

| 机制点 | L07 | L08 | L09 | L10 | L11 | L12 | 判定 |
|---|---|---|---|---|---|---|---|
| `Subst` 持久化单链、`extend` O(1) cons（右偏 union，链头=最新） | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | 六层 ref+twin 逐点同构（如 `L07 mod.rs:294` ↔ `L12 bump:436`） |
| `compose` 外层条目接链头（O(|σ|) cons_all，键冲突外层覆盖） | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | 合法同构 |
| `lookup_hit` 条件包裹（`mentions_level` 浅扫，解值不引用已解层级则零分配直通） | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | 扫描面随层特性裁剪（L09 无 Prim/Decl、L12 增 Match origin 槽），宁宽勿窄口径一致 |
| `VSub` 包裹点（`wrap_sub`，σ 空零开销） | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | 合法 |
| `frcs` 槽位纪律（spine/Sum/SumCase 只包裹不物化、闭包 env 逐槽包裹、Match scrutinee 推进） | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | L09 的 Match 重选不在 frcs（eval 的 `Tm::Match` 臂做，README 已记载）；L10–L12 在 frcs 内重选并烧 1——与各层 ref 一致 |
| frcs 解析应用（已解 rigid + 非空 spine，`v_applicable`/`vapp_ok` 守卫） | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | 守卫判定存在 **F1 所列 λ 分叉**（见发现列表） |
| 燃烧剖面（VSub 入口不烧、lookup 命中烧 1、耗尽返回裸 rigid） | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | L07/L08 的 force Match 重选臂与 L10–L12 的 frcs Match 重选臂各多烧 1——与各层 ref 逐点对齐 |
| 燃料池常量 4096 | `mod.rs:430` | `mod.rs` 同 | `mod.rs` 同 | twin `PM_FUEL` | twin `PM_FUEL` | twin `PM_FUEL` | ref=Infer 字段、L07/L08 twin=函数参数 `Fuel`、L09–L12 twin=`thread_local PM_FUEL`——实现位置不同、常量与充值/燃烧点一致 |
| `SpecSolve` 穿参 | unify 全递归臂 + 白名单 | 同 L07 | unify 全递归臂 + 白名单；**unify_pm 内 `spec_refine` 仅界守卫** | 仅 `unify_pm`，无白名单 | 同 L10 | 同 L10 | 与 status doc §3 登记口径基本一致，唯 L09 的登记面不全（F5） |
| `subst_cxt`（env+types+src_names/names.by_lvl 包裹，lvl/locals/pruning 不动） | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | 六层 twin 均同步 by_lvl 影子索引（status doc §5.4 要求） |
| `force_arg` 逐层解包 VSub | ✓ `mod.rs:487` | ✓ `:496` | ✓ `:577` | ✓ `:665` | ✓ `:718` | ✓ `:852` | 合法 |
| occurs 守卫 `val_mentions_lvl`（VSub 只扫内层、不扫 σ 映射值） | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | 合法 |
| quote 的 VSub 防御臂 | 打印内层 | 打印内层 | 打印内层 | **U(0)+debug_assert** | **U(0)+debug_assert** | 打印内层 | **F2 所列疑似漏项**（见发现列表） |
| `(fuel exhausted)` 尾注 | ✓ ref+twin | ✓ ref+twin | ✗ | ✗ | ✗ | ✗ | **F3**（架构差异下的诊断能力回退） |

## 2. 发现列表

### [P2] F1 孪生 `vapp_ok` 把 λ（tag 1）判为可应用，参考版 `v_applicable` 对 `Lam` 判否 —— frcs 解析应用守卫语义分叉（影响面：全部六层）

- 位置（两侧）：
  - ref：`src/L07_sum_type/mod.rs:333-344`（`v_applicable` 的 `matches!` 列表为 `Flex|Rigid|Decl|Obj|Prim|Match|VSub`，**不含 `Val::Lam`**）；frcs 守卫读点 `mod.rs:626`。各层同码：`L08 mod.rs:342,635`、`L09 mod.rs:291,490`、`L10 mod.rs:299,529`、`L11 mod.rs:340,572`、`L12 mod.rs:398,697`。
  - twin：`src/L07_sum_type/bump_spine_iter.rs:1232-1241`（`vapp_ok` 的 `match v_tag(v) { 3|4|6 => false, 7 => ..., _ => true }` —— **tag 1（λ 闭包）落入 `_ => true`**）；frcs 守卫读点 `bump:1751`。各层同码：`L08 bump:1232,1754`、`L09 bump:973,1179`、`L10 bump:924,1204`、`L11 bump:947,1238`、`L12 bump:994,1285`。
- 证据（diff 形态对照）：

  ```rust
  // ref  L07 mod.rs:333（Lam 不在列表 => false）
  pub(crate) fn v_applicable(v: &Val) -> bool {
      matches!(v, Val::Flex(..) | Val::Rigid(..) | Val::Decl(..) | Val::Obj(..)
                 | Val::Prim(..) | Val::Match(..) | Val::VSub(..))
  }
  // twin L07 bump:1232（tag 1 = Clo(λ) 落 _ => true）
  fn vapp_ok(v: V) -> bool {
      match v_tag(v) { 3 | 4 | 6 => false, 7 => !matches!(...), _ => true }
  }
  ```

- 机制/影响：frcs 的解析应用臂中 `head = force(σ.lookup_hit(x))`——`force` 对 λ 值原样返回（twin force 的 `_ => return v`），故当 **σ 中存在 λ 形态的解**（ref 特化臂 `(Rigid x, v)` 的 `v` 允许任意非 Flex 值，`unification.rs:678-705`，含 `Lam`）且该层级的读点带非空 spine 时：ref 判不可应用 → 卡回裸 `Rigid(x, sp)`；twin 判可应用 → `vapp1` β-归约。两个 oracle 在该输入类上**可观测输出不同**（`?0 a` 卡住 vs 归约到 λ 体），属于潜在 parity 裂缝。η 臂的 `vapp_ok` 调用点（`bump:3342/3360` 等）只在另一侧为 λ 时才询问，tag 1 分支在该处不可达，不受影响；分叉仅在 frcs 读点成立。当前六层 parity 全绿，说明现有语料未覆盖该输入类。twin 侧注释（`bump:1224-1230`）自称"与参考版守卫同判"，与实际不符。
- 判定：**疑似漏项/分叉**（ref 的 `Lam` 排除可能是有意保守，twin 未复刻；或 twin 的 β 更完备而 ref 漏放——无论哪边是"对"，两版必须一致）。
- 处置建议：二选一对齐（建议都放行 λ——λ 是函数，`v_app`/`vapp1` 均不会 panic，ref 现口径把良型 β-红ex卡住反而更不完备），并补一条"λ 解 + 非空 spine"parity 用例钉死。

### [P2] F2 L10/L11 参考版 quote 的 VSub 防御臂未同步 bbcf214 修复：`debug_assert!(false)` + 降级 `U(0)`，且与自家孪生相反（影响面：L10/L11）

- 位置（两侧）：
  - ref：`src/L10_typeclass/mod.rs:859-864`、`src/L11_macro/mod.rs:903-908`：

    ```rust
    // 不变式：force 的返回值顶层不会是 VSub（防御臂；fuel 耗尽时
    // frcs 的降级会留裸 rigid 而非 VSub，故此臂仅在极端角落可达）
    Val::VSub(..) => {
        debug_assert!(false, "quote: VSub survived force");
        Tm::U(0).into()
    }
    ```

  - twin：`src/L10_typeclass/bump_spine_iter.rs:2036-2041`、`src/L11_macro/bump_spine_iter.rs:2149-2155`：`XCell::VSub { val, .. } => tasks.push(QJob::Q(*val, level))`，注释为"防御臂**解包打印内层**（**参考版 quote 的 VSub 臂同款**，链式 VSub 由递归消化）"。
  - 蓝本对照：`L07 mod.rs:1129-1135`、`L08 mod.rs:1144`、`L09 mod.rs:775-777`、`L12 mod.rs:1138-1141` 均为 `Val::VSub(v, _) => self.quote(decl, l, *v)`；源头是 `bbcf214`（"quote 的 VSub 防御臂改为解包打印内层（fuel 耗尽时不再降级成 U）"）。
- 机制/影响：L07 轮 1 评审的修复 `bbcf214` 在 L10/L11 移植时被漏掉（L08/L09/L12 均带修复，L10 `ad412ab`、L11 `2129975` 用的是修复前的形状）——典型"修了一份没修其他份"。后果分两级：
  1. **若该臂可达**（L07 侧注释 `mod.rs:1132` 断言"fuel 耗尽时 force 原样返回 VSub"，且 `bbcf214` 据此修）：L10/L11 参考版在 **debug 构建 panic**（`debug_assert!`），release 打印 `U(0)` 垃圾节点；而同层孪生打印内层 → 层内 parity 裂缝 + 可达 panic（P1 级）。
  2. **若该臂不可达**（L10/L11 注释自称"本层无燃料降级例外……仅在极端角落可达"）：则只是死臂分叉 + twin 注释失实（"参考版同款"为假）。注意 L07 与 L10/L11 的注释互相矛盾，二者必有一处不实。
- 判定：**疑似漏项**（跨层修复未同步），可达性待证（见 needs-verify）。
- 处置建议：把 L10/L11 ref 的该臂改为与 L07/L08/L09/L12 及其孪生一致的"解包打印内层"，顺带订正 twin 注释或 ref 注释中关于可达性的错误断言。

### [P3] F3 `"(fuel exhausted)"` 诊断尾注只移植到 L08；L09–L12 的"假不可达"无任何燃料标记（影响面：L09–L12）

- 位置：`src/L07_sum_type/mod.rs:1230-1234`、`src/L07_sum_type/pattern_match.rs:269-277`（`分支不可达 (fuel exhausted)`）；`src/L08_product_type/mod.rs:1239`、`src/L08_product_type/pattern_match.rs:272`（同款）。L09–L12 全部 `pattern_match.rs`/`elaboration.rs` 中 `fuel exhausted` 0 命中；L10–L12 的 unify_pm 方程失败文案为**空串** `Error(t_span.map(|_| "".to_string()))`（`src/L10_typeclass/elaboration.rs:158-165`，L11/L12 同码），不可达走 `Warning::Unreachable`（`src/L10_typeclass/pattern_match.rs:575-588`）。
- 机制/影响：`a5eb72b` 修复的 P1（燃料耗尽被误报"分支不可达"、无法与结构冲突区分）在 L09–L12 的对应面（Warning/空串 Err）上没有诊断改进。行为限制本身已被 status doc §5.2 登记（"fuel 是有界降级……仍可能假 absurd"），故不算 bug；但同一改进在 L07/L08 与 L09–L12 间的诊断能力不一致属跨层漂移。
- 判定：合法差异（架构不同：决策树 Warning 体系 vs L07/L08 逐臂错误文案）+ 需登记的漂移。
- 处置建议：在 L09–L12 的 `Warning::Unreachable` 生成处（或 unify_pm occurs-Err 消费点）补燃料水位判断，或至少在 README 已知限制中写明该层无燃料诊断。

### [P3] F4 设计文档 §9.5 要求"各层移植必须复刻"的两个钉死测试仅存在于 L07（影响面：L08–L12）

- 位置：`src/L07_sum_type/tests.rs:1454`（`test_fn_typed_index_slot_applied_after_refine`，钉死 frcs 解析应用）、`src/L07_sum_type/tests.rs:1478-1485`（`test_deep_pattern_fuel_budget_regression`，d=400 燃料预算边界，`a5eb72b` 新增）。`grep` 全仓：L08–L12 无同名/同型测试（L09–L12 无 `tests.rs`；L08 `tests.rs` 45 个用例无 slot-applied/fuel-budget 对应物；`tests/l08~l12_fast_parity.rs` 中亦无 `400`/深嵌套预算用例）。
- 机制/影响：`docs/l07-dpm-refactor-design.md` §9.5 明文"frcs 对'已解 rigid+非空 spine'做解析应用……各层移植必须复刻（测试钉死）"；`a5eb72b` 的 d=400 回归是燃烧剖面回归的唯一哨兵。现在只有 L07 有哨兵：若后续层改动脉冲剖面（如 F1 的对齐改动），其余五层不会被测试捕获。
- 判定：疑似漏项（测试侧的"修一份没修其他份"；细节归 D6，此处按跨层同步登记）。
- 处置建议：L08 至少补同型单测；L09–L12 在 parity 语料中加"已解 rigid 带非空 spine"与深嵌套 d≈400 两类程序。

### [P3] F5 文档/注释登记面不全（影响面：文档准确性，兼交 D6）

- 位置与证据：
  - status doc `docs/explicit-subst-refactor-status.md` §3 只登记"L10/L11/L12 的 `unify_pm` 无 `solvable` 白名单"；实际 **L09 的 `unify_pm`/`spec_refine` 也无白名单**（`src/L09_mltt/elaboration.rs:212-230`，仅 `x.0 >= cxt.lvl.0 => Ok(())` 界守卫），而 L09 的 `unify` 特化臂有白名单（`src/L09_mltt/unification.rs:594-624` `s.solvable.contains(x)`）——L09 内部两套特化入口口径不一，且与 L10–L12（连界守卫都没有，`src/L10_typeclass/elaboration.rs:149-163`）细节不同，文档未记载。
  - L07 孪生对 eval 序"先函数后实参"的文档化偏差有完整注释（`src/L07_sum_type/bump_spine_iter.rs` 原 hunk，"仅当两侧都有 eval 期副作用时可观测"），L08 孪生同码但注释被删剩一行（`L08 bump` 对应位置仅"复合函数头：通用三推"）——可观测条件说明只在 L07 保留。
- 判定：文档漂移（非行为问题）。
- 处置建议：status doc §3 的 P2 登记补上 L09；L08 孪生回填偏差注释。

## 3. needs-verify 清单（验证方法）

1. **F1 的触发可达性**：构造"σ 中存在 λ 值解 + 被解层级带非空 spine 读点"的程序（思路：索引/参数类型为函数类型的和类型，模式位置放具体 λ，使特化方程解出 `x := λz.…`；再在分支体里以实参引用 x 的 spine 槽）。分别跑同层 `run` 与 `run_fast` 比对输出：ref 卡住（`Var` 形态）而 twin 归约（λ 体）即证实 P1 级 parity 裂缝；全部语料不可达则降级 P3 死码分叉。
2. **F2 的 force-顶层 VSub 可达性**：在 debug 构建下用 L07 的 d=400 深嵌套语料（`tests.rs:1478` 思路移植）跑 L10/L11 参考版——`debug_assert` 触发即证实"可达 panic + parity 裂缝"（升 P1）；不触发则需静态论证 L07 注释"fuel 耗尽时 force 原样返回 VSub"的路径在 L10/L11 是否被层特性关闭，并据实修订两处注释。
3. （低优先）L07 孪生 `mentions_level` 的 tag 2 链头 `head_hit` 只认裸 rigid(tag 0)与 Obj/VSub(tag 7) 头，链中再嵌链（头为 tag 2）时 head_hit=false——若 packed 表示可能出现"链头仍是链"的形态，会相对 ref 的 `Rigid(y,sp)` 头扫描欠近似。验证方法：在 twin 侧断言 `spine.spine_head(h)` 的 tag ≠ 2 遍历全部 parity 语料；当前五方样板（先 push 头再收实参）下推不出该形态，判定为不可达，仅登记。

## 4. 设计决定讨论（不属 bug，只记录）

以下分叉均已核对为**合法差异**（有测试锁定或文档记载），供后续评审引用：

| 分叉 | 证据 | 依据 |
|---|---|---|
| L07↔L08 近逐字拷贝对全部 diff 为层特性 | `pattern_match.rs`/`struct_eq.rs`/`syntax.rs` 0 行差；`cxt.rs` 仅 import 序；`unification.rs` 38 行 = L08 新增 `(Obj,Obj)` 合同臂（`unification.rs:772-780`，注释自证"L07 潜伏缺口，剥链使其可达"）；`lex.rs`/`parser`/`pretty`/`elaboration`/`mod.rs` 差异全部为 struct/new 脱糖、多段投影链与文案 | 层特性 |
| L08 孪生 `intersect_bump` 不再把"Obj 头位相等链"排除出位相等捷径 | `L07 bump:2961-2964` 有 `hk==HK_OBJ` 排除、`L08 bump:2972` 无 | 与 L08 ref 新增 `(Obj,Obj)` 臂配套（Obj/Obj 在 L08 可成功），各层与各自 ref 一致 |
| L08 孪生 `(Match,Match)` 改 `MatchStruct` 屏障项（模式相等检查从"前置全查"改为"逐分支前查"） | `L08 bump:2891/3201` | 层内重构，语义合取等价；parity 锁定 |
| L09 ref/twin 的 force 无 Match 重选臂，重选在 eval 的 `Tm::Match` 臂 | `L09 mod.rs` frcs 注释、`L09 README` ①-⑥ 差异清单 | README 记载 |
| L10–L12 特化限 `unify_pm`（spec 不穿入常规 unify），且无白名单 | `L10 elaboration.rs:115-127` 注释、status doc §3 | 已登记的刻意分歧（L09 白名单面见 F5） |
| L07/L08 twin 燃料为函数参数 `Fuel`，L09–L12 twin 为 `thread_local PM_FUEL` | `L07 bump:843-855` vs `L10 bump:936-955` | 实现位置差异，常量/燃烧点一致（dbe79cf 照 L09 模板补齐） |
| L09 孪生平坦 defs env 不做 Pi env 链式包裹；occurs 对 Flex 不透明 | status doc §3 P2 | 已登记 |
| `?N`/Span 归一化偏差、低层 `?0` 洞显示、宽松臂"后注册者覆盖" | `tests/lXX_fast_parity.rs` 归一化函数、BRIEF §0 | 测试锁定 |
| L11/L12 孪生 `vapp1` 的 VSub 预检位置不同（L11 函数入口前置、L12 在 tag-7 臂内） | `L11 bump:917-923` vs `L12 bump:972-984` | 纯顺序 cosmetic，语义同 |

**诚实声明**：除上列 F1–F5 外，未发现其它"修一份漏其他份"或移植变形；L07 蓝本的机制点（单链 σ、右偏 extend、O(|σ|) compose、VSub 包裹点、frcs 燃烧口径、SpecSolve 穿参、浅 occurs 守卫、subst_cxt 槽位纪律、force_arg 逐层解包）在 L08–L12 的 ref 与 twin 中均有完整对应物（见 §1 对照表）。两层 P2 均为"未覆盖输入类上的分叉/漏移植"，当前 66 个 parity 目标全绿与其不矛盾。

---
verdict 摘要：P0:0 P1:0 P2:2 P3:3 needs-verify:2
