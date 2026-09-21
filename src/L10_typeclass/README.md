# L10：trait / typeclass 实例求解

本层在 L09 之上加 trait/typeclass：`trait` / `impl` 声明、接收者方法调用
（`x.foo y` 的脱糖）、`outParam`、实例表 Prolog 求解。参考版是分文件实现
（`mod.rs` + `elaboration.rs` / `unification.rs` / `pattern_match.rs` /
`typeclass.rs` / `cxt.rs`）；性能孪生 `bump_spine_iter.rs`（L09 冠军配方
`bump_spine_iter` 向本层的移植）。实例求解器 `typeclass.rs::Synth` 为
**参考版与孪生共用**；其余参考版 / 孪生各一份，语义以参考版为准，
`tests/l10_fast_parity.rs` 以「Ok 逐字节 / Err 判定一致」为闸门。

本 README 主线是 2026-09-18 前后的匹配编译器三连改造（参考版 + 孪生同步
落地）：决策树矩阵 → **逐臂下钻**（`4e97743`）、覆盖探测从推断级改
**值级结构探测**（`e2560a4`）、评审修复轮恢复**嵌套覆盖检查**（`aafa5ed`）。
实例匹配的单向一阶化（`match_typ`，d4c05ea）与精化载体的显式替换移植
（`ad412ab`，L07 重构回合同批）是更早的两轮，分别见 §1.3 与 §4。

---

## 1. 语言特性（trait / typeclass）

### 1.1 trait 声明 = `is_trait` 的 enum

`trait` 声明脱糖为 enum（`Val::Sum`/`Tm::Sum` 带 `is_trait` 标记，构造子
即实例），另在 Infer 的两张伴生表里维护：`trait_definition`（trait 名 →
参数表 + out 掩码 + 方法表）与 `trait_out_param`（elaboration.rs:624-633，
`TraitDecl` 臂）。`impl` 声明（`ImplDecl` 臂，elaboration.rs:535）把方法
登记为实例：`Synth::impl_trait_for` 挂进 `class_instances`（typeclass.rs:168），
支持泛型参数（`impl[T] List[T] { … }`）与毛毯实例（`impl[T] Say for T`）。

期望类型是 trait Sum 时，`fresh_meta` 不做 pruning 应用、直接放一个
**待解 meta**（mod.rs:500-505）——实例合成被推迟到 def 体检查完后的
`solve_multi_trait`（elaboration.rs:367；unification.rs:451 逐个扫未解
meta 调 `solve_trait`）。`solve_trait`（unification.rs:468）是 Val 世界与
`Typ` 世界的桥：头是 trait Sum 时按 out 掩码滤掉 out 位实参、经
`force_deep().to_typ()` 转成 `Assertion` 交给 `Synth`，命中后把实例名
`infer_expr` 回 Val 世界，并把实例的 typ 与期望 trait Sum 合一。

### 1.2 接收者方法调用（trait_wrap）

`x.foo y` 的脱糖在 `trait_wrap`（elaboration.rs:1003）：扫全部 trait 的
方法表找同名方法，对每个候选以 `(接收者类型, Any×out位数)` 构造断言让
`Synth` 试解（试解失败的方法不产生候选），命中后拼一个 `Let` 包裹的
"实例参数应用"项（`$this`/`$$` 合成参数 + 方法 β 应用）交给常规推断。
找不到可解候选（或接收者类型 `to_typ` 失败）报 `has no object`。

### 1.3 实例匹配与 outParam

- 实例匹配是**单向一阶匹配** `match_typ`（typeclass.rs:398）：只有
  **pattern 侧**（实例断言）的 `Typ::Var` 允许被绑定，goal 侧的泛型
  rigid 不得被实例构造子"吃掉"。旧实现是双向绑定且无 occurs check，会让
  `impl[T] Say for List[T]` 假匹配泛型目标（`f two` 错答 "list"）；
  d4c05ea 改单向，与 L12/L13 的 `val_match` 同族。
- `outParam`：trait 参数可标 `outParam(Type 0)`（如
  `trait Add[T, O: outParam(Type 0)]`），对应 `trait_out_param` 的布尔
  掩码。**out 位不参与实例查找**：求解断言里 out 位填 `Typ::Any` 通配
  （`match_typ` 的 Any 臂恒真，typeclass.rs:413），`solve_trait` 侧同样
  先滤掉 out 位（unification.rs:483-489）。
- `Val::to_typ` 的 Sum 参数槽对不可作类型的值（未解 meta）**刻意剔除**
  （typeclass.rs:45-58 注释论证，勿"修"成整体 None）：实例登记侧对
  `to_typ()==None` 的实参直接 Err，实例断言永不含被剔形态；trait_wrap
  接收者路径**依赖**该剔除（`x: List[?m]` 接收者类型化为
  `Construct("List",[])` 与 pattern 一阶匹配成功）——改成整体 None 会让
  这类合法程序从 Ok 变 Err。快版 `val_to_typ` 的 filter_map 同款语义。
- `to_typ` 对 `LiteralType`/`LiteralIntro`/`Prim` 返回 None（typeclass.rs:33-35；
  旧实现 `todo!()` 可被 `"s".foo` 触发崩溃，b7b4225 修，快版恒 None 同语义）。

### 1.4 求解器的护栏与缺陷（诚实清单）

`Synth`（typeclass.rs:138）是表驱动 Prolog：`generator_stack`（逐实例
DFS）× `consumer_stack`（子目标消费）× `assertion_table`（子目标 →
waiters/answers，**顺带是答案缓存**——重复子目标直接取已有答案，
`consume`，typeclass.rs:310-354）。两条硬边界：

- **effort ≤ 1000**（`synth` 主循环，typeclass.rs:219-224）：超限
  `panic!("Too much effort :(")`——是**崩溃**不是类型错误。这是实例搜索
  这一本层自有失控类的护栏（L09 README 时代缺口第 2 条的 L10 部分），
  但护栏本身的失败形态是 panic，属已知缺陷面。
- `new_subgoal` 每个子目标克隆整份实例表（typeclass.rs:299 `.clone()`），
  `trait_wrap` 每次调用克隆整个 `trait_definition`（elaboration.rs:1008，
  源码内 `//TODO: can remove this clone?` 自证）——traitchain 负载参考版
  慢的候选因素（见 §6.1，未做剖析核实）。

### 1.5 跨层连贯性（A4 评审登记）

- **继承自 L09 的时代缺口（与 L09 相同，不修）**：无 builtin 注册表 /
  可变全局 / 文件 IO；无 `struct_eq`；卡住 match 不可再应用（η 臂已加
  `v_applicable`/`vapp_ok` 守卫改判 Err，unification.rs:651）。unify/force
  **有** fuel（L08 护栏，本层参考版 `UNIFY_FUEL=4096`，mod.rs:448——早先
  README 登记的"无 fuel"已过时）。
- **L10 相对 L09 的恢复项**：`unify` 补 `(Obj, Obj)` 合同臂（L08 血统）。
- **显示形态（A4-R3 定案）**：SumCase 打印为 L09-L13 的 **comma 血统**
  （`头名::分支名(实参, …)`；锚点见 `src/L09_mltt/README.md` 显示形态条
  与 `src/L13_namespace/legacy_tests.rs:604`）。卡住 match 显示保留
  `(unsolved match …)` 简形（同 L09，刻意分歧，l10 golden 锚定）。
- 构造子只以**裸名**登记（无 L07 的 `Enum.case` 限定名别名）；
  **重定义静默覆盖**（参考版无 L07/L11 的 `redefine` 检查）。

## 2. 全局名字：`Infer.global` 按层级存

L10 **没有 decl 表**（这是它与 L11/L12 匹配编译器适配点不同的根源，
见 §3.2）：def/enum/构造子按**层级**登记在
`Infer.global: HashMap<Lvl, Rc<VTy>>`（mod.rs:453），项层引用是
`Tm::Var(Ix(global_idx + 1919810))`——越过哨兵 `1919810` 的下标查 global
表（eval 的 Var 臂，mod.rs:786；`lvl2ix` 的边界必须是 `>=`，mod.rs:411-421
有反例注释），quote/rename 对越过哨兵的 Rigid 原样产出大下标 Var。

- **递归 def** = `fake_bind`（把名字占进 src_names）+ 检查前 global 表放
  `VVar(自身大层级)` 占位、检查后覆盖真值（孪生模块注释同款表述）；
- **Match 分支体的往返**：quote/rename 的 Match 臂把 global 表整体换成
  中性视图（`Rigid(层级 + 1919810)`，mod.rs:959-975 的 `avoid_recursive`）
  再重求值分支体——避免递归调用在 quote 往返中被重展开。53e8adb 探针
  实测 L10 全部 7 个负载该路径 0 次命中，不值得优化；
- **builtin 只有 `string_concat`**：λ 链体是无名的 `Tm::Prim`，求值读
  env 前两槽（全字面量则拼接，否则卡 `Val::Prim`——不带 spine）。

## 3. 模式匹配的编译（pattern_match.rs）

### 3.1 决策树矩阵为什么被换掉

L09–L13 参考版与孪生都用**决策树矩阵**编译 match，L07/L08 用逐臂下钻；
`docs/bench-matrix-2026-09-17.md` 的 match 行显示前四层孪生反而慢于自己的
参考版（L10 首测 0.8×）。诊断（`docs/l09l13-match-compiler-analysis-
2026-09-17.md`）把差距全部定位到**编译期**：L11 孪生探针显示单次 run
360 次决策树节点访问、`filter_accessible_constrs`（逐 (构造子 × 臂) 的
重复探测 + 逐节点上下文克隆）占 elab 34%；只做常数优化拿不到量级，
遂按 L07 口径整体重写（受控实验见 `docs/pmab-per-arm-vs-decision-tree.md`）。

L10 的适配点（`4e97743` 提交信息）：参考版 `Cxt` 无 decl 表（§2）、孪生
机器是"env 口径"（force/eval 不带 cxt 参数，与 L11/L12 的 Cxt 口径不同）、
`Error` 单参、`XCell::Sum { params, cases, is_trait }`。实测（l10bench
同窗口交错取 min，k=11）：参考版 basic 0.750→0.252 ms（3.0×）、孪生
fast_ss 0.946→0.186 ms（5.1×）；其余负载无回归；`match` 负载的孪生/参考
由 0.8×（落后）转 1.28×（领先，矩阵口径）。

### 3.2 逐臂下钻的结构

`Compiler::compile`（pattern_match.rs:182）对每个臂独立下钻（保持用户
书写顺序 = 运行时首匹配）：

1. **走查** `walk_pat`（pattern_match.rs:394，L07 `walk_con` 口径）：绑定
   模式变量槽并构建运行时 `PatternDetail`。槽位纪律：枚举隐式参数不占槽
   （用头部 Sum 的实参值实例化 Π 链）、构造子隐式绑定器补虚通配（`[p]`
   隐式子模式支持）、变量模式以用户名绑槽、**Con 本身不占槽**。构造子
   类型经 `infer_expr(Raw::Var(名))` 取——与树头部展开同一次名字查找
   （§2 无 decl 表的后果）；
2. **特化方程**：`check_pm_final` 对 raw 重推断解 meta 方程；走查返回的
   槽位刚性（各层 Con 的走查返回类型）以 σ 作种子补解入
   （pattern_match.rs:246-273）——L10 的臂特化走 raw 侧 meta 间接，走查
   槽位不在其解里，须由显式方程链接（`aafa5ed` 的关键适配）；
3. **臂上下文** `subst_cxt`（σ 包裹 env 槽与类型包，槽位布局不动）→
   期望类型 quote→eval **重锚** → 体检查（spec 不穿参）。

### 3.3 覆盖探测：推断级 → 值级结构探测（`e2560a4`）

逐臂重写后，覆盖探测成了 match 编译的唯一热点。旧
`filter_accessible_constrs` 是**推断级**的：每个构造子拼一个带洞的 Raw，
逐层 `infer_expr` + quote + bind_name（孪生还 clone_cxt），整体套
`run_pure_probe` 快照回滚。新 `probe_accessible`（pattern_match.rs:88-146）
是**值级**的，L07 口径：

- 构造子类型走 `cxt.src_names` 的 名字 → (层级, 类型值) 表——与
  `infer_expr(Var)` 的 Var 臂同一次查找，不再走整条推断（孪生侧抽
  `Machine::resolve_name` 供 Var 臂与探测共用，防两处解析漂移）；
- Π 链上枚举隐式参数用头部 Sum 的实参实例化（不产槽），其余绑定器用
  超出上下文的 **scratch 层** fresh rigid；返回 Sum 与头部 Sum 参数逐槽
  `unify_pm`（`unify_indices`，头部一侧在前，解只进探测私有 σ，弃掉即
  回滚）；只快照/回滚 meta 表（孪生 = metas/unsolved 两表同换）；
- **每个探测独立充值** fuel（pattern_match.rs:114，多构造子枚举的逐 ctor
  探测不互相挤占）；索引方程失败时用 `fuel_exhausted` 区分"结构冲突"与
  "预算耗尽"——后者**按可达处理**（保守要求覆盖），否则深负载下的非穷尽
  match 会被静默接受（pattern_match.rs:134-141）。

判定与旧探测逐例一致（临时探针 8 例核对，`e2560a4` 提交信息）；孪生顺带
修一例旧漏报（GADT `Vec[T] l` 只写 nil 时应报 cons，旧孪生漏报）。实测
（k=11 match）：孪生 fast_ss 0.187→0.047 ms（4.0×）、参考版 0.234→0.160
（1.5×——旧探测只占其编译期小头）。

### 3.4 嵌套覆盖检查：收窄与恢复（`aafa5ed`/f774703 同轮）

逐臂下钻的初始口径相对决策树有三处诊断收窄（登记于
`docs/l09l13-match-compiler-analysis-2026-09-17.md`）：覆盖只做顶层、
遮蔽只认通配臂、特化失败的臂静默跳过。其中**嵌套覆盖缺失**（如
`nil` + `cons(h, nil)` 缺 `cons(h, cons(..))`）被 2026-09-18 评审定为
P0——修复前静默接受、运行期在尾部为 cons 的值上卡住——L07 同款恢复：

- **两段式记账**：走查中嵌套 `Con` 字段位置只记入 `pending_pos`（路径 +
  字段 Sum + 走查 ret）；本臂全部特化方程**解出后**（σ 为终态）才提升为
  带 σ/lvl 快照的 `NestedCheck`（pattern_match.rs:55-60、279-288）——
  字段走查时索引精化不在 σ 里，提前探测会把已精化下不可达的构造子误判
  可达。整臂特化失败（荒谬臂）丢弃记账；
- **结算**（pattern_match.rs:302-341）：字段 Sum 置于记录臂的终态 σ 之下
  force 后逐构造子探测；覆盖集 = 已走查臂的 `PatternDetail` 沿路径的结构
  贡献（`PosCover`/`cover_at`，mod.rs:104-133，**参考版与孪生共用同一实
  现**保证判定与文案逐字节一致）。缺覆盖报
  `match 不完整：模式位置 {path} 缺少构造子 {ctor}`（`Warning::
  IncompleteNested`，L07 同文案）；
- **保留的两条收窄**：遮蔽只认通配臂（`is_catch_all` 之后的臂报
  `Unreachable`，pattern_match.rs:299-301；非通配的联合遮蔽不报）；
  特化方程失败的臂静默跳过（不进 `pats`、不告警——与决策树叶子上
  `check_pm_final` 失败即 `Ok(false)` 的口径一致）。若后续要恢复路径感知
  的遮蔽诊断，需另建 usefulness 分析。
- 构造子良构性检查（同轮）：`ret` 不是本 enum、参数位特化（隐式参数位
  非参数变量）在注册期拒绝（mod.rs:1996 起的 `test_ctor_wf_*` 钉）；
  重绑定参数惯用法（`p[A,B](a,b) -> Pack[A][B] a b`）放行。

## 4. 精化载体：显式替换（L07 重构回合的同批移植，`ad412ab`）

参考版 + 孪生同批把模式精化从"上下文改写"改为"显式替换"（dpm-nbe 对
齐），机制与 L07/L08 逐一对齐（L07 README §1.2/§1.3），此处只记本层定制：

- `unify_pm` 不再返回改写后的 `Cxt`，改为累积 `SpecSolve.acc`（持久化单
  链 `Subst`/`SubstV`，mod.rs:210-328）；臂边界回滚 = Rc 指针赋值；
  `Cxt::update_cxt`/`refresh` 删除，调用侧改 `subst_cxt`（env 槽 +
  `names.by_lvl` 影子索引包裹）。
- **L10 定制**：(a) 可解集 = **任意裸 Rigid**（无 L07 的 bind-slot 白名
  单），故 `SpecSolve` 无 `solvable` 字段；(b) **occurs 守卫不扫 Flex 的
  spine**（mod.rs:380）——本层元变量以全 scope 剪枝 spine 登记，spine
  合法含当前方程的 rigid，扫了会把 GADT 嵌套 match 的合法解误判成环
  （test5/test6/test_index/test0/test7 回归）；(c) `to_typ` 消费点改走
  `force_deep`（mod.rs:670，Sum/SumCase 槽位一并推开），否则 trait 接收者
  类型经 `val_to_typ` 掉参；(d) 孪生 `subst_cxt` 必须同步包裹
  `names.by_lvl` 影子索引，只包 `types` 链会丢外层精化。
- **交互点**：`unify_pm` 只服务模式方程路径；trait 实例求解走常规
  `unify`（`solve_trait`），不带 spec——实例求解过程中的合一不会获得
  特化解能力（elaboration.rs:118 注释）。
- 孪生侧 `frcs` 同构移植（`XCell::VSub`）；`force` 的 VSub 入口不烧
  fuel，frcs 的 lookup 命中烧 1（燃烧剖面对齐参考版）。

## 5. 性能孪生（`bump_spine_iter.rs`）

L09 冠军配方（bump arena + 打包值 tag 编码 + 迭代内核 + quote 记忆化 +
O(1) 名字解析 + `Tycker` 稳态复用）的 L10 移植（孪生模块头注释 1-73 行
是权威清单）。L10 的增量与落地项：

- **trait 面**：trait = `is_trait` 的 Sum；`Machine::solve_trait_ref` 镜像
  参考版 `solve_trait`；快版 → 求解器的 `Typ` 桥 `val_to_typ`（只在求解
  边界用，非热路径）；`Synth` 直接共用参考版 typeclass.rs；
- **global 大下标哨兵**（`GLOBAL_BASE`，bump_spine_iter.rs:89）与中性
  globals 视图（Match/Match 分支体重求值用，替代 L11 的 declb 存根表）；
- **名字/声明表 COW**（2026-09-12 轮，`docs/opt-name-table-cow-2026-09-12.md`）：
  同轮删除参考版 `DeclTm::Def` 的 eager `nf + pretty_tm` 两字段——无任何
  消费方而 body 全规范化在大值负载上是每 decl O(值大小)，是 church 负载
  参考版对孪生 162× 的全部来源（k=13 单 decl 探针 205ms / 最终 quote 仅
  9.6ms）；删除后 church basic k=13 199.4→6.78 ms，对孪生倍率回落 5.1×；
- **精化燃料池补齐**（`dbe79cf`，第三轮评审 P1）：孪生原本完全没有燃料
  池，照 L09 模板补 `PM_FUEL`（thread_local，4096；bump_spine_iter.rs:991-1010）
  ——三处燃烧（frcs 的 lookup 命中 / Match 重选 / spine 链 rigid 头命中）、
  五处入口充值；语义 = lookup 耗尽返回裸 rigid（有界降级）、Match 耗尽不
  重选。注意孪生 force 的 **meta 展开**当前无 fuel 门（窗口不可达，保留
  降级臂，bump_spine_iter.rs:3436-3440），与参考版 force 的 meta 展开烧 1
  是已知剖面差；
- **匹配编译器**：§3 全套（逐臂下钻 + 值级探测 + 两段式嵌套覆盖 +
  `fast_substv_reclaimed_across_rounds` 的 σ 跨轮回收）。

### 双 oracle

`cargo test --test l10_fast_parity`：`#[path]` 独立 crate（只编
list/bimap/parser_lib/L10），参考版 `run` vs 孪生 `run_fast`，判据
**Ok 输出逐字节一致 / Err 判定 + span 归一化后正文一致**（`norm_err`
剥掉 Debug-Span 的 `@ N,M` 与 `start_offset/end_offset/path_id` 数字；
meta 编号不剥——L10 双实现分配序列一致，L11 才有该偏差）。覆盖面：
L09 层语义回归（enum/match/struct/投影/宇宙）、trait 全家
（`parity_trait_full_demo` / `trait_pieces` / `trait_errors` /
`golden_trait_tostring_and_say_synthesis` / `golden_outparam_add_chain`）、
深负载（church/strchain/match/struct/universe/traitchain 生成器，含与
参考版 `bench_check_nf` 的节点数互检）、卡住投影契约、嵌套覆盖正负例、
`parity_review_fixes_2026_09_18`、σ 跨轮回收
（`fast_substv_reclaimed_across_rounds`）。

### 基准

```text
cargo run --release --bin l10bench -- --workload all --max-k 11
```

负载族：`church` / `strchain`（L06）/ `match`（L07）/ `enum`（L07 GADT）/
`struct`（L08）/ `universe`（L09）/ `traitchain`（**L10 特色**：固定
trait/impl 段 + 2^(k+1) 层 `def c{i} = c{i-1}.say zero` 方法调用链，每层
一次实例合成 + 方法 β 应用）。

实测（`docs/bench-matrix-2026-09-18.md`，隔离进程，`--rounds 3`，每格
min；`traitchain` 取 k=9）：

| 负载 | k | basic (ms) | fast_ss (ms) | fast (ms) | basic/孪生 |
|---|---|---|---|---|---|
| church | 11 | 1.586 | 0.334 | 0.491 | 4.7× |
| strchain | 11 | 921.897 | 3.259 | 3.058 | 282.9× |
| match | 11 | 0.235 | 0.183 | 0.187 | 1.3× |
| enum | — | — † | — | — | — |
| struct | 11 | 1000.137 | 4.138 | 4.176 | 241.7× |
| universe | 11 | 1267.544 | 2.361 | 2.506 | 536.9× |
| traitchain | 9 | 22769.215 | 84.704 | 99.139 | 268.8× |

（basic = 参考版 `bench_check_nf` 口径 check+nf；fast/fast_ss = 孪生
`Tycker` bench 口径，解析在计时外。表注：L10 非 match 负载与 09-12 存档
比值 0.978–1.017×，符合"只换了 match 编译器"的预期；match 的孪生/参考
由首测 0.8× 落后转为 1.28× 领先。）

## 6. 已知偏差与已知限制（诚实清单）

### 6.0 已修复：`fresh_meta` close 的 O(n²) 内存（2026-09-21）

`fresh_meta` 的闭类型路径沿 telescope 链**全量**包装（Bind → Π、Define →
Let）以与参考版 `close_ty` 逐值同轨。但 impl 声明的类型参数经
`ImplDecl` 臂泄漏进 decl 级上下文（参考版同款泄漏，`cxt.bind` 后
`cxt = c`）后，`env_ext_defs` 的 tip 路径永久失效（`binds.is_none()` 不再
成立），此后每个顶层 define 都落进 binder 链——`flat_len` 停在泄漏前的
13，于是 close 的 `k = cxt.lvl - flat_len` 随 define 数线性增长。方法调用
密集负载（traitchain）每次 `.say` 触发 ~4 次 `fresh_meta`，每轮闭环
2.1M 个 wrapper 节点：**k=9 142.67MB / k=11 2,115.82MB / k=13 ~32GB，
内存 O(n²)**（l06l13mem 分配计数实测；L10SOLVE_PROBE 的 CLOSE 行
`k_sum=2108412` 即死重量）。

探针画像：**75% 的 close 调用 q 是闭项**（trait_wrap 合成 Let 的隐式 `T`
参数，类型 `Type 0`），25% 只引用那一个泄漏的深层 Bind（`?k T`）。

**修复 = 值中性化简**（`close_tm_reduced`）：只保留 ① 全部 Bind 槽
（Π 层是参考版可观察语义）② q 实际引用的 define 槽；其余 define 槽丢弃，
q 的自由变量下标按保留槽位重编号（`remap_free_vars`）。正确性依据：`Let`
包一个体项不引用的变量，求值结果与不包相同——与既有
`binds == 0 && !has_free_var(q)` 快路径同族（该路径已在生产）。平坦层
由 `global_env` 供给、q 引用它们的 Var 保持自由，与舊路径一致。

实测（l06l13mem / l10bench，k=9 / k=11）：内存 **142.67→30.63MB /
2,115.82→125.63MB**（−78% / −94%，转为线性）；CLOSE 探针
`kept_avg=1`（每调用只包 1 层）；traitchain fast_ss **81.3→50.4ms
（−38%）**，universe −6%、struct −3%，其余负载在噪声带内。门禁：
`l10_fast_parity` 46 / lib 25 全绿，l10bench 七负载「快版==参考版」互检
通过（enum 负载的既有孪生发散与本修复无关——原始二进制同样失败）。

### 6.1 性能缺口

- **traitchain 参考版 268×**：参考版侧的候选因素——`trait_wrap` 每次调用
  克隆整个 `trait_definition`（elaboration.rs:1008 的源码 TODO 自证）、
  `Synth::new_subgoal` 每子目标克隆实例表、`synth` 每次前置 `clean()`。
  **归因未核实**（无剖析数据），且孪生侧同走 `Synth`，差距主要在参考引擎
  其余部分。
- **非 match 大值负载 200–500×**（strchain/struct/universe）：与 L09-L13
  同型（孪生 bump arena + 迭代内核 vs 参考版 Box 树 + 递归），非本层特有。
- **enum 负载不可测（既有）**：孪生发散/参考版不可测（矩阵 † 注），与本
  轮改动无关（改动前二进制同样失败）。

### 6.2 语义与诊断

- **effort 超限 panic**（§1.4）：`Too much effort :(` 是崩溃面不是错误。
- 孪生偏差：错误消息内嵌 Debug-Val/Tm 的名字 Span 全零（参考版携带源码
  偏移），套件比对前归一化；无其它已知 Ok 输出偏差（parity 逐字节保证）。
- 卡住 match 的显示是 `(unsolved match …)` 简形（与 L07 的完整形态刻意
  分歧，golden 锚定）。
- 无 K 公理层面的安全保护（精化出现在其它假设里的变量，教学取舍，同 L07）。

## 7. 测试

- `cargo test --lib L10_typeclass`：**21 个**（`mod.rs` 16 +
  `parser/` 5）。`mod.rs` 内含 L09 血统的 test0-test7 / test_trait /
  test_index（GADT、嵌套 match、bits_adder 全加器）与 2026-09-18 评审
  回归钉 7 个（mod.rs:1874 起：嵌套覆盖正负例 ×3 / 索引精化无假阳性 /
  构造子良构性三态）。
- `cargo test --test l10_fast_parity`：**42 个** = 套件自有 21 + `#[path]`
  引入 `mod.rs`（含 parser 子模块）带入的 21 个单测。判据见 §5 双 oracle。
- 基准正确性闸门：l10bench 各负载的「快版 == 参考版」输出互检 + nf 节点
  数互检（traitchain 无闭式，以互检代替硬编码）。

（历史注：`4e97743` 落地时的验收口径是 l10_fast_parity 33 / lib 14；
`aafa5ed` 评审修复轮加钉后为 42/21，即当前数。）

## 8. 参考资料

- [elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo) 07
  （unification 骨架；本层 inherit 自 L09 重写）
- [KonjacSource/dpm-nbe](https://github.com/KonjacSource/dpm-nbe)
  （explicit substitutions + forcing：§4 的机制蓝本）
- 本仓库 `src/L07_sum_type/README.md`（逐臂下钻与显式替换的原始设计）、
  `docs/l09l13-match-compiler-analysis-2026-09-17.md`（决策树诊断与
  收窄登记）、`docs/bench-matrix-2026-09-18.md`（基准口径与全表）、
  `docs/review-continuity/a4-r1.md`（跨章连贯性登记）
