# L12：canonical 层（trait 求解 Val 级重写 + 宏 + canonical 搜索）

本层在 L11（宏展开）之上再叠三件事：**trait 求解器 Val 级重写**
（`typeclass.rs` 移除 `Typ` 桥接，求解器直接匹配 `Val`）、**`Val::Call`
内联节点**（HDL regNext 泛型：def 调用被内联后保留名字与显示实参）、
**canonical 搜索**（`canonical.rs` 的 `iddfs`/`search`，Err 重试路径专属）；
参考版全面 SmolStr 化。性能孪生 `bump_spine_iter.rs` 是 L11 冠军配方
（commit `4c6552f`）向本层的移植，与参考版共用 parser / pretty /
preprocess，**Ok 输出逐字节一致**（互检测试 +
`tests/l12_fast_parity.rs`）。

与 L07/L08 的关系：本层的依赖模式匹配与精化机制是 L07 显式替换方案
（dpm-nbe 对齐）的同源实现——`Subst` 持久化单链 + `Val::VSub` 读点推开
（§3），特化合一走 `SpecSolve` 穿参（§2.5）。与 L13 的关系：L13 的
`check_pm_final` 返回精化后 `Cxt`（`update_cxt` 血统），本层返回 σ——
两条精化载体路线在本仓各有一层代表。

---

## 1. 语言特性

```typort
enum Nat {                              -- 构造子换行分隔
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {                 -- [A] 隐式参数；(len: Nat) 显式索引
    nil -> Vec[A] zero                  -- -> 自定义返回类型（GADT）
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

struct Point[T] {                       -- 投影 p.x；脱糖出 `Point.mk` 构造子
    x: T
    y: T
}
def get_x[T](p: Point[T]): T = p.x

trait Add[T, O: outParam(Type 0)] { def +(that: T): O }
impl Add[Nat, Nat] for Nat { def +(that: Nat): Nat = nat_add_helper this that }
def four = two + two                    -- 算符方法经 trait 求解分派

def ttt =
    let useless1 = create_global "Nat" 2;
    let useless2 = change_mutable("Nat", z => succ(z));
    get_global "Nat"

macro_rules module { ($name: ident) => {def $name = string_concat("module ", stringify $name)} }
module test2
```

- **enum / 构造子**：方括号隐式、圆括号显式；`-> ret` 自定义返回类型。
  无标注的隐式参数域**钉为 U(0)**（L07 评审前向传播，P13 钉
  `parity_enum_struct_impl_hole_pinned_u0`：否则第 2+ 参数域是带 pruning
  的部分应用 meta，使用点显式供参需解它，invert 对非变量 spine 实参
  误报 can't unify）。
- **构造子良构性（WF）**（2026-09-18 评审 P1，`elaboration.rs`
  `check_ctor_wf`）：实例化构造子类型全部绑定器后，ret 的 WHNF 必须是
  本 enum 的 `Sum`，且隐式参数位逐一等于 telescope 内 bare rigid——拒绝
  phantom 构造子（`c -> Nat`：向构造子名字空间注入"类型正确但永不匹配
  任何模式"的值，覆盖完备的 match 在该值上卡死）与参数位特化
  （`c -> Foo[Bool]`；特化请走显式索引）。构造子重绑定参数惯用法
  （`p[A,B](a,b) -> Pack[A][B] a b`）不受误伤（回归钉
  `test_ctor_rebind_params_ok`）。
- **trait / impl**：`trait` 声明方法签名（含 out 参数标注
  `O: outParam(Type 0)`），`impl` 提供实例；`x.m` 方法调用先走
  **inherent 方法**（`Cxt.namespace` 表，§4.3），再走 trait 求解器
  （`typeclass.rs` 的 `Synth`，generator/consumer 搜索树 + 实例表）。
  算符方法（`def +`）经 impl 注册后，内联调用
  （`Val::Call`）在 quote 时按登记的算符符号还原中缀显示。
- **宏**：`macro_rules` 声明级展开（`stringify` / `$name: ident` /
  `$body: raw`），自递归受 `MAX_MACRO_EXPANSION_DEPTH = 256` 守卫
  （`parser/mod.rs:142`，f51a0e4 家族；探针
  `probe_macro_self_recursion_depth_limit`）。
- **字符串 / 可变全局内建**（`Cxt::new` 注册，`cxt.rs:125-191`）：
  `string_concat` / `string_to_global_type`（字符串 → decl 表动态引用）
  / `create_global` / `change_mutable` / `get_global` /
  `change_mutable_default`——前两个是纯 λ 链体（`Tm::Prim` 节点），后四
  个读写 `Infer.mutable_map`（RwLock，每轮清空，跨轮不泄漏，
  `steady_state_reuse` 钉）。
- **重定义语义分层**：`fake_bind`（`cxt.rs:248`）在体检查前把 def 名
  登记成中性占位，撞名报 `redefine {名}`（递归自引用 = 占位存根）；体
  检查后的正式登记走 `decl`（`cxt.rs:294`），其中**重定义检查被注释**
  ——顶层同名静默覆盖（参考版现状，孪生同口径，快版模块注释
  `bump_spine_iter.rs` "重定义静默覆盖"条）。构造子以**裸名**登记
  （无 `Enum.case` 别名；struct 的 case 名本身是 `Name.mk`）。
- **构造子值显示格式（分层契约）**：本章（及 L11/L13）构造子值显示为
  `{头}[{隐式实参}]::{分支}({显式实参 逗号连接})`，如
  `Point[Nat]::Point.mk(4, 6)`、`Vec[Bool]::cons(1, Bool::false, …)`
  ——L09 起的血统格式，被本章内置测试（test0/test2/test7/test8/
  test_trait、bits_adder）字面锁定；与 L08 的空格 + `[名]` 隐式格式
  **分层**，不得互贴（a4-r2 曾把 L08 格式误移植 L09-L12，终门禁回滚）。
  非 Sum 头的 `sum_head_name` panic 降级保留；Nat 字面守卫臂
  `pretty_nat` 不受影响。

## 2. 匹配编译器：决策树 → 逐臂下钻（2026-09-18，commit `45330e6`）

参考版与孪生都从**决策树矩阵**重写为 L07 的**逐臂下钻**（同 L10/L11；
动机是 `match` 上孪生反而比参考版慢，首测 0.3×——根因分析见
`docs/l09l13-match-compiler-analysis-2026-09-17.md`：360 次决策树节点
访问 vs L07 逐臂 2 条臂，`filter_accessible_constrs` 一项就占 elab
34%）。实测（同窗口交错 A/B 的**比值**，两窗口一致）：

| 口径 | 相对移植前 |
|---|---|
| 参考版 basic | **4.8×** 更快 |
| 孪生 fast_ss | **8.9×** 更快 |
| 孪生 fast_run | **7.1×** 更快 |

移植后绝对数见 §5 基准表。语义相对决策树的**三处收窄**（诊断面）与
L10/L11 完全一致（`docs/l09l13-match-compiler-analysis-2026-09-17.md`
§2）：

1. **覆盖只做顶层 + 嵌套位置**（§2.2），不再有决策树 usefulness 的
   路径感知全量分析——`Unmatched` 的形态固定为「构造子 + 999 通配」；
2. **遮蔽只认通配臂**：catch-all 之后的臂报 `Unreachable`；非通配的
   重叠臂不再逐一判定；
3. **特化失败静默跳过**：荒谬臂（索引方程不可解，如 `Vec[Nat] zero`
   上的 `cons`）不报"分支不可达"，直接跳过、不产生覆盖义务（同 L10
   口径，非 L07 的报错口径）。

### 2.1 逐臂下钻主干（`pattern_match.rs`）

`Compiler::compile`（`pattern_match.rs:177`）按用户书写顺序逐臂处理
（保持运行时首匹配语义）：`walk_pat` 走查模式并绑槽 → `check_pm_final`
特化合一 → 臂上下文里检查分支体。`walk_pat`（`:376`）的下钻纪律与
L07 `walk_con` 同构：

1. **剥构造子 Π 链**：枚举隐式参数用头部 Sum 的实参值实例化（不产生
   槽），其余绑定器逐个绑成 fresh rigid，按 icit 对齐用户子模式（隐式
   子模式 `[p]` 支持；没写/对不上补虚通配 `_`）；
2. **槽位纪律**：枚举隐式参数不占槽、变量模式以用户名绑槽、**Con 本身
   不占槽**——与运行时 `eval_aux` 的"值-模式 zip"严格同序同数；
3. 非本类型构造子的裸名回落为变量模式（`PatternDetail::Bind`）；带子
   模式解构非构造子报定向错误。

### 2.2 嵌套覆盖检查：两段式记账（2026-09-18 评审 P0 前向传播，L07 同款）

嵌套 `Con` 字段位置的可达性若不被枚举，非穷尽 match（如 `cons(h, nil)`
缺 `cons(h, cons(..))`）被静默接受、运行期卡死。机制
（`pattern_match.rs:33-64`）：

- **走查期**只记 `(路径, 字段 Sum)` 到 `pending_pos`（路径 = 根到字段
  的 (构造子名， 字段下标) 链，`cur_path` 臂内 push/pop 平衡）；
- **`check_pm_final` 成功后**（特化方程已解出、σ 为终态）才提升为带
  σ/lvl 快照的完整记账 `NestedCheck`——字段走查时外层方程尚未解出，
  索引精化不在 σ 里，此时探测会把已精化下不可达的构造子误判可达；
- **整臂结算后**逐记账探测：字段 Sum 置于记录臂 σ 之下 force，可达且
  无臂覆盖的构造子报 `Warning::UnmatchedAt`（文案与 L07 统一：
  `match 不完整：模式位置 {cons#2 → nil#1 形路径} 缺少构造子 {ctor}`；
  路径无 Span 可挂，直塞字符串保证参考/孪生 Debug 输出逐字节一致）；
- 覆盖贡献按 `cover_at`（`mod.rs:201`）沿路径判定：var/Any = 全覆盖、
  同 ctor 前缀 = 贡献其末端构造子、祖先异 ctor = 不可达该位置；可达集
  取各记账臂探测的并集（保守）；`reported` 集合去重；
- **失败臂丢弃记账**（走查错/特化冲突的臂不产生覆盖义务）。

回归钉：`mod.rs` 的 `test_nested_coverage_gap` / `_gap3` /
`_complete_ok` / `_gadt_tail_position`（索引族嵌套位置在本层的保守
判定：尾部索引槽未被 σ 精化时 nil/cons 都按可达 → 缺 nil 报缺失，
拒绝方向 = incomplete 而非 unsound）+ parity 侧
`parity_review_fixes_2026_09_18`。

### 2.3 覆盖探测：值级结构探测（commit `a8fcaef`）

`probe_accessible`（`pattern_match.rs:87`）：直接读 decl 表拿构造子
类型，走 Π 链实例化——枚举隐式参数用头部 Sum 实参、其余绑定器用超出
上下文的 scratch 层 fresh rigid（探测状态全在本地，meta 快照换入换出
即回滚），返回类型与头部类型跑一次索引方程（`unify_indices`，头部一侧
在前——双侧可解变量时解"头部变量 := 构造子侧值"）。成功 = 该构造子
可能出现在头部类型的值里；结构冲突 = absurd，不计入覆盖。

- **每个探测独立充值** fuel（多构造子枚举的逐 ctor 探测不互相挤占共享
  池；探测本身回滚，只有燃料单向消耗）；
- **fuel 耗尽的失败按可达处理**（保守要求覆盖）：反方向（判不可达 →
  覆盖检查放过该构造子）会让深负载下的非穷尽 match 被静默接受
  （unsound → incomplete 的方向选择，L07 评审 P1-2 前向传播）；
- **嵌套位置的延迟探测**显式穿参 `lvl`：scratch 层级必须落在该臂全部
  真槽之外，否则与臂内模式槽的 rigid 撞层级（探测方程误把真槽当
  scratch 解）。

### 2.4 臂边界与状态隔离

L12 无 L07 的 bind-slot 白名单可污染（见 §2.5），臂 σ 逐臂重建，臂序
不影响判定——`test_stale_solvable_order_independent`（L07 stale-
solvable 场景的本层移植）断言两种臂序判定一致；被通配臂遮蔽的臂跳过
并报 `Unreachable`（保持首匹配语义不报错）。

### 2.5 特化合一（`unify_pm` + `SpecSolve`）

`check_pm_final`（`elaboration.rs:87`）= `infer_expr` + `insert` +
`unify_pm` + 第二方程（被匹配项的值 `ori` 与精化后模式项值再对一次，
失败容忍丢弃）；返回 `(项, σ)`——**不是** L13 的精化 Cxt。`SpecSolve`
（`elaboration.rs:23`）只带 `acc`（已累积解）：L12 的可解集 = **任意
裸 Rigid**（旧 `update_cxt` 对任何裸 rigid 都改写槽位，没有 L07 的
bind-slot 白名单），故没有 `solvable` 字段。`unify_pm`（`:124`）的臂：

- 双裸 Rigid 同名 = 自反 Ok；单侧裸 Rigid = occurs 守卫后解入 `acc`
  （Flex 解值保持旧机制 no-op；`val_mentions_lvl` 只扫解值自身结构、
  **不扫 Flex 的 spine**——本层元变量以全 scope 剪枝 spine 登记，
  spine 里合法含当前方程正在解的 rigid，`mod.rs:473` 头注）；
- `SumCase`/`SumCase` 同名构造子只逐字段比 + **比 Sum 头名字**（2026-09-18
  评审 P1 前向传播：跨 enum 重名构造子是两个不同值，同 case_name 不足
  以判定身份；typ 值比较会经索引槽互相引用深递归，索引等式由外层
  Sum/Sum 参数 zip 建立）；
- 方程两侧在入口置于当前 acc 之下再解释（先解出的方程对后到的子方程
  自动可见）；其余形态回落 `unify_catch`（常规合一器，不带特化解能力
  ——canonical 搜索与 trait 实例求解也不会获得特化解能力，边界与旧
  `update_cxt` 只从 unify_pm 调用的口径一致）。

## 3. 显式替换精化（σ：`Subst` / `Val::VSub` / `frcs`）

精化载体是 L07 同款的显式替换（dpm-nbe 对齐；`mod.rs:288-455`）：

- **`Subst`**：层级 → 值的持久化单链（链头 = 最新），`extend` O(1)
  cons、`compose` 外层条目接链头（对齐旧"后写覆盖"）、`lookup_hit`
  首个命中 + **条件包裹**（解值浅结构不引用任何已解层级时原样返回——
  读点热路径零分配零 fuel；引用才包 `VSub`，`mentions_level` 的扫描
  口径宁宽勿窄：误报只多一次包裹，漏报才丢精化）；
- **`Val::VSub(v, σ)`**：解不改写既有值，只包在被消费的值外；`force`
  的 `frcs` 臂（`mod.rs:717`）在读点把 σ 推进值的结构——spine 槽只
  **包裹**不推进（槽位引用是作用域事实，物化会破坏后续 solve 的
  invert）、闭包 env 逐槽包裹、Match 的 scrutinee **推进**（推进后是
  构造子值就按首匹配重选——旧 `refresh` 在槽值重求值时连带重选分支的
  等价物）；被解变量的读点（lookup 命中）烧 1 fuel，对齐旧 refresh
  的燃烧剖面；
- **臂上下文**：`cxt_arm = cxt_walk.subst_cxt(&sigma)`（`cxt.rs:320`）
  ——env 槽与 src_names 类型包 `VSub`，lvl/locals/pruning 不动，**槽位
  布局 = 运行时布局永不漂移**；σ 为空时零开销直通；
- **`force_arg`**（`mod.rs:896`）：合一器参数视角的 WHNF——逐层解包
  VSub 但不展开精化、不做 Match 重选（`invert`/`prune_vflex` 关心的
  槽位存在性不随分支内精化改变）；`force_deep`（`:858`）服务 trait
  求解等结构消费者的 Sum/SumCase 槽位按需展开（非热路径）；
- **fuel 池**：`UNIFY_FUEL = 4096`（`mod.rs:605`）共享池护 `force`
  meta 展开 + unify 结构递归（L08 护栏前向传播）；`unify(.., fuel)`
  参数另护 Decl 头展开重试臂。覆盖探测的 fuel 语义见 §2.3。

## 4. 核心数据结构

### 4.1 decl 表与 Rc 别名

```rust
type Rc<T> = std::sync::Arc<T>;                        // mod.rs:22（LSP 线程边界 Send/Sync）
type Decl = HashMap<SmolStr, (Span<()>, Rc<Tm>, Rc<Val>, Rc<Ty>, Rc<VTy>)>;  // 5 元组
```

`Cxt.decl: Rc<Decl>`（`cxt.rs:21`，commit `53e8adb`，同 L11 口径）：
每次 `Cxt` 构造只递增引用计数，写入走 `Rc::make_mut` 写时复制——
`struct` 负载 k=11 3397→530 ms、`macro` 2731→801 ms（3.4–6.4×）。
残留（插入路径的整表克隆）见
`docs/perf-l08l13-followup-2026-09-17.md` §3.4。

### 4.2 项与值（相对 L07 的增量）

`Tm`/`Val` 骨架同 L07（Var/Decl/Obj/Lam/App/AppPruning/U/Pi/Let/Meta/
Literal/Sum/SumCase/Match + `Val::VSub`），增量：

- **`Tm::Call(名, 显示实参, 值实参, 体)` / `Val::Call(名, 值实参, 体)`**
  ：def 调用内联节点——体是原 def 的 λ 链体，名字与显示实参供 quote /
  pretty 还原调用形态（HDL regNext 泛型的显示基础）；`Val::Call` 在
  `v_app` 下透明穿透到体，`force` 推进体。
- **`MetaEntry::Unsolved` 三元**：`(闭类型, Arc<Cxt> 快照, 原始类型)`
  ——服务 `no_metas` 错误路径的 pretty/lvl/decls 重建与
  `meta_contrains` 挂账（孪生侧同构为 `MetaSnap`，见 §5）。
- **`hover_table` / `completion_table`**（`mod.rs:615-616`）：LSP 观察
  面雏形（hover 条目 = (span, def span, Cxt, 类型值)，completion 条目
  = (span, 名字)），由 `x.m` 方法解析与 trait 方法补全路径填充；L13
  才升级为 push 期渲染串（§L13 README）。

### 4.3 `Cxt.namespace`：inherent 方法分发

`List<(Rc<Val> 接收者类型, HashSet<SmolStr> 方法名集, Raw 接收者名)>`
（`cxt.rs:22`）：`impl` 声明（need_create 路径）把接收者类型与方法名
集前插进表，方法本体以 `前缀 ++ 方法名` 登记为顶层 def；`x.m` 解析时
沿表找接收者类型可合一的条目，把调用改写为 `前缀方法名 x` 再 infer
（`elaboration.rs:1196`）。这是 L13 全量命名空间
（package/import/`TypeHead.method` 直查）的前身。

### 4.4 `Match` 的运行时

卡住 match 是中性值 `Val::Match(scrutinee, 捕获 env, arms, origin)`；
`eval_aux`（`pattern_match.rs:305`）按 `PatternDetail` 首匹配选分支，
嵌套 Con 递归 zip；quote/rename 分支体在 **declb 简化 decl 表**（全表
条目换成 `Decl(name)` 存根）下重求值再导出，中性表构建提到分支循环外
（避免 #分支 × |decls| 次全表重建）；`origin`（`lookup_function_by_cases`
按模式形状反查 def 名）让卡住 match 的 quote 能包上 `Tm::Call` 显示
外衣。

## 5. 性能孪生设计（`bump_spine_iter.rs`）

L11 冠军配方（bump arena + 打包值 tag 编码 + 迭代内核 + 记忆化 + 稳态
复用）的移植，继承 L05-L11 全部机制；模块头注释（`bump_spine_iter.rs:1`）
记录了与参考版的逐条对位。本层增量：

- **未解 meta 保留上下文快照**：`MetaEntry::Unsolved` 三元同构
  （闭类型， `MetaSnap`, 原始类型）；`MetaSnap` = { 创建时层级， 名字
  telescope, decls }，`Rc<MetaSnap>` 跨轮 reset 前句柄已消亡（两步
  transmute 入 `'a`）。
- **快版 → 求解器的 `Val` 桥**（`v_to_ref_val`，取代 L11 的
  `val_to_typ`）：L12 `typeclass.rs` 移除 `Typ` 桥接、求解器 `Val` 级
  匹配，实参逐项解码成 `Arc<CVal>`（Pi/Match/Decl 链等形态降级为永不
  匹配的标记值——参考版 `val_match` 对非构造子 goal 一律 false，观察
  面相同）。只在求解边界用，非热路径。
- **`solve_trait_ref` 对齐参考版**：实参 force 后直通 `Val`，任一仍
  Flex 即 `Ok(None)` 交回合一；方法名命中 trait 时以
  `Flex(MetaVar(u32::MAX))` 通配参数试探。
- **canonical/`iddfs` 不移植**：参考版只在 Err 路径的重试闭包
  （`elaboration.rs` 的 `ret = move || infer.iddfs(...)`）调用，不影
  响判定与 Ok 输出，快版无搜索机。
- **`PrimId` 枚举**替代参考版 `Rc<dyn Fn>` 闭包（bump 内不能携带闭
  包），语义逐句移植 `cxt.rs` 的 6 个内建。
- **σ 跨轮回收**（2026-09-18，L07 §7.7 同款）：bump `reset()` 不跑
  `Drop`，arena 内 `XCell::VSub` 持有的 `Rc<SubstV>` 克隆跨轮不递减
  （长生命周期 Tycker 下无上界慢泄漏）。修：`wrap_sub` 登记指针进
  `VSUB_REGS`（thread_local）+ 轮界 `vsub_reclaim` 逐指针归还；
  `SUBSTV_ALIVE` 是观察口。回归钉
  `fast_substv_reclaimed_across_rounds`（同一 Tycker 连跑两轮，计数
  回落轮前基线；测试侧配套 `SigmaGuard`/`SigmaExcl` 可重入采样闸）。
- **无燃料池**：快版无 `UNIFY_FUEL` 等价物（`XCell::VSub` 注释明写
  "本层无燃料池，故不存在耗尽返回 VSub 的例外"）；参考版的 Decl 头
  展开燃料臂在孪生无对应口径（无已知触发例，登记不盲补，§6）。
- **逐臂匹配编译器**：`45330e6` 同步移植（`compile`/`walk_pat`/
  `probe_accessible`/`unify_indices` 全套），嵌套覆盖两段式与
  `cover_at`/文案与参考版逐字节一致（parity 钉）；深负载
  （natadd/strchain/match/struct）逐字节互检 + Err 归一化正文一致。

### 基准

```text
cargo run --release --bin l12bench -- --workload all --max-k 11
```

`docs/bench-matrix-2026-09-18.md`（隔离进程、rounds=3、每格 min；
k=11）全流程表：

| 负载 | basic (ms) | fast_ss (ms) | fast (ms) | fast_run (ms) | basic/孪生 |
|---|---|---|---|---|---|
| natadd | 1.692 | 0.917 | 0.935 | 0.755 | 2.2× |
| strchain | 635.565 | 3.332 | 2.994 | 7.634 | 83.3× |
| match | 0.218 | 0.176 | 0.179 | 0.222 | 1.0× |
| struct | 542.786 | 4.077 | 4.010 | 10.891 | 49.8× |

口径注意（矩阵文档 §0 注）：

- **`fast_run` 是与 `basic` 可比的全流程口径**（含 parse + 每轮重装）；
  `fast_ss` 是稳态裸口径（Tycker 复用、不含流程常数），相对较低故
  比值偏大。match 负载的孪生/参考 = **0.98–1.24×（持平到略优）**——
  移植前的 0.3×（落后）已被 `45330e6` 消除；同窗口交错 A/B 的比值
  （参考版 4.8×、孪生 8.9×）与首测口径一致，绝对数窗口间会漂。
- 其余负载 `natadd` 0.83–0.93×、`strchain`/`struct` 0.97–1.04×（无
  回归，符合"只换了 match 编译器"的预期）。

### 已知偏差（与参考版）

- 错误消息 span 全零（快版错误里内嵌 Debug-Val/Tm 的名字 Span 不携带
  源码偏移），meta 编号 `?N` 分配序列不同——parity 套件比对前按
  `start_offset/end_offset/path_id`/`?N` 归一化；
- parity 已知偏差家族（套件头注登记）：mod.rs 全部 8 个测试源、
  trait/impl 实例合成演示源与 `get_global` 缺名 panic 用例涉及 GADT
  索引宇宙判定 / struct 接收者实例 / 单臂构造子匹配 / Prim 求值时机
  差，在快版上分叉或发散，整体剔除；Ok/Err 判定 parity 由结构化用例
  保证。bench 侧对应表现：`enum` 负载孪生 check+nf 失败、`traitchain`
  孪生 parity 失败（perf-debt P5）——均**既有缺口**，与 match 编译器
  移植无关（改动前二进制同样失败），矩阵文档表注同口径登记。

## 6. 已知分歧 / 刻意取舍（跨层连贯性评审登记）

- **SumCase 显示格式分层**：见 §1 末条（L09-L13 一族 vs L08，不得互
  贴）。
- **快版孪生不移植 canonical/`iddfs`**：参考版只在 Err 重试闭包调用，
  不影响判定与 Ok 输出（`bump_spine_iter.rs:29-30` 模块头）。
- **`iddfs` 预算调度**：现行为 `1, 2, 3, …, target_limit` 逐 1 递增
  （`canonical.rs:8` `iddfs`——旧 `+= 2` 的偶数跳档已修：授权
  `target_limit` 为奇数时最后一档必然被跳过的完备性缺口不复存在；
  iddfs 仅由 LSP quickfix 的重试闭包触达，`run`/`run_fast` 不经此
  路径，预算细化不影响测试口径）。
- **`vals_eq_ground` 把 Flex 视为等于一切**（`typeclass.rs:196`）：与
  `val_match` 的 Flex 宽放同一策略（实例匹配容忍未解实参），刻意语义。
- **快版 `unify` 无 Decl 头展开燃料臂**：参考版 `unify(.., fuel)` 带
  Decl 头 `quote+eval` 重试配额；孪生无此机制（模块头 unify_iter
  注释），`constraints`（Stuck 挂账）已移植。无已知触发例，登记不盲
  补。
- **快版孪生 `unify_sp_lockstep` 的实参位相等免比**：tag 7 与 Obj 头
  链不免比，由 (Obj, Obj) 合同臂接管判定。
- **`declb_of` 无缓存 / 参考版 `no_metas` 为 quote 版**：同 L11（见
  L11 README；L13 同源机制 71e11ae / 指针键缓存未下沉的论证一致）。
- **参考版 `Cxt.decl` 按 `Rc` 共享**（`53e8adb`）：见 §4.1；写时复制
  语义不变。
- **宏展开深度守卫 `MAX_MACRO_EXPANSION_DEPTH = 256`**（f51a0e4，
  `parser/mod.rs:142`）。
- **`preprocess` 等字节长不变量**：单遍扫描 + 单输出缓冲的注释剥离
  （`mod.rs:1381`，与 L13 同实现；输出与输入等字节长，保持 parser
  span 偏移——黄金校验：全仓 .typort 逐文件 diff + 差分模糊测试）。

## 7. 测试

- `cargo test --lib L12_canonical`：mod.rs 17 个 `#[test]`（test_trait
  / test5 / test6 / test4 / test2 / test0 / test_index / test7 / test8
  全串 + 2026-09-18 评审修复轮回归钉：嵌套覆盖 gap/complete/GADT 尾
  位置、构造子良构性 phantom/参数特化/重绑定正向、stale-solvable 臂
  序无关）；`pattern_match.rs` 无独立测试模块（行为由上述钉覆盖）。
- `cargo test --test l12_fast_parity`（15 个 `#[test]`）：参考版
  `run` ↔ 快版 `run_fast` **Ok 输出逐字节一致 / Err 判定 + 归一化
  正文一致**。覆盖：宏展开、binder 下卡住投影（`parity_stuck_proj_
  under_binder`——快版 force Obj 臂死循环回归）、Err 五例（scope /
  icit / 投影未命中 / 方法不在 trait / 期望宇宙）、深负载四族
  （natadd/strchain/match 链/struct 链，`bench_check` 与 parity 双
  驱动）、稳态复用（含跨轮 mutable 全局不泄漏）、packed-word 对齐钉
  （`XCell`/`CloCell`/`PiCell` ≥ 8）、Round-2 探针（η 守卫 / 超大整
  数 / 宏自递归 / trait 求解失败可恢复 / pruning 掩码反转）、泛型
  trait 假匹配拒绝、enum 隐式域钉 U(0) 四源、2026-09-18 评审修复轮
  parity 钉（嵌套覆盖 / WF / 臂序，用具体枚举载体——List/Vec 载体在
  孪生侧踩中既有 `check_pm_final` 分叉族，套件头注登记）、σ 跨轮回收
  钉。
