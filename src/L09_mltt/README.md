# L09：MLTT 切片（`Type N` 分层宇宙 + 和类型 / match）

本层是**再定基层**：以 MLTT 教学章（宇宙层级 + 和类型 / match）为基底
重写内核，非逐行继承 L08 代码。与 L06–L08 的 decl 表世界有系统性不同——
def / enum 的**名字**按大下标哨兵层级进 `Infer.global` 值表，没有名字键
decl 表；构造子则走 `Cxt::define` 的 env define 槽（§2）。相应地，模式
编译器取构造子类型走 `infer_expr(Var(名))` 而非 decl 直查——这是与
L07/L08 及 L10–L13 的关键结构差异。继承面与已知分歧在跨章节连贯性评审
A4 登记（锚点见 `docs/review-continuity/a4-r1.md`、`a4-r2.md`；其中
部分登记已被后续移植轮取代，以 §2/§6 的现状描述为准）。

2026-09 的两条主线：

- **精化载体显式替换**（`ccfcb87`）：`Subst`（持久化单链）+ `Val::VSub`
  + `frcs` 读点推开 + `SpecSolve` 穿参，与 L07 蓝本逐点同构；
- **匹配编译器逐臂下钻**（`09b9ee8`，2026-09-19）：决策树矩阵 → L07
  口径的逐臂实现（参考版 + 孪生同步，L10–L13 随后跟进），match 负载
  孪生 9.5×、参考版 3.8×（§5）。

## 1. 语言特性（分层宇宙）

```text
def t0 : Type 1 = Type 0
def t1 : Type 2 = Type 1 -> Type 0

enum HighLvl[A] {
    case1(a: A)
    case2(a: t1)
}

def hl : HighLvl[Nat] = case1 zero

def Eq[A](x: A, y: A) = (P : A -> Type 0) -> P x -> P y
def refl[A, x: A]: Eq[A] x x = _ => px => px
```

- **`Type N` 分层宇宙**：`Tm::U(u32)` / `Val::U(u32)` 携带层级（语法
  `Type N`，pretty 同款渲染）；**裸 `U` 只是普通变量名**——宇宙必须
  写 `Type N`（`bump_spine_iter.rs` 模块头与 bench 头注同证）。
- **类型注解一律过宇宙检查**（`check_universe`，`elaboration.rs:246`）：
  推断类型非 `U` → `expected universe` 定向报错；未解 meta 有两条解
  路径——spine 为空且 meta 类型 force 后是 `U` → 解为 `U(0)`；spine
  非空 → 经带 occurs 的 rename 造出 `U(0)` 解。`let` 域 / `def` 类型 /
  `enum` 参数与构造子域全走这一道。
- **enum 声明收集 universe_lvl**：参数域与构造子字段域逐个
  `check_universe` 取 max（`elaboration.rs:451-463`），enum 本体的类型
  是 `Type universe_lvl` 上的 Π 链——高宇宙 enum（`HighLvl[Nat] :
  Type 2`）由此成立。
- **隐式参数域无标注钉为 `U(0)`**（`elaboration.rs:429-450`）：域洞若
  保留，第 2+ 个参数的域经 `fresh_meta` 成为部分应用 meta（`?m A`），
  使用点显式供给枚举隐式实参（`P1[Nat][Bool]`）需解 `?m A := U(0)`，
  invert 对非变量 spine 实参直接 Err → 误报 can't unify。这是 L07/L08
  黑盒三轮修复的 L09 形态（L09 的全局默认层级是 `U(0)`）；显式标注
  `[A : Type 1]` 与显式索引不动。回归钉
  `parity_enum_struct_impl_hole_pinned_u0`。
- **构造子良构性**（`check_ctor_wf`，`elaboration.rs:567`）：构造子
  `-> ret` 实例化全部绑定器后，ret 的 WHNF 必须是本 enum 的 Sum，且
  隐式参数位逐一等于 telescope 内 bare rigid——拒绝参数特化
  （`c -> Foo[Bool]`）与非本 enum 的 ret（`c -> Nat`，会向构造子名字
  空间注入永不匹配任何模式的 phantom 值）；重绑定参数惯用法
  （`p1[A,B](a,b) -> P1[A][B]`）放行。L07 2026-09-18 评审修复 6 的
  同步移植。
- **继承自 L08 的语言面**：struct 脱糖（单构造子 enum `{Name}.mk`）、
  `new`、值级投影与卡住投影、多段投影链、字符串字面量与
  `string_concat`（**唯一的 builtin**：体是无名 `Tm::Prim`，求值读 env
  前两槽、全为字面量则拼接否则卡住，`mod.rs:742-752`）。无可变全局 /
  文件 IO / builtin 注册表——时代口径（A4-R2 登记）。
- **隐式实参逗号合写**：`f[A, B]` ≡ `f[A][B]`（`e2d04bb`，2026-09-19
  自 L11 形态回移植；命名隐式 `[A = x, B = y]` 与拖尾逗号同口径，
  展开的 Raw::App 链完全同构）。
- **重定义静默覆盖**：顶层 def / enum 重名不报 `redefine`（L13
  `fake_bind` 前传的 L07+ 检查未回灌本层，时代缺口）；构造子只以
  **裸名**经 `define` 登记（无 `Enum.case` 限定别名；struct 的 case
  名本身是 `{Name}.mk`）。
- **显示形态（A4-R3 定案）**：构造子值打印为 L09–L13 的 comma 血统
  `头名::分支名(实参, …)`（`pretty.rs:212`；终点章锚点
  `src/L13_namespace/legacy_tests.rs:604`、`src/L12_canonical/mod.rs:1479`）。
  L08 的 `.mk` 去重 + 实参空格连接是其**本地形态**，不随 L08→L09
  继承（A4-R2 曾向 L08 对齐，终门禁证明方向反了，已回滚）。卡住
  match 显示保留 `(unsolved match n)` 简形（`pretty.rs:226`，golden
  `golden_stuck_match_display` 锚定）；越哨兵的大下标 Var 显示
  `recursive_N`（`pretty.rs:119`）。`SumCase.typ` 非 Sum 头时沿 App
  链找头名、找不到退化 `?` 不 panic（`sum_head_name`）。

## 2. 核心数据结构：层级化全局表（无 decl 表）

- **登记分两路**。def / enum **本名**：`fake_bind` 把名字插入
  `src_names` 为 `(global_idx + 1919810, 类型)` 占位（`cxt.rs:111`），
  值进 `Infer.global: HashMap<Lvl, VTy>`（键 = `global_idx`，即登记时
  的表长，`elaboration.rs:393`）；项层引用是
  `Tm::Var(Ix(global_idx + 1919810))`（哨兵 `GLOBAL_BASE = 1919810`）。
  **构造子**：`Cxt::define` 登记——值进 env 的 define 槽，
  `src_names` 记 (局部层级, 类型)（`elaboration.rs:544-554`），不经
  global 表。
- **哨兵边界必须是 `>=`**：`lvl2ix` 对 `x.0 >= 1919810` 原样放行——
  0 号全局恰等于 1919810，用 `>` 会让首个声明的自引用走 `l - x - 1`
  下溢（`mod.rs:398-408`；off-by-one 修复见 `fd25b74`）。eval 的 Var
  臂越过哨兵查 global 表（`mod.rs:689-692`）；quote / rename 对越过
  哨兵的 Rigid 原样产出大下标 Var。
- **名字解析只走 `src_names`**（BiMap 名字 ↔ (层级, 类型)，`cxt.rs:14`）：
  `infer_expr(Var)` 一次查表同时覆盖局部 binder、define 槽与哨兵
  全局（`elaboration.rs:633`）。**global 表只存值，类型事实全在
  src_names**——这就是"按层级存、无名字键 decl 表"的完整含义，也是
  模式编译器（§3）取构造子类型必须绕道 `infer_expr(Var(名))` 的原因
  （L07/L08 有 `decl_get` 直查，本层没有同构物）。
- **递归 def**：`fake_bind` 占名 → global 表先插指向自身的卡住 Rigid
  `Val::vvar(global_idx + 1919810)` → 体检查 → 用真值覆盖同一条目
  （`elaboration.rs:393-405`；enum 本体 `503-511`）。值层无 unfold
  算子——global 表存的都是终值，故 L06–L08 fuel 的"decl 展开"烧点
  在本层无宿主。
- **卡住 match 是中性值，但无 pending splice**：eval 的 `Tm::Match`
  臂把 scrutinee force 后是构造子值即 `eval_aux` 首匹配选臂，否则整体
  卡成 `Val::Match(scrutinee, env, arms)`（`mod.rs:783-795`）。`v_app`
  对 Match **panic**（`mod.rs:641-657`）——"卡住 match 再被应用"是
  时代缺口（L07 起以值层 splice 实现了该特性；本层参考版与快版同崩 +
  parity 一致，模块头 `mod.rs:1-10`）。unify 的两个 η 臂已加
  `v_applicable` 守卫（`mod.rs:323-331`）：卡住 match / 字面量一侧与
  λ 比较时改判 Err 而非 panic。
- **force 只有两个展开臂**：Flex（meta 解）与 VSub（σ 推开，
  `mod.rs:486-499`）。没有 Match 重选、decl 展开、Prim 归约——精化
  传播进卡住 match 内部的机制不存在；match 的分支重选只发生在 eval
  的 Tm::Match 臂（σ 推开 scrutinee 后若是构造子值即选臂，frcs 对
  Match 只**推进 scrutinee**、捕获 env 只包裹，`mod.rs:584-592`）。
- **显式替换（`ccfcb87` 起）**：`Subst` 持久化单链（写入 O(1) cons、
  读取沿链扫描 + 条件包裹，`mod.rs:200-321`）、`Val::VSub` 包裹
  （`wrap_sub`，σ 空时零开销直通）、`frcs` 读点推开（槽位纪律 =
  L07 同款：spine / Sum / SumCase 槽只**包裹**不物化、闭包 env 逐槽
  包裹，`mod.rs:502-596`）、`force_arg`（合一器参数视角：逐层解包
  VSub、不推开精化、不做 Match 重选，`mod.rs:613-628`）。
- **燃料（有界降级）**：`UNIFY_FUEL = 4096`（`mod.rs:444-451`），唯一
  烧点是 frcs 的 Rigid 臂 lookup 命中（烧 1；耗尽按未解处理、返回裸
  rigid，`mod.rs:521-538`）；充值点 = unify_catch 入口 / nf /
  check_pm(_final) / 探测入口。A4-R2 的"六烧点无宿主"论证（§6.3）
  仍覆盖其余失控类；σ 精化传播读点是显式替换移植带来的唯一新增
  失控面。

## 3. 匹配编译器（pattern_match.rs，逐臂下钻）

2026-09-19 前本层用**决策树矩阵**编译 match（与 L10–L13 同族）。
`docs/l09l13-match-compiler-analysis-2026-09-17.md` 的算法级诊断定位
根因：同源负载上决策树比 L07/L08 的逐臂下钻慢约 20×，且差距全在
编译期（`filter_accessible_constrs` 占 elab 34%，其余是逐节点
quote / clone / 体检查开销）——常数优化拿不到量级，遂按 L07 蓝本
整体重写（`09b9ee8`，参考版 + 孪生同步），随后 `88242bc` 移植 L07
2026-09-18 评审修复轮（嵌套位置覆盖 P0、逐 ctor 独立充值、fuel 耗尽
保守判可达、SumCase 比头名）。

`Compiler::compile`（`pattern_match.rs:183`）对每个 match：

1. **顶层覆盖检查**：对 scrutinee Sum 的每个构造子跑
   `probe_accessible`，可达且无臂 `covers` → `Unmatched`（「构造子 +
   999 通配」形态）。不可达（`Vec[A] zero` 上的 `cons`）不报——索引
   方程不可解即结构上不可能出现。
2. **逐臂下钻**（保持用户书写顺序 = 运行时首匹配）：`walk_pat`
   （`:416`）绑定模式变量槽并构建运行时 `PatternDetail`。槽位纪律 =
   L07：枚举隐式参数用头部 Sum 实参实例化（不占槽）、构造子隐式
   绑定器缺省补虚通配、变量模式按用户名绑槽、Con 本身不占槽；
   `[p]` 隐式子模式支持。**构造子类型经 `infer_expr(Raw::Var(名))`
   取**（`:455`，src_names 一次查表，§2）。嵌套 Con 的字段位置记入
   `pending_pos`（两段式记账）。
3. **特化方程**：`check_pm_final`（`elaboration.rs:74`）解两条方程
   ——「模式作为表达式」≐ 期望类型、被匹配变量 ≐ 模式值（头部精化）
   ——解入显式替换 σ；本臂每层 Con 的「头部 ≐ 走查返回类型」方程在
   compile 内以 σ 作种子**补解结算**（`:253-283`），把走查槽位刚性
   链接进 σ——嵌套位置的延迟探测由此看到索引精化（如 `Vec[Nat]
   (succ zero)` 的尾部上 `nil` 不可达）。方程失败 = 荒谬臂，连同
   嵌套记账静默跳过。
4. **臂上下文**：`subst_cxt`（`cxt.rs:156`）把 env 槽与 src_names
   类型包 VSub，lvl / locals / pruning 不动——槽位布局（= 运行时
   布局）永不漂移。可解集 `bind_slots`（`cxt.rs:180`）解包 VSub 看
   **槽的原始形态**（嵌套 match 的入口上下文可能已被外层臂包裹；
   let 定义槽天然不在可解集）。
5. **分支体检查**：期望类型 quote → eval 重锚到臂上下文（flex 免锚；
   σ 经臂上下文的 wrapped env 在 eval 读点生效），spec 不穿参——
   常规转换不得解假设。
6. **嵌套位置覆盖检查（两段式）**：走查中只记 (路径, 字段 Sum, 本层
   ret)；本臂方程解出、σ 为终态后才提升为记账并延迟探测——字段走查
   时索引精化不在 σ 里，提前探测会把已精化下不可达的构造子误判
   可达。覆盖集 = 已走查臂的 PatternDetail 沿路径的结构贡献
   （`PosCover` / `cover_at`：var/Any 全覆盖、祖先异 ctor 不可达、
   同 ctor 前缀贡献其末端构造子，`mod.rs:105-138`）；可达集取各记账
   臂探测的并集。缺失报 `match 不完整：模式位置 {path} 缺少构造子
   {ctor}`（`fmt_path` 的 `cons#2 → nil#1` 路径形态，与 L07 同文案）。

**值级结构探测**（`probe_accessible`，`pattern_match.rs:84`）：构造子
类型 Π 链上枚举隐式参数用头部 Sum 实参实例化、其余绑定器用超出上下文
的 scratch 层 fresh rigid（同为刚性、可被方程解出；探测状态全在本地，
弃掉即回滚），返回类型再与头部 Sum 跑一次索引方程（`unify_indices`，
`:149`——头部一侧在前：两侧都是可解变量时解"头部变量 := 构造子侧
值"）。配套纪律：metas **整表 clone** 快照回滚（探测期解掉的已有 meta
可能引用循环内新建 meta，截断会悬空，`b0afe73`；孪生侧统一走
`run_pure_probe`）；**逐构造子独立充值**（多构造子枚举的逐 ctor 探测
不互相挤占共享燃料池）；**fuel 耗尽的失败按可达处理**（保守要求
覆盖——反方向会让深负载下的非穷尽 match 被静默接受）。

相对决策树的三处诊断收窄（换算法的语义代价，L10–L13 同款）：顶层
`Unmatched` 不再给出决策树的路径感知填充（用「构造子 + 999 通配」，
嵌套缺口改走 `fmt_path` 路径文案）；「某臂被前面臂遮蔽」只在**通配臂**
之后报 `Unreachable`（重叠臂的 usefulness 检查未移植）；荒谬臂特化
失败静默跳过。

运行时：`eval_aux`（`pattern_match.rs:354`）按模式**首匹配**选臂
（Any/Bind 整体绑定、Con 同名逐字段下钻、异名构造子臂跳过）；
`covers` / `is_catch_all`（`:546-563`）判臂对构造子的结构覆盖与通配。

## 4. 性能孪生（`bump_spine_iter.rs`）

L08 冠军配方（bump arena + 打包值 + 迭代内核 + 复合环境 + 记忆化 +
`Tycker` 稳态复用）的移植（`2a949ef`），加同族 perf 线同步（spine
链头种类 `Entry.hk` `00d5b3d`、env 槽单趟收集 `fd54399`、Sum/SumCase
装配单缓冲 `4fa054a`、RenBuf 高水位克隆 `7000902`）。L09 自己的增量：

- **宇宙层级进打包值**：tag 3 从立即数改携带层级（`V = lvl<<3|3`，
  61 位余量）——`Type N` 无需为层级另开 XCell。
- **全局名字搬 Machine**（`8101e8c`，perf-debt P2）：`globals: Vec<V>`
  （下标 = global_idx，递归占位先压后覆盖，与参考版 global 表同构）+
  `global_names: FxHashMap<SmolStr, (u32, V)>`（顶层 define 的 名字 →
  (层级, 类型)，append-only、**不随 Cxt 克隆**——旧设计把 define 累积
  进 Cxt 名字快照、每 binder 克隆整表 O(D²)）+ `neutral` 中性视图缓存
  O(1)（卡住 match 分支重求值的 avoid_recursive 视图）。轮界
  `clear_round` 全清（对应参考版每次 run 新建 Infer）。
- **builtin 只有 `string_concat`**：无名 `Tm::Prim` 读 env 前两槽；
  `Val::Prim` 是**无 spine 裸标记**（v_app 对它 panic，永无 Prim 头
  的链——L08 fuel 的 Prim 归约烧点在本层无宿主的孪生侧证据）。
- **env 口径机器**：`force_v` / `quote` / `eval` 不带 cxt（上下文状态
  在 `Cxt<'a>`，值内核只吃 env）。模式编译器的孪生版（`compile` /
  `walk_pat` / `probe_accessible` / `unify_indices` /
  `covers` / `is_catch_all`，`:6002-6446`）与参考版逐点同构，探测快照
  统一走 `run_pure_probe`（metas 整表 clone 换入换出，`:5122`）。
- **显式替换 + 评审修复逐点同步**（`ccfcb87`、`88242bc`、`09b9ee8`）：
  `SubstV` / `XCell::VSub` / frcs / `SpecSolve` / `subst_cxt`（`:5192`）
  与参考版同构；σ 跨轮回收 = `wrap_sub` 登记 `Rc::as_ptr` 进
  `VSUB_REGS`（thread_local）+ 轮界 `vsub_reclaim`（`clear_round` 与
  `run_decls` 出口 guard 严格伴生，`:7170-7183`）——L07 2026-09-18
  同款机制的移植，`fast_substv_reclaimed_across_rounds` 钉住
  （`SUBSTV_ALIVE` 计数连跑两轮后回落基线）。

Ok 输出与参考版**逐字节一致**。已知偏差仅错误消息内容：快版错误里
内嵌的 Debug-Val/Tm 的名字 Span 全零（参考版携带源码偏移），parity
比对前按 `start_offset/end_offset/path_id` 归一化。

## 5. 基准

```text
cargo run --release --bin l09bench -- --workload all --max-k 11
```

负载族（`src/bin/l09bench.rs` 头注）：L08 全家桶去掉 `global`（builtin
只剩 `string_concat`，无可变全局）+ L09 宇宙特色负载 `universe`（固定
宇宙塔 `Type 1 = Type 0`、`Type 2 = Type 1 -> Type 0`、高宇宙 enum
`HighLvl`，+ 2^(k+1) 层 `def c{i} : Type 2 = Type 1 -> Type 0` def
链——每层一次 `check_universe` 的 Pi 规则判定 + global 登记）。nf 节
点数闭式：church = 2n + 4、strchain = 1、struct = 2；match / enum /
universe 无闭式，以双实现互检代替。

矩阵数据（`docs/bench-matrix-2026-09-18.md` §3 的 L09 行；隔离进程、
`--max-k 11`（`enum` 取 k=9）、`--rounds 3`、每格 min；Windows 10，
release）：

| 负载 | k | basic (ms) | fast_ss (ms) | basic/fast_ss |
|---|---|---|---|---|
| church | 11 | 4.464 | 0.331 | 13.5× |
| strchain | 11 | 2717.255 | 3.105 | 875.1× |
| match（移植前） | 11 | 2.163 | 0.966 | 2.2× |
| enum（移植前） | 9 | 13.268 | 1.619 | 8.2× |
| struct | 11 | 4506.220 | 3.791 | 1188.7× |
| universe | 11 | 3271.889 | 1.763 | 1855.9× |

**逐臂下钻移植后**（`09b9ee8`，2026-09-19 补测，同文档 §0 / §0.1）：

- **match**：参考版 basic 2.175 → 0.570 ms（3.8×），孪生 fast_ss
  0.457 → 0.048 ms（9.5×）。孪生对参考的领先从首测的 2.2× 扩大到约
  一个量级（矩阵 §0 表记 0.11×，与 L10–L12 同档）；分析文档 §0.0 记
  9.6×（2.215→0.576 / 0.469→0.049）——窗口间绝对数漂移、比值一致。
- **enum**：**两侧都能跑**且快 ~10×（basic 13.268 ms / 孪生移植后
  1.37 ms）。首测"enum 孪生判型失败"是 L11/L12 的事，本层从未不可跑
  （首测 13.3 ms）。
- 其余负载 0.96–1.07×（只换了 match 编译器，非 match 路径不变）。

**参考引擎地板（诚实清单）**：本层参考版的非 match 负载本就系统性慢
L10 参考版 2.5–4.5×（分析文档 §0.0 的定位），match 移植后的参考版
残差同源。表中 basic 列的大比值（strchain 875×、struct 1189×、
universe 1856×）以这个更慢的参考版为基数，跨层比较应以 L10 行为
参照；成因与参考版 `Cxt::define` 逐 decl 克隆 `src_names`（名字表
不搬出上下文，孪生侧已由 `global_names` 规避，§4）相关的部分**未
单独测量核实**。

## 6. 已知限制（诚实清单）

1. **卡住 match 不可再被应用**：`v_app` 对 `Val::Match` panic；合法
   源码（打印引用自递归卡住 match 的函数值）可触发，参考版与快版
   同崩 + parity 一致，属时代缺口而非缺陷。修复需实参吸收并参考版 +
   快版同步大改，刻意不修（模块头 `mod.rs:1-10`）；η 臂的
   `v_applicable` 守卫已把"卡住 match / 字面量与 λ 比较"改判 Err。
2. **无 Match 重选 / decl 展开 / Prim 归约 / struct_eq 快路径**：force
   只有 Flex + VSub 臂，卡住 match 恒卡住；`unify(Match, Match)` 的
   分支体在**中性 global 克隆**下重求值（`avoid_recursive` 全局 →
   rigid 封口，`unification.rs:354-361/733-741`），与 L07/L08 的
   `struct_eq` 结构快路径不同构（A4-R2 登记，刻意分歧）。
3. **fuel 的适用面（A4-R2 论证 + 显式替换后的现状）**：L08 fuel 的
   六个烧点中五个在本层无触发面——① meta 解链间接环（solve 的
   rename 带 `occ: Some(m)` 做逐 meta occurs check，解链无环）；
   ② pm_defs 精化展开（grep 0 命中）；③ Match 重选；④ decl 展开
   （global 存终值、值层无 unfold）；⑤ Prim 归约（Prim 无 spine）。
   给这些路径加护栏属不可触发的死代码，且 L08 fuel 耗尽有可见行为
   （`(fuel exhausted)` 诊断、unify fuel=0 判 Err），盲加有 Ok→Err
   行为变更风险。唯一新增失控面是 σ 精化传播读点（`ccfcb87` 起），
   已以 `UNIFY_FUEL` 4096 有界（§2 末条）。注意：孪生模块头的
   "unify 无燃料"一行写于该移植之前，现状以本条与 §2 为准（源码
   注释待更新，本轮只改文档）。
4. **重定义静默覆盖**（§1 已述）：顶层 def / enum 重名后定义覆盖
   `src_names` 与 global 表条目，无 `redefine` 定向报错；构造子裸名
   跨 enum 重复按最后注册解析。
5. **显示形态刻意分歧**（A4-R3 定案，不修）：comma 血统 +
   `(unsolved match n)`；与 L08 的 `.mk` 去重形态互不继承。
6. **深值路径未做迭代化**：L07/L08 的 2026-09-18 深值栈安全轮
   （occurs / 结构比较 / rename 的工作栈化与 σ 回收之外的其余项）
   未移植本层；`quote` / `pretty` / 深值的递归 Drop 仍是按值深度的
   递归路径。parity 与 bench 都在大栈线程里跑（parity 256 MB、bench
   `L09_STACK_MB` 默认 128 MB），常规负载不触界；深值压测未做，
   具体边界**未核实**。
7. **pending σ 的跨轮回收已落地**（非缺口，防误报）：孪生 arena 内
   `XCell::VSub` 持有的 `Rc<SubstV>` 克隆曾被 bump reset 跳过 Drop
   （跨轮慢泄漏）——`VSUB_REGS` 登记 + 轮界归还已修（§4 末条）。

## 7. 测试

- `cargo test --test l09_fast_parity`：`#[path]` 独立 crate（只编
  list / bimap / parser_lib / L09_mltt，不含 LSP 与其它章节），
  **29 个 `#[test]`**，判据 = Ok 输出逐字节一致 / Err 判定一致
  （错误正文经 span 归一化——剥 `start_offset/end_offset/path_id`
  ——后也逐字节比对）：
  - parity 主力 14：基础与索引族（`parity_tests_rs_basic` / `_index` /
    `_dependent_match`）、宇宙层级（`parity_universe_levels`：`Type N`
    分层 / 高宇宙 enum / 依赖类型参数）、λ 演算、等式推理
    （`parity_eq_reasoning` / `parity_eq_proofs`）、卡住 match、
    递归定义与哨兵自引用（`parity_recursive_defs` /
    `parity_global_sentinel_self_ref`）、非线性 pruning 反转掩码、
    嵌套模式、洞与 let、错误用例；
  - golden 显示形态 6：字符串字面量与拼接、Nat/Bool 构造子值、
    struct mk 值与投影、宇宙与卡住 prim、递归 add/even、
    `golden_stuck_match_display`（`(unsolved match n)` 锚定）；
  - L08 血统契约 4：`parity_struct_new_projection_l08_heritage`
    （struct / new / 多段投影 `l.a.x` + 依赖字段 `Dd[P]`）、
    `parity_ctor_value_print_shape`（comma 血统 + `sum_head_name`
    降级不漂移正常输出）、`parity_struct_dependent_field_projection`、
    `parity_enum_struct_impl_hole_pinned_u0`；
  - 孪生机制钉 3：`fast_substv_reclaimed_across_rounds`（σ 跨轮
    回收）、`deep_workloads_parity`（church / strchain / match /
    enum / struct 全负载的 nf 节点数闭式互检 + Ok 互检）、
    `steady_state_reuse`（同一 Tycker 连续多轮 = 每轮新建）；
  - 评审回归 2：`parity_review_fixes_2026_09_18`（嵌套覆盖缺口两版
    同 Err 且文案与 L07 逐字同款、补臂后 Ok、构造子良构性、SumCase
    头名检查的正向对照）、`parity_stale_solvable_order_independent`
    （臂序无关：荒谬臂静默跳过后覆盖仍完备，臂交换两序输出一致）。

  随 `#[path]` 编入本目标的还有模块内 5 个 lib 用例（即下条的 lib
  全部），计入总运行数（L08 §8 同款结构；确切总数以 cargo test 输出
  为准，本轮未跑）。
- `cargo test --lib L09_mltt`：**5 个**（`mod.rs` 的 `test1` /
  `test2`——DEMO 全串：宇宙塔 `HighLvl` / `HighLvl2` / `HighLvl3`、
  `Eq` 教学编码、`Bits` struct 与 `refl` 传递；`parser/mod.rs` 的
  `test` 与 `test_bad_decl_reported_prefix_kept`——resilient 解析：
  坏 decl 报错且保留前缀；`parser/lex.rs` 的 `test`）。大栈线程。

## 8. 参考资料

- 本仓库 `src/L07_sum_type/README.md`（显式替换精化与逐臂下钻的蓝本）、
  `src/L08_product_type/README.md`（struct / new / 投影的出处）；
- 跨章节连贯性评审 A4：`docs/review-continuity/a4-r1.md`、`a4-r2.md`
  （继承面 / 显示形态 / 时代缺口的登记与裁决）；
- `docs/l09l13-match-compiler-analysis-2026-09-17.md`（决策树 → 逐臂
  的算法级诊断与五层移植记录）；
- `docs/bench-matrix-2026-09-17.md` / `docs/bench-matrix-2026-09-18.md`
  （本层全部基准数字的来源）；
- [elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo)
  （MLTT 教学章：宇宙层级 + 和类型 / match 的切片原型）。
