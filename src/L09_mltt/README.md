# L09：MLTT 切片（`Type N` 分层宇宙 + 和类型 / match）

本层是**再定基层**：以 MLTT 教学章（宇宙层级 + 和类型 / match）为基底
重写内核，非逐行继承 L08 代码。与 L06–L08 的 decl 表世界有系统性不同——
def / enum 的**名字**按大下标哨兵层级进 `Infer.global` 值表，没有名字键
decl 表；构造子则走 `Cxt::define` 的 env define 槽（§2）。相应地，模式
编译器取构造子类型走 `infer_expr(Var(名))` 而非 decl 直查——这是与
L07/L08 及 L10–L13 的关键结构差异。继承面与已知分歧在跨章节连贯性评审
A4 登记（锚点见 `docs/archive/review-continuity/a4-r1.md`、`a4-r2.md`；其中
部分登记已被后续移植轮取代，以 §2/§6 的现状描述为准）。

2026-09 的两条主线：

- **精化载体显式替换**（`ccfcb87`）：`Subst`（持久化单链）+ `Val::VSub`
  + `frcs` 读点推开 + `SpecSolve` 穿参，与 L07 蓝本逐点同构；
- **匹配编译器逐臂下钻**（`09b9ee8`，2026-09-19）：决策树矩阵 → L07
  口径的逐臂实现（参考版 + 孪生同步，L10–L13 随后跟进），match 负载
  孪生 9.5×、参考版 3.8×（§5）。

**2026-11-11 参考版加固回灌（本轮）**：参考版补齐 L07 的 P1–P11 适用子集，
此前登记为"时代缺口"的以下各项已落地（孪生版本轮**未**移植，见 §6）：

- **深值栈安全（P11 + 09-18 深值轮）**：`quote` 改迭代 `quote_deep`
  （Frame 显式任务栈 + `InlineStack`）、`rename` 改 `rename_deep`
  （Sum/SumCase/Obj 深链帧式收集）、`val_mentions_lvl` 迭代化、`pretty`
  加 `MAX_DEPTH` 定深截断；新增 `struct_eq.rs`（`EqTask`/`InlineStack`
  迭代结构相等 + 预算），并接回 `unify(Match, Match)` 结构快路径
  （中性 global 视图保留为 fallback）。
- **卡住 match 的 pending splice（L07 S1）**：`Val::Match` 恢复第 4 字段
  `Rc<Vec<(Rc<Val>, Icit)>>`，`v_app` 从 panic 改为累积实参、分支选中后
  在值层逐个应用；`force`/`quote`/`rename`/`unify`/`struct_eq` 全链适配。
- **P2 卡住 match 比较总预算**：`MATCH_CMP_BUDGET = 64`（每顶层合一入口
  一份，结构快路径之后计数）。
- **P3 三档诊断**：`UnifyKind{Absurd, Undecided, Fuel}` + `Infer` 上
  `unify_kind: Cell`，失败臂按 L07 口径 note；覆盖探测对 `Undecided`
  保守判可达（不再把"判不出"当"分支不可达"）。
- **P5 跨 meta 环守卫**：`meta_expanding: RefCell<Vec<MetaVar>>`，`force`
  展开已解 meta 时压栈、同 meta 再现返回卡住 Flex（L09 原实现无 fuel 也无
  守卫，跨 meta 环会栈溢出）。
- **P0-2 判定**：L09 的探测回滚不走整表 `meta.clone()` 的路径，暂不引入
  undo-log（记录为 N/A）。
- **P8 / P1-2 判定**：依赖 decl 表（L09 无名字键表 / 无 registered-prim
  守卫面），记录为 N/A。

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
- **重定义报错（2026-11-13 从 L07/L08 继承）**：顶层 `def` / `enum` 重名
  （含撞 `Cxt::new` 内建、撞构造子裸名）→ `redefine {名}` 定向报错，
  不再静默覆盖；顺序与 L07/L08/L13 一致（先检查类型、后查重定义）。
  构造子只以**裸名**登记（无 `Enum.case` 限定别名；struct 的 case
  名本身是 `{Name}.mk`）——这条与 L08 相同。
- **显示形态（A4-R3 定案）**：构造子值打印为 L09–L13 的 comma 血统
  `头名::分支名(实参, …)`（`pretty.rs:212`；终点章锚点
  `src/L13_namespace/legacy_tests.rs:604`、`src/L12_canonical/mod.rs:1479`）。
  L08 的 `.mk` 去重 + 实参空格连接是其**本地形态**，不随 L08→L09
  继承（A4-R2 曾向 L08 对齐，终门禁证明方向反了，已回滚）。卡住
  match 显示保留 `(unsolved match n)` 简形（`pretty.rs:226`，golden
  `golden_stuck_match_display` 锚定）；越哨兵的大下标 Var 显示
  `recursive_N`（`pretty.rs:119`）。`SumCase.typ` 非 Sum 头时沿 App
  链找头名、找不到退化 `?` 不 panic（`sum_head_name`）。

## 2. 核心数据结构：全局值表（id 键，无名字键 decl 表）

- **两层表**：`Infer.global: FxHashMap<Lvl, VTy>`（键 = `global_idx`，值为
  终值；递归 def 在体检查期间先放 `Val::vvar(global_idx + 1919810)` 占位、
  检查完覆盖）+ `Infer.global_names: FxHashMap<String, (Lvl, Rc<VTy>)>`
  （真名 → (哨兵层级, 类型)，append-only、不随 Cxt 克隆）。**名字键的 decl
  表不存在**——L07/L08 的 `decl_get` 直查在本层的等价物是「名字 →
  `global_names` → 哨兵层级 → `global` 表」两次 O(1) 查。
- **顶层声明不占类型检查上下文（2026-11-12 载体切换）**：`define_global`
  只写上面两张表（+ `shadow_local`），**不再** `env.prepend` / `lvl+1` /
  `locals::Define` / `pruning.prepend(None)`。因此 `Cxt` 的
  env/lvl/locals/pruning 长度只随**局部 binder** 增长。旧设计随声明数 D
  增长：全局引用按 de Bruijn 下标在 Rc 单链 env 上 `iter().nth` 线性找
  （每次 O(D)）、`fresh_meta` 的 `close_ty(&cxt.locals, …)` 要包 D 层 Let
  并重求值（每次 O(D²)），strchain/struct/Eq 证明阶梯因此超线性（诊断与
  实测见 `docs/l09-perf-gap-2026-11-12.md`）。
- **项层引用两种编码**：已定名全局 → `Tm::Global(Ix(global_idx +
  1919810))`；递归定义体检查期间的**自身占位**引用 → `Tm::Var(Ix(global_idx
  + 1919810))`（旧 `fake_bind` 哨兵，代码里以 `in_progress_globals` 集合
  区分）。`eval` 的 Var 臂**先判哨兵**直查 `Infer.global` O(1)，不扫 env。
  中性全局视图（quote/rename/Match 合一的分支体重求值）只中和
  `Var(哨兵)`（递归占位），`Global` 照常展开——与旧版「哨兵 vs env 槽」的
  两分法逐点一致（`Tm::Global` 对应旧版的 env 槽引用语义，parity/黑盒
  文案逐字节对齐）。
- **哨兵边界必须是 `>=`**：`lvl2ix` 对 `x.0 >= 1919810` 原样放行——
  0 号全局恰等于 1919810，用 `>` 会让首个声明的自引用走 `l - x - 1`
  下溢（`mod.rs` 的 `lvl2ix`；off-by-one 修复见 `fd25b74`）。quote /
  rename 对越过哨兵的 Rigid 原样产出大下标 Var。
- **名字解析两表**（`src_names` 局部 + `global_names` 全局）：`infer_expr(Var)`
  先查 `cxt.src_names`（BiMap 名字 ↔ (层级, 类型)：`Cxt::new` 的两个内建 +
  当前 def 内的 binder/let，局部优先遮蔽），回落 `global_names`。
  **global 表只存值，类型事实在两张名字表**；模式编译器（§3）取构造子
  类型仍绕道 `infer_expr(Var(名))`——与 L07/L08 的 `decl_get` 两次 O(1)
  查等价（历史注：载体切换前构造子类型取出还要付上下文线性代价）。
- **递归 def**：`fake_bind` 占名（插入 `global_names` 哨兵层级 + 标记
  `in_progress_globals`，不改 Cxt）→ global 表先插指向自身的卡住 Rigid
  `Val::vvar(global_idx + 1919810)` → 体检查（自身引用编成
  `Tm::Var(哨兵)`）→ `define_global` 用真值覆盖同一条目、登记哨兵名字、
  移出 in_progress（enum 本体 / 构造子同路）。值层无 unfold 算子——
  global 表存的都是终值，故 L06–L08 fuel 的"decl 展开"烧点在本层无宿主。
- **卡住 match 是中性值，pending splice 已回灌**：eval 的 `Tm::Match`
  臂把 scrutinee force 后是构造子值即 `eval_aux` 首匹配选臂，否则整体
  卡成 `Val::Match(scrutinee, env, arms, pending)`。`v_app` 把后续实参
  累积进 `pending`（值层保存；项层 splice 会把实参自由变量引到错误
  上下文），分支选中后逐个应用——与 L07 S1 同构。`v_applicable` 守卫
  继续把"卡住 match / 字面量与 λ 比较"改判 Err 而非 panic。
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

- **参考版 ↔ 孪生载体对齐（2026-11-12）**：参考版把全局值/名字搬出 Cxt
  （`Infer.global` 值表 + `global_names` 名表 + `Tm::Global` 哨兵直查），
  与孪生的 `globals: Vec<V>` + `global_names` 同构。此前参考版把顶层声明
  做成上下文条目（env/lvl/locals/pruning 随 D 增长），strchain/struct/Eq
  证明阶梯是 O(D²)；载体切换后参考版回到 L07/L08 量级（§5）。
- **`Tm::Lam/Pi` 体 Rc 表示（2026-11-13 从 L07/L08 继承，G3）**：参考版
  `Tm` 的 λ 体与 Π 域/余域由 `Box` 改 `Rc`（与 L07/L08 一致）。借用版
  `eval_ref` 建 `Closure` 只需 `Rc::clone`，不再深拷整棵体项；`quote`/
  `rename`/`lams_go`/`struct_eq`/`tm_size`/孪生 CTm 导出逐点同步。语义
  零变化（parity 46/82 绿），但 common/church/natadd 的常数差距随之抹平
  （§5：载体切换后 common 96.5 → **67.1 ms**，与 L07/L08 持平）。
- **`Val` 名字 span 句柄化（2026-11-13，`VSpan = Rc<Span<String>>`）**：
  `Val` 的构造子/绑定器/投影字段名等 5 类 span 由 `Span<String>` 改为
  `Rc` 句柄（`Deref` 保持 `.data`/显示透明；跨表示比较只看名字；`Debug`
  与内层 `Span<String>` 同形以保 parity 错误正文）。动机：common ladder
  单文件 **1.17M 次 Val 克隆**（SumCase 666k/Sum 303k/Lam 192k），每次
  克隆旧实现都复制一个名字 String；句柄化后只是引用计数递增。收益：
  common 67.1→**50.4 ms（−24.9%）**、strchain −17.6%、natadd −21.0%、
  struct k10 −20.8%、match −13.6%、enum −6.3%、universe −9.0%（church
  持平），见 `docs/l09-value-span-rc-2026-11-13.md`（含同轮否决的
  `rc_take` unique-move 实验：实测 ≈0，rc_take 仅 1405 次/轮）。

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

矩阵数据（**2026-11-13 最终复测**：载体切换 + `Tm::Lam/Pi` Rc + `Val`
名字 span 句柄化后；隔离进程、`--max-k 11`（`enum` 取 k=9）、`--rounds 3`、
每格 min；Windows 10 release；参考版 `basic`）：

| 负载 | k | L09 参考版 basic (ms) | L07 | L08 | L09/对照 |
|---|---|---|---|---|---|
| church | 11 | 1.427 | 1.307 | 1.323 | 1.09× / 1.08× |
| strchain | 11 | 7.494 | 7.100 | 7.805 | 1.06× / 0.96× |
| match | 11 | 0.093 | 0.094 | 0.095 | 0.99× / 0.98× |
| enum | 9 | 0.215 | 0.173 | 0.176 | 1.24× / 1.22× |
| struct | 10 | 5.117 | — | 4.967 | 1.03× |
| universe | 11 | 4.006 | — | — | — |
| natadd | 11 | **2.704** | 2.763 | 2.828 | 0.98× / 0.96× |

> L07/L08 列是**同族但各自生成器**的数字（L09 后来也把 VSpan 合入了
> L07/L08，见 `docs/bench-crosslayer-vspan-2026-11-13.md`）；严格同文件
> 对照看下方真实语料表。L09 与 L07/L08 在 common 上已同水位（50.3 vs
> 50.9/51.1 ms），残差为 enum 1.24×、church/strchain 1.06–1.09× 与 Eq 阶梯
> 1.12×（宇宙/构造子检查的固定常数）。

`strchain` k=9→12 曲线 1.90 / 4.01 / 8.93 / 21.2 ms（≈线性，与 L07/L08
一样只剩 `string_concat` 负载本身的 O(n²) 字节拷贝；句柄化后 k=11 绝对值降到
7.49 ms）。

真实语料与跨层对照（`realbench --rounds 3 --only basic`，min；
`target/perf09/crosslayer_vspan/after/`）：

| 口径 | 载体切换前（2026-11-12） | 最终（2026-11-13） | 加速 | 同窗口对照 |
|---|---:|---:|---:|---|
| L09 自有语料整目录（34 文件） | 1763.7 ms | **8.68 ms** | **203×** | — |
| Eq 证明阶梯单文件（801 decls） | 1678.5 ms | **2.66 ms** | **630×** | L07 2.38 / L08 2.38（**1.12×**） |
| common 6 文件（L07 风格代码） | 115.3 ms | **50.35 ms** | 2.29× | L07 50.87 / L08 51.14（**0.99× / 0.98×**） |

> 历史注：`docs/bench-matrix-2026-09-18.md` 的 2717ms（strchain）/4506ms
> （struct）/3271ms（universe）等是 2026-09-20 `866f23e5` 修复前的旧机数据，
> 只可作历史；`参考引擎地板`（旧版 §5 末段）已随 2026-11-12 载体切换、
> 2026-11-13 `Tm` Rc 继承与 `Val` 名字 span 句柄化（随后也合入 L07/L08）
> 消除——**L09 与 L07/L08 现已同水位（common 差 ≤1%）**，不再有链条上的
> 性能断层。

**仍存的常数级差距**（都不构成数量级问题）：enum 1.24×（固定小源的宇宙
层级/构造子检查常数）、Eq 阶梯单文件 1.12×（宇宙/构造子检查每 decl 的成本）、
church/strchain 1.06–1.09×（固定常数）；内建 `string_concat` 仍走普通 β +
`Tm::Prim`（无 PrimFunc/eta，但 strchain 句柄化后已 0.96× L08）。这些不值得
再引入 PrimFunc/eta 或牺牲 A4-R2 的宇宙/fuel 论证（见
`docs/l09-carrier-switch-2026-11-12.md` §6、`docs/l09-value-span-rc-2026-11-13.md`
与跨层对比 `docs/bench-crosslayer-vspan-2026-11-13.md`）。


## 6. 已知限制（诚实清单）

1. **卡住 match 已可再被应用（2026-11-11 回灌）**：`Val::Match` 带第 4
   字段 pending，`v_app` 累积实参、分支选中后在值层应用；参考版不再
   panic。**孪生版未移植**（其 `XCell::Match` 仍是 3 字段 + 原 panic
   路径）——两版在该行为上按文档化不对称处理，parity 对该族只钉参考版
   行为。
2. **struct_eq 快路径已回灌；Match 重选 / decl 展开 / Prim 归约仍无宿主**：
   force 仍只有 Flex + VSub 臂（卡住 match 恒卡住；进 match 内部靠 σ 推开
   scrutinee 后 eval 重选）；`unify(Match, Match)` 现在**先走 struct_eq
   迭代结构快路径**（EqTask + 预算），失效后回落到中性 global 克隆重求值
   （原路径保留，与 L07 同构）。decl 展开/Prim 归约在本层无宿主（global
   存终值、Prim 无 spine），维持 A4-R2 论证。
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
4. **显示形态刻意分歧**（A4-R3 定案，不修）：comma 血统 +
   `(unsolved match n)`；与 L08 的 `.mk` 去重形态互不继承。
5. **深值路径已迭代化（2026-11-11 回灌）**：`quote` / `rename` /
   `val_mentions_lvl` / `struct_eq` 走迭代实现、`pretty` 定深截断；
   L07 的深值回归（10 万层 succ 链、默认栈）在参考版通过。仍为递归的：
   深值 `Drop`（按值深度递归，未做 L13 式迭代 Drop）——parity/bench 的
   大栈线程（256 MB / `L09_STACK_MB` 128 MB）继续兜底。**孪生版未移植
   深值轮**（本轮只做参考版），深值负载在孪生上仍可能爆栈。
6. **pending σ 的跨轮回收已落地**（非缺口，防误报）：孪生 arena 内
   `XCell::VSub` 持有的 `Rc<SubstV>` 克隆曾被 bump reset 跳过 Drop
   （跨轮慢泄漏）——`VSUB_REGS` 登记 + 轮界归还已修（§4 末条）。

> 已从 L08 继承、不再列为缺口的项：重定义报错（2026-11-13）、
> `Tm::Lam/Pi` 体 `Rc` 表示（2026-11-13，G3）、struct_eq / pending /
> P2/P3/P5 / 深值轮（2026-11-11 回灌）。L09 时代刻意保留的差异只有
> 语言面裁剪（无可变全局 / 文件 IO / builtin 注册表，A4-R2 登记）与
> 显示形态（A4-R3）——这两项属章节设计，不是链断裂。

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

  随 `#[path]` 编入本目标的还有模块内 **17** 个 lib 用例（即下条的
  lib 全部），计入总运行数：`cargo test --test l09_fast_parity` 实测
  **46 passed / 0 failed**（29 自有 + 17 lib）。
- `cargo test --lib L09_mltt`：**17 个** = 原有 10（`mod.rs` 的
  `test1` / `test2` 与 5 个 pm 负例、`parser/mod.rs` 的 `test` 与
  `test_bad_decl_reported_prefix_kept`、`parser/lex.rs` 的 `test`）
  + 2026-11-11 回灌回归 7（`deep_value_iterative_under_default_stack`、
  `cross_meta_cycle_force_is_bounded`、
  `test_unify_kind_separates_absurd_from_undecided`、
  `test_stuck_match_splice`、`test_stuck_match_applied_with_outer_binder`、
  `test_stuck_match_equation_bounded`、
  `struct_eq_compares_match_pending_values`）。实测 17 passed。
- `cargo test --test l09_blackbox`：**65 个黑盒用例**（2026-11-11 新增，
  10 个家族：输出/显示契约、求值/递归/高阶、和类型/索引/GADT、struct/new
  脱糖、Type N 宇宙、构造子良构/重定义、覆盖诊断、错误/span、解析恢复、
  负向事实）；随 `#[path]` 带入 17 个 lib 用例 → 实测 **82 passed / 0 failed**。

## 8. 参考资料

- 本仓库 `src/L07_sum_type/README.md`（显式替换精化与逐臂下钻的蓝本）、
  `src/L08_product_type/README.md`（struct / new / 投影的出处）；
- 跨章节连贯性评审 A4：`docs/archive/review-continuity/a4-r1.md`、`a4-r2.md`
  （继承面 / 显示形态 / 时代缺口的登记与裁决）；
- `docs/l09l13-match-compiler-analysis-2026-09-17.md`（决策树 → 逐臂
  的算法级诊断与五层移植记录）；
- `docs/bench-matrix-2026-09-17.md` / `docs/bench-matrix-2026-09-18.md`
  （本层历史基准数字的来源；2026-09-20 前的旧机数据）；
- `docs/l09-perf-gap-2026-11-12.md`（参考版 vs L07/L08 的差距定位与
  G1/G2 根因）与 `docs/l09-carrier-switch-2026-11-12.md`（2026-11-12
  载体切换：全局移出 Cxt、`Tm::Global` 三态编码、A/B 验收）；
- [elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo)
  （MLTT 教学章：宇宙层级 + 和类型 / match 的切片原型）。


## 7. struct 模式支持与已知精化缺口（2026-11-15）

- p_pattern 已补齐与 L08/L11–L13 同款的 struct 模式糖：case Boxed { p1, p2 }
  解析为 Boxed.mk(p1, p2)（struct 脱糖后 case 名即 Name.mk）。简单 struct
  解构（字段为变量）可正确求值；ill-typed 的"返回尾部变量"用例会正确拒绝
  （can't unify Vec[A, succ _l] == Vec[A, _l]）。
- 已知缺口：两字段交叉索引精化仍不完整——L13 probe 的 weak03 输出
  (unsolved match …)（卡住值，语义未落实），weak05 被误拒
  （match 不完整：模式位置 VecHolder.mk#2 缺少构造子 fsucc），与 L10–L12
  同族。根因是 check_pm_final 对"第一字段精化改变第二字段索引"的跨字段
  传播缺失（L13 的 2026-09-29 修复未回灌）。行为矩阵与翻转条件见
  tests/gadt_refine_cross_layer_tests.rs。
- eval/eval_ref 的 match 入口在"无臂命中"时不再 unwrap panic，改为保留
  Val::Match 卡住值（与 L11/L12 同款；此前 struct 模式会触发 panic）。
