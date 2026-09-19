# L07：和类型与依赖模式匹配

本层是 07 章的重写版，合并了原先拆开的 `L07_sum_type`（和类型）与
`L07a_depend_pm`（依赖模式匹配）两部分：一份实现同时覆盖 enum 声明
（类型参数、索引、GADT 返回类型）与 `match`（嵌套模式、索引精化、
覆盖性检查、卡住的 match 作为中性值参与类型检查 / 求值 / 合一）。

本版是**按理论正向重构**的实现：先把依赖模式匹配的正确机制想清楚
（specialization by unification），再映射到 NbE 的值表示上。旧实现
（"改写 env 槽 + 刷新上下文"式精化）的 bug 族——add_assoc 一类的
meta 解槽位错位——在新架构下**按构造排除**，不再是逐案修补。

---

## 1. 正向设计：依赖模式匹配应该怎么写

### 1.1 理论

依赖模式匹配的标准构造（Coquand '92；Cockx & Abel《Elaboration of
dependent pattern matching》的 specialization by unification）：在
scrutinee 类型 `D p̄ ī` 上匹配构造子 `c`，等价于解一组**特化方程**——
构造子返回类型的索引 ū 与头部索引 ī 合一。这个合一：

- **解得出** ⇒ 分支可达，且解 `x := v`（子句变量 := 值）就是**精化**；
- **结构冲突** ⇒ 分支不可能（absurd），不计入覆盖；
- 全部构造子都不可达或被覆盖 ⇒ 覆盖性。

可达性、覆盖性、精化由**同一套机制**给出，不需要三段各自的代码。

### 1.2 映射到 NbE：三条纪律

**纪律一：模式变量一律刚性。** 构造子的所有绑定器（含隐式）各占一个
env 槽、绑定为 fresh rigid，与运行时 `eval_aux` 的 prepend 严格同序同数。
通配的隐式（`cons[_](x, xs)` 里没写的 `l`）是"模式变量"而非存在量词，
不再像旧实现那样用 fresh meta 充当——meta 会参与 invert/prune，把
模式匹配的约束问题搅进元变量求解里。

**纪律二：特化解是显式替换（explicit substitution），不是上下文改写。**
方程的解 `len := succ l`、`a := zero` 只是 `Compiler::sub: Rc<Subst>`
（持久化单链，链头 = 最新）里的一条记录，由 `Subst::extend` O(1) 叠加：

- 变量的层级、env 槽、元变量 spine **一概不动**；
- "解前构建、解后消费"的值在**读点**用 `wrap_sub` 包裹成
  `Val::VSub`，`force` 的 frcs 臂在读点把 σ 推进值的结构；
- 臂边界回滚 = `self.sub` 的 Rc 指针赋值；可达性探测用局部 σ + meta
  快照。

旧实现"改写 env 槽 + quote→eval 刷新上下文"的根本缺陷：凡是已经捕获
了旧上下文的值——卡住 match 的捕获 env、meta 解、闭包——全部变成过期
引用；被精化变量又从元变量 pruning 里剔除（`update_cxt` 把槽置 None），
解的 λ 深度与使用现场槽位数错开，分支体固定 de Bruijn 索引读偏。
显式替换让这类错位**无从产生**：没有任何东西被改写，解以值的形式
随用随取。（2026-09 之前本层以 `Infer::pm_defs` 全局事实表承载同一
思想；本轮改为随编译器走的显式替换，见 §6 末行与
`docs/l07-dpm-refactor-design.md`。）

**纪律三：合一器只有一个。** `unify` 与模式特化共用同一套结构规则，
差别只在 `unify` 的 `spec: Option<&mut SpecSolve>` 参数——`SpecSolve`
携带当前子句的可解槽集 `solvable` 与已累积的解 `acc`：`spec` 非空
（模式走查 / 覆盖探测）时 bare rigid 可解，解经 `Subst::extend` 记入
`spec.acc`（方程两侧在 unify 入口置于 acc 之下——dpm-nbe
"剩余方程置于解之下"的惰性等价物）；`spec = None`（分支体检查等常规
转换）时不得解假设，否则 `Eq x y` 会被"证成" `Eq y y`。可解性不再
是 Infer 上的全局通道（旧 `pm_solvable_take/set` 编排已随之删除）。
配套的边界纪律：

- **走查期间**（模式槽逐个绑定、方程逐槽解）`spec.acc` 单调增长；
  每个方程结束后编译器把 `acc` 取回为新 σ；
- **分支体检查期间** spec 不穿参——体检查走常规转换，不得解假设；
- **臂边界**回滚 σ 快照（本臂解出的 meta 不回滚：分支体 Tm 引用着
  它们，且解在 rename 时已把精化事实烘焙成无 def 形式）。

### 1.3 惰性精化的两个读点

`force` 是精化传播的唯一入口，它有两条精化归约路径：

1. **VSub 推开（frcs）**：`force(VSub(v, σ))` 把 σ 推进 v 的结构——
   被解变量的读点取出解值并按应用序拼接 spine（λ ⇒ β），闭包 env /
   spine / Sum 槽逐层包裹（槽位只包裹不物化，见 design doc §4）。所有
   消费者（unify / quote / rename）都经过 force，精化对类型检查自动
   生效；
2. **Match 重选**：`force(Val::Match)` 重新 force scrutinee，一旦它
   （经 σ 推开 / meta 解）变成构造子值就重试选分支。没有这一步，精化
   无法传播进"卡住 match 内部"——`Eq (add a zero) a` 里 `add a zero`
   这个 stuck match 要等 `a := zero` 之后才可能归约。

由此，旧实现"被匹配变量本身的精化"（`a := succ t`）不需要任何门控
（旧版按返回类型是否含 stuck match 条件触发）：它只是头部精化方程
的又一条事实，force 的 Match 重选负责让它起作用。`val_contains_match`
与 `L07_NO_HEAD_REFINE` 环境变量一并删除。

精化的可见性边界：σ 只对**被包裹过的值**生效——meta 的解（rename
产物，Tm 层）与 decl 表条目不在 σ 的扫描/包裹范围内，meta 解值若引用
后被特化的槽位，精化在读点不可见（重构既定取舍，孪生移植需对齐同一
边界）。

### 1.4 两个配套机制

**期望类型重锚（rebase）。** 每臂检查前把期望类型 quote → eval 到臂
上下文：quote 把其中所有 rigid 引用重定向为相对臂 env 的索引（quote 时
defs 活跃，精化等式一并烘焙），eval 在臂 env 里重建。语义上不重锚也
正确（force 惰性展开）；但值层面只有重锚后，期望里的卡住 match 与
meta 解物化出来的副本才有**同样的 env 布局**（meta 解经 spine 应用
物化，spine = 臂 env），unify 的结构快路径（`struct_eq::val_eq`）才能
命中——否则"同一个 `add t b`"的两份不同布局表示会逐层展开、永不收敛
（fuel 耗尽误报 can't unify）。

**参数视角的 force（`force_arg`）。** `invert` / `prune_vflex` 关心的是
"元变量被应用在哪些**槽位**上"——槽位引用（`Rigid(x)`）本身就是作用域
事实，分支内的精化等式（x := zero）不改变槽位的存在。这两个入口用
`force_arg`（不展开 defs、不重选 Match）看 spine；在它们身上展开反而
会把可逆 spine 变成含构造子值的不可逆 spine（未标注返回类型的
`def add(x, y) = match x …` 的类型 meta 就这么挂过）。

## 2. 语言特性

```typort
enum Bool {
    true
    false
}

enum Vec[A](len: Nat) {          -- [A] 隐式类型参数；(len: Nat) 显式索引
    nil -> Vec[A] zero           -- -> 给出构造子的返回类型（GADT 风格）
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

def t[len: Nat](x: Vec[Nat] len, y: Vec[Nat] len): Vec[Nat] (succ len) =
    match x {
        case nil => cons zero nil
        case cons(x, xs) => match y {
            case cons(y, ys) => cons x (t xs ys)
        }
    }

def head[T, L: Nat](x: Vec[T] (succ L)): T =
    match x {
        case cons(x, _) => x
    }
```

- `enum` 声明：方括号参数是隐式（自动插入），圆括号参数是显式；
  每个构造子可以 `-> ret` 自定义返回类型（缺省为 `Name` 应用到所有
  隐式参数）。索引的等式在 `ret` 与使用处的合一中自动生效。
- **重定义报错**（L13 `fake_bind` 语义前传）：顶层 `def` / `enum` 名字
  已在 decl 表（builtin / 先前 def / enum）中 → `redefine {名}` 定向
  报错，不再静默覆盖；类型错误先于重定义报出。构造子裸名跨 enum 重复
  仍按最后注册解析（与 L13 一致——检查只罩 def/enum 名）。
- **类型注解的 universe 定向报错**（L13 `check_universe` 轻量移植）：注解
  形态确定非类型（字面量；名字/构造子名的类型非 U 且不是未解 meta）→
  `expected universe, got …`（结构预检零副作用，`?N` 编号不受扰动）；
  洞 / 未解 meta 放行——可解性交主检查路径。
- 构造子引用：裸名即可；跨 enum **重名构造子**裸名按最后注册解析，
  消歧用限定名**点号**语法 `Vec.cons`（注册键 `Enum.case`，经 Obj
  投影特判解析；打印才渲染 `Vec::cons`——读写格式不对称）。
- 显式参数是**索引**，不自动成为构造子绑定器：构造子的字段/返回类型
  需要参数作 binder 时必须自己再量化一遍（`box1(T : U)(x : T)`），
  直接 `box1(x : T)` 报 `name not in scope: T`。这是索引特化语义的
  推论（索引值由返回类型方程解出，前置成实参会破坏精化）。
- `match` 只能是**检查模式**（需要期望类型）；分支体在**精化过的**上下文
  里检查，期望类型按臂重锚。
- `.field` 投影：对 Sum（类型）取索引参数的值，对构造子值先查索引再查
  字段。
- 位置显式实参只能供给显式绑定器：`refl(a: A)` 可用 `refl a`，
  `refl[a: A]` 要写 `refl[A] a`（旧实现同样如此，测试里两种声明都有）。

## 3. 核心数据结构

```rust
Tm::Var(Ix) | Tm::Decl(SmolStr) | Tm::Obj(tm, 名) | Tm::Lam/App/AppPruning
  | Tm::U | Tm::Pi/Let | Tm::Meta | Tm::LiteralType/Intro | Tm::Prim
  | Tm::Sum(名, 参数(名, 值项, 类型项, icit), 构造子名表)
  | Tm::SumCase { typ, case_name, datas }
  | Tm::Match(scrutinee, [(PatternDetail, 分支体)])

Val::Flex(MetaVar, Spine) | Val::Rigid(Lvl, Spine) | Val::Decl(SmolStr, Spine)
  | Val::Obj(val, 名, Spine) | Val::Lam/Pi(闭包) | Val::U | 字面量
  | Val::Sum(名, 参数(名, 实参值, 实参类型, icit), 构造子名表)
  | Val::SumCase { typ, case_name, datas }
  | Val::Match(scrutinee, 捕获env, [(PatternDetail, 分支体Tm)])
  | Val::VSub(val, Rc<Subst>)   -- 显式替换下的值：force 读点把 σ 推进
```

### 3.1 为什么 `SumCase` 要携带实例化的 `typ`

`typ` 槽是**构造子应用点完整实例化后的 Sum 值**（如 `Vec[Nat] (succ l)`
的 `Val::Sum(Vec, [(A, Nat), (len, succ l)], …)`），因此：

- 合一 `SumCase vs SumCase` 同名构造子比字段（datas）即可——typ 是
  datas 的函数，索引等式在外层 Sum-Sum 的参数 zip 里建立，比 typ 只会
  陷入"索引槽 ↔ 构造子值"的互相引用环；
- 运行时投影 `t.len` 直接查 `typ` 的参数表；
- 头部精化写入 σ 的构造子值天然带着正确的类型。

### 3.2 全局名字与递归

顶层 def / enum / 构造子都登记在 `Cxt.decl: HashMap<SmolStr, DeclEntry{ty, val}>`
中；项里的引用是 `Tm::Decl(name)`，求值查表取缓存的 WHNF（体只求值一次）。

递归如此实现：检查一个 def 的体之前，先把它的名字登记成**指向自身的中性占位**
`Val::Decl(name, [])`（写时复制，只对本次检查可见），体里的自引用因此是
"未展开的名字"而非死循环；体检查完后用真实 WHNF 覆盖同一条目。

### 3.3 卡住的 match 是一等中性值

`eval` 里 `Tm::Match` 的求值：scrutinee 归约到构造子值（`Val::SumCase`）就用
`eval_aux` 按模式首匹配选分支；否则整个 match **卡住**成 `Val::Match`，
作为一个中性值继续参与一切：

- **应用**：`v_app(Val::Match, u)` 不 panic，而是把参数**拼进每个分支体**
  （splice）——scrutinee 一旦归约恰好命中一个分支，应用语义保持；
- **合一**：`Match vs Match` 先做结构快路径（`struct_eq::val_eq`：
  scrutinee、捕获 env、模式与分支体全部字面相同 ⇒ 直接判等——同源值的
  两份拷贝必须短路，否则逐分支重求值会把递归函数逐层展开、fresh 层级
  随深度递增永不收敛），再比 scrutinee、逐分支在 fresh 变量槽下比体；
  `Match vs 其它` 只接受**严格 eta**（每个分支都是通配且分支体就是
  scrutinee 本身），防止把任意 `f x` 证成 `x`——能归约的 match 在
  unify 入口的 force（含 Match 重选）已经消掉；
- **quote / rename**：分支体在"捕获 env + fresh 槽"下重新求值再 quote——
  用**简化 decl 表**（全局值换成中性 `Val::Decl`，enum 本体除外）避免
  递归调用在往返中被重展开。新架构下槽位布局永不漂移，rename 产物的
  λ 深度与使用现场天然一致，无需旧版的槽位重映射补丁。

### 3.4 深度防护（fuel）

索引槽与构造子值可能互相嵌入（`succ ?l` 的 `typ` 里 len 槽就是 `succ ?l`），
某些合一路径会无限递归。共享 fuel 池（`Cell<u32>`，外层入口充值，递归
入口递减）把无限递归转成可诊断的错误；`force` 的展开（meta 链 / decl /
精化 def / Match 重选）同样受保护。测试在 64 MB 栈线程里运行。

## 4. 模式匹配的编译（pattern_match.rs）

### 4.1 逐臂下钻

对每个臂独立下钻其模式（保持用户书写顺序，运行时即首匹配语义），
沿途 `cxt.bind` 模式绑定器（每绑定器一槽 + 计入可解集），在每个构造子
节点做特化方程。构造子臂的下钻：

1. **head 槽**：Con 模式自身占一槽（编译期绑定、运行时 prepend、
   `bind_count` 三方同序同数——嵌套模式由子 walk_con 入口绑自己的
   head 槽，不再由父级代绑哑槽）；
2. **剥构造子 Pi 链**：枚举隐式参数用头部 Sum 的实参值实例化（不产生
   槽），其余绑定器逐个绑成 fresh rigid，按 icit 对齐用户子模式
   （`[p]` 隐式子模式也支持；隐式绑定器可缺省 = 自动通配）；
3. **特化方程**：头部 Sum 参数与构造子返回 Sum 参数逐槽 `unify`
   （头部在前——双侧都是可解变量时解"头部变量 := 构造子侧值"；
   方程两侧由 unify 入口置于当前 acc 之下解释）。
   失败 = 分支不可达（absurd），臂报错且不计入覆盖；
4. **头部精化（无条件）**：被匹配变量若是本子句未精化的 bare rigid，
   把构造子值（typ = 头部 Sum，datas = 模式变量）经 `wrap_sub` 包裹后
   `Subst::extend` 写入 σ（嵌套方程的解经组合链对其可见）；
   环守卫（`val_mentions_lvl` 浅 occurs，只扫解值自身结构）失败时跳过
   不阻断；
4.5. **分支体检查前**：臂上下文 `subst_cxt`（env 槽与 src_names 类型
   包 VSub；lvl/locals/pruning 不动——槽位布局 = 运行时布局，永不漂移，
   dpm-nbe `subst sub ctx` 的同款）；
5. **分支体检查**：期望类型 wrap + 重锚（§1.4）后在臂上下文里 `check`
   （spec 不穿参——常规转换不得解假设）。

覆盖检查：**同一套方程**在快照回滚下对头部 Sum 的每个构造子跑一遍
（探测不产生真槽，绑定器用 scratch 层级；meta 与精化状态都回滚），
解得出的构造子必须被某个臂覆盖（通配臂覆盖全部），否则报"match 不完整"。
探测一次算出可达集，臂内方程给出同一判定，不再像旧版那样臂内再探一遍。
通配臂之后的臂跳过（运行时永不可达，保持首匹配语义不报错）。

## 5. 合一器（unification.rs）

骨架是 elaboration-zoo 07 的 meta 求解器（invert / prune / rename /
solve / intersect）。在此之上：

- `Val::Decl` 作为中性头参与（同名比 spine，不同名失败）；
- **可解 rigid**：`spec: Option<&mut SpecSolve>` 非空时，bare rigid 与
  任意非 Flex 值合一 ⇒ `Subst::extend` 记入 `spec.acc`（Flex 除外——
  交给 meta 求解规则）；方程两侧在 unify 入口置于 acc 之下——先解出
  的方程对后到的子方程自动可见（dpm-nbe "剩余方程置于解之下"）；
- `Sum` 同名即逐参数（含索引）合一；`SumCase` 同构造子只逐字段比
  （§3.1）；`Val::Match` 的规则见 §3.3；
- flex-flex 尝试两个方向（先短 spine 方向、失败回滚再反向）；
- invert / prune_vflex 用 `force_arg`（§1.4）；
- fuel 深度防护（§3.4）。

## 6. 相对旧实现（改写式精化）修了什么

| 旧问题 | 本层处理 |
|---|---|
| `update_cxt` 改写 env 槽 + 刷新，已捕获旧上下文的值（stuck match 捕获 env、meta 解）全部过期；被精化变量从 pruning 剔除，解的 λ 深度与使用现场槽位错开，分支体 de Bruijn 读偏 → **add_assoc / double_add / prove 一族失败**（README 旧"已知限制 #1"） | 事实表 + force 惰性展开：层级、槽位、pruning 一概不动，错位**无从产生**。add_assoc / add_comm / add_succ_right 全过 |
| `unify` / `unify_pm` 双轨，后者带"先比 datas 后比 typ""头部在前""已精化则再合一"等补丁 | 单一合一器 + 可解集；方向约定只剩调用侧参数顺序一条 |
| 隐式构造子绑定器用 fresh meta 充当，可解性与元变量求解纠缠 | 一律 fresh rigid（模式变量）；meta 只来自常规 elaboration |
| 可达性探测：克隆上下文 + meta 快照，每个臂的 walk_con 再探一遍 | 覆盖检查一次探测（scratch 层级，不产生真槽）；臂内方程即判定 |
| 被匹配变量精化按"期望类型是否含 stuck match"门控（`val_contains_match`），普通依赖返回类型不精化 | 头部精化无条件；force 的 Match 重选让精化传播进 stuck match 内部 |
| 期望类型不改写就丢失精化（改写又破坏 meta spine 视图） | 期望类型按臂**重锚**（quote→eval，defs 烘焙），与 meta 解物化布局字面一致 |
| `unify(Match, Match)` 的按值槽位重映射（`bodies_eq_aligned`）补丁 | 删除——布局不再漂移，`val_eq` 结构快路径 + 重锚覆盖 |
| `lvl2ix` 越界静默降级 `Ix(0)` | debug 构建断言，release 保留降级（显示路径） |
| 旧账（相对更早的 L07/L07a）：`1919810` 全局 hack、Raw-in-Term 构造子字段、quote(Match) 原样拷贝、矩阵算法丢分支、`panic!("impossible apply")` 等 | 均已在上一轮重写中处理，本版保留 |
| **黑盒二轮（2026-09）**：`force(Val::Prim)` 不 force spine 实参——嵌套 prim（`str_eq "foo" (string_concat "f" "oo")`）与 `change_mutable` 连续更新链（存入未 force 的 `f old`）永远过不了字面量检查，卡住不化简 | 读点对齐 `Val::Obj` 先 force 头部的纪律：逐个 force 实参再交 `prim_reduce`；参考版与孪生版同步修改（parity 保持，strchain/global 负载语义不变） |
| match 臂分隔符是单个 `EndLine`——臂间**注释行**经预处理剥成空行后变成残余 token，整个 def 解析失败 | 分隔符放宽为 `EndLine+`（臂间注释行/空行合法；行尾注释本就安全） |
| **黑盒三轮（2026-09）**：多隐式参数 enum 的无标注域洞在第 2+ 个参数处成为带 pruning 的部分应用 meta（`?m A`），构造子上显式供给枚举隐式实参（`P1[Nat][Bool]`）需解 `?m A := U`，invert 无法倒序 Decl 头 spine → 误报 can't unify | enum 声明处把无标注隐式参数的域**钉为 U**（方括号参数在语言定义上就是类型参数，任意类型的索引留给圆括号；显式标注 `[A : Nat]` 与显式索引不动）。参考版 + 孪生版同步；def 的隐式参数不限于类型，不受此修复影响（域洞保留，显式供参本就可用） |
| **连贯性评审（2026-09）**：三处 L08 侧修复的 L07 同码位点回合——①投影限定构造子快捷路径尊重局部遮蔽（L08 b66f5e4，遮蔽时走投影而非静默解析全局构造子）；②enum case 分隔放宽为 `EndLine+`（case 间注释行/空行合法，同 match 臂）；③unify 的 Π 臂 quote 改用当前层级 `l`（η descent 后 `l == cxt.lvl` 不变式已破，L08 §5 同款） | ①参考版 `elaboration.rs` `Raw::Obj` 臂 + 孪生同位（消融口径同步）；②`parser/mod.rs` `p_enum`；③参考版 `unification.rs`（孪版 Pi 臂不 quote 域值，无此路径）。回归：`l07_blackbox_v3` §H |
| **显式替换重构（2026-09，dpm-nbe 对齐）**：`pm_defs` 事实表 + `pm_solvable` 全局旁路作为精化载体，`pm_def` 读点 O(n) 反序扫、回滚靠长度截断、可解性与合一器经 Infer 全局状态耦合 | `Subst`（持久化单链，extend O(1)）+ `Val::VSub` 包裹 + `force` 的 frcs 臂；可解性经 `SpecSolve` 穿参（方程两侧在入口置于 acc 之下）；臂边界回滚 = Rc 指针赋值。机制、槽位纪律（spine 只包裹不物化）与多轮评审记录见 `docs/l07-dpm-refactor-design.md`。本表前各行所述的"事实表"载体自本轮起改为显式替换，行为语义不变（全套测试逐字节保持） |
| **深值栈安全轮（2026-09-18，LSP 接入前置）**：①`val_mentions_lvl` / `struct_eq` 全家 / `rename` 的 Sum/SumCase/Obj 臂按**值深度**原生递归（`succ^N zero` 型深值可由 def 倍增链构造，~万级深度在常规栈 1–8 MB 爆栈）；②孪生同款（`mentions_level` / `struct_val_eq` 族 / `rename_iter` 深链内联递归）；③孪生 arena 内 `XCell::VSub` 持有的 `Rc<SubstV>` 克隆跨轮不回收（长生命周期 Machine 下无上界慢泄漏） | ①参考版：`struct_eq` 改任务栈（短路序与燃烧面逐点对齐旧递归）、`val_mentions_lvl` 改工作栈、`rename` 拆 `rename_deep` 帧式收集器（Sum/SumCase/Obj 整链消化，`rename_arm` 收口浅臂，深链在任意深度进入收集器后不再按值深递归）；②孪生：`val_mentions_lvl`/`mentions_level` 工作栈、`struct_val_eq` 族任务栈、`rename_iter` 新增 `ObjWrap`/`ObjSpineFold`/`SumBuild`/`SumCaseBuild` 四收集任务（icit 平行栈与折叠序与 `SpineFold` 同构）；③`wrap_sub` 登记 `Rc::as_ptr` 进 `VSUB_REGS`（thread_local）+ 轮界 `vsub_reclaim`（`clear_round` 与 `run_decls` 出口 guard）逐指针归还，`SUBSTV_ALIVE` 存活计数为观察口。回归钉：`deep_value_iterative_under_default_stack` ×3（**默认 2 MB 测试栈**：10 万层 occurs/结构比较、1 万层 rename 收集器）与 `fast_substv_reclaimed_across_rounds`（两轮复用后计数回落基线）。残留边界见 §7.6（深值的递归 Drop 与 quote/pretty 深路径） |
| **代码评审轮（2026-09-17）**：①孪生 `vapp1` 的 VSub→闭包路径用调用方的 work/vals 重入 `eval_iter`，入口 clear 静默截断外层在飞的求值任务（match 臂内对 let 绑定 λ 做多参应用 + 结果进注解即触发，**ref Ok / twin Err 判定分裂**，现有 65 个 parity 用例零命中）；②参考版 frcs 的"头不可应用"守卫不含 λ，与孪生 `vapp_ok`（Clo tag 放行）分裂；③文件族 IO 失败直接 panic（源码可达）；④参考版 `eval(Tm::Prim)` 从现场 env 收集实参 spine——只在 builtin λ 链体的正典路径下正确，quoted Prim 在其它 env 下重求值会捕获无关槽；⑤孪生 Match/Match 的结构预检整体前置，Err 路径上 scrutinee 合一的 meta 副作用被吞；⑥探测不独立充值燃料，多构造子枚举逐 ctor 探测互相挤占 | ①VSub→闭包 β 改用本次私有草稿栈（`force` 同款纪律；回归钉 `parity_vsub_slot_applied_closure_workbuf`）；②frcs 读点放行 `Val::Lam`（只改 frcs，η 臂共用的 `v_applicable` 语义不变）；③四个文件臂改卡住降级（双版同步，v2 三个 panic 契约改写为 `v2_file_*_stuck_not_panic`）；④`Tm::Prim` 改零元卡住头、builtin 值体与 quote 产物一律经 App 应用实参（双版同步）；⑤改为 `MatchPrecheck` / `MatchPendingLen` / `MatchPending` 三个屏障任务，与参考版逐点交错（scrutinee → 分支数 → 逐分支模式+体 → pending 长度 → 逐 pending icit+值）；⑥`probe_accessible` 入口充值（双版同点） |

## 7. 已知限制（诚实清单）

1. **期望类型里的外层 meta**：若期望类型含有 match 之外创建的未解
   meta，臂内约束可能把它解成含臂局部模式变量的值，rename 因作用域
   越界失败而报 can't unify（Agda 对此做 generalize / block）。教学取舍，
   与旧版同级。
2. **force 无记忆 + fuel 预算是软防护**：`force(Val::Match)` 的重选与
   def 展开不做缓存；精化读点（lookup 命中）与各展开臂消耗共享 fuel
   池（4096，外层入口充值；**可达性探测每个 ctor 独立充值**——2026-09-17
   起，多构造子枚举的逐 ctor 探测不互相挤占，见 §6 评审轮行）。
   fuel 耗尽时精化读点**按未解处理**——极深嵌套模式负载下可能把合法
   分支误判为不可达（假 absurd），这是有界降级而非纯显示问题：燃烧
   剖面已对齐旧 pm_defs（旧版 d=2000 / 新版 d=400+ 同池均安全，
   `test_deep_pattern_fuel_budget_regression` 钉住边界），特化方程路径
   的失败文案带 `(fuel exhausted)` 尾注供诊断。更深的负载需加大
   `UNIFY_FUEL`。
3. **没有 K 公理层面的安全保护**：精化一个出现在其它假设里的变量在
   完整依赖理论里需要 `--without-K` 级论证，本层与 L07a 相同，是教学取舍。
4. **probe 与臂内方程理论上可能不同步**：两者跑同一套代码，但探测用
   scratch 层级、臂内用真槽，极端情形（方程解依赖层级数值本身）判定
   可能不一致——现有测试未触发。
5. **pretty 的 `AppPruning` 只显示内核**（不按掩码渲染实参，L06/L13 的
   `go_pr_inner` 全量渲染未移植）：本层所有 pretty 调用点都吃 quote 产物
   （quote 对 Flex 产 `Meta` + 实参链，不产 `AppPruning`），该分支仅作
   不 panic 的兜底，渲染差异不可达；`go_ix` 越界退化 `@{ix}`（与 L06 的
   固定文案不同，语义同为不崩）。
6. **深值遍历已迭代化（2026-09-18）；深值的"释放"级联仍是递归**：原先
   `val_mentions_lvl` / `struct_eq` 全家 / `rename` 的 Sum/SumCase/Obj 臂
   按**值深度**递归（`succ^N zero` 型深值可由 eval 不烧 fuel 地构造，
   def 倍增链），~万级深度在常规栈（1–8 MB）爆栈。现已全部改为显式工作
   栈 / 任务栈 / 帧式收集器（机制与回归钉见 §6 末行）；遍历面在**默认
   2 MB 测试栈**下经 10 万层深值验证。**残留边界**（诚实清单）：
   a. 深值的**释放**是 Rc/Box 链的递归 Drop——参考版的真树表示在深值析构
      时仍按深度吃栈（回归测试用句柄保留 + `mem::forget` 泄漏承接，测试
      基建行为、非被测路径）；孪生 arena 表示不跑 `Drop`，天然豁免；
   b. `quote` / `pretty` 对深值仍是递归路径（触发面 = nf 输出与错误显示，
      未含在本轮迭代化内，走 LSP 前需一并迭代化或定深拒绝）。
7. **孪生 σ 的跨轮回收已落地（2026-09-18）**：bump `reset()` 不跑 `Drop`，
   arena 内 `XCell::VSub` 持有的 `Rc<SubstV>` 克隆跨轮不递减。修：
   `wrap_sub` 在构造克隆的同一时刻把 `Rc::as_ptr` 登记进 `VSUB_REGS`
   （thread_local），轮界 `clear_round`（与三处 `bump.reset()` 严格伴生）
   与 `run_decls` 出口 guard 逐指针 `Rc::from_raw` + drop——恰好归还
   "arena 那一份"强引用（SAFETY 论证见 `VSUB_REGS` 注释）；归还后链若
   仍有表外持有者则继续存活（正常 Rc 语义）。泄漏上界从"无界累积"降为
   "单轮量"，且轮尾归还后每轮归零。回归钉
   `fast_substv_reclaimed_across_rounds`：`SUBSTV_ALIVE`（σ 链条目存活计数）在同一 Tycker 连跑两轮后
   回落轮前基线。开销：仅"真包裹"分支多一次 TLS 表 push（条件包裹不命中
   时零开销）。

## 8. 测试

`cargo test --lib L07_sum_type`（48 个测试；除深值栈安全 3 个外都在
64 MB 栈线程里跑）：

- 移植自 L07a：基础 ADT / 索引族与投影 / 依赖匹配（`t`）/ 嵌套 match /
  等式推理核心（cong / symm / trans / rfl）/ Church 编码与字符串；
- 依赖递归函数的索引族等式推理全家：`add_zero_right` / `add_succ_right` /
  `mul_zero_right` / `mul_one_right` / **`add_comm` / `add_assoc`**（后三者
  中的后者是旧实现已知限制 #1 的主体，本架构下按构造排除该 bug 族）；
- 迁移自 L13 legacy test7 的 `bits_adder`——Vec[Bool] 递归全加器
  （嵌套模式、多参数索引族、递归调用结果继续被匹配）；
- 回归（针对旧 bug）：泛型类型上的 match、通配臂混合、GADT 可达性与
  不可达报错、覆盖缺失报错、索引等式负例、投影类型标注、stuck match
  的合一 / 应用（splice）、分支体里的洞、嵌套模式、递归定义、
  嵌套解构引用外层绑定器；
- L06 演进同步（2026-09，见 §10）：字符串 builtin 全家 / 可变全局族 /
  缺名卡住与宽松臂把关 / string_to_global_type / 文件 IO / DEMO 全串；
- 显式替换重构（2026-09）机制层单测：Subst 链语义（取最新 / compose
  覆盖 / Rc 共享）、lookup 条件包裹、force_arg 多层解包、struct_eq 的
  VSub 分支；`test_fn_typed_index_slot_applied_after_refine` 钉死
  frcs 对"已解 rigid + 非空 spine"的解析应用行为（旧版卡住，孪生版
  移植必须复刻）；
- 深值栈安全（2026-09-18）回归钉：`deep_value_iterative_under_default_
  stack`（参考版 occurs/结构相等，10 万层，**默认 2 MB 测试栈**）、
  `unification::deep_rename_tests::deep_rename_collector_under_default_
  stack`（rename 收集器 1 万层，默认栈）、孪生同名单测（occurs /
  mentions / 结构比较，10 万层，默认栈）。

黑盒与双 oracle：`cargo test --test l07_blackbox`（49 个：48 可跑 +
1 个 `--ignored` 深度探针，参考版唯一入口 `run`）；`cargo test --test
l07_blackbox_v2`（53 个：51 可跑 + 2 个 `--ignored` 格式探针，二轮攻击面：
builtin 全量扫描含文件 IO 卡住降级契约（IO 失败不 panic，与实参非
字面量同口径；2026-09-17 评审轮落地）/ enum 冷僻特性（重名、显式参数、
空 enum、点号限定名、命名隐式实参）/ 类型层 match / preprocess 怪癖 /
run 层契约（Display、path_id、并发、跨 run 隔离）；§6 两条新修复的
回归在此）；`cargo test --test
l07_blackbox_v3`（95 个：94 可跑 + 1 个 `--ignored` 格式探针；它同样
`#[path]` 引入 `mod.rs`，故深值栈安全 3 钉也在其中跑。三轮攻击面：
依赖匹配深水区（`T n` 返回族 / 臂体换行嵌套 match / 双重精化 / `add` 型
索引算术 / 荒谬嵌套模式 / 零臂假前提 / 投影 scrutinee / 隐式子模式具名 /
遮蔽臂不查体）/ unification 边界（rigid 头不同、spine 长度不齐、自引用
占位 Decl、flex-flex、卡住投影不证等）/ 性能悬崖表征（深嵌套模式、
多 pending 卡住 match，带超时防护）/ 解析残缺（截断不 panic、match
位置精确刻画、CRLF、非 ASCII）；§6 三轮修复的回归在此）；`cargo test --test
l07_fast_parity`（70 个：run vs run_fast 逐字节互检，见 §10；含
2026-09-17 评审轮的 `parity_vsub_slot_applied_closure_workbuf`、本轮
`fast_substv_reclaimed_across_rounds`（σ 跨轮回收）与孪生深值默认栈钉等
工作区回归钉）。

## 9. 参考资料

- Coquand, *Pattern matching with dependent types* (1992)
- Cockx & Abel, *Elaboration of Dependent Pattern Matching*（specialization
  by unification：本层 §1.1 的理论来源）
- [elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo) 07
  （pruning / unification 骨架）
- [KonjacSource/dpm-nbe](https://github.com/KonjacSource/dpm-nbe)（explicit
  substitutions + forcing：2026-09 重构的机制蓝本，对照见
  `docs/l07-dpm-refactor-design.md`）
- 本仓库 `src/L13_namespace`：生产版（其 GADT 精化仍有弱点的分析见
  `docs/pattern-match-refinement-analysis.md`；本层的显式替换方案
  （dpm-nbe 对齐）是另一条路线，供其参考）

## 10. 性能孪生（`bump_spine_iter`，2026-09 与 L06 同步）

L06 的冠军配方（bump arena + 打包值 tag 编码 + 迭代内核 + 记忆化 + 稳态
复用 + prim 元数预检/单次收集/手工拼接）的 L07 移植，另加 sum-type 层的
机制落地。

> **机制对齐（2026-09，移植完成）**：参考版的显式替换精化已移植到孪生版
> ——`SubstV`（持久化单链，`Rc` 共享）/ `XCell::VSub` / `frcs` +
> `SpecSolve` 穿参，与参考版 `Subst`/`Val::VSub`/`frcs`/`SpecSolve`
> 逐点同构；`pm_defs`/`pm_solvable`/`pm_mark`/`pm_restore` 已随之删除。
> 两条参考版侧的关键语义选择在孪生侧复刻：design doc §4 的槽位纪律
> （spine/Sum/SumCase 槽只包裹不物化、Lam/Pi 闭包 env 逐槽包裹、Match
> scrutinee 单独推进）与 `frcs` 对"已解 rigid + 非空 spine"的解析应用
> 选择（`tests.rs` 的 `test_fn_typed_index_slot_applied_after_refine`
> 钉死，l07_fast_parity 逐字节保证）。fuel 燃烧点同步对齐：VSub 推开
> 入口不烧，frcs 的 lookup 命中烧 1（对齐旧 force(Rigid) 查表剖面），
> 耗尽返回裸 rigid。σ 用 std `Rc`（不进 reset arena——跨越单次模式编译
> 生存）。**轮界回收（2026-09-18）**：`wrap_sub` 登记 + `clear_round`/
> `run_decls` 出口归还，消除 arena 内克隆的跨轮泄漏（见 §7.7 与
> `VSUB_REGS` 注释）；`deep_value_tests`（默认栈深值）与
> `fast_substv_reclaimed_across_rounds` 为孪生侧回归钉。

机制落地清单（孪生侧现状）：

- **值编码**：tag 7 XCell 扩为 `Lit / Decl / Prim / Obj / Sum / SumCase /
  Match / VSub`；Decl/Prim/Obj 头的链经 spine 栈的**链头种类标志** O(1)
  判定（church 热路径零额外遍历）；
- **L07 语义的落点**：模式特化 = 显式替换（解入 `SpecSolve.acc`，臂边界
  Rc 指针赋值回滚；上下文经 `subst_cxt` 包裹 env 槽与类型表，布局不动；
  `force_arg` 逐层解包 VSub、不推开精化、不重选 Match）、`unify_fuel`
  （force 展开/每次 unify 递归各耗 1，充值点与参考版一致；frcs 的 lookup
  命中烧 1）、Match 运行时首匹配（`eval_aux` 的值层迭代版）+ 卡住期
  pending 的值层应用、Match quote/rename 的分支体在**简化 decl 表**下
  重求值再导出（与参考版 `simpl_decl` 逐点对应）、struct_eq 快路径
  （bump 版 budget 结构比较，VSub 对仅同 Rc 实例短路）、Compiler（模式
  编译 + 特化合一）全套；
- **decl 表平铺化**：参考版 `Cxt::decl_insert` 是 `Rc` 写时复制（条目按
  `Rc<DeclEntry>` 共享：整表克隆 = 重建哈希桶 + 逐条 Rc 递增，O(n)/次但
  每条的常数是引用计数而非值深拷贝——`Val` 深拷贝对 `Lam`/`Pi` 是整棵
  `Box<Tm>` 闭包树、对 `LiteralIntro` 是 String 分配，那才是主项）；
  快版用 `Rc<RefCell<FxHashMap>>` 平铺覆盖——顶层 elaboration 的插入全部
  单调（占位 → 同名覆盖为终值），语义等价且 O(1)/次（Ref 带 Drop 在作用域
  尾释放，借用按块化纪律组织）。两版都保留写时复制/覆盖的**语义**差别：
  参考版克隆出的父上下文看不到占位，快版因父上下文在体检查期间不被读而
  等效（`tests/l07_fast_parity.rs` 是这条的 oracle）。
  首版写时复制（值深拷贝）实测 strchain k=12 慢 70×，平铺后与 L06 同阶；
  参考版条目 Rc 化（2026-09-17）后 k=11 strchain basic 2120 → 124 ms
  （重构前 1902 ms 的 1/15），见 `docs/perf-l07-2026-09-17.md`。

### 双 oracle

`cargo test --test l07_fast_parity`：`#[path]` 独立 crate，run vs run_fast
**Ok 输出逐字节一致 / Err 判定一致**——覆盖 DEMO 全串（enum + 依赖
match + 字符串/文件 IO/可变全局）、tests.rs 全部用例源码、Err 判定
9 例、深负载（church/strchain/global/match 链/GADT enum，含与参考版
`bench_check_nf` 的节点数互检）、卡住 match × 卡住 prim 混合、稳态复用。

### 基准

```text
cargo run --release --bin l07bench -- --workload all --max-k 13
```

实测（Windows 10，release，rounds=5 取 min；2026-09-17 复测，含参考版
decl 条目 Rc 化）：

```text
== workload: church ==（check + nf）
k=12  n=8192    fast_ss=0.610ms      basic=9.111ms      (≈15×)
== workload: strchain ==（每层 prim 触发）
k=11  n=4096    fast_ss=4.632ms      basic=124.071ms    (≈27×)
k=12  n=8192    fast_ss=8.987ms      （basic 未跑满）
== workload: global ==（可变全局 + 重入 prim）
k=11  n=4096    fast_ss=7.592ms      basic=138.073ms    (≈18×)
k=12  n=8192    fast_ss=16.327ms
== workload: match ==（L07 特色：自递归依赖 match def 链）
k=13  n=16384   fast_ss=0.053ms      basic=0.177ms      (≈3×)
== workload: enum ==（L07 特色：GADT + 投影 + 索引等式）
                fast_ss=0.069ms      basic=0.341ms      (≈5×)
```

> **2026-09-18 深值栈安全轮 A/B 实测**：方法 = 独立 worktree（基线 =
> 本档提交版，`git worktree` 各自 target 缓存）+ 交错 10 轮取 min（当日
> 环境有周期性干扰——中位数口径互差可达 2×，min 口径稳定可复现）。
> 结论：strchain / global / enum / natadd / church 全部持平（±1.5%）；
> 唯一系统性差异 = **match 负载 +2~4%**（绝对 1–2 μs，k=9 39→40 μs）
> ——归因 = 任务栈创建与 §7.7 σ 回收 TLS 登记（真包裹分支一次 push）
> 等常数项。首次测得 +7.7%（k=9）后定位到任务栈**每次调用**的堆分配，
> 主循环栈全部内联化（`InlineStack`，溢出转 Vec）回收大半；表内数字
> 保留 2026-09-17 基线（同口径）。

注：`strchain`/`global`/`natadd` 仍是超线性（值本身就是逐层变长的字符串，
`string_concat` 复制 O(n) 字节 → 总量 O(n²) 字节），孪生版同样如此；参考版
与孪生的差距已从"decl 表值深拷贝"缩小到常数因子。

### 已知偏差（与参考版）

- 错误消息 span 全零（文档化偏差，同 L06）；unify_catch 文案带
  pretty 项 + `(fuel exhausted)` 尾注，span 数字两版不同；
- 卡住 Prim 的 force 每次烧 1 fuel（与参考版同语义，频率依赖）；
- eval(Tm::App) 复合函数头的求值序是先函数后实参（参考版先实参后函数；
  仅当两侧都有 eval 期副作用时可观测，L06 孪生同序）；
- 沿 meta 类型的 Π 层包 λ（`lams_from_ty`）把 `_` binder 改名
  `x{n}`（参考版保留 `_`；L06 冠军配方沿袭）；
- 消融开关沿用 `L06_NO_CONV_MEMO` / `L06_NO_NAME_MAP` 命名——L06/L07/L08
  三层孪生共用同名开关的项目级约定，非笔误。

### 性能 backlog（评审确认、待负载画像再动）

以下项经评审确认存在收益空间，但需要内核级签名穿参或收益依赖尚未
出现的负载形态，留待后续带测量落地：

- **force 草稿栈复用**：每次展开型 force 分配 4 张临时 Vec（L06 复用
  调用方缓冲）。干净形态是 Machine 常驻 `ForceScratch` + 深度标记
  （depth==0 清空复用、>0 私有局部），但 force/eval_iter 需穿参
  ~22 个调用点；预期个位数百分比，需 bench 证实后再动。
- ~~**simpl_decl 版本缓存**~~：**已落地（2026-09-19）**——thread-local 单槽
  旁路缓存（decl 表实例地址为键），`decl_insert` 唯一写点逐次失效 +
  轮界 `clear_round` 失效（缓存条目引用当轮 bump，跨轮即悬垂）；
  quote/rename/unify 三处 Match 消费点共享缓存 Rc。
- ~~**pending cons 化**~~：**已落地（2026-09-19）**——`XCell::Match.pending`
  改 `Option<&PendingCons>` 头插 cons 链（头 = 最新实参、尾部共享），
  vapp1 逐应用 O(k²)→O(k)；8 个消费点适配，栈序逐字节保持
  （parity 钉住）。
- **subst_cxt 平坦区丢失**：**已落地（2026-09-19）**——包裹槽经 `&mut
  defs` 追加为 defs 尾部新平坦区（append-only 不破坏旧 env 共享），
  臂体内 `env_nth` 恢复 O(1)。已知取舍：同作用域 match 之后再有
  let-define 回落 binder 链（非 tip 路径，语义一致）。
- **XCell 拆 Big 变体**：高频小单元 64B 重量级——结构性改动面广，
  留待后续。
- **frcs_env 闭包 env 逐槽包裹走链**：与 subst_cxt 平坦区同形态的
  遗留优化点（~L2030），待负载画像。
