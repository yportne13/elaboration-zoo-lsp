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

**纪律二：特化解是上下文外的事实表，不是上下文改写。** 方程的解
`len := succ l`、`a := zero` 只是 `Infer::pm_defs` 里一条
`(层级 → 值)` 记录：

- 变量的层级、env 槽、元变量 spine **一概不动**；
- `force` 在**读点**惰性展开（`force(Rigid(x))` → x 的定义值）；
- 臂边界 / 可达性探测做快照回滚（`pm_mark` / `pm_restore`）。

旧实现"改写 env 槽 + quote→eval 刷新上下文"的根本缺陷：凡是已经捕获
了旧上下文的值——卡住 match 的捕获 env、meta 解、闭包——全部变成过期
引用；被精化变量又从元变量 pruning 里剔除（`update_cxt` 把槽置 None），
解的 λ 深度与使用现场槽位数错开，分支体固定 de Bruijn 索引读偏。
事实表 + 惰性展开让这类错位**无从产生**：没有任何东西被改写。

**纪律三：合一器只有一个。** `unify` 与模式特化共用同一套结构规则，
差别只在一个集合——`pm_solvable`（当前子句的 bind 槽）：非空时
bare rigid 是可解的（解进 `pm_defs`）；为空时就是常规转换。旧实现的
`unify` / `unify_pm` 双轨（后者带"先比 datas 后比 typ"等环回避补丁）
合并为一条规则。配套的边界纪律：

- **走查期间**（模式槽逐个绑定、方程逐槽解）可解集增长；
- **分支体检查期间**可解集摘走（`pm_solvable_take` / `set`）——
  体检查走常规转换，不得解假设，否则 `Eq x y` 会被"证成" `Eq y y`；
- **臂边界**回滚事实表（本臂解出的 meta 不回滚：分支体 Tm 引用着
  它们，且解在 rename 时已把精化事实烘焙成无 def 形式）。

### 1.3 惰性精化的两个读点

`force` 是精化传播的唯一入口，它新增两条归约路径：

1. **def 展开**：`force(Rigid(x))` 查 `pm_defs`，有定义就展开。所有
   消费者（unify / quote / rename）都经过 force，精化对类型检查自动
   生效——`Cxt::update_cxt` 的整套刷新 machinery 因此删除；
2. **Match 重选**：`force(Val::Match)` 重新 force scrutinee，一旦它
   （经 defs / meta 解）变成构造子值就重试选分支。没有这一步，精化
   无法传播进"卡住 match 内部"——`Eq (add a zero) a` 里 `add a zero`
   这个 stuck match 要等 `a := zero` 之后才可能归约。

由此，旧实现"被匹配变量本身的精化"（`a := succ t`）不需要任何门控
（旧版按返回类型是否含 stuck match 条件触发）：它只是头部精化方程
的又一条事实，force 的 Match 重选负责让它起作用。`val_contains_match`
与 `L07_NO_HEAD_REFINE` 环境变量一并删除。

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
```

### 3.1 为什么 `SumCase` 要携带实例化的 `typ`

`typ` 槽是**构造子应用点完整实例化后的 Sum 值**（如 `Vec[Nat] (succ l)`
的 `Val::Sum(Vec, [(A, Nat), (len, succ l)], …)`），因此：

- 合一 `SumCase vs SumCase` 同名构造子比字段（datas）即可——typ 是
  datas 的函数，索引等式在外层 Sum-Sum 的参数 zip 里建立，比 typ 只会
  陷入"索引槽 ↔ 构造子值"的互相引用环；
- 运行时投影 `t.len` 直接查 `typ` 的参数表；
- 头部精化写入事实表的构造子值天然带着正确的类型。

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
   （头部在前——双侧都是可解变量时解"头部变量 := 构造子侧值"）。
   失败 = 分支不可达（absurd），臂报错且不计入覆盖；
4. **头部精化（无条件）**：被匹配变量若是本子句未精化的 bare rigid，
   把构造子值（typ = 头部 Sum，datas = 模式变量）写入 `pm_defs`；
   环守卫（`pm_solve` 的 occurs 检查）失败时跳过不阻断；
5. **分支体检查**：期望类型重锚（§1.4）后在臂上下文里 `check`。

覆盖检查：**同一套方程**在快照回滚下对头部 Sum 的每个构造子跑一遍
（探测不产生真槽，绑定器用 scratch 层级；meta 与精化状态都回滚），
解得出的构造子必须被某个臂覆盖（通配臂覆盖全部），否则报"match 不完整"。
探测一次算出可达集，臂内方程给出同一判定，不再像旧版那样臂内再探一遍。
通配臂之后的臂跳过（运行时永不可达，保持首匹配语义不报错）。

## 5. 合一器（unification.rs）

骨架是 elaboration-zoo 07 的 meta 求解器（invert / prune / rename /
solve / intersect）。在此之上：

- `Val::Decl` 作为中性头参与（同名比 spine，不同名失败）；
- **可解 rigid**：`pm_solvable` 非空时，bare rigid 与任意非 Flex 值合一
  ⇒ `pm_solve` 记入事实表（Flex 除外——交给 meta 求解规则）；
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

## 7. 已知限制（诚实清单）

1. **期望类型里的外层 meta**：若期望类型含有 match 之外创建的未解
   meta，臂内约束可能把它解成含臂局部模式变量的值，rename 因作用域
   越界失败而报 can't unify（Agda 对此做 generalize / block）。教学取舍，
   与旧版同级。
2. **force 无记忆**：`force(Val::Match)` 的重选与 def 展开不做缓存，
   同一值被反复 force 会重复归约（正确性无虞，纯性能项；fuel 充值由
   各外层入口负责）。
3. **没有 K 公理层面的安全保护**：精化一个出现在其它假设里的变量在
   完整依赖理论里需要 `--without-K` 级论证，本层与 L07a 相同，是教学取舍。
4. **probe 与臂内方程理论上可能不同步**：两者跑同一套代码，但探测用
   scratch 层级、臂内用真槽，极端情形（方程解依赖层级数值本身）判定
   可能不一致——现有测试未触发。

## 8. 测试

`cargo test --lib L07_sum_type`（39 个测试，64 MB 栈线程）：

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
  缺名卡住与宽松臂把关 / string_to_global_type / 文件 IO / DEMO 全串。

黑盒与双 oracle：`cargo test --test l07_blackbox`（49 个：48 可跑 +
1 个 `--ignored` 深度探针，参考版唯一入口 `run`）；`cargo test --test
l07_blackbox_v2`（53 个：51 可跑 + 2 个 `--ignored` 格式探针，二轮攻击面：
builtin 全量扫描含文件 IO panic 契约 / enum 冷僻特性（重名、显式参数、
空 enum、点号限定名、命名隐式实参）/ 类型层 match / preprocess 怪癖 /
run 层契约（Display、path_id、并发、跨 run 隔离）；§6 两条新修复的
回归在此）；`cargo test --test
l07_blackbox_v3`（46 个：45 可跑 + 1 个 `--ignored` 格式探针，三轮攻击面：
依赖匹配深水区（`T n` 返回族 / 臂体换行嵌套 match / 双重精化 / `add` 型
索引算术 / 荒谬嵌套模式 / 零臂假前提 / 投影 scrutinee / 隐式子模式具名 /
遮蔽臂不查体）/ unification 边界（rigid 头不同、spine 长度不齐、自引用
占位 Decl、flex-flex、卡住投影不证等）/ 性能悬崖表征（深嵌套模式、
多 pending 卡住 match，带超时防护）/ 解析残缺（截断不 panic、match
位置精确刻画、CRLF、非 ASCII）；§6 三轮修复的回归在此）；`cargo test --test
l07_fast_parity`（57 个：本文件 18 个 #[test] + `#[path]` 引入库内的
cfg(test) 测试 39 个，run vs run_fast 逐字节互检，见 §10）。

## 9. 参考资料

- Coquand, *Pattern matching with dependent types* (1992)
- Cockx & Abel, *Elaboration of Dependent Pattern Matching*（specialization
  by unification：本层 §1.1 的理论来源）
- [elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo) 07
  （pruning / unification 骨架）
- 本仓库 `src/L13_namespace`：生产版（其 GADT 精化仍有弱点的分析见
  `docs/pattern-match-refinement-analysis.md`；本层的事实表方案是另一条
  路线，供其参考）

## 10. 性能孪生（`bump_spine_iter`，2026-09 与 L06 同步）

L06 的冠军配方（bump arena + 打包值 tag 编码 + 迭代内核 + 记忆化 + 稳态
复用 + prim 元数预检/单次收集/手工拼接）的 L07 移植，另加 sum-type 层的
机制落地：

- **值编码**：tag 7 XCell 扩为 `Lit / Decl / Prim / Obj / Sum / SumCase /
  Match`；Decl/Prim/Obj 头的链经 spine 栈的**链头种类标志** O(1) 判定
  （church 热路径零额外遍历）；
- **L07 语义的落点**：`pm_defs` 事实表 + `pm_solvable` 可解集（truncate
  回滚）、`unify_fuel`（force 展开/每次 unify 递归各耗 1，充值点与参考版
  一致）、Match 运行时首匹配（`eval_aux` 的值层迭代版）+ 卡住期 pending
  的值层应用、Match quote/rename 的分支体在**简化 decl 表**下重求值再
  导出（与参考版 `simpl_decl` 逐点对应）、struct_eq 快路径（bump 版
  budget 结构比较）、Compiler（模式编译 + 特化合一）全套；
- **decl 表平铺化**：参考版 `Cxt::decl_insert` 是 `Rc` 写时复制（整表
  克隆 O(n)/次 → def 链 O(n²)）；快版用 `Rc<RefCell<FxHashMap>>` 平铺
  覆盖——顶层 elaboration 的插入全部单调（占位 → 同名覆盖为终值），
  语义等价且 O(1)/次（Ref 带 Drop 在作用域尾释放，借用按块化纪律组织）。
  首版写时复制实测 strchain k=12 慢 70×，平铺后与 L06 同阶。

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

实测（Windows 10，release，rounds=3 取 min；CLI 默认 rounds=5）：

```text
== workload: church ==（check + nf）
k=12  n=8192    fast=0.726ms         basic=9.884ms      (≈14×)
== workload: strchain ==（每层 prim 触发；basic 二次方）
k=11  n=4096    fast=5.975ms*        basic=2488.8ms     (≈400×)
k=12  n=8192    fast=11.841ms*       （basic O(n²) 未跑满）
== workload: global ==（可变全局 + 重入 prim）
k=11  n=4096    fast=9.894ms*        basic=508.2ms      (≈51×)
k=12  n=8192    fast=20.456ms*
== workload: match ==（L07 特色：自递归依赖 match def 链）
k=13  n=16384   fast=0.060ms*        basic=0.533ms      (≈9×)
== workload: enum ==（L07 特色：GADT + 投影 + 索引等式）
                 fast=0.086ms*        basic=0.737ms      (≈9×)
```

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
- **simpl_decl 版本缓存**：quote/rename/unify 的卡住 match 臂每次全表
  重建简化 decl 表（O(表) 次分配/事件，l13-perf-review §2.4 的同构
  问题）。唯一写点 decl_insert 可挂版本号，但 Match 臂深处只持有
  `&FxHashMap`，缓存需随表穿参或引入按地址键的旁表（有别名陷阱）。
- **pending cons 化 / XCell 拆 Big 变体**：卡住 match 逐应用 O(k²) 拷贝、
  高频小单元 64B 重量级——结构性改动面广（6 消费点 / ~30 匹配点），
  与上两项同窗口做以摊薄回归成本。
