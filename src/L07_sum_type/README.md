# L07：和类型与依赖模式匹配

本层是 07 章的重写版，合并了原先拆开的 `L07_sum_type`（和类型）与
`L07a_depend_pm`（依赖模式匹配）两部分：一份实现同时覆盖 enum 声明
（类型参数、索引、GADT 返回类型）与 `match`（嵌套模式、索引精化、
覆盖性检查、卡住的 match 作为中性值参与类型检查 / 求值 / 合一）。

相比旧实现，本层重写了四个关键机制：

- **全局名字**：用 `Tm::Decl` / `Val::Decl` + decl 表（名字 → 类型与 WHNF）
  取代旧版 `Var(lvl + 1919810)` 的"越界层级"hack；
- **构造子表示**：`SumCase` 携带**实例化的 Sum 类型值**（`typ` 槽）与构造子
  名字，取代"名字 + 字段值"的贫信息表示——索引等式的合一因此有了依据；
- **匹配编译**：逐臂（per-arm）下钻取代"构造子矩阵"，修掉通配臂与构造子臂
  混合时的丢分支 / 分支体跨上下文复用错误；
- **索引精化**：`unify_pm` + `Cxt::update_cxt`（改写 env 槽并由 quote/eval
  往返刷新依赖值）把"匹配精化索引变量"显式化，取代旧的 `(x := e)` 命名参数
  hack（语法改用 `-> ret` 直接写返回类型）。

下面按层讲解设计。

---

## 1. 语言特性

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
- `match` 只能是**检查模式**（需要期望类型）；分支体在**精化过的**上下文里
  检查，期望类型也按分支重实例化。
- `.field` 投影：对 Sum（类型）取索引参数的值，对构造子值先查索引再查字段。

## 2. 核心数据结构

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

### 2.1 为什么 `SumCase` 要携带实例化的 `typ`

旧版 `Val::SumCase { sum_name, case_name, params, cases_name }` 只有名字，
两个构造子值是否"同一索引"无从比较。新版 `typ` 槽是**构造子应用点完整实例化
后的 Sum 值**（如 `Vec[Nat] (succ l)` 的 `Val::Sum(Vec, [(A, Nat), (len, succ l)], …)`），
因此：

- 合一 `SumCase vs SumCase` 时索引等式有实际内容可比；
- 运行时投影 `t.len` 直接查 `typ` 的参数表；
- GADT 匹配的可达性探测（`nil` 是否可能出现在 `Vec[Nat] (succ l)` 中）就是
  一次"构造子返回类型 vs 头部类型"的合一。

`Tm::Sum` 的参数是 **(名, 值项, 类型项, icit)** 三元：声明处值项即参数自身
（`Vec[A](len: Nat)` 的 Sum 体里是 `Var A`、`Var len`），应用后值槽携带实参。
同时存类型槽是投影类型检查（`t.len : Nat`）的依据。

### 2.2 全局名字与递归

顶层 def / enum / 构造子都登记在 `Cxt.decl: HashMap<SmolStr, DeclEntry{ty, val}>`
中；项里的引用是 `Tm::Decl(name)`，求值查表取缓存的 WHNF（体只求值一次）。

递归如此实现：检查一个 def 的体之前，先把它的名字登记成**指向自身的中性占位**
`Val::Decl(name, [])`（写时复制，只对本次检查可见），体里的自引用因此是
"未展开的名字"而非死循环；体检查完后用真实 WHNF 覆盖同一条目。这样：

- 不需要旧版的 `lvl + 1919810` 全局偏移 hack，也没有"全局"与"局部"的层数耦合；
- `force` 遇到 `Val::Decl` 时查表展开（如同元变量的解）；
- quote / rename 把 `Val::Decl` 中性化处理，卡住的递归调用保形。

### 2.3 卡住的 match 是一等中性值

`eval` 里 `Tm::Match` 的求值：scrutinee 归约到构造子值（`Val::SumCase`）就用
`eval_aux` 按模式首匹配选分支；否则整个 match **卡住**成 `Val::Match`，
作为一个中性值继续参与一切：

- **应用**：`v_app(Val::Match, u)` 不 panic，而是把参数**拼进每个分支体**
  （splice）——scrutinee 一旦归约恰好命中一个分支，应用语义保持；
- **合一**：`Match vs Match` 先比 scrutinee、再逐分支在 fresh 变量槽下比体；
  `Match vs 其它` 先尝试归约（scrutinee 已是构造子时），再接受**严格的 eta**
  （每个分支都是通配且分支体就是 scrutinee 本身），防止把任意 `f x` 证成 `x`；
- **quote / rename**：分支体在"捕获 env + fresh 槽"下重新求值再 quote——
  用**简化 decl 表**（全局值换成中性 `Val::Decl`，enum 本体除外）避免递归调用
  在往返中被重展开。这是旧版只做"原样拷贝分支体"（de Bruijn 全错）的地方。

### 2.4 深度防护（fuel）

索引槽与构造子值可能互相嵌入（`succ ?l` 的 `typ` 里 len 槽就是 `succ ?l`），
某些合一路径会无限递归。旧实现直接栈溢出或侥幸终止；本层用共享 fuel 池
（`Cell<u32>`，外层 unity 入口充值，递归入口递减）把无限递归转成可诊断的
错误，`force` 的展开同样受保护（耗尽即停止展开、把值当未解处理）。
测试在 64 MB 栈线程里运行（合一递归的正常深度受 meta 链影响可达数千层）。

## 3. 模式匹配的编译（pattern_match.rs）

### 3.1 逐臂下钻

对每个臂独立下钻其模式（保持用户书写顺序，运行时即首匹配语义），
沿途 **`cxt.bind` 模式绑定器**。核心不变量：**每个绑定器占一个 env 槽**，
先绑定后下钻、深度优先——与运行时 `eval_aux` 的 prepend 顺序严格一致，
分支体的 de Bruijn 索引因此天然对齐（嵌套模式的旧账一并了结）。

构造子臂的下钻：

1. **可达性探测**：在克隆上下文 + 元变量快照回滚下，用全 meta 实例化构造子
   返回类型并与头部类型 `unify_pm`；失败 = 该构造子在这类值上不可能
   （如 `Vec[Nat] zero` 上不可能有 `cons`），分支报"不可达"且不计入覆盖；
2. **剥构造子 Pi 链**：枚举隐式参数用头部 Sum 的实参值实例化（不产生槽），
   其余绑定器逐个——隐式 = fresh meta，显式 = 它自己的 fresh rigid——先绑定
   槽位再按 icit 对齐用户子模式继续下钻（`[p]` 隐式子模式也支持）；
3. **索引精化**：构造子返回类型与头部类型 `unify_pm`（头部在前），加上
   **被匹配变量本身的精化**（见下）；
4. **分支体**：在精化后的臂上下文里 `check`，期望返回类型 quote → eval
   重实例化（精化写进 env 槽，重实例化把它传播进类型）。

覆盖检查：每个可达构造子必须被某个臂覆盖（通配 / 变量臂覆盖全部），
否则报"match 不完整"；通配臂之后的臂跳过（运行时永不可达）。

### 3.2 精化：`unify_pm` 与 `Cxt::update_cxt`

- **头部类型精化**（总是做）：`unify_pm(头部类型, 构造子返回类型)` 逐槽递归；
  遇到"当前上下文里尚未精化的 rigid 变量"（env 槽仍是自身的 vvar）就把它的
  槽**改写**为对侧的值（`update_cxt`），并把它依赖的所有 env 槽与 src_names
  类型按"旧环境 quote → 新环境 eval"刷新——`trans` 里 `e2 : Eq y z` 在
  `y := a` 之后类型自动刷新成 `Eq a z` 靠的就是这一下。
- **被匹配变量精化**（条件做）：若**期望返回类型里包含卡住的 match**
  （`Eq (add a zero) a` 含 `add a zero` 的 stuck；`V n` 本身就是 stuck），
  说明类型依赖被匹配变量的形态，则把该变量精化成构造子值
  （`case zero` → `a := zero`），分支体的期望类型重实例化后 `add a zero`
  才能归约。对普通返回类型（`Vec[Nat] (succ len)`）不做——那会把变量槽
  变成构造子值，使之后新建的 meta 与既有 meta 的 spine 视图不一致
  （flex-flex 的 invert 要求 spine 项是 rigid），且那里并不需要。

`unify_pm` 与普通 `unify` 的分工：pm 合一修改的是**上下文**（env 槽），
普通合一修改的是**元变量**；`SumCase vs SumCase` 的 pm 比较不递归 typ
（两个构造子值在匹配编译中必然同类型，参数比较由调用侧完成），
避免"索引槽 ↔ 构造子值"的互相引用环。

## 4. 合一器（unification.rs）

骨架是 elaboration-zoo 07 的 meta 求解器（invert / prune / rename / solve /
intersect）。在此之上：

- `Val::Decl` 作为中性头参与（同名比 spine，不同名失败）；
- `Sum` 同名即逐参数（含索引）合一；`SumCase` 同构造子只逐字段比；
- `Val::Match` 的规则见 §2.3；splice 使 eta 展开（`unify(t, Lam)` 时 `v_app`
  stuck match）也正确；
- `rename(Match)` 分支体在 fresh 槽 + 简化 decl 表下求值再 rename——
  元变量解里带着 stuck match 时（`?m := match x …`）依然良构；
- flex-flex 尝试两个方向（先短 spine 方向、失败回滚再反向），
  因为头部变量被精化后 spine 里可能出现非 rigid 项，单方向会漏解；
- fuel 深度防护（§2.4）。

## 5. 修了什么（相对旧 L07 / L07a）

| 旧问题 | 本层处理 |
|---|---|
| `lvl2ix` 的 `1919810` 全局 hack | `Tm::Decl` + decl 表，无魔数 |
| `Tm::Sum` 的构造子字段类型是 **Raw 语法**，匹配时按名字现场检查——泛型即时可用，参数名不在现场就报错或错绑 | 字段类型来自**构造子的注册类型**按头部实参实例化 |
| `quote(Match)` 原样拷贝分支体（de Bruijn 失配）；`rename(Match)` 是注释掉的 TODO | 分支体在 fresh 槽 + 简化 decl 表下求值再 quote/rename |
| `eval_aux(...).unwrap()` 与 `v_app` 的 `panic!("impossible apply")` | stuck match 一律卡住成中性值；应用走 splice |
| 通配臂与构造子臂混合时矩阵算法丢分支、`checked_ret` 按 Raw 跨上下文复用错误分支体 | 逐臂下钻 + 分臂精化，无跨臂复用 |
| `.field` 投影的类型是字段的"值" | Sum 参数的**类型槽**；构造子字段走 Pi 剥取真实类型 |
| `SubstCase` 只有名字，索引等式无从比较 | `typ: Val`（实例化 Sum）+ case_name |
| 匹配即时只用 `(x := e)` 语法 hack | `-> ret` 直接写返回类型（L07a 语法） |
| unify 里活着的调试 `println!`、pretty 的 `todo!()`（AppPruning） | 全部实现/移除 |
| unify 无终止保护（索引槽互相嵌入时死循环或碰巧终止） | fuel 防护 + 双向 flex-flex + 探测回滚 |
| 递归占位改 env / 名字耦合 | decl 表写时复制占位 |

## 6. 已知限制（诚实清单）

1. **依赖递归函数的索引族等式推理**（`add_zero_right` / `add_succ_right` /
   `add_comm` / `add_assoc` 这类 L07a 测试）：期望类型里出现"递归函数应用于
   模式绑定器"的 stuck match 组合时，unify 会在"索引槽 ↔ 构造子值"的互相
   引用上不收敛（fuel 拦下后报 `can't unify (fuel exhausted)`）。
   这是把运行时换成"全 stuck 中性值 + 简化 decl 表"体系后的已知差距；
   L07a 的原始实现依赖其特定的合一顺序侥幸通过。`test_eq_reasoning` 目前
   覆盖到 cong / symm / trans 这一档。
2. **嵌套构造子模式**（`case cons(succ(m), t)` 等）经过多层解构时，
   绑定器类型若引用了更早的显式绑定器，可能与深层槽位产生偏差
   （L07a/L13 同样存在，未修是刻意保留简单性）。
3. 被匹配变量精化（§3.2）是"有条件的"：期望类型不含 stuck match 时不做，
   某些依赖该变量的类型（不经过 match 的表达式）无法归约——这是与完整
   GADT 系统的差距。
4. 没有 K 公理层面的安全保护：精化一个出现在其它假设里的变量（如
   `trans` 的做法）在完整依赖理论里需要 `--without-K` 级别的论证，本层
   与 L07a 相同，是教学取舍。

## 7. 测试

`cargo test --lib L07_sum_type`（19 个测试）：

- 移植自 L07a：基础 ADT / 索引族与投影 / 依赖匹配（`t`）/ 嵌套 match /
  等式推理核心 / Church 编码与字符串；
- 回归（针对旧 bug）：泛型类型上的 match、通配臂混合、GADT 可达性与
  不可达报错、覆盖缺失报错、索引等式负例、投影类型标注、stuck match
  的合一 / 应用（splice）、分支体里的洞、嵌套模式、递归定义。

测试在 64 MB 栈线程里跑（§2.4）。

## 8. 参考资料

- [elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo) 07
  （pruning / unification 骨架）
- 本仓库 `src/L13_namespace`：把 L07 的"问题修好了"的最终版
  （本层的 `Val::SumCase` 带 typ、quote/rename Match 三段式、fuel 防护、
  splice、decl 表自引用都源于对它的裁剪与简化）
- 旧 `L07a_depend_pm` 的 git 历史（`git log -- src/L07_sum_type` 与
  `src/L07a_depend_pm`）：本层保留了它"构造子类型可剥取"与"索引精化"的
  设计方向，重写了匹配编译与合一器的实现。