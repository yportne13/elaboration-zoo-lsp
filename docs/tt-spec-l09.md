# L09_mltt 类型检查内核 —— 精确逆向规格（Lean 4 形式化用）

> 对象：`src/L09_mltt/`（**参考版**，权威）。孪生 `bump_spine_iter/` 仅用于交叉确认。
> 所有论断带 `文件:行` 锚点；行号对应当前工作区快照（`docs/tt-spec-l09.md` 写入时）。
> 本文只读代码得出，未运行任何构建/测试；一切"行为"论断均为对源码的直接转写。
>
> 阅读顺序建议：§1 语法 → §2 值域 → §3 求值 → §4 force/quote → §5 合一 →
> §6 双向检查 → §7 声明 → §8 上下文/全局 → §9 模式编译 → §10 缺口与孪生差异 → §11 判断汇总（形式化清单）。

## 0. 总览：判断清单（Lean 4 形式化的入口）

| 参考版函数 | 判断 | 锚点 |
|---|---|---|
| `Infer::eval(env, tm)` | `Γ ⊢ t ⇓ v`（环境为值栈，de Bruijn 下标寻址） | `mod.rs:755` |
| `Infer::v_app(t, u, i)` | `v • (u,i)` 中性/β 应用 | `mod.rs:710` |
| `Infer::force(v)` | `v ⇓ʷ v'`（WHNF：仅 Flex 展开 + VSub 推开） | `mod.rs:555` |
| `Infer::frcs(sub, v)` | `v[σ]` 显式替换推进 | `mod.rs:575` |
| `Infer::quote(l, v)` | `v ↑ l`（readback，`l` = 当前层级） | `mod.rs:899` |
| `Infer::nf(env, tm)` | `nf` = `quote(len env, eval(env, tm))` | `mod.rs:977` |
| `Infer::unify(l, cxt, t, u, spec)` | `t ≈ u`（可解 rigid 集由 `spec` 携带） | `unification.rs:542` |
| `Infer::unify_pm(...)` | 模式方程 `t ≐ u`，解累积进 `Subst` | `elaboration.rs:127` |
| `Infer::rename(pren, v)` | 部分重命名/剪枝 `v ↦ t`（含 occurs） | `unification.rs:265` |
| `Infer::invert(gamma, sp)` | 反演 spine 得 `PartialRenaming` + 非线性掩码 | `unification.rs:85` |
| `Infer::check(cxt, raw, a)` | `Γ ⊢ t ⇐ A`（双向） | `elaboration.rs:296` |
| `Infer::infer_expr(cxt, raw)` | `Γ ⊢ t ⇒ A`（双向，返回 `(Tm, Val)`） | `elaboration.rs:624` |
| `Infer::check_universe(cxt, raw)` | `Γ ⊢ A ⇐ Type ?`，返回 `u` 使 `A : Type u` | `elaboration.rs:246` |
| `Infer::infer(cxt, decl)` | 声明层：`def` / `enum` / `println` | `elaboration.rs:377` |
| `Compiler::compile(...)` | match 编译 + 覆盖/不可达检查 | `pattern_match.rs:190` |
| `Compiler::eval_aux(...)` | 运行时首匹配选臂 | `pattern_match.rs:361` |

注意：**参考版没有 `conv` 函数**，合一只有 `unify`（孪生 `machine.rs` 里的 `conv: ConvScratch`
只是工作表复用缓冲，`bump_spine_iter/machine.rs:59`）。本文用 `unify` 表述全部转换判断。

---

## 1. 核心语法

### 1.1 表面语法 `Raw`（解析器输出，`parser/syntax.rs:50-68`）

```rust
pub enum Raw {
    Var(Span<String>),
    Obj(Box<Raw>, Span<String>),
    Lam(Span<String>, Either, Box<Raw>),
    App(Box<Raw>, Box<Raw>, Either),
    U(u32),
    Pi(Span<String>, Icit, Box<Raw>, Box<Raw>),
    Let(Span<String>, Box<Raw>, Box<Raw>, Box<Raw>),
    Hole,
    LiteralIntro(Span<String>),
    Match(Box<Raw>, Vec<(Pattern, Raw)>),
    Sum(Span<String>, Vec<(Span<String>, Icit, Raw)>, Vec<Span<String>>, u32),
    SumCase {
        typ: Box<Raw>,
        case_name: Span<String>,
        datas: Vec<(Span<String>, Raw, Icit)>,
    },
}
```

```rust
pub enum Icit { Impl, Expl }                       // parser/syntax.rs:3-7
pub enum Either { Name(Span<String>), Icit(Icit) } // parser/syntax.rs:9-13
pub enum Pattern {
    Any(Span<()>, Icit),
    Con(Span<String>, Vec<Pattern>, Icit),
}                                                  // parser/syntax.rs:15-19
pub enum Decl {
    Def { name: Span<String>, params: Vec<(Span<String>, Raw, Icit)>, ret_type: Raw, body: Raw },
    Println(Raw),
    Enum { name: Span<String>, params: Vec<(Span<String>, Raw, Icit)>,
           cases: Vec<(Span<String>, Vec<(Span<String>, Raw, Icit)>, Option<Raw>)> },
}                                                  // parser/syntax.rs:98-111
```

关键点：

- **`Raw::U(u32)` 是唯一的宇宙构造子**，语法为 `Type N`（`parser/mod.rs:330-332`：
  `Cut((kw(TypeKeyword), string(Num))).map(|(_, num)| Raw::U(num.parse::<u32>()...unwrap_or(0)))`）。
  **裸 `U` 不是宇宙**，只是一个普通标识符（`parser/mod.rs:327-329` 先试 `string(Ident)`；
  孪生模块头同证：`bump_spine_iter.rs:13`）。
- `Raw::Hole` 由记号 `_` 产生（`parser/lex.rs:136` 把 `_` 词法为 `Hole`；`parser/mod.rs:333`），
  **也**被解析器在缺省处合成：缺类型标注（`p_def` 的 `ret_type`，`parser/mod.rs:624`）、
  隐式 binder 无标注（`p_pi_impl_binder`，`parser/mod.rs:430-433`）、缺 `=>` 体（`parser/mod.rs:410`）。
  单 binder 位置上的 `_` 仍是一个合法的 Lam 名（`p_bind` 接受 `Hole`，`parser/mod.rs:386-387`），
  故 `_ => e` 是 `Raw::Lam("_", Expl, e)` 而非洞；独立 `_` 原子才走 `p_atom1` 的 `Hole` 臂。
- `Raw::Obj(t, f)` = 投影（`t.f`，`parser/mod.rs:339-348`）。
- `Raw::Sum` 只由 `enum` 声明在同层内部构造（`elaboration.rs:490-495`），源码不能直接写；
  第 4 字段是**声明处算出的宇宙层级**（见 §7.3）。
- `Raw::SumCase` 只由构造子登记构造（`elaboration.rs:514-526`）。
- `struct` 脱糖为单构造子 `enum`，构造子名 = `{Name}.mk`（`parser/mod.rs:667-690`，
  第 683 行 `format!("{x}.mk")`）；`new Name(a, b)` 脱糖为
  `App(Var("Name.mk"), a, b)`（`parser/mod.rs:580-591`）。
- 隐式实参逗号合写 `f[A, B] ≡ f[A][B]`（`p_arg`/`p_spine`，`parser/mod.rs:360-385`）。

### 1.2 核心项 `Tm`（`mod.rs:63-84`）

```rust
pub enum Tm {
    Var(Ix),
    Obj(Box<Tm>, Span<String>),
    Lam(Span<String>, Icit, Box<Tm>),
    App(Box<Tm>, Box<Tm>, Icit),
    AppPruning(Box<Tm>, Pruning),
    U(u32),
    Pi(Span<String>, Icit, Box<Ty>, Box<Ty>),
    Let(Span<String>, Box<Ty>, Box<Tm>, Box<Tm>),
    Meta(MetaVar),
    LiteralType,
    LiteralIntro(Span<String>),
    Prim,
    Sum(Span<String>, Vec<(Span<String>, Tm, Ty, Icit)>, Vec<Span<String>>),
    SumCase { typ: Box<Tm>, case_name: Span<String>, datas: Vec<(Span<String>, Tm, Icit)> },
    Match(Box<Tm>, Vec<(PatternDetail, Tm)>),
}
```

配套类型（全部在 `mod.rs`）：

```rust
pub struct MetaVar(u32);                    // mod.rs:31-32
pub struct Ix(u32);                         // mod.rs:40-41
type Ty = Tm;                               // mod.rs:140（别名，无独立类型层）
type VTy = Val;                             // mod.rs:386
type Env   = List<Val>;                     // mod.rs:159
type Spine = List<(Val, Icit)>;             // mod.rs:160
pub type Pruning = List<Option<Icit>>;      // syntax.rs:7
pub(crate) struct Closure(Env, Rc<Tm>);     // mod.rs:162-163
pub struct Lvl(u32);                        // mod.rs:142-143（Add/Sub 见 145-157）
enum MetaEntry { Solved(Val, VTy), Unsolved(VTy) }  // mod.rs:34-38
enum DeclTm { Def {}, Println(Tm), Enum {} }         // mod.rs:49-61
```

语义逐条：

| 构造子 | 载荷 | 语义 |
|---|---|---|
| `Var(Ix i)` | de Bruijn 下标（自最内层起 0） | 若 `i < env.len()` 取环境槽；否则是**全局哨兵**，索引全局值表（§8） |
| `Obj(t, f)` | 项 + 字段名 | 投影 `t.f` |
| `Lam(x, i, b)` | 名、icity、体 | λ |
| `App(f, a, i)` | 函数、实参、icity | 应用 |
| `AppPruning(h, pr)` | 头 + 掩码 `List<Option<Icit>>` | **meta 实例化的掩码应用**：只把 `pr` 中 `Some(i)` 位置对应的 env 槽喂给头（`Option::None` 跳过）。由 `fresh_meta` 产出（`mod.rs:544-551`） |
| `U(n)` | 层级 | `Type n`（`Type n : Type (n+1)`） |
| `Pi(x,i,a,b)` | 名、icity、域、余域 | 依值函数类型 |
| `Let(x,a,t,u)` | 名、类型标注、值、体 | let（`a` 仅供显示/闭包；求值忽略，见 §3） |
| `Meta(m)` | meta 变量号 | 未解/已解由 `Infer.meta` 表决定 |
| `LiteralType` | — | 内建类型 `String`（`Cxt::new` 首条 define，`cxt.rs:36-42`） |
| `LiteralIntro(s)` | 字符串字面量 | `"..."` 的值项 |
| `Prim` | — | **唯一 builtin** `string_concat` 的体（无名、无 spine），`cxt.rs:43-91` |
| `Sum(name, params, cases)` | 枚举名、参数 `(名, 值项, 类型项, icity)`、构造子名表 | 和类型（本层唯一的归纳族） |
| `SumCase{typ, case_name, datas}` | 实例化返回类型、构造子名、字段 `(名, 值项, icity)` | **构造子值/构造子体的望远镜**（不是 case 表达式） |
| `Match(scrut, arms)` | scrutinee、臂 `(PatternDetail, Tm)` | match；臂已过滤（荒谬/被遮蔽臂丢弃，§9） |

### 1.3 模式 `PatternDetail`（`mod.rs:86-91`）

```rust
pub enum PatternDetail {
    Any(Span<()>),
    Bind(Span<String>),
    Con(Span<String>, Vec<PatternDetail>),
}
```

- `Any` = `_`（无绑定）；`Bind(n)` = 变量模式（绑定一个槽）；`Con(c, subs)` = 构造子模式。
- `bind_count`（`mod.rs:93-103`）：`Any|Bind → 1`；`Con` → 子模式 `bind_count` 之和
  （**Con 本身不占槽**，与 `walk_pat` 的槽位纪律一致）。
- `PatternDetail: PartialEq`（`mod.rs:86`），`unify` 的 Match/Match 臂用它做结构相等（§5.7）。
- 覆盖判定辅助：`enum PosCover { All, Ctor(String), None }`（`mod.rs:107-114`）、
  `cover_at(detail, path)`（`mod.rs:117-130`）、`fmt_path`（`mod.rs:133-138`，形态 `cons#2 → nil#1`）。

### 1.4 替换 `Subst`（`mod.rs:210-222`）

```rust
pub struct Subst { head: Option<Rc<SubEntry>> }
struct SubEntry { lvl: Lvl, val: Val, next: Option<Rc<SubEntry>> }
```

持久化单链，**链头 = 最新解**；写入 O(1)、读取沿链扫描。

- `is_empty`（`mod.rs:225-227`）。
- `lookup_hit(sub, x) -> Option<Val>`（`mod.rs:233-246`）：沿链找首个 `e.lvl == x`；
  若 `!mentions_level(e.val, sub)` 原样返回 `e.val`（零分配热路径），否则返回
  `Val::VSub(Box::new(e.val), sub)`（把整条 σ 包在解值外，解值不含 x 自身由 occurs 保证）。
- `mentions_level(v, sub)`（`mod.rs:253-279`）：浅结构扫描；`Val::VSub` 保守返回 `true`；
  `Val::Lam` 只看闭包 **env 槽**（不看体）；`Val::Match` 看 scrutinee 与捕获 env；
  字面量/`U`/`Prim` 返回 `false`。
- `has(sub, x)`（`mod.rs:282-291`）。
- `extend(sub, x, v) = {x ↦ v} :: sub`（`mod.rs:294-302`）。
- `compose(outer, inner)`（`mod.rs:306-320`）：`outer` 条目接到链头 —— **同键取 outer（最新）**；
  语义为"inner 先应用、outer 后应用"。
- `wrap_sub(sub, v)`（`mod.rs:335-341`）：σ 空则直通，否则 `Val::VSub(v, sub)`。

### 1.5 上下文 telescope `Locals`（`syntax.rs:22-27`）

```rust
pub enum Locals {
    Here,
    Define(Rc<Locals>, Span<String>, Ty, Tm),  // 定义槽：类型项 + 体项
    Bind(Rc<Locals>, Span<String>, Ty),        // binder 槽：类型项
}
```

`close_ty(mcl, b)`（`syntax.rs:35-52`）：把项 `b` 沿 telescope 闭包成类型 —
`Bind(x,a) ↦ Tm::Pi(x, Expl, a, ·)`；`Define(x,a,t) ↦ Tm::Let(x, a, t, ·)`。头 = 最内层。

---

## 2. 值域 `Val`

```rust
pub enum Val {                                          // mod.rs:171-198
    Flex(MetaVar, Spine),
    Rigid(Lvl, Spine),
    Obj(Box<Val>, Span<String>, Spine),
    Lam(Span<String>, Icit, Closure),
    Pi(Span<String>, Icit, Box<VTy>, Closure),
    U(u32),
    LiteralType,
    LiteralIntro(Span<String>),
    Prim,
    Sum(Span<String>, Vec<(Span<String>, Rc<Val>, Rc<VTy>, Icit)>, Vec<Span<String>>),
    SumCase { typ: Rc<Val>, case_name: Span<String>, datas: Vec<(Span<String>, Rc<Val>, Icit)> },
    Match(Box<Val>, Env, Vec<(PatternDetail, Tm)>),
    VSub(Box<Val>, Rc<Subst>),
}
```

| 变体 | 含义 |
|---|---|
| `Flex(m, sp)` | 未解（或 fuel 降级后视作未解）的**灵活头** meta `?m` 应用于中性 spine `sp` |
| `Rigid(l, sp)` | **刚性头**：局部变量 `l` 或全局哨兵层级应用于 spine |
| `Obj(v, f, sp)` | **卡住的投影**（接收者非构造子时）；`sp` 是投影值继续被应用时累积的实参 |
| `Lam(x,i,cl)` | 函数值（闭包）；`cl.env` = 创建点环境，`cl.1` = 体项 |
| `Pi(x,i,a,cl)` | 依值函数**类型值**；余域为闭包 |
| `U(n)` | 宇宙值 |
| `LiteralType` / `LiteralIntro` | 字符串类型 / 字面量值 |
| `Prim` | **无 spine 的裸标记**：`string_concat` 未饱和/卡住时的值（`v_app` 对它 panic，故永不出现 Prim 头链） |
| `Sum(name, params, cases)` | 和类型值；`params[i] = (名, 实参值, 参数类型值, icity)`，`cases` = 构造子名表 |
| `SumCase{typ, case_name, datas}` | **构造子值**：`typ` = 实例化的返回类型值（⟶ `Sum`），`datas[i] = (字段名, 字段值, icity)` = 该构造子的字段实参 |
| `Match(s, env, arms)` | **卡住的 match**：`s` = scrutinee 值、`env` = 捕获环境、`arms` = 项层臂表 |
| `VSub(v, σ)` | 显式替换下的值（模式精化）；**不变式：`force` 的返回值顶层不会是 `VSub`**（fuel 耗尽的降级点在 `frcs` 的 lookup 命中处返回裸 rigid，`mod.rs:193-197`） |

辅助：

- `Val::vvar(x) = Rigid(x, [])`（`mod.rs:389-391`）；`Val::vmeta(m) = Flex(m, [])`（`mod.rs:393-395`）。
- `Spine` 头 = **最内层（最后应用的）实参**；`v_app` 用 `spine.prepend`（`mod.rs:721-723`），
  `v_app_sp` 从尾到头 fold（`mod.rs:728-737`）。
- `v_applicable(v)`（`mod.rs:326-331`）：`Flex | Rigid | Obj | VSub` 为真 —— 只有这些能吃
  η 新变量；字面量/`U`/`Pi`/`Sum`/`SumCase`/卡住 `Match` 与实参相遇时无从应用（η 臂改判 `Err`）。
- `val_mentions_lvl(v, x)`（`mod.rs:357-384`）：浅结构扫描层级出现。**`Flex` 头的实参视为不透明
  （返回 `false`）**（`mod.rs:369`，理由见注释：可达性探测用 `?m … l …` 是合法形）；
  `VSub` 只扫解值自身、不扫 σ 的映射值；闭包/Pi/`U`/字面量/Prim 不扫。
- `rc_take(v)`（`mod.rs:435-437`）：`Rc` 独占零拷贝否则深拷。

---

## 3. 求值

### 3.1 `eval(env, tm)`（`mod.rs:755-873`）

| 项 | 规则 | 锚点 |
|---|---|---|
| `Var(Ix i)` | `env[i]`；越界则查 `Infer.global[Lvl(i - 1919810)]`，取不到 `.unwrap()` panic；**中性全局视图**置位时返回 `Rigid(Lvl(i), [])` | `757-768` |
| `Obj(t, f)` | 先 eval `t`；若结果是 `VSub` 先 `force`。然后：`Sum(_,params,_)` → 在 `params` 里按名找字段，取 `params[i].1`（**找不到 `.unwrap()` panic**）；`SumCase{typ,datas,..}` → 把 `force(typ)` 的 `Sum` 参数链 `(名,值,icity)` 接上 `datas` 后按名找，取该值；`Rigid(_,_)` → 卡住 `Val::Obj(Rigid, f, [])`；**其它（含 `Flex`/`Lam`/`Pi`/`U`/…）→ `panic!("impossible {x:?}")`** | `769-803` |
| `App(t,u,i)` | `v_app(eval t, eval u, i)` | `804` |
| `Lam(x,i,b)` | `Val::Lam(x, i, Closure(env.clone(), b))` —— **惰性**，不进入体 | `805` |
| `Pi(x,i,a,b)` | `Val::Pi(x, i, eval a, Closure(env.clone(), b))` —— 余域惰性 | `806-808` |
| `Let(_,_,t,u)` | **急切**：`eval(env.prepend(eval(env, t)), u)`；类型标注被忽略 | `809-812` |
| `U(n)` | `Val::U(n)` | `813` |
| `Meta(m)` | `v_meta(m)`：已解返回**解值本身（未 force、未加 spine）**，未解 `Flex(m, [])` | `814`, `698-703` |
| `AppPruning(t, pr)` | `v_app_pruning(env, eval t, pr)` | `815` |
| `LiteralIntro(s)` / `LiteralType` | 逐字构造 | `816-817` |
| `Prim` | 读 `env[1]`（更外层实参）与 `env[0]`（最内层），**各自先 `force`**；两者都是 `LiteralIntro` → `Val::LiteralIntro(a ++ b)`（`a.map(\|x\| format!("{x}{}", b.data))`，即 `env[1]` 的值在前）；否则 `Val::Prim` | `818-828` |
| `Sum(name,params,cases)` | 逐参数 `(名, eval 值项, eval 类型项, icity)`；`cases` 原样 | `829-842` |
| `SumCase{typ,name,datas}` | 逐字段 `(名, eval 值项, icity)`；`typ` = `eval typ` | `843-858` |
| `Match(t, arms)` | `let v = force(eval t)`；`v` 是 `SumCase` → `Compiler::eval_aux(self, &v, env, &arms).unwrap()` 得 `(body, env')` 再 `eval(env', body)`；**否则**卡成 `Val::Match(v, env.clone(), arms)` | `859-871` |

`eval_neutral(env, tm)`（`mod.rs:875-884`）：置位 `neutral_globals` → `eval` → 恢复旧值（可嵌套）。
用在三处"分支体重求值"（Match 合一 `unification.rs:733-734`、`rename` 的 Match 臂
`unification.rs:358`、`quote` 的 Match 臂 `mod.rs:967`），用途是**全局名字不再递归展开**。

### 3.2 值层应用

```rust
fn v_app(&self, t: Val, u: Val, i: Icit) -> Val {          // mod.rs:710-726
    match t {
        Val::VSub(..) => { let t = self.force(t); self.v_app(t, u, i) }
        Val::Lam(_, _, closure) => self.closure_apply(&closure, u),
        Val::Flex(m, sp) => Val::Flex(m, sp.prepend((u, i))),
        Val::Rigid(x, sp) => Val::Rigid(x, sp.prepend((u, i))),
        Val::Obj(x, name, sp) => Val::Obj(x, name, sp.prepend((u, i))),
        x => panic!("impossible apply\n  {:?}\nto\n  {:?}", x, u),
    }
}
```

- `closure_apply(cl, u) = eval(&cl.0.prepend(u), (*cl.1).clone())`（`mod.rs:705-708`）——**β 唯一产生点**。
- `v_app_sp(t, sp)`（`mod.rs:728-737`）：`sp` 尾到头依次 `v_app`（尾 = 最外层实参先应用）。
- `v_app_pruning(env, v, pr)`（`mod.rs:739-753`）：`(env,pr)` 从链头（最内层）配对；
  `pr` 头 `Some(i)` → 把 `env` 头作为实参应用；`None` → 跳过该槽；两链同时空 → 返回 `v`；
  **其余（长度失配/形状错配）→ `panic!("impossible {v:?}")`**。
  不变式：`env.len() == cxt.lvl == pr.len()`（§8）。

### 3.3 运行时选臂 `Compiler::eval_aux`（`pattern_match.rs:361-411`）

```
eval_aux(infer, heads, cxt: &Env, arms) -> Option<(Tm, Env)>
  force(heads) 为 SumCase{typ, case_name, datas} ->
      constrs = force(typ) 为 Sum 的 cases（否则 panic!("by now only can match a sum type, but get ...")）
      否则 (case_name = "$unknown$", params = [], constrs = [])
  按 arms 顺序找第一个匹配臂：
    Any(_)   -> (body, cxt.prepend(heads))
    Bind(_)  -> (body, cxt.prepend(heads))
    Con(c, ps) 且 c ∉ constrs -> (body, cxt.prepend(heads))      // 非构造子名的“变量模式”兜底
    Con(c, ps) 且 c == case_name ->
        对 (params[i].1, ps[i]) zip 依次递归 eval_aux，折叠出 (body, env')
        注：任一字段递归返回 None 则整臂 None（try_fold）
    其它（异名构造子）-> None（跳过）
```

**首匹配语义**（保持用户书写顺序）；无臂匹配时 `eval` 处的 `.unwrap()` panic
（`mod.rs:864`）。`params` 是 `SumCase.datas`（构造子声明绑定器，含隐式绑定器），
与 `walk_pat` 产出的 `details` 位置对齐（§9.2）。

---

## 4. force / frcs / quote / nf

### 4.1 `force`（`mod.rs:555-569`）

```rust
fn force(&self, t: Val) -> Val {
    match t {
        Val::Flex(m, sp) => match self.lookup_meta(m) {
            MetaEntry::Solved(t_solved, _) => self.force(self.v_app_sp(t_solved.clone(), sp)),
            MetaEntry::Unsolved(_) => Val::Flex(m, sp),
        },
        Val::VSub(v, sub) => self.frcs(&sub, *v),
        _ => t,
    }
}
```

**只有两个展开臂**：meta 解、VSub。没有 Match 重选、没有 decl 展开、没有 Prim 归约
（README §6.2，`README.md:295-299`）。入口**不烧 fuel**。

### 4.2 `frcs(sub, v)`（`mod.rs:575-665`）：把 σ 推进值的结构

σ 空 → `force(v)`（`576-578`）。逐构造子：

| 形状 | 规则 | 锚点 |
|---|---|---|
| `VSub(v2, sub2)` | `frcs(compose(sub, sub2), v2)`（内层先、外层后，组合后一次推进） | `581-584` |
| `Rigid(x, sp)` | `lookup_hit(x)`：命中且 `burn()` 成功 → `force(hit)`；命中但 **fuel 耗尽 → 原样返回 `Rigid(x, sp)`（有界降级）**；未命中 → `vvar(x)`。若 `sp` 非空且 `head` 不可应用（`!v_applicable`）→ 返回裸 `Rigid(x, sp)`（守卫）。否则按应用序（spine 尾→头）`head = v_app(head, wrap_sub(sub, u), i)` | `590-608` |
| `Flex(m, sp)` | `force(Flex(m, wrap_sp(sub, sp)))` —— spine **只包裹不物化** | `611` |
| `Obj(o,name,sp)` | `force(Obj(frcs(sub,o), name, wrap_sp(sub,sp)))` | `612-616` |
| `Lam(x,i,cl)` | `Lam(x, i, Closure(frcs_env(sub, &cl.0), cl.1))` —— 闭包 **env 逐槽包裹（`Val::VSub`），不进体** | `618` |
| `Pi(x,i,a,cl)` | `Pi(x,i,frcs(sub,a), Closure(frcs_env(sub,&cl.0), cl.1))` | `619-624` |
| `Sum(...)` | 参数值/类型槽 **只包裹**（`Rc::new(wrap_sub(sub, rc_take(v)))`） | `626-640` |
| `SumCase{...}` | `typ` 与 `datas` 槽 **只包裹** | `641-652` |
| `Match(s, env, arms)` | scrutinee **推进** `frcs(sub, *s)`；捕获 env 只包裹 | `653-661` |
| `U / LiteralType / LiteralIntro / Prim` | 原样 | `662-663` |

`wrap_sp`（`mod.rs:667-672`）、`frcs_env`（`mod.rs:674-679`，逐槽 `Val::VSub`）。
**槽位纪律**：spine / Sum / SumCase 槽只包裹不物化 —— 槽位引用是作用域事实，
物化会破坏后续 `solve` 的 `invert`（`mod.rs:571-574`）。

### 4.3 `force_arg`（`mod.rs:687-697`）：合一器参数视角

逐层解包 `VSub`（取最内层）；若最内层是 **空 spine 的 `Rigid`** → 返回该裸 rigid；
若是 `Rigid(非空)` 或 `Match` → **原样返回 `t`**（含外层 VSub）；否则 `force(t)`。
不推开精化、不做 Match 重选。

### 4.4 燃料

- `const UNIFY_FUEL: u32 = 4096`（`mod.rs:476`），池在 `Infer.unify_fuel: Cell<u32>`（`mod.rs:472`）。
- `burn(cell)`：0 → `false`；否则减一 → `true`（`mod.rs:345-352`）。
- **唯一烧点**：`frcs` 的 `Rigid` 臂 `lookup_hit` 命中（`mod.rs:594`）。
- 充值点（`meta_refuel`，`mod.rs:531-533`）：`unify_catch` 入口（`mod.rs:990`）、
  `nf`（`mod.rs:979`）、`check_pm`（`elaboration.rs:114`）、`check_pm_final`（`elaboration.rs:84`）、
  `probe_accessible` 每个构造子探测各一次（`pattern_match.rs:116`）、`bench_check_nf`（`mod.rs:1142`）。
- `fuel_exhausted()` = 池为 0（`mod.rs:534-539`）；覆盖探测据此把失败保守判"可达"
  （`pattern_match.rs:142`）。

### 4.5 `quote(l, v)`（`mod.rs:899-975`）

入口先 `force(t)`（`901`）。分派：

| 值 | 规则 | 锚点 |
|---|---|---|
| `VSub(v,_)` | 正常路径不会出现；fuel 耗尽时出现 → `quote(l, *v)`（解包打印内层） | `905` |
| `Flex(m, sp)` | `quote_sp(l, Tm::Meta(m), sp)` | `906` |
| `Rigid(x, sp)` | `quote_sp(l, Tm::Var(lvl2ix(l, x)), sp)` | `907` |
| `Obj(x,name,sp)` | `quote_sp(l, Tm::Obj(quote(l,x), name), sp)` | `908` |
| `Lam(x,i,cl)` | `Tm::Lam(x, i, quote(l+1, closure_apply(cl, vvar(l))))` | `909-913` |
| `Pi(x,i,a,cl)` | `Tm::Pi(x,i, quote(l,a), quote(l+1, closure_apply(cl, vvar(l))))` | `914-919` |
| `U(n)` / `LiteralIntro` / `LiteralType` / `Prim` | 逐字 | `920-923` |
| `Sum(name,params,cases)` | 参数 `(名, quote 值, quote 类型, icity)`，`cases` 原样 | `924-931` |
| `SumCase{typ,name,datas}` | `(名, quote 值, icity)`；`typ` = `quote typ` | `932-948` |
| `Match(val, env, cases)` | 见下 | `949-973` |

`quote` 的 Match 臂：对每臂把 `env` 前置 `bind_count` 个 `Val::vvar(l + x)`（`963-964`），
分支体在**中性全局视图**下重求值 `eval_neutral(env', tm)`（`967`），再
`quote(l + bind_count, tm')`；scrutinee `quote(l, *val)`。

`quote_sp(l, t, sp)`（`mod.rs:886-897`）：从 spine 尾到头 fold 出 `Tm::App`（保序）。
`lvl2ix(l, x)`（`mod.rs:398-408`）：

```rust
if x.0 >= 1919810 { Ix(x.0) } else { Ix(l.0 - x.0 - 1) }
```

（边界必须 `>=`：0 号全局恰等于 1919810，用 `>` 会让首个声明的自引用下溢。）
`close_val(cxt, t) = Closure(cxt.env.clone(), Rc::new(quote(cxt.lvl + 1, t)))`（`mod.rs:984-986`）。
`nf(env, t)`（`mod.rs:977-982`）：充值燃料，`l = Lvl(env.len())`，`quote(l, eval(env, t))`。

---

## 5. 合一 / 转换

### 5.1 `PartialRenaming` 与辅助（`unification.rs:24-51`）

```rust
pub struct PartialRenaming {
    pub occ: Option<MetaVar>,   // occurs 守卫：解算中的 meta 自身
    pub dom: Lvl,               // 目标（结果项）上下文大小 Γ
    pub cod: Lvl,               // 源上下文大小 Δ
    pub ren: HashMap<u32, Lvl>, // Δ 变量 → Γ 变量
}
fn lift(pr) -> pr' { ren' = ren[cod ↦ dom]; dom+1; cod+1 }        // 32-42
fn skip(pr) -> pr' { dom 不变; cod+1; ren 不变 }                  // 44-51
```

> ⚠ 代码内 `unification.rs:47` 的注释 `// decrement dom` 是**陈旧笔误**：实现是 `cod + 1`，
> `dom` 不变（与 `prune_ty_go` 的用法自洽，见 §5.5）。形式化时以代码为准。

`SpinePruneStatus { OKRenaming, OKNonRenaming, NeedsPruning }`（`unification.rs:53-58`）。

### 5.2 `invert(gamma, sp)`（`unification.rs:85-112`）

`invert_go`（`61-84`）**从 spine 尾（最外层实参）向头**递归：
对每个实参取 `force_arg`，要求是**空 spine 的 `Rigid(x)`**，否则 `Err(UnifyError)`。
- 首次出现的 `x`：`ren[x] = dom`，`dom += 1`。
- 重复出现（非线性）：`ren.remove(x)`，`nlvars.insert(x)`，`dom += 1`。

返回 `(PartialRenaming{occ: None, dom, cod: gamma, ren}, mask)`，`mask` 仅在非线性时
`Some(Pruning)`：`fsp`（按 spine 顺序的 `(lvl, icit)`）映到 `Some(icit)` / 非线性位置 `None`。
即 **`invert` 要求 spine 全是变量**（这就是"非变量 spine 不可反演"的含义）；非线性只影响剪枝掩码。

### 5.3 `rename(pren, t)`（`unification.rs:265-366`）——解算的右侧重命名

入口 `force(t)`。分派：

- `VSub` → `Err(UnifyError)`（防御；不变式说不会出现）（`269`）。
- `Flex(m', sp)` → `pren.occ == Some(m')` → **`Err`（occurs 检查）**；否则 `prune_vflex(pren, m', sp)`（`270-273`）。
- `Rigid(x, sp)`（`274-285`）：`pren.ren.get(x)`；
  `None` 且 `x < 1919810` → `Err`（scope error，含被剪枝的非线性变量）；
  `None` 且 `x >= 1919810`（**全局哨兵**）→ `Tm::Var(lvl2ix(pren.dom, x))`；
  `Some(x')` → `Tm::Var(lvl2ix(pren.dom, x'))`。随后 `rename_sp` 逐实参。
- `Obj(x,name,sp)`（`286-290`）：重命名接收者 + `Tm::Obj` + `rename_sp`。
- `Lam(x,i,cl)`（`291-297`）：`rename(lift(pren), closure_apply(cl, vvar(pren.cod)))`。
- `Pi(x,i,a,cl)`（`298-305`）：域 `rename(pren, a)`；余域 `rename(lift(pren), closure_apply(cl, vvar(pren.cod)))`。
- `U`/`LiteralType`/`LiteralIntro`/`Prim` 逐字（`306-309`）。
- `Sum`（`310-324`）：逐参数**同时**重命名值槽与类型槽；任一失败即失败。
- `SumCase`（`325-343`）：`typ` + 各 `datas` 值槽。
- `Match`（`344-364`）：scrutinee `rename`；每臂把 `env` 前置 `bind_count` 个 `vvar(pren.cod)`
  并 `lift` pren，体经 `eval_neutral` 后 `rename`。

`rename_sp(pren, t, sp)`（`255-264`）从尾到头 fold 出 `Tm::App`。

### 5.4 `prune_vflex` / `intersect`（同一 meta 的两条 spine 求交）

`prune_vflex_go`（`unification.rs:180-214`）**从 spine 尾到头**递归；对每实参 `force_arg`：

| 情形 | 结果 |
|---|---|
| `Rigid(x,[])` 且 `pren.ren[x] = Some(x')` 且 status 非 NeedsPruning | `Some(Tm::Var(lvl2ix(pren.dom, x')))` |
| `Rigid(x,[])`，`ren` 无 x，status == OKNonRenaming | `Err`（前有非变量实参，次序冲突） |
| `Rigid(x,[])`，`ren` 无 x，其它 status | `None`（该槽待剪枝），status := NeedsPruning |
| 非 Rigid 头，status == NeedsPruning | `Err`（非变量实参出现在被剪枝槽之后） |
| 非 Rigid 头，其它 | `rename(pren, t)` 后 `Some(t)`，status := OKNonRenaming |

`prune_vflex(pren, m, sp)`（`215-254`）：由 status 决定 —— `OKRenaming`/`OKNonRenaming` →
若 `self.meta[m]` 已是 `Solved` 则 `Err`（fuel 耗尽窗口的降级），否则保留 `m`；`NeedsPruning` →
`prune_meta(mask, m)` 得 `m'`。最后 fold 出 `Tm::App` 链（`None` 槽跳过；注释 `//TODO:need rev()?`
保留在 `251`）。

`intersect(l, cxt, m, sp, sp', spec)`（`524-541`）：
`intersect_go`（`497-523`）逐槽配对 `force` 后的 `Rigid(x,[])`，相等 → `Some(icit)`，否则 `None`；
**长度失配/非 rigid → `None`**。判定：`None` → `unify_sp` 兜底；`Some(pr)` 且含 `None` →
`prune_meta(pr, m)`；否则 `Ok(())`。

### 5.5 `prune_ty` / `prune_meta`（剪枝）

`prune_ty(pr, a)`（`unification.rs:138-153`）：`pr` 头 = **最内层**槽，
先 `rev.reverse()` 成"外→内"，再从 `PartialRenaming{occ:None, dom:0, cod:0, ren:{}}` 起走：

```rust
fn prune_ty_go(rev, pren, a) {                     // 113-137
    match (rev.split_first(), force(a)) {
        (None, a) => rename(pren, a),
        (Some((Some(_), rest)), Pi(x,i,a,b)) => { let a = rename(pren,*a)?;
            let b = closure_apply(&b, vvar(pren.cod));
            Pi(x,i,a, prune_ty_go(rest, &lift(pren), b)?) }
        (Some((None, rest)), Pi(x,i,_,b)) => {
            let b = closure_apply(&b, vvar(pren.cod));
            prune_ty_go(rest, &skip(pren), b) }     // 该 Π 层被丢弃
        _ => Err(UnifyError),
    }
}
```

`prune_meta(pruning, m)`（`154-179`）：要求 `self.meta[m] = Unsolved`（否则 `Err`，`161`）；
`prune_ty` 得新类型 → `eval` → `m' = new_meta(...)`；解
`m := eval(&[], lams(pruning.len(), mty, Tm::AppPruning(Meta(m'), pruning)))`；返回 `m'`。

### 5.6 `lams` / `solve`（`unification.rs:367-447`）

`lams_go(l, t, a, l_prime)`（`367-398`）：从 `l_prime = 0` 到 `l`，对 `a` 逐层剥 `Π` 造
`Tm::Lam(name, icit, ·)`，每层把闭包应用于 `Val::Rigid(l_prime, [])`；binder 名为 `"_"` 时改名
`x{l_prime}`；`a` 不是 Π 且未到 `l` → `unreachable!()`。`lams(l,a,t) = lams_go(l,t,a,Lvl(0))`。
注意：**生成项的绑定变量层级从 0 起**，故解项在空环境下求值。

`solve(gamma, m, sp, rhs)`（`402-413`）：`invert(gamma, sp)` → `solve_with_pren`。
`solve_with_pren`（`414-447`）：

1. 要求 `self.meta[m] = Unsolved`，否则 `Err`（`421-427`）；
2. 若 `invert` 给出非线性掩码 `pr` → `prune_ty(&pr, mty)?`（**只作可行性检查，结果弃置**）（`432-434`）；
3. `rhs = rename(&PartialRenaming{occ: Some(m), ..pren}, rhs)?`（occurs）；
4. `solution = eval(&[], lams(pren.dom, mty, rhs))`；
5. `self.meta[m] = Solved(solution, mty)`。

### 5.7 `unify(l, cxt, t, u, spec)`（`unification.rs:542-759`）

入口：`t = force(t)`、`u = force(u)`（`551-552`）；若 `spec.acc` 非空则两侧都
`force(wrap_sub(&acc, ·))`（先解出的方程对后续子方程可见，`556-561`）。随后按**臂序**匹配：

| # | 模式 | 规则 | 锚点 |
|---|---|---|---|
| 1 | `(U x, U y)` | `x == y` → Ok；否则落兜底 Err。**非累积性**：`U(n) ≢ U(m)`（`n≠m`） | `569` |
| 2 | `(Pi(x,i,a,b), Pi(_,i',a',b'))` | 要求 `i == i'`；`unify a a'`；再在 `l+1`、`cxt.bind(x, quote(l,a), a)` 下 `unify(b[vvar l], b'[vvar l])`。注意 binder 类型用 `quote(l, a)` 而**非** `cxt.lvl`（`l+1` 递归不推进 cxt，理由见 `572-578`） | `570-584` |
| 3 | `(Rigid x sp, Rigid x' sp')` | `x == x'` → `unify_sp` | `585-587` |
| 4 | `(Obj(o1,f1,sp1), Obj(o2,f2,sp2))` | `f1.data == f2.data` → `unify o1 o2` 且 `unify_sp sp1 sp2`（卡住投影的合同规则） | `593-596` |
| 5 | `(Rigid(x,[]), v)` | 若 `spec` 携带 `solvable ∋ x` 且 `v` 不是 `Flex`：`val_mentions_lvl(v,x)` → Err；否则 `acc := extend(acc, x, v)`（**解假设**） | `603-616` |
| 6 | `(v, Rigid(x,[]))` | 同 #5 对称 | `617-630` |
| 7 | `(Flex(m,sp), Flex(m,sp'))` | 同一 meta → `intersect` | `631-633` |
| 8 | `(Flex(m,sp), Flex(m',sp'))` | → `flex_flex` | `634-636` |
| 9 | `(Lam(_,_,t), Lam(_,_,t'))` | `unify(l+1, cxt, t[vvar l], t'[vvar l])` | `637-643` |
| 10 | `(t, Lam(_,i,t'))` | `v_applicable(t)` → `unify(l+1, cxt, v_app(t, vvar l, i), t'[vvar l])`（**λ-η**） | `644-650` |
| 11 | `(Lam(_,i,t), t')` | `v_applicable(t')` → 对称 | `651-657` |
| 12 | `(Flex(m,sp), t')` | `solve(l, m, sp, t')` | `658` |
| 13 | `(t, Flex(m,sp))` | `solve(l, m, sp, t)` | `659-661` |
| 14 | `(LiteralType,LiteralType)` / `(LiteralType,Prim)` / `(Prim,LiteralType)` | Ok（宽松臂） | `662-664` |
| 15 | `(Sum(a,pa,_), Sum(b,pb,_))` | `a.data == b.data` → **逐槽只比 `params[i].1`（值）**，忽略参数类型与 icity | `665-677` |
| 16 | `(SumCase{typ=a,case_name=ca,datas=da}, SumCase{typ=b,case_name=cb,datas=db})` | `ca.data == cb.data` → `unify a b` 且逐槽比 datas 值 | `678-694` |
| 17 | `(Match(s1,e1,c1), Match(s2,e2,c2))` | ① `unify s1 s2`；② `c1.len() != c2.len()` → Err；③ 逐臂要求 `p1 == p2`（`PatternDetail` 结构相等），把两侧 env 各前置 `bind_count` 个 `vvar(l+idx)`，体经 `eval_neutral` 后 `unify(l+count, ...)` | `695-756` |
| 18 | `_` | `Err(UnifyError)`（刚性失配） | `757` |

`unify_sp(l, cxt, sp, sp', spec)`（`448-470`）：两链同时空 → Ok；两头都有 → 先递归尾再比头；
否则 Err。

`flex_flex(gamma, m, sp, m', sp')`（`472-495`）：

```rust
let mut go = |m, sp, m', sp'| match self.invert(gamma, sp.clone()) {
    Err(_) => self.solve(gamma, m_prime, sp_prime, Val::Flex(m, sp)),
    Ok((pren, p1)) => self.solve_with_pren(m, pren, p1, Val::Flex(m_prime, sp_prime)),
};
if sp.len() < sp'.len() { go(m', sp', m, sp) } else { go(m, sp, m', sp') }
```

即**优先解"较短的 spine"的 meta 为另一侧**（`490-494`）。**单方向尝试、无快照回滚**（孪生模块头
`bump_spine_iter.rs:42` 同述）。

`unify_catch(cxt, t, t', span)`（`mod.rs:988-1009`）：`meta_refuel()`；`unify(cxt.lvl, cxt, t, t', None)`
（**`spec = None`：常规转换不得解假设**）；失败时用 `pretty_tm` 组装
`"can't unify\n      find: {}\n  expected: {}"` 报错（`Error` 携带 `Span<String>`）。

### 5.8 模式特化合一 `unify_pm`（`elaboration.rs:127-223`）

`(cxt, t, t', span, spec: &mut SpecSolve)`。先 `force` 两侧；`spec.acc` 非空则两侧再置于 acc 之下。
然后：

1. **双裸 Rigid 同级自反**：`(Rigid(x1,[]), Rigid(x2,[]))` 且 `x1 == x2` → Ok（`144-148`）。
2. **单侧裸 Rigid → 精化解**：`Rigid(x,[])` 一侧 → `Self::spec_refine(cxt, x, other, span, spec)`（`150-159`）。
3. `(SumCase{...}, SumCase{...})`（`161-193`）：`case_name` 不同 → `Err`；相同则
   **再比 Sum 头名** —— 若两侧 `typ` `force` 后都是 `Val::Sum` 且名字不同 → `Err`（跨 enum 重名构造子）；
   否则逐槽 `unify_pm` datas。**不比 typ 的值**（避免互相引用深递归）。
4. `(Sum(...), Sum(...))`（`194-209`）：头名相同 → 逐槽 `unify_pm` 参数值；不同 → `Err`。
5. 其余 → 落 `unify(cxt.lvl, cxt, u, v, Some(spec))`，失败时组装同样的 `can't unify` 文案（`211-221`）。

`spec_refine(cxt, x, v, span, spec)`（`227-245`）守卫，按顺序：
`v` 是 `Flex` → `Ok(())`（不精化）；
`x.0 >= cxt.lvl.0` → `Ok(())`（越界/全局层级，无操作）；
`val_mentions_lvl(&v, x)` → Err（浅 occurs，= 该臂不可达）；
否则 `spec.acc = Subst::extend(&spec.acc, x, v)`。

`SpecSolve`（`unification.rs:19-22`）：

```rust
pub(crate) struct SpecSolve<'a> { pub(crate) solvable: &'a [Lvl], pub(crate) acc: Rc<Subst> }
```

`solvable` = 本子句可解 rigid 层级（`cxt.bind_slots()`，§8.4）；`acc` = 已解替换（调用方在方程
结束后取走做 `subst_cxt`；臂边界回滚 = 恢复快照指针）。

`check_pm(cxt, raw, a)` / `check_pm_final(cxt, raw, a, ori)`（`elaboration.rs:74-122`）：

- `check_pm`：`infer_expr` → `insert` → `meta_refuel` → `solvable = cxt.bind_slots()` →
  单条方程 `unify_pm(cxt, a, inferred_type, span, spec)` → 返回 `(t_inferred, spec.acc)`；失败即 Err。
- `check_pm_final`：同前，随后**第二条方程**：`let ori_v = self.eval(&cxt.env, t_inferred.clone())`，
  `let _ = self.unify_pm(cxt, ori, ori_v, span, spec)`（**失败被容忍**，`_` 绑定），返回终态 acc。

---

## 6. 双向类型化

### 6.1 `check`（`elaboration.rs:296-376`）

入口对期望类型 `force`（`298`）。四条规则，按序：

1. **λ 检查**（`300-310`）：

```rust
(Raw::Lam(x, i, t), Val::Pi(x_t, i_t, a, b_closure))
    if (i.clone(), i_t) == (Either::Name(x_t.clone()), Icit::Impl) || i == Either::Icit(i_t) =>
{
    let body = self.check(&cxt.bind(x.clone(), self.quote(cxt.lvl, *a.clone()), *a), *t,
                          self.closure_apply(&b_closure, Val::vvar(cxt.lvl)))?;
    Ok(Tm::Lam(x, i_t, Box::new(body)))
}
```

   条件：命名隐式 `[x_t = e]` 且 Pi 是隐式，或 icity 直接相等。体在 `cxt.bind`（**名字进
   `src_names`**）下检查，余域以 `vvar(cxt.lvl)` 实例化。

2. **隐式 Π 引入**（`311-318`）：任意项 `t` 对 `Val::Pi(x, Impl, a, b)` →
   在 `cxt.new_binder(x, quote(cxt.lvl, a))`（**名字不进 `src_names`**）下 `check`，
   产出 `Tm::Lam(x, Impl, body)`。注意它排在规则 1 之后，故**显式 λ 遇到隐式 Π 会走本臂**、
   被再包一层隐式 λ。

3. **let**（`320-336`）：`check_universe(cxt, *a)`（丢弃层级）→ `va = eval(env, a_checked)` →
   `check(cxt, *t, va)` → `vt = eval(env, t_checked)` → 在
   `cxt.define(x, t_checked, vt, a_checked, va)` 下 `check(*u, a_prime)` →
   `Tm::Let(x, a_checked, t_checked, u_checked)`。

4. **洞**（`339`）：`(Raw::Hole, a) => Ok(self.fresh_meta(cxt, a))`（`a` 已是 force 后的期望类型）。

5. **match**（`341-365`）：

```rust
(Raw::Match(expr, clause), expected) => {
    let expr_span = expr.to_span();
    let (tm, typ) = self.infer_expr(cxt, *expr)?;
    let mut compiler = Compiler::new(expected);
    let error = compiler.compile(self, typ, &clause, cxt, self.eval(&cxt.env, tm.clone()))?;
    if !error.is_empty() { Err(Error(expr_span.map(|_| format!("{error:?}")))) }
    else { Ok(Tm::Match(Box::new(tm), compiler.pats)) }
}
```

   **动机/返回类型完全来自 `expected`**，不推断 motive；错误列表非空即整体 Err
   （文案 = `Vec<Warning>` 的 `Debug`，`elaboration.rs:347`）。注意产出的是
   `compiler.pats`（**已过滤**的臂表）。

6. **兜底**（`368-374`）：`infer_expr(t)` → `insert` → `unify_catch(cxt, expected, inferred_type, span)` →
   返回推断出的 `Tm`。

### 6.2 隐式插入（`elaboration.rs:16-71`）

```rust
fn insert_go(&mut self, cxt, t, va) -> (Tm, VTy) {          // 16-29
    match self.force(va) {
        Val::Pi(_, Icit::Impl, a, b) => {
            let m = self.fresh_meta(cxt, *a);
            let mv = self.eval(&cxt.env, m.clone());
            self.insert_go(cxt, Tm::App(Box::new(t), Box::new(m), Icit::Impl),
                           self.closure_apply(&b, mv))
        }
        va => (t, va),
    }
}
fn insert_t(cxt, act) = act.map(|(t,va)| insert_go(cxt, t, va));         // 30-32
fn insert(cxt, act) = act.and_then(|(t,va)|
    if t 是 Tm::Lam(_, Icit::Impl, _) { Ok((t,va)) } else { insert_t(cxt, Ok((t,va))) }); // 33-38
```

`insert_until_go(cxt, name, t, va)`（`39-63`）：沿隐式 Π 插 meta，**直到** binder 名等于
`name`，此时停下返回 `(t, Val::Pi(x, Impl, a, b))`；若走到非 Π 仍未命中 →
`Err("no named implicit arg {name}")`。`insert_until_name` = `and_then` 包装（`64-71`）。

### 6.3 `infer_expr`（`elaboration.rs:624-917`）

| 形式 | 规则 | 锚点 |
|---|---|---|
| `Raw::Var(x)` | 查 `cxt.src_names`（局部/内建，**遮蔽优先**），回落 `Infer.global_names`（顶层 def/enum/构造子，append-only）；命中 → `(Tm::Var(lvl2ix(cxt.lvl, l)), ty)`；未命中 → `Err("error name not in scope: {x}")` | `640-647` |
| `Raw::Obj(x, t)`，`t == "mk"` 且 `x` 是 `Var(sum)` | 改写为 `infer_expr(Var(sum.mk))`（`new` 的兜底形态） | `649-654` |
| `Raw::Obj(x, t)` 一般 | `infer_expr(*x)` 得 `(tm, a)`；`force(a)`：<br>**`Sum(_, params, cases)`**：若 `cases.len() == 1` 且唯一 case 名含 `".mk"`（struct），取该构造子类型，剥 Π 链求字段类型表 `ret`：隐式 binder 用头部 Sum 的**隐式实参值**（按声明序，`param.reverse()` + `pop()`，耗尽则 `Val::U(0)`）实例化；显式字段 binder 用**接收者的卡住投影** `eval(cxt.env, Tm::Obj(tm, 字段名))` 实例化。返回类型 = `ret` 中按名找到的字段类型；**否则**回落 `params` 中按名匹配项的**第三槽（该参数的类型值，`rc_take`）**；都没有 → `Err("`{tm}`: {a} has no object `{t}`")`。<br>**`SumCase{datas, ..}`**：在 `datas` 按名找字段类型；找不到 → 同样的 `has no object` 错。<br>其它 → `Err("`{tm}` has no object `{t}`")` | `649-739` |
| `Raw::Lam(x, Icit(i), t)` | 新 meta `?a : U(0)`，`a = eval ?a`；`new_cxt = cxt.bind(x, quote(cxt.lvl, a), a)`；`infer_expr(new_cxt, t)` 后 `insert`；`b_closure = close_val(cxt, b)`；返回 `(Tm::Lam(x, i, t'), Val::Pi(x, i, a, b_closure))` | `742-754` |
| `Raw::Lam(x, Either::Name(_), t)` | `Err("infer named lambda")` | `756` |
| `Raw::App(t, u, i)` | icity 解析：`Name(n)` → `insert_until_name`（结果 icit = Impl）；`Icit(Impl)` → **不插入**；`Icit(Expl)` → `insert_t`（插前置隐式）。然后 `force(tty)`：<br>`Pi(_, i_t, a, b)`：`i == i_t` → `(a, b)`；否则 `Err("icit mismatch {i:?} {i_t:?}")`。<br>非 Π：造 `?a`、`?b`（`b_closure = Closure(cxt.env, fresh_meta(&cxt.bind("x", quote a, a), U(0)))`，即在扩展上下文里生成 `(x:a) → Type 0` 类型的 meta 项），`unify_catch` 该 `Pi` 与 `tty`，取 `(a, b_closure)`。<br>最后 `check(cxt, *u, a)`，返回 `(Tm::App(t, u', i), closure_apply(b_closure, eval(u')))` | `759-819` |
| `Raw::U(n)` | `(Tm::U(n), Val::U(n + 1))` —— **`Type n : Type (n+1)`** | `822` |
| `Raw::Pi(x,i,a,b)` | `check_universe(*a)` 得 `lvl_a`；`a_eval = eval a`；`check_universe(cxt.bind(x, quote(a_eval), a_eval), *b)` 得 `lvl_b`；`universe = max(lvl_a, lvl_b)`；返回 `(Tm::Pi, Val::U(universe))` | `825-839` |
| `Raw::Let(x,a,t,u)` | 同 `check` 的 let，但体走 `infer_expr`（返回体的推断类型） | `842-866` |
| `Raw::Hole` | `?a := fresh_meta(cxt, U(0))`；`a = eval ?a`；`t = fresh_meta(cxt, a)`；返回 `(t, a)` —— **两个洞：类型洞 + 值洞** | `869-874` |
| `Raw::LiteralIntro(s)` | `(Tm::LiteralIntro(s), Val::LiteralType)` | `876` |
| `Raw::Match(_,_)` | `Err("try to infer match")` —— **match 只能 check，不能 infer** | `878` |
| `Raw::Sum(name, params, cases, universe)` | 逐参数 `infer_expr(参数类型项)` 得 `(ty_checked, typ_val)`，第二槽存 `quote(cxt.lvl, typ_val)`；返回 `(Tm::Sum(name, new_params, cases), Val::U(universe))` —— **层级直接用声明处算出的 `universe`，不重算**（`889` 注释 `//TODO: universe need to consider cases?`） | `880-891` |
| `Raw::SumCase{typ, case_name, datas}` | `infer_expr(*typ)`（丢弃其类型）得 `typ_checked`；`typ_val = eval(typ_checked)`；逐字段 `infer_expr(字段项)`；返回 `(Tm::SumCase{...}, typ_val)` —— **SumCase 的类型就是它的 `typ` 字段** | `893-915` |

### 6.4 `check_universe`（`elaboration.rs:246-295`）

```rust
let t_span = t.to_span();
let x = self.infer_expr(cxt, t);
let (t_inferred, inferred_type) = self.insert(cxt, x)?;
match inferred_type {
    Val::U(u) => Ok((t_inferred, u)),
    Val::Flex(m, sp) => {
        let (pren, prune_non_linear) = self.invert(cxt.lvl, sp.clone())
            .map_err(|_| Error(t_span.map(|_| "invert failed".to_owned())))?;
        let mty = match self.meta[m.0 as usize] {
            MetaEntry::Unsolved(ref a) => a.clone(),
            _ => unreachable!(),
        };
        if let Some(pr) = prune_non_linear {
            self.prune_ty(&pr, mty.clone()).map_err(|_| ..."prune failed")?;
        }
        if pren.dom.0 == 0 {
            match self.force(mty.clone()) {
                Val::U(x) => { self.meta[m.0 as usize] = MetaEntry::Solved(Val::U(0), mty);
                               Ok((t_inferred, 0)) },
                _ => Err(..."meta type {:?} is not a universe"),
            }
        } else {
            let rhs = self.rename(&PartialRenaming { occ: Some(m), ..pren }, Val::U(0))...;
            let solution = self.eval(&List::new(), self.lams(pren.dom, mty.clone(), rhs));
            self.meta[m.0 as usize] = MetaEntry::Solved(solution, mty);
            Ok((t_inferred, 0))
        }
    }
    _ => Err(Error(t_span.map(|_| format!("expected universe, got {:?}", inferred_type)))),
}
```

要点（形式化必须逐条照抄）：

- 返回 `u` 使被检查项 `: Type u`。**`Type N` 走 `Val::U(u)` 臂返回 `u = N`**
  （因 `infer_expr(U N) = U(N+1)`，故 `check_universe(Type N) = N`）。这就是
  `def test0: Type 1 = Type 0` 成立的机制：`Type 1` 作注解时 `check_universe` 返回 1 用于
  计算 Pi 的 max，而注解**值** `Val::U(1)` 才是体的期望类型。
- **meta 型的处理**：先 `invert(cxt.lvl, sp)`（spine 必须全是变量，否则 `"invert failed"`）；
  `mty` 必须是 `Unsolved`（**已解则 `unreachable!()` panic**，`255-258`——这是参考版与
  孪生共同保留的 `unreachable!`，见 `bump_spine_iter/machine.rs:846-853` 注释与 `:853`）。
  非线性时先做 `prune_ty` 可行性检查（结果弃置）。
  - `pren.dom == 0`（**spine 为空**）：`force(mty)` 必须是 `Val::U(_)` —— 把 meta **解为
    `Val::U(0)`（硬编码 0，绑定的 `x` 未用，源码注释 `//TODO:x?`）**，返回层级 `0`；
    否则 `"meta type {..} is not a universe"`。
  - `pren.dom != 0`：`rhs = rename({occ: Some(m), ..pren}, Val::U(0))`（失败 →
    `"when check universe, try to rename failed"`），`solution = eval(&[], lams(pren.dom, mty, rhs))`，
    meta 解为 solution，返回 `0`。
  - **两分支都返回层级 0**，与孪生一致（`bump_spine_iter/machine.rs:829-830` 注释）。
- `inferred_type` 非 `U`/非 `Flex` → `"expected universe, got {..}"`。

**非累积性**体现在两处：(a) `unify` 的 `(U x, U y) if x == y`（`unification.rs:569`）；
(b) `check_universe` 对非 `U` 类型直接报 `expected universe`。故 `Type 0` 不能当 `Type 1` 用、
`Nat` 不能当 `Type 0` 用（`Nat : Type 0` 是 `Val::U(0)` 值，只有 `Nat` 本身作注解时
`check_universe` 走 `Val::U(0)` 臂返回 0 —— 即 `def x: Type 0 = Nat` 合法而不合法
的相反方向是 `def x: Nat = Type 0`：`infer_expr(U 0) = U(1)`，`unify(Nat, U(1))` Err）。

---

## 7. 声明层

### 7.1 `Decl::Def`（`elaboration.rs:377-418`）

```rust
let ret_cxt = cxt;
// 参数折成 Π / λ（rev 折叠，保持书写顺序）
let typ = params.iter().rev().fold(ret_type, |a,b| Raw::Pi(b.0, b.2, b.1, a));
let bod = params.iter().rev().fold(body,    |a,b| Raw::Lam(b.0, Either::Icit(b.2), a));
let ret_cxt = {
    let global_idx = Lvl(self.global.len() as u32);
    let (typ_tm, _) = self.check_universe(ret_cxt, typ)?;      // 类型注解先过宇宙检查
    let vtyp = self.eval(&ret_cxt.env, typ_tm.clone());
    let fake_cxt = self.fake_bind(ret_cxt, name.clone(), vtyp.clone(), global_idx);
    self.global.insert(global_idx, Val::vvar(global_idx + 1919810));  // 递归占位
    let t_tm = self.check(&fake_cxt, bod, vtyp.clone())?;             // 体检查
    let vt = self.eval(&fake_cxt.env, t_tm.clone());
    self.global.insert(global_idx, vt.clone());                       // 覆盖真值
    self.define_global(ret_cxt, name.clone(), t_tm, vt, typ_tm, vtyp)
};
Ok((DeclTm::Def {}, Val::U(0), ret_cxt))       // 返回的“类型”是占位 U(0)（源码 TODO）
```

要点：
- **类型注解先于 `fake_bind` 检查**，故类型注解**不能**自引用（未在作用域）；
  体检查时 `fake_bind` 已生效 → 体可递归。
- 参数（`params`）的 icit 记在 `Raw::Pi`/`Raw::Lam` 上；`Decl::Def` 自身不区分隐式/显式参数域。
- 返回值 `Val` 是 `U(0)` 占位（`417` 注释 `//TODO:vt may be wrong`），调用方（`run`）忽略它。
- 缺省类型注解 → `Raw::Hole`（`parser/mod.rs:624`）→ `check_universe` 走 meta 臂解出层级 0，
  类型为一个 meta，由体检查时的 `unify` 解出。

### 7.2 `Decl::Println`（`elaboration.rs:419-423`）

`Ok((DeclTm::Println(self.infer_expr(cxt, t)?.0), Val::U(0), cxt.clone()))` —— 上下文不变；
`run` 对返回的 `Tm` 做 `nf(&cxt.env, ·)` 后 `pretty_tm` 输出（`mod.rs:1030-1036`）。

### 7.3 `Decl::Enum`（`elaboration.rs:424-556`）

1. **隐式参数域洞钉 `U(0)`**（`440-450`）：`params` 中 `Icit::Impl && matches!(a, Raw::Hole)`
   的参数域改写为 `Raw::U(0)`（理由见 `429-439` 注释：否则第 2+ 参数域成为部分应用 meta，
   使用点显式供给隐式实参时 `invert` 对非变量 spine 直接 Err → 误报）。
2. **`universe_lvl` 扫描**（`451-463`）：

```rust
let mut universe_lvl = 0;
for p in params.iter() {                                     // 注意：用改写后的 params
    if let Ok((Tm::U(lvl), _)) = self.infer_expr(cxt, p.1.clone()) {
        universe_lvl = max(lvl, universe_lvl);               // 只认“参数域写的就是 Type N”
    }
}
for case in cases.iter() {                                   // 构造子字段域
    for c in case.1.iter() {
        if let Ok((_, lvl)) = self.check_universe(cxt, c.1.clone()) {
            universe_lvl = max(lvl, universe_lvl);           // 字段类型所在的宇宙层级
        }
    }
}
```

   注意两侧**口径不同**：参数侧取"参数域项自身是 `Tm::U(lvl)` 时的 `lvl`"（非原子域如
   `Type 1 -> Type 0` 不贡献）；字段侧取 `check_universe` 的返回值（= 字段类型所在的宇宙层级）。
   失败一律静默忽略（`if let Ok`）。副作用（解 meta）照常发生。
3. **构造子类型**（`464-489`）：`new_params = params.map(|x| (x.0, x.2 /*icity*/, Raw::Var(x.0)))`；
   `default_ret = Var(name)` 依次应用到所有隐式参数（`Raw::App(·, Var(p), Icit(p.2))`）；
   `new_cases[case] = params.filter(Impl).chain(该 case 的字段列表).rev().fold(该 case 的
   `-> ret` 或 `default_ret`, |ret,x| Raw::Pi(x.0, x.2, x.1, ret))`。
4. **本体**：`sum = Raw::Sum(name, new_params, 各 case 名, universe_lvl)`；
   `typ = params.rev().fold(Raw::U(universe_lvl), |a,b| Raw::Pi(b.0, b.2, b.1, a))`；
   `bod = params.rev().fold(sum, |a,b| Raw::Lam(b.0, Icit(b.2), a))`。
   然后与 `Def` 同构地：`check_universe(typ)` → `vtyp` → `fake_bind` → global 占位 →
   `check(bod, vtyp)` → 覆盖真值 → `define_global`。
   **即 `Enum` 本体的类型是 `Type universe_lvl` 上的 Π 链，本体值是 λ 链返回 `Sum`。**
5. **逐构造子注册**（`513-555`）：对每个 case 构造
   `body_ret_type = Raw::SumCase { typ: 该 case 的 `-> ret` 或 `default_ret`,
   case_name, datas: 该 case 的字段列表.map(|(n,_,i)| (n, Var(n), i)) }`；
   构造子体 `bod = params.filter(Impl).chain(该 case 字段).rev().fold(body_ret_type, λ)`；
   构造子类型 `typ = new_cases[i].1`；然后：

```rust
let (typ_tm, _) = self.check_universe(&cxt, typ)?;
let vtyp = self.eval(&cxt.env, typ_tm.clone());
self.check_ctor_wf(&cxt, &name.data, &c.0.data, &vtyp)?;     // 良构性
let t_tm = self.check(&cxt, bod, vtyp.clone())?;
let vt = self.eval(&cxt.env, t_tm.clone());
self.define_global(&cxt, c.0.clone(), t_tm, vt, typ_tm, vtyp)  // 登记，cxt 前进
```

   构造子名 = **裸名**（无 `Enum.case` 限定别名；struct 的 case 名本身是 `Name.mk`）。

### 7.4 `check_ctor_wf`（`elaboration.rs:567-622`）

```rust
let base = cxt.lvl.0;
let mut ty = ctor_vtyp.clone(); let mut bound = 0u32;
let ret = loop {                                   // 实例化全部 Π 绑定器
    match self.force(ty.clone()) {
        Val::Pi(_, _, _, closure) => { let u = Val::vvar(Lvl(base + bound)); bound += 1;
                                       ty = self.closure_apply(&closure, u); }
        ret => break ret,
    }
};
let ret_sum = match self.force(ret) { s @ Val::Sum(..) => s,
    _ => return Err(..."构造子 {ctor_name} 的返回类型不是和类型") };
let (sname, sparams) = (Sum 的名字, 参数表);
if sname.data != enum_name { return Err(..."构造子 {ctor_name} 的返回类型是 {sname}，不是 {enum_name}") }
let non_rigid = sparams.iter().filter(|(_,_,_,i)| *i == Icit::Impl)
    .map(|(_,v,_,_)| v.as_ref())
    .find(|v| !matches!(v, Val::Rigid(l, sp) if l.0 >= base && l.0 < base + bound && sp.is_empty()));
if non_rigid.is_some() { return Err(..."构造子 {ctor_name} 的返回类型参数必须是 {enum_name} 的参数变量（参数不得特化，特化请用显式索引）") }
Ok(())
```

要点：只检查 **`Icit::Impl`** 的参数槽（显式索引参数可任意，用于索引特化）；
允许构造子重绑定参数（重绑定后仍是 telescope 内的 bare rigid）。
裸名/无 spine 要求（`sp.is_empty()`）——参数槽不得是应用。

### 7.5 全局登记两条路径

- `Infer::fake_bind(cxt, x, a, global_idx)`（`mod.rs:502-510`）：`lvl = global_idx + 1919810`；
  `global_names[x] = (lvl, Rc::new(a))`；返回 `cxt.clone()` 并 `shadow_local` 同名局部条目。
  **env/lvl/locals/pruning 全不动**。
- `Infer::define_global(cxt, x, t, vt, a, va)`（`mod.rs:515-529`）：`global_names[x] = (cxt.lvl, va)`；
  `env.prepend(vt)`；`lvl+1`；`locals = Define(父, x, a, t)`；`pruning.prepend(None)`；
  `src_names` 克隆 + `shadow_local`。**顶层 def / enum / 构造子都走这条**（`elaboration.rs:405`,
  `511`, `553`）。
  > README §2（`README.md:92-94`）说"构造子走 `Cxt::define` 登记"——**已过时**：O(D²) 修复后
  > 构造子同样走 `define_global`（真名进 `Infer.global_names`）；env/lvl/locals 效果与
  > `Cxt::define` 相同。以代码为准。
- `Infer::shadow_local(cxt, x, lvl, ty)`（`mod.rs:493-497`）：仅当 `cxt.src_names` 已有同名条目时
  覆写（否则新定义会被 `Cxt::new` 的内建 `String` / `string_concat` 遮蔽）。

---

## 8. 上下文

### 8.1 `Cxt`（`cxt.rs:24-31`）

```rust
pub struct Cxt {
    pub env: Env,                                   // 求值环境（值栈，头 = 最内层）
    pub lvl: Lvl,                                   // 层级 = 下一个可用层级 = env.len()
    pub locals: Rc<Locals>,                         // telescope（close_ty 用）
    pub pruning: Pruning,                           // 每槽掩码：bind → Some(Expl)；define → None
    pub src_names: BiMap<String, Lvl, Rc<VTy>>,     // 局部名字表（内建 + 当前 def 的 binder/let）
}
```

`Cxt::new()`（`cxt.rs:34-92`）：`empty()` 后依次 `define` 两条内建：

1. `String : LiteralType : Type 0`（`36-42`）；
2. `string_concat`：值 = `Lam(x, Expl, Lam(y, Expl, Prim))`；类型值 =
   `Pi(x, Expl, LiteralType, Closure([LiteralType], Pi(y, Expl, Var(1), Var(2))))`
   （`43-91`）。最终 `lvl = 2`、`env.len() = 2`。

`empty()`（`93-101`）：`env = []`、`lvl = 0`、`locals = Here`、`pruning = []`、`src_names = {}`。

**不变式（形式化的核心）**：`env.len() == lvl.0 == pruning.len()`；`AppPruning` 的掩码长度
等于其求值点环境长度。所有扩展操作（`bind`/`new_binder`/`define`/`define_global`）都同时
推 env 槽、`lvl+1`、一条 pruning；`fake_bind` 三者都不动；`subst_cxt` 只改 env 与 src_names 的
**内容**（包 `VSub`），不改长度。

### 8.2 四种扩展

| 方法 | env | lvl | locals | pruning | src_names | 锚点 |
|---|---|---|---|---|---|---|
| `bind(x, a_quote, a)` | `prepend(vvar(lvl))` | +1 | `Bind(·, x, a_quote)` | `Some(Expl)` | 插入 `x ↦ (旧 lvl, Rc(a))` | `cxt.rs:114-125` |
| `new_binder(x, a_quote)` | `prepend(vvar(lvl))` | +1 | `Bind(·, x, a_quote)` | `Some(Expl)` | **不变** | `127-136` |
| `define(x, t, vt, a, va)` | `prepend(vt)` | +1 | `Define(·, x, a, t)` | `None` | 插入 `x ↦ (旧 lvl, Rc(va))` | `141-152` |
| `define_global`（Infer 侧） | `prepend(vt)` | +1 | `Define(·, x, a, t)` | `None` | 不变（+shadow） | `mod.rs:515-529` |

`bind` / `new_binder` 的区别只在 `src_names` 是否插名（对应 §6.1 的规则 1 / 规则 2）。
`define` 的 `t` 与 `vt` 分别是体项与体值；`a`/`va` 是类型项与类型值。

### 8.3 `subst_cxt(sub)`（`cxt.rs:167-183`）

```rust
if sub.is_empty() { return self.clone(); }
let wrap = |v: &Val| Val::VSub(Box::new(v.clone()), sub.clone());
let mut src_names = BiMap::new();
for (k, l, ty) in self.src_names.iter_all() { src_names.insert(k.clone(), (*l, Rc::new(wrap(&**ty)))); }
Cxt { env: self.env.map(wrap), lvl: self.lvl, locals: self.locals.clone(),
      pruning: self.pruning.clone(), src_names }
```

`env` 每槽包 `VSub`、`src_names` 的类型值包 `VSub`；**lvl / locals / pruning 一律不动**
（槽位布局 = 运行时布局，被解变量仍在原槽位，读点经 `force` 展开）。
全局名字（`Infer::global_names`）不参与包裹（理由见 `cxt.rs:162-166` 注释）。

### 8.4 `bind_slots()`（`cxt.rs:191-207`）

```rust
let n = self.lvl.0;
self.env.iter().enumerate().filter_map(|(i, v)| {
    let mut raw = v;
    while let Val::VSub(inner, _) = raw { raw = inner; }        // 解包 VSub 看“槽的原始形态”
    match raw { Val::Rigid(l, sp) if sp.is_empty() && l.0 + (i as u32) + 1 == n => Some(*l),
                _ => None }
}).collect()
```

含义：取出仍是"自身 `vvar`"的槽（`env` 槽 i 对应层级 `n-1-i`）——即**真变量槽**；
`let` 定义槽（槽里是值不是 vvar）天然不在其中。这是模式特化方程的可解集
（`SpecSolve.solvable`），**不含全局**（全局不在 env 里）。

`names()`（`cxt.rs:103-112`）沿 `Locals` 收集名字（供 pretty 打印）。

---

## 9. 模式匹配编译

### 9.1 `Compiler` 结构（`pattern_match.rs:27-57`）

```rust
pub struct Compiler {
    warnings: Vec<Warning>,
    pub pats: Vec<(PatternDetail, Tm)>,      // 运行时臂表（已过滤）
    ret_type: Val,                           // = check 的期望类型（唯一返回类型来源）
    nested_checks: Vec<NestedCheck>,
    pending_pos: Vec<(Vec<(String, usize)>, Val, Val)>,
    cur_path: Vec<(String, usize)>,
}
pub enum Warning { Unreachable(Raw), Unmatched(Pattern), IncompleteNested(String) }   // 18-25
struct NestedCheck { path, field_sum: Val, cxt: Cxt, sub: Rc<Subst> }                 // 52-57
```

### 9.2 `compile`（`pattern_match.rs:190-359`）

输入 `(infer, typ, arms, cxt, target_val)`；输出 `Vec<Warning>`（空 = 无问题）。步骤：

1. `typ = force(typ)`；`constrs/c tor_names` = `typ` 是 `Val::Sum` 时的 case 名表，
   否则空（`202-209`）。**scrutinee 类型不是 Sum 时没有任何覆盖义务**（任意模式都当变量）。
2. **顶层覆盖检查**（`213-226`）：对每个 `ctor`，若
   `probe_accessible(infer, cxt, &typ, ctor, empty_sub)` 为真（可达）且没有任何臂
   `covers(pat, ctor, ctor_names)` → push `Warning::Unmatched(Pattern::Con(ctor, [Any; 999], Expl))`
   （"构造子 + 999 通配"形态）。
3. **逐臂下钻**（`229-319`），保持书写顺序：
   - 若 `shadowed`（此前出现过 catch-all 臂）→ push `Warning::Unreachable(body)`，`continue`。
   - `walk_pat` 失败 → 静默跳过（清 `pending_pos`）。
   - `check_pm_final(&cxt_walk, pat.to_raw(), typ, target_val)` 失败 → **荒谬臂静默跳过**。
   - **本层特化方程结算**（`254-289`）：`solvable = cxt_walk.bind_slots()`，
     `spec = SpecSolve{ solvable, acc: sigma0 }`；若 `top_ret` 是 `Some` →
     `unify_pm(&cxt_walk, typ, top_ret, span, &mut spec)`；再对每个
     `(_, field_sum, ret) ∈ pending_pos` → `unify_pm(&cxt_walk, field_sum, ret, ...)`；
     任一失败 → `absurd = true`，清 `pending_pos` 并 `continue`。
   - `sigma = spec.acc`；把 `pending_pos` 提升为 `NestedCheck{path, field_sum, cxt: cxt_walk, sub: sigma}`。
   - `cxt_arm = cxt_walk.subst_cxt(&sigma)`（臂上下文）。
   - **期望类型重锚**（`307-313`）：`ret_type` 是 `Flex` 则原样；否则 `quote(cxt_arm.lvl, ·)` 再
     `eval(&cxt_arm.env, ·)`。
   - `ret = infer.check(&cxt_arm, body.clone(), ret_type)?`；`pats.push((detail, ret))`。
   - `is_catch_all(pat, ctor_names)` → `shadowed = true`。
4. **警告顺序**（`320-323`）：`unreachable ++ warnings`（前者全部 Unreachable，后者全部 Unmatched）。
5. **嵌套位置覆盖检查**（`331-357`）：对每条 `NestedCheck`：
   `field_sum = force(wrap_sub(&nc.sub, nc.field_sum))`（在记录臂的终态 σ 下），取 case 名表；
   对每个 `ctor`：`probe_accessible(infer, &nc.cxt, &field_sum, ctor, &nc.sub)` 不可达 → 跳过；
   可达且 `!self.pats.iter().any(|(d,_)| cover_at(d, &nc.path) 覆盖该 ctor)` →
   push `Warning::IncompleteNested("match 不完整：模式位置 {path} 缺少构造子 {ctor}")`
   （`reported` 去重）。

`covers(pat, ctor, ctor_names)`（`553-560`）：`Any → true`；`Con(name,..) → !ctor_names.contains(name) || name == ctor`。
`is_catch_all(pat, ctor_names)`（`563-570`）：`Any → true`；`Con(name, [], _) → !ctor_names.contains(name)`。

### 9.3 `walk_pat`（`pattern_match.rs:423-549`）

返回 `(PatternDetail, Cxt, Option<Val>)`（第三项 = 该层 Con 的**走查返回类型**，已 force）。

- `Pattern::Any(span,_)`：`cxt2 = cxt.bind("_", quote(cxt.lvl, head_ty), head_ty)`；
  detail = `Any(span)`；第三项 `None`（`431-435`）。
- `Pattern::Con(name, subs, _)`：
  - `force(head_ty)` 非 `Sum`：若 `subs` 非空 → `Err("`{n}` 不是构造子，不能带子模式解构")`；
    否则按变量模式绑定 `Bind(name)`（`436-450`）。
  - `Sum(_, params, cases)` 且 `name ∉ cases`：同上，`Bind(name)`；`subs` 非空则
    `Err("`{n}` 不是该类型的构造子，不能带子模式解构")`（`451-460`）。
  - 真构造子：`infer_expr(cxt, Raw::Var(name))` 取构造子类型（`462`，与 `Var` 臂同一查表路径）；
    `impl_vals` = 头部 Sum 的**隐式**参数值（`reverse()`）。
    按 Π 链循环（`473-544`）：
    - `impl_vals.pop()` 有值 → 用它实例化（枚举隐式参数，**不占槽**；此处**不检查 binder icity**，
      依赖 `new_cases` 把枚举隐式参数排在构造子自身绑定器之前），`continue`。
    - 否则按 binder icit 从 `sub_queue`（子模式队列，前取）挑子模式：
      `Impl` binder 只接受 `get_icit() == Impl` 的子模式；`Expl` binder 只接受 `Expl`。
    - 无子模式 → 补 `PatternDetail::Any(empty_span(()))` 并 `bind(_{bname})`（构造子隐式
      binder 缺省补虚通配 / 显式字段缺子模式）。
    - `Pattern::Any` 子模式 → `Any(span)` + `bind("_{bname}")`。
    - `Pattern::Con` 子模式 → 先 `field_sum = force(dom)`；若它是 `Sum` 且含该子模式的构造子名：
      push `cur_path ∋ (name, details.len())`，递归 `walk_pat`（用 `cxt_arm`），pop 路径；
      若递归返回 `Some(inner_ret)` → push
      `pending_pos ∋ (cur_path + [(name, details.len())], field_sum, inner_ret)`；
      **否则**（字段不是含该构造子的 Sum）直接递归，不记账。
    - 每层 `u = Val::vvar(cxt_arm.lvl)`，`details.push(detail)`，
      `ty = closure_apply(&closure, u)`；`cxt_arm` 随 `bind` 增长。
  - 返回 `(Con(name, details), cxt_arm, Some(force(ty)))`。

**槽位纪律**（`413-415` 注释）：枚举隐式参数**不占槽**（用头部 Sum 实参实例化）；
构造子隐式绑定器缺省补虚通配；变量模式以用户名绑槽；**Con 本身不占槽**；
`[p]` 隐式子模式支持。因此 `details.len() == SumCase.datas.len()`，与 `eval_aux` 的
`zip` 对齐。

### 9.4 可达性探测 `probe_accessible`（`pattern_match.rs:84-150`）

```
force(head_sum) 必须是 Sum(name, params, _)：
  impl_vals = params.filter(Impl).map(值)         // 头部 Sum 的隐式实参
构造子类型：cxt.src_names(优先) 回落 infer.global_names 查 ctor 名；缺失 → false
infer.meta_refuel();  snap = infer.meta.clone()   // metas 整表快照
ty = 构造子类型值
loop:
  force(ty) 是 Pi(_,_,_,closure) ->
      u = impl_vals 用尽 ? vvar(cxt.lvl + scratch++) : impl_vals[i++]
      ty = closure_apply(closure, u)
  否则 break unify_indices(infer, cxt, sum_name, head_params, force(ty), init_sub)
              || infer.fuel_exhausted()
infer.meta = snap                                 // 整表回滚（不能 truncate）
```

`unify_indices`（`156-185`）：要求 `ret_ty` force 后是同名 `Sum` 且参数个数相同；
`SpecSolve{ solvable: cxt.bind_slots(), acc: init_sub }`，
`head_params[i].1`（头部一侧在前）与 `ret_sum.params[i].1` 逐槽 `unify_pm`，全 Ok 才算可达。
方向语义：两侧皆可解变量时解"头部变量 := 构造子侧值"。
**fuel 耗尽的失败按可达处理**（`142`，保守要求覆盖）。

---

## 10. 刻意缺口与孪生差异

### 10.1 README 明示的缺口（`README.md:288-324`）

1. **卡住 match 不可再被应用**（`README.md:290-294`；模块头 `mod.rs:1-10`）：
   `v_app` 对 `Val::Match` 走 `x => panic!("impossible apply ...")`（`mod.rs:724`）。
   合法源码（打印引用自递归卡住 match 的**函数值**）可触发；参考版与快版同崩 + parity 一致，
   属时代缺口。η 臂的 `v_applicable` 守卫已把"卡住 match / 字面量与 λ 比较"改判 `Err`。
   形式化建议：**把 `Val::Match` 应用于实参建模为 `panic`/`stuck`（未定义行为）**，或在
   类型检查器层禁止该形态。
2. **无 Match 重选 / decl 展开 / Prim 归约 / struct_eq 快路径**（`README.md:295-299`）：
   `force` 只有 Flex + VSub 两臂；卡住 match 恒卡住；`unify(Match, Match)` 的分支体在
   **中性全局视图**下重求值（`eval_neutral`），与 L07/L08 的 `struct_eq` 结构快路径不同构
   （刻意分歧）。形式化：**不给 `force` 定义 Match/Prim/decl 展开规则**。
3. **fuel 适用面**（`README.md:300-310`）：L08 fuel 的六个烧点中五个在本层无触发面
   （① meta 解链间接环——`solve` 的 `rename` 带 `occ: Some(m)` 做逐 meta occurs；
   ② `pm_defs` 精化展开——本层无该表；③ Match 重选；④ decl 展开——global 存终值、值层无 unfold；
   ⑤ Prim 归约——`Prim` 无 spine）。**唯一新增失控面是 σ 精化传播读点**，
   已用 `UNIFY_FUEL = 4096` 有界。孪生模块头"unify 无燃料"一行写于该移植之前，已过时。
4. **重定义静默覆盖**（`README.md:311-313`）：顶层 def/enum 重名不报 `redefine`
   （`global_names.insert` 直接覆写，`mod.rs:506/518`；`shadow_local` 只修同名局部影子）。
   构造子裸名跨 enum 重复按最后注册解析。形式化：环境按名查找是**覆盖语义**，无唯一性约束。
5. **显示形态刻意分歧**（`README.md:314-315`，A4-R3 定案）：构造子值打印为
   `头名::分支名(实参, …)`（`pretty.rs:212-225`）；卡住 match 显示 `(unsolved match n)`
   （`pretty.rs:226-229`）；越哨兵大下标 Var 显示 `recursive_N`（`pretty.rs:119`）；
   `SumCase.typ` 非 Sum 时沿 App 链找头名、找不到退化 `?`（`pretty.rs:236-242`）。
   这些只影响输出，不影响判定。
6. **深值路径未做迭代化**（`README.md:316-321`）：`quote`/`pretty`/深值的递归 Drop 仍是
   按值深度递归；parity/bench 在大栈线程里跑（默认 128 MB），具体栈界**未核实**。
7. （非缺口）孪生 arena 内 `XCell::VSub` 的 `Rc<SubstV>` 跨轮回收已修（`README.md:322-324`）。

### 10.2 代码中额外观察到、README 未列的限制

以下都不改变"能通过的类型检查"，但形式化时需显式决定如何处理（锚点导向）：

- `eval` 的 `Tm::Obj` 臂对**接收者不是 Sum/SumCase/Rigid** 的情形 `panic!("impossible ...")`
  （`mod.rs:777-802`）。**对 meta 接收者的投影（`?m.f`）会 panic**，因为只有 `Rigid` 才卡住。
  同理 `Sum` 接收者但字段名不在参数表里 → `.unwrap()` panic（`782`）；
  `SumCase` 的 `typ` 非 `Sum` → `panic!("impossible {t:?}")`（`789`）。
- `eval` 的全局回落对未登记层级 `.unwrap()` panic（`mod.rs:761`）；对 `x.0 < 1919810`
  且越界的 `Var` 会先下溢（`x.0 - 1919810`）。
- `v_app_pruning` 长度失配时 `panic!("impossible ...")`（`mod.rs:751`）。
- `eval` 的 `Tm::Match` 在 `eval_aux` 返回 `None` 时 `.unwrap()` panic（`mod.rs:864`）——
  静态覆盖检查是保守近似，故被探测判"不可达"但运行期实际可达的构造子会导致 panic；
  且**荒谬臂被静默丢弃**（不在 `pats` 里），故运行期该臂不可达这一前提是健全性假设。
- `check_universe` 对**已解 meta** 走 `unreachable!()`（`elaboration.rs:257`）；`lams_go`
  在类型层数不足时 `unreachable!()`（`unification.rs:395`）。孪生保留同款
  （`bump_spine_iter/machine.rs:853`）。
- `unify` 的 `(LiteralType, Prim)` 与 `(Prim, LiteralType)` 宽松臂（`unification.rs:663-664`）：
  `Prim` 与 `String` 类型被视作可互换。字面量值之间**没有**自反放行臂（只有
  `LiteralType`；`LiteralIntro` 值之间的比较落兜底 `Err`）。
- 顶层 `Decl::Def` 返回的类型是 `Val::U(0)` 占位（`elaboration.rs:415`，源码 `TODO`）；
  `DeclTm::Def {}` 不带载荷（`mod.rs:50-56`，字段被注释掉）。

### 10.3 与 `bump_spine_iter` 孪生的差异

README §4（`README.md:206-241`）与孪生模块头（`bump_spine_iter.rs:1-88`）的登记，
逐条与代码核对后的现状：

| 项 | 参考版 | 孪生 | 结论 |
|---|---|---|---|
| Ok 输出与错误**判定** | — | — | **逐字节一致**（`README.md:238-240`） |
| 错误文案内的 Debug-Val/Tm 名字 Span | 带源码偏移 | 全零 | **唯一已知偏差**；parity 比对前按 `start_offset/end_offset/path_id` 归一化（`README.md:238-240`、`bump_spine_iter.rs:48-52`） |
| 引擎形态 | 分文件、`Rc` 树、`List` | bump arena + 打包值 `V` + 迭代内核 + 记忆化 + `Tycker` 复用 | 同语义 |
| `unify` 燃料 | `UNIFY_FUEL = 4096`（`mod.rs:476`） | 模块头称"unify 无燃料" | **文档过时**：`bump_spine_iter/force.rs:107-131` 有 `refuel`/`fuel_exhausted`/`burn`，README §6.3 已声明"以 §2 为准"（`README.md:308-310`） |
| `(Obj, Obj)` 合同臂 | 有（`unification.rs:593-596`） | 模块头 `bump_spine_iter.rs:40` 称"无 (Obj,Obj) 臂" | **文档过时**：孪生 `unify.rs:596-601`、`:785-792` 皆有，注释自称"参考版新臂，L08 8988f7c 评审修复回移" |
| `LiteralType` 宽松臂 | 有（`unification.rs:662-664`） | 有（模块头臂序列在 `bump_spine_iter.rs:41`） | 一致（模块头同一行"无…宽松臂"字样自相矛盾，属笔误） |
| `SumCase/SumCase` | 比 `typ` + `datas`（`unification.rs:678-694`） | 模块头称"L07+ 只比 datas" | 孪生注释亦记"比 typ+datas"（`bump_spine_iter.rs:42-44`）；以代码/互检测试为准，两者应为同款 |
| `check_universe` | 完整（meta 两分支，返回 0） | 完整移植（`machine.rs:829-905`），**同款 `unreachable!()`** | 一致 |
| 模式编译器 | `pending_pos` 两段式 + `IncompleteNested` | 同构（`compiler.rs:46/205/245/302/364/490`） | 一致 |
| 全局名字表 | `Infer.global_names`（`mod.rs:456`） | `Machine.global_names`（`machine.rs`；孪生 `define_name_in`） | 一致（O(D²) 修复） |
| `Cxt.src_names` 克隆成本 | 逐 decl 克隆局部表（结构体头注释 `cxt.rs:10-23`；README §5 `README.md:283-286` 承认本层参考版残余更慢） | 已由 `global_names` 规避 | **性能差异，非语义差异** |

---

## 11. 形式化清单（可直接转写为归纳判断/函数）

**语法层**：`Tm`（§1.2）15 个构造子；`Val`（§2）13 个构造子；`PatternDetail` 3 个；
`Subst` + `Locals`（telescope）；`Pruning = List (Option Icit)`。

**关键不变式（Lean 4 里建议作为结构不变式/`Prop`）**：

- `env.len() = lvl = pruning.len()`；`AppPruning` 掩码长度 = 求值点 env 长度。
- `force` 返回值顶层非 `VSub`。
- `Locals` 链长度 = `lvl`。
- 模式臂 `details.len() = SumCase.datas.len()`。
- 解算 `solve`/`solve_with_pren` 只作用于 `Unsolved` meta；`occ = Some(m)` 阻止自引用。

**值层规则**（§3、§4）：`eval` 15 条（含 Prim 合并、Obj 三分支、Match 选臂）；
`v_app` 5 分支 + panic；`force` 2 臂（+ 空 σ 早退）；`frcs` 10 臂（+ 空 σ 早退）；`quote` 13 臂。

**合一规则**（§5）：`unify` 18 臂 + `unify_sp` + `flex_flex`（短 spine 优先、单方向）；
`invert`（全变量 spine + 非线性掩码）；`rename`（occurs、全局哨兵放行、scope error）；
`prune_ty`/`prune_meta`；`lams`/`solve`；`unify_pm`（5 分支 + `spec_refine` 三守卫）。

**类型层规则**（§6、§7）：`check` 6 条；`infer_expr` 14 条；`check_universe` 3 分支；
声明 `Def`/`Println`/`Enum`（含 `universe_lvl` 双口径扫描、`check_ctor_wf` 三条拒绝条件）；
模式编译 §9（顶层 `Unmatched`、遮蔽 `Unreachable`、荒谬臂静默跳过、
嵌套 `IncompleteNested`、`probe_accessible` + `unify_indices` 的可达性语义）。

**必须显式建模为"未定义/panic"的形态**（§10）：`Val::Match` 被应用；对非
Sum/SumCase/Rigid 接收者的投影；全局未登记层级；`AppPruning` 掩码长度失配；
非穷尽 match 的 `.unwrap()`；已解 meta 进入 `check_universe`/`prune` 的
`unreachable!()`；`solve` 的 `lams_go` 层数不足。
