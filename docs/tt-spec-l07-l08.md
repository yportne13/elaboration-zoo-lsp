# TYPORT 归纳族（enum）与积类型（struct）形式化规范 —— L07 / L08

> 本文是对 `elaboration-zoo-lsp` 仓库 Rust 实现（**L07_sum_type** 和
> **L08_product_type** 两层）的精确逆向工程结果，供 Lean 4 形式化直接使用。
> 所有结论都带 `file:line` 锚点，规则处引用真实 Rust / typort 源码。
>
> 阅读约定：
> - `L07` = `src/L07_sum_type/`，`L08` = `src/L08_product_type/`；
> - "参考版" = `L07/mod.rs`、`L07/elaboration.rs` 等顶层文件（树形 `Val`/`Tm` 表示）；
>   同目录下 `bump_spine_iter/` 是逐字节等价的性能孪生实现（bump arena + 迭代内核），
>   **语义以顶层参考版为准**，孪生版仅在机制落点上另行标注；
> - `L08` 的核心机**不新增任何 Tm/Val 变体**（`L08/README.md:4-9`）；
> - 行号对应本文写作时的仓库状态。

---

## 0. 全景：语言的最小内核

### 0.1 语法与项/值表示

| 概念 | 参考版定义 |
|---|---|
| 源码 AST | `Raw`（`L07/parser/syntax.rs:51-68`） |
| 模式 AST | `Pattern`（`L07/parser/syntax.rs:16-19`） |
| 声明 AST | `Decl`（`L07/parser/syntax.rs:71-84`） |
| 内核项 | `Tm`（`L07/mod.rs:65-94`） |
| 语义域（NbE 值） | `Val`（`L07/mod.rs:184-220`） |
| 编译后的模式 | `PatternDetail`（`L07/mod.rs:99-103`） |
| 显式替换 σ | `Subst`（`L07/mod.rs:237-248`） |

```rust
// L07/parser/syntax.rs:51-68
pub enum Raw {
    Var(Span<String>),
    Obj(Box<Raw>, Span<String>),          // x.field
    Lam(Span<String>, Either, Box<Raw>),
    App(Box<Raw>, Box<Raw>, Either),
    U,
    Pi(Span<String>, Icit, Box<Raw>, Box<Raw>),
    Let(Span<String>, Box<Raw>, Box<Raw>, Box<Raw>),
    Hole,
    LiteralIntro(Span<String>),
    Match(Box<Raw>, Vec<(Pattern, Raw)>),
    Sum(Span<String>, Vec<(Span<String>, Icit, Raw)>, Vec<Span<String>>),
    SumCase { typ: Box<Raw>, case_name: Span<String>, datas: Vec<(Span<String>, Raw, Icit)> },
}
```

注意：`Raw::Sum` / `Raw::SumCase` **没有对应的解析产生式**——它们只由 `enum`
声明和 `match` 编译在内部构造（`L07/parser/mod.rs:506-509` 的 `p_decl` 只有
`p_def | p_print | p_enum`；`p_atom1`/`p_raw` 里没有 Sum/SumCase）。

```rust
// L07/mod.rs:65-94（截取要点）
pub enum Tm {
    Var(Ix), Decl(SmolStr), Obj(Box<Tm>, Span<String>),
    Lam(Span<String>, Icit, Box<Tm>), App(Box<Tm>, Box<Tm>, Icit), AppPruning(Box<Tm>, Pruning),
    U, Pi(Span<String>, Icit, Box<Ty>, Box<Ty>), Let(...), Meta(MetaVar),
    LiteralType, LiteralIntro(Span<String>), Prim(SmolStr),
    /// enum 类型本体（enum 声明 λ 链的体）。params = (参数名, 值项, 值的类型, icit)
    Sum(Span<String>, Vec<(Span<String>, Tm, Ty, Icit)>, Vec<Span<String>>),
    /// 构造子值：typ 必须是其所属的（已实例化）`Val::Sum`，datas = 构造子自身绑定器的值
    SumCase { typ: Box<Tm>, case_name: Span<String>, datas: Vec<(Span<String>, Tm, Icit)> },
    Match(Box<Tm>, Vec<(PatternDetail, Tm)>),
}
```

```rust
// L07/mod.rs:184-220（截取要点）
pub enum Val {
    Flex(MetaVar, Spine), Rigid(Lvl, Spine), Decl(SmolStr, Spine),
    Obj(Box<Val>, Span<String>, Spine),          // 卡住的投影
    Lam(Span<String>, Icit, Closure), Pi(Span<String>, Icit, Box<VTy>, Closure), U,
    LiteralType, LiteralIntro(Span<String>), Prim(SmolStr, Spine),
    Sum(Span<String>, Vec<(Span<String>, Rc<Val>, Rc<VTy>, Icit)>, Vec<Span<String>>),
    SumCase { typ: Rc<Val>, case_name: Span<String>, datas: Vec<(Span<String>, Rc<Val>, Icit)> },
    Match(Box<Val>, Env, Vec<(PatternDetail, Tm)>, Vec<(Val, Icit)>),
    VSub(Box<Val>, Rc<Subst>),                   // 显式替换包裹（模式精化）
}
```

**不是**全 `Val` 都由 `Var/Decl` 区分 rigid/flex 头：`Sum` 是"类型层面的 enum 实例"，
`SumCase` 是"构造子值"，二者都是**中性值**（既非 λ 也非 Π），可以参与合一与投影。

### 0.2 全局声明表

顶层 `def` / `enum` / 构造子都登记在 `Cxt.decl: Decls`（`L07/cxt.rs:74-...`），
项里以 `Tm::Decl(name)` 引用，求值时查表取缓存的 WHNF（`L07/mod.rs:1108-1111`）。
递归的实现（`L07/elaboration.rs:216-238`）：检查 def 体之前先把名字登记为指向自身的
中性占位 `Val::Decl(name, [])`，体检查完后覆盖为真实值。`force` 对
`Decl(自身名, [])` 有自引用守卫（`L07/mod.rs:629-641`），不会自旋。

### 0.3 universe

`Ty = Tm`（`L07/mod.rs:149`）。`U` 只有一个层级（无 `Type 0 / Type 1` 分层），
`Raw::Pi` 的域与余域都在 `check_ty` 里检查成 `Val::U`（`L07/elaboration.rs:635-646`）。
`def P: A -> Type 0` 这种写法在 L13 语法里出现（`src/prelude/core/eq.typort:49`），
L07 的 `Raw` 无 `Type n` 节点，只写 `U`。

---

## 1. 归纳族声明（`enum`）的语法与 elaboration

### 1.1 语法

```rust
// L07/parser/syntax.rs:79-83
Enum {
    name: Span<String>,
    params: Vec<(Span<String>, Raw, Icit)>,                                  // 参数（隐式/显式混排）
    cases: Vec<(Span<String>, Vec<(Span<String>, Raw, Icit)>, Option<Raw>)>, // 构造子：(名, 绑定器表, 可选返回类型)
}
```

解析（`L07/parser/mod.rs:477-504`）：

```rust
fn p_enum<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
    (
        kw(EnumKeyword),
        string(Ident),
        p_pi_binder.many0().map(|x| x.into_iter().flatten().collect::<Vec<_>>()),
        brace((
            string(Ident),
            p_pi_binder.many0().map(...),
            (kw(T![->]), p_raw).option().map(|x| x.map(|y| y.1)),
        )
        .many1_sep(kw(EndLine).many1())),
    )
    .map(|(_, name, params, fields)| Decl::Enum { name, params, cases: fields })
}
```

`p_pi_binder`（`L07/parser/mod.rs:339-354`）= `p_pi_impl_binder | explicit_binder`：

```rust
square((p_bind, (kw(Colon), p_raw).option().map(...)).map(|(xs, a)| (xs, a, Icit::Impl)).many0_sep(kw(T![,])))
// 或
paren((p_bind, kw(Colon).with(p_raw)).map(|(xs, a)| (xs, a.1, Icit::Expl)).many0_sep(kw(T![,])))
```

- `[A]` → `(A, Raw::Hole, Icit::Impl)`；`[A : U]` → `(A, Raw::U, Icit::Impl)`；
- `(len : Nat)` → `(len, Raw::Var("Nat"), Icit::Expl)`；
- enum case 之间允许一个或多个 `EndLine`（注释行/空行合法，`L07/parser/mod.rs:492-495`）。

### 1.2 参数 vs 索引

**区分完全由 icit 决定**（`L07/README.md:123`、`L07/README.md:142-143`）：

- **方括号参数 = 隐式参数 = "参数"**：`enum Vec[A](len: Nat)` 里的 `A`；
- **圆括号参数 = 显式参数 = "索引"**：`len`；
- 隐式参数自动插入：构造子类型里把它前置成 Π 绑定器（§1.4），使用点缺省时
  由 `insert`/`insert_go` 插 meta（`L07/elaboration.rs:15-40`）；
- **显式参数（索引）不会自动成为构造子的绑定器**：构造子的字段/返回类型需要参数
  作 binder 时必须自己再量化一遍，例如 `box1(T : U)(x : T)`；直接写
  `box1(x : T)` 报 `name not in scope: T`（`L07/README.md:156-159`）。
  这是"索引特化"语义的推论：索引值由返回类型方程解出，前置成实参会破坏精化。

**额外的声明期规范化**（`L07/elaboration.rs:250-267`）：隐式参数中**无标注**
（`Raw::Hole`）的域被**钉成 `Raw::U`**：

```rust
let params: Vec<(Span<String>, Raw, Icit)> = params
    .into_iter()
    .map(|(n, a, i)| {
        let a = if i == Icit::Impl && matches!(a, Raw::Hole) { Raw::U } else { a };
        (n, a, i)
    })
    .collect();
```

理由（注释 `L07/elaboration.rs:250-256`）：域洞若保留，第 2+ 个隐式参数的域会成为带
pruning 的部分应用 meta（`?m A`），使用点显式供给隐式实参（`P1[Nat][Bool]`）时
`invert` 无法倒序 `Decl` 头 spine 而误报 can't unify。用户**显式标注**的域
（`[A : Nat]`）与显式索引不动。

### 1.3 enum 类型本体

`enum Name[params] { cases }` 的类型本体是（`L07/elaboration.rs:268-315`）：

```
enum_ty  := Π (params ∀) → U                       -- 逐参数包 Pi，icit 保留，域 = 用户写的域
enum_bod := λ (params ∀) → Sum(Name, [(p, Var p, icit_p) for p in params], case_names)
```

```rust
// L07/elaboration.rs:268-313（关键片段）
let new_params: Vec<_> = params.iter()
    .map(|x| (x.0.clone(), x.2, Raw::Var(x.0.clone())))   // (名, icit, 值 = 参数自身)
    .collect();
let sum = Raw::Sum(name.clone(), new_params,
                   new_cases.iter().map(|x| x.0.clone()).collect());
let typ = params.iter().rev()
    .fold(Raw::U, |a, b| Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a)));
let bod = params.iter().rev()
    .fold(sum, |a, b| Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a)));
```

要点：
- `Raw::Sum` 的第 2 个字段在 `Raw` 层是 `(名, icit, 值项)`；**值的类型是推断出来的**
  （`L07/elaboration.rs:688-698`：`infer_expr(cxt, raw)` 得值，`quote` 得类型），
  因此 `Tm::Sum`/`Val::Sum` 的参数槽是 `(名, 值, 值的类型, icit)` 四元组；
- 声明处"值项 = `Var p`"（参数自身），实例化后（`Vec[Nat] 3`）值槽携带当前实参；
- 构造子名表只是名字列表，用于投影/模式/合一里的成员判定。

类型检查与求值（`L07/elaboration.rs:314-337`）：

```rust
let typ_tm = self.check_ty(cxt, typ)?;                 // 类型本体：Π params → U
let vtyp = self.eval(decl, &cxt.env, &typ_tm);
if cxt.decl().contains_key(name.data.as_str()) { return Err(Error(format!("redefine {}", name.data))); }
let fake_cxt = cxt.decl_insert(name.clone(), DeclEntry { ty: vtyp.clone(), val: Val::Decl(name, []) });
let t_tm = self.check(&fake_cxt, bod, vtyp.clone())?;  // λ params → Sum(...)，自身引用可见
let vt = self.eval(fake_cxt.decl(), &fake_cxt.env, &t_tm);
let mut cxt = cxt.decl_insert(name.clone(), DeclEntry { ty: vtyp, val: vt });
```

**重定义规则**：`enum`/`def` 名与已有 decl 表键（builtin / 先前的 def / enum）冲突 →
`redefine {名}`；检查顺序是"先类型后重定义"（`L07/elaboration.rs:316-320`）。
构造子裸名**不做**重定义检查：跨 enum 重名按最后注册解析（`L07/README.md:146-148`）。

### 1.4 构造子类型（telescope）

缺省返回类型（`L07/elaboration.rs:273-283`）——`Name` 逐个应用到**隐式参数**：

```rust
let default_ret = params.iter()
    .filter(|x| x.2 == Icit::Impl)
    .fold(Raw::Var(name.clone()), |ret, x| {
        Raw::App(Box::new(ret), Box::new(Raw::Var(x.0.clone())), Either::Icit(Icit::Impl))
    });
```

于是 `enum Bool { true false }` 的 `true : Bool`；`enum Pair[A, B] { p }` 的 `p : Pair A B`；
`enum Vec[A](len: Nat) { ... }` 的缺省会是 `Vec A`（所以 `Vec` 的构造子都写了 `->`）。

构造子类型 = **Π(enum 隐式参数) → Π(构造子自己的绑定器) → ret**（`L07/elaboration.rs:284-299`）：

```rust
let new_cases = cases.iter().map(|(case_name, p, bind)| {
    let ty = params.iter()
        .filter(|x| x.2 == Icit::Impl)      // 隐式参数前置
        .cloned()
        .chain(p.clone())                    // 再是构造子绑定器
        .rev()
        .fold(bind.clone().unwrap_or(default_ret.clone()), |ret, x| {
            Raw::Pi(x.0.clone(), x.2, Box::new(x.1.clone()), Box::new(ret))
        });
    (case_name.clone(), ty)
}).collect::<Vec<_>>();
```

形式化摘要：

```
ctor_ty(c) = Π (A : dom_A) → … → Π (f₁ : T₁) → … → Π (fₙ : Tₙ) → ret
其中 (A…) = enum 的隐式参数（按声明序），(f₁…) = 构造子自己的绑定器（按声明序），
     ret  = 用户 `-> ret`（若给出）或 default_ret = Name A₁ … A_k（只对隐式参数）
```

注意：构造子绑定器的域 `Tᵢ` **可以引用 enum 的隐式参数**（因为它们在 Π 链前面，
检查时在作用域内），也可以引用**前面的构造子绑定器**（依赖字段）。

### 1.5 构造子**值**（body）与注册

构造子体 = `λ(隐式参数) → λ(自己的绑定器) → SumCase{ typ: ret, datas: 绑定器自身 }`
（`L07/elaboration.rs:338-377`）：

```rust
let body_ret = Raw::SumCase {
    typ: Box::new(ret.unwrap_or(default_ret.clone())),
    case_name: case_name.clone(),
    datas: binders.iter().map(|(n, _, i)| (n.clone(), Raw::Var(n.clone()), *i)).collect(),
};
let bod = params.iter().filter(|x| x.2 == Icit::Impl).cloned().chain(binders).rev()
    .fold(body_ret, |a, b| Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a)));
let typ_tm = self.check(&cxt, ctor_ty, Val::U)?;
let vtyp = self.eval(cxt.decl(), &cxt.env, &typ_tm);
self.check_ctor_wf(&cxt, &name.data, &ctor_name.data, &vtyp)?;     // §1.6
let t_tm = self.check(&cxt, bod, vtyp.clone())?;
let vt = self.eval(cxt.decl(), &cxt.env, &t_tm);
let entry = DeclEntry { ty: vtyp, val: vt };
cxt = cxt.decl_insert(SmolStr::new(format!("{}.{}", name.data, ctor_name.data)), entry.clone());
cxt = cxt.decl_insert(ctor_name.data.clone(), entry);
```

要点：
- **`Val::SumCase.typ` 是构造子应用点完整实例化后的 Sum 值**（如
  `Val::Sum("Vec", [(A, Nat), (len, succ l)], …)`），`datas` 只装构造子**自己的**
  绑定器值（隐式参数由 `typ` 的对应槽携带，不在 datas 里）；
- 注册**双轨**：限定名 `Enum.case`（`Tm::Decl("Vec.cons")`，由 `Raw::Obj` 臂特判解析）
  + 裸名别名（后注册者覆盖同名裸名）；
- 打印时限定名渲染成 `Vec::cons`（读写格式不对称，`L07/README.md:153-155`）。

### 1.6 `check_ctor_wf`：构造子良构性的**精确**条件

源码（`L07/elaboration.rs:383-443`，逐字）：

```rust
    /// 构造子返回类型良构性：实例化构造子类型的全部绑定器后，ret 的
    /// WHNF 必须是 `enum_name` 的 `Sum`，且其隐式参数位逐一等于 telescope
    /// 内的 bare rigid。允许构造子重绑定参数（`p[A,B](a,b) -> Pack[A][B]
    /// a b`——使用点经特化方程解回枚举参数，v3_multi_index_gadt 钉），
    /// 拒绝参数位为非变量的特化（`c -> Foo[Bool]`）与非本 enum 的 ret
    /// （`c -> Nat`）：后者向构造子名字空间注入永不匹配任何模式的
    /// phantom 值，对覆盖检查完备的 match 在封闭输入上卡死。
    fn check_ctor_wf(
        &mut self,
        cxt: &Cxt,
        enum_name: &str,
        ctor_name: &str,
        ctor_vtyp: &Val,
    ) -> Result<(), Error> {
        let decl = cxt.decl();
        let base = cxt.lvl.0;
        let mut ty = ctor_vtyp.clone();
        let mut bound = 0u32;
        let ret = loop {
            match self.force(decl, ty) {
                Val::Pi(_, _, _, closure) => {
                    let u = Val::vvar(Lvl(base + bound));
                    bound += 1;
                    ty = self.closure_apply(decl, &closure, u);
                }
                ret => break ret,
            }
        };
        let ret_sum = match self.force(decl, ret) {
            s @ Val::Sum(..) => s,
            _ => {
                return Err(Error(format!(
                    "构造子 {ctor_name} 的返回类型不是和类型"
                )))
            }
        };
        let (sname, sparams) = match &ret_sum {
            Val::Sum(n, ps, _) => (n, ps),
            _ => unreachable!(),
        };
        if sname.data != enum_name {
            return Err(Error(format!(
                "构造子 {ctor_name} 的返回类型是 {}，不是 {enum_name}",
                sname.data
            )));
        }
        let non_rigid = sparams
            .iter()
            .filter(|(_, _, _, i)| *i == Icit::Impl)
            .map(|(_, v, _, _)| v.as_ref())
            .find(|v| {
                !matches!(v, Val::Rigid(l, sp) if base <= l.0 && l.0 < base + bound && sp.is_empty())
            });
        if let Some(v) = non_rigid {
            let _ = v;
            return Err(Error(format!(
                "构造子 {ctor_name} 的返回类型参数必须是 {enum_name} 的参数变量（参数不得特化，特化请用显式索引）"
            )));
        }
        Ok(())
    }
```

**算法（可直接实现的形式）**，设检查点上上下文层级为 `base`：

1. **实例化 telescope**：反复 `force`；每遇到一个 `Π`，注入新 rigid
   `Val::Rigid(Lvl(base + bound), [])`（`bound` 从 0 起递增），得到 `ret`。
   绑定器的名字与 icit **全部忽略**——只数个数。记最终 `bound = k`（构造子类型的
   Π 深度）。
2. **ret 必须是本 enum 的 `Sum`**：
   - `force(ret)` 不是 `Val::Sum` → `构造子 {c} 的返回类型不是和类型`；
   - `Sum` 的头名 `≠ enum_name` → `构造子 {c} 的返回类型是 {sname}，不是 {enum_name}`。
3. **隐式参数位必须是 telescope 内的 bare rigid**：对返回 Sum 的**每一个 icit = Impl
   的参数槽**，其值必须是形如 `Val::Rigid(l, [])` 且 `base ≤ l < base + bound`。
   否则 → `构造子 {c} 的返回类型参数必须是 {enum_name} 的参数变量（参数不得特化，特化请用显式索引）`。
   - **只检查 Impl 参数位**；Expl（索引）位**不受限**（索引就是用来特化的，见 §1.2）。
   - `sp.is_empty()` 要求 bare：带 spine 的 rigid（`A x`）也不合格。
4. 显式参数（索引）**不检查**个数是否与被匹配类型一致——那个检查在模式匹配侧
   （`unify_indices` 的长度比较，`L07/pattern_match.rs:369-371`）。

**允许的"重绑定惯用法"**（`L07/elaboration.rs:385-386` 注释；回归钉
`tests/l07_blackbox_v3.rs:530-558` 的 `v3_multi_index_gadt`）：

```typort
enum Pack[A, B](x: A, y: B) {
    p[A, B](a: A, b: B) -> Pack[A][B] a b     -- 构造子重新绑定 A、B，合法
}
def sw: Pack[Nat][Bool] zero true = p[Nat][Bool] zero true
def un(p: Pack[Nat][Bool] zero true): Bool =
    match p { case p(a, b) => b }
```

合法原因：`ret = Pack[A][B] a b` 的两个 Impl 槽分别是**构造子自己重新绑定的** `A`、`B`，
它们落在 telescope 的 rigid 区间内（`bound` 覆盖它们），只是**名字**与 enum 参数
同名/不同名都无所谓，检查只看"是不是本 telescope 的 bare rigid"。使用点通过特化
方程把 enum 参数解回这些变量。

**被拒绝的两类**（各自有回归钉）：

| 形态 | 例子 | 报错 | 钉 |
|---|---|---|---|
| ret 不是本 enum | `enum Foo { c -> Nat }` | `构造子 c 的返回类型是 Nat，不是 Foo` | `L07/tests.rs:1700-1717` |
| Impl 参数位被特化 | `enum Foo[A] { c -> Foo[Bool] }` | `…参数必须是 Foo 的参数变量（参数不得特化，特化请用显式索引）` | `L07/tests.rs:1719-1741` |

目的（注释 `L07/elaboration.rs:387-389`）：拒绝向构造子名字空间注入"永不匹配任何模式
的 phantom 值"——对覆盖检查完备的 `match`，这种值会让封闭输入上的 match 卡死。

**与 L08 的差异**：L08 的同名函数（`L08/elaboration.rs:397-450`）逐句相同；
L08 唯一的不同是它在 §5 修了 `unify` 的 Π 臂 quote 层级 bug（`L08/README.md:103-113`）。

---

## 2. 消去（elimination）：`match` 的类型规则与编译

### 2.1 语法与"只能检查"

```rust
// L07/parser/mod.rs:419-433
fn p_match<...>(...) -> IResult<'a, 'b, Raw> {
    (kw(MatchKeyword), p_raw,
     brace((kw(CaseKeyword), p_pattern, kw(T![=>]), kw(EndLine).option(), p_raw)
        .map(|(_, pattern, _, _, body)| (pattern, body))
        .many0_sep(kw(EndLine).many1())))
    .map(|(_, scrutinee, body)| Raw::Match(Box::new(scrutinee), body))
}
```

```rust
// L07/elaboration.rs:122-127 —— match 只在 check 模式
(Raw::Match(expr, clauses), expected) => {
    let (tm, typ) = self.infer_expr(cxt, *expr)?;
    let mut compiler = Compiler::new();
    compiler.compile(self, typ, tm.clone(), &clauses, cxt, expected)?;
    Ok(Tm::Match(Box::new(tm), compiler.pats))
}
```

```rust
// L07/elaboration.rs:683-686 —— infer 模式下直接报错
Raw::Match(..) => Err(Error(
    "match cannot be inferred; give it an expected type".to_owned(),
)),
```

**类型规则（非形式化）**：

```
Γ ⊢ s ⇒ D p̄ ī          Γ, (臂上下文) ⊢ motive …           每个臂编译通过
────────────────────────────────────────────────────────────────────────
Γ ⊢ match s { arms } ⇐ motive
```

- `match` **必须**有期望类型（motive），它决定每个分支体的检查类型；
- scrutinee 是**推断**的（`infer_expr`），其 WHNF 必须是 `Val::Sum`，否则
  `match 的对象必须是和类型（enum）`（`L07/pattern_match.rs:125-128`）；
- 结果项是 `Tm::Match(scrut, compiled_arms)`，`compiled_arms` 的元素是
  `(PatternDetail, Tm)`（已编译模式 + 已检查的体）。

### 2.2 模式表示

**源码模式**（`L07/parser/syntax.rs:16-19`）：

```rust
pub enum Pattern {
    Any(Span<()>, Icit),
    Con(Span<String>, Vec<Pattern>, Icit),
}
```

解析（`L07/parser/mod.rs:406-417`）：

```rust
fn p_pattern<...>(...) -> IResult<'a, 'b, Pattern> {
    (string(Ident),
     paren(p_pattern.many0_sep(kw(T![,])))
        .or(square(p_pattern.map(|x| x.to_impl()).many0_sep(kw(T![,]))))
        .many0().map(|x| x.concat()))
        .map(|(x, t)| Pattern::Con(x, t, Icit::Expl))
        .or(kw(T![_]).map(|x| Pattern::Any(x, Icit::Expl)))
}
```

- `_` → `Pattern::Any`；
- 任何其它 Ident → `Pattern::Con(name, subpats, Expl)`，**即使它其实是个变量**
  （`cons(x, xs)` 里的 `x` 就是 `Con("x", [], Expl)`）；
- 子模式用圆括号 → `Expl`；用**方括号** → `to_impl()` 强制 `Impl`
  （`L07/parser/syntax.rs:22-27`），即**隐式子模式 `[p]`**；
- 嵌套 `Con` 可以任意深。

**编译后模式**（`L07/mod.rs:96-113`）：

```rust
/// 编译后的模式。bind_count = 该模式在运行时消耗的 env 槽数：
/// Any / Bind 各占 1 槽（整个 head 值），Con 占 1 槽（head 自身）加各子模式槽数。
pub enum PatternDetail {
    Any(Span<()>),
    Bind(Span<String>),
    Con(Span<String>, Vec<PatternDetail>),
}
impl PatternDetail {
    pub fn bind_count(&self) -> u32 {
        match self {
            PatternDetail::Any(_) => 1,
            PatternDetail::Bind(_) => 1,
            PatternDetail::Con(_, subs) => 1 + subs.iter().map(|s| s.bind_count()).sum::<u32>(),
        }
    }
}
```

- `Any` 与 `Bind` 的**运行时行为完全相同**（都 prepend head 值，`L07/pattern_match.rs:708`）；
  区别只在显示/覆盖语义：`Any` 来自 `_` 或缺失的隐式绑定器，`Bind` 来自"写成标识符
  但该名字不是头部类型的构造子"（`L07/pattern_match.rs:457`、`:480`、`:610`）。
- `bind_count` 是**槽位契约**：编译期绑定的槽数、运行时 prepend 的槽数、
  quote/rename 分支体时喂的 fresh rigid 数三方必须一致
  （`L07/pattern_match.rs:421-426`、`L07/mod.rs:1285-1287`）。

### 2.3 编译总流程（`Compiler::compile`）

`L07/pattern_match.rs:111-267`。数据结构（`:46-71`）：

```rust
pub struct Compiler {
    pub errors: Vec<String>,                 // 一次报全：覆盖缺失 / 分支不可达
    pub pats: Vec<(PatternDetail, Tm)>,
    sub: Rc<Subst>,                          // 当前精化替换 σ（持久化单链，链头 = 最新）
    solvable: Vec<Lvl>,                      // 本子句可解的 rigid 层级
    nested_checks: Vec<NestedCheck>,         // 嵌套覆盖记账
    pending_pos: Vec<(Vec<(String, usize)>, Val)>, // 本臂待提升的位置
    cur_path: Vec<(String, usize)>,          // 当前下钻路径（根 → 当前字段）
}
```

算法（按源码顺序）：

```
compile(scrut_ty, scrut, arms, cxt, expected):
  head_val ← eval(scrut)                       -- match 现场的被匹配值
  meta_refuel()                                 -- 共享 fuel 池充值
  head_sum ← force(scrut_ty) 必须是 Val::Sum    -- 否则 Err "match 的对象必须是和类型（enum）"
  ctor_names ← head_sum 的构造子名表
  self.solvable ← cxt.bind_slots()              -- §2.7.3 可解集基线

  -- ① 顶层覆盖检查（用无臂无关的探测）
  for ctor in head_sum 的每个构造子:
      if probe_accessible(cxt.lvl, head_sum, ctor, σ, solvable)
         and not any arm 的 covers(pat, ctor, ctor_names):
          errors += "match 不完整：缺少构造子 {ctor}"

  -- ② 逐臂下钻（保持用户书写顺序 = 运行时首匹配）
  shadowed ← false
  for (pat, body) in arms:
      if shadowed: errors += "分支不可达：模式 {pat} 被前面的通配臂遮蔽"; continue
      sub_snap ← σ;  solvable_snap ← solvable
      match walk(pat, scrut_ty, head_val, cxt):
        Matched(detail, cxt_arm):
            -- 提升本臂的嵌套位置记账（此刻 σ 为终态）
            for (path, field_sum) in pending_pos:
                nested_checks += NestedCheck{path, field_sum, σ, solvable, cxt_arm.lvl}
            cxt_arm' ← cxt_arm.subst_cxt(σ)                  -- §2.7.2
            ret_type ← 重锚(expected, σ, cxt_arm')            -- §2.8
            tm ← check(cxt_arm', body, ret_type)              -- spec 不穿参
            pats += (detail, tm)
            if is_catch_all(pat, ctor_names): shadowed ← true
        Unreachable:
            pending_pos.clear()
            errors += "分支不可达：模式 {pat} 与被匹配类型不相容"
      σ ← sub_snap;  solvable ← solvable_snap;  cur_path.clear()   -- 臂边界回滚

  -- ③ 嵌套位置覆盖检查
  for nc in nested_checks:
      field_sum ← force(wrap_sub(nc.sub, nc.field_sum))   -- 置于记录臂的终态 σ 之下
      必须是 Val::Sum，否则 skip
      for ctor in field_sum 的构造子:
          if not probe_accessible(nc.lvl, field_sum, ctor, nc.sub, nc.solvable): continue
          covered ← pats 中存在 d 使 cover_at(d, nc.path) 为 All 或 Ctor(ctor.data)
          if not covered and (nc.path, ctor.data) 未报过:
              errors += "match 不完整：模式位置 {fmt_path(path)} 缺少构造子 {ctor}"

  if errors 非空: Err(errors.join("\n")) else Ok(())
```

### 2.4 下钻 `walk` / `walk_con`：槽位纪律

`Lang: Pattern::Any`（`L07/pattern_match.rs:406-419`）：

```rust
Pattern::Any(span, _) => {
    let lvl = cxt.lvl;
    let cxt = cxt.bind(span.map(|_| "_".to_owned()),
                       infer.quote(cxt.decl(), cxt.lvl, head_ty.clone()), head_ty);
    self.solvable.push(lvl);
    Ok(Walk::Matched(PatternDetail::Any(span), cxt))
}
```

`walk_con`（`L07/pattern_match.rs:431-669`）步骤：

1. `head_sum ← force(wrap_sub(σ, head_ty))`；若不是 `Val::Sum`，或 `name` 不在
   该 Sum 的构造子表里 → **变量绑定**：不允许带子模式（否则
   `` `x` 不是构造子，不能带子模式解构 `` / `` `x` 不是 {Sum} 的构造子… ``），
   绑定 `PatternDetail::Bind(name)`；若带子模式就报错。
2. 取构造子声明 `entry ← cxt.decl_get("{Sum}.{name}")`（找不到 → `找不到构造子 {Sum}.{name}`）。
3. **head 槽**：`Con` 模式自身占一槽——先 `cxt.bind("_{name}", quote(head_ty), head_ty)`
   并 `solvable.push(lvl)`（`L07/pattern_match.rs:485-494`）。
4. **剥构造子 Π 链**（`:506-621`）：逐个 `force` 构造子类型；
   - 若还在 enum 隐式参数区（`impl_idx < impl_vals.len()`）：用**头部 Sum 的实参值**
     实例化，**不产生槽**、不消耗用户子模式；
   - 否则是一个构造子绑定器 `(bname, bicit, dom, closure)`：
     - 用户子模式按 icit 对齐：`Impl` 绑定器可缺省（自动 `Any`），
       仅当 `sub_queue` 队首 icit 也是 `Impl` 时取用；`Expl` 绑定器**必须**有
       `Expl` 子模式，否则 `构造子 {name} 缺少字段 {bname} 的模式`；
     - 绑定器的"值"一律是 **fresh rigid**：`let u = Val::vvar(cxt.lvl);`（`:542`）；
     - 子模式分派（`:543-613`）：
       - `None`（隐式缺省）→ `PatternDetail::Any(empty_span(()))`，绑定 `_{bname}`；
       - `Pattern::Any(sp, _)` → `PatternDetail::Any(sp)`；
       - `Pattern::Con(cn, csubs, _)` 且 **`cn` 是该字段 Sum 的构造子** → 递归
         `walk_con(cn, csubs, dom, u, cxt)`（子 walk 入口绑自己的 head 槽，槽值 = `u`），
         同时 `pending_pos.push((cur_path ++ [(name, details.len())], field_sum))`；
         `cur_path` push/pop 平衡；递归返回 `Unreachable` 则整臂 `Unreachable`；
       - `Pattern::Con(cn, [], _)` 但不能解构 → `PatternDetail::Bind(cn)`（变量绑定）；
         带子模式则报错；
     - `details.push(detail)`；`ctor_datas.push((bname, Rc::new(u), bicit))`；
       `ty ← closure_apply(closure, u)`。
5. 子模式多余 → `构造子 {name} 的模式多了 {n} 个子模式`（`:622-628`）。
6. `ret_sum ← force(wrap_sub(σ, ret))`，必须 `Val::Sum`（否则
   `构造子 {name} 的返回类型不是和类型`）。
7. **特化方程**（§2.5）→ 失败则 `Walk::Unreachable`。
8. **头部精化**（§2.6）。
9. 返回 `Walk::Matched(PatternDetail::Con(name, details), cxt)`。

**槽位契约**（`L07/pattern_match.rs:421-426` 的注释，形式化时是关键不变式）：

> 每个绑定器一个槽，先绑定后下钻；构造子 Pi 链上每个绑定器都在当前 `cxt.lvl`
> 处绑定为 fresh rigid（枚举隐式参数除外：用头部 Sum 的实参实例化，不产生槽）。
> **编译期绑定、运行时 prepend、bind_count 三方同序同数。**

### 2.5 特化方程（specialization by unification）

`L07/pattern_match.rs:350-396`：

```rust
    /// 特化方程：头部 Sum 的参数（含索引）与构造子返回 Sum 的参数逐槽合一，
    /// **头部一侧在前**——两侧都是可解变量时解的方向是"头部变量 := 构造子
    /// 侧值"（即"老的变量 := 新的变量"，与上下文顺序一致）。解累积进
    /// `spec.acc`（调用方以当前 σ 作种子，方程后取回新 σ）；方程两侧由
    /// unify 入口置于 acc 之下解释（`subst ɑ vs` 的惰性等价物），无需在此
    /// 预包裹。
    fn unify_indices(
        infer: &mut Infer, cxt: &Cxt, lvl: Lvl, spec: &mut SpecSolve<'_>,
        head_sum: &Val, ret_sum: &Val, ctor: &str,
    ) -> Result<(), Error> {
        let (hp, rp) = match (head_sum, ret_sum) {
            (Val::Sum(_, p1, _), Val::Sum(_, p2, _)) => (p1, p2),
            _ => return Err(Error(format!("构造子 {ctor} 的返回类型不是和类型"))),
        };
        if hp.len() != rp.len() {
            return Err(Error(format!("构造子 {ctor} 与被匹配类型的参数数不一致")));
        }
        for (a, b) in hp.iter().zip(rp.iter()) {
            infer.unify(cxt.decl(), lvl, cxt,
                        a.1.as_ref().clone(),   // 头部参数值（在前）
                        b.1.as_ref().clone(),   // 构造子返回参数值
                        Some(spec))
                 .map_err(|_| { /* fuel 尾注 */ Error(format!(
                     "构造子 {ctor} 与被匹配类型不相容（分支不可达）{fuel_note}")) })?;
        }
        Ok(())
    }
```

调用点（`L07/pattern_match.rs:641-649`）：

```rust
let mut spec = SpecSolve { solvable: &self.solvable, acc: self.sub.clone() };
let spec_res = Self::unify_indices(infer, &cxt, cxt.lvl, &mut spec, &head_sum, &ret_sum, &name.data);
self.sub = spec.acc;                       // 取回新 σ
if spec_res.is_err() { return Ok(Walk::Unreachable); }
```

`SpecSolve`（`L07/unification.rs:37-45`）：

```rust
/// 特化合一的进行时状态（dpm-nbe `unifyS` 的 Γ-shrinking + ɑ-accumulation
/// 的 Rust 形态）。`solvable` = 本子句可解的 rigid 层级（模式槽 + 外层
/// bind 槽基线）；`acc` = 已解出的替换——编译器的 σ 作种子，方程途中
/// 叠加，调用方在方程结束后取走 `acc` 作为新 σ
pub(crate) struct SpecSolve<'a> {
    pub(crate) solvable: &'a [Lvl],
    pub(crate) acc: Rc<Subst>,
}
```

**合一器中的"可解 rigid"规则**（`L07/unification.rs:895-928`）——这是"方程解得出 ⇔
分支可达"的唯一判据：

```rust
            // 模式特化（dpm-nbe unify1 的 VVar 臂）：可解 rigid（spec 携带的
            // 模式槽集）与非 Flex 值相遇 ⇒ 解入 `spec.acc`（显式替换，force
            // 读点惰性展开）。Flex 除外——交给 Flex 规则（meta := var）。
            // occurs 环守卫失败 = Err（对齐旧 pm_solve false ⇒ Err：调用侧
            // 判为分支不可达）。spec = None（常规转换）时守卫不成立，落空
            // 到后续臂——不得解假设，否则 `Eq x y` 会被"证成" `Eq y y`。
            (Val::Rigid(x, sp), v)
                if sp.is_empty()
                    && matches!(spec.as_deref(),
                        Some(s) if s.solvable.contains(x) && !matches!(v, Val::Flex(..))) =>
            {
                if val_mentions_lvl(v, *x) { return Err(UnifyError); }
                let s = spec.as_deref_mut().unwrap();
                s.acc = Subst::extend(&s.acc, *x, v.clone());
                Ok(())
            }
            (v, Val::Rigid(x, sp)) if /* 对称 */ { … }
```

并且 unify 入口把方程两侧置于**已积累的解**之下（`L07/unification.rs:854-865`）：

```rust
let mut t = self.force(decl, t);
let mut u = self.force(decl, u);
if let Some(s) = spec.as_deref() {
    if !s.acc.is_empty() {
        t = self.force(decl, wrap_sub(&s.acc, t));
        u = self.force(decl, wrap_sub(&s.acc, u));
    }
}
```

**与普通转换的分工**：分支体检查走 `spec = None`（`unify_catch`，
`L07/mod.rs:1317-1330`），此时"可解 rigid"规则不成立，`unify` 不得解假设。
这就是 README §1.2 纪律三的"两副面孔"。

### 2.6 头部精化（"as 方程" / "scrutinee ≐ pattern value" 的落地）

**本实现没有 surface 的 `as` 模式**（全仓库无 `Pattern::As`，grep 无命中）。
任务里说的两类方程在本实现中这样落地：

1. **"scrutinee ≐ pattern value"（as 方程）**：`Con` 模式的 **head 槽**占一个 env 槽，
   运行时 prepend 的正是**被匹配值自身**（`L07/pattern_match.rs:729`：
   `let mut cur = env.prepend(head.clone());`）。所以"把 scrutinee 命名为整个模式的值"
   由这个槽表达——它确实被绑定，但**没有对应的源码名字**（槽名是 `_{ctor}`）。
2. **"scrutinee 变量 ≐ 构造子值"（索引精化）**：把被匹配的变量写进 σ。

源码（`L07/pattern_match.rs:650-667`，逐字）：

```rust
        // 头部精化（无条件）：被匹配变量本身写入精化替换。`V a`、`add a zero`
        // 这类依赖被匹配变量的类型，要等 a := zero / a := succ t 之后才能
        // 归约——force 在读点推进 VSub（σ 链逐层推开）。只对"本子句里尚未
        // 精化的变量"做（σ 已有解的不会再以 bare Rigid 出现）。存入的构造
        // 子值用当前 σ 包裹——后续嵌套方程的解经组合链对其保持可见。
        if let Val::Rigid(x, sp) = &infer.force(cxt.decl(), wrap_sub(&self.sub, head_val.clone())) {
            if sp.is_empty() && x.0 < cxt.lvl.0 && self.solvable.contains(x) && !self.sub.has(*x) {
                let ctor_val = Val::SumCase {
                    typ: Rc::new(head_sum.clone()),
                    case_name: name.clone(),
                    datas: ctor_datas,
                };
                // 环守卫（浅 occurs）失败时跳过精化，不阻断分支检查
                if !val_mentions_lvl(&ctor_val, *x) {
                    self.sub = Subst::extend(&self.sub, *x, wrap_sub(&self.sub, ctor_val));
                }
            }
        }
```

条件逐条：

| 条件 | 含义 |
|---|---|
| `force(wrap_sub(σ, head_val)) = Rigid(x, [])` | 被匹配值在**当前精化下**仍是 bare rigid（不是已解出的构造子值、不是 neutral 应用） |
| `x.0 < cxt.lvl.0` | `x` 是**上下文里的真变量**（不是下钻途中新建的槽） |
| `self.solvable.contains(x)` | `x` 在可解集里（`bind_slots` 基线或本子句新绑的槽） |
| `!self.sub.has(*x)` | 本子句**尚未**精化过它（σ 已有解则跳过） |
| `!val_mentions_lvl(&ctor_val, *x)` | **浅 occurs 环守卫**：解值不得引用 `x` 自身；失败则**跳过精化但不阻断**分支检查 |

解值 `ctor_val = Val::SumCase { typ = head_sum, case_name, datas = ctor_datas }`：

- `typ` 是**头部 Sum**（不是构造子返回 Sum）——头部精化写入的构造子值天然带正确类型
  （`L07/README.md:193`）；
- `datas` 是构造子自己的绑定器值（fresh rigid，§2.4 步骤 4），枚举隐式参数不在其中；
- 用 `wrap_sub(σ, ctor_val)` 包裹后再 `Subst::extend`，使后续嵌套方程的解经组合链可见
  （`L07/pattern_match.rs:653-654`）。

**runs 何时生效**：σ 只对**被包裹过的值**生效（`wrap_sub` 的纪律）；读点 `force` 的
`VSub` 臂把 σ 推进结构（§2.7.1）。这一条精化让 `x` 在分支体、期望类型、以及**卡住的
match 内部**（`force` 的 Match 重选）都变成构造子值。

### 2.7 `Subst` / σ 显式替换的精确语义

#### 2.7.1 表示与查找

```rust
// L07/mod.rs:224-248
/// 模式特化的解：层级 → 值 的**持久化单链**（dpm-nbe 的 explicit
/// substitution；链头 = 最新的解）。仅由模式编译器经 `Subst::extend` /
/// 特化合一的 `SpecSolve::acc` 构建；`Rc` 共享让臂边界回滚 = 指针赋值、
/// `Val::VSub` 包裹 = O(1)。
pub struct Subst { head: Option<Rc<SubEntry>> }
struct SubEntry { lvl: Lvl, val: Val, next: Option<Rc<SubEntry>> }
```

| 操作 | 语义 | 源码 |
|---|---|---|
| `extend(σ, x, v)` | O(1) cons 到链头（链头 = 最新，同键旧条目留在链上但永不命中） | `L07/mod.rs:331-339` |
| `has(σ, x)` | 链上是否存在 `x` | `L07/mod.rs:318-327` |
| `lookup_hit(σ, x)` | 沿链找第一个 `lvl == x`。**命中时**：若解值不引用 σ 的任何已解层级则原样返回；否则返回 `VSub(解值, 整条 σ)`（把更新的解叠在解值外） | `L07/mod.rs:260-273` |
| `lookup(σ, x)` | `lookup_hit` 未命中 ⇒ fresh rigid `Rigid(x, [])`（dpm-nbe `lookupSub` 的恒等延拓） | `L07/mod.rs:276-278` |
| `compose(outer, inner)` | 内层先、外层后；外层条目接链头（先被查到 = 覆盖同键） | `L07/mod.rs:344-361` |
| `wrap_sub(σ, v)` | σ 空则直通（零开销）；否则 `Val::VSub(Box::new(v), σ)` | `L07/mod.rs:385-391` |

```rust
// L07/mod.rs:383-391
pub(crate) fn wrap_sub(sub: &Rc<Subst>, v: Val) -> Val {
    if sub.is_empty() { v } else { Val::VSub(Box::new(v), sub.clone()) }
}
```

#### 2.7.2 σ 施加到上下文（`subst_cxt`）

```rust
// L07/cxt.rs:329-352
    /// 把精化替换 σ 施加到上下文（dpm-nbe `subst sub ctx`）：env 槽与
    /// src_names 的类型包 `VSub`；lvl / locals / pruning / decl 不动——
    /// **槽位布局（= 运行时布局）不变**，被解变量仍在原槽位，读点经
    /// force 展开看到解。σ 为空时零开销直通。
    pub fn subst_cxt(&self, sub: &Rc<super::Subst>) -> Self {
        if sub.is_empty() { return self.clone(); }
        let wrap = |v: &super::Val| super::Val::VSub(Box::new(v.clone()), sub.clone());
        Cxt {
            env: self.env.map(wrap),
            lvl: self.lvl,
            locals: self.locals.clone(),
            pruning: self.pruning.clone(),
            src_names: Rc::new(self.src_names.iter()
                .map(|(k, e)| (k.clone(), Rc::new((e.0, wrap(&e.1)))))
                .collect()),
            decl: self.decl.clone(),
        }
    }
```

**关键不变式**：`lvl`、槽位数、pruning、de Bruijn 索引**一概不动**。旧实现"改写 env 槽
+ quote→eval 刷新"的做法被显式替换按构造排除（`L07/README.md:38-55`）。

#### 2.7.3 可解集基线（`bind_slots`）

```rust
// L07/cxt.rs:354-376
    /// 当前上下文里"真变量"（bind 槽，env 槽仍指向自身 vvar）的层级集合：
    /// 这些是模式特化方程可以求解的对象。let 定义槽（槽里是值不是
    /// vvar）天然不在其中。嵌套 match 的入口上下文可能已被外层精化
    /// 包裹（`subst_cxt`）——解包 VSub 看**槽的原始形态**；外层已解变量
    /// 也按 raw 层级进入基线（无害：方程里它不再以 bare rigid 出现，
    /// force 在读点已展开）。
    pub fn bind_slots(&self) -> Vec<Lvl> {
        let n = self.lvl.0;
        self.env.iter().enumerate().filter_map(|(i, v)| {
            let mut raw = v;
            while let Val::VSub(inner, _) = raw { raw = inner; }
            match raw {
                Val::Rigid(l, sp) if sp.is_empty() && l.0 + (i as u32) + 1 == n => Some(*l),
                _ => None,
            }
        }).collect()
    }
```

即：env 槽仍是"自引用 vvar"（`lvl` 与位置自洽）的那些层级是**可解**的；
`let` 绑定槽（槽里是值）不在其中。

#### 2.7.4 σ 的推进：`force` 的 `VSub` 臂与 `frcs`

```rust
// L07/mod.rs:589-605（force 入口）
pub fn force(&self, decl: &Decls, t: Val) -> Val {
    match t {
        Val::Flex(m, sp) => match self.lookup_meta(m) { ... },
        // 显式替换（dpm-nbe `frc`）：把模式精化的解推进值的结构。入口
        // 不烧 fuel——真正的精化传播只发生在被解变量的读点（frcs 的
        // Rigid 臂 lookup 命中时烧 1）…
        Val::VSub(v, sub) => self.frcs(decl, &sub, *v),
        ...
    }
}
```

`frcs`（`L07/mod.rs:673-787`）的**槽位纪律**（README §1.4、`:742`）：

| 值形态 | σ 的处理 |
|---|---|
| `VSub(v2, sub2)` | 组合 `compose(sub, sub2)` 后一次推进 |
| `Rigid(x, sp)` | `lookup_hit(x)` 命中：**烧 1 fuel**，`force` 解值，再按应用序 `v_app` 逐个拼 spine（λ ⇒ β，Match ⇒ pending，中性头 ⇒ spine）；未命中零成本直通。头不可应用（且非 λ）时保持卡住 |
| `Flex/Decl/Prim(name, sp)` | spine 槽**只包裹不推进**（`wrap_sp`），再交回 `force` 走既有臂 |
| `Obj(o, name, sp)` | 接收者**推进**（`frcs`），spine 只包裹 |
| `Lam(x, i, cl)` | 闭包 **env 逐槽包裹**（`frcs_env`），**不进入闭包体**求值 |
| `Pi(x, i, a, cl)` | 域推进，闭包 env 逐槽包裹 |
| `Sum` / `SumCase` 的槽 | **只包裹不物化**（参数值/类型、typ、datas 全包 `VSub`） |
| `Match(s, env, cases, pending)` | **scrutinee 推进**（重选分支需要解出的构造子值）；捕获 env 与 pending 只包裹；交回 `force` |

`frcs_env`（`L07/mod.rs:796-801`）：σ 非空时把 env 每个槽包成 `VSub`。

**为什么 spine 槽只包裹不物化**（`:721-725`）：槽位引用是**作用域事实**，物化会破坏后续
`solve` 的 `invert`。`force_arg`（`L07/mod.rs:563-582`）是"参数视角的 WHNF"：与 force
相同但不做 Match 重选，且 bare rigid 的 VSub 解包后原样返回——供 `invert`/`prune_vflex`
使用。

**可见性边界**（诚实清单，`L07/README.md:92-95`）：σ 只对**被包裹过的值**生效；
meta 的解（rename 产物，Tm 层）与 decl 表条目不在 σ 的扫描/包裹范围内。

### 2.8 motive（期望类型）的处理与"重锚"

```rust
// L07/pattern_match.rs:178-197
                    // 分支体走**常规转换**检查：spec 不穿参…
                    // 上下文先置于精化之下（dpm-nbe `subst sub ctx`）：env 槽
                    // 与 src_names 类型包 VSub，lvl/locals/pruning 不动——
                    // 槽位布局（= 运行时布局）永不漂移，读点 force 展开。
                    let cxt_arm = cxt_arm.subst_cxt(&self.sub);
                    // 期望类型**重锚**到臂上下文：quote → eval 把其中所有
                    // rigid 引用重定向到臂 env（quote 时 VSub 全部推开——
                    // 精化等式一并烘焙进去）。语义上不重锚也正确（force 惰性
                    // 推开），但值层面只有重锚后，期望里的卡住 match 与
                    // meta 解物化出来的副本才有同样的 env 布局——unify 的
                    // 结构快路径（val_eq）才能命中，否则双方逐层展开不收敛。
                    let ret_type = match infer.force(cxt_arm.decl(), wrap_sub(&self.sub, expected.clone())) {
                        t @ Val::Flex(..) => t,
                        t => {
                            let tm = infer.quote(cxt_arm.decl(), cxt_arm.lvl, t);
                            infer.eval(cxt_arm.decl(), &cxt_arm.env, &tm)
                        }
                    };
                    let tm = infer.check(&cxt_arm, body.clone(), ret_type)?;
```

算法：

```
motive_arm(expected, σ, cxt_arm):
    t ← force(wrap_sub(σ, expected))
    if t 是未解 Flex: 原样返回 t          -- 不重锚（避免把 meta 打成结构）
    else: quote(cxt_arm.lvl, t) |> eval(cxt_arm.env)   -- rebase：rigid 重定向为臂 env 的索引
```

**为什么重锚**（`L07/README.md:97-106`）：语义上不重锚也正确（force 惰性展开）；
但值层面只有重锚后，期望里的卡住 match 与 meta 解物化出来的副本才有同样的 env 布局，
`unify` 的结构快路径 `struct_eq::val_eq` 才能命中；否则"同一个 `add t b`"的两份不同布局
表示会逐层展开、永不收敛（fuel 耗尽误报 can't unify）。

**注意**：`match` 的 motive 在编译期**没有被显式抽象成函数**（没有 generalize 步骤）；
每个臂各自用同一份 `expected` 值重锚。这与 Agda 的 motive 抽象不同，是教学取舍，
其后果写在诚实清单 §7.1（`L07/README.md:306-309`）。

### 2.9 可达性 / 覆盖性 / 不可达

#### 2.9.1 可达性探测 `probe_accessible`

```rust
// L07/pattern_match.rs:269-348（结构摘要 + 关键行）
    /// 构造子可达性探测：在（meta + σ + 本地可解集）快照回滚下跑一次特化
    /// 方程。探测不产生真槽——构造子绑定器用超出上下文的 scratch 层级
    /// 实例化（同为刚性、同可被方程解出，探测状态全在本地，弃掉即回滚）。
    /// 成功 = 该构造子可能出现在头部类型的值里；结构冲突
    /// （`Vec[A] zero` 上不可能有 `cons`）= absurd。
    fn probe_accessible(
        infer: &mut Infer, cxt: &Cxt, lvl: Lvl, head_sum: &Val, ctor: &Span<String>,
        init_sub: &Rc<Subst>, base_solvable: &[Lvl],
    ) -> bool {
        let (sum_name, impl_vals) = match head_sum { Val::Sum(name, params, _) => (
            name, params.iter().filter(|(_,_,_,i)| *i == Icit::Impl).map(|(_,v,_,_)| v.as_ref().clone()).collect()),
            _ => return false };
        let entry = match cxt.decl_get(&format!("{}.{}", sum_name.data, ctor.data)) { Some(e)=>e, None=>return false };
        infer.meta_refuel();                       // 每个探测独立充值
        let snap = infer.meta_snapshot();
        let decl = cxt.decl().clone();
        let mut solvable = base_solvable.to_vec();
        let sub = init_sub.clone();
        let mut ty = entry.ty.clone();
        let mut impl_idx = 0; let mut scratch = 0u32;
        let ok = loop {
            match infer.force(&decl, wrap_sub(&sub, ty.clone())) {
                Val::Pi(_, _, _, closure) => {
                    let u = if impl_idx < impl_vals.len() { let v = impl_vals[impl_idx].clone(); impl_idx += 1; v }
                            else { let l = Lvl(lvl.0 + scratch); scratch += 1; solvable.push(l); Val::vvar(l) };
                    ty = infer.closure_apply(&decl, &closure, u);
                }
                ret => {
                    let ret_sum = match infer.force(&decl, wrap_sub(&sub, ret)) { s @ Val::Sum(..) => s, _ => break false };
                    break { let mut spec = SpecSolve { solvable: &solvable, acc: sub.clone() };
                        Self::unify_indices(infer, cxt, lvl, &mut spec, head_sum, &ret_sum, &ctor.data).is_ok()
                        || infer.fuel_exhausted() };
                }
            }
        };
        infer.meta_restore(snap);
        ok
    }
```

要点：
- 探测**不产生真槽**：构造子绑定器用 `Lvl(lvl + scratch)` 的 scratch rigid 实例化并
  临时加入可解集；探测结束 `meta_restore(snap)` 回滚 meta。
- **失败 = 结构冲突 ⇒ 该构造子不可达（absurd）**；但 fuel 耗尽的失败按**可达**处理
  （保守地要求覆盖，避免深负载下非穷尽 match 被静默接受，`:336-338`）。
- `lvl` 显式穿参：顶层探测传入口 `cxt.lvl`；嵌套位置的延迟探测传记账时的**臂内层级**
  （scratch 层级必须落在该臂全部真槽之外）。

#### 2.9.2 顶层覆盖谓词（文本层）

```rust
// L07/pattern_match.rs:749-763
/// 顶层覆盖判定：通配 / 变量模式覆盖一切；Con 只覆盖同名构造子。
fn covers(pat: &Pattern, ctor: &str, ctor_names: &[String]) -> bool {
    match pat {
        Pattern::Any(..) => true,
        Pattern::Con(name, _, _) => !ctor_names.iter().any(|c| c == &name.data) || name.data == ctor,
    }
}

/// 通配臂：覆盖所有取值的臂（其后的臂不可达 → 报「分支不可达」）。
fn is_catch_all(pat: &Pattern, ctor_names: &[String]) -> bool {
    match pat {
        Pattern::Any(..) => true,
        Pattern::Con(name, subs, _) => subs.is_empty() && !ctor_names.iter().any(|c| c == &name.data),
    }
}
```

- `covers(_, ctor, ctor_names)`：`Con(name, …)` 当 `name` **不是**该类型构造子时
  视为变量模式，覆盖一切；否则只覆盖同名构造子；
- `is_catch_all`：`Any`，或 `Con(name, [], _)` 且 `name` 不是构造子（变量模式）；
- 顶层覆盖检查用**源码模式**（不是编译后的 detail）：一个被判 `Unreachable` 的臂
  在文本上**仍可能"覆盖"**某个构造子——但该臂不贡献 `pats`，嵌套覆盖用的是 `pats`
  （`L07/pattern_match.rs:248`），所以两种检查的覆盖面略有差异（这是有意的：
  顶层缺失报"缺少构造子"，荒谬臂报"分支不可达"）。

#### 2.9.3 嵌套覆盖：路径与贡献

```rust
// L07/mod.rs:115-147
/// 已走查臂在某嵌套位置的覆盖贡献：全覆盖（var/Any，含路径中途变变量）、
/// 贡献某构造子（路径末端是 Con）、不可达该位置（祖先选了别的构造子）。
pub(crate) enum PosCover { All, Ctor(String), None }

/// 沿 (构造子名, 字段下标) 路径下钻一棵已走查的 PatternDetail 树。
/// 字段下标与 `walk_con` 的 details 布局同源（望远镜中产槽绑定器的序数）。
pub(crate) fn cover_at(detail: &PatternDetail, path: &[(String, usize)]) -> PosCover {
    let mut cur = detail;
    for (ctor, field) in path {
        match cur {
            PatternDetail::Any(_) | PatternDetail::Bind(_) => return PosCover::All,
            PatternDetail::Con(n, subs) if n.data == *ctor => cur = &subs[*field],
            PatternDetail::Con(..) => return PosCover::None,
        }
    }
    match cur {
        PatternDetail::Any(_) | PatternDetail::Bind(_) => PosCover::All,
        PatternDetail::Con(n, _) => PosCover::Ctor(n.data.clone()),
    }
}

/// 人读路径：`cons#2 → nil#1` 表示 cons 第二字段的 nil 第一字段处。
pub(crate) fn fmt_path(path: &[(String, usize)]) -> String {
    path.iter().map(|(c, f)| format!("{c}#{}", f + 1)).collect::<Vec<_>>().join(" → ")
}
```

**嵌套记账的提升时机**（`L07/pattern_match.rs:66-82`、`:166-177`）：

```rust
struct NestedCheck {
    path: Vec<(String, usize)>,   // 根到被拆字段的 (构造子名, 字段下标) 链
    field_sum: Val,               // 该字段在记录臂实例化下的 Sum 值
    sub: Rc<Subst>,               // 记录时刻的 σ 快照
    solvable: Vec<Lvl>,
    lvl: Lvl,
}
```

两段式（`:58-66`）：走查中只记 `(路径, 字段 Sum)`；臂走查**成功后**（特化方程已解出、
σ 为终态）才提升为带 σ/solvable/lvl 快照的完整记账——字段走查时外层方程尚未解出，
索引精化不在 σ 里，此时探测会把"已精化下不可达的构造子"误判可达。整臂 `Unreachable`
时 `pending_pos.clear()` 丢弃（`:203-206`）。

可达集取**各记账臂探测的并集**（保守：任一臂实例化下可达的构造子都要求被覆盖）。
被遮蔽臂与荒谬臂不在 `pats` 里，天然不贡献覆盖。

#### 2.9.4 不可达的两种来源与文案

| 来源 | 判定 | 文案 | 锚点 |
|---|---|---|---|
| 荒谬臂 | `walk_con` 里特化方程失败（`unify_indices` Err） | `分支不可达：模式 {pat:?} 与被匹配类型不相容` | `L07/pattern_match.rs:203-209`、`:647-648` |
| 被遮蔽臂 | 前面出现过通配臂（`is_catch_all`），首匹配语义下永不可达 | `分支不可达：模式 {pat:?} 被前面的通配臂遮蔽` | `L07/pattern_match.rs:152-161` |
| 缺失构造子（顶层） | 可达但无臂覆盖 | `match 不完整：缺少构造子 {ctor}` | `L07/pattern_match.rs:140-149` |
| 缺失构造子（嵌套） | 路径位置可达但无臂贡献覆盖 | `match 不完整：模式位置 {path} 缺少构造子 {ctor}` | `L07/pattern_match.rs:253-259` |

所有错误**一次报全**（`errors: Vec<String>`，`Err(Error(errors.join("\n")))`，
`L07/pattern_match.rs:262-266`）。

#### 2.9.5 与旧 L13 实现的对照

`docs/pattern-match-refinement-analysis.md` 描述了**L13 旧实现**（"改写 env 槽 +
`update_cxt` 刷新"）的 GADT 精化缺陷（正文 `docs/pattern-match-refinement-analysis.md:31-67`）：
绑定变量的类型"冻结"在 `Vec[A] l'`，而返回类型细化为 `Vec[A] (succ l')`，两者无法统一。
L07 的显式替换架构（本文 §2.7）**按构造排除**了这一 bug 族（`L07/README.md:283-302`）。
`docs/opt-pattern-match.md` 是 L13 的优化笔记（`filter_accessible_constrs` 快速路径、
预计算构造子签名、用结构相等替换完整统一化），对应到 L07 就是
`probe_accessible` + `unify_indices` + `struct_eq` 快路径；其中"非索引和类型跳过
GADT 可达性分析"这一快速路径在 L07 的探测里**没有**——L07 对每个构造子统一走
索引合一探测（但非索引类型下方程退化平凡，成本可忽略）。

---

## 3. ι-归约 / 运行时 match 语义

### 3.1 求值：首匹配

`Tm::Match` 的求值（`L07/mod.rs:1181-1202`）：

```rust
            Tm::Match(tm, cases) => {
                let val = self.force(decl, self.eval(decl, env, tm));
                match val {
                    Val::SumCase { .. } => {
                        match Compiler::eval_aux(self, decl, &val, env, cases) {
                            Some((body, env)) => self.eval(decl, &env, body),
                            None => Val::Match(Box::new(val), env.clone(), cases.clone(), Vec::new()),
                        }
                    }
                    neutral => Val::Match(Box::new(neutral), env.clone(), cases.clone(), Vec::new()),
                }
            }
```

**规则**：

```
eval(match s { arms }, ρ) =
    let v = force(eval(s, ρ))
    if v = SumCase{…} and eval_aux(v, ρ, arms) = Some(body, ρ')  then  eval(body, ρ')
    else  Val::Match(v, ρ, arms, pending = [])        -- 卡住
```

注意第二条也覆盖"v 是构造子**值**但没有臂匹配"（`eval_aux` 返回 `None`）——此时
`Val::Match` 的 scrutinee 是构造子值。

### 3.2 选中臂：`eval_aux` / `eval_aux_arm`

```rust
// L07/pattern_match.rs:671-746
    /// 运行时分支选择：按模式首匹配。返回 (分支体, 扩展后的 env)。
    /// 任何 head 都不会 panic——不命中就返回 None，由调用方停成 `Val::Match`。
    pub fn eval_aux<'a>(infer: &Infer, decl: &Decls, head: &Val, env: &Env,
                        cases: &'a [(PatternDetail, Tm)]) -> Option<(&'a Tm, Env)> {
        let head = infer.force(decl, head.clone());
        for (pat, body) in cases {
            if let Some(env) = Self::eval_aux_arm(infer, decl, &head, env, pat) {
                return Some((body, env));
            }
        }
        None
    }

    fn eval_aux_arm(infer: &Infer, decl: &Decls, head: &Val, env: &Env, pat: &PatternDetail) -> Option<Env> {
        match pat {
            PatternDetail::Any(_) | PatternDetail::Bind(_) => Some(env.prepend(head.clone())),
            PatternDetail::Con(name, subs) => {
                let Val::SumCase { typ, case_name, datas } = head else { return None; };
                let Val::Sum(_, _, ctor_names) = typ.as_ref() else { return None; };
                let in_type = ctor_names.iter().any(|c| c.data == name.data);
                if in_type && case_name.data == name.data {
                    if subs.len() != datas.len() { return None; }
                    // 先 prepend 被匹配值本身（head 槽），再逐字段 prepend 子模式槽值
                    let mut cur = env.prepend(head.clone());
                    for ((_, v, _), sub) in datas.iter().zip(subs.iter()) {
                        let v = infer.force(decl, (**v).clone());
                        cur = Self::eval_aux_arm(infer, decl, &v, &cur, sub)?;
                    }
                    Some(cur)
                } else if !in_type {
                    // 不是该类型的构造子名 → 变量模式（保守兼容）
                    Some(env.prepend(head.clone()))
                } else {
                    // 同类型不同构造子 → 本臂不命中
                    None
                }
            }
        }
    }
```

**形式化规则**（`⇓` 为按声明序的槽 prepend；`::` 表示 prepend 到 env 头部）：

```
match_arm(v, ρ, Any)            = Some(ρ :: v)
match_arm(v, ρ, Bind(_))        = Some(ρ :: v)
match_arm(v, ρ, Con(c, ps))     =
   if v = SumCase{typ = Sum(D, _, cases), case_name = c, datas = ds}
      and c ∈ cases and |ps| = |ds|
   then fold over (dsᵢ, psᵢ): ρ ← match_arm(force dsᵢ, ρ, psᵢ)   (任一失败 ⇒ None)
        starting from ρ :: v
   else if c ∉ cases            -- 变量模式（保守兼容）
   then Some(ρ :: v)
   else None

eval_aux(v, ρ, arms) = 第一个 match_arm(v, ρ, pat) = Some(ρ') 的臂的 (body, ρ')；全失败 ⇒ None
```

**槽序契约**（必须与编译期 `walk_con` 一致）：

1. `Con` 的 head 槽在最前（`ρ :: v`）；
2. 然后按 `datas`（= 构造子**自己的**绑定器，声明序）与子模式 `zip`，逐字段 prepend；
3. `bind_count` = `1 + Σ 子模式 bind_count`，正好等于 prepend 的数量。

注意：`datas` 里**不含** enum 隐式参数，编译期的 `details` 也不含——两者一致。

### 3.3 卡住的 match 是一等中性值

```rust
// L07/mod.rs:211-215
    /// 卡住的 match：scrutinee 不是构造子值，等待 scrutinee 归约后再选分支。
    /// `pending` = 卡住期间累积的应用实参（值层保存，分支选中后在值层应用
    /// ——项层 splice 把实参 quote 进分支体时，实参的自由变量会引用到
    /// 错误的上下文，见 `v_app` 的 Match 臂）。
    Match(Box<Val>, Env, Vec<(PatternDetail, Tm)>, Vec<(Val, Icit)>),
```

#### 3.3.1 应用：`pending` 累积

```rust
// L07/mod.rs:1060-1063
            Val::Match(val, env, cases, mut pending) => {
                pending.push((u, i));
                Val::Match(val, env, cases, pending)
            }
```

即 `v_app(Val::Match, u)` 不 panic，把实参**收进 pending**（值层保存）。
旧实现的"项层 splice 进每个分支体"被替换为值层 pending（`:1042-1045` 的理由：
实参的自由变量层级可能超出捕获 env）。

#### 3.3.2 重选分支：`force` 的 Match 臂

```rust
// L07/mod.rs:606-628
            // 卡住的 match：scrutinee 是在 match 创建之后才被特化/解出时，
            // 这里重新尝试选分支。没有这一步，精化无法传播进"卡住 match
            // 里面"（期望类型 `Eq (add a zero) a` 的 `add a zero` 就是它）。
            Val::Match(s, env, cases, pending) => {
                let s2 = self.force(decl, (*s).clone());
                if let Val::SumCase { .. } = &s2 {
                    if burn(&self.unify_fuel) {
                        if let Some((tm, env2)) = Compiler::eval_aux(self, decl, &s2, &env, &cases) {
                            // 分支选中：先在值层应用卡住期累积的实参…
                            let mut v = self.eval(decl, &env2, tm);
                            for (u, i) in pending.iter().cloned() {
                                v = self.v_app(decl, v, u, i);
                            }
                            return self.force(decl, v);
                        }
                    }
                }
                Val::Match(s, env, cases, pending)
            }
```

**规则**：

```
force(Match(s, ρ, arms, pending)) =
    let s' = force s
    if s' = SumCase{…} and eval_aux(s', ρ, arms) = Some(body, ρ')
    then force( v_app*(eval(body, ρ'), pending) )        -- pending 按应用序逐个值层应用
    else Match(s', ρ, arms, pending)
```

`pending` **不是** ι-归约的一部分：它只在分支选中后作为值层应用补上；未选中时随
中性值保留。

#### 3.3.3 卡住 match 的合一与 quote

**合一（Match vs Match）**（`L07/unification.rs:1032-1085`）：先走**结构快路径**
（`struct_eq::val_eq(scrutinee) && env_eq(env) && 模式逐元素相等 && tm_eq(体) && pending 相等`
⇒ 直接 `Ok(())`），再退化为 `unify(scrutinee)` → 分支数/模式逐一相等 → 每个分支在
`l + i` 的 fresh rigid 槽下**重求值**后合一（用 `simpl_decl` 简化表）→ 最后逐 pending 合一。
结构快路径是必需的：否则"同一 decl 值在合一两侧各展开一份"会逐层展开、fresh 层级递增、
永不收敛（`:1035-1040`）。

**合一（Match vs 其它）**（`L07/unification.rs:1086-1112`）：只接受**严格 eta**——
`pending` 为空、scrutinee force 成 bare rigid、且**每个分支都是通配（`Any`/`Bind`）
且分支体就是 `Tm::Var(Ix(0))`**：

```rust
                if !pending.is_empty() { return Err(UnifyError); }
                match (self.force(decl, (**s).clone()), other) {
                    (Val::Rigid(x, sp), Val::Rigid(y, sp2))
                        if x == *y && sp.is_empty() && sp2.is_empty() =>
                    {
                        let is_eta = !cases.is_empty() && cases.iter().all(|(pat, body)| {
                            matches!(pat, PatternDetail::Any(..) | PatternDetail::Bind(_))
                                && matches!(body, Tm::Var(Ix(0)))
                        });
                        if is_eta { Ok(()) } else { Err(UnifyError) }
                    }
                    _ => Err(UnifyError),
                }
```

无条件接受会把 `f x` 证成 `x`（注释 `:1087-1088`）。

**quote（Match）**（`L07/mod.rs:1275-1302`）：分支体在"捕获 env + `bind_count` 个
fresh rigid 槽"下**用简化 decl 表重新求值**再 quote，pending 作为 `Tm::App` 包在
`Tm::Match` 外：

```rust
                let declb = self.simpl_decl_cached(decl);
                let tm_cases = cases.into_iter().map(|(p, b)| {
                    let count = p.bind_count();
                    let env = (0..count).fold(env.clone(), |env, i| env.prepend(Val::vvar(l + i)));
                    let tm = self.eval(&declb, &env, &b);
                    (p, self.quote(&declb, l + count, tm))
                }).collect();
                let m = Tm::Match(Box::new(self.quote(decl, l, *val)), tm_cases);
                pending.into_iter().fold(m, |acc, (u, i)| {
                    Tm::App(Box::new(acc), Box::new(self.quote(decl, l, u)), i)
                })
```

`simpl_decl`（`L07/mod.rs:1470-1487`）：所有非 `Sum` 的全局值换成中性
`Val::Decl(自身名, [])`，防止递归定义在求值分支体时被重展开；`Sum` 保持原样
（构造子值的 `typ` 槽需要真实 Sum）。

### 3.4 结构覆盖谓词（汇总）

形式化时把"覆盖"分成两个层次：

**(a) 语法覆盖（syntactic coverage）**——只看模式树：

```
covers(Any, _)                 = true
covers(Con(c, ps), ctor)       = (c ∉ ctors(head)) ∨ (c = ctor)
is_catch_all(Any)              = true
is_catch_all(Con(c, [], _))    = c ∉ ctors(head)
is_catch_all(Con(_, _::_, _))  = false
cover_at(d, [])                = All(d)
cover_at(Any|Bind, _)          = All
cover_at(Con(n, subs), (c,f)::rest) = if n = c then cover_at(subs[f], rest) else None
cover_at(Con(n, _), [])        = Ctor(n)
```

**(b) 语义可达性（accessibility）**——`probe_accessible`：一个构造子在其返回类型的
索引与头部索引**特化合一成功**时可达，否则 absurd。合一失败 = 结构冲突；
fuel 耗尽按可达处理（保守）。

**(c) 结构的项/值相等快路径**（`L07/struct_eq.rs:1-53`）：

```rust
pub fn tm_eq(a: &Tm, b: &Tm) -> bool;
pub fn env_eq(a: &Env, b: &Env) -> bool;
pub fn val_eq(a: &Val, b: &Val) -> bool;   // 同址直接 true
```

不 force、不展开、不求值、忽略 span；预算 `EQ_BUDGET = 20_000` 封顶，超限按"不相等"
（`L07/struct_eq.rs:24-53`）。只用于把"本可判等但求值发散"的情形**提前**判等。

---

## 4. `struct` / 积类型（L08）

> 结论先行：**L08 的核心机不新增任何 Tm/Val 变体**；`struct` 是纯语法糖，
> 在解析器内就脱糖成单构造子 `enum`（`L08/README.md:4-9`）。

### 4.1 `struct` 声明与脱糖

```rust
// L08/parser/mod.rs:539-570（逐字）
/// `struct Name[A: U, ...] { field: Type ... }` —— 积类型语法糖：脱糖成
/// **单构造子 enum**，构造子名为 `{Name}.mk`，字段全部显式（Expl），参数
/// 走隐式方括号组（`[A]` / `[A: U]`）。字段可依赖参数与在前字段
/// （依赖积 / Sigma）…
fn p_struct<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
    (
        kw(StructKeyword),
        string(Ident),
        p_pi_impl_binder.option().map(|x| x.unwrap_or_default()),
        brace(
            (string(Ident), kw(T![:]), p_raw)
                .map(|(name, _, ty)| (name, ty))
                .many0_sep(kw(EndLine).many1()),
        ),
    )
        .map(|(_, name, params, fields)| Decl::Enum {
            name: name.clone(),
            params,
            cases: vec![(
                name.map(|x| format!("{x}.mk")),
                fields.into_iter().map(|(n, ty)| (n, ty, Icit::Expl)).collect(),
                None,
            )],
        })
        .parse(input, state)
}
```

**脱糖规则（精确）**：

```
struct Name[p₁ … p_k] { f₁ : T₁  …  fₙ : Tₙ }
  ≡  enum Name[p₁ … p_k] { Name.mk(f₁ : T₁, …, fₙ : Tₙ) }
```

- 构造子**名**就是字符串 `{Name}.mk`（例如 `Point.mk`、`Unit.mk`）；
- 字段 icit **全部 `Expl`**；`-> ret` 缺省（`None`）⇒ 走 §1.4 的 `default_ret`
  = `Name` 应用到隐式参数，即 `Point.mk : Π[T] → T → T → Point T`
  （字段按声明序，隐式参数在最前；`L08/elaboration.rs:280-306`）；
- **AST 层没有 `Decl::Struct` / `Raw::New` / `Raw::Struct`**：全仓库 grep 无命中，
  `Decl` 只有 `Def | Println | Enum`（`L08/parser/syntax.rs:70-84`）。
  核心机对 struct 一无所知；
- 参数只认**一个前导 `[..]` 隐式组**（`p_pi_impl_binder.option()`，
  `L08/parser/mod.rs:330-346`）：`struct Name[A] {…}` / `struct Name[A : U] {…}` /
  无参 `struct Name {…}` 可以；`(x : T)` 显式组**不被接受**（`L08/README.md:238`）；
- 字段**按行分隔、无逗号**；字段间允许连续空行/注释行（`many0_sep(EndLine.many1())`）；
  **末尾逗号会解析失败**；字段体可为空 ⇒ **nullary 构造子**；
- 空 `struct Unit { }` → `Unit.mk`（`L08/README.md:43`）；
- **不支持 tuple struct**（`struct S(Nat, Nat)`），文法只有 `brace((Ident ":" raw)…)`
  （`L08/README.md:235-236`）。

**注册名的双轨结果**（`L08/README.md:44-47`、`L08/elaboration.rs:378-383`）：
脱糖后走 §1.5 的 enum 注册。以 `struct Point[T] {x: T  y: T}` 为例：

| decl 表键 | 内容 |
|---|---|
| `Point` | enum 类型本体（`Val::Sum` 的生产者），`L08/elaboration.rs:338-344` |
| `Point.Point.mk` | 构造子（限定键 = `format!("{enum}.{case}")`，而 case 已含 `.mk`） |
| `Point.mk` | **裸名别名**——正是 `new`（`Raw::Var` 路径）与 `Point.mk`（`Raw::Obj` 限定路径）两条引用路径的查找键 |

不产生裸 `mk` 的全局别名冲突。

**`new` 的消解路径**（`L08/elaboration.rs:471-478`）：`Point.mk` 写作
`Raw::Obj(Var "Point", "mk")`，限定构造子快捷路径按
`format!("{}.{}", n.data, f.data)` = `Point.mk` 查表，得 `Tm::Decl("Point.mk")`；
**局部遮蔽优先**——`src_names` 里有同名 binder 时**不**走快捷路径，而是走正常投影。

### 4.2 `new`

```rust
// L08/parser/mod.rs:444-465（逐字）
/// `new Name(a, b, ...)` —— 积类型的构造语法糖：脱糖成限定构造子
/// `Name.mk` 的显式应用（`struct` 注册的构造子名就是 `{Name}.mk`）。
/// 结果可直接接 `.field` 投影后缀链（与原子同等待遇，`new P(a, b).x`
/// 等价 `(new P(a, b)).x`）；裸 spine 实参位仍不接 `new`（p_arg 不动）。
fn p_new<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    (
        kw(NewKeyword), string(Ident),
        paren(p_raw.many0_sep(kw(T![,]))),
        (kw(T![.]), string(Ident)).many0(),
    )
        .map(|(_, name, args, suffixes)| {
            let head = args.into_iter().fold(
                Raw::Var(name.map(|x| format!("{x}.mk"))),
                |acc, x| Raw::App(Box::new(acc), Box::new(x), Either::Icit(Icit::Expl)),
            );
            suffixes.into_iter().fold(head, |acc, (_, f)| Raw::Obj(Box::new(acc), f))
        })
        .parse(input, state)
}
```

**规则**：

```
new Name(e₁, …, eₖ)        ≡  Name.mk e₁ … eₖ        （全部 Expl 应用）
new Name(e₁, …).f.g        ≡  ((new Name(e₁, …)).f).g
```

- **没有独立的 `new` 类型规则**：脱糖后就是普通的限定构造子引用 + 应用，
  走 `Raw::App` 的推断/检查路径（`L07/elaboration.rs:572-631`）；
- 隐式参数由 `insert_t` 插 meta（`L07/elaboration.rs:15-32`）——`new Point(zero, four)`
  靠这条自动供给 `[T]`（unify 与期望类型解出）；或在需要时显式写
  `Name.mk [A] e₁ …`（`L08/README.md:31`）；
- 每个字段实参用 `self.check(cxt, u, a)` **按声明序**检查（`L07/elaboration.rs:626`）；
- **缺实参不是错误**：得到部分应用函数（构造子值本身是 λ 链）；投影它报
  `cannot project field {f}`（接收者类型是 Π，`L08/elaboration.rs:603`；
  `L08/README.md:241-242`）；
- **多给实参**：没有专门文案，走通用 `unify_catch` 失配路径
  （`L07/elaboration.rs:597-624` → `L07/mod.rs:1317-1330`）；
- 未知 struct 名：`new Nope(zero)` → `name not in scope: Nope.mk`
  （`L07/elaboration.rs:455`）；
- `new` 在 `p_raw` 链上（`L08/parser/mod.rs:467-474` 的 `.or(p_new)`），
  所以 `new Line(new Point(...))` 合法；
- **裸 spine 实参位不接 `new`**：`p_arg` 只用 `p_atom`（不含 `p_new`），
  所以 `f new Point(...)` 解析失败，要写 `f (new Point(...))`
  （`L08/README.md:239-240`）；`new P(a,b).x` 则合法（`p_new` 自带后缀链）。

### 4.3 字段投影

#### 4.3.1 多段投影链（语法）

```rust
// L08/parser/mod.rs:254-262
/// 原子 + 投影后缀链。L07 只允许单个 `.field`，嵌套 struct 的 `l.a.x`
/// 会以 leftover `.` 解析失败；L08 扩为**左结合多段投影链**（纯语法扩展，
/// 单段与无段行为逐字不变）。
fn p_atom<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    (p_atom1, (kw(T![.]), string(Ident)).many0())
        .map(|(x, t)| t.into_iter().fold(x, |acc, (_, f)| Raw::Obj(Box::new(acc), f)))
}
```

`a.b.c` ≡ `Raw::Obj(Raw::Obj(a, b), c)`，每段各按 §4.3.2 推进。

#### 4.3.2 投影的**类型**规则（`Raw::Obj` 的三条路径）

L08 版（`L08/elaboration.rs:466-…`）在 L07 版基础上多一条"类型级 `.mk` 剥链"：

```rust
            Raw::Obj(x, f) => {
                // ① 限定构造子引用 `Enum.case`——局部遮蔽优先
                if let Raw::Var(n) = &*x {
                    if !cxt.src_names.contains_key(&n.data) {
                        let key = format!("{}.{}", n.data, f.data);
                        if let Some(e) = cxt.decl_get(&key) {
                            return Ok((Tm::Decl(SmolStr::new(key)), e.ty.clone()));
                        }
                    }
                }
                let (tm, ty) = self.infer_expr(cxt, *x)?;
                match self.force(decl, ty) {
                    // ② 接收者**只有类型**（Val::Sum）
                    Val::Sum(sname, params, cases) => {
                        if let Some((_, _, fty, _)) = params.iter().find(|(n, ..)| n == &f) {
                            return Ok((Tm::Obj(Box::new(tm), f.clone()), fty.as_ref().clone()));
                        }
                        if cases.len() == 1 && cases[0].data.contains(".mk") {
                            if let Some(e) = cxt.decl_get(&cases[0].data) {
                                let impl_vals: Vec<Val> = params.iter()
                                    .filter(|(_,_,_,i)| *i == Icit::Impl)
                                    .map(|(_, v, _, _)| v.as_ref().clone()).collect();
                                let mut ty = e.ty.clone();
                                let mut impl_idx = 0;
                                while let Val::Pi(bname, _, bdom, closure) = self.force(decl, ty) {
                                    if bname.data == f.data {
                                        return Ok((Tm::Obj(Box::new(tm), f.clone()), *bdom));
                                    }
                                    let u = if impl_idx < impl_vals.len() {
                                        let v = impl_vals[impl_idx].clone(); impl_idx += 1; v
                                    } else {
                                        // 显式字段 binder：用**接收者的卡住投影值**实例化
                                        self.eval(decl, &cxt.env,
                                                  Tm::Obj(Box::new(tm.clone()), bname.clone()))
                                    };
                                    ty = self.closure_apply(decl, &closure, u);
                                }
                            }
                        }
                        Err(Error(format!("{} has no field {}", sname.data, f.data)))
                    }
                    // ③ 接收者是构造子**值**（Val::SumCase）——L07 已有
                    Val::SumCase { typ, case_name, datas } => { … 参数（索引）槽优先，
                        // 否则剥构造子类型链：隐式参数用头部 Sum 的实参实例化，
                        // 显式字段 binder 用实例 datas 的**真实值**实例化 … }
                    _ => Err(Error(format!("cannot project field {}", f.data))),
                }
            }
```

**规则表**（`L08/README.md:60-86`）：

| 接收者类型 | 查找顺序 | 出处 |
|---|---|---|
| `Val::SumCase`（构造子**值**） | ① 参数（索引）槽 → ② 剥构造子类型链：隐式参数用头部 Sum 实参实例化，显式字段 binder 用实例 `datas` 的**真实值** | L07 已有 |
| `Val::Sum`（只有**类型**，如 `def f(p: Point) = p.x`） | ① 参数槽 → ② 若**单 case 且 case 名含 `.mk`**：剥 `mk` 的类型链（隐式参数同上；显式字段 binder 以**接收者的卡住投影值** `eval(Obj(接收者项, 字段名))` 实例化） | **L08 新增** |

- **门控**：`cases.len() == 1 && case.data.contains(".mk")`；**普通单 case enum 不享受
  类型级剥链**——`enum Wrap { only(x: Nat) }` 上 `w.x` 报 `Wrap has no field x`
  （`L08/README.md:70-72`）。
- **精确剥链**是依赖积的关键：剥到目标字段之前经过的每个**显式字段** binder，用
  卡住投影中性值 `Obj(tm, bname)` 实例化，于是后字段拿到精确类型，例如
  `Exists.proof : P e.witness`。旧实现以 `U` 占位会假拒
  （`L08/README.md:73-79`，回归测试 `test_product_dependent_check`）。
- 失败文案两版一致：`{类型名} has no field {字段}`；接收者既不是 Sum/SumCase 时
  是 `cannot project field {字段}`（`L07/elaboration.rs:551`、`L08/elaboration.rs:603`）。
- **两条臂的查表键不同**（重要细节）：`Val::Sum` 臂用**裸名别名**
  `cxt.decl_get(&cases[0].data)`（`cases[0].data == "Point.mk"`，
  `L08/elaboration.rs:500`）；`Val::SumCase` 臂用**限定键**
  `format!("{}.{}", sname.data, case_name.data)`（= `"Point.Point.mk"`，
  `L08/elaboration.rs:555-557`）。
- **struct 不能被 `Con` 模式解构**：case 名含 `.`，而 `p_pattern` 的头部是单个
  `Ident` token，`case Point.mk(a, b)` / `case Point(a, b)` 都解析不了
  （`L08/README.md:231-234`）。所以匹配 struct 只能用变量臂（绑定整个值）再投影。

#### 4.3.3 投影的**值**规则与卡住投影

```rust
// L07/mod.rs:1436-1462（L08 复用，零改动）
/// `v.field` 的值级投影：Sum 取索引参数的值；SumCase 先查 typ 的参数（索引）再查构造子字段。
/// 其余（Rigid / Flex / Decl / 卡住的 Obj / 函数……）返回 None → 卡住成 `Val::Obj`。
fn project(v: &Val, name: &Span<String>) -> Option<Val> {
    match v {
        Val::Sum(_, params, _) => params.iter().find(|(n, ..)| n == name)
            .map(|(_, v, _, _)| (**v).clone()),
        Val::SumCase { typ, datas, .. } => {
            let params = match typ.as_ref() { Val::Sum(_, params, _) => params, _ => return None };
            params.iter().find(|(n, ..)| n == name).map(|(_, v, _, _)| (**v).clone())
                .or_else(|| datas.iter().find(|(n, _, _)| n == name).map(|(_, v, _)| (**v).clone()))
        }
        _ => None,
    }
}
```

求值（`L07/mod.rs:1112-1118`）：

```rust
            Tm::Obj(tm, name) => {
                let v = self.eval(decl, env, tm);
                match project(&v, name) {
                    Some(p) => p,
                    None => Val::Obj(Box::new(v), name.clone(), List::new()),   // 卡住
                }
            }
```

force 的卡住投影臂（`L07/mod.rs:660-668`）：

```rust
            Val::Obj(v, name, sp) => {
                let v = self.force(decl, *v);
                match project(&v, &name) {
                    Some(p) if burn(&self.unify_fuel) => self.force(decl, self.v_app_sp(decl, p, sp)),
                    _ => Val::Obj(Box::new(v), name, sp),
                }
            }
```

**规则**：

```
eval(x.f, ρ):
    v ← eval(x, ρ)
    match project(v, f) { Some(p) → p ; None → Obj(v, f, []) }      -- 卡住

project(Sum(D, params, _), f)      = params[f].value        （若无 f 槽 → None）
project(SumCase{typ=Sum(D,params,_), datas}, f) =
        params[f].value  若 f 是索引参数名
   else datas[f].value   若 f 是构造子字段名
   else None
project(其它, f)                    = None

force(Obj(v, f, sp)):
    v' ← force v
    match project(v', f) { Some(p) → force(v_app_sp(p, sp)) ; None → Obj(v', f, sp) }
```

卡住投影是**中性值**，参与合一（§4.4）、quote（`L07/mod.rs:1230-1232`）、
以及"再投影"（force 会先 force 接收者）。

### 4.4 依赖字段与 `unify` 的 `Obj`-`Obj` 合同臂

依赖积标准形态（`L08/README.md:48-58`）：

```typort
struct Exists[A: U, P: A -> U] {
    witness: A
    proof: (P witness)
}
def exists_two: Exists[Nat][x => Eq x two] =
    Exists.mk[Nat][x => Eq x two] two rfl
```

字段类型可引用**参数**与**在前字段**（`P witness`）。精确剥链让
`def use_proof (e : Exists[Nat][x => Eq x two]) : Eq e.witness two = e.proof`
可判过，代价是暴露了 L07 潜伏缺口：两个卡住投影首次同场合一。L08 补的臂
（`L08/unification.rs:779-787`，逐字）：

```rust
            // 卡住的投影：字段名相同即比接收者与卡住期实参 spine（合同规则）。
            // L07 潜伏缺口：两侧同为 `Val::Obj` 的合一从未发生（投影类型走
            // 剥链直接出结果）；L08 剥链以接收者卡住投影精确实例化后，
            // `e.witness ≡ e.witness` 成为可达形态，落到兜底臂即误报
            // can't unify。`Obj` vs 其它仍按失配处理（兜底臂）。
            (Val::Obj(o1, f1, sp1), Val::Obj(o2, f2, sp2)) if f1.data == f2.data => {
                self.unify(decl, l, cxt, (**o1).clone(), (**o2).clone(), spec.as_deref_mut())?;
                self.unify_sp(decl, l, cxt, sp1, sp2, spec.as_deref_mut())
            }
```

### 4.5 L08 相对 L07 的差异清单

| 项 | L07 | L08 | 锚点 |
|---|---|---|---|
| `struct` / `new` | 无 | 解析器脱糖（§4.1、§4.2） | `L08/parser/mod.rs:539-570`、`:444-465` |
| 投影链 | 单段 `.field` | 左结合多段 `.f.g` | `L08/parser/mod.rs:254-262` |
| 类型级 `.mk` 剥链 | 无 | 有（`cases.len()==1 && contains(".mk")`） | `L08/elaboration.rs:499-534` |
| `unify` `(Obj,Obj)` 臂 | 无（潜伏缺口） | 有 | `L08/unification.rs:779-787` |
| `unify` Π 臂 quote 层级 | 已回合修 | 修（`l` 而非 `cxt.lvl`） | `L08/README.md:103-113` |
| pretty 去重 `Point::Point.mk` | — | `Point.mk(...)` | `L08/README.md:96-101`、`L08/pretty.rs:189-193` |
| `check_ctor_wf` | 有 | **逐句相同**（只有签名 `Val` vs `&Val`、`ty` 的 move/clone、注释三处机械差异） | `L07/elaboration.rs:383-443` vs `L08/elaboration.rs:390-450` |
| 核心机 Tm/Val 变体 | — | **零新增** | `L08/README.md:4-9` |

**L08 测试锚点**（形式化时的行为参照）：
`src/L08_product_type/tests.rs:1464-1520`（`test_product_dependent`：`Bits` 字面量类型字段 +
`Exists` 依赖字段，构造 `Exists.mk[Nat][x => Eq x two] two rfl`，断言
`exists_two.witness` 打印为 `two`）；`src/L08_product_type/tests.rs:1580-1608`
（`test_product_dependent_check`：`def use_proof (e : Exists[Nat][x => Eq x two]) : Eq e.witness two = e.proof`
——精确剥链的回归钉）；`tests/l08_fast_parity.rs:1277-1345`（孪生 parity 同款）。

**L08 性能孪生**（`L08/bump_spine_iter/`）**共用参考版 parser**
（`bump_spine_iter.rs:110`），所以 struct/new 的脱糖就是同一份代码；
孪生侧 `(Obj,Obj)` 臂在 `bump_spine_iter/unify.rs:636-676`，`project` 在
`bump_spine_iter/force.rs:109-133`。struct 相关在孪生侧**没有**任何编译步骤
（`bump_spine_iter/compiler.rs` 是**模式匹配**编译器，不是 struct 编译器）。

---

## 5. `Eq` 类型与证明项

### 5.1 `Eq` 是真归纳族（**不是** Leibniz 编码）

```typort
// src/prelude/core/eq.typort:7-11
/// The identity type: a proof that `x` and `y` are definitionally equal.
enum Eq[A](x: A, y: A) {
    /// Reflexivity: proves `Eq a a` for any `a`.
    refl(a: A) -> Eq a a
}
```

`Eq` 是**索引族**：隐式参数 `A`（参数），显式参数 `x : A`、`y : A`（索引）。
`refl` 的返回类型 `Eq a a` 把两个索引都特化成构造子**自己重新绑定**的 `a : A`
——这正是 §1.6 允许的重绑定惯用法（Implicit 槽 `A` 是本 telescope 的 bare rigid）。

**编码判定（任务问题）**：`Eq` 是**真正的归纳族，不是 Leibniz 编码**。
证据：全仓库 `*.typort` 里 `enum Eq` 只有一处命中（`src/prelude/core/eq.typort:8`），
`src/prelude/` 下不存在 `(P : A -> Type) -> P x -> P y` 形式的 `Eq` 定义。
**唯一的** Leibniz 形态出现在 **Rust 测试文件里的测试夹具文本**中——那些程序
不加载 prelude，自己定义局部 `Eq`，例如
`src/L13_namespace/legacy_tests.rs:140-142`：

```rust
def Eq[A](x: A, y: A) = (P : A -> Type 0) -> P x -> P y

def refl[A, x: A]: Eq[A] x x = _ => px => px
```

（同型夹具另见 `legacy_tests.rs:469`、`:545`、`:5520`；`src/L13_namespace/parser/mod.rs:3850`；
`parser/lex.rs:379`；`bump_spine_iter/bench_src.rs:155`。）形式化时**不要**把它当成
`Eq` 的实现。

注意：`Eq` 缺省参数写法既可用 `Eq[A] x y` 也可用 `Eq x y`（隐式 `A` 由使用点插入）；
`refl` 可以 `refl a` 也可以 `refl[A] a` 或裸 `refl`（在期望类型决定 A、a 时）。
在 L07 的自包含测试里常写成（`L07/tests.rs:147-149`）：

```typort
enum Eq[A](x: A, y: A) {
    refl[a: A] -> Eq[A] a a
}
```

（等价；`refl` 的绑定器写成显式 `[a : A]` 隐式绑定器，返回类型里用限定形式。）

### 5.2 基本组合子（`src/prelude/core/eq.typort`，逐字）

```typort
// :13-15
/// Reflexivity, with the type arguments inferred: `rfl : Eq a a`.
def rfl[A][a: A]: Eq a a =
    refl a

// :17-21
/// Congruence: equal arguments give equal results under any function.
def cong[A, B, x: A, y: A](f: A -> B, e: Eq x y): Eq (f x) (f y) =
    match e {
        case refl(a) => refl (f a)
    }

// :23-27
/// Symmetry: `Eq x y` implies `Eq y x`.
def symm[A, x: A, y: A](e: Eq[A] x y): Eq[A] y x =
    match e {
        case refl(a) => refl[A] a
    }

// :29-33
/// Transitivity: `Eq x y` and `Eq y z` imply `Eq x z`.
def trans[A, x: A, y: A, z: A](e1: Eq[A] x y, e2: Eq[A] y z): Eq[A] x z =
    match e1 {
        case refl(a) => e2
    }

// :48-52
/// Substitution: if `x` equals `y`, a proof of `P x` yields a proof of `P y`.
def subst[A, P: A -> Type 0, x: A, y: A](e: Eq[A] x y, p: P x): P y =
    match e {
        case refl(a) => p
    }
```

其它组合子（同文件）：

| 名字 | 行 | 类型（简述） | 体 |
|---|---|---|---|
| `eq_comm` | `:55` | `Eq x y → Eq y x` | `symm e` |
| `eq_congr` | `:58` | `(e : Eq x y) (f : A → B) → Eq (f x) (f y)` | `cong f e` |
| `cong2` | `:62-68` | `f : A → B → C, e1 : Eq x y, e2 : Eq u v → Eq (f x u) (f y v)` | 双层 `match` 到 `refl (f a b)` |
| `cong_ap` | `:72-78` | `e1 : Eq f g, e2 : Eq x y → Eq (f x) (g y)` | 双层 `match` |
| `trans3` | `:81-82` | `Eq x y → Eq y z → Eq z w → Eq x w` | `trans (trans e1 e2) e3` |
| `cong3` | `:87-88` | 三元 `cong` | `trans (trans (cong (z => f z u p) e1) (cong (z => f y z p) e2)) (cong (f y v) e3)` |
| `subst2` | `:97-102` | `e1 : Eq x y, e2 : Eq u v, p : P x u → P y v` | 双层 `match` |
| `Cast` trait / `impl Cast for T` | `:36-46` | `cast : Eq(Self, U) → U` | `match prove { case refl(a) => this }`（`this` 即被转型值，K 式消去） |

**关键语义注记**：

- `refl` 的消去（`match e { case refl(a) => … }`）**只对 `a` 引入一个绑定器**；
  头部精化把 `e` 精化成构造子值，同时把两个索引用**特化方程**统一成同一个值；
- `subst` 的 `P : A -> Type 0` 是**显式命名**的隐式参数——注释 `:92-96` 提醒：
  `P` 若不能从期望类型 invert 出来，需要显式实例化整个隐式 telescope
  （`subst2[Nat, Nat, eqfam, x, y, u, v] e1 e2 p`）；
- **没有** `J`、没有 `transport` 别名、没有 `subst` 的错误消去；`Eq` 只有 `refl` 一个构造子；
- **没有 K 公理层面的安全保护**：精化一个出现在其它假设里的变量在完整依赖理论里需要
  `--without-K` 级论证，本层是教学取舍（`L07/README.md:320-321`）。

### 5.3 `cong_succ` 与 Nat 引理（`src/prelude/core/nat.typort`）

题目点名的引理全部存在，且都在 `src/prelude/core/nat.typort`：

```typort
// :50-52
/// Congruence of `succ`: equal arguments give equal successors.
def cong_succ[x: Nat, y: Nat](e: Eq x y): Eq (succ x) (succ y) =
    cong succ e

// :54-58   （注意：靠 nat_add 的 primop 定义性归约，rfl 即可）
/// `a + 0 = a`, by computation (the primop returns `x` when the second
/// argument is `zero`).
def add_zero_right(a: Nat): Eq (a + 0) a =
    rfl

// :60-66
/// `0 + a = a`, by induction on `a`.
def add_zero_left(a: Nat): Eq (0 + a) a =
    match a {
        case zero => refl 0
        case succ(t) => cong_succ (add_zero_left t)
    }

// :68-70
/// `n + (succ m) = succ (n + m)`, definitionally.
def add_succ_right (n: Nat, m: Nat): Eq ((n + (succ m))) (succ (n + m)) =
    rfl

// :72-77
/// `(succ n) + m = succ (n + m)`, by induction on `m`.
def add_succ_left (n: Nat, m: Nat): Eq (((succ n) + m)) (succ (n + m)) =
    match m {
        case zero => refl[Nat] (succ n)
        case succ(k) => cong_succ (add_succ_left n k)
    }

// :79-84
/// Addition is commutative: `n + m = m + n`.
def add_comm (n: Nat, m: Nat): Eq(n + m, m + n) =
    match m {
        case zero => symm(add_zero_left n)
        case succ(k) => trans (cong_succ (add_comm n k)) (symm (add_succ_left k n))
    }

// :86-91
/// Addition is associative: `(n + m) + k = n + (m + k)`.
def add_assoc (n: Nat, m: Nat, k: Nat): Eq((n + m) + k, n + (m + k)) =
    match k {
        case zero => rfl
        case succ(l) => cong_succ (add_assoc n m l)
    }
```

**题目点名的引理 → 位置对照表**：

| 引理 | 是否在 prelude | 位置 |
|---|---|---|
| `add_zero_right` | ✅ | `src/prelude/core/nat.typort:57-58` |
| `add_comm` | ✅ | `src/prelude/core/nat.typort:80-84` |
| `add_assoc` | ✅ | `src/prelude/core/nat.typort:87-91` |
| `add_succ_left` | ✅ | `src/prelude/core/nat.typort:73-77` |
| `cong_succ` | ✅ | `src/prelude/core/nat.typort:51-52` |
| （另：`add_zero_left` `:62`、`add_succ_right` `:69`、`mul_zero_right` `:101`、`mul_one_right` `:277`、`mul_comm` `:130`、`mul_assoc` `:155`、`double` `:227`、`pred` `:165` 等） | | |

乘法律要求注意形态（`:93-98` 的注释）：`nat_mul` 对**第二个**参数递归，所以语句
形如 `n * succ m = n + n * m`；`n * m + n` 与左端不 definitionally 相等，不能作语句。

### 5.4 `calc` 链式语法

`src/prelude/core/calc.typort` 提供 `calc { a = b by p … }`。**它不是内核的一部分**，
而是一个 `#[macro_export] macro_rules calc`（L11 的宏机制），位于 `PRELUDE_CORE`
清单内（`src/L13_namespace/mod.rs:4099`），因此所有证明示例都能用。

**关键：它展开为 let 链 + `Eq` 注解 + `trans`，不是嵌套 `trans`**（`src/prelude/core/calc.typort:14-21`
的设计注释，宏体 `:48-64`）：

```
calc { a = b by p1   b = c by p2   c = d by p3 }
⇒
let _c : Eq (a) (b) = (p1);
let _ : Eq (b) (c) = (p2);          -- 逐步检查**书写出来的两端**
let _c = trans (_c) (p2);
let _ : Eq (c) (d) = (p3);
let _c = trans (_c) (p3);
_c
```

- 第一步带注解的 `let` 用证明检查两端；后续每步的注解 `let` 同时写出两端
  （注释 `:22-26` 解释：早先的 `Eq _ _ ($z)` 洞写法会留下未解 meta）；
- `trans` let 负责链的**连续性**（上一步右端 ≐ 下一步左端）；
- 两个宏臂：花括号多行形式（步骤以换行分隔，`:48-53`）与单行形式
  `calc a = b by p1 = c by p2`（`:59-64`）；
- `by` 是专用 token（`TokenKind::ByKeyword`），不是 Op 也不是 Ident，所以
  `$y: raw` 片段会在它前面干净停下（`:31-38`）。

用法示例：`examples/theorem_proving.typort:30-34`、`:114-118`；
`examples/adder_proof.typort:81-85`、`:163-167`。

形式化时可把 `calc` 当作纯语法糖：它就是 `trans` 链 + 中间类型注解。

### 5.5 勘误：三个 `examples/` 程序实际包含什么

任务描述假设 `examples/theorem_proving.typort` / `adder_proof.typort` /
`typeclass_complex.typort` 里有"用 enums / GADT 风格索引族"的程序。实际情况是：

| 文件 | 自己声明的 enum | 用到的索引族 |
|---|---|---|
| `examples/theorem_proving.typort`（272 行） | **0 个** | 无（只有 `Nat`/`Boolean` 上的 `Eq` 证明） |
| `examples/adder_proof.typort`（371 行） | **0 个** | **prelude 的 `Vec[A](len: Nat)`**（外部声明的 GADT） |
| `examples/typeclass_complex.typort`（294 行） | 3 个（`Tree[T]`、`BoolExpr`、`Arith`）；**都不是索引族** | 无 |

- **GADT 消去的最佳例子仍是 `src/prelude/data/vec.typort`**（§6.5），特别是
  `impl[T, len: Nat] Vec[T](succ len) { … }` 这种**带索引约束的实例块**
  （`src/prelude/data/vec.typort:145-163`）——它使 `case cons(x, _)` 成为唯一可达臂。
- `examples/adder_proof.typort` 展示了真实规模的索引族消去：
  `def vec_adder[len: Nat](ci: Boolean, a: Vec[Boolean] len, b: Vec[Boolean] len)` 的
  `nil` 分支只所以能类型检查，是因为 `a : Vec[Boolean] 0` 把 `b` 也精化成 `nil`
  （`examples/adder_proof.typort:61-66`）。
- `examples/theorem_proving.typort` 是 `Eq` 组合子的用法总览：`trans`/`symm`/`cong`
  （含带 λ 的 `cong`，`:132-136`）、`calc` 的六个变体、`Boolean` 上的 `match`
  （`not_not`，`:224-228`——**prelude 故意不定义这个名字**，见下）。
- `subst` 在 `examples/` 里**从未被调用**：`theorem_proving.typort:234-251` 的注释讨论
  它，但 `subst_eg`（`:249`）的体是 `trans(add_zero_right(5), rfl)`。
- `typeclass_complex.typort` 里 `eq_congr_eg`（`:293`）的注释写着 `eq_congr`，函数体
  实际调用 `cong`；`eq_congr`（`src/prelude/core/eq.typort:58`）在 `examples/` 中无调用点。

**命名空间是扁平的**：`src/prelude/core/bool.typort:201-202` 明确记录"不在 prelude 里
定义 `not_not`"，因为 `examples/theorem_proving.typort:224` 定义了它，重名会让该
example 报 `redefine`。这从侧面确认了 §1.3 的重定义规则在 prelude 与用户代码之间生效。

---

## 6. `Nat` / `Boolean` 与其它内建-ish 类型

### 6.1 来源：prelude 文件（不是 Rust 硬编码）

`Nat` 与 `Boolean` 都是**普通 typort 声明**，位于 `src/prelude/core/`，
由 `include_str!` 编译进二进制。加载清单与顺序（`src/L13_namespace/mod.rs:4095-4111`，
注释在 `:4086-4094`）：

```rust
pub(crate) const PRELUDE_CORE: &[(&str, &str)] = &[
    ("op", include_str!("../prelude/core/op.typort")),
    ("eq", include_str!("../prelude/core/eq.typort")),
    ("nat", include_str!("../prelude/core/nat.typort")),
    ("calc", include_str!("../prelude/core/calc.typort")),
    ("bool", include_str!("../prelude/core/bool.typort")),
    ("option", include_str!("../prelude/data/option.typort")),
    ("result", include_str!("../prelude/data/result.typort")),
    ("order", include_str!("../prelude/data/order.typort")),
    ("void", include_str!("../prelude/core/void.typort")),
    ("decidable", include_str!("../prelude/data/decidable.typort")),
    ("vec", include_str!("../prelude/data/vec.typort")),
    ("either", include_str!("../prelude/data/either.typort")),
    ("list", include_str!("../prelude/data/list.typort")),
    ("string", include_str!("../prelude/data/string.typort")),
    ("nonempty", include_str!("../prelude/data/nonempty.typort")),
];
```

顺序有意义：`eq` 在 `nat` 之前（`nat.typort` 用 `Eq`）；`op` 最先（`Add`/`Mul` 等 trait）。
加载实现：`load_prelude_state_impl`（`src/L13_namespace/mod.rs:4218-4282`）拼接
`PRELUDE_CORE` + `PRELUDE_HDL`（19 个文件，`:4114-4140`）+ `PRELUDE_SHOW`（`:4142-4143`，
恒排最后，依赖 `nat_to_dec` prim），逐文件 `preprocess` → `parser_with_macros` →
逐 decl `infer_in_place`（`:4244-4268`）。
**L07/L08 层自身不加载 prelude**（grep `PRELUDE|include_str!` in `src/L07_sum_type`
无命中）——L07 的测试都在源码里自己声明 `enum Nat { zero succ(x: Nat) }`。
`L07_sum_type` 是**完全名字无关**的（只按结构操作 `Raw::Sum`/`SumCase`）；所有
按名字特判 `"Nat"` 的代码都在 `src/L13_namespace`（`is_nat_sum`
`L13_namespace/mod.rs:249-251`、`nat_step_value` `:280-292`、`pretty.rs:210-216`）。

**哪些是硬编码的**：

- **字符串字面量**：`Raw::LiteralIntro`，类型 `Val::LiteralType`（`L07/elaboration.rs:681`）；
- **Nat 数字字面量**：L07 的 `Raw` **没有** nat literal 节点，L07 里不能写 `0`/`5`；
  L13 才有 `Raw::Nat(Span<u64>)`（`src/L13_namespace/parser/syntax.rs:94`，elaboration
  `elaboration.rs:3385-3391`）。`theorem_proving.typort` 里的 `5`、`7` 是 L13 语法；
- **Nat 算术 primop**：`nat.typort` 加载**之后**，`Cxt::register_nat_builtins`
  把 `nat_add`/`nat_mul`/`nat_sub`/`nat_div`/`nat_rem` **替换**为原生 u64 primop，
  "复现完全相同的归约行为"（`src/prelude/core/nat.typort:3-8`、`:19-24`；
  `src/L13_namespace/cxt.rs:1121-1163`，循环在 `:1152-1161`）。
  触发点是**内容比较**而非索引/名字：`if p == nat_typort { … }`，其中
  `nat_typort = include_str!("../prelude/core/nat.typort")`（`L13_namespace/mod.rs:4236`、
  `:4276-4281`）。这就是 `add_zero_right` 能写成 `rfl` 的原因：primop 在第二参数为
  `zero` 时直接返回 `x`。`pred`/`nat_max`/`nat_min`/`double`/`nat_pow`/`nat_factorial`
  **仍是 typort 递归定义**（注释 `cxt.rs:1147-1151`）。同一函数还注册
  `nat_to_dec`、`width_range`、`nat_is_ground`（`cxt.rs:1124-1145`）。
- **字符串 builtin**（`string_concat` / `str_eq` / `str_indent2` …）：Rust 里的
  `prim_reduce`（`L07/mod.rs:807+`），值层经 `Val::Prim(name, spine)` 卡住/归约。

**L13 的 Nat 压缩注意事项**（形式化时不要依赖）：L13 用 `Val::Nat(u64)` 原生表示，
`nat_step_value`（`L13_namespace/mod.rs:284-291`）与 Nat 的模式匹配臂
（`L13_namespace/pattern_match.rs:629-634`、`:642-647`）**硬编码 index 0 = `zero`、
index 1 = `succ`**，只以"Sum 名字是否等于 `Nat`"为门控，不比较构造子名。
L07/L08 **没有**这套压缩（L07 的 `Nat` 就是普通 `SumCase` 链），所以这条
只影响 L13 及以后的层。

### 6.2 `Nat`（`src/prelude/core/nat.typort:10-16`，逐字）

```typort
/// Unary (Peano) natural numbers.
enum Nat {
    /// Zero.
    zero
    /// The successor of `n`.
    succ(n: Nat)
}
```

加法（fallback 递归定义，随后被 primop 覆盖；`:26-31`）：

```typort
/// Addition, by recursion on the second argument.
def nat_add(x: Nat, y: Nat): Nat =
    match y {
        case zero => x
        case succ(n) => succ (nat_add x n)
    }
```

乘法（`:38-43`）：

```typort
/// Multiplication, by recursion on the second argument.
def nat_mul(x: Nat, y: Nat): Nat =
    match y {
        case zero => zero
        case succ(n) => nat_add(x, nat_mul x n)
    }
```

运算符实例（`:33-36`、`:45-48`）：`impl Add[Nat, Nat] for Nat { def +(that: Nat): Nat = nat_add this that }`、
`impl Mul[Nat, Nat] for Nat { … nat_mul this that }`；另有 `Sub`（`:182-184`）、
`Div`（`:202-204`）、`Rem`（`:222-224`）、`Default`（`:237-239`）。

### 6.3 `Boolean`（`src/prelude/core/bool.typort:16-21`，逐字）

```typort
enum Boolean {
    /// Logical truth.
    true
    /// Logical falsity.
    false
}
```

注意文件头（`:3-9`）说明：`Boolean` 是**运行时真值**类型；HDL 的硬件信号 `Bool`
是 `hdl-types.typort` 里的另一个 struct（`{name, zz_expr}`）。两者不同，
转换见 `impl Into[Bool] for Boolean`（经 `bool_to_nat`）。

**`Bool` 不是内建**：`grep '"Bool"'` 在 `src/` 里只命中 HDL 宏与测试
（`src/L13_namespace/parser/derive.rs:280`、`:521-522`、`:1323`、`:1343`）。
`Bool` 只在 **HDL prelude** 里存在：`src/prelude/hdl/hdl-types.typort:91-99`
的 `struct Bool { name: Option[String]  zz_expr: Expr }`，桥接在
`hdl-types.typort:116-118`（`impl Into[Bool] for Boolean { def into: Bool = Bool.mk(None, literal(bool_to_nat(this))) }`）。
`hdl-types.typort` 是第 4 个 HDL 文件（`src/L13_namespace/mod.rs:4121`），
在 core 之后很久才加载；`load_prelude_skip_hdl()` 时 `Bool` 不可用
（`src/lib.rs:1302-1304`）。形式化时**核心语言只有 `Boolean`**。

`Boolean` 的方法与实例（`bool.typort:23-53`）：`impl Boolean { def not }`、`impl Xor`、`impl And`、
`impl Or`、`impl Boolean { def &&, def || }`（后者必须放在 `And`/`Or` 实例之后，
否则方法体里的 `&`/`|` 解析不到）。`true`/`false` 的裸名别名来自通用别名 pass
（`src/L13_namespace/mod.rs:4287-4308`、`src/lib.rs:1359+`），**不是** Rust 特判。

### 6.4 `Void`（`src/prelude/core/void.typort`，全文 7 行）

```typort
//! The empty type `Void` and its eliminator.

/// The uninhabited type: it has no constructors.
enum Void {}

/// Ex falso: from a `Void` value, produce a value of any type `A`.
def absurd[A](v: Void): A = match v {}
```

**零构造子 enum + 零臂 match** 是这一层必须支持的两个边界：`enum Void {}`
（注意：L07 与 L08 的 `p_enum` 用 `many1_sep`（`L07/parser/mod.rs:495`、
`L08/parser/mod.rs` 的 `p_enum`），**至少一个 case**，所以空 enum 在 L07/L08 的
解析器里**不能**直接写；只有 L13 的 `p_enum` 用 `many0_sep`（`src/L13_namespace/parser/mod.rs:2287`）
可以解析空 enum）；`match v {}` 是零臂 match，编译期：
`head_sum` 的构造子表为空 ⇒ 覆盖循环空转；逐臂循环空转；`self.pats` 为空 ⇒
`Tm::Match(v, [])`。运行时 `eval_aux` 对空 `cases` 返回 `None` ⇒ 卡住
（`L07/pattern_match.rs:688-693`）。形式化应支持零构造子 enum 与零臂 match，
语义完全良定义。

### 6.5 GADT 索引族示例：`Vec`

```typort
// src/prelude/data/vec.typort:3-9（逐字）
/// A vector of exactly `len` elements of type `A`.
enum Vec[A](len: Nat) {
    /// The empty vector, of length 0.
    nil -> Vec[A] 0
    /// A cons cell: prepending one element raises the length by one.
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (l + 1)
}
```

- `A` 是隐式参数；`len` 是显式索引；
- `nil` 的返回 `Vec[A] 0`：Impl 槽 `A` 是 enum 参数的 bare rigid（合格），
  Expl 槽 `0` 是索引特化（不检查）；
- `cons` 自己重新绑定 `[l : Nat]`（**与索引 `len` 同名不同槽**），返回 `Vec[A] (l + 1)`；
- 使用点写 `Vec[A] (succ L)` / `Vec[A] l`，比较靠 `unify_indices`。

`impl[T, len: Nat] Vec[T](succ len) { … }`（`:145-163`）是**带索引约束的实例块**：
接收者类型写 `Vec[T] (succ len)`，方法体里 `this : Vec[T] (succ len)`，于是
`case cons(x, _)` 是唯一可达臂。这是 GADT 消去的最简实用形态。

---

## 7. 汇总：形式化时必须保持的不变式与边界

### 7.1 必须保持的不变式（invariants）

| # | 不变式 | 锚点 |
|---|---|---|
| I1 | `bind_count(Con(c, ps)) = 1 + Σ bind_count(ps)`；编译期槽、运行时 prepend、quote 的 fresh rigid 三方同序同数 | `L07/mod.rs:106-113`、`L07/pattern_match.rs:421-426`、`:729-735`、`L07/mod.rs:1285-1287` |
| I2 | `Val::SumCase.typ` 是**完整实例化**的 Sum；`datas` 只含构造子自己的绑定器（不含 enum 隐式参数） | `L07/mod.rs:206-210`、`L07/elaboration.rs:338-358` |
| I3 | `force` 的返回值顶层**不会是 VSub**（fuel 耗尽除外） | `L07/mod.rs:216-219`、`:1222-1226` |
| I4 | `Subst` 链头 = 最新解；`extend` O(1)；同键旧条目留在链上但永不命中 | `L07/mod.rs:224-235`、`:331-339` |
| I5 | σ 只对**被包裹过**的值生效（meta 解与 decl 表条目不在扫描/包裹范围内） | `L07/README.md:92-95` |
| I6 | `subst_cxt` 不改 `lvl` / 槽位数 / pruning / de Bruijn 索引 | `L07/cxt.rs:329-352` |
| I7 | 头部精化只对 `x < cxt.lvl`、在可解集内、且**尚未**有解、且 occurs 守卫通过的 bare rigid 做；失败**不阻断** | `L07/pattern_match.rs:655-666` |
| I8 | 臂边界回滚 σ 与 solvable（O(1) 指针赋值），**meta 解不回滚** | `L07/pattern_match.rs:211-219` |
| I9 | `frcs` 只对 Rigid 头推进（命中烧 1 fuel）；闭包 env / spine / Sum / SumCase / Match-env 只包裹 | `L07/mod.rs:673-787` |
| I10 | 方程的调用侧顺序是"头部在前"；`unify_indices` 里 `hp` 与 `rp` 同长 | `L07/pattern_match.rs:350-371` |
| I11 | `match` 的臂按**用户书写顺序**保存，运行时首匹配；通配臂之后一律报"分支不可达" | `L07/pattern_match.rs:150-161`、`:688-693` |
| I12 | `Raw::Obj` 的局部遮蔽优先于全局限定名解析 | `L07/elaboration.rs:459-472` |
| I13 | struct 脱糖后唯一可用的类型级剥链门控是 `cases.len()==1 && case.data.contains(".mk")` | `L08/elaboration.rs:499` |

### 7.2 诚实边界（不要当作规范的一部分）

1. **期望类型里的外层 meta**（`L07/README.md:306-309`）：若期望类型含 match 之外创建的
   未解 meta，臂内约束可能把它解成含臂局部模式变量的值，rename 因作用域越界失败而报
   can't unify。Lean 4 侧应对应于 generalize / block。
2. **force 无记忆 + fuel 是软防护**（`L07/README.md:310-319`）：燃料耗尽时精化读点按
   **未解**处理 ⇒ 极深嵌套模式负载下可能把合法分支误判为不可达（假 absurd）。
   特化方程失败的文案带 `(fuel exhausted)` 尾注。
3. **没有 K 层面的保护**（`L07/README.md:320-321`）。
4. **probe 与臂内方程理论上可能不同步**（`L07/README.md:322-324`）：探测用 scratch 层级、
   臂内用真槽，极端情形（方程解依赖层级数值本身）判定可能不一致。
5. **深值遍历已迭代化，但深值的"释放"仍是递归 Drop；`quote`/`pretty` 对深值仍是递归**
   （`L07/README.md:330-340`）。纯实现细节，不影响语义。
6. **空 enum 在 L07/L08 解析器不可写**：`p_enum` 的 case 列表用 `many1_sep`
   （`L07/parser/mod.rs:495`；L08 同，`L08/parser/mod.rs` 的 `p_enum`），至少一个 case。
   `enum Void {}` 只存在于 L13/prelude 的解析器（L13 的 `p_enum` 用 `many0_sep`，
   `src/L13_namespace/parser/mod.rs:2287`）。形式化时应支持零构造子 enum
   （语义上完全没问题：覆盖循环空转、零臂 match 合法）。
7. **`Eq` 只有一个构造子，没有 `J`/`K` 区分**；`subst`/`symm`/`trans`/`cong` 全部是
   用 `match` 手写的组合子，不是内核原语。
8. **`struct` 不产生新的类型论构造**：形式化可把 `struct` 当作"单构造子索引族 +
   投影定义"的记法糖，投影的值级规则就是 pattern-match/recursor 的 `β` 规则。
9. **L13 起的 `Nat` 原生压缩**（§6.1）与 `Bool`（HDL-only，§6.3）都是 L13 层的事，
   不属于 L07/L08 的语义；L07/L08 里 `Nat`/`Boolean` 就是普通的
   `Sum`/`SumCase` 树。

### 7.3 重新实现的检查清单（顺序即依赖序）

1. 实现 `Σ`/Π/`U` 与 NbE（meta 求解器 invert/prune/solve/intersect）；
2. 实现 `Val::Sum`（名字 + 参数四元组 + 构造子名表）与 `Val::SumCase`（typ + case + datas）；
3. 实现 enum 声明：隐式参数钉 U → enum 类型 `Π params → U` → 构造子类型
   `Π impl_params → Π binders → ret|default` → `check_ctor_wf`（三条件）→ 注册双轨名；
4. 实现 `Subst`（持久化单链）+ `wrap_sub` + `force` 的 `VSub`/`frcs`（槽位纪律）；
5. 实现模式编译器：`bind_slots` 基线 → 逐臂 `walk`/`walk_con`（head 槽 + 隐式参数
   实例化 + 每绑定器 fresh rigid + icit 对齐 + 嵌套递归）→ `unify_indices`（头部在前）
   → 头部精化（四条件 + occurs 守卫）→ `subst_cxt` + motive 重锚 → `check` body；
6. 实现可达性探测（scratch 层级 + meta 快照回滚 + 逐 ctor 独立充值 + fuel 耗尽按可达）
   与两级覆盖检查（顶层 `covers`、嵌套 `cover_at`/`PosCover`）；
7. 实现运行时：`eval(Tm::Match)` 首匹配、`Val::Match` 卡住 + `pending` 值层应用、
   `force` 的重选分支、`quote`/`unify` 的 Match 臂、`struct_eq` 快路径；
8. 实现投影 `project`（索引槽优先 + 字段 datas/类型链）+ force 的 `Obj` 再投影；
9. L08 增量：`struct`→`{Name}.mk` 单构造子 enum、`new`→限定构造子应用、
   多段投影链、类型级 `.mk` 剥链（卡住投影精确实例化）、`unify` 的 `(Obj,Obj)` 臂。

---

## 附录 A：错误文案速查

| 文案 | 触发 | 锚点 |
|---|---|---|
| `redefine {名}` | enum/def 名与已有 decl 表键冲突 | `L07/elaboration.rs:319`、`:214` |
| `构造子 {c} 的返回类型不是和类型` | `check_ctor_wf` 第 2 步 | `L07/elaboration.rs:414-416` |
| `构造子 {c} 的返回类型是 {X}，不是 {E}` | 同上，头名不符 | `L07/elaboration.rs:424-427` |
| `构造子 {c} 的返回类型参数必须是 {E} 的参数变量（参数不得特化，特化请用显式索引）` | 同上，Impl 位非 bare rigid | `L07/elaboration.rs:438-440` |
| `match 的对象必须是和类型（enum）` | scrutinee 类型非 Sum | `L07/pattern_match.rs:127` |
| `` `{n}` 不是构造子，不能带子模式解构 `` | 头部非 Sum 且带子模式 | `L07/pattern_match.rs:445-448` |
| `` `{n}` 不是 {E} 的构造子，不能带子模式解构 `` | 头部是 Sum 但 n 不是构造子且带子模式 | `L07/pattern_match.rs:467-471` |
| `找不到构造子 {E}.{n}` | decl 表缺该构造子 | `L07/pattern_match.rs:484` |
| `构造子 {n} 缺少字段 {f} 的模式` | 显式绑定器无对应 Expl 子模式 | `L07/pattern_match.rs:534-537` |
| `构造子 {n} 的模式多了 {k} 个子模式` | 子模式多余 | `L07/pattern_match.rs:622-627` |
| `构造子 {c} 与被匹配类型参数数不一致` | 两侧 Sum 参数个数不同 | `L07/pattern_match.rs:370` |
| `构造子 {c} 与被匹配类型不相容（分支不可达）`（可带 ` (fuel exhausted)`） | 特化方程失败 | `L07/pattern_match.rs:390-392` |
| `分支不可达：模式 {p:?} 与被匹配类型不相容` | 上述失败落到编译错误 | `L07/pattern_match.rs:208` |
| `分支不可达：模式 {p:?} 被前面的通配臂遮蔽` | 通配臂之后 | `L07/pattern_match.rs:159` |
| `match 不完整：缺少构造子 {c}` | 顶层覆盖缺失 | `L07/pattern_match.rs:147` |
| `match 不完整：模式位置 {path} 缺少构造子 {c}` | 嵌套覆盖缺失 | `L07/pattern_match.rs:254-258` |
| `name not in scope: {x}` | 变量未绑定（含"显式索引不能直接当构造子 binder"） | `L07/elaboration.rs:455` |
| `{E} has no field {f}` | 投影找不到字段 | `L07/elaboration.rs:483`、`L08/elaboration.rs:535` |
| `cannot project field {f}` | 接收者既非 Sum 也非 SumCase | `L07/elaboration.rs:551` |
| `expected universe, got …` | 类型注解形态确定非类型 | `L07/elaboration.rs:161-164` |
| `match cannot be inferred; give it an expected type` | `match` 出现在推断位 | `L07/elaboration.rs:684-686` |
| `can't unify[ (fuel exhausted)] {a} == {b}` | 常规转换失败 | `L07/mod.rs:1326-1330` |
| `ill-scoped SumCase` | 接收者 SumCase 的 `typ` 不是 Sum | `L07/elaboration.rs:493` |

---

## 附录 B：本规范引用的源码清单

| 文件 | 作用 |
|---|---|
| `src/L07_sum_type/README.md` | 设计蓝图（后续章节引用；本文大量对照） |
| `src/L07_sum_type/mod.rs` | `Tm`/`Val`/`PatternDetail`/`Subst`、`force`/`frcs`/`eval`/`quote`/`project` |
| `src/L07_sum_type/elaboration.rs` | enum 声明 + `check_ctor_wf` + `check`/`infer_expr` + 投影类型规则 |
| `src/L07_sum_type/pattern_match.rs` | `Compiler`：下钻、特化方程、头部精化、可达性、覆盖检查、`eval_aux` |
| `src/L07_sum_type/unification.rs` | `SpecSolve`、可解 rigid 规则、所有合一臂 |
| `src/L07_sum_type/cxt.rs` | 上下文、`bind`/`define`、`subst_cxt`、`bind_slots`、decl 表 |
| `src/L07_sum_type/struct_eq.rs` | 结构相等快路径 |
| `src/L07_sum_type/parser/syntax.rs` | `Raw`/`Pattern`/`Decl`/`Icit` |
| `src/L07_sum_type/parser/mod.rs` | `p_pattern`/`p_match`/`p_enum`/`p_decl`/`p_pi_binder` |
| `src/L07_sum_type/tests.rs` | 单元测试（含 `test_ctor_wf_*` 等回归钉） |
| `src/L08_product_type/README.md` | L08 设计蓝图 |
| `src/L08_product_type/parser/mod.rs` | `p_struct`（脱糖）、`p_new`、`p_atom`（投影链） |
| `src/L08_product_type/elaboration.rs` | 类型级 `.mk` 剥链（`Raw::Obj`） |
| `src/L08_product_type/unification.rs` | `(Obj,Obj)` 合同臂 |
| `src/prelude/core/eq.typort` | `Eq`/`refl`/`rfl`/`cong`/`symm`/`trans`/`subst`/`cong2`/`cong3`/`subst2`/`Cast` |
| `src/prelude/core/nat.typort` | `Nat` + `nat_add`/`nat_mul` + 全部算术引理 |
| `src/prelude/core/bool.typort` | `Boolean` + 布尔方法/实例 |
| `src/prelude/core/void.typort` | `Void` + `absurd` |
| `src/prelude/data/vec.typort` | `Vec`（GADT 索引族范例）+ 实例块 |
| `src/L13_namespace/mod.rs` | prelude 加载清单与顺序（`PRELUDE_CORE`） |
| `examples/theorem_proving.typort` | `Eq` 组合子/`calc` 实用示例 |
| `examples/adder_proof.typort` | 大规模归纳证明（`Vec`/`Eq`/`calc`/`cong_succ`/`add_assoc`…） |
| `tests/l07_blackbox_v3.rs` | `v3_multi_index_gadt`（重绑定惯用法钉） |
