# Typort 元变量 / 隐式参数 / 类型类 —— Lean 4 形式化规格

> 逆向工程自本仓 `F:\projects\hermes\elaboration-zoo-lsp` 的 Rust 实现。
> 所有 `file:line` 锚点对应本次检出的**参考实现**（`mod.rs` / 分文件版），
> Rust 引文均为逐字复制。性能孪生 `bump_spine_iter*` 语义与参考实现
> 「Ok 输出逐字节一致」，本规格不区分二者，仅在孪生有独占机制时点明。

---

## 0. 范围、记号与实现层次

### 0.1 层次

| 层 | 目录 | 相对上一层新增 |
|---|---|---|
| L03 | `src/L03_holes/` | 元变量（hole）、`insert`/`solve`、pattern unification、occurs/scope check |
| L04 | `src/L04_implicit/` | `Icit` 穿线、隐式实参**插入**、命名隐式实参、`NameOrigin` |
| L05 | `src/L05_pruning/` | typed meta（meta 存类型）、`Pruning` 掩码、pruning（剪枝）、`intersect`、`flexFlex` |
| L10 | `src/L10_typeclass/` | `trait`/`impl`/`outParam`、实例表、tabled resolution、`trait_wrap` 点号调用、`SpecSolve` |
| L12 | `src/L12_canonical/` | Val 级实例匹配（无 `Typ` 桥）、decl 表、canonical 搜索（`iddfs`/`search`）、`no_metas` 错误路径 |

L03–L05 **无宇宙层级**（`Val::U` 是单点）；L09 起 `Val::U(u32)`。L03–L05 无
`decl` 表、无 builtin、无 `fuel`；L10 起有 `fuel`，L12 起有 `decl` 表与
显式替换 `Subst`/`VSub`。

### 0.2 记号对照（Rust → 数学）

| Rust | 数学 |
|---|---|
| `Lvl(u32)` | 层级 `l`（de Bruijn **level**，绑定时自增） |
| `Ix(u32)` | 索引 `x`（de Bruijn **index**，`lvl2ix l x = l - x - 1`，`src/L03_holes/mod.rs:138-140`） |
| `MetaVar(u32)` | 元变量 `?m`（metacontext 下标） |
| `Val::Flex(m, sp)` | 未解元变量的中性链 `?m sp` |
| `Val::Rigid(x, sp)` | 局部变量中性链 `x sp` |
| `Spine = List<(Val, Icit)>` | 实参表，**snoc**：`List` 头 = **最后**应用的实参（`src/L04_implicit/mod.rs:108-109`） |
| `Pruning = List<Option<Icit>>` | 掩码，与 env 平行，头 = 最内层槽位（`src/L05_pruning/mod.rs:97-99`） |

**关键约定（几乎所有 bug 都出在这里）**：`Spine` 是 snoc，头 = 最后应用的
实参，尾 = 更早的实参。因此 `invert_go`/`rename_sp`/`unify_sp` 都**先递归
tail 再处理 head**（`src/L03_holes/mod.rs:312-326`、`:339-354`、`:400-409`），
而任何"按应用序重建"的地方都必须显式 `reverse`（`src/L05_pruning/mod.rs:783-784`）。

### 0.3 双实现与语义权威

- `src/L03_holes/readme.md:9-13`：`mod.rs` = 参考实现（对应上游
  elaboration-zoo `Main.hs`），`bump_spine_iter.rs` = 性能实现，**两版输出
  逐字节一致**（互检测试）。
- `src/L10_typeclass/README.md:7-9`：实例求解器 `typeclass.rs::Synth` 为
  参考版与孪生**共用**；其余各一份，语义以参考版为准。
- `src/L12_canonical/README.md:9-10`：L12 与孪生「Ok 输出逐字节一致」，
  错误消息内嵌 Span 全零系孪生偏差（`src/L12_canonical/README.md:354-356`）。

---

## 1. 元变量（metavariables / holes）

### 1.1 核心语法（L03）

`src/L03_holes/mod.rs:86-101`：

```rust
/// 表面语法经 elaboration 产出的核心语法。
#[derive(Debug, Clone)]
enum Tm {
    Var(Ix),
    Lam(Name, Box<Tm>),
    App(Box<Tm>, Box<Tm>),
    U,
    Pi(Name, Box<Ty>, Box<Ty>),
    Let(Name, Box<Ty>, Box<Tm>, Box<Tm>),
    /// 显式引用的 meta（`rename` 产出：解里对其它 meta 的引用、以及
    /// `?m := ?m'` 一类解）。
    Meta(MetaVar),
    /// hole 处插入的 meta：抽象掉 elaboration 当时的全部 Bound 变量
    /// （`bds` 与求值环境平行，`Defined` 槽位跳过）。
    InsertedMeta(MetaVar, List<BD>),
}
```

注意 **L05 把 `InsertedMeta(m, bds)` 换成了 `AppPruning(t, pr)`**
（`src/L05_pruning/mod.rs:176-178`）：

```rust
    /// 把项（实践中即 `Meta`）按掩码应用到当前 scope：`Some(icit)` 槽位
    /// 应用（icit 取掩码里的）、`None` 槽位跳过（上游 `TAppPruning`）。
    AppPruning(Box<Tm>, Pruning),
```

`BD`（L03/L04 的槽位标记，`src/L03_holes/mod.rs:78-84`）：

```rust
/// fresh meta 抽象的作用域掩码：`Bound` = 真依赖（解里要 λ 抽象），
/// `Defined` = 可展开的 let 定义（解里跳过该槽位）。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BD {
    Bound,
    Defined,
}
```

**语义**：hole 处生成的元变量是一个「函数」，其参数是当前作用域的
**全部 `Bound` 变量**（`Defined` 槽位跳过，因为 let 定义在解里必须展开）。
L05 起参数改为「掩码筛过的 scope」，每个保留槽位记录其 `Icit`。

### 1.2 值层与 metacontext

`src/L03_holes/mod.rs:119-128`（L04 给 `Lam`/`Pi` 加 `Icit`，
`src/L04_implicit/mod.rs:116-124`）：

```rust
#[derive(Debug, Clone)]
enum Val {
    /// 未解 meta 的中性应用链（已解的 meta 在 force 时展开成解值）。
    Flex(MetaVar, Spine),
    /// 局部变量的中性应用链。
    Rigid(Lvl, Spine),
    Lam(Name, Closure),
    Pi(Name, Box<VTy>, Closure),
    U,
}
```

metacontext（L03：只有「已解/未解」二态，`src/L03_holes/mod.rs:45-50`）：

```rust
/// metacontext 条目：已解（解是空环境下的值）或未解。
#[derive(Debug, Clone)]
enum MetaEntry {
    Solved(Val),
    Unsolved,
}
```

**L05 起 meta 一律携带类型**（`src/L05_pruning/mod.rs:64-70`）——pruning
必须能检查"剪后的类型是否良型"：

```rust
/// metacontext 条目：**类型一律保留**（pruning 要检查剪后的类型良型），
/// 已解另存解值。
#[derive(Debug, Clone)]
enum MetaEntry {
    Solved(Val, VTy),
    Unsolved(VTy),
}
```

L12 进一步变成三元组 `Unsolved(闭类型, Arc<Cxt> 快照, 原始类型)`
（`src/L12_canonical/mod.rs:29-33`）：

```rust
#[derive(Debug, Clone)]
enum MetaEntry {
    Solved(Rc<Val>, Rc<VTy>),
    Unsolved(Rc<VTy>, std::sync::Arc<Cxt>, Rc<VTy>),
}
```

第三分量（`origin_typ`，创建处的**未闭化**类型）专门服务错误报告与
`no_metas`（`src/L12_canonical/README.md:261-263`）。

`Infer` 就是一个 metacontext 向量：

- L03：`struct Infer { metas: Vec<MetaEntry> }`（`src/L03_holes/mod.rs:147-155`）
- L05：`struct Infer { meta: Vec<MetaEntry> }`（`src/L05_pruning/mod.rs:400-416`）
- L10/L12：`Infer` 另带 `trait_solver` / `trait_definition` /
  `trait_out_param` / `unify_fuel`（`src/L10_typeclass/mod.rs:461-499`、
  `src/L12_canonical/mod.rs:607-621`）。

### 1.3 `fresh_meta`

**L03**（`src/L03_holes/mod.rs:157-174`）——注意**没有类型**：

```rust
    /// 挂新洞：metacontext 追加未解条目，产出应用到当前全部 Bound 槽位的
    /// `InsertedMeta`。
    fn fresh_meta(&mut self, cxt: &Cxt) -> Tm {
        self.metas.push(MetaEntry::Unsolved);
        Tm::InsertedMeta(MetaVar(self.metas.len() as u32 - 1), cxt.bds.clone())
    }
```

**L05**（`src/L05_pruning/mod.rs:412-447`）——带类型，且类型被**闭成迭代 Π**：

```rust
    /// 挂新 meta（带类型），返回编号。
    fn new_meta(&mut self, a: VTy) -> MetaVar {
        self.meta.push(MetaEntry::Unsolved(a));
        MetaVar(self.meta.len() as u32 - 1)
    }

    /// `freshMeta cxt a`：类型闭成迭代 Π 存进 metacontext，项侧是
    /// `AppPruning ?m (cxtPruning)`——把 meta 应用到当前全部绑定槽位。
    fn fresh_meta(&mut self, cxt: &Cxt, a: VTy) -> Tm {
        let closed = self.close_meta_ty(cxt, self.quote(cxt.lvl, &a));
        let m = self.new_meta(closed);
        Tm::AppPruning(Box::new(Tm::Meta(m)), cxt.pruning.clone())
    }
```

闭化函数（`src/L05_pruning/mod.rs:148-168`，注意 **`Bind` 补**显式 Π、
`Define` 补 `let`**，且内层 binder 包得更深）：

```rust
pub fn close_ty(mcl: &Locals, b: Ty) -> Ty {
    match mcl {
        Locals::Here => b,
        Locals::Bind(mcl, x, a) => close_ty(
            mcl,
            Tm::Pi(x.clone(), Icit::Expl, Box::new((**a).clone()), Box::new(b)),
        ),
        Locals::Define(mcl, x, a, t) => close_ty(
            mcl,
            Tm::Let(
                x.clone(),
                Box::new((**a).clone()),
                Box::new((**t).clone()),
                Box::new(b),
            ),
        ),
    }
}
```

**形式化规则（L05 版）**：设当前上下文 telescope 为 `Δ`（`Bind`/`Define`
交替），`a` 为当前上下文中的类型项。

```
Δ ⊢ a : Type      q = quote_{|Δ|}(a)      closed = eval [] (close_ty Δ q)
─────────────────────────────────────────────────────────────────────────
Δ ⊢ fresh_meta(a)  ⇝  AppPruning ?m pr ,   ?m ↦ Unsolved(closed) ,  pr = 掩码(Δ)
```

L12 的额外分支（`src/L12_canonical/mod.rs:661-682`）：期望类型若是 trait Sum，
**不**加 pruning 直接放 `Tm::Meta`；L10 同一处**先**试 `solve_trait`
（`src/L10_typeclass/mod.rs:570-587`）：

```rust
    fn fresh_meta(&mut self, cxt: &Cxt, a: Rc<VTy>) -> Rc<Tm> {
        // 期望类型可能被精化 σ 包裹：先推开，实例合成 / trait 判形才看得到
        // 真实形态（对齐旧 refresh 后槽值已展开的世界）
        let a = self.force(&a);
        if let Ok(Some((a, _))) = self.solve_trait(cxt, &a) {
            a
        } else if let Val::Sum(_, _, _, true) = a.as_ref() {
            let m = self.new_meta(a);
            Tm::Meta(MetaVar(m)).into()
        } else {
            ...
            let m = self.new_meta(closed);
            Tm::AppPruning(Tm::Meta(MetaVar(m)).into(), cxt.pruning.clone()).into()
        }
    }
```

> **注意**（`src/L10_typeclass/README.md:30-32` 与 `docs/opt-typeclass.md:91-93`）：
> 这条"急切 `solve_trait`"被文档列为待优化项（问题 5），但**当前行为就是
> 急切求解**，形式化时不能省。

**L04 的 `fresh_meta` 形态**（无类型，`src/L04_implicit/mod.rs:162-167`）与
L03 同构，只是 `bds` 的 `Defined`/`Bound` 都按 `Expl` 应用（见下 §3）。

### 1.4 `force`

`force` 只展开**头构造器**，不下钻子值（`src/L03_holes/mod.rs:245-259`）：

```rust
    /// **force**：把值更新到 metacontext 的当前状态（只展开到下一个不可再
    /// 解阻塞的头构造器，不下钻子值——模式匹配只需要头构造器，深展开会
    /// 重复做功）。unify/quote/rename 一律先 force 再分派。
    fn force(&self, t: &Val) -> Val {
        match t {
            Val::Flex(m, sp) => match self.lookup_meta(*m) {
                MetaEntry::Solved(t_solved) => {
                    let v = self.v_app_sp(t_solved, sp);
                    self.force(&v)
                }
                MetaEntry::Unsolved => Val::Flex(*m, sp.clone()),
            },
            _ => t.clone(),
        }
    }
```

**规则**：`force (?m sp)` = 若 `?m := v` 则 `force (v sp)`，否则 `?m sp`；
其余值原样。这是**唯一的"读 metacontext"入口**——`unify`/`quote`/`rename`
进入时都必须先 `force`（`src/L03_holes/mod.rs:246-247`）。

L10/L12 的 `force` 多了两条（`src/L10_typeclass/mod.rs:591-609`、
`src/L12_canonical/mod.rs:686-710`）：`VSub(v, σ)` 走 `frcs`（把显式替换 σ
推进值的结构）；L12 另有 `Obj`/`Call` 臂。**展开烧 1 fuel**，池空则停止
展开按未解处理（防止解链成环无限递归，`src/L12_canonical/mod.rs:690-691`）。

### 1.5 求解 `?m spine ≡ rhs`：invert / rename / occurs / lams

#### 1.5.1 求解方程与解的形状

L03（`src/L03_holes/mod.rs:391-398`）：

```rust
    /// `Γ ⊢ ?m spine ≡ rhs` 的求解：`?m := λ spine⁻¹. rhs[spine⁻¹]`。
    fn solve(&mut self, gamma: Lvl, m: MetaVar, sp: &Spine, rhs: &Val) -> Result<(), UnifyError> {
        let pren = self.invert(gamma, sp)?;
        let rhs = self.rename(m, &pren, rhs)?;
        let solution = self.eval(&List::new(), &self.lams(pren.dom, rhs));
        self.metas[m.0 as usize] = MetaEntry::Solved(solution);
        Ok(())
    }
```

**解的形状**（这就是要形式化的对象）：

```
?m := eval [] (lams_{dom} (rename_{occ=?m} rhs))
```

即：**解是一个空环境下的闭值**，形如 `λ x1 … xn. t`，`n = dom`（= spine 中
互异 rigid 变量的个数）。`lams` 按解域大小包 λ（`src/L03_holes/mod.rs:297-308`）：

```rust
    /// `λ x1 x2. … body`：按解域大小包 λ（名字 x1、x2、…，只服务 pretty）。
    fn lams(&self, l: Lvl, t: Tm) -> Tm {
        fn go(x: u32, l: Lvl, t: Tm) -> Tm {
            if x == l.0 {
                t
            } else {
                let var_name = format!("x{}", x + 1);
                Tm::Lam(empty_span(var_name.into()), Box::new(go(x + 1, l, t)))
            }
        }
        go(0, l, t)
    }
```

L05 的 `lams` **从 meta 类型取 Π 层与 icit**（`src/L05_pruning/mod.rs:841-862`）：

```rust
    /// `lams l a t`：沿 meta 类型 `a` 的 Π 层包 `l` 个 λ——binder 名与 icit
    /// 取自 Π（`"_"` 改名 `x{l'}`，0 起）；逐层用新的 `VVar l'` 剥闭包。
```

L04 的 `lams` **从 spine 取 icit**（`src/L04_implicit/mod.rs:400-411`，
注释自陈与上游同款"历史 TODO"）：

```rust
        // spine 头 = 最后应用的实参；反转成应用序——最外层 λ 取最先应用
        // 槽位的 icit（上游 `lams (reverse $ map snd sp)` 同款）
        let mut icits: Vec<Icit> = sp.iter().map(|(_, i)| *i).collect();
        icits.reverse();
```

#### 1.5.2 `invert`：spine → partial renaming

L03（`src/L03_holes/mod.rs:310-335`）：

```rust
    /// 把 spine 反演成 partial renaming（Γ 变量 → 解域位置）。spine 必须
    /// 由**互不相同的** rigid 变量构成，否则非模式问题，报 `UnifyError`。
    fn invert_go(&self, sp: &Spine) -> Result<(Lvl, HashMap<u32, Lvl>), UnifyError> {
        match sp.head() {
            None => Ok((Lvl(0), HashMap::new())),
            Some(t) => {
                let (dom, mut ren) = self.invert_go(&sp.tail())?;
                match self.force(t) {
                    Val::Rigid(x, sp2) if sp2.is_empty() && !ren.contains_key(&x.0) => {
                        ren.insert(x.0, dom);
                        Ok((dom + 1, ren))
                    }
                    _ => Err(UnifyError),
                }
            }
        }
    }
```

**这就是"spine 必须是变量"的失败点**。仓内没有字面串 `spine is not a
variable`（已全仓 grep 确认）；等价失败臂是：

- `src/L03_holes/mod.rs:322` — `_ => Err(UnifyError)`，上方注释
  `src/L03_holes/mod.rs:310-311`：「spine 必须由**互不相同的** rigid 变量
  构成，否则非模式问题，报 `UnifyError`」。
- `src/L05_pruning/mod.rs:626` — `_ => Err(UnifyError), // 非变量实参（含带 spine 的变量）`。
- `src/L12_canonical/unification.rs:82-83`（`Stuck` 而非 `Basic`，
  且上游的 Flex 臂被注释掉）：

```rust
                    //Val::Flex(_, _) => Err(UnifyError::Stuck),
                    _ => Err(UnifyError::Stuck),
```

**L05 的 `invert` 记非线性并顺带**产出掩码**（`src/L05_pruning/mod.rs:599-659`）：

```rust
    /// `invert` 的核：spine 必须是**纯变量**（icit 不参与）。返回
    /// (dom, ren, nlvars, fsp)：`nlvars` 记非线性（重复）变量，`fsp` 是
    /// 应用序的 (lvl, icit) 收集（头 = 最内层）。
    fn invert_go(
        &self,
        sp: &Spine,
    ) -> Result<(Lvl, HashMap<u32, Lvl>, HashSet<u32>, List<(Lvl, Icit)>), UnifyError> {
        match sp.head() {
            None => Ok((Lvl(0), HashMap::new(), HashSet::new(), List::new())),
            Some((t, i)) => {
                let (dom, mut ren, mut nlvars, fsp) = self.invert_go(&sp.tail())?;
                match self.force(t) {
                    Val::Rigid(x, sp2) if sp2.is_empty() => {
                        if ren.contains_key(&x.0) || nlvars.contains(&x.0) {
                            // 重复出现：移出 renaming、记入非线性集
                            ren.remove(&x.0);
                            nlvars.insert(x.0);
                        } else {
                            ren.insert(x.0, dom);
                        }
                        Ok((dom + 1, ren, nlvars, fsp.prepend((x, *i))))
                    }
                    _ => Err(UnifyError), // 非变量实参（含带 spine 的变量）
                }
            }
        }
    }
```

非线性时产出「**把重复变量的全部出现剪掉**」的掩码（`src/L05_pruning/mod.rs:632-659`）：

```rust
    /// invert：若 spine 非线性（有重复变量），产出把**重复变量的全部出现**
    /// 记为 `None` 的掩码（solve 前用它检查剪枝可行性）。
    fn invert(
        &self,
        gamma: Lvl,
        sp: &Spine,
    ) -> Result<(PartialRenaming, Option<Pruning>), UnifyError> {
        let (dom, ren, nlvars, fsp) = self.invert_go(sp)?;
        Ok((
            PartialRenaming { occ: None, dom, cod: gamma, ren },
            if nlvars.is_empty() {
                None
            } else {
                Some(fsp.map(|(x, i)| {
                    if nlvars.contains(&x.0) { None } else { Some(*i) }
                }))
            },
        ))
    }
```

`PartialRenaming`（`src/L05_pruning/mod.rs:332-340`，比 L03 多一个 `occ`）：

```rust
/// partial renaming：`ren` 把 Γ 变量映射到解域位置；`occ` 是 occurs check
/// 目标（rename rhs 时挂上被解 meta；prune_ty 里是 `None`）。
#[derive(Debug, Clone)]
struct PartialRenaming {
    occ: Option<MetaVar>,
    dom: Lvl,               // size of Γ（解体所在的域 = spine 长度 + lift）
    cod: Lvl,               // size of Δ（rhs 所在的域）
    ren: HashMap<u32, Lvl>, // mapping from Δ vars to Γ vars
}
```

两个推进算子（`src/L05_pruning/mod.rs:342-362`）——**`lift` 与 `skip` 的区别
就是"保留槽位 vs 剪除槽位"**：

```rust
/// Lifting over an extra bound variable（Γ、Δ 各深一层，binder 进映射）。
fn lift(pren: &PartialRenaming) -> PartialRenaming {
    let mut ren = pren.ren.clone();
    ren.insert(pren.cod.0, pren.dom);
    PartialRenaming { occ: pren.occ, dom: pren.dom + 1, cod: pren.cod + 1, ren }
}

/// Skipping a bound variable（Δ 深一层但**不进**映射：被剪的槽位越界）。
fn skip(pren: &PartialRenaming) -> PartialRenaming {
    PartialRenaming { occ: pren.occ, dom: pren.dom, cod: pren.cod + 1, ren: pren.ren.clone() }
}
```

#### 1.5.3 `rename` / `rename_go`：occurs check + scope check

L03（`src/L03_holes/mod.rs:337-389`）——**occurs check 与 scope check 在同一
个遍历里**：

```rust
    fn rename_go(&self, m: MetaVar, pren: &PartialRenaming, v: &Val) -> Result<Tm, UnifyError> {
        let v = self.force(v);
        match v {
            // occurs check
            Val::Flex(m_prime, sp) if m == m_prime => Err(UnifyError),
            Val::Flex(m_prime, sp) => self.rename_go_sp(m, pren, Tm::Meta(m_prime), &sp),
            Val::Rigid(x, sp) => match pren.ren.get(&x.0) {
                // scope error（"escaping variable"）
                None => Err(UnifyError),
                Some(x_prime) => {
                    let t = Tm::Var(lvl2ix(pren.dom, *x_prime));
                    self.rename_go_sp(m, pren, t, &sp)
                }
            },
            Val::Lam(x, clo) => {
                let t = self.rename_go(
                    m, &lift(pren),
                    &self.closure_apply(&clo, Val::vvar(pren.cod)),
                )?;
                Ok(Tm::Lam(x, Box::new(t)))
            }
            Val::Pi(x, a, b) => { /* a 用 pren，b 用 lift(pren) */ }
            Val::U => Ok(Tm::U),
        }
    }
```

**规则**（L03/L04）：
- `?m' sp`（同号）→ **occurs check 失败**；
- `?m' sp`（异号）→ 改写成 `Meta(m')` 后递归 spine；
- `Rigid(x, sp)` 且 `x ∉ ren` → **scope error**（"escaping variable"）；
- `Rigid(x, sp)` 且 `x ∈ ren` → `Var(lvl2ix(dom, ren x))` 后递归 spine；
- `Lam`/`Pi` 体用 `lift(pren)`，实例化用 `vvar(pren.cod)`。

**L05 的 `rename` 是 `&mut self`，且 flex 分支改为 `pruneVFlex`**（可能剪枝）
（`src/L05_pruning/mod.rs:810-839`）：

```rust
    /// 对 rhs 执行 partial renaming，同时做 occurs check 与 scope check；
    /// flex spine 走 `pruneVFlex`（可能剪枝）。
    fn rename(&mut self, pren: &PartialRenaming, v: &Val) -> Result<Tm, UnifyError> {
        let v = self.force(v);
        match v {
            Val::Flex(m_prime, sp) => match pren.occ {
                Some(m) if m == m_prime => Err(UnifyError), // occurs check
                _ => self.prune_vflex(pren, m_prime, &sp),
            },
            Val::Rigid(x, sp) => match pren.ren.get(&x.0) {
                None => Err(UnifyError), // scope error（"escaping variable"）
                Some(x_prime) => {
                    let t = Tm::Var(lvl2ix(pren.dom, *x_prime));
                    self.rename_sp(pren, t, &sp)
                }
            },
            ...
        }
    }
```

### 1.6 pruning 掩码（L05）：计算、求逆、`prune_ty`、`prune_meta`、`prune_vflex`

#### 1.6.1 掩码的两种来源

1. **`invert` 的非线性掩码**（§1.5.2）：重复变量 → 全部出现记 `None`。
2. **`prune_vflex` 的越界变量掩码**（见下）。

在 `solve` 里，非线性掩码先被用来**验证剪枝可行性**，再求解
（`src/L05_pruning/mod.rs:864-898`）：

```rust
    /// `Γ ⊢ ?m spine ≡ rhs` 的求解（非线性时先验证剪枝可行性）。
    fn solve(&mut self, gamma: Lvl, m: MetaVar, sp: &Spine, rhs: &Val) -> Result<(), UnifyError> {
        let (pren, prune_non_linear) = self.invert(gamma, sp)?;
        self.solve_with_pren(m, pren, prune_non_linear, rhs)
    }

    fn solve_with_pren(
        &mut self,
        m: MetaVar,
        pren: PartialRenaming,
        prune_non_linear: Option<Pruning>,
        rhs: &Val,
    ) -> Result<(), UnifyError> {
        let mty = match &self.lookup_meta(m) {
            MetaEntry::Unsolved(a) => a.clone(),
            _ => unreachable!(),
        };

        // 非线性 spine：先检查非线性的变量槽位可以从 meta 类型里剪掉
        // （剪完仍良型才允许求解）。
        if let Some(pr) = prune_non_linear {
            self.prune_ty(&pr, mty.clone())?;
        }

        let rhs = self.rename(
            &PartialRenaming { occ: Some(m), ..pren },
            rhs,
        )?;
        let solution = self.eval(&List::new(), &self.lams(pren.dom, &mty, rhs));
        self.meta[m.0 as usize] = MetaEntry::Solved(solution, mty);
        Ok(())
    }
```

#### 1.6.2 `prune_ty`：掩码 ↔ Π 层的配对（**必须外→内**）

`src/L05_pruning/mod.rs:661-700`：

```rust
    /// 上游 `pruneTy (revPruning pr) a`：掩码**外→内**配对 Π 层：
    /// `Some` 层保留（定义域过 renaming，进 lift），`None` 层整个删掉
    /// （进 skip）；掩码耗尽后剩余类型过 renaming。
    fn prune_ty(&mut self, pr: &Pruning, a: Val) -> Result<Tm, UnifyError> {
        // revPruning：头 = 最外层（与 Π 剥层同序）
        let mut rev: Vec<Option<Icit>> = pr.iter().copied().collect();
        rev.reverse();
        self.prune_ty_go(
            &rev,
            &PartialRenaming { occ: None, dom: Lvl(0), cod: Lvl(0), ren: HashMap::new() },
            a,
        )
    }

    fn prune_ty_go(
        &mut self,
        rev: &[Option<Icit>],
        pren: &PartialRenaming,
        a: Val,
    ) -> Result<Tm, UnifyError> {
        match (rev.split_first(), self.force(&a)) {
            (None, a) => self.rename(pren, &a),
            (Some((Some(_), rest)), Val::Pi(x, i, a, b)) => {
                let a_tm = self.rename(pren, &a)?;
                let b_v = self.closure_apply(&b, Val::vvar(pren.cod));
                let b_tm = self.prune_ty_go(rest, &lift(pren), b_v)?;
                Ok(Tm::Pi(x, i, Box::new(a_tm), Box::new(b_tm)))
            }
            (Some((None, rest)), Val::Pi(_, _, _, b)) => {
                let b_v = self.closure_apply(&b, Val::vvar(pren.cod));
                self.prune_ty_go(rest, &skip(pren), b_v)
            }
            _ => Err(UnifyError), // impossible：掩码与类型结构不匹配
        }
    }
```

> `readme.md:20-26` 记录了两处历史错位 bug：掩码方向（旧版内→外）与
> `pruneVFlex` 的折叠方向。形式化时必须钉死：**掩码按"内先序"存储
> （头 = 最内层），`prune_ty` 入口 `reverse` 成"外先序"再与 Π 剥层
> 同序配对**。

#### 1.6.3 `prune_meta`：造新 meta + 旧 meta 解为「λ 掩码应用」

`src/L05_pruning/mod.rs:702-720`：

```rust
    /// `pruneMeta`：按掩码剪掉 meta 的实参——检查剪后类型良型、造新 meta、
    /// 旧 meta 解为 `λ telescope. AppPruning ?m' pruned`。
    fn prune_meta(&mut self, pruning: Pruning, m: MetaVar) -> Result<MetaVar, UnifyError> {
        let mty = match &self.lookup_meta(m) {
            MetaEntry::Unsolved(a) => a.clone(),
            _ => unreachable!(), // 只对未解 meta 剪枝
        };
        let pruned_tm = self.prune_ty(&pruning, mty.clone())?;
        let prunedty = self.eval(&List::new(), &pruned_tm);
        let m_prime = self.new_meta(prunedty);
        let solution_tm = self.lams(
            Lvl(pruning.len() as u32),
            &mty.clone(),
            Tm::AppPruning(Box::new(Tm::Meta(m_prime)), pruning),
        );
        let solution = self.eval(&List::new(), &solution_tm);
        self.meta[m.0 as usize] = MetaEntry::Solved(solution, mty);
        Ok(m_prime)
    }
```

**规则**：`pruneMeta pr ?m` 先 `prune_ty pr mty`（失败即整体失败），造
`?m' : prunedty`，然后 `?m := λ^{|pr|}. ?m' pr`。返回 `?m'` 供调用方继续。

#### 1.6.4 `prune_vflex`：rename 的 flex 分支

状态机（`src/L05_pruning/mod.rs:364-373`）：

```rust
/// `pruneVFlex` 的 spine 状态（上游 SpinePruneStatus）。
#[derive(Debug, Clone, Copy, PartialEq)]
enum SpinePruneStatus {
    /// 合法 spine 且是 renaming（全是互不相同的变量）。
    OKRenaming,
    /// 合法 spine 但不是 renaming（含非变量实参）。
    OKNonRenaming,
    /// 是 renaming 但含越界变量槽位——需要剪枝。
    NeedsPruning,
}
```

核（`src/L05_pruning/mod.rs:722-756`）与重建（`:758-792`）：

```rust
    fn prune_vflex_go(
        &mut self,
        pren: &PartialRenaming,
        sp: &Spine,
    ) -> Result<(List<(Option<Tm>, Icit)>, SpinePruneStatus), UnifyError> {
        match sp.head() {
            None => Ok((List::new(), SpinePruneStatus::OKRenaming)),
            Some((t, i)) => {
                let (sp_rest, status) = self.prune_vflex_go(pren, &sp.tail())?;
                match self.force(t) {
                    Val::Rigid(x, sp2) if sp2.is_empty() => match (pren.ren.get(&x.0), status) {
                        (Some(xp), _) => Ok((
                            sp_rest.prepend((Some(Tm::Var(lvl2ix(pren.dom, *xp))), *i)),
                            status,
                        )),
                        (None, SpinePruneStatus::OKNonRenaming) => Err(UnifyError),
                        (None, _) => Ok((sp_rest.prepend((None, *i)), SpinePruneStatus::NeedsPruning)),
                    },
                    t => match status {
                        SpinePruneStatus::NeedsPruning => Err(UnifyError),
                        _ => {
                            let t = self.rename(pren, &t)?;
                            Ok((sp_rest.prepend((Some(t), *i)), SpinePruneStatus::OKNonRenaming))
                        }
                    },
                }
            }
        }
    }

    /// rename 的 flex 分支：可能触发剪枝的 meta+spine 重建。
    fn prune_vflex(
        &mut self,
        pren: &PartialRenaming,
        m: MetaVar,
        sp: &Spine,
    ) -> Result<Tm, UnifyError> {
        let (sp, status) = self.prune_vflex_go(pren, sp)?;

        let m_prime = match status {
            SpinePruneStatus::NeedsPruning => {
                // 掩码 = 保留槽位的 icit（剪除槽位 → None）；只对未解 meta
                self.prune_meta(sp.map(|(mt, i)| mt.as_ref().map(|_| *i)), m)?
            }
            _ => {
                match self.lookup_meta(m) {
                    MetaEntry::Unsolved(_) => m,
                    _ => unreachable!(), // force 已保证未解
                }
            }
        };

        // 上游 `foldr (\(mu, i) t -> maybe t (\u -> App t u i) mu) (Meta m') sp`：
        // foldr 从尾（最外层）起 = 最外层实参先应用（修正旧移植 `iter().fold`
        // 从内层起导致的倒序）。
        let mut slots: Vec<(Option<Tm>, Icit)> = sp.iter().cloned().collect();
        slots.reverse();
        let mut t = Tm::Meta(m_prime);
        for (mu, i) in slots {
            if let Some(u) = mu {
                t = Tm::App(Box::new(t), Box::new(u), i);
            }
        }
        Ok(t)
    }
```

**状态机规则**（形式化时最易错的部分）：
- 状态是「整条 spine 的一个下界」：`OKRenaming < OKNonRenaming < NeedsPruning`
  在"单调上升"意义上使用；一旦某槽位判 `NeedsPruning`，**之后（更外层）
  再出现非变量实参即失败**（`:743-744`）。
- 一旦出现非变量实参（`OKNonRenaming`），**之后（更外层）再出现越界变量
  即失败**（`:740`）。
- 最终 `NeedsPruning` → 掩码 = 「保留槽位 = `Some(icit)`，剪除槽位 =
  `None`」，调 `prune_meta`；重建时**最外层实参先应用**。

### 1.7 `SpecSolve`（"specialize solve"，L10/L12 特化合一）

L03–L05 **没有** `SpecSolve`。它随模式精化的「显式替换（dpm-nbe）」重构
进入 L10/L12：`unify_pm` 不再改写上下文，而是把解累积进 `spec.acc`。

定义（`src/L12_canonical/elaboration.rs:18-25`；L10 同构
`src/L10_typeclass/elaboration.rs:21`）：

```rust
/// 特化合一的进行时状态（dpm-nbe `unifyS` 的 ɑ-accumulation 的 Rust 形态）：
/// `acc` = 已解出的替换——编译器的 σ（嵌套 match 时）作种子，方程途中叠加，
/// 调用方在方程结束后取走 `acc` 作为新 σ。L12 的可解集 = **任意裸 Rigid**
/// （旧 `update_cxt` 对任何裸 rigid 都改写槽位，没有 L07 的 bind-slot 白名单），
/// 故这里没有 `solvable` 字段——臂条件 `sp.is_empty()` 即全部约束。
pub(crate) struct SpecSolve {
    pub(crate) acc: Rc<Subst>,
}
```

可解臂与 occurs 守卫（`src/L12_canonical/elaboration.rs:140-172`）：

```rust
        match (t.as_ref(), t_prime.as_ref()) {
            (Val::Rigid(x1, sp1), Val::Rigid(x2, sp2))
                if sp1.is_empty() && sp2.is_empty() && x1 == x2 => { Ok(()) }
            // 单侧裸 Rigid：解入 acc。Flex 解值保持旧 `update_cxt` 的 no-op
            // （那时对 Flex 直接 clone、不改写槽）；occurs 环守卫只扫解值
            // 自身结构（Flex 头不透明），失败 = 方程不可满足（分支不可达）。
            (Val::Rigid(x, sp), v) if sp.is_empty() => {
                if matches!(v, Val::Flex(..)) { return Ok(()); }
                if val_mentions_lvl(v, *x) {
                    return Err(Error(t_span.map(|_| "".to_string()), vec![]));
                }
                let v = Rc::new(v.clone());
                spec.acc = Subst::extend(&spec.acc, *x, v);
                Ok(())
            }
            (v, Val::Rigid(x, sp)) if sp.is_empty() => { /* 对称 */ }
            ...
```

**回滚纪律**：`spec.acc` 是 `Rc`（L12）/`Rc` 指针，**臂边界回滚 = 指针赋值**
（`src/L10_typeclass/README.md:211-212`：「臂边界回滚 = Rc 指针赋值」）。
`check_pm_final` 的第二方程也用它做"失败容忍丢弃"
（`src/L12_canonical/elaboration.rs:87-104`）：

```rust
    pub fn check_pm_final(&mut self, cxt: &Cxt, t: Raw, a: Rc<Val>, ori: Rc<Val>) -> Result<(Rc<Tm>, Rc<Subst>), Error> {
        let t_span = t.to_span();
        let x = self.infer_expr(cxt, t);
        let (t_inferred, inferred_type) = self.insert(cxt, x)?;
        let mut spec = SpecSolve { acc: Rc::new(Subst::default()) };
        self.unify_pm(cxt, &a, &inferred_type, t_span, &mut spec)?;
        // 第二方程：把被匹配项的值 `ori` 与精化后的模式项值再对一次
        // （旧 `.unwrap_or(new_cxt)`——失败容忍，丢弃第二次方程的解）。
        let cxt2 = cxt.subst_cxt(&spec.acc);
        let ori_v = self.eval(&cxt2.decl, &cxt2.env, &t_inferred);
        let mut spec2 = SpecSolve { acc: spec.acc.clone() };
        if self.unify_pm(&cxt2, &ori, &ori_v, t_span, &mut spec2).is_ok() {
            spec.acc = spec2.acc;
        }
        Ok((t_inferred, spec.acc))
    }
```

**边界（重要）**：`unify_pm` **只服务模式方程路径**；canonical 搜索与 trait
实例求解走常规 `unify`，**不带 spec**，即实例求解过程中的合一不会获得
特化解能力（`src/L12_canonical/elaboration.rs:118-123`、
`src/L10_typeclass/README.md:223-225`）。

### 1.8 fuel 与回滚纪律

| 层 | fuel | 回滚 |
|---|---|---|
| L03/L04/L05 | **无** | 无需回滚：求解只发生在比较成功路径，工作表是纯合取（`src/L03_holes/readme.md:233-235`） |
| L10 | `UNIFY_FUEL = 4096`，`burn_fuel`/`refuel`（`src/L10_typeclass/mod.rs:450`、`:548-559`） | 同上；`meta_contrains` 已存在（Stuck 挂账） |
| L12 | 同上（`src/L12_canonical/mod.rs:602-656`） | `meta_contrains`（Stuck 挂账）+ `no_metas` 判定 + `iddfs` 候选之间 `meta_contrains.clear()` |

L12 的 fuel 纪律（`src/L12_canonical/mod.rs:637-649`）：

```rust
    /// 烧 1 格 fuel；池空返回 `false`（调用方按各自失败语义降级）。
    fn burn_fuel(&self) -> bool {
        let f = self.unify_fuel.get();
        if f == 0 { return false; }
        self.unify_fuel.set(f - 1);
        true
    }
    /// 外层入口充值（L08 `meta_refuel` 同款纪律）。
    fn refuel(&self) {
        self.unify_fuel.set(UNIFY_FUEL);
    }
```

消耗点：`force` 的 meta 展开（`src/L12_canonical/mod.rs:692`）与 `unify` 的
每次递归入口（`src/L12_canonical/unification.rs:665-667`）：

```rust
        // 递归深度防护（L08 前向传播，与 `fuel` 参数互补）：fuel 耗尽按
        // 不可合一失败
        if !self.burn_fuel() {
            return Err(UnifyError::Basic);
        }
```

耗尽语义：**`unify` 按不可合一失败；`force` 停止展开、把已解 meta 当未解
返回**（`src/L12_canonical/mod.rs:617-619`）。后者留下一个"窗口"：已解 meta
被当成未解后可能走到求解臂，L12 显式降级处理
（`src/L12_canonical/unification.rs:454-459`）：

```rust
        let mty = match self.meta[m.0 as usize] {
            MetaEntry::Unsolved(ref a, _, _) => a.clone(),
            // fuel 耗尽窗口（同 prune_meta 注）：已解 meta 被 force 当未解
            // 返回后走到求解臂，按合一失败降级而不是 panic
            _ => return Err(UnifyError::Basic),
        };
```

**`UnifyError` 的层次**（`src/L12_canonical/mod.rs:566-571`）：

```rust
pub enum UnifyError {
    Basic,
    Stuck,
    Trait(String),
}
```

- `Basic` = 刚性失配 / occurs / scope / 非模式 spine（L03–L05 只有这一种）。
- `Stuck` = 「方程不可判定」（L12 的 `invert` 非变量实参、spine 含未解
  flex 被当实参）。`unify` 的 flex 臂把 `Stuck` **挂账** `meta_contrains`
  并返回 `Ok`（见 §2.6）。
- `Trait(String)` = 实例求解失败，携带已格式化的错误消息
  （`src/L10_typeclass/unification.rs:457-458`、`src/L12_canonical/mod.rs:1228`）。

---

## 2. 元变量合一 `unify`

### 2.1 L03：最小内核（无 pruning、无 fuel）

`src/L03_holes/mod.rs:411-455`（**完整调度，逐字**）：

```rust
    /// unification：结构比较，遇到 `?m spine =? rhs` 形态的方程则求解。
    /// 分派次序与 Main.hs 一致（λ 情形 → U → Π → 同头中性 → 求解）。
    fn unify(&mut self, l: Lvl, t: &Val, u: &Val) -> Result<(), UnifyError> {
        let t = self.force(t);
        let u = self.force(u);
        match (&t, &u) {
            (Val::Lam(_, t_clo), Val::Lam(_, u_clo)) => self.unify(
                l + 1,
                &self.closure_apply(t_clo, Val::vvar(l)),
                &self.closure_apply(u_clo, Val::vvar(l)),
            ),
            (_, Val::Lam(_, u_clo)) => {
                let t2 = self.v_app(&t, Val::vvar(l));
                self.unify(l + 1, &t2, &self.closure_apply(u_clo, Val::vvar(l)))
            }
            (Val::Lam(_, t_clo), _) => {
                let u2 = self.v_app(&u, Val::vvar(l));
                self.unify(l + 1, &self.closure_apply(t_clo, Val::vvar(l)), &u2)
            }

            (Val::U, Val::U) => Ok(()),

            (Val::Pi(_, a, b), Val::Pi(_, a_prime, b_prime)) => {
                self.unify(l, a, a_prime)?;
                self.unify(
                    l + 1,
                    &self.closure_apply(b, Val::vvar(l)),
                    &self.closure_apply(b_prime, Val::vvar(l)),
                )
            }

            (Val::Rigid(x, sp), Val::Rigid(x_prime, sp_prime)) if x == x_prime => {
                self.unify_sp(l, sp, sp_prime)
            }

            (Val::Flex(m, sp), Val::Flex(m_prime, sp_prime)) if m == m_prime => {
                self.unify_sp(l, sp, sp_prime)
            }

            (Val::Flex(m, sp), _) => self.solve(l, *m, sp, &u),
            (_, Val::Flex(m_prime, sp_prime)) => self.solve(l, *m_prime, sp_prime, &t),

            _ => Err(UnifyError), // rigid 失配
        }
    }
```

**逐例规则**（L03/L04 版，`l` 是当前层级 = 上下文长度）：

| # | `t` | `u` | 动作 |
|---|---|---|---|
| 1 | `Lam t'` | `Lam u'` | `unify (l+1) (t' vvar l) (u' vvar l)` |
| 2 | 任意 | `Lam u'` | **η**：`unify (l+1) (t vvar l) (u' vvar l)` |
| 3 | `Lam t'` | 任意 | **η**：`unify (l+1) (t' vvar l) (u vvar l)` |
| 4 | `U` | `U` | `Ok` |
| 5 | `Pi a b` | `Pi a' b'` | `unify l a a'` 且 `unify (l+1) (b vvar l) (b' vvar l)` |
| 6 | `Rigid x sp` | `Rigid x sp'`（`x` 相同） | `unify_sp` |
| 7 | `Flex m sp` | `Flex m sp'`（`m` 相同） | `unify_sp`（**同号 flex-flex 逐实参比较**） |
| 8 | `Flex m sp` | 任意 `u` | **求解** `solve l m sp u` |
| 9 | 任意 `t` | `Flex m sp` | **求解** `solve l m sp t` |
| 10 | 其它 | 其它 | `Err(UnifyError)` |

> 注意 L03/L04 **没有独立的异头 flex-flex 臂**：`(Flex m sp, Flex m' sp')` 且
> `m ≠ m'` 会落到第 8 例（解左侧）。L04 的 readme 明说：`(2,2)` 同号
> flex-flex 走逐实参比较，因为「solve 的 occurs check 对同号必败」
> （`src/L04_implicit/readme.md` 对应 L03 `readme.md:229-233`）。

### 2.2 L04：加 icit 相等与 η 守卫

`src/L04_implicit/mod.rs:425-470` 的差异只有三处（其余同 L03）：

```rust
            // η：按 λ 一侧的 icit 应用中性一侧（守卫见 `v_applicable`）
            (_, Val::Lam(_, i, u_clo)) if v_applicable(&t) => {
                let t2 = self.v_app(&t, Val::vvar(l), *i);
                self.unify(l + 1, &t2, &self.closure_apply(u_clo, Val::vvar(l)))
            }
            ...
            (Val::Pi(_, i, a, b), Val::Pi(_, i_prime, a_prime, b_prime)) if i == i_prime => {
                ...
            }

            (Val::Rigid(x, sp), Val::Rigid(x_prime, sp_prime)) if x == x_prime => {
                self.unify_sp(l, sp, sp_prime)
            }
            (Val::Flex(m, sp), Val::Flex(m_prime, sp_prime)) if m == m_prime => {
                self.unify_sp(l, sp, sp_prime)
            }
```

1. **Π 比较要求 `i == i_prime`**，否则落到 `_ => Err(UnifyError), // rigid 失配 / Pi icit 失配`（`src/L04_implicit/mod.rs:468`）。
2. **η 有可应用性守卫** `v_applicable`（`src/L04_implicit/mod.rs:134-142`）：

```rust
/// η 展开的可应用性守卫（L06 `unification::v_applicable` 同款）：只有中性值
/// （Flex/Rigid）能吃 η 新变量。L04 无 decl/builtin，无法制造"λ 值当类型"
/// 的种子，故 η 臂的 Pi/U 分支本层不可达；补守卫后该分支由 `v_app` 的
/// impossible panic（`mod.rs:182`）变为普通 unify 失败（Err）。
fn v_applicable(v: &Val) -> bool {
    matches!(v, Val::Flex(_, _) | Val::Rigid(_, _))
}
```

3. **spine 实参比较忽略 icit**（`src/L04_implicit/mod.rs:413-423`）：

```rust
    /// 同头中性的逐实参比较（icit 不比：类型已定，上游同款）。
    fn unify_sp(&mut self, l: Lvl, sp: &Spine, sp_prime: &Spine) -> Result<(), UnifyError> {
        match (sp.head(), sp_prime.head()) {
            (None, None) => Ok(()),
            (Some(_), Some(_)) => {
                self.unify_sp(l, &sp.tail(), &sp_prime.tail())?;
                self.unify(l, &sp.head().unwrap().0, &sp_prime.head().unwrap().0)
            }
            _ => Err(UnifyError), // spine 长度不等
        }
    }
```

### 2.3 L05：pruning 版调度

`src/L05_pruning/mod.rs:983-1026`（**完整调度，逐字**）：

```rust
    /// unification：结构比较 + 模式求解，分派与上游 Unification.hs 逐项
    /// 对应（U → Π（icit 相等）→ 同头 rigid → 同头 flex = intersect →
    /// 异头 flex = flexFlex → λ/η → 求解）。
    fn unify(&mut self, l: Lvl, t: &Val, u: &Val) -> Result<(), UnifyError> {
        let t = self.force(t);
        let u = self.force(u);
        match (&t, &u) {
            (Val::U, Val::U) => Ok(()),
            (Val::Pi(_, i, a, b), Val::Pi(_, i_prime, a_prime, b_prime)) if i == i_prime => {
                self.unify(l, a, a_prime)?;
                self.unify(
                    l + 1,
                    &self.closure_apply(b, Val::vvar(l)),
                    &self.closure_apply(b_prime, Val::vvar(l)),
                )
            }
            (Val::Rigid(x, sp), Val::Rigid(x_prime, sp_prime)) if x == x_prime => {
                self.unify_sp(l, sp, sp_prime)
            }
            (Val::Flex(m, sp), Val::Flex(m_prime, sp_prime)) if m == m_prime => {
                self.intersect(l, *m, sp, sp_prime)
            }
            (Val::Flex(m, sp), Val::Flex(m_prime, sp_prime)) => {
                self.flex_flex(l, *m, sp, *m_prime, sp_prime)
            }
            (Val::Lam(_, _, t_clo), Val::Lam(_, _, u_clo)) => self.unify(
                l + 1,
                &self.closure_apply(t_clo, Val::vvar(l)),
                &self.closure_apply(u_clo, Val::vvar(l)),
            ),
            // η：按 λ 一侧的 icit 应用中性一侧（守卫见 `v_applicable`）
            (_, Val::Lam(_, i, u_clo)) if v_applicable(&t) => {
                let t2 = self.v_app(&t, Val::vvar(l), *i);
                self.unify(l + 1, &t2, &self.closure_apply(u_clo, Val::vvar(l)))
            }
            (Val::Lam(_, i, t_clo), _) if v_applicable(&u) => {
                let u2 = self.v_app(&u, Val::vvar(l), *i);
                self.unify(l + 1, &self.closure_apply(t_clo, Val::vvar(l)), &u2)
            }
            (Val::Flex(m, sp), _) => self.solve(l, *m, sp, &u),
            (_, Val::Flex(m_prime, sp_prime)) => self.solve(l, *m_prime, sp_prime, &t),
            _ => Err(UnifyError), // rigid 失配 / Pi icit 失配
        }
    }
```

**相对 L03/L04 的两条新增**：同号 flex-flex 走 `intersect`（取交 + 剪枝），
异头 flex-flex 走 `flex_flex`（较长 spine 一侧优先反演）。

`flex_flex`（`src/L05_pruning/mod.rs:912-940`）：

```rust
    /// 异头 flex-flex：较长 spine 一侧优先反演（解内层 meta 少剪枝）；
    /// 反演失败则用另一侧求解。
    fn flex_flex(&mut self, gamma, m, sp, m_prime, sp_prime) -> Result<(), UnifyError> {
        let mut go = |m, sp, m_prime, sp_prime| -> Result<(), UnifyError> {
            match self.invert(gamma, sp) {
                Err(UnifyError) => self.solve(gamma, m_prime, sp_prime, &Val::Flex(m, sp.clone())),
                Ok((pren, p1)) => {
                    self.solve_with_pren(m, pren, p1, &Val::Flex(m_prime, sp_prime.clone()))
                }
            }
        };

        if sp.len() < sp_prime.len() {
            go(m_prime, sp_prime, m, sp)
        } else {
            go(m, sp, m_prime, sp_prime)
        }
    }
```

`intersect`（`src/L05_pruning/mod.rs:942-981`）：

```rust
    /// `intersect` 的核：两 spine 逐槽都是变量时产出「相等槽位 = 其 icit、
    /// 不等槽位 = None」的掩码；含非变量槽位返回 None（回落 unify_sp）。
    /// 长度不等也返回 None（上游 `impossible` 分支——本层落地为 unify_sp
    /// 的长度失配失败，不炸栈，结论同为不可解）。
    fn intersect_go(&self, sp: &Spine, sp_prime: &Spine) -> Option<Pruning> {
        match (sp.head(), sp_prime.head()) {
            (None, None) => Some(List::new()),
            (Some((t, i)), Some((t_prime, _))) => {
                match (self.force(t), self.force(t_prime)) {
                    (Val::Rigid(x, s1), Val::Rigid(x_prime, s2))
                        if s1.is_empty() && s2.is_empty() =>
                    {
                        self.intersect_go(&sp.tail(), &sp_prime.tail())
                            .map(|l| l.prepend(if x == x_prime { Some(*i) } else { None }))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// `?m sp =? ?m sp'`：两 spine 都是变量序列时**取交**——差异槽位从
    /// `?m` 剪掉（`pruneMeta`）；否则回落逐实参比较。
    fn intersect(&mut self, l, m, sp, sp_prime) -> Result<(), UnifyError> {
        match self.intersect_go(sp, sp_prime) {
            None => self.unify_sp(l, sp, sp_prime),
            Some(pr) if pr.iter().any(|x| x.is_none()) => {
                self.prune_meta(pr, m)?;
                Ok(())
            }
            Some(_) => Ok(()),
        }
    }
```

**`intersect` 规则**：`?m sp ≡ ?m sp'` 且两 spine 皆 `Rigid(·, [])` 序列：
逐槽取交，交掩码中 `None` 槽即差异槽 → `prune_meta` 把差异槽从 `?m` 剪掉；
全 `Some` → 直接 `Ok`；含非变量或长度不等 → 回落 `unify_sp` 判失败
（**立即失败、不比较共同前缀**，`src/L05_pruning/readme.md:145-149`）。

### 2.4 L10/L12：加 fuel / Decl / Sum / Match / `solve_multi_trait`

L12 的 `unify`（`src/L12_canonical/unification.rs:662-...`）在 §2.1 的骨架外
加了（**顺序即优先级**）：

1. `if !self.burn_fuel() { return Err(UnifyError::Basic); }`（`:663-667`）
2. `Call` 内联穿透：`(Val::Call(_,_,t_body), _) => unify t_body u`（`:678-679`）
3. `U(x)` / `U(y)` 要求 `x == y`（`:680`）
4. Π：icit 相等 + `unify` 定义域 + `unify` 余定义域，且**余定义域的 quote
   用当前层级 `l` 而不是 `cxt.lvl`**（`:685-690` 长注释解释 η 递归臂下
   `l == cxt.lvl` 的不变式会破）。
5. `Rigid`/`Rigid` 同名 → `unify_sp`；`Decl`/`Decl` 同名 → `unify_sp`；
   `Decl`/非 Decl → `quote`+`eval` 后重试，**该重试受 `fuel` 参数配额**：

```rust
            (Val::Decl(..), _) => {
                if fuel == 0 {
                    Err(UnifyError::Basic)
                } else {
                    self.unify(l, cxt,
                        &self.eval(&cxt.decl, &cxt.env, &self.quote(&cxt.decl, l, &t)),
                        &u, fuel - 1)
                }
            }
```

6. `Flex`/`Flex` 同号 → `intersect`；异号 → `flex_flex`。
7. `Lam`/`Lam`、η（带守卫）、`Flex`/`_` 与 `_`/`Flex` **求解 + Stuck 挂账 +
   `solve_multi_trait`**（见 §2.6）。
8. `LiteralType`/`LiteralType`、`Prim` 透传、`Sum`/`Sum` 同名比参、
   `SumCase`/`SumCase` 同名（**比 Sum 头名 + 逐字段；见 §5 与 L12
   `unify_pm` 注**）、`Match`/`Match`（scrutinee、env 长度、分支体；分支
   体在 `declb` 中性视图下重求值，`src/L12_canonical/unification.rs:786-...`）。

L10 的 `unify` 与 L12 同构（`src/L10_typeclass/unification.rs:508-...`），
但没有 `Decl` 头（L10 用 `global` 大下标 + `Rigid` 表示全局名，
`src/L10_typeclass/README.md:98-105`）。

### 2.5 `unify_catch`：把 `UnifyError` 变成用户错误

L03（`src/L03_holes/mod.rs:590-601`）：

```rust
    fn unify_catch(&mut self, cxt: &Cxt, t: &Val, t_prime: &Val) -> Result<(), Error> {
        self.unify(cxt.lvl, t, t_prime).map_err(|_| {
            Error {
                msg: format!(
                    "Cannot unify expected type\n\n  {}\n\nwith inferred type\n\n  {}",
                    show_tm(cxt, &self.quote(cxt.lvl, t)),
                    show_tm(cxt, &self.quote(cxt.lvl, t_prime)),
                ),
                pos: cxt.pos,
            }
        })
    }
```

L12 的 `unify_catch` 是**唯一的 Stuck 挂账检查点**
（`src/L12_canonical/mod.rs:1203-1245`）：

```rust
    fn unify_catch(&mut self, cxt: &Cxt, t: &Rc<Val>, t_prime: &Rc<Val>, span: Span<()>) -> Result<(), Error> {
        self.meta_contrains.clear();
        self.refuel();
        let ret = self.unify(cxt.lvl, cxt, t, t_prime, 100)
            .map_err(|e| {
                let err = match e {
                    UnifyError::Basic | UnifyError::Stuck => format!(
                        "can't unify\n  expected: {}\n      find: {}",
                        pretty_tm(0, cxt.names(), &self.quote(&cxt.decl, cxt.lvl, t)),
                        pretty_tm(0, cxt.names(), &self.quote(&cxt.decl, cxt.lvl, t_prime)),
                    ),
                    UnifyError::Trait(e) => e,
                };
                Error(span.map(|_| err.clone()), vec![])
            });
        if !self.meta_contrains.is_empty() {
            let err = format!(
                    "can't unify for unsolved meta\n  expected: {}\n      find: {}",
                    pretty_tm(0, cxt.names(), &self.quote(&cxt.decl, cxt.lvl, t)),
                    pretty_tm(0, cxt.names(), &self.quote(&cxt.decl, cxt.lvl, t_prime)),
                );
            self.meta_contrains.clear();
            Err(Error(span.map(|_| err.clone()), vec![]))?
        }
        self.meta_contrains.clear();
        ret
    }
```

### 2.6 失败 / 歧义 / 挂账（Stuck）——**形式化必须建模的三态**

L12 的 flex 求解臂（`src/L12_canonical/unification.rs:743-764`）：

```rust
            (Val::Flex(m, sp), _) => {
                match self.solve(l, &cxt.decl, *m, sp.clone(), &u) {
                    Ok(()) => Ok(()),
                    Err(UnifyError::Stuck) => {
                        self.meta_contrains.push((t.clone(), u.clone()));
                        Ok(())
                    },
                    Err(e) => Err(e),
                }?;
                self.solve_multi_trait(cxt, *m)
            },
            (_, Val::Flex(m, sp)) => { /* 对称 */ },
```

**语义**：`unify` 是**三值**的：

| 结果 | 含义 |
|---|---|
| `Ok(())`，`meta_contrains` 空 | 方程已解 |
| `Ok(())`，`meta_contrains` 非空 | 方程**挂账**（不可判定），调用方须在 `unify_catch` 边界升级为错误 |
| `Err(Basic)` | 刚性失配（真失败） |
| `Err(Stuck)` | 传播中的"不可判定"（例如 `invert` 遇到非变量实参） |
| `Err(Trait(msg))` | 实例求解失败 |

L03–L05 只有 `Ok` / `Err(UnifyError)` 两态，**没有挂账**。

**"歧义"在合一器里不存在**：flex-flex 异号总是"解一侧"（L05 选较长 spine
一侧优先反演），从不报歧义。歧义只可能出现在类型类实例求解（§4.5），而那里
的实现是"取第一个匹配者"，也不报歧义（见 §6）。

---

## 3. 隐式参数

### 3.1 语法

**L04/L05 的表面语法用花括号**（`src/L04_implicit/parser/mod.rs:10-42`）：

```rust
/// 隐式/显式标记（上游 04 `Icit`）。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Icit {
    Impl,
    Expl,
}

/// lambda binder / 应用实参的命名引用（上游 `Either Name Icit`）：
/// `Name` = 命名隐式（`\{x = y}` binder、`t {x = u}` 实参——按 Pi binder
/// 名字定位插入点）；`Icit` = 位置隐式/显式。
#[derive(Clone, Debug, PartialEq)]
pub enum Either {
    Name(Span<SmolStr>),
    Icit(Icit),
}

#[derive(Clone, Debug)]
pub enum Raw {
    Var(Span<SmolStr>),
    Lam(Span<SmolStr>, Either, Box<Raw>),
    App(Box<Raw>, Box<Raw>, Either),
    U,
    Pi(Span<SmolStr>, Icit, Box<Raw>, Box<Raw>),
    Let(Span<SmolStr>, Box<Raw>, Box<Raw>, Box<Raw>),
    Hole,
    SrcPos(Span<()>, Box<Raw>),
}
```

对应的产生式（`src/L04_implicit/parser/mod.rs:210-303`）：

```rust
/// 实参（上游 `pArg`）：`{x = t}` 命名隐式 | `{t}` 隐式 | atom 显式。
/// 命名形态须先于隐式形态尝试（`{x = t}` 的 `x` 会先吃掉 `{`）。
fn p_arg(...) -> ... {
    let named_arg = brace((string(Ident), kw(Eq), p_raw)).map(|(x, _, t)| (Either::Name(x), t));
    let implicit_arg = brace(p_raw).map(|t| (Either::Icit(Icit::Impl), t));
    let explicit_arg = p_atom.map(|t| (Either::Icit(Icit::Expl), t));
    named_arg.or(implicit_arg).or(explicit_arg).parse(input, state)
}

/// Pi binder（上游 `pPiBinder`）：`{xs}` / `{xs : A}`（类型可省 → 洞，隐式）
/// | `(xs : A)`（显式）。
fn p_pi_binder(...) -> ... {
    let implicit_binder = brace((
        p_bind.many1(),
        (kw(Colon), p_raw).option().map(|x| match x {
            Some((_, x)) => x,
            None => Raw::Hole,
        }),
    )).map(|(xs, a)| (xs, a, Icit::Impl));
    let explicit_binder = paren((p_bind.many1(), kw(Colon).with(p_raw)))
        .map(|(xs, a)| (xs, a.1, Icit::Expl));
    implicit_binder.or(explicit_binder).parse(input, state)
}
```

**L10/L12 起改用方括号 `[...]`**（`src/L10_typeclass/parser/mod.rs:722-753`、
`src/L12_canonical/parser/mod.rs:952-1033`）：

```rust
fn p_arg(...) -> ... {
    let named_impl_arg = square_cut(
        (smolstr(Ident), Cut((kw(Eq), p_raw))).map(|(x, t)| (Either::Name(x.clone()), t))
            .or(p_raw.map(|t| (Either::Icit(Icit::Impl), t)))
            .many0_sep(kw(T![,]))
    ).map(|x| x.ok().unwrap_or_default());
    let explicit_arg = expr.map(|t| vec![(Either::Icit(Icit::Expl), t)]);
    ...
}
```

**因此「`f[A, B]` 逗号合并」= `many0_sep(T![,])`**：一个方括号组内多个实参
全部是隐式（`Iter` 折叠成嵌套 `App`），`f[A = x]` 则是 `Either::Name`。

Pi binder 的方括号形态（`src/L12_canonical/parser/mod.rs:1009-1043`）：

```rust
/// [x: A] or [x]
fn p_pi_impl_binder(...) {
    square_cut(
        (p_bind, (kw(Colon), p_raw).option())
            .map(|(xs, opt)| {
                let a = match opt {
                    Some((_, x)) => x,
                    None => Raw::Hole(xs.end_span()),
                };
                (xs, a, Icit::Impl)
            })
            .many0_sep((kw(T![,]), kw(EndLine).option())),
    )
    ...
}
```

即 **`[x]` 的域是 `Raw::Hole`**——这正是"隐式参数域默认 `U(0)`"的**语法
起点**（§3.7 给出该洞被解成 `U(0)` 的地方）。

### 3.2 `Icit` 穿线

| 位置 | L03 | L04+ |
|---|---|---|
| `Tm::Lam` | `Lam(Name, Box<Tm>)` | `Lam(Name, Icit, Box<Tm>)`（`src/L04_implicit/mod.rs:89`） |
| `Tm::App` | `App(Box<Tm>, Box<Tm>)` | `App(Box<Tm>, Box<Tm>, Icit)`（`:90`） |
| `Tm::Pi` | `Pi(Name, Box<Ty>, Box<Ty>)` | `Pi(Name, Icit, Box<Ty>, Box<Ty>)`（`:92`） |
| `Spine` | `List<Val>` | `List<(Val, Icit)>`（`:109`） |
| `Val::Lam/Pi` | 无 icit | `Lam(Name, Icit, Closure)` / `Pi(Name, Icit, Box<VTy>, Closure)`（`:121-122`） |

**β 应用不看 icit**（`src/L05_pruning/mod.rs:481`：`/// `vApp t u i`：β 应用
不看 icit，中性链把 `(u, i)` 记进 spine。`）。

### 3.3 插入算法

`src/L04_implicit/mod.rs:480-547`（L05 同构，只把 `fresh_meta(cxt)` 换成
带类型版本）：

```rust
    /// `insert'`：类型的隐式 Pi 前缀逐个补 fresh meta 实参（上游 `insert'`）。
    fn insert_go(&mut self, cxt: &Cxt, t: Tm, va: &Val) -> (Tm, VTy) {
        match self.force(va) {
            Val::Pi(_, Icit::Impl, _, b) => {
                let m = self.fresh_meta(cxt);
                let mv = self.eval(&cxt.env, &m);
                let va = self.closure_apply(&b, mv);
                self.insert_go(cxt, Tm::App(Box::new(t), Box::new(m), Icit::Impl), &va)
            }
            va => (t, va),
        }
    }

    /// infer 后无条件插入（上游 `insert'` 的 Result 包装）。
    fn insert_t(&mut self, cxt: &Cxt, t: Tm, va: VTy) -> Result<(Tm, VTy), Error> {
        Ok(self.insert_go(cxt, t, &va))
    }

    /// infer 后插入，但隐式 lambda 本身免插（`\{A} x. …` 已显式拿住隐式
    /// binder，再插就是多余应用）。
    fn insert(&mut self, cxt: &Cxt, t: Tm, va: VTy) -> Result<(Tm, VTy), Error> {
        match &t {
            Tm::Lam(_, Icit::Impl, _) => Ok((t, va)),
            _ => self.insert_t(cxt, t, va),
        }
    }

    /// `insertUntilName`：插入到名字匹配的隐式 Pi binder 为止；类型的隐式
    /// 前缀耗尽仍无匹配 → `NoNamedImplicitArg`。
    fn insert_until_go(
        &mut self, cxt: &Cxt, name: &Span<SmolStr>, t: Tm, va: &Val,
    ) -> Result<(Tm, VTy), Error> {
        match self.force(va) {
            Val::Pi(x, Icit::Impl, a, b) => {
                if x.data == name.data {
                    Ok((t, Val::Pi(x, Icit::Impl, a, b)))
                } else {
                    let m = self.fresh_meta(cxt);
                    let mv = self.eval(&cxt.env, &m);
                    let va = self.closure_apply(&b, mv);
                    self.insert_until_go(cxt, name,
                        Tm::App(Box::new(t), Box::new(m), Icit::Impl), &va)
                }
            }
            _ => Err(report_at(cxt.pos,
                format!("No named implicit argument with name {}", name.data))),
        }
    }
```

**规则（插入）**：

```
insert cxt t va:
  if t = λ^{Impl} …           → 不插入（幂等）
  else                        → insert_t
insert_t = insert_go:
  insert_go (Π^{Impl} x:A. B) t = insert_go B[x := ?m] (t ?m)   ?m = fresh_meta A
  insert_go 其它 va          t = (t, va)

insert_until_name n t va:
  va = Π^{Impl} x:A. B 且 x = n  → (t, va)         -- 停在匹配 binder，不应用
  va = Π^{Impl} x:A. B 且 x ≠ n  → insert_until_name n (t ?m) B[x := ?m]
  其它                            → 错误 "No named implicit argument with name n"
```

L12 用 `name.map(|x| format!("no named implicit arg {}", x))`
（`src/L12_canonical/elaboration.rs:76`）——**措辞与 L04/L05 不同**。

### 3.4 `check`：非 λ 项对隐式 Π 补 binder（不补 meta）

`src/L04_implicit/mod.rs:549-604`（**逐字**，注意注释里的匹配语义）：

```rust
    fn check(&mut self, cxt: &Cxt, t: &Raw, a: &VTy) -> Result<Tm, Error> {
        match (t, &self.force(a)) {
            (Raw::SrcPos(pos, t), _) => { ... }

            // binder 形态与 Π 的 icit 匹配：位置 binder 要求 icit 相等，
            // 命名 binder（\{x = y}）要求**Pi binder 名**相等且 Π 为隐式
            // （上游 `either (\x -> x == x' && i' == Impl) (== i') i`——
            // 匹配的 Either Name 是引用名，Pi 名才是被匹配方）。
            (Raw::Lam(x, i, t), Val::Pi(x_t, i_t, a, b))
                if match i {
                    Either::Name(n) => n.data == x_t.data && *i_t == Icit::Impl,
                    &Either::Icit(j) => j == *i_t,
                } =>
            {
                let body = self.check(
                    &cxt.bind(x.clone(), (**a).clone()),
                    t,
                    &self.closure_apply(b, Val::vvar(cxt.lvl)),
                )?;
                Ok(Tm::Lam(x.clone(), *i_t, Box::new(body)))
            }

            // 非 lambda 项检查到隐式 Π：插入隐式 binder（对源码名不可见）
            (t, Val::Pi(x, Icit::Impl, a, b)) => {
                let body = self.check(
                    &cxt.new_binder(x.clone(), (**a).clone()),
                    t,
                    &self.closure_apply(b, Val::vvar(cxt.lvl)),
                )?;
                Ok(Tm::Lam(x.clone(), Icit::Impl, Box::new(body)))
            }

            (Raw::Let(x, a, t, u), a_prime) => { ... }

            // hole：直接以 fresh meta 填充
            (Raw::Hole, _) => Ok(self.fresh_meta(cxt)),

            (t, expected) => {
                let (t, tty) = self.infer(cxt, t)?;
                let (t, tty) = self.insert(cxt, t, tty)?;
                self.unify_catch(cxt, expected, &tty)?;
                Ok(t)
            }
        }
    }
```

**check 中"洞在哪里"的规则**：
- λ binder 与 Π 逐一配对（icit / 名字匹配）；
- **非 λ 项**对隐式 Π → **生成隐式 λ binder**（而不是 meta），因此
  `def f[A](x: A): A = x` 中 `x` 的隐式参数是"检查期提升"，不产生 meta；
- `Raw::Hole` → `fresh_meta(cxt)`（L05 起带期望类型 `a`：`fresh_meta(cxt, a.clone())`，`src/L05_pruning/mod.rs:1152-1153`）；
- 兜底：`infer` → `insert` → `unify_catch`。

### 3.5 `infer` 的 App 分派（插入触发点）

`src/L04_implicit/mod.rs:648-700`（**逐字**）：

```rust
            Raw::App(t, u, arg) => {
                // 实参分派：命名 → insertUntilName 后按 Impl 应用；
                // 位置 Impl → 直接应用（显式给隐式）；位置 Expl → 先 insert_t。
                let (i, t, tty) = match arg {
                    Either::Name(name) => {
                        let (t, tty) = self.infer(cxt, t)?;
                        let (t, tty) = self.insert_until_name(cxt, name, t, tty)?;
                        (Icit::Impl, t, tty)
                    }
                    &Either::Icit(Icit::Impl) => {
                        let (t, tty) = self.infer(cxt, t)?;
                        (Icit::Impl, t, tty)
                    }
                    &Either::Icit(Icit::Expl) => {
                        let (t, tty) = self.infer(cxt, t)?;
                        let (t, tty) = self.insert_t(cxt, t, tty)?;
                        (Icit::Expl, t, tty)
                    }
                };
                let (a, b) = match self.force(&tty) {
                    Val::Pi(_, i_t, a, b) if i_t == i => ((*a).clone(), b.clone()),
                    Val::Pi(_, i_t, _, _) => {
                        return Err(report_at(
                            cxt.pos,
                            format!(
                                "Function icitness mismatch: expected {}, got {}.",
                                show_icit(i),
                                show_icit(i_t)
                            ),
                        ))
                    }
                    // 非 Π 头：合成 Π（定义域 + 余定义域挂洞）与之合一。
                    tty => { ... }
                };
                let u = self.check(cxt, u, &a)?;
                let b_applied = self.closure_apply(&b, self.eval(&cxt.env, &u));
                Ok((Tm::App(Box::new(t), Box::new(u), i), b_applied))
            }
```

**三条规则**：
1. **显式实参位**（`Expl`）：先 `insert_t` 把头的隐式 Π 前缀补成 `?m`，
   再要求剩下的 Π 是显式。
2. **隐式实参位**（`Impl`）：**不插入**，直接要求 Π 是隐式；若头类型是显式
   Π → `Function icitness mismatch: expected implicit, got explicit.`。
3. **命名实参位**（`Name n`）：先插入到名为 `n` 的隐式 binder，再按 `Impl`
   应用。

**非 Π 头的合成 Π**（`src/L04_implicit/mod.rs:679-695`；L05 把两个洞钉成
`Val::U`，`src/L05_pruning/mod.rs:1231-1254`）：

```rust
                    // 非 Π 头：合成 Π（定义域 + 余定义域挂洞）与之合一。
                    // 合成 binder 用普通 bind + 名字 "x"（上游同款）。
                    tty => {
                        let new_meta = self.fresh_meta(cxt);
                        let a = self.eval(&cxt.env, &new_meta);
                        let cod_meta = self.fresh_meta(&cxt.bind(empty_span("x".into()), a.clone()));
                        let b = Closure(cxt.env.clone(), Box::new(cod_meta));
                        // 实参序 (tty, 合成Π) 系上游 04 的 unifyCatch 次序；
                        // 上游 03 是 (合成Π, tty)——各层各自忠实，只影响
                        // 报错文案里 expected/inferred 的方向。
                        self.unify_catch(cxt, &tty,
                            &Val::Pi(empty_span("x".into()), i, Box::new(a.clone()), b.clone()))?;
                        (a, b)
                    }
```

> **注意实参序**：L03 是 `(合成Π, tty)`（`src/L03_holes/mod.rs:547`），
> L04/L05/L10/L12 是 `(tty, 合成Π)`——只影响错误消息里 expected/find 的
> 方向（`src/L04_implicit/mod.rs:686-688` 自陈）。

`infer` 的 λ 分支也会插入，且**在扩展后的上下文里插**
（`src/L04_implicit/mod.rs:628-641`）：

```rust
            Raw::Lam(x, Either::Icit(i), t) => {
                // 定义域挂洞；余定义域闭包住当前环境（解可引用局部变量）。
                // 体推断后在**扩展后**的上下文里 insert（上游 `insert cxt'`）。
                let new_meta = self.fresh_meta(cxt);
                let a = self.eval(&cxt.env, &new_meta);
                let cxt1 = cxt.bind(x.clone(), a.clone());
                let (t, b) = self.infer(&cxt1, t)?;
                let (t, b) = self.insert(&cxt1, t, b)?;
                let b_closure = self.close_val(cxt, &b);
                ...
            }
```

L05 的同一处把定义域洞钉 `Val::U`（`src/L05_pruning/mod.rs:1182-1193`）。

### 3.6 inserted binder 对源码名不可见

`src/L04_implicit/mod.rs:767-776` 与 `:799-819`：

```rust
/// binder 的来源：`Source` = 源码写出的（名字可被 `Raw::Var` 引用），
/// `Inserted` = elaboration 补插的隐式 binder（对源码名字不可见）。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NameOrigin {
    Inserted,
    Source,
}

/// scope 里每一项（名字、来源、类型；头 = 最内层绑定）。
type Types = List<(Name, NameOrigin, VTy)>;
```

```rust
    /// Extend Cxt with an inserted implicit binder（对源码名不可见）。
    fn new_binder(&self, x: Name, a: VTy) -> Cxt {
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl)),
            types: self.types.prepend((x, NameOrigin::Inserted, a)),
            lvl: self.lvl + 1,
            bds: self.bds.prepend(BD::Bound),
            pos: self.pos,
        }
    }
```

名字查找只认 `Source`（`src/L04_implicit/mod.rs:614-624`）：

```rust
                for (x2, origin, a) in cxt.types.iter() {
                    // inserted binder 对源码名字不可见
                    if x.data == x2.data && *origin == NameOrigin::Source {
                        return Ok((Tm::Var(Ix(i)), a.clone()));
                    }
                    i += 1;
                }
```

L12 用 `src_names` 名字表 + `lvl2ix` 直接命中（`src/L12_canonical/elaboration.rs:1172-1178`
对应 L05 的 `src/L05_pruning/mod.rs:1172-1178`），插入 binder 不入表。

### 3.7 "隐式参数域默认 `U(0)`"规则

规则有两处落点，**都必须形式化**：

**(a) 语法层**：`[A]`（无标注）→ `Raw::Pi(A, Impl, Raw::Hole, …)`
（`src/L12_canonical/parser/mod.rs:1014-1027`）。

**(b) 宇宙检查层**：洞作为"类型"被 `check_universe` 检查，**未解 meta 的域
洞一律解成 `U(0)`**（`src/L10_typeclass/elaboration.rs:208-259`，L12
`elaboration.rs:...` 同构）：

```rust
            Val::Flex(m, sp) => {
                let (pren, prune_non_linear) = self.invert(cxt.lvl, sp)?;
                ...
                if pren.dom.0 == 0 {
                    let mty = self.force(&mty);
                    match mty.as_ref() {
                        Val::U(x) => {//TODO:x?
                            self.meta[m.0 as usize] = MetaEntry::Solved(Val::U(0).into(), mty);
                            Ok((t_inferred, 0))
                        },
                        _ => {
                            let err_typ = self.force(&mty);
                            Err(Error(t_span.map(|_|  format!("meta type {:?} is not a universe", err_typ))))
                        },
                    }
                } else {
                    let rhs = self.rename(
                        &PartialRenaming { occ: Some(*m), ..pren },
                        &Val::U(0).into(),
                    )?;
                    let solution = self.eval(&List::new(), &self.lams(pren.dom, &mty, rhs));
                    self.meta[m.0 as usize] = MetaEntry::Solved(solution, mty);
                    Ok((t_inferred, 0))
                }
            }
```

**(c) 声明层（L09+）**：enum/struct/trait 的**无标注隐式参数域**在脱糖时就
钉成 `Raw::U(0)`（`src/L10_typeclass/elaboration.rs:400-421`）：

```rust
                // 隐式参数是类型参数：无标注（Hole）的域钉为 U(0)。域洞若保留，
                // 第 2+ 个参数的域经 fresh_meta 的 AppPruning 成为部分应用
                // meta（`?m A`），使用点显式供给枚举隐式实参（`P1[Nat][Bool]`）
                // 需解 `?m A := U(0)`，invert 对非变量 spine 实参（如 Nat 的
                // 值）直接 Err → 误报 can't unify（L07/L08 黑盒三轮修复的
                // 前向传播；check_universe 只解洞的类型 meta，域值 meta 仍
                // 未解，触发链完整）。钉 U(0)（与 check_universe 的 meta 解
                // U(0) 同口径）从声明处消除该 meta；宇宙扫描对 U(0) 域贡献
                // lvl 0 = max 恒等，不扰动 universe_lvl。用户显式标注的域
                // （`[A : Type 1]`）与显式索引不动——需高层级实例化时显式
                // 标注即可。
                let params: Vec<(Span<String>, Raw, Icit)> = params
                    .into_iter()
                    .map(|(n, a, i)| {
                        let a = if i == Icit::Impl && matches!(a, Raw::Hole) {
                            Raw::U(0)
                        } else {
                            a
                        };
                        (n, a, i)
                    })
                    .collect();
```

**形式化规则**：

```
Γ ⊢ ?m : U(k)      （?m 是一个"类型"洞）
────────────────────────────────────────
?m := U(0)          （无论 k 为何，一律 0）
```

### 3.8 隐式参数相关的错误文案

| 条件 | 文案 | 锚点 |
|---|---|---|
| 名字不在 scope | `Name not in scope: x` | `src/L04_implicit/mod.rs:623` |
| 命名隐式实参找不到 binder | `No named implicit argument with name x` | `src/L04_implicit/mod.rs:532-535`；L12 作 `no named implicit arg x`（`elaboration.rs:76`） |
| 无法推断命名 λ 的类型 | `Cannot infer type for lambda with named argument` | `src/L04_implicit/mod.rs:643-646` |
| icit 失配 | `Function icitness mismatch: expected implicit, got explicit.` | `src/L04_implicit/mod.rs:669-678` + `show_icit` `:867-873` |
| 合一失败 | `Cannot unify expected type\n\n  …\n\nwith inferred type\n\n  …` | `src/L04_implicit/mod.rs:735-744` |

---

## 4. trait / typeclass 系统

### 4.1 声明语法与 AST

**L10 语法**（`src/L10_typeclass/parser/mod.rs:696-753`；L12 同构但用 `for`）：

```rust
/// Parse a `trait Name` body: method declarations without bodies
/// (`def eq(x: A): Bool`) — the shape this lesson's checker consumes.
fn p_trait_def<'a: 'b, 'b>(input, state) -> IResult<'a, 'b, Decl> {
    let p_def_declare = (
        kw(DefKeyword),
        string(Ident),
        p_pi_binder.many0().map(|x| x.into_iter().flatten().collect::<Vec<_>>()),
        (kw(T![:]), p_raw).map(|(_, x)| x),
    ).map(|(_, name, params, ret)| (name, params, ret));
    (
        kw(TraitKeyword),
        string(Ident),
        p_pi_impl_binder_option,
        brace(p_def_declare.many0_sep(kw(EndLine))),
    ).map(|(_, name, params, body)| Decl::TraitDecl { name, params, methods: body.ok().unwrap_or_default() })
     .parse(input, state)
}

fn p_impl<'a: 'b, 'b>(input, state) -> IResult<'a, 'b, Decl> {
    (
        kw(ImplKeyword),
        p_pi_impl_binder_option,
        string(Ident),
        square_cut(p_raw.many0_sep(kw(T![,]))).option()...,
        kw(ForKeyword),
        p_raw,
        brace(p_def.many0_sep(kw(EndLine))),
    ).map(|x| (x, false)).or((
        kw(ImplKeyword),
        p_pi_impl_binder_option,
        p_raw,
        brace(p_def.many0_sep(kw(EndLine))),
    ).map(|x| (..., true)))
     .map(|((_, params, trait_name, trait_params, _, name, body), need_create)| Decl::ImplDecl {
            name, params, trait_name, trait_params,
            methods: body.ok().unwrap_or_default(), need_create,
        })
     .parse(input, state)
}
```

AST（`src/L10_typeclass/parser/syntax.rs:178-205`）：

```rust
#[derive(Clone, Debug)]
pub enum Decl {
    Def { name: Span<String>, params: Vec<(Span<String>, Raw, Icit)>, ret_type: Raw, body: Raw },
    Println(Raw),
    Enum { is_trait: bool, name: Span<String>, params: Vec<(Span<String>, Raw, Icit)>,
           cases: Vec<(Span<String>, Vec<(Span<String>, Raw, Icit)>, Option<Raw>)> },
    TraitDecl { name: Span<String>, params: Vec<(Span<String>, Raw, Icit)>,
                methods: Vec<(Span<String>, Vec<(Span<String>, Raw, Icit)>, Raw)> },
    ImplDecl { name: Raw, params: Vec<(Span<String>, Raw, Icit)>,
               trait_name: Span<String>, trait_params: Vec<Raw>,
               methods: Vec<Decl>, need_create: bool },
}
```

**两种 `impl` 形态**：`impl … Trait[args] for Type { … }`（`need_create = false`）
与 `impl … Type { … }`（固有 impl，`need_create = true`，trait 名被合成为
`$trait_name$…`）。

**`where` 子句**（**只在 `def` 上**，L12 `parser/mod.rs:1362-1443`）：
`where T: Show + Eq, U: Trait[U]` 脱糖为**追加在显式参数之后的隐式参数**，
名字规则 `_{trait_lowercased}_{TypeName}`：

```rust
            // Desugar where clause to implicit parameters (appended after all explicit params)
            if let Some(clause) = where_clause {
                for items in clause {
                    for (type_name, bounds) in items {
                        for bound in bounds {
                            ...
                            let inst_name = SmolStr::new(format!("_{}_{}", trait_name.to_lowercase(), type_name.data));
                            ...
                            all_params.push((type_name.to_span().map(|_| inst_name.clone()), trait_app, Icit::Impl));
```

**trait 头 / impl 头上的 `where` 不支持**——`p_where_clause` 只出现在 `p_def`
中（`src/L12_canonical/parser/mod.rs:1364-1377`），这正是
`src/prelude/show.typort:9-11` 说 `impl[T] Show for List[T] where T: Show`
不被支持的原因。**L10 更彻底：`where` 只是保留字**，`WhereKeyword` 在
`src/L10_typeclass/parser/` 里除 `lex.rs:21`（枚举成员）、`:76`（Display）、
`:130`（关键字表）外**没有任何语法规则消费它**；`class`/`static`/`by`
同为死关键字（`src/L10_typeclass/parser/lex.rs:112-133`）。

### 4.2 `trait` 声明脱糖 = `is_trait` 的 enum

`src/L10_typeclass/elaboration.rs:624-659`（L12 同构 `elaboration.rs:763-797`）：

```rust
            Decl::TraitDecl { name, mut params, methods } => {
                self.trait_solver.new_trait(name.data.clone());
                let mut param = vec![(name.clone().map(|_| "Self".to_owned()), Raw::Hole, Icit::Impl)];
                param.append(&mut params);
                let out_param = param.iter().map(|x| match &x.1 {
                        Raw::App(t, ..) if matches!(t.as_ref(), Raw::Var(d) if d.data == "outParam") => true,
                        _ => false,
                    }).collect::<Vec<_>>();
                self.trait_definition.insert(name.data.clone(), (param.clone(), out_param.clone(), methods.clone()));
                self.trait_out_param.insert(name.data.clone(), out_param);
                let mut cxt = cxt.clone();
                let (_, _, c) = self.infer(&cxt, Decl::Enum {
                    is_trait: true,
                    name: name.clone(),
                    params: param,
                    cases: vec![(
                        name.map(|x| format!("{x}.mk")),
                        methods.into_iter().map(|x| (
                            x.0.clone(),
                            std::iter::once((x.0.clone().map(|_| "this".to_owned()),
                                             Raw::Var(x.0.map(|_| "Self".to_owned())), Icit::Expl))
                                .chain(x.1.into_iter())
                                .rev()
                                .fold(x.2, |a, b| Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))),
                            Icit::Expl,
                        )).collect(),
                        None,
                    )],
                })?;
                cxt = c;
                Ok((DeclTm::Trait {}, Val::U(0).into(), cxt.clone()))
            },
```

**要点（形式化必须照抄的"编码"）**：

- `trait T[A₁, …, Aₙ] { def m(ps): R }` 被编码为一个 **enum**
  `T`（`Val::Sum`/`Tm::Sum` 带 `is_trait = true`），
  **实例 = 该 enum 的构造子值**（构造子名 `T.mk`）；
- trait 参数 = `[Self : _] ++ params`，**`Self` 是第 0 个隐式参数**；
- `T.mk` 的字段是各方法，每个字段的类型是
  `Π (this : Self) (方法参数). R`（`this` 显式）；
- 两张伴生表：
  - `trait_definition : HashMap<String, (参数表, out 掩码, 方法表)>`
  - `trait_out_param : HashMap<String, Vec<bool>>`
  （`src/L10_typeclass/mod.rs:467-468`）

### 4.3 `impl` 登记：`Instance`

`src/L10_typeclass/elaboration.rs:556-594`（**诊断字典传递 / 实例的表示**）：

```rust
                let mut trait_param = vec![typ.clone()];
                for a in trait_params.clone() {
                    ...
                    trait_param.push(x);
                }
                let out_param = self.trait_out_param.get(&trait_name.data)
                    .ok_or(Error(trait_name.clone().map(|n| format!("trait `{}` not declared", n))))?;
                let trait_param = trait_param.into_iter()
                    .zip(out_param)
                    .filter(|x| !x.1)
                    .map(|x| x.0)
                    .collect();
                let typ_name = format!("{:?}{:?}", trait_name.data, trait_param);
                let inst = Instance {
                    assertion: Assertion { name: trait_name.data.clone(), arguments: trait_param },
                    dependencies: List::new(),
                    lvl: trait_name.to_span().map(|_| typ_name.clone()),
                };
                self.trait_solver.impl_trait_for(trait_name.data.clone(), inst);
```

`Instance`（`src/L10_typeclass/typeclass.rs:72-85`）：

```rust
/// A type class applied to arguments.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Assertion {
    pub name: String,
    pub arguments: Vec<Typ>,
}

/// A type class instance declaration.
#[derive(Debug, Clone)]
pub struct Instance {
    pub assertion: Assertion,
    pub dependencies: List<Assertion>,
    pub lvl: Span<String>,
}
```

**答案：实例的"值"就是字典**——`Val::SumCase{is_trait:true, …}`（trait Sum
的构造子 `T.mk` 应用到各方法实现）。但 `Instance` 里**不存这个值**，只存
它的**顶层 def 名**（`Instance.lvl`）；求解命中后 L10/L12 **用这个名字当
源码变量重新 `infer_expr`** 把字典项取回来（`src/L10_typeclass/unification.rs:493`、
`src/L12_canonical/unification.rs:538`）：

```rust
                let ret = self.infer_expr(cxt, Raw::Var(a));
                let (tm, _) = self.insert(cxt, ret).map_err(|e| e.0.data)?;
                let val = self.eval(&cxt.env, &tm);
                if let Val::SumCase { typ, .. } = val.as_ref() {
                    let _ = self.unify(cxt.lvl, cxt, typ, &x);
                }
                Ok(Some((tm, val)))
```

而该 `impl` 声明本身被登记为一个 `Decl::Def`：名字 = `typ_name`，
类型 = `T[A₁]…[Aₙ]`（隐式应用），体 = `T.mk name A₁ … Aₙ (λ this ps. body)…`
（`src/L10_typeclass/elaboration.rs:590-620`）：

```rust
                let mut ret = std::iter::once(name.clone())
                    .chain(trait_params.clone())
                    .fold(Raw::Var(trait_name.clone().map(|x| format!("{x}.mk"))), |ret, x| {
                        Raw::App(Box::new(ret), Box::new(x), Either::Icit(Icit::Impl))
                    });
                for decl in methods {
                    if let Decl::Def { name: def_name, params, ret_type: _, body } = decl {
                        ret = Raw::App(
                            Box::new(ret),
                            Box::new(Raw::Lam(
                                def_name.map(|_| "this".to_owned()),
                                Either::Icit(Icit::Expl),
                                Box::new(params.into_iter().rev()
                                    .fold(body, |ret, x| Raw::Lam(x.0.clone(), Either::Icit(x.2), Box::new(ret))))
                            )),
                            Either::Icit(Icit::Expl),
                        );
                    }
                }
                let (_, _, c) = self.infer(&cxt, Decl::Def {
                    name: trait_name.to_span().map(|_| typ_name.clone()),
                    params,
                    ret_type: trait_params.into_iter()
                        .fold(Raw::App(Raw::Var(trait_name).into(), name.into(), Either::Icit(Icit::Impl)),
                              |a, b| Raw::App(Box::new(a), Box::new(b), Either::Icit(Icit::Impl))),
                    body: ret,
                })?;
```

**所以字典传递的形式是**：实例 = `T.mk <实例类型参数> <方法实现（λ this ps. body）…>`，
方法调用 = 先取到该实例值 `$$`，再 `$$.m $this ps…`
（见 §4.8 的 `trait_wrap`）。**实例项与普通项完全同构**，没有独立的
dictionary 语法。

`dependencies: List::new()`（`src/L10_typeclass/elaboration.rs:582-586`、
`src/L12_canonical/elaboration.rs:720-724`）——**L10/L12 的实例没有任何
子目标**，求解器里的 consumer/子目标机制结构性空转（§6）。

**实例名的构造**（形式化时须照抄，因为它就是字典的"键"）：

```rust
let typ_name = format!("{:?}{:?}", trait_name.data, trait_param);   // src/L10_typeclass/elaboration.rs:581
let typ_name = SmolStr::new(format!("{:?}{:?}", trait_name.data, trait_param));  // src/L12_canonical/elaboration.rs:719
```

`Span` 的 `Debug` 携带 offset（`{data:?} @ {start},{end}`），因此**实例名
是"trait 名 + 实参 `Typ` 的 Debug"，且不同源码位置的同名 impl 得到不同
名字**；泛型 impl 的名字里含裸 `Var(层级)`（如 `"Say"[Var(0)]`）。该名字
随后被 `Decl` 表/`global` 表当成普通顶层名登记。

**方法投影**（两个方向都必须形式化）：

- **项层**：`Tm::Obj(dict, m)`（`x.m` 的语法就是 `Raw::Obj`，
  `src/L10_typeclass/parser/mod.rs:342-360`）。
- **推断侧**：由构造子 Π 链里的同名字段给出字段类型
  （`src/L10_typeclass/elaboration.rs:749-826`）：先按 trait Sum / SumCase 的
  字段找，找到即 `Tm::Obj(tm, t)`；找不到才落 `trait_wrap`（§4.8）。
- **求值侧**：从 `SumCase.datas` 取值（`src/L10_typeclass/mod.rs:869-893`）：

```rust
            Tm::Obj(tm, name) => {
                let a = self.eval(env, tm);
                let a = self.force(&a);
                match a.as_ref() {
                    Val::Sum(_, params, _, _) => {
                        params.iter().find(|(f_name, _, _, _)| f_name == name).unwrap().1.clone()
                    },
                    Val::SumCase { datas, typ, .. } => {
                        (match typ.as_ref() {
                            Val::Sum(_, params, _, _) => params,
                            _ => panic!("impossible {typ:?}"),
                        }).iter()
                            .map(|x| (x.0.clone(), x.1.clone(), x.3))
                            .chain(datas.iter().cloned())
                            .find(|(f_name, _, _)| f_name == name)
                            .unwrap().1.clone()
                    },
                    _ => Val::Obj(a, name.clone(), List::new()).into(),
                }
            }
```

- **字典不可作类型参数**：`Val::SumCase` 的 `to_typ()` 恒 `None`
  （`src/L10_typeclass/typeclass.rs:63`），所以字典永不进入实例断言。
- **`impl Type { … }`（固有 impl，`need_create = true`）先合成一个
  `Decl::TraitDecl`**（`src/L10_typeclass/elaboration.rs:537-555`），即把它
  变成"一个只有它自己的无名 trait 的实例"：私有 trait 名
  `format!("$trait_name${}", SelfTy的Display)`，参数 = impl 参数。

### 4.4 `outParam`

- 标注写法：`trait Add[T, O: outParam(Type 0)]`（`src/prelude/core/op.typort:22`），
  依赖 `def outParam[A](a: A): A = a`（`:19`）作为**类型层面的标记**。
- 识别：`Raw::App(t, ..) if matches!(t.as_ref(), Raw::Var(d) if d.data == "outParam")`
  （`src/L10_typeclass/elaboration.rs:628-631`）——**纯语法识别**，不检查
  `outParam` 是否指向那个 `def`。
- **语义**：out 位**不参与实例查找**。两处实现：
  - 求解侧滤掉 out 位（`src/L12_canonical/unification.rs:519-528`）；
  - 登记侧也被滤掉（`src/L12_canonical/elaboration.rs:714-718`）。
- `trait_wrap` 试解时 out 位填**通配** `Flex(MetaVar(u32::MAX), [])`
  （`src/L12_canonical/elaboration.rs:1169-1170`、`:1222-1223`）。

### 4.5 实例求解器 `Synth`

数据结构（`src/L10_typeclass/typeclass.rs:87-153`）：

```rust
pub struct GeneratorNode {
    goal: Assertion,
    instances: Vec<Instance>,
    index: usize,
}

pub struct ConsumerNode {
    goal: Assertion,
    subgoals: List<Assertion>,
    lvl: Span<String>,
}

pub enum Waiter { Root, ConsumerNode(ConsumerNode) }

pub struct TableEntry {
    waiters: Vec<Waiter>,
    answers: Vec<(Assertion, Span<String>)>,
}

/// The state of the algorithm.
#[derive(Debug, Clone, Default)]
pub struct Synth {
    /// A stack of [`GeneratorNode`]s.
    generator_stack: Vec<GeneratorNode>,
    /// A stack of [`ConsumerNode`], [`Assertion`] pairs.
    resume_stack: Vec<(ConsumerNode, Assertion)>,
    /// The instances available for a type class.
    class_instances: HashMap<String, Vec<Instance>>,
    /// Information about each `subgoal` being solved.
    assertion_table: HashMap<Assertion, TableEntry>,
    /// The "final" answer for the algorithm.
    root_answer: Option<Span<String>>,
}
```

主循环（L10，`src/L10_typeclass/typeclass.rs:213-285`）：

```rust
    /// The entry point for the algorithm.
    pub fn synth(&mut self, assertion: Assertion) -> Option<Span<String>> {
        // Insert the "root" goal to be solved.
        self.new_subgoal(&assertion, &Waiter::Root);

        // Visciously terminate on cycles.
        let mut effort = 0;
        loop {
            effort += 1;
            if effort > 1000 {
                panic!("Too much effort :(");
            }

            // Terminate once we find an answer for the root goal.
            if let Some(root_answer) = &self.root_answer {
                break Some(root_answer.clone());
            }

            if let Some((consumer_node, answer)) = self.resume_stack.pop() {
                match uncons(&consumer_node.subgoals) {
                    Some((subgoal, remaining)) => {
                        if self.try_answer(&subgoal, &answer) {
                            self.consume(ConsumerNode { goal: consumer_node.goal, subgoals: remaining, lvl: consumer_node.lvl });
                        } else { continue; }
                    }
                    None => panic!("Cannot resume with empty subgoals."),
                }
            } else if let Some(generator_node) = self.generator_stack.last_mut() {
                if generator_node.index == 0 {
                    self.generator_stack.pop();
                } else {
                    generator_node.index -= 1;
                    let goal = generator_node.goal.clone();
                    let instance = generator_node.instances[generator_node.index].clone();
                    if let Some((subgoals, lvl)) = self.try_resolve(&goal, &instance) {
                        self.consume(ConsumerNode { goal, subgoals, lvl });
                    }
                }
            } else {
                break None;
            }
        }
    }
```

子目标创建与消费（`src/L10_typeclass/typeclass.rs:287-354`）：

```rust
    fn new_subgoal(&mut self, subgoal: &Assertion, waiter: &Waiter) {
        self.assertion_table.insert(subgoal.clone(),
            TableEntry { waiters: vec![waiter.clone()], answers: vec![] });
        // TODO: local instances should work too!
        let instances = self.class_instances.get(&subgoal.name).unwrap().clone();
        // Try instances from the end, counting down to zero.
        let index = instances.len();
        self.generator_stack.push(GeneratorNode { goal: subgoal.clone(), instances, index });
    }

    fn consume(&mut self, consumer_node: ConsumerNode) {
        match uncons(&consumer_node.subgoals) {
            None => {
                self.assertion_table
                    .entry(consumer_node.goal.clone())
                    .and_modify(|TableEntry { waiters, answers }| {
                        let answer = consumer_node.goal;
                        answers.push((answer.clone(), consumer_node.lvl.clone()));
                        for waiter in waiters {
                            match waiter {
                                Waiter::Root => self.root_answer = Some(consumer_node.lvl.clone()),
                                Waiter::ConsumerNode(consumer_node) => self
                                    .resume_stack.push((consumer_node.clone(), answer.clone())),
                            }
                        }
                    });
            }
            Some((subgoal, _)) => {
                if let Some(TableEntry { waiters, answers }) = self.assertion_table.get_mut(&subgoal) {
                    for answer in answers {
                        self.resume_stack.push((consumer_node.clone(), answer.0.clone()));
                    }
                    waiters.push(Waiter::ConsumerNode(consumer_node));
                } else {
                    self.new_subgoal(&subgoal, &Waiter::ConsumerNode(consumer_node));
                }
            }
        }
    }
```

**算法规格（tabled resolution / SLD 带答案表）**：

- `synth G`：
  1. `new_subgoal G Root`：为 `G` 建表项（waiters = `[Root]`，answers = `[]`），
     取 `class_instances[G.name]` 的**克隆**，压 `GeneratorNode{G, idx}`。
  2. 主循环（**effort ≤ 1000，超出 panic**）：
     - 若 `resume_stack` 非空 → 弹出 `(consumer, answer)`：若 `answer` 与
       consumer 的第一个子目标相等（`try_answer`）则 `consume`（子目标减一），
       否则丢弃该 answer；
     - 否则看栈顶 generator：`index == 0` → 弹出（候选耗尽）；否则
       `index -= 1` 并试第 `index` 个实例：`try_resolve` 成功则
       `consume(goal, subgoals, lvl)`；
     - 都空 → `None`。
  3. `consume`：
     - 子目标空 → 目标得解：查表项，把 `(goal, lvl)` 加入 `answers`，并**把
       该表项的全部 waiters 唤醒**（`Root` → 置 `root_answer`；`ConsumerNode`
       → 把 `(node, answer)` 压 `resume_stack`）；
     - 子目标非空 → 若该子目标已有表项，把**已有答案**全部压 `resume_stack`，
       并把当前 consumer 挂成 waiter（**这就是缓存/表化**）；否则递归
       `new_subgoal`。

- `try_resolve`（`src/L10_typeclass/typeclass.rs:186-211`）：

```rust
    fn try_resolve(&mut self, goal: &Assertion, instance: &Instance) -> Option<(List<Assertion>, Span<String>)> {
        // 名字必须匹配
        if goal.name != instance.assertion.name { return None; }
        // 参数数量必须一致
        if goal.arguments.len() != instance.assertion.arguments.len() { return None; }
        // 一阶匹配：goal 视为已确定，pattern（实例断言）可含实例类型参数
        let mut subst = Subst::new();
        for (g_arg, i_arg) in goal.arguments.iter().zip(&instance.assertion.arguments) {
            if !match_typ(g_arg, i_arg, &mut subst) { return None; }
        }
        // 应用代换到 dependencies，得到具体 subgoals
        let concrete_deps = instance.dependencies
            .map(|dep| apply_subst_to_assertion(dep, &subst));
        Some((concrete_deps, instance.lvl.clone()))
    }
```

- `try_answer`（L10 用 `Assertion` 结构相等，`src/L10_typeclass/typeclass.rs:182-184`）：

```rust
    fn try_answer(&mut self, subgoal: &Assertion, answer: &Assertion) -> bool {
        subgoal == answer
    }
```

**搜索序（L10 与 L12 相反，必须分别形式化）**：

| | 候选序 | 锚点 |
|---|---|---|
| L10 | `index = len` 后 `-= 1` ⇒ **最后登记的先试** | `src/L10_typeclass/typeclass.rs:270-276`、`:300-301`（注释 `// Try instances from the end, counting down to zero.`） |
| L12 | `index = 0` 后 `+= 1` ⇒ **最先登记的先试** | `src/L12_canonical/typeclass.rs:338-344`、`:366-367`（注释 `// Try instances from the beginning (more specific first).`） |
| L13 | 同 L12（登记序） | `docs/typeclass-syntax.md` 与 prelude 注释 `src/prelude/hdl/hdl-types.typort:297-299`「MUST stay last」 |

L12 的 `assertion_table` 从 `HashMap` 改为 `Vec<(Assertion, TableEntry)>` +
`find_assertion_entry`，键相等用 `vals_eq_ground`（**Flex 等于一切**）
（`src/L12_canonical/typeclass.rs:296-303`）：

```rust
    /// Find an assertion entry in the table by name and argument matching.
    fn find_assertion_entry(&self, target: &Assertion) -> Option<usize> {
        self.assertion_table.iter().position(|(a, _)| {
            if a.name != target.name || a.arguments.len() != target.arguments.len() {
                return false;
            }
            a.arguments.iter().zip(&target.arguments).all(|(x, y)| Self::vals_eq_ground(x, y))
        })
    }
```

### 4.6 实例侧一阶匹配 `match_typ` / `val_match`

**L10（`Typ` 世界）**（`src/L10_typeclass/typeclass.rs:389-429`）：

```rust
/// 一阶结构匹配：`goal`（目标，视为已确定）对 `pattern`（实例断言，可含实例
/// 类型参数 `Typ::Var`）。只有 **pattern 侧** 的 `Var` 允许被绑定；目标侧的
/// `Var`（泛型 rigid）不得被实例构造子"吃掉"。
///
/// 旧实现是双向 `subst.insert`（且无 occurs check），会让
/// `impl[T] Say for List[T]` 假匹配泛型目标 `Say[T]`：`Say[Var(0)]` 对
/// `Say[Construct("List", [Var(0)])]` 把目标 rigid 绑成 `List[..]` 而静默选出
/// 错误实例（`f two` 错答 "list"）。L12/L13 的 `val_match` 就是这套单向语义，
/// 此处按 `Typ` 镜像。
fn match_typ(goal: &Typ, pattern: &Typ, subst: &mut Subst) -> bool {
    let goal = apply_subst_to_typ(goal, subst);
    let pattern = apply_subst_to_typ(pattern, subst);

    match (&goal, &pattern) {
        (Typ::Var(i), Typ::Var(j)) if i == j => true,
        // pattern 侧变量：绑定目标值；已绑定则要求与既有绑定结构相等
        (_, Typ::Var(j)) => match subst.get(j) {
            Some(existing) => existing == &goal,
            None => { subst.insert(*j, goal); true }
        },
        // `Any` 是 trait_wrap 给 out_param 填的通配，与任何目标值匹配
        (Typ::Any, _) | (_, Typ::Any) => true,
        // 目标侧的 rigid 不能与实例构造子匹配（假匹配根因）
        (Typ::Var(_), _) => false,
        (Typ::Val(s1), Typ::Val(s2)) => s1 == s2,
        (Typ::Construct(n1, args1), Typ::Construct(n2, args2)) => {
            n1 == n2 && args1.len() == args2.len()
                && args1.iter().zip(args2).all(|(a1, a2)| match_typ(a1, a2, subst))
        }
        (Typ::Fn(a1, b1), Typ::Fn(a2, b2)) => {
            match_typ(a1, a2, subst) && match_typ(b1, b2, subst)
        }
        _ => false,
    }
}
```

**L12（`Val` 世界）**：`val_match`（`src/L12_canonical/typeclass.rs:123-193`）
把 `Flex` 两侧都当通配：

```rust
        match (a, b) {
            // Flex (unsolved meta) in either side matches anything
            (Val::Flex(..), _) | (_, Val::Flex(..)) => true,
            // Rigid vars - must be same level with empty spines
            (Val::Rigid(x1, sp1), Val::Rigid(x2, sp2)) if x1 == x2 && sp1.is_empty() && sp2.is_empty() => true,
            // Rigid var in instance pattern (empty spine) - bind to ground goal value.
            // 单向一阶匹配（对齐 L10/L11 的 `match_typ`，d4c05ea 同族）：
            // 只允许**实例侧** rigid 变量被绑定；目标侧的裸 rigid（调用方的
            // 泛型变量）不得被实例构造子"吃掉"……
            (_, Val::Rigid(x, sp)) if sp.is_empty() => {
                if let Some(existing) = subst.get(&x.0) {
                    Self::vals_eq_ground(a, existing)
                } else {
                    subst.insert(x.0, a.clone());
                    true
                }
            }
            (Val::Decl(x1, sp1), Val::Decl(x2, sp2)) => { ... }
            (Val::Sum(n1, p1, _, _), Val::Sum(n2, p2, _, _)) => { ... }
            (Val::SumCase { case_name: n1, datas: d1, .. }, Val::SumCase { case_name: n2, datas: d2, .. }) => { ... }
            (Val::U(x1), Val::U(x2)) => x1 == x2,
            (Val::LiteralType, Val::LiteralType) => true,
            (Val::Obj(a1, n1, sp1), Val::Obj(a2, n2, sp2)) => { ... }
            _ => false,
        }
```

**`val_match` 规格（形式化时最该注意的）**：

```
val_match goal pattern σ:
  goal = Flex _                        → true        （未解实参容忍）
  pattern = Flex _                     → true
  goal = Rigid x [], pattern = Rigid x []  → true
  pattern = Rigid x []                 → if x ∈ dom σ then vals_eq_ground goal (σ x)
                                          else σ := σ[x ↦ goal]; true
  goal = Rigid _ _（非裸）              → false       （目标 rigid 不得被吃掉）
  同名构造子/Decl/Sum/SumCase          → 逐位 val_match（Decl/Obj 还要求 icit 相等）
  U(x) vs U(y)                         → x == y
  其它                                 → false
```

`vals_eq_ground`（`src/L12_canonical/typeclass.rs:196-249`）**把 Flex 视为等于
一切**（`:203-205`）：

```rust
            // Flex（未解 meta）视为等于一切：与 `val_match` 的 Flex 宽放
            // 同一策略（实例匹配容忍未解实参，靠后续 refine），刻意语义。
            (Val::Flex(..), _) | (_, Val::Flex(..)) => true,
```

`Match` 的比较要求分支体 `Rc::ptr_eq`（`:235-246`）。

### 4.7 三个触发点：`solve_multi_trait` / `solve_trait` / `fresh_meta`

**(1) `solve_multi_trait`：def 体检查后批量扫未解 meta**

`src/L12_canonical/unification.rs:491-507`（L10 同构 `unification.rs:449-465`）：

```rust
    pub fn solve_multi_trait(&mut self, cxt: &Cxt, m: MetaVar) -> Result<(), UnifyError>{
        let prepare = self.meta.get(m.0 as usize ..)
            .iter()
            .flat_map(|x| x.iter())
            .enumerate()
            .flat_map(|x| if let MetaEntry::Unsolved(v, _, _) = x.1 { Some((x.0, v.clone())) } else { None })
            .collect::<Vec<_>>();
        for (idx, x) in prepare {
            let typ = self.solve_trait(cxt, &x)
                .map_err(UnifyError::Trait)?;
            if let Some((_, val)) = typ {
                self.meta[idx + m.0 as usize] = MetaEntry::Solved(val, x);
            }
        }
        Ok(())
    }
```

调用点：
- `Decl::Def` 的体检查**之后**（`src/L10_typeclass/elaboration.rs:367-368`、
  `src/L12_canonical/elaboration.rs:391-392`），从**本次 def 开始时**的 meta
  下标起扫（L12 用 `this_meta = self.meta.len()` 记录，
  `src/L12_canonical/elaboration.rs:372`）。失败 → `Error` 带 `Trait` 文案。
- `unify` 的 flex 求解臂之后重新扫（`src/L12_canonical/unification.rs:752`、
  `:763`）：因为新解可能引入新的 trait 型 meta。
- `flex_flex` 解内层 meta 之后（`src/L12_canonical/unification.rs:603`）。

**(2) `solve_trait`：Val → 求解器 → 回 Val**

`src/L12_canonical/unification.rs:508-564`（**逐字**；L10
`unification.rs:466-507` 同构，差别仅在 L10 用 `force_deep().to_typ()`
转 `Typ`、`x` 是 `Rc<Val>`）：

```rust
    pub fn solve_trait(&mut self, cxt: &Cxt, x: &Rc<Val>) -> Result<Option<(Rc<Tm>, Rc<Val>)>, String> {
        // 精化 σ 包裹的接收者先推开（子句体内引用被解槽时会出现）
        let x = self.force(&cxt.decl, x);
        if let Val::Sum(name, params, _, true) = x.as_ref() {
            let out_param = if let Some(o) = self.trait_out_param.get(&name.data) {
                o
            } else {
                return Ok(None)
            };
            // Collect non-output param values directly as Val.
            // Skip if any param contains unsolved metas (Flex) - let unification handle later.
            let params: Vec<Rc<Val>> = params
                .iter()
                .zip(out_param)
                .filter(|(_, x)| !**x)
                .map(|x| x.0)
                .map(|(_, tm, _, _)| self.force_deep(&cxt.decl, tm))
                .collect();
            // If any param is still Flex (unsolved meta), bail out
            if params.iter().any(|v| matches!(v.as_ref(), Val::Flex(..))) {
                return Ok(None);
            }
            self.trait_solver.clean();
            if let Some(a) = self.trait_solver.synth(Assertion {
                name: name.data.clone(),
                arguments: params.clone(),
            }) {
                let ret = self.infer_expr(cxt, Raw::Var(a));
                let (tm, _) = self.insert(cxt, ret)
                    .map_err(|e| e.0.data)?;
                let val = self.eval(&cxt.decl, &cxt.env, &tm);
                if let Val::SumCase { typ, .. } = val.as_ref() {
                    let _ = self.unify_catch(cxt, typ, &x, empty_span(()));
                }
                Ok(Some((tm, val)))
            } else {
                Err(format!(
                    "solve trait failed: {}[{:?}]\n{}",
                    name.data,
                    params.iter().map(|v| format!("{:?}", v)).collect::<Vec<_>>().join(", "),
                    self.trait_solver
                        .class_instances
                        .get(&name.data)
                        .unwrap_or(&vec![])
                        .iter()
                        .map(|x| format!("{:?}", x))
                        .reduce(|a, b| a + "\n" + &b)
                        .unwrap_or_default(),
                ))?
            }
        } else {
            Ok(None)
        }
    }
```

**注意 `synth` 前必 `clean()`**（清空 generator/resume/表/root_answer），
所以**答案表是每次求解内部缓存，不跨调用**（`src/L10_typeclass/typeclass.rs:175-180`）。

**L10 与 L12 在"实参收集"上的一处真实分歧**（形式化时不要合并）：

- **L10** 用 **`flat_map(… to_typ())`**（`src/L10_typeclass/unification.rs:481-487`）：
  某个非 out 实参 `to_typ()` 为 `None`（未解 meta、字面量类型、Pi…）时**静默
  丢参** → 断言 arity 变短 → `try_resolve` 的 arity 检查几乎必然失配 →
  "no instance"。**不会**选出错误实例（`typeclass.rs:45-58` 有长注释论证这是
  刻意语义）。
- **L12** 收集**全部**（含 Flex）实参，然后 **任一仍 `Flex` 就 `Ok(None)` 交回
  合一**（`src/L12_canonical/unification.rs:519-532`），**不丢参**。

**`new_trait` 是覆盖写**（`src/L10_typeclass/typeclass.rs:164-166`）：

```rust
    pub fn new_trait(&mut self, name: String) {
        self.class_instances.insert(name, vec![]);
    }
```

**重复声明同名 trait 会清空该 trait 的既有实例表**；而
`impl_trait_for` 是 `entry().or_default().push`（追加）。

**(3) `fresh_meta`：期望类型是 trait Sum 时急切求解**（§1.3 已引）。

### 4.8 `trait_wrap`：接收者方法调用 `x.foo y`

L12（`src/L12_canonical/elaboration.rs:1167-1298`），与 L10
（`elaboration.rs:1009-1099`）同构，L12 多了 inherent 方法（`namespace`）与
补全表。核心三段：

```rust
    fn trait_wrap(&mut self, cxt: &Cxt, t: Span<SmolStr>, a: Rc<Val>, x: Box<Raw>, tm: Rc<Tm>, t_span: Span<()>) -> Result<(Rc<Tm>, Rc<Val>), Error> {
        let typ_raw = self.eval(&cxt.decl, &cxt.env, &self.quote(&cxt.decl, cxt.lvl, &a));
        // Wildcard Val: Flex metavariables match anything in val_eq
        let wildcard_val: Rc<Val> = Val::Flex(MetaVar(u32::MAX), List::new()).into();
        ...
        {
            let traits = self.trait_definition
                .clone()//TODO: can remove this clone?
                .iter()
                .flat_map(|(trait_name, (trait_params, out_param, methods))| {
                    methods.iter()
                        .find(|x| x.0.data == t.data)
                        .map(|x| (trait_name, trait_params, out_param, x))
                })
                .filter(|(x, _, out_param, _)| {
                    let len = out_param.iter().filter(|x| !**x).count();
                    let mut args = vec![typ_raw.clone()];
                    for _ in 1..len { args.push(wildcard_val.clone()); }
                    self.trait_solver.clean();
                    self.trait_solver.synth(Assertion { name: x.clone().clone(), arguments: args }).is_some()
                })
                .map(|(trait_name, trait_params, _, (methods_name, methods_params, ret_type))| (
                    trait_name.clone(),
                    {
                        let params = {
                            let mut params = trait_params.clone();
                            params.push((methods_name.clone().map(|_| SmolStr::new("$this")),
                                         Raw::Var(methods_name.clone().map(|_| SmolStr::new("Self"))),
                                         Icit::Expl));
                            params.push((methods_name.clone().map(|_| SmolStr::new("$$")),
                                         trait_params.iter().map(|x| x.0.clone())
                                             .fold(Raw::Var(methods_name.clone().map(|_| SmolStr::new(trait_name))),
                                                   |ret, x| Raw::App(Box::new(ret), Box::new(Raw::Var(x)), Either::Icit(Icit::Impl))),
                                         Icit::Impl));
                            params.append(&mut methods_params.clone());
                            params
                        };
                        let body = std::iter::once((Raw::Var(methods_name.clone().map(|_| SmolStr::new("$this"))), Icit::Expl))
                            .chain(methods_params.iter().map(|x| (Raw::Var(x.0.clone()), x.2)))
                            .fold(
                                Raw::Obj(Box::new(Raw::Var(methods_name.clone().map(|_| SmolStr::new("$$")))), Some(methods_name.clone())),
                                |ret, (x, icit)| Raw::App(Box::new(ret), Box::new(x), Either::Icit(icit))
                            );
                        Raw::Let(
                            methods_name.clone().map(|x| SmolStr::new(format!("${x}"))),
                            Box::new(params.iter().rev().fold(ret_type.clone(), |a, b| {
                                Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                            })),
                            Box::new(params.iter().rev().fold(body.clone(), |a, b| {
                                Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a))
                            })),
                            Box::new(Raw::App(
                                Box::new(Raw::Var(methods_name.clone().map(|x| SmolStr::new(format!("${x}"))))),
                                x.clone(), Either::Icit(Icit::Expl),
                            )),
                        )
                    }
                ))
                .collect::<Vec<_>>();
            //TODO: if traits.len() > 1, return err
            let traits = traits.first().and_then(|(_, decl)| self.infer_expr(cxt, decl.clone()).ok());
            if let Some(ret) = traits { Ok(ret) } else {
                Err(Error(t.clone().map(|t| format!(
                    "`{}`: {} has no object `{}`",
                    super::pretty_tm(0, cxt.names(), &tm),
                    super::pretty_tm(0, cxt.names(), &self.nf(&cxt.decl, &cxt.env, &self.quote(&cxt.decl, cxt.lvl, &a))),
                    t,
                )), vec![]))
            }
        }
    }
```

**规则（方法调用脱糖）**：`x.m a₁ … aₙ` 中

1. 在 `trait_definition` 的全部 trait 里找**同名方法** `m` 的候选；
2. 对每个候选构造断言 `T[τ, ⊥, …, ⊥]`（`τ` = 接收者类型的求值，out 位填
   `Flex(max, [])` 通配），用 `Synth` 试解；
3. 命中后合成：

```
let $m : Π (Self : Impl) ($this : Self) ($$ : T[Self, 参数…]) (方法参数…) . R
      := λ (Self) ($this) ($$) (参数…). $$.m $this 参数…
in  $m  x a₁ … aₙ
```

即**字典传递**：`$$` 是由常规隐式插入给出的实例值，
`$$.m $this 参数…` 是对象投影 + 应用。

4. **多个候选命中不报歧义**：源码 `//TODO: if traits.len() > 1, return err`
   后直接 `traits.first()`（`src/L12_canonical/elaboration.rs:1282-1283`）；
   候选枚举走 `trait_definition`（HashMap）迭代，**顺序不确定**。
5. 找不到 → `"`{expr}`: {类型} has no object `{方法名}`"`。
6. **候选谓词只看 receiver 头**：试解时除 `Self` 位外**全部实参填
   `Typ::Any` 通配**（`src/L10_typeclass/elaboration.rs:1019-1024`；
   L12 同理但用 `Flex(max,[])`，`src/L12_canonical/elaboration.rs:1219-1224`），
   而 `match_typ`/`val_match` 的 `Any`/`Flex` 臂恒真——即"这个方法名是否
   对**某个** trait 的**该 receiver 头**可解"。
7. **`.first()` 之后不回退**：若第一个候选的 `infer_expr` 失败，**不会**
   试下一个候选，直接报 `has no object`（`src/L10_typeclass/elaboration.rs:1081-1094`）。
8. **一次 `x.m` 通常触发两次实例求解**：一次是候选谓词（`Any` 通配），
   一次是合成项里 `$$` 的隐式 Π 域被 `insert_go → fresh_meta → solve_trait`
   真正求解（`src/L10_typeclass/elaboration.rs:1042-1050` 的 `$$` 参数 +
   `src/L10_typeclass/mod.rs:574`）。因此 `trait_wrap` 的性能特征与
   求解器缓存策略强相关（`docs/opt-typeclass.md:29-35`）。

### 4.9 失败报告

| 层 | 失败形态 | 锚点 |
|---|---|---|
| `Synth` 内部循环超限 | **`panic!("Too much effort :(")`**（崩溃，不是类型错误） | `src/L10_typeclass/typeclass.rs:222-223`、`src/L12_canonical/typeclass.rs:314-315` |
| 未注册 trait | `class_instances.get(...).unwrap()` → panic | `src/L10_typeclass/typeclass.rs:299`、`src/L12_canonical/typeclass.rs:365` |
| resume 空子目标 | `panic!("Cannot resume with empty subgoals.")` | `src/L10_typeclass/typeclass.rs:268`、`src/L12_canonical/typeclass.rs:336` |
| 求解失败（无实例） | `Err("solve trait failed: {Trait}[{参数}]" + 可用实例表)` | `src/L10_typeclass/unification.rs:502`、`src/L12_canonical/unification.rs:547-559` |
| def 检查后仍有未解 meta 且其类型是 trait Sum | 三条细分文案（见下） | `src/L12_canonical/elaboration.rs:395-430` |
| 其它残留 meta | `find unsolved meta with type `{类型}`` | `src/L12_canonical/elaboration.rs:431-436` |

L12 细分文案（`src/L12_canonical/elaboration.rs:395-430`）：

```rust
                        let err_msg = if let Val::Sum(name, params, _, true) = oty.as_ref() {
                                let has_flex = params.iter().any(|(_, val, _, _)| {
                                    matches!(self.force(&cxt.decl, val).as_ref(), Val::Flex(..))
                                });
                                let instances = self.trait_solver.class_instances.get(&name.data);
                                if has_flex {
                                    format!("cannot infer typeclass `{}`: type parameter is unknown", name.data)
                                } else if params.is_empty() {
                                    format!("no instance of typeclass `{}`", name.data)
                                } else {
                                    ...
                                    if instances.map_or(true, |i| i.is_empty()) {
                                        format!("no instance of typeclass `{}` for types `{}`", trait_repr, first)
                                    } else {
                                        format!(
                                            "no matching instance of typeclass `{}` for types `{}`\navailable instances: {}",
                                            trait_repr, first,
                                            insts.iter().map(|i| i.lvl.data.to_string()).collect::<Vec<_>>().join(", "),
                                        )
                                    }
                                }
                            } else {
                            format!("find unsolved meta with type `{}`", ...)
                        };
```

**检测机制**：`Tm::no_metas(self, decl, l) -> Option<(Cxt, Val)>`
（`src/L12_canonical/mod.rs:102-125`）在项里找**第一个**未解 meta，返回其
**创建时的 `Cxt` 快照**与 `origin_typ`：

```rust
            Tm::Meta(m) => match infer.lookup_meta(*m) {
                MetaEntry::Unsolved(_, cxt, oty) => Some((cxt.as_ref().clone(), oty.clone())),
                MetaEntry::Solved(v, _) => infer.quote(decl, l, v).no_metas(infer, decl, l),
            },
```

### 4.10 解析一个隐式实例实参的 typing rule（形式化用）

把 §4.2–§4.9 压成规则。设 `Γ` 为上下文，`T` 为 trait 名，
`out(T) ∈ Bool*` 为其 out 掩码（`|out(T)| = 参数数`）。

**（R-Trait-Goal）** 求解目标：

```
Γ ⊢ τ ⇝ Sum(T, [p₀, …, p_k], _, true)        out(T) 已登记
ps = [ force_deep pᵢ | i ≤ k, ¬out(T)ᵢ ]     每个 ps 都不是未解 Flex
Synth(T, ps) = Some ℓ
──────────────────────────────────────────────────────────────────
Γ ⊢ solve_trait(τ) ⇝ (实例项, 实例值) := (infer_expr(Var ℓ), eval 之)

（附带：若实例值是 SumCase{typ,…}，则 unify_catch typ τ）
```

**（R-Trait-Meta）** `fresh_meta` 中期望类型是 trait Sum：

```
Γ ⊢ solve_trait(τ) ⇝ Some e
──────────────────────────────
Γ ⊢ fresh_meta(τ) ⇝ e          （不创建 meta）
```

**（R-Trait-Defer）** 求解失败或参数含未解 Flex：

```
solve_trait(τ) ⇝ None
─────────────────────────────────────────────────
Γ ⊢ fresh_meta(τ) ⇝ Meta ?m : τ     （推迟，等 solve_multi_trait）
```

**（R-Def-Body）** def 体检查完毕后的批量求解：

```
∀ ?mᵢ ∈ metas[this_meta ..] . ?mᵢ 未解
∀ i . solve_trait(Γ(?mᵢ)) = Ok vᵢ = Some eᵢ        （某个失败即 Trait 错误）
────────────────────────────────────────────────────────────────────
?mᵢ := eᵢ ；再检查 no_metas（失败 → §4.9 文案 + 可选 iddfs 重试）
```

**（R-Method-Call）** 接收者方法调用（§4.8 的 `trait_wrap`）：

```
τ = eval(接收者类型)
∃T, m. T 的方法表含 m ∧ Synth(T, [τ, ⊥…]) = Some ℓ    （⊥ = Flex(max,[])）
────────────────────────────────────────────────────────────────────────
Γ ⊢ x.m a⃗ ⇝ let $m = λSelf $this $$ a⃗. $$.m $this a⃗  in  $m x a⃗
```

**（R-Instance-Reg）** impl 登记：

```
impl[…] T[θ⃗] for τ' { def m⃗ }  ⇒
  Instance { assertion = T[τ', θ⃗ 去掉 out 位], dependencies = [], lvl = "T{τ'…}" }
  并登记 Decl::Def{ name = "T{τ'…}", typ = T τ' θ⃗, body = T.mk τ' θ⃗ (λthis ps. body)⃗ }
```

### 4.11 prelude 中的 trait / 实例（实测清单）

`src/prelude/**/*.typort` 共 **29 个 `trait` 声明、约 170 个实例**（含 5 个
blanket）。核心声明（逐字）：

```typort
/// Wrap a value as an output (`outParam`) type argument.  Used in trait
/// headers to mark the result type that the instance solver should infer.
def outParam[A](a: A): A = a

/// Addition: `this + that`.  `O` is the (solver-inferred) result type.
trait Add[T, O: outParam(Type 0)] {
    /// Add `that` to `this`, producing `O`.
    def +(that: T): O
}
```
（`src/prelude/core/op.typort:17-25`）

```typort
/// Conversion into a target type: `x.into`.
trait Into[O: outParam(Type 0)] {
    /// Convert `this` into `O`.
    def into: O
}

impl[T] Into[T] for T {
    def into: T = this
}
```
（`src/prelude/core/op.typort:67-75`）

```typort
/// Types that can be rendered as a `String`.
trait Show {
    /// Render `this` as a string.
    def show: String
}

impl Nat {
    /// Render a `Nat` in decimal.
    def show: String = nat_to_dec this
}
```
（`src/prelude/show.typort:13-22`——注意 `Nat` 走**固有 impl**，`Show` 的 32
个实例里**没有 `Nat`**；这与 §4.8 的"零参数方法 + `$$` 隐式实参"缺陷、
`docs/trait-system-analysis.md:590` Bug 1 一致）

| trait | 声明 | 实例数（代表） |
|---|---|---|
| `Show` | `src/prelude/show.typort:14` | 32（Int/Boolean/Ordering/Unit/Void/String/List[…]/Option[…]/Product/Tuple2/Either/Result/…；**不含 Nat**） |
| `Add`/`Sub`/`Mul`/`Div`/`Rem` | `src/prelude/core/op.typort:22/28/34/40/142` | String/Int/Nat/HDL 类型 |
| `And`/`Or`/`Xor`/`Neg`/`Not` | `src/prelude/core/op.typort:46/52/58/100/136` | Boolean/Int |
| `Equal`/`Compare` | `src/prelude/core/op.typort:79/88` | Nat/Boolean/HDL 类型 |
| `Into` | `src/prelude/core/op.typort:68` | 41（最大户） |
| `Default` | `src/prelude/core/op.typort:106` | Unit/Nat/Boolean/`List[T]`/`Option[T]` |
| `Clone`/`Cast`/`Cons`/`LetNamed` | `op.typort:165`/`eq.typort:36`/`vec.typort:166`/`hdl-types.typort:248` | 各一个 blanket |
| `Cat`/`VEq`/`CaseEq`/`Data`/`RegNext`/`MemOps`/`RangeSyntax`/`Module`/`IMasterSlave`/`Bundle` | `hdl-ops.typort:468`/`hdl-verilog-compat.typort:82`/`:136`/`hdl-types.typort:60`/`hdl-signals.typort:705`/`hdl-clock.typort:73`/`hdl-core.typort:1185`/`:438`/`hdl-bus.typort:81`/`:185` | 1–13；后 3 个 prelude 内无实例（宏/derive 生成） |

**5 个 blanket impl**（Self 裸变量，`impl[T] T for T` 形态）：
`src/prelude/core/op.typort:73`（`Into`）、`:172`（`Clone`）、
`src/prelude/core/eq.typort:41`（`Cast`）、`src/prelude/data/vec.typort:171`（`Cons`）、
`src/prelude/hdl/hdl-types.typort:300`（`LetNamed`）。

**三点形式化必读**：

1. **`Eq` / `Ord` / `Num` / `Decidable` 都不是 trait**：`Eq` 是归纳恒等类型
   （`src/prelude/core/eq.typort:8` `enum Eq[A](x: A, y: A) { refl(a: A) -> Eq a a }`），
   typeclass 侧的对应物是 `Equal`（`op.typort:79`）；`Ord` ↔ `Compare`；
   数值能力拆成 `Add`/`Sub`/`Mul`/`Div`/`Rem`/`Neg`/`Default`；
   `Decidable` 是 `enum Dec[A]` + 固有 impl（`src/prelude/data/decidable.typort:5`）。
2. **`outParam(Type 0)` 是唯一的 out 参数写法**（9 个 trait 使用），且
   `outParam` 必须由用户自己 `def`（`op.typort:19`）。
3. **实例优先级 = 注册顺序，没有 canonical 注解、没有 specificity 比较**。
   prelude 唯一显式依赖此语义的位置（逐字）：

```typort
// Reflexive no-op fallback — MUST stay last (the trait solver takes the
// first registered matching instance). Covers every other receiver type:
// bundles, sub-module instances, Nat/String locals.
impl[T] LetNamed[T] for T {
    def mkNamed(name: String): T = this
}
```
（`src/prelude/hdl/hdl-types.typort:297-301`）

**prelude 用到的语法比设计文档保守**：无关联类型、无 supertrait、无
`static def`、无真 `#[derive(...)]`（仅在注释中出现）；`where` 只出现在**方法**
上（6 处，均为 `T: Into[Self]` 形态，生成隐参名 `_into_T`，
`src/prelude/hdl/hdl-types.typort:62`、`:102-104`）；`impl[...] Trait for T` 的
blanket 与 `impl[len: Nat] Show for Vec[Nat] len` 这类**泛型但无条件**的实例
都可表达，**唯独条件实例不行**——见 §6.6 的 `show.typort:9-11` 引文。

---

## 5. canonical 形式（L12）

### 5.1 "canonical"在此层是什么意思

> **命名澄清（形式化前必读）**：本仓 **`L12_canonical/` 里不存在
> `Canonical` / `Canon` 结构体或枚举，也没有 `canonicalize`/`is_canonical`
> 函数**（全目录 grep 为 0 命中）；`canonical` 只是**模块名**
> （`src/L12_canonical/mod.rs:20` `mod canonical;`）与仓库层面的一句定位
> （根 `README.md:147`：`| L12_canonical | Canonical forms for typeclass resolution |`）。

代码里 "canonical" 落在**三件互不相同的事**上：

**(a) 项的"已 canonical/已闭"判据 `Tm::no_metas`**——项中是否还有未解 meta。
这是 canonical 搜索的**触发谓词**（`src/L12_canonical/mod.rs:102-125`，
逐字见 §4.9）。命中则返回**第一个**未解 meta 的 `(创建时 Cxt, 原始类型)`。

**(b) 检查模式 `check::<const CANONICAL: bool>`**（`src/L12_canonical/elaboration.rs:274`）：
`check::<true>` 走**严格 `unify`**（`self.refuel()` + `unify(…, 100)`，
**不吞** `Stuck`、不产生 "unsolved meta" 诊断）；`check::<false>` 走
`unify_catch`（带 `meta_contrains` 挂账与 `can't unify for unsolved meta`
文案）。canonical 搜索内部一律用 `check::<true>`（`canonical.rs:114`）。

```rust
// src/L12_canonical/elaboration.rs:336-359
            // General case: infer type and unify
            (t, _) => {
                let t_span = t.to_span();
                let x = self.infer_expr(cxt, t);
                let (t_inferred, inferred_type) = self.insert(cxt, x)?;
                if CANONICAL {
                    // 顶层合一入口：充值 fuel 池（L08 前向传播的护栏纪律）
                    self.refuel();
                    self.unify(cxt.lvl, cxt, &a, &inferred_type, 100).map_err(|e| {
                        let err = match e {
                            super::UnifyError::Basic | super::UnifyError::Stuck => format!(
                                "can't unify\n  expected: {}\n      find: {}",
                                super::pretty_tm(0, cxt.names(), &self.quote(&cxt.decl, cxt.lvl, &a)),
                                super::pretty_tm(0, cxt.names(), &self.quote(&cxt.decl, cxt.lvl, &inferred_type)),
                            ),
                            super::UnifyError::Trait(e) => e,
                        };
                        Error(t_span.map(|_| err.clone()), vec![])
                    })?;
                } else {
                    self.unify_catch(cxt, &a, &inferred_type, t_span)?;
                }
                Ok(t_inferred)
            }
```

**(c) canonical 项搜集合成本身**——`canonical.rs` 的 `iddfs`/`search`：
给定一个目标类型 `σ`，在（局部变量 + decl 表）中找一个候选头，把它的 Π
telescope 用 fresh meta 实例化，令其结果类型与 `σ` 合一，再递归地搜索它的
显式实参——即"构造一个 canonical（正规）项"。它只在**错误恢复 / quickfix**
路径被调用，且**不建任何表、不做记忆化**（§5.2、§5.5）。

L12 的 `canonical` **不是**"实例解析的规范化"——恰恰相反，L12 相对 L10
**删掉了** goal 的 `Typ` canonicalization（§5.4）。

定义依据：`src/L12_canonical/README.md:3-6`：

```
本层在 L11（宏展开）之上再叠三件事：**trait 求解器 Val 级重写**
（`typeclass.rs` 移除 `Typ` 桥接，求解器直接匹配 `Val`）、**`Val::Call`
内联节点**……**canonical 搜索**（`canonical.rs` 的 `iddfs`/`search`，Err 重试路径专属）；
```

以及 `src/L12_canonical/README.md:306-308`：

```
- **canonical/`iddfs` 不移植**：参考版只在 Err 路径的重试闭包
  （`elaboration.rs` 的 `ret = move || infer.iddfs(...)`）调用，不影
  响判定与 Ok 输出，快版无搜索机。
```

### 5.2 `iddfs` 与 `search`（**全文逐字**）

`src/L12_canonical/canonical.rs:8-31`：

```rust
    pub fn iddfs(
        &mut self,
        cxt: &Cxt,
        target: &[Rc<Val>],
        origin_cxt: &Cxt,
        origin_target: &Rc<Val>,
        raw: Rc<dyn Fn(List<Raw>) -> Raw>,
        depth: u32,
        target_limit: usize,
        avoid_recurse: &str,//TODO: this is incorrect
    ) -> Result<String, UnifyError> {
        let mut basic_target_limit = 1;
        // 预算逐步递增至含 target_limit（修复旧 `+= 2` + `<` 的跳档：偶数
        // 预算与最终预算永不尝试——调用方授权的 target_limit 恰为奇数时
        // 最后一档必然跳过，完备性缺口）。iddfs 仅由 LSP quickfix 的重试
        // 闭包触达（`run`/`run_fast` 不经此路径），预算细化不影响测试口径。
        while basic_target_limit <= target_limit {
            if let Ok(s) = self.search(cxt, target, origin_cxt, origin_target, raw.clone(), depth, basic_target_limit, avoid_recurse) {
                return Ok(s);
            }
            basic_target_limit += 1;
        }
        Err(UnifyError::Basic)
    }
```

`search`（`src/L12_canonical/canonical.rs:32-152`）关键段：

```rust
        if depth == 0 || target.len() > target_limit {
            return Err(UnifyError::Basic);
        } else {
            let mut typ = self.force(&cxt.decl, &target[0]);
            let mut cxt = cxt.clone();
            let mut lamb = List::new();
            while let Val::Pi(span, icit, dom, clos) = typ.as_ref() {
                let lvl = cxt.lvl;
                if *icit == Icit::Expl { lamb = lamb.prepend(span.data.clone()); }
                cxt = cxt.bind(span.clone(), self.quote(&cxt.decl, cxt.lvl, dom), dom.clone());
                typ = self.closure_apply(&cxt.decl, clos, Val::vvar(lvl).into());
            }
            let names = cxt.names();
            let iterator = names.iter()
                .map(|t| { let (l, (_, v)) = &cxt.src_names.get(t).unwrap(); ... })
                .chain(cxt.decl.iter().map(|t| (t.0.clone(), &t.1.4, t.1.2.clone())))
                .filter(|(t, _, _)| ![
                    "create_global", "change_mutable", "change_mutable_default",
                    "string_to_global_type", "string_concat", "get_global",
                    "outParam", avoid_recurse].contains(&t.as_str()));
            for (t, v, mut vtm) in iterator {
                let mut vt = v.clone();
                let mut new_list = vec![];
                while let Val::Pi(span, icit, dom, clos) = vt.as_ref() {
                    let icit = *icit;
                    let new_meta = self.fresh_meta(&cxt, dom.clone());
                    let meta = self.eval(&cxt.decl, &cxt.env, &new_meta);
                    if icit == Icit::Expl { new_list.push(dom.clone()); }
                    vt = self.closure_apply(&cxt.decl, clos, meta.clone());
                    vtm = self.v_app(&cxt.decl, &vtm, meta, icit);
                }
                ...
                self.refuel();
                if matches!(self.unify(cxt.lvl, &cxt, &vt, &typ, 5), Ok(_) | Err(UnifyError::Stuck))
                    && self.check::<true>(origin_cxt, raw.clone()(raw_list), origin_target).is_ok() {
                        ...
                        if new_list.is_empty() {
                            if !target.get(1..).map(|x| x.is_empty()).unwrap_or(true) {
                                if let Ok(ret) = self.search(&cxt, &target[1..], origin_cxt, origin_target, ..., depth, target_limit - 1, avoid_recurse) { return Ok(ret) }
                            } else {
                                return Ok(format!("{}", raw(List::new().prepend(this_raw))))
                            }
                        } else if let Ok(ret) = self.search(&cxt, &[new_list, target[1..].to_vec()].concat(), origin_cxt, origin_target, ..., depth - 1, target_limit - 1, avoid_recurse) {
                            return Ok(ret)
                        }
                }
                self.meta_contrains.clear();
            }
        }
        Err(UnifyError::Basic)
```

**算法规格**：

```
search Γ [g₀, g₁, …, gₙ] depth budget avoid:
  if depth = 0 ∨ n+1 > budget → fail
  Δ := Γ 扩展 g₀ 的 Π telescope（每个隐式/显式 binder 都进上下文；
       `lamb` 收集显式 binder 名）
  对每个候选头 h ∈ (局部变量 ∪ decl 表) \ {builtins, outParam, avoid}：
      (v_h, 其类型) := h
      把 v_h 的 Π telescope 用 fresh meta 实例化，得到 vt；
      显式实参位置收集进 new_list
      this_raw := h 应用到 |new_list| 个 Hole，外面包 |lamb| 层 λ
      重充 fuel；若 unify(5) vt g₀ 成功（或 Stuck）且
         check(origin_cxt, raw(this_raw :: holes), origin_target) 成功：
          if new_list 为空：
              若没有剩余目标 → 返回 raw([this_raw])
              否则 search [g₁…] depth (budget-1)
          else search (new_list ++ [g₁…]) (depth-1) (budget-1)
      失败则 meta_contrains.clear()  （回滚本次候选的挂账）
  fail
```

关键点（**形式化必须保留的细节**）：

1. **两层预算**：`depth`（每用一个**带显式实参**的候选减 1）与 `target_limit`
   （剩余目标数上限，每步减 1）。`iddfs` 对 `target_limit` 做 **1,2,3,…,limit
   的迭代加深**，`depth` 由调用方固定。
2. **候选集合**：局部变量 + decl 表全部条目，**硬编码黑名单**（6 个 builtin +
   `outParam` + `avoid_recurse`）。
3. **`avoid_recurse`** = 当前正在检查的 def 名（`src/L12_canonical/elaboration.rs:455`
   传 `&name.data`），防止"用自己证明自己"；源码注释自陈
   `//TODO: this is incorrect`（`canonical.rs:17`、`:41`）。
4. **探测的"成功"判定**：`unify` 成功 **或** `Stuck`（挂账算通过），**并且**
   用 `check::<true>` 在**原始上下文/原始目标**下真的把合成的 `Raw` 检查一遍。
   这是一次"用 elaborator 自身当判定器"的双重验证。
5. **回滚**：每个候选失败后 `self.meta_contrains.clear()`；每次探测前
   `self.refuel()`（`canonical.rs:110-112`）。
6. 结果不是项而是**字符串**（`Result<String, UnifyError>`），因为 `raw` 闭包
   负责把实参列表拼成 `Raw` 再由 `check` 渲染（`raw: Rc<dyn Fn(List<Raw>) -> Raw>`）。

### 5.3 与实例解析的关系

**两条路径分开**（`src/L12_canonical/README.md:188-208`、`:306-308`、
`src/L12_canonical/elaboration.rs:113-123`）：

- **实例解析**：`Synth`（tabled resolution，§4.5），在**正常检查路径**上；
- **canonical 搜索**：`iddfs`/`search`，**只在 `Decl::Def` 检查失败后构造的
  重试闭包里**（LSP quickfix 用），失败不影响判定与 Ok 输出。

调用点（`src/L12_canonical/elaboration.rs:445-462`）：

```rust
                        let ret = move || {
                            let mut infer = infer.clone();
                            infer.iddfs(
                                &meta_cxt,
                                &[oty.clone()],
                                &meta_cxt,
                                &oty,
                                Rc::new(|x| x.head().unwrap().clone()),
                                5,
                                6,
                                &name.data,
                            ).and_then(|x| if !infer.meta_contrains.is_empty() {
                                infer.meta_contrains.clear();
                                Err(super::UnifyError::Basic)
                            } else {
                                Ok(x)
                            }).ok()
                        };
                        return Err(Error(bod.to_span().map(|_|
                            err_msg.clone()
                        ), vec![Box::new(ret)]));
```

`depth = 5`、`target_limit = 6`。**canonicalization 不影响实例解析的语义**；
它只是"错误恢复时试着合成一个项"。

### 5.4 与 L10 的差异

| | L10 | L12 |
|---|---|---|
| 实例匹配世界 | `Val::to_typ()` → `Typ`（`typeclass.rs:18-70`） | 直接在 `Val` 上 `val_match` |
| 实例表 | `HashMap<Assertion, TableEntry>` | `Vec<(Assertion, TableEntry)>` + `vals_eq_ground` 查表 |
| 候选序 | 后登记先试 | 先登记先试 |
| `dependencies` | 恒空（`elaboration.rs:584`） | 恒空（`elaboration.rs:722`） |
| canonical 搜索 | 无 | `canonical.rs`（Err 重试专属） |
| `effort > 1000` | `panic!` | `panic!`（L13 起降级为 `None`） |
| 全局名 | `Infer.global: HashMap<Lvl, Val>` + 大下标哨兵 `1919810` | `Cxt.decl: decl 表` + `Tm::Decl(name)` |

### 5.5 形式化 canonical 搜索时必须照抄的 8 个细节

1. **无 `Canonical`/`Canon` 类型、无表、无记忆化**：整个 `canonical.rs`
   只有 `iddfs` 与 `search` 两个函数（`canonical.rs:1-153`）；候选池每次
   `search` 现物化（`:59-78`），答案不缓存。
2. **IDDFS 的加深维度是 `target_limit`，不是 `depth`**：`iddfs` 对
   `basic_target_limit = 1,2,…,target_limit` 各跑一遍从头 DFS
   （`canonical.rs:19-28`），`depth` 每轮都是调用方给的常数（唯一调用点给
   **`depth = 5`、`target_limit = 6`**，`src/L12_canonical/elaboration.rs:453-454`）。
   `depth` 只在"候选带显式实参"分支递减（`canonical.rs:143`），零实参分支
   不递减（`:128`）。
3. **探测的"成功"= 两个独立判据都通过**：`unify(cxt.lvl, &cxt, &vt, &typ, 5)`
   必须 `Ok` **或 `Err(UnifyError::Stuck)`**（`canonical.rs:113`），**并且**
   `check::<true>(origin_cxt, raw(raw_list), origin_target)` 必须 `Ok`
   （`:114`）。后者是"把合成的部分项（未合成位置填 `Raw::Hole`）拿回
   **原始**上下文与**原始**目标下再检查一遍"——用 elaborator 自身当判定器。
4. **Stuck 被当通过**：因为 `unify` 会把 `Stuck` 吞掉并挂账（§2.6），
   canonical 搜索显式把它当"可接受"，但**返回前会检查挂账**：
   `if !infer.meta_contrains.is_empty() { clear; Err(Basic) }`
   （`src/L12_canonical/elaboration.rs:456-461`）——"合成成功但仍有未兑现
   约束 ⇒ 视为失败"。
5. **逐候选只清挂账，不恢复 meta**：候选失败时唯一的清理是
   `self.meta_contrains.clear()`（`canonical.rs:147`）。**解掉的 meta 不回滚**
   （`solve` 已写 `MetaEntry::Solved`），`check::<true>` 里 `Raw::Hole`
   产生的 fresh meta 也不回收。唯一的粗粒度快照是重试闭包外的
   `let infer = self.clone();`（`elaboration.rs:437`）+ 闭包内
   `let mut infer = infer.clone();`（`:446`，`Infer` 是 `#[derive(Clone)]`），
   而**同一闭包内 1..=6 各档预算共用同一份 `infer`**——前档失败的解会带到
   后档。
6. **每次探测前 `self.refuel()`**（`canonical.rs:112`）：把共享 fuel 池重置为
   `UNIFY_FUEL = 4096`；第 5 个参数 `fuel = 5` 是**另一个**配额，只护
   `(Decl,_)`/`(_,Decl)` 的 `quote+eval` 重试臂（`src/L12_canonical/unification.rs:702-715`）。
   递归调用本身**不** refuel。
7. **候选序不确定**：候选池 = `cxt.names()`（局部 binder/let，**最新者在前**）
   **再** `cxt.decl.iter()`（`std::collections::HashMap`，**进程内随机序**），
   减黑名单（6 个内建 + `outParam` + `avoid_recurse`）。因此"多个候选都能
   合成"时**选出的项不保证确定**——形式化的搜索关系只能是
   `∃` 而非函数式。
8. **结果是 `String`（quickfix 文本），不是项**：`search : … -> Result<String, UnifyError>`，
   由 `raw : Rc<dyn Fn(List<Raw>) -> Raw>` 续延决定渲染；最终作为
   `Error(msg, vec![Box::new(ret)])` 的第 1 分量交给 LSP
   （`src/lib.rs:3658-3671`「Canonical Quick Fix」），失败表现为
   `"failed to find a solution"`。**它不影响本次 elaboration 的 Ok/Err 判定**
   （`src/L12_canonical/README.md:369-375`）。

---

## 6. 限制与缺口（各章自陈）

### 6.1 L03

`src/L03_holes/readme.md:288-307`：

- 解析失败只有 `parse error`，没有带位置报错（`:291-292`）。
- `basic` 的递归 eval/quote/unify/rename/solve 深度受线程栈限；深负载需
  `L03_STACK_MB` 调大（`:293-295`）。
- **解必须是"模式解"（spine 由互不相同的 rigid 变量构成）；非模式情形
  （如 `?m a a` 与 rhs 的合一、scope check 失败）报 Cannot unify——与上游
  一致（L05 才引入完整剪枝）**（`:299-301`）。← 形式化的关键边界。
- `nf`/`type` 对带 binder 的未解 hole 不 panic，未解 meta 一律以 spine
  应用形态引读（`:302-307`）。

### 6.2 L04

`src/L04_implicit/readme.md:129-144`：

- check/infer 与 parser 在 let 链上仍是递归，需深栈（`:131-133`）。
- pretty 的 Var 下标越界保留 panic（`:136-138`）。
- λ 体内的 `let` 曾与全局 def 位置冲突（已修，`:139-144`）。
- 两处历史 TODO 与上游同款：`BD` 不带 icit（`vAppBDs` 硬编码 `Expl`）、
  solve 的 `lams` 取 meta spine 的 icit（`readme.md:16-19`）。
- **`{u}` 位置隐式实参应用到显式 Pi 头 → `Function icitness mismatch`**
  （`:40-41`）；反方向在 check 侧被插 binder 捕获，不产生该错误。

### 6.3 L05

`src/L05_pruning/readme.md:129-153`：

- **`prune` 负载的 telescope 物化代价**：typed meta 的闭类型沿增长的
  define 链构造，绑定层下每次 `fresh_meta` 是 O(上下文深)
  （`:131-140`）。参考实现有 `close_meta_ty` 快捷（`:137-140`）。
- 深负载需大栈（`:141-143`）。
- **`intersect` 的长度失配分支（上游 `impossible`）：双实现均立即失败、
  零比较**——性能版 `if n1 != n2 { return false }`（刻意不比较共同前缀，
  避免前缀里的 flex 被提前求解）；参考版 `intersect_go` 返回 `None` 回落
  `unify_sp`，长度失配即 `Err`（`:145-149`）。
- pretty 的越界形态保留上游同款 panic（`:150-153`）。

### 6.4 L10

`src/L10_typeclass/README.md`：

- **`effort > 1000` → `panic!("Too much effort :(")`；这是崩溃面不是错误**
  （`:74-77`、`:345`；`typeclass.rs:219-224`）。
- `new_subgoal` 每子目标克隆实例表（`typeclass.rs:299`）、`trait_wrap` 每次
  调用克隆整个 `trait_definition`（`elaboration.rs:1008` 的
  `//TODO: can remove this clone?` 自证）——traitchain 参考版 268× 的候选
  因素，**归因未核实**（`:78-81`、`:333-337`）。
- 无 K 公理层面的安全保护（`:350`）。
- 构造子只以裸名登记；**重定义静默覆盖**（`:95-96`）。
- 卡住 match 的显示是 `(unsolved match …)` 简形（`:348-349`）。
- 匹配编译器三处收窄：覆盖只做顶层 + 嵌套位置；遮蔽只认通配臂；特化失败
  静默跳过（`:110-120`）。
- `unify` **有** fuel（`UNIFY_FUEL = 4096`，`mod.rs:448`）——早先 README 的
  "无 fuel" 已过时（`:87-89`）。
- **`solve_trait` 的"命中"判定不动元状态，但命中之后的
  `infer_expr`/`insert`/`eval`/`unify` 会写 meta，且没有 commit/rollback**；
  `solve_multi_trait` 中某个 meta 求解失败时**此前已解的 meta 保持已解**
  （`src/L10_typeclass/unification.rs:456-463`）。
- **`solve_trait` 末尾那次把实例 `typ` 与期望 Sum 合一的调用，失败被丢弃**
  （`let _ = self.unify(...)`，`unification.rs:497-499`）。

**L10 结构上未实现（代码 + README 共同确认）**：

| 未实现 | 证据 |
|---|---|
| `where` 子句 | 词法有、**无语法规则**（`parser/lex.rs:130` 是唯一引用） |
| supertrait / 父 trait | `p_trait_def` 无 `:` 分支（`parser/mod.rs:696-720`） |
| trait 方法默认体 | `p_def_declare` 无 `= body`（同处） |
| 关联类型 | `Decl::TraitDecl` 只有 `methods`（`parser/syntax.rs:192-196`） |
| 局部实例 | `// TODO: local instances should work too!`（`typeclass.rs:298`） |
| 实例依赖 / 实例上下文 | `Instance.dependencies` 恒 `List::new()`，全仓唯一构造点 `elaboration.rs:584` |
| 方法名跨 trait 重载 | 只取"第一个命中且可解"的 trait（`//TODO: if traits.len() > 1, return err`，`elaboration.rs:1080`） |
| `redefine` 检查 | 顶层名字重复静默覆盖（`README.md:95-96`） |

> **README 与代码的一处出入**：`src/L10_typeclass/README.md:30-32` 说"期望
> 类型是 trait Sum 时 `fresh_meta` 不做 pruning 应用、直接放一个**待解
> meta**（mod.rs:500-505）"；代码（`mod.rs:570-587`）**先 eager 调
> `solve_trait`**，只有失败或非 trait 才留待解 meta。**以代码为准**
> （该 README 的行号锚点也已过期）。

### 6.5 L12

`src/L12_canonical/README.md`：

- 快版孪生不移植 canonical/`iddfs`（`:369-370`）。
- `iddfs` 预算调度：`1,2,3,…,target_limit` 逐 1 递增；旧 `+= 2` 会在
  `target_limit` 为奇数时跳过最后一档，是**完备性缺口**（已修，`:371-375`）。
- **`vals_eq_ground` 把 Flex 视为等于一切**（`typeclass.rs:196`）——与
  `val_match` 的 Flex 宽放同一策略，**刻意语义**（`:376-377`）。
- 快版 `unify` 无 Decl 头展开燃料臂；`constraints`（Stuck 挂账）已移植
  （`:378-381`）。
- `no_metas` 为 quote 版；`declb_of` 无缓存（`:384-385`）。
- 参考版 `Cxt.decl` 按 `Rc` 共享，写时复制（`:386-387`）。
- 匹配编译器三处收窄（同 L10，`:110-120`）。
- 已知偏差：错误 span 全零、`?N` 编号不同（`:354-356`）；parity 套件剔除
  一批 GADT/struct 接收者/单臂构造子/Prim 时机用例（`:357-363`）。
- **canonical 搜索的自认缺陷**（`src/L12_canonical/canonical.rs`）：
  - `avoid_recurse` 的语义作者自陈不正确：两处 `//TODO: this is incorrect`
    （`canonical.rs:17`、`:41`）；
  - 候选池两处 `unwrap` 依赖"locals ⊆ src_names"（`canonical.rs:62-63`）——
    `clone_without_src_names()` 会制造违反该前提的上下文；
  - **复杂度**：无剪枝的全量候选 × 指数分支 + 每帧 `cxt.clone()`、
    `[new_list, target[1..]].concat()` 复制、`env.iter().nth(...)` 的
    O(n²) 取槽；终止性只由 `depth-1`/`target_limit-1` 双下降保证；
  - `depth` 恒 5，因此"需要更深显式实参链"的解**不会被更深地触及**；
  - 隐式 Π binder 被绑进候选池却不回包 λ（由后续 `check` 的隐式插入兜底）；
  - `vals_eq_ground_impl` 的 `visited: &mut HashMap<u32,u32>` 参数
    在函数体里**从未被写入或读取**——递归无环保护、无记忆化
    （`src/L12_canonical/typeclass.rs:200-249`）；
  - `typeclass.rs` 的生命周期兜底是 panic：`effort > 1000 → panic!("Too much effort :(")`
    （`:314-316`）与 `panic!("Cannot resume with empty subgoals.")`（`:336`）。

### 6.6 设计文档声明的限制（**注意文档口径**）

`docs/trait-system-analysis.md`（**该文档以 L13 为对象**，且与源码存在矛盾——
见 §6.7）的总结表（`:519-555`）给出总数：Rust 侧 ~310 项，Typort ✅ ~27、
⚠️ ~4、❌ ~279。逐条最重要的缺口：

| 缺口 | 逐字引文 | 锚点 |
|---|---|---|
| 无 supertrait | `无继承语法` | `docs/trait-system-analysis.md:140` |
| 无关联类型 | `无关联类型语法` | `:87` |
| trait 头 where 不支持 | `无 where 子句语法` | `:53`、`:113` |
| impl 头条件约束不支持 | `| 5.3 | 条件 impl (where) | … | ❌ | — |` | `:159` |
| 无默认方法体（文档口径） | `方法必须提供定义（在 impl 中）` | `:79` |
| 重叠规则不检查 | `Typort 允许重叠，求解器选第一个匹配的` | `:181` |
| 无孤儿规则检查 | `Typort 无跨文件 coherence 检查` | `:180` |
| 溢出保护只有硬限制 | `1000 次循环硬限制` | `:509` |
| 无多变量类型推断 | `| 31.5 | 多变量类型推断 | 多个类型参数推断 | ❌ | — |` | `:511` |
| 无动态分发 / trait 对象 | `无 dyn Trait 概念` / `不支持 trait 对象` | `:213`、`:227` |
| 方法歧义不解析 | `当前实现取第一个匹配` | `:390` |

**prelude 中留下的工作痕迹**（`src/prelude/show.typort:9-11`，**逐字**）：

```
//! `Show` covers the base types (`Nat`, `Int`, `Boolean`, `Ordering`, `Unit`,
//! `String`, `Void`) and concrete `List` / `Option` / `Product` / `Tuple2` /
//! `Either` / `Result` instances over them; generic conditional instances
//! (`impl[T] Show for List[T] where T: Show`) are not yet supported by the
//! elaborator, hence the per-element-type helpers below.
```

**`docs/opt-typeclass.md` 的 5 条性能问题**：
1. `assertion_table` 线性扫描（已解决）（`:5`）；
2. `clean()` 丢弃全部缓存；`synth()` 实际被当"成员测试"用
   （`:7-35`，建议 `can_satisfy`，已在 L13 落地）；
3. **实例没有头部类型索引**（`:77-85`，L13 已加 `head_index`）——
   **L10/L12 没有**，仍是 `HashMap<TraitName, Vec<Instance>>` 线性扫描；
4. `solve_trait` 急切完整展开每个候选实例（`:87-89`，"详见讨论中的单独分析"，
   该独立分析在 `docs/` 中不存在）；
5. **`fresh_meta` 急切调用 `solve_trait`**（`:91-93`）——**L10/L12 当前行为
   就是急切求解**（§1.3）。

**prelude / 源码内自陈的 trait 系统缺口**（这些是**实现方自己写下的**限制，
比 `trait-system-analysis.md` 的对比表更可信）：

| # | 缺口 | 逐字引文 | 锚点 |
|---|---|---|---|
| 1 | 条件实例不支持 | `generic conditional instances (\`impl[T] Show for List[T] where T: Show\`) are not yet supported by the elaborator` | `src/prelude/show.typort:9-11` |
| 2 | 同上（中文注） | `泛型条件实例（\`impl[T] Show for List[T] where T: Show\` 这类）elaborator / 暂不支持（where 约束、字典参数均解析失败）` | `src/prelude/show.typort:139-141` |
| 3 | 固有 impl 每个方法名只能有一个 + 其 where 隐参不在调用点插入 ⇒ 被迫用 trait | `Inherent impl blocks allow / only one method per name and their where-clause implicits don't get / inserted at call sites, so follow the Equal pattern instead` | `src/prelude/hdl/hdl-verilog-compat.typort:71-75` |
| 4 | trait 默认体不能通过 `this` 派发 sibling 方法 | `a default body cannot / dispatch sibling methods through \`this\` (filled-trait-default limitation)` | `src/prelude/hdl/hdl-bus.typort:181-184` |
| 5 | trait 默认体内的 `:=` 方法分派会让 where 隐参求解失败 | `implemented via driveExpr (not \`:=\`) because a \`:=\` method-call / dispatch inside a trait default body leaves the where-clause's implicit / solver unsolved` | `src/prelude/hdl/hdl-types.typort:71-73` |
| 6 | `#[derive(Bundle)]` 在 prelude 内与构造器短名冲突 | `#[derive(Bundle)] 在 prelude 文件中与 Expr 枚举的 \`create\` / 构造器短名冲突（既有限制）` | `src/prelude/hdl/hdl-bus-proto.typort:7-10` |
| 7 | 实例的 Nat 型参数不在调用点实例化（残留 `Rigid(Lvl(0))`）；参数化宽度下**静默生成 1 位信号** | `# 在实例求解时**不会被调用点的实际宽度实例化**：实例的引用里残留 / **实例声明上下文的级别变量 \`Rigid(Lvl(0))\`**` | `docs/l13-typeclass-instance-nat-param-bug.md:25-27` |
| 8 | 上述根治需架构级改动（meta 解无法表达"消费点参数化"） | `让约束 meta 的解能表达**消费点参数化**……这是 elaborator 架构级改动，影响 quote/eval/meta 全链路，需单独立项。` | `docs/l13-typeclass-instance-nat-param-bug.md:239-243` |
| 9 | **非终止**：实例搜索硬上限 1000，超限是 `panic` 而非类型错误 | `effort ≤ 1000（\`synth\` 主循环，typeclass.rs:219-224）：超限 \`panic!("Too much effort :(")\`——是**崩溃**不是类型错误。` | `src/L10_typeclass/README.md:74-77` |
| 10 | **重叠检查缺失**：允许多个 impl 同时适用，取第一个匹配者 | `Typort 允许重叠，求解器选第一个匹配的` | `docs/trait-system-analysis.md:181` |
| 11 | 无跨文件 coherence / 孤儿规则检查 | `Typort 无跨文件 coherence 检查` | `docs/trait-system-analysis.md:180` |
| 12 | 求解器内嵌 Span 的 Debug 进实例名 ⇒ 名字与源码位置耦合 | 见 §4.3 的 `typ_name` 构造 | `src/L10_typeclass/elaboration.rs:581` |

> **对"非终止"的形式化结论**：L10–L12 的实例搜索**不是良基的**——`Synth`
> 只靠 `effort > 1000` 硬停（且停的方式是 `panic`，在 L13 才降级为返回
> `None`）；由于 `dependencies` 恒空，实际可达的终止性论据只有"候选数有限"。
> 若要在 Lean 里给出终止性定理，必须**额外假设实例表有限**（或显式引入
> 同样的 fuel 上限并证明其单调下降）。

### 6.7 ⚠️ 文档与代码不一致（形式化的坑）

`docs/typeclass-syntax.md:263-265`、`:513-514`、`:568-569` 声称有
**"Head-indexing O(1) 实例查找"**；`docs/opt-typeclass.md:77-85` 则说
**没有**头索引（只是建议）。就 **L10/L12 的源码**而言，后者正确：

- L10 `class_instances: HashMap<String, Vec<Instance>>`，`new_subgoal` 全量
  克隆 `Vec` 后线性尝试（`src/L10_typeclass/typeclass.rs:148`、`:299`）；
- L12 `class_instances: HashMap<SmolStr, Vec<Instance>>`，`find_assertion_entry`
  线性扫描（`src/L12_canonical/typeclass.rs:87`、`:296-303`）。
- 头索引（`head_index`/`can_satisfy`）只出现在 **L13**
  （`docs/opt-typeclass.md` 的落地记录 + `src/L13_namespace/typeclass.rs`）。

**因此：形式化 L10/L12 时不要假设 O(1) 实例查找，也不要有 head indexing。**
`docs/typeclass-syntax.md` 的 BNF 描述的是**语法层**（L13 亦支持 supertrait /
关联类型，`src/L13_namespace/elaboration.rs:2305-2370`），而 **L10/L12 的
parser 不解析 supertrait / 关联类型 / `where`（除 def 上的之外）**：
`src/L10_typeclass/parser/mod.rs:698-753` 的 `p_trait_def` 只接受
`trait 名 [参数] { def … }`。

同理，`docs/typeclass-syntax.md:229-239` 描述 `where` 在 `def` 上脱糖为
`_<trait小写>_<类型名>` 隐式参数——这在 L12 的 parser 里**确实实现**
（`src/L12_canonical/parser/mod.rs:1400`），但 **impl / trait 头上的 where
不支持**，所以 `impl[T] Show for List[T] where T: Show`（条件实例）不可用。

---

## 附录 A：Lean 4 形式化的建议骨架

元变量（对应 §1）：

```lean
structure MetaId where n : Nat
inductive MetaEntry (α : Type) where
  | solved   : α → α → MetaEntry α      -- 解值, 类型（L05+ 保留类型；L12 另存 Cxt/origin）
  | unsolved : α → MetaEntry α          -- 类型
```

- `fresh_meta cxt a`：push `unsolved (close_ty cxt a)`，返回
  `AppPruning ?m cxt.pruning`（L05）/ `InsertedMeta ?m cxt.bds`（L03/L04）。
- `solve γ ?m sp rhs`：`pren ← invert γ sp`（非变量实参 → 非模式失败 / Stuck）；
  `rhs' ← rename (occ := some ?m) pren rhs`（occurs + scope check）；
  `?m := eval [] (lams pren.dom rhs')`。
- 求解的**唯一副作用**是 `metas[m] := solved …`；`rename`/`pruneVFlex` 会
  额外**造新 meta 并解旧 meta**（`pruneMeta`），形式化时须把 `solve` 与
  `prune` 归为同一类"改写 metacontext"的效果。

`unify`（对应 §2）：把 §2.1/§2.3/§2.4 的臂表实现成一个**带 fuel 与
`meta_contrains` 挂账表的、返回 `Except UnifyError Unit` 的相互递归函数**；
两个必须建模的非纯细节：(a) `force` 烧 fuel、耗尽时把已解 meta 当未解；
(b) flex 臂的 `Stuck` 被吞掉并挂账（§2.6）。

隐式参数（对应 §3）：`Icit = impl | expl`；`insert` / `insert_until_name`
是纯函数（除 `fresh_meta` 的 metacontext 副作用）；`check` 的隐式 Π 分支
产生 λ binder 而非 meta——**这是"插入"与"洞"的分界**。

类型类（对应 §4）：`Synth` 建议直接照 §4.5 抽成归纳关系

```
Synth(insts, G) ⇝ some ℓ
```

而不是抽成函数式状态机（waiters/answers 是并发式 SLD 的实现细节）。
`Instance` 在 L10/L12 恒为 `{assertion, dependencies := [], lvl}`，
即**只有无条件实例**。

## 附录 B：锚点索引（主题 → file:line）

| 主题 | 锚点 |
|---|---|
| `MetaVar` / `MetaEntry`（L03） | `src/L03_holes/mod.rs:36-50` |
| `MetaEntry` 带类型（L05） | `src/L05_pruning/mod.rs:64-70` |
| `MetaEntry` 三元（L12） | `src/L12_canonical/mod.rs:29-33` |
| `Val::Flex` / `Rigid` | `src/L03_holes/mod.rs:119-128` |
| `Tm::Meta` / `InsertedMeta` | `src/L03_holes/mod.rs:95-100` |
| `Tm::AppPruning` | `src/L05_pruning/mod.rs:176-178` |
| `fresh_meta`（L03/L04/L05/L10） | `src/L03_holes/mod.rs:159-162`；`src/L05_pruning/mod.rs:420-424`；`src/L10_typeclass/mod.rs:570-587` |
| `force` | `src/L03_holes/mod.rs:248-259`；`src/L12_canonical/mod.rs:686-710` |
| `invert` / `invert_go` | `src/L03_holes/mod.rs:312-335`；`src/L05_pruning/mod.rs:602-659` |
| `rename` / occurs / scope | `src/L03_holes/mod.rs:356-389`；`src/L05_pruning/mod.rs:812-839` |
| `lams` | `src/L03_holes/mod.rs:298-308`；`src/L05_pruning/mod.rs:843-862` |
| `solve` / `solve_with_pren` | `src/L03_holes/mod.rs:392-398`；`src/L05_pruning/mod.rs:865-898` |
| `prune_ty` / `prune_meta` / `prune_vflex` | `src/L05_pruning/mod.rs:664-792` |
| `intersect` / `flex_flex` | `src/L05_pruning/mod.rs:914-981` |
| `unify` | `src/L03_holes/mod.rs:413-455`；`src/L05_pruning/mod.rs:986-1026`；`src/L12_canonical/unification.rs:662-...` |
| `unify_sp` | `src/L04_implicit/mod.rs:414-423`；`src/L05_pruning/mod.rs:901-910` |
| `unify_catch`（Stuck 挂账） | `src/L12_canonical/mod.rs:1203-1245` |
| `UnifyError` | `src/L03_holes/mod.rs:54`；`src/L12_canonical/mod.rs:566-571` |
| `unify_fuel` / `refuel` / `burn_fuel` | `src/L12_canonical/mod.rs:602-656` |
| `SpecSolve` | `src/L12_canonical/elaboration.rs:18-25`；`src/L10_typeclass/elaboration.rs:21` |
| `unify_pm` | `src/L12_canonical/elaboration.rs:124-...` |
| `Icit` / `Either`（L04） | `src/L04_implicit/parser/mod.rs:10-24` |
| `Icit` / `Either`（L10） | `src/L10_typeclass/parser/syntax.rs:5-15` |
| `insert` / `insert_t` / `insert_go` | `src/L04_implicit/mod.rs:481-505` |
| `insert_until_name` | `src/L04_implicit/mod.rs:509-547` |
| `check`（隐式 binder） | `src/L04_implicit/mod.rs:549-604` |
| `infer` App（插入触发） | `src/L04_implicit/mod.rs:648-700` |
| `infer` Lam（扩展后插入） | `src/L04_implicit/mod.rs:628-641` |
| `NameOrigin` / `new_binder` | `src/L04_implicit/mod.rs:767-776`、`:810-819` |
| `v_applicable` | `src/L04_implicit/mod.rs:134-142` |
| `[A]` 域 → Hole | `src/L12_canonical/parser/mod.rs:1009-1043` |
| `check_universe` 的 `U(0)` 解 | `src/L10_typeclass/elaboration.rs:208-259` |
| 声明处隐式域钉 `U(0)` | `src/L10_typeclass/elaboration.rs:400-421`；`src/L12_canonical/elaboration.rs:508-523` |
| `where` 子句脱糖 | `src/L12_canonical/parser/mod.rs:1362-1443` |
| `TraitDecl` / `ImplDecl` AST | `src/L10_typeclass/parser/syntax.rs:178-205` |
| `p_trait_def` / `p_impl` | `src/L10_typeclass/parser/mod.rs:696-753`；`src/L12_canonical/parser/mod.rs:1722-1782` |
| trait 脱糖为 enum | `src/L10_typeclass/elaboration.rs:624-659`；`src/L12_canonical/elaboration.rs:763-797` |
| impl 登记为 `Instance` | `src/L10_typeclass/elaboration.rs:556-620`；`src/L12_canonical/elaboration.rs:697-761` |
| `Assertion` / `Instance` | `src/L10_typeclass/typeclass.rs:72-85`；`src/L12_canonical/typeclass.rs:11-24` |
| `Synth` 数据结构 | `src/L10_typeclass/typeclass.rs:87-153`；`src/L12_canonical/typeclass.rs:26-92` |
| `Synth::synth` | `src/L10_typeclass/typeclass.rs:213-285`；`src/L12_canonical/typeclass.rs:305-353` |
| `try_resolve` / `match_typ` | `src/L10_typeclass/typeclass.rs:186-211`、`:389-429` |
| `val_match` / `vals_eq_ground` | `src/L12_canonical/typeclass.rs:123-249` |
| `solve_multi_trait` | `src/L10_typeclass/unification.rs:449-465`；`src/L12_canonical/unification.rs:491-507` |
| `solve_trait` | `src/L10_typeclass/unification.rs:466-507`；`src/L12_canonical/unification.rs:508-564` |
| `trait_wrap` | `src/L10_typeclass/elaboration.rs:1009-1099`；`src/L12_canonical/elaboration.rs:1167-1298` |
| `no_metas` | `src/L12_canonical/mod.rs:102-125` |
| 错误文案（trait） | `src/L12_canonical/elaboration.rs:395-436` |
| `iddfs` / `search` | `src/L12_canonical/canonical.rs:8-152` |
| canonical 调用点 | `src/L12_canonical/elaboration.rs:445-465` |
| prelude `Add` / `Into` / `Equal` | `src/prelude/core/op.typort:22`、`:68`、`:79` |
| prelude `Show` | `src/prelude/show.typort:14` |
| 条件实例不支持 | `src/prelude/show.typort:9-11`、`:139-141` |
| 实例优先级 = 登记序 | `src/prelude/hdl/hdl-types.typort:297-301` |
| `docs/opt-typeclass.md` 五问题 | `docs/opt-typeclass.md:5,7-35,77-85,87-89,91-93` |
| `docs/typeclass-syntax.md` 算法/BNF | `docs/typeclass-syntax.md:245-265`、`:569-620` |
| `docs/trait-system-analysis.md` 总结 | `docs/trait-system-analysis.md:519-610` |

