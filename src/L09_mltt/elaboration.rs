use std::rc::Rc;

use crate::{
    list::List,
    parser_lib::{Span, ToSpan},
};
use smol_str::SmolStr;

use super::{
    Closure, Cxt, DeclTm, Error, Infer, Lvl, MetaEntry, Tm, Val,
    cxt::DeclEntry,
    empty_span, lvl2ix,
    parser::syntax::{Decl, Either, Icit, Raw},
    pattern_match::Compiler,
    pretty::pretty_tm,
    surface,
    unification::PartialRenaming,
};
impl Infer {
    fn insert_go(&mut self, cxt: &Cxt, t: Tm, va: Val) -> Result<(Tm, Val), Error> {
        match self.force(cxt.decl(), va) {
            Val::Pi(_, Icit::Impl, a, b) => {
                let m = self.fresh_meta(cxt.decl(), cxt, (*a).clone());
                let mv = self.eval(cxt.decl(), &cxt.env, &m);
                self.insert_go(
                    cxt,
                    Tm::App(Box::new(t), Box::new(m), Icit::Impl),
                    self.closure_apply(cxt.decl(), &b, mv),
                )
            }
            va => Ok((t, va)),
        }
    }

    fn insert_t(&mut self, cxt: &Cxt, act: Result<(Tm, Val), Error>) -> Result<(Tm, Val), Error> {
        act.and_then(|(t, va)| self.insert_go(cxt, t, va))
    }

    /// 隐式参数插入；如果项本身已经是隐式 λ 则不再插入（用户显式给出了隐式参数）。
    fn insert(&mut self, cxt: &Cxt, act: Result<(Tm, Val), Error>) -> Result<(Tm, Val), Error> {
        act.and_then(|x| match x {
            (t @ Tm::Lam(_, Icit::Impl, _), va) => Ok((t, va)),
            (t, va) => self.insert_t(cxt, Ok((t, va))),
        })
    }

    fn insert_until_go(
        &mut self,
        cxt: &Cxt,
        name: Span<SmolStr>,
        t: Tm,
        va: Val,
    ) -> Result<(Tm, Val), Error> {
        match self.force(cxt.decl(), va) {
            Val::Pi(x, Icit::Impl, a, b) => {
                if x.data == name.data {
                    Ok((t, Val::Pi(x, Icit::Impl, a, b)))
                } else {
                    let m = self.fresh_meta(cxt.decl(), cxt, (*a).clone());
                    let mv = self.eval(cxt.decl(), &cxt.env, &m);
                    self.insert_until_go(
                        cxt,
                        name,
                        Tm::App(Box::new(t), Box::new(m), Icit::Impl),
                        self.closure_apply(cxt.decl(), &b, mv),
                    )
                }
            }
            _ => Err(Error::new(format!("no named implicit arg {}", name.data))),
        }
    }

    fn insert_until_name(
        &mut self,
        cxt: &Cxt,
        name: Span<SmolStr>,
        act: Result<(Tm, Val), Error>,
    ) -> Result<(Tm, Val), Error> {
        act.and_then(|(t, va)| self.insert_until_go(cxt, name, t, va))
    }

    pub fn check(&mut self, cxt: &Cxt, t: Raw, a: Val) -> Result<Tm, Error> {
        let decl = cxt.decl();
        match (t, self.force(decl, a)) {
            // λ 检查：命名隐式 `[x = e]` 对准同名隐式 Π；显式对显式
            (Raw::Lam(x, i, t), Val::Pi(x_t, i_t, a, b_closure))
                if (i_t == Icit::Impl && matches!(&i, Either::Name(n) if n == &x_t))
                    || i == Either::Icit(i_t) =>
            {
                let body = self.check(
                    &cxt.bind(x.clone(), Rc::new(self.quote(decl, cxt.lvl, (*a).clone())), (*a).clone()),
                    *t,
                    self.closure_apply(decl, &b_closure, Val::vvar(cxt.lvl)),
                )?;
                Ok(Tm::Lam(x, i_t, Rc::new(body)))
            }
            // 非 λ 项 against 隐式 Π：插入一个隐式绑定器
            (t, Val::Pi(x, Icit::Impl, a, b_closure)) => {
                let body = self.check(
                    &cxt.new_binder(super::tmspan(&x), Rc::new(self.quote(decl, cxt.lvl, (*a).clone()))),
                    t,
                    self.closure_apply(decl, &b_closure, Val::vvar(cxt.lvl)),
                )?;
                Ok(Tm::Lam(super::tmspan(&x), Icit::Impl, Rc::new(body)))
            }
            // let
            (Raw::Let(x, a, t, u), a_prime) => {
                let (a_checked, va, t_checked, vt) = if matches!(a.as_ref(), Raw::Hole) {
                    // 无类型注解的 let：直接推导 t 的类型，避免为 binder 造一个
                    // 闭合 meta。fresh_meta 的 close_ty 在 n 层嵌套 let 的 hole
                    // 链上是 O(n²)（每层都重建整条 Locals 的 Pi/Let 类型）；
                    // 深 let 探针 n=1000 从 ~168ms 降到 ~2.4ms。
                    let (t_checked, ty) = self.infer_expr(cxt, *t)?;
                    // 无注解 let 的推断类型**不物化为 Tm**（L07/L08 同款，2026-11-23）：
                    // 该 Tm 只被 `close_ty` 拼进 meta 类型的 `Tm::Let`，`eval(Tm::Let)` 不读它，
                    // `prune_ty`/`lams` 只在值层 Π 上工作，显示层用名字表的值——是死代码。
                    // 物化会把 2^n 的类型树写成项。占位 `Tm::U` 永不求值/打印。
                    let a_checked = Tm::U(0);
                    let vt = self.eval(decl, &cxt.env, &t_checked);
                    (a_checked, ty, t_checked, vt)
                } else {
                    let a_checked = self.check_ty(cxt, *a)?;
                    let va = self.eval(decl, &cxt.env, &a_checked);
                    let t_checked = self.check(cxt, *t, va.clone())?;
                    let vt = self.eval(decl, &cxt.env, &t_checked);
                    (a_checked, va, t_checked, vt)
                };
                let u_checked = self.check(
                    &cxt.define(x.clone(), Rc::new(t_checked.clone()), vt, Rc::new(a_checked.clone()), va),
                    *u,
                    a_prime,
                )?;
                Ok(Tm::Let(
                    x,
                    Box::new(a_checked),
                    Box::new(t_checked),
                    Box::new(u_checked),
                ))
            }
            // 洞
            (Raw::Hole, a) => {
                // 观察面：期望类型已知（无未解 meta）时补一条 inlay；洞没有源码
                // span，锚点退到当前最内层 binder 尾（顶层 def 体 ⇒ 0）。
                if self.lsp_collect {
                    let pos = if cxt.lvl.0 > 0 {
                        self.local_binder_span(cxt, cxt.lvl - 1).end_offset
                    } else {
                        0
                    };
                    self.push_inlay_hint(cxt, pos, a.clone());
                }
                Ok(self.fresh_meta(decl, cxt, a))
            }
            // match：编译 + 逐分支检查
            (Raw::Match(expr, clauses), expected) => {
                let (tm, typ) = self.infer_expr(cxt, *expr)?;
                let mut compiler = Compiler::new();
                compiler.compile(self, typ, tm.clone(), &clauses, cxt, expected)?;
                Ok(Tm::Match(Box::new(tm), compiler.pats))
            }
            // 一般情形：推断 + 合一
            (t, expected) => {
                let x = self.infer_expr(cxt, t);
                let (t_inferred, inferred_type) = self.insert(cxt, x)?;
                self.unify_catch(decl, cxt, expected, inferred_type)?;
                Ok(t_inferred)
            }
        }
    }

    /// 类型注解的 universe 检查（`Type N` 分层宇宙）：推断注解项，要求其
    /// 类型是 `Val::U(u)` 并返回层级 u。未解 meta 的类型按 L09 规则解为
    /// `U(0)`（空 spine 直接解；非空 spine 经带 occurs 的 rename 造 λ 解）。
    /// `def`/`enum` 类型、`let` 注解、Π 的域与余域都走这里。
    pub fn check_universe(&mut self, cxt: &Cxt, t: Raw) -> Result<(Tm, u32), Error> {
        let x = self.infer_expr(cxt, t);
        let (t_inferred, inferred_type) = self.insert(cxt, x)?;
        match inferred_type {
            Val::U(u) => Ok((t_inferred, u)),
            Val::Flex(m, sp) => {
                let (pren, prune_non_linear) = self
                    .invert(cxt.decl(), cxt.lvl, sp.clone())
                    .map_err(|_| Error::new("invert failed".to_owned()))?;
                let mty = match self.meta[m.0 as usize] {
                    MetaEntry::Unsolved(ref a) => a.clone(),
                    // fuel 窗口：已解 meta 被 force 当未解返回——按预算失败处理
                    _ => return Err(Error::new("when check universe, meta already solved".to_owned())),
                };
                if let Some(pr) = prune_non_linear {
                    self.prune_ty(cxt.decl(), &pr, mty.clone())
                        .map_err(|_| Error::new("prune failed".to_owned()))?;
                }
                if pren.dom.0 == 0 {
                    match self.force(cxt.decl(), mty.clone()) {
                        Val::U(_) => {
                            self.overwrite_meta(m, MetaEntry::Solved(Val::U(0), mty));
                            Ok((t_inferred, 0))
                        }
                        other => {
                            let other = self.force(cxt.decl(), other);
                            Err(Error::new(format!(
                                "meta type {:?} is not a universe",
                                other
                            )))
                        }
                    }
                } else {
                    let mut pren = PartialRenaming {
                        occ: Some(m),
                        ..pren
                    };
                    let rhs = self
                        .rename(cxt.decl(), &mut pren, Val::U(0))
                        .map_err(|_| {
                            Error::new("when check universe, try to rename failed".to_owned())
                        })?;
                    let solution = self.eval(
                        cxt.decl(),
                        &List::new(),
                        &self.lams(cxt.decl(), pren.dom, mty.clone(), rhs),
                    );
                    self.overwrite_meta(m, MetaEntry::Solved(solution, mty));
                    Ok((t_inferred, 0))
                }
            }
            _ => Err(Error::new(format!(
                "expected universe, got {:?}",
                inferred_type
            ))),
        }
    }

    /// 类型注解检查入口（Def/enum 类型 / let 注解 / Π 域与余域）：
    /// 统一走 [`Self::check_universe`]，返回被检查的注解项。
    fn check_ty(&mut self, cxt: &Cxt, t: Raw) -> Result<Tm, Error> {
        Ok(self.check_universe(cxt, t)?.0)
    }

    /// 持久化入口（保持旧签名/外部调用不变）：浅克隆 `cxt` 后委托给
    /// [`Infer::infer_owned`]。
    pub fn infer(&mut self, cxt: &Cxt, t: Decl) -> Result<(DeclTm, Val, Cxt), Error> {
        self.infer_owned(cxt.clone(), t)
    }

    /// 顺序声明路径入口：接管 `Cxt` 所有权，使 decl 表 `Rc` 强计数为 1，
    /// `decl_insert_mut` 可原地写。旧实现每个 def 先 `clone` 整表再
    /// `make_mut`（强计数恒 2 ⇒ 深拷），在 strchain/global 的 2^(k+1) 个
    /// 顶层 def 上是 O(D²)；改为所有权传递后降至 O(D)（见
    /// `docs/optimal-design/L07-upgrade-bench-2026-11-09.md`）。
    pub fn infer_owned(&mut self, mut cxt: Cxt, t: Decl) -> Result<(DeclTm, Val, Cxt), Error> {
        match t {
            Decl::Def {
                name,
                params,
                ret_type,
                body,
            } => {
                let typ = params.iter().rev().fold(ret_type.clone(), |a, b| {
                    Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                });
                let bod = params.iter().rev().fold(body.clone(), |a, b| {
                    Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a))
                });
                let typ_tm = self.check_ty(&cxt, typ)?;
                let vtyp = self.eval(cxt.decl(), &cxt.env, &typ_tm);
                // 重定义检查（L13 `fake_bind` 移植）：名字已登记（builtin /
                // 先前 def / enum）→ 定向报错，不再静默覆盖。先类型后重定义，
                // 与 L13 检查顺序一致。
                if cxt.decl().contains_key(name.data.as_str()) {
                    return Err(Error::new(format!("redefine {}", name.data)));
                }
                // 递归：先把名字登记成指向自身的中性占位，检查体，再用真实值覆盖。
                // 就地插入（L13 `fake_bind` + `decl` 模式）：cxt 由调用方移交、
                // Rc 计数=1，make_mut 原地写；旧实现每次先 clone 整表再 make_mut
                // ⇒ 强计数恒 2 ⇒ 每个顶层 def 深拷整张表（strchain/global 的
                // O(D²) 放大器）。
                cxt.decl_insert_mut(
                    name.data.clone(),
                    DeclEntry { prim: None, eta: None, prim_names: None,
                        ty: vtyp.clone(),
                        val: Val::Decl(SmolStr::new(&name.data), List::new()),
                    },
                );
                let t_tm = self.check(&cxt, bod, vtyp.clone())?;
                // 注册值归约到 WHNF：builtin 副作用（可变全局写 / 文件 IO）
                // 在声明序上驱动——L06「应用时触发」的等价物（否则
                // change_mutable 等只在别处 force 到它时才生效）。递归
                // 自引用由 force 的占位守卫兜住，不会展开。
                let vt = self.force(cxt.decl(), self.eval(cxt.decl(), &cxt.env, &t_tm));
                // 观察面（def 登记处）：span 旁表 + 登记期渲染串 + def-site hover；
                // 无显式返回类型注解时补一条 inlay（锚点 = 最后参数结束 +1）。
                // 形状登记（方案 3）：把 def 返回类型里的 match 形状记下来，供显示层
                // 在展开出的 `Val::Match` 上认回这个名字（无类型注解的 def 也能保真）。
                // 只在 lsp_collect 时做（纯显示用途，cost 可忽）。
                if self.lsp_collect {
                    let shapes = super::shape::shapes_for(self, cxt.decl(), vtyp.clone(), vt.clone());
                    if !shapes.is_empty() {
                        self.decl_shapes
                            .borrow_mut()
                            .insert(SmolStr::new(&name.data), shapes);
                    }
                }
                if self.lsp_collect {
                    let key = SmolStr::new(&name.data);
                    self.decl_spans.insert(key.clone(), name.to_span());
                    let want_def_hover = self
                        .hover_query
                        .map_or(true, |q| name.to_span().contains(q));
                    if want_def_hover {
                        // 方案 4（源码注解渲染）：有显式类型注解的 def 直接打**源码文本**——
                        // 于是 `def g(n: Nat): T n` 显示 `(n: Nat) → T n`，而不是求值后
                        // 展开的 `match n { … }`。无注解（ret_type 是洞）仍走值渲染。
                        let src_ty = super::raw_pretty::has_source_type(&ret_type).then(|| {
                            super::raw_pretty::def_type_from_source(&params, &ret_type)
                        });
                        let rendered_vtyp = vtyp.clone();
                        let (s, fin) = match src_ty {
                            Some(s) => (s, true),
                            None => self.render_typ_pretty(&cxt, rendered_vtyp),
                        };
                        self.decl_pretty.insert(key.clone(), (Rc::new(s.clone()), fin));
                        self.push_hover_rendered(name.to_span(), name.to_span(), &s);
                    }
                    if matches!(ret_type, Raw::Hole) {
                        let pos = params
                            .last()
                            .map(|p| surface::raw_span(&p.1).end_offset + 1)
                            .unwrap_or_else(|| name.to_span().end_offset);
                        if self.inlay_wanted(pos) {
                            let (ret_val, ret_lvl, peeled) = self.peel_pi_collect(&cxt, vtyp.clone());
                            let q = self.quote(cxt.decl(), ret_lvl, ret_val);
                            if !self.tm_has_unsolved_meta(&q) {
                                let mut names = cxt.names();
                                for pn in peeled.iter().rev() {
                                    names = names.prepend(SmolStr::new(&*pn));
                                }
                                let label = surface::inlay_label(&pretty_tm(0, names, &q));
                                self.push_inlay_label(pos, label);
                            }
                        }
                    }
                }
                cxt.decl_insert_mut(
                    name.data.clone(),
                    DeclEntry { prim: None, eta: None, prim_names: None,
                        ty: vtyp,
                        val: vt,
                    },
                );
                Ok((DeclTm::Def, Val::U(0), cxt))
            }
            Decl::Println(t) => Ok((
                DeclTm::Println(self.infer_expr(&cxt, t)?.0),
                Val::U(0),
                cxt,
            )),
            Decl::Enum {
                name,
                params,
                cases,
            } => {
                // 隐式参数是类型参数：无标注（Hole）的域钉为 U。域洞若保留，
                // 第 2+ 个参数的域 meta 会带 pruning（形如 `?m A` 的部分应用
                // meta），使用点解 `?m A := U` 时 invert 无法倒序 Decl 头
                // spine（Nat 等）而失败——显式提供隐式实参（`P1[Nat][Bool]`）
                // 即报 can't unify。语言定义上方括号参数就是类型参数（任意
                // 类型的索引留给圆括号），钉 U 从声明处消除该 meta；用户
                // 显式标注的域（`[A : Nat]`）与显式参数（索引）不动。
                let params: Vec<(Span<SmolStr>, Raw, Icit)> = params
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
                // enum 的 universe 层级（L09 分层宇宙）：取参数域与构造子字段域
                // 的 universe 最大者——enum 本体的类型是 `Type N` 上的 Π 链，
                // 高宇宙 enum（`HighLvl[Nat] : Type 2`）由此成立。扫描不改变
                // 检查结果：`infer_expr`/`check_universe` 只用于取层级（洞会被
                // check_universe 解为 U(0)，与随后正式检查同口径）。
                let mut universe_lvl = 0;
                for p in params.iter() {
                    if let Ok((Tm::U(lvl), _)) = self.infer_expr(&cxt, p.1.clone()) {
                        universe_lvl = std::cmp::max(lvl, universe_lvl);
                    }
                }
                for case in cases.iter() {
                    for c in case.1.iter() {
                        if let Ok((_, lvl)) = self.check_universe(&cxt, c.1.clone()) {
                            universe_lvl = std::cmp::max(lvl, universe_lvl);
                        }
                    }
                }
                // enum 类型本体：λ params → Sum(name, [(p, Var p, type-of-p, icit)], cases)
                let new_params: Vec<_> = params
                    .iter()
                    .map(|x| (x.0.clone(), x.2, Raw::Var(x.0.clone())))
                    .collect();
                // 构造子缺省返回类型：Name 逐个应用到隐式参数（显式索引留给构造子的 -> 给出）
                let default_ret = params
                    .iter()
                    .filter(|x| x.2 == Icit::Impl)
                    .fold(Raw::Var(name.clone()), |ret, x| {
                        Raw::App(
                            Box::new(ret),
                            Box::new(Raw::Var(x.0.clone())),
                            Either::Icit(Icit::Impl),
                        )
                    });
                // 构造子类型：Pi(枚举隐式参数 ++ 构造子绑定器) -> (用户 -> ret || 缺省)
                let new_cases = cases
                    .iter()
                    .map(|(case_name, p, bind)| {
                        let ty = params
                            .iter()
                            .filter(|x| x.2 == Icit::Impl)
                            .cloned()
                            .chain(p.clone())
                            .rev()
                            .fold(bind.clone().unwrap_or(default_ret.clone()), |ret, x| {
                                Raw::Pi(x.0.clone(), x.2, Box::new(x.1.clone()), Box::new(ret))
                            });
                        (case_name.clone(), ty)
                    })
                    .collect::<Vec<_>>();
                let sum = Raw::Sum(
                    name.clone(),
                    new_params,
                    new_cases.iter().map(|x| x.0.clone()).collect(),
                    universe_lvl,
                );
                let typ = params
                    .iter()
                    .rev()
                    .fold(Raw::U(universe_lvl), |a, b| {
                        Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                    });
                let bod = params.iter().rev().fold(sum, |a, b| {
                    Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a))
                });
                let typ_tm = self.check_ty(&cxt, typ)?;
                let vtyp = self.eval(cxt.decl(), &cxt.env, &typ_tm);
                // 重定义检查（L13 `fake_bind` 移植）：同名 enum / def / builtin
                // → 定向报错，不再静默覆盖。
                if cxt.decl().contains_key(name.data.as_str()) {
                    return Err(Error::new(format!("redefine {}", name.data)));
                }
                // 先占位再检查本体（本体内部引用自身时报"指向自身的中性值"）；
                // 就地插入，避免每个 enum 深拷整表。
                cxt.decl_insert_mut(
                    name.data.clone(),
                    DeclEntry { prim: None, eta: None, prim_names: None,
                        ty: vtyp.clone(),
                        val: Val::Decl(SmolStr::new(&name.data), List::new()),
                    },
                );
                let t_tm = self.check(&cxt, bod, vtyp.clone())?;
                let vt = self.eval(cxt.decl(), &cxt.env, &t_tm);
                cxt.decl_insert_mut(
                    name.data.clone(),
                    DeclEntry { prim: None, eta: None, prim_names: None,
                        ty: vtyp,
                        val: vt,
                    },
                );
                // 逐构造子注册：体 = λ(隐式参数, 字段) → SumCase{typ: ret, datas: 字段自身}
                for ((case_name, binders, ret), (ctor_name, ctor_ty)) in
                    cases.into_iter().zip(new_cases.into_iter())
                {
                    let body_ret = Raw::SumCase {
                        typ: Box::new(ret.unwrap_or(default_ret.clone())),
                        case_name: case_name.clone(),
                        datas: binders
                            .iter()
                            .map(|(n, _, i)| (n.clone(), Raw::Var(n.clone()), *i))
                            .collect(),
                    };
                    let bod = params
                        .iter()
                        .filter(|x| x.2 == Icit::Impl)
                        .cloned()
                        .chain(binders)
                        .rev()
                        .fold(body_ret, |a, b| {
                            Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a))
                        });
                    let typ_tm = self.check_ty(&cxt, ctor_ty)?;
                    let vtyp = self.eval(cxt.decl(), &cxt.env, &typ_tm);
                    // 构造子良构性（2026-09-18）：ret 必须是本 enum 的 Sum
                    // 且参数位是 telescope 内的 bare rigid（防 phantom 构造
                    // 子注入，见 check_ctor_wf）
                    self.check_ctor_wf(&cxt, &name.data, &ctor_name.data, &vtyp)?;
                    let t_tm = self.check(&cxt, bod, vtyp.clone())?;
                    let vt = self.eval(cxt.decl(), &cxt.env, &t_tm);
                    let entry = DeclEntry { prim: None, eta: None, prim_names: None,
                        ty: vtyp,
                        val: vt,
                    };
                    // 观察面：登记 enum 与构造子的定义处 span（限定键 E.c 与
                    // 裸名都记，def_span 统一指向源码 name token）。
                    if self.lsp_collect {
                        self.decl_spans.insert(SmolStr::new(&name.data), name.to_span());
                        // 限定键 + 裸名别名都记（裸名引用走 Raw::Var → push_hover_decl）
                        self.decl_spans.insert(
                            SmolStr::new(format!("{}.{}", name.data, ctor_name.data)),
                            ctor_name.to_span(),
                        );
                        self.decl_spans
                            .insert(SmolStr::new(&ctor_name.data), ctor_name.to_span());
                    }
                    // 限定名 `Enum.case` + 裸名别名（后注册者覆盖同名裸名）
                    cxt.decl_insert_mut(
                        SmolStr::new(format!("{}.{}", name.data, ctor_name.data)),
                        entry.clone(),
                    );
                    cxt.decl_insert_mut(ctor_name.data.clone(), entry);
                }
                Ok((DeclTm::Enum, Val::U(0), cxt))
            }
        }
    }

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
                return Err(Error::new(format!(
                    "构造子 {ctor_name} 的返回类型不是和类型"
                )))
            }
        };
        let (sname, sparams) = match &ret_sum {
            Val::Sum(n, ps, _) => (n, ps),
            _ => unreachable!(),
        };
        if sname.data != enum_name {
            return Err(Error::new(format!(
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
            return Err(Error::new(format!(
                "构造子 {ctor_name} 的返回类型参数必须是 {enum_name} 的参数变量（参数不得特化，特化请用显式索引）"
            )));
        }
        Ok(())
    }

    pub fn infer_expr(&mut self, cxt: &Cxt, t: Raw) -> Result<(Tm, Val), Error> {
        let decl = cxt.decl();
        match t {
            // 变量：先局部（名字表），再全局（decl 表）
            Raw::Var(x) => {
                if let Some(e) = cxt.lookup_src(&x.data) {
                    let (lvl, ty) = e.as_ref();
                    // 观察面：局部名使用处 hover（def_span 从 Locals 轨迹取）
                    if self.lsp_collect {
                        let def_span = self.local_binder_span(cxt, *lvl);
                        self.push_hover(cxt, x.to_span(), def_span, ty.clone());
                    }
                    Ok((Tm::Var(lvl2ix(cxt.lvl, *lvl)), ty.clone()))
                } else if let Some(e) = cxt.decl_get(&x.data) {
                    // 观察面：全局名使用处 hover（登记期串 final 时直取）
                    if self.lsp_collect {
                        let ty = e.ty.clone();
                        self.push_hover_decl(cxt, x.to_span(), &x.data, ty);
                    }
                    Ok((Tm::Decl(SmolStr::new(&x.data)), e.ty.clone()))
                } else {
                    Err(Error::new(format!("name not in scope: {}", x.data)))
                }
            }

            Raw::Obj(x, f) => {
                // 限定构造子引用 `Enum.case`——**局部遮蔽优先**：接收者名字
                // 已被局部 binder 占用时必须走正常投影（与 Raw::Var 的
                // 「局部先于全局」同序），否则同名局部会让 `Foo.c2` 静默
                // 解析成全局构造子（类型恰巧对上即是错误的 Ok）。
                // b66f5e4（L08 评审修复）回合：L07 同码潜伏。
                if let Raw::Var(n) = &*x {
                    if !cxt.has_src(&n.data) {
                        // 观察面：限定投影 `E.c` 的补全候选 = 该枚举的构造子名
                        // （receiver span = 枚举名 token）。
                        if self.lsp_collect {
                            let enum_val = cxt.decl_get(&n.data).map(|e| e.val.clone());
                            if let Some(v) = enum_val {
                                if let Val::Sum(_, _, cases) = self.force(decl, v) {
                                    for c in cases.iter() {
                                        self.completion_table.push((n.to_span(), c.data.to_string()));
                                    }
                                }
                            }
                        }
                        let key = format!("{}.{}", n.data, f.data);
                        if let Some(e) = cxt.decl_get(&key) {
                            return Ok((Tm::Decl(SmolStr::new(key)), e.ty.clone()));
                        }
                    }
                }
                let recv_span = surface::raw_span(&x);
                let (tm, ty) = self.infer_expr(cxt, *x)?;
                let ty_forced = self.force(decl, ty);
                // 观察面：投影的补全候选 = 接收者类型上的字段名（Sum 的索引参数 /
                // 构造子值的字段）；receiver span 取表达式折叠出的源码区间。
                if self.lsp_collect {
                    match &ty_forced {
                        Val::Sum(_, params, _) => {
                            for (n, ..) in params.iter() {
                                self.completion_table.push((recv_span, n.data.to_string()));
                            }
                        }
                        Val::SumCase { datas, .. } => {
                            for (n, _, _) in datas.iter() {
                                self.completion_table.push((recv_span, n.data.to_string()));
                            }
                        }
                        _ => {}
                    }
                }
                match ty_forced {
                    // 接收者类型是 Sum：字段=索引参数，类型取参数的**类型槽**
                    Val::Sum(sname, params, cases) => {
                        if let Some((_, _, fty, _)) = params.iter().find(|(n, ..)| n == &f) {
                            return Ok((
                                Tm::Obj(Box::new(tm), f.clone()),
                                fty.as_ref().clone(),
                            ));
                        }
                        if cases.len() == 1 && cases[0].data.contains(".mk") {
                            if let Some(e) = cxt.decl_get(&cases[0].data) {
                                let impl_vals: Vec<Val> = params
                                    .iter()
                                    .filter(|(_, _, _, i)| *i == Icit::Impl)
                                    .map(|(_, v, _, _)| v.as_ref().clone())
                                    .collect();
                                let mut ty = e.ty.clone();
                                let mut impl_idx = 0;
                                while let Val::Pi(bname, _, bdom, closure) =
                                    self.force(decl, ty)
                                {
                                    if bname.data == f.data {
                                        return Ok((
                                            Tm::Obj(Box::new(tm), f.clone()),
                                            (*bdom).clone(),
                                        ));
                                    }
                                    let u = if impl_idx < impl_vals.len() {
                                        let v = impl_vals[impl_idx].clone();
                                        impl_idx += 1;
                                        v
                                    } else {
                                        let proj =
                                            Tm::Obj(Box::new(tm.clone()), super::tmspan(&bname));
                                        self.eval(decl, &cxt.env, &proj)
                                    };
                                    ty = self.closure_apply(decl, &closure, u);
                                }
                            }
                        }
                        Err(Error::new(format!("{} has no field {}", sname.data, f.data)))
                    }
                    // 接收者类型是构造子值：索引参数优先，否则剥构造子类型取字段真实类型
                    Val::SumCase {
                        typ,
                        case_name,
                        datas,
                    } => {
                        let (sname, params) = match self.force(decl, super::rc_take(typ)) {
                            Val::Sum(sname, params, _) => (sname, params),
                            _ => return Err(Error::new("ill-scoped SumCase".to_owned())),
                        };
                        if let Some((_, _, fty, _)) =
                            params.iter().find(|(n, ..)| n == &f)
                        {
                            return Ok((
                                Tm::Obj(Box::new(tm), f.clone()),
                                fty.as_ref().clone(),
                            ));
                        }
                        let ctor_ty = cxt
                            .decl_get(&format!("{}.{}", sname.data, case_name.data))
                            .ok_or_else(|| Error::new("missing constructor decl".to_owned()))?
                            .ty
                            .clone();
                        let impl_vals: Vec<Val> = params
                            .iter()
                            .filter(|(_, _, _, i)| *i == Icit::Impl)
                            .map(|(_, v, _, _)| v.as_ref().clone())
                            .collect();
                        let mut ty = ctor_ty;
                        let mut impl_idx = 0;
                        loop {
                            match self.force(decl, ty) {
                                Val::Pi(bname, _, bdom, closure) => {
                                    if bname.data == f.data {
                                        return Ok((
                                            Tm::Obj(Box::new(tm), f.clone()),
                                            (*bdom).clone(),
                                        ));
                                    }
                                    let u = if impl_idx < impl_vals.len() {
                                        let v = impl_vals[impl_idx].clone();
                                        impl_idx += 1;
                                        v
                                    } else {
                                        datas
                                            .iter()
                                            .find(|(n, _, _)| n == &bname)
                                            .map(|(_, v, _)| v.as_ref().clone())
                                            .ok_or_else(|| {
                                                Error::new(format!(
                                                    "no field {} on {}",
                                                    f.data, sname.data
                                                ))
                                            })?
                                    };
                                    ty = self.closure_apply(decl, &closure, u);
                                }
                                _ => {
                                    return Err(Error::new(format!(
                                        "{} has no field {}",
                                        sname.data, f.data
                                    )))
                                }
                            }
                        }
                    }
                    _ => Err(Error::new(format!("cannot project field {}", f.data))),
                }
            }

            // λ 推断：域用 fresh meta，值域闭包封口
            Raw::Lam(x, Either::Icit(i), t) => {
                let new_meta = self.fresh_meta(decl, cxt, Val::U(0));
                let a = self.eval(decl, &cxt.env, &new_meta);
                let new_cxt = cxt.bind(x.clone(), Rc::new(self.quote(decl, cxt.lvl, a.clone())), a.clone());
                let infered = self.infer_expr(&new_cxt, *t);
                let (t_inferred, b) = self.insert(&new_cxt, infered)?;
                let b_closure = self.close_val(decl, cxt, b);
                Ok((
                    Tm::Lam(x.clone(), i, Rc::new(t_inferred)),
                    Val::Pi(super::vspan(x), i, Rc::new(a), b_closure),
                ))
            }

            Raw::Lam(x, Either::Name(_), _) => Err(Error::new(format!("infer named lambda {x:?}"))),

            // 应用
            Raw::App(t, u, i) => {
                let (i, t, tty) = match i {
                    Either::Name(name) => {
                        let infered = self.infer_expr(cxt, *t);
                        let (t, tty) = self.insert_until_name(cxt, name, infered)?;
                        (Icit::Impl, t, tty)
                    }
                    Either::Icit(Icit::Impl) => {
                        let (t, tty) = self.infer_expr(cxt, *t)?;
                        (Icit::Impl, t, tty)
                    }
                    Either::Icit(Icit::Expl) => {
                        let infered = self.infer_expr(cxt, *t);
                        let (t, tty) = self.insert_t(cxt, infered)?;
                        (Icit::Expl, t, tty)
                    }
                };
                let (a, b_closure) = match self.force(decl, tty) {
                    Val::Pi(_, i_t, a, b_closure) => {
                        if i == i_t {
                            ((*a).clone(), b_closure)
                        } else {
                            return Err(Error::new(format!("icit mismatch {i:?} {i_t:?}")));
                        }
                    }
                    tty => {
                        let new_meta = self.fresh_meta(decl, cxt, Val::U(0));
                        let a = self.eval(decl, &cxt.env, &new_meta);
                        let b_closure = Closure(
                            cxt.env.clone(),
                            Rc::new(self.fresh_meta(
                                decl,
                                &cxt.bind(
                                    empty_span(SmolStr::new("x")),
                                    Rc::new(self.quote(decl, cxt.lvl, a.clone())),
                                    a.clone(),
                                ),
                                Val::U(0),
                            )),
                        );
                        self.unify_catch(
                            decl,
                            cxt,
                            Val::Pi(
                                super::vspan(empty_span(SmolStr::new("x"))),
                                i,
                                Rc::new(a.clone()),
                                b_closure.clone(),
                            ),
                            tty,
                        )?;
                        (a, b_closure)
                    }
                };
                let u_checked = self.check(cxt, *u, a)?;
                Ok((
                    Tm::App(Box::new(t), Box::new(u_checked.clone()), i),
                    self.closure_apply(decl, &b_closure, self.eval(decl, &cxt.env, &u_checked)),
                ))
            }

            Raw::U(x) => Ok((Tm::U(x), Val::U(x + 1))),

            Raw::Pi(x, i, a, b) => {
                let (a_checked, a_lvl) = self.check_universe(cxt, *a)?;
                let a_eval = self.eval(decl, &cxt.env, &a_checked);
                let (b_checked, b_lvl) = self.check_universe(
                    &cxt.bind(x.clone(), Rc::new(self.quote(decl, cxt.lvl, a_eval.clone())), a_eval),
                    *b,
                )?;
                Ok((
                    Tm::Pi(x, i, Rc::new(a_checked), Rc::new(b_checked)),
                    Val::U(std::cmp::max(a_lvl, b_lvl)),
                ))
            }

            Raw::Let(x, a, t, u) => {
                let a_checked = self.check_ty(cxt, *a)?;
                let va = self.eval(decl, &cxt.env, &a_checked);
                let t_checked = self.check(cxt, *t, va.clone())?;
                let vt = self.eval(decl, &cxt.env, &t_checked);
                let (u_inferred, b) = self.infer_expr(
                    &cxt.define(
                        x.clone(),
                        Rc::new(t_checked.clone()),
                        vt.clone(),
                        Rc::new(a_checked.clone()),
                        va,
                    ),
                    *u,
                )?;
                Ok((
                    Tm::Let(
                        x,
                        Box::new(a_checked),
                        Box::new(t_checked),
                        Box::new(u_inferred),
                    ),
                    b,
                ))
            }

            Raw::Hole => {
                let new_meta = self.fresh_meta(decl, cxt, Val::U(0));
                let a = self.eval(decl, &cxt.env, &new_meta);
                let t = self.fresh_meta(decl, cxt, a.clone());
                Ok((t, a))
            }

            Raw::LiteralIntro(literal) => {
                // 观察面：字面量自身的类型
                if self.hover_wanted(literal.to_span()) {
                    self.hover_table
                        .push((literal.to_span(), literal.to_span(), "String".to_owned()));
                }
                Ok((Tm::LiteralIntro(literal), Val::LiteralType))
            }

            // match 只能在检查模式下使用（期望类型决定分支体怎么查）
            Raw::Match(..) => Err(Error::new(
                "match cannot be inferred; give it an expected type".to_owned(),
            )),

            Raw::Sum(name, params, cases, universe) => {
                let new_params = params
                    .iter()
                    .map(|(n, i, raw)| {
                        let (value_checked, value_ty) = self.infer_expr(cxt, raw.clone())?;
                        let ty = self.quote(decl, cxt.lvl, value_ty);
                        Ok((n.clone(), value_checked, ty, *i))
                    })
                    .collect::<Result<Vec<_>, Error>>()?;
                Ok((Tm::Sum(name, new_params, cases), Val::U(universe)))
            }

            Raw::SumCase {
                typ,
                case_name,
                datas,
            } => {
                let (typ_checked, _) = self.infer_expr(cxt, *typ)?;
                let typ_val = self.eval(decl, &cxt.env, &typ_checked);
                let datas = datas
                    .into_iter()
                    .map(|(n, raw, i)| {
                        let (tm, _) = self.infer_expr(cxt, raw)?;
                        Ok((n, tm, i))
                    })
                    .collect::<Result<Vec<_>, Error>>()?;
                // 观察面：构造子使用处 hover（键 = 枚举名.构造子名，与 decl 表键一致；
                // 类型从 decl 表取，按限定键记忆化渲染串）。
                if self.lsp_collect {
                    if let Val::Sum(sname, _, _) = &self.force(decl, typ_val.clone()) {
                        let key = format!("{}.{}", sname.data, case_name.data);
                        if let Some(e) = cxt.decl_get(&key) {
                            let ty = e.ty.clone();
                            self.push_ctor_hover(cxt, case_name.to_span(), &key, ty);
                        }
                    }
                }
                Ok((
                    Tm::SumCase {
                        typ: Box::new(typ_checked),
                        case_name,
                        datas,
                    },
                    typ_val,
                ))
            }
        }
    }
}
