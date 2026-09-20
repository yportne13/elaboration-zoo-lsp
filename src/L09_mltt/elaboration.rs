use std::cmp::max;
use std::rc::Rc;

use crate::{list::List, parser_lib::Span};

use super::{
    Closure, Cxt, DeclTm, Error, Infer, Subst, Tm, VTy, Val,
    Lvl,
    empty_span, lvl2ix, val_mentions_lvl, wrap_sub,
    parser::syntax::{Decl, Either, Icit, Raw},
    pattern_match::Compiler, pretty::pretty_tm, MetaEntry,
    unification::{PartialRenaming, SpecSolve},
};

impl Infer {
    fn insert_go(&mut self, cxt: &Cxt, t: Tm, va: Val) -> (Tm, VTy) {
        match self.force(va) {
            Val::Pi(_, Icit::Impl, a, b) => {
                let m = self.fresh_meta(cxt, *a);
                let mv = self.eval(&cxt.env, m.clone());
                self.insert_go(
                    cxt,
                    Tm::App(Box::new(t), Box::new(m), Icit::Impl),
                    self.closure_apply(&b, mv),
                )
            }
            va => (t, va),
        }
    }
    fn insert_t(&mut self, cxt: &Cxt, act: Result<(Tm, VTy), Error>) -> Result<(Tm, VTy), Error> {
        act.map(|(t, va)| self.insert_go(cxt, t, va))
    }
    fn insert(&mut self, cxt: &Cxt, act: Result<(Tm, VTy), Error>) -> Result<(Tm, VTy), Error> {
        act.and_then(|x| match x {
            (t @ Tm::Lam(_, Icit::Impl, _), va) => Ok((t, va)),
            (t, va) => self.insert_t(cxt, Ok((t, va))),
        })
    }
    fn insert_until_go(
        &mut self,
        cxt: &Cxt,
        name: Span<String>,
        t: Tm,
        va: Val,
    ) -> Result<(Tm, VTy), Error> {
        match self.force(va) {
            Val::Pi(x, Icit::Impl, a, b) => {
                if x.data == name.data {
                    Ok((t, Val::Pi(x, Icit::Impl, a, b)))
                } else {
                    let m = self.fresh_meta(cxt, *a);
                    let mv = self.eval(&cxt.env, m.clone());
                    self.insert_until_go(
                        cxt,
                        name,
                        Tm::App(Box::new(t), Box::new(m), Icit::Impl),
                        self.closure_apply(&b, mv),
                    )
                }
            }
            _ => Err(Error(name.map(|x| format!("no named implicit arg {}", x)))),
        }
    }
    fn insert_until_name(
        &mut self,
        cxt: &Cxt,
        name: Span<String>,
        act: Result<(Tm, VTy), Error>,
    ) -> Result<(Tm, VTy), Error> {
        act.and_then(|(t, va)| self.insert_until_go(cxt, name, t, va))
    }
    /// 模式方程（"模式作为表达式"与期望类型 / 被匹配值合一）：解累积为
    /// **显式替换 σ**（返回给调用方做 `subst_cxt`），不再返回改写过的 Cxt。
    pub fn check_pm_final(
        &mut self,
        cxt: &Cxt,
        t: Raw,
        a: Val,
        ori: Val,
    ) -> Result<(Tm, Rc<Subst>), Error> {
        let t_span = t.to_span();
        let x = self.infer_expr(cxt, t);
        let (t_inferred, inferred_type) = self.insert(cxt, x)?;
        self.meta_refuel();
        let solvable = cxt.bind_slots();
        let mut acc = Rc::new(Subst::default());
        {
            let mut spec = SpecSolve {
                solvable: &solvable,
                acc,
            };
            self.unify_pm(cxt, a, inferred_type, t_span, &mut spec)?;
            acc = spec.acc;
        }
        // 第二条方程：被匹配变量的值 ≐ 模式的值（头部精化的显式替换形态）。
        // 在**未改写**的原 env 下求值 t_inferred，再由方程入口置于 acc 之下
        // 解释（旧实现是在已改写 env 下求值——显式替换的等价口径）。失败
        // 容忍（旧 `.unwrap_or(new_cxt)` 同款）。
        let ori_v = self.eval(&cxt.env, t_inferred.clone());
        {
            let mut spec = SpecSolve {
                solvable: &solvable,
                acc,
            };
            let _ = self.unify_pm(cxt, ori, ori_v, t_span, &mut spec);
            acc = spec.acc;
        }
        Ok((t_inferred, acc))
    }
    pub fn check_pm(&mut self, cxt: &Cxt, t: Raw, a: Val) -> Result<(Tm, Rc<Subst>), Error> {
        let t_span = t.to_span();
        let x = self.infer_expr(cxt, t);
        let (t_inferred, inferred_type) = self.insert(cxt, x)?;
        self.meta_refuel();
        let solvable = cxt.bind_slots();
        let mut spec = SpecSolve {
            solvable: &solvable,
            acc: Rc::new(Subst::default()),
        };
        self.unify_pm(cxt, a, inferred_type, t_span, &mut spec)?;
        Ok((t_inferred, spec.acc))
    }
    /// 模式特化合一：解入 `spec.acc`（显式替换 σ），调用方在方程结束后取走
    /// 做 `subst_cxt` / 下一方程入口的 wrap。失败语义与旧 `unify_pm` 一致
    /// （臂报不可达）。`pub(crate)`：模式编译器的覆盖探测（probe_accessible
    /// 的索引方程）也走这里。
    pub(crate) fn unify_pm(
        &mut self,
        cxt: &Cxt,
        t: Val,
        t_prime: Val,
        t_span: Span<()>,
        spec: &mut SpecSolve<'_>,
    ) -> Result<(), Error> {
        let mut f1 = self.force(t);
        let mut f2 = self.force(t_prime);
        // 方程两侧置于**当前已积累的解**之下再解释（dpm-nbe `subst ɑ vs`
        // 的惰性等价物）。acc 为空时零开销。
        if !spec.acc.is_empty() {
            f1 = self.force(wrap_sub(&spec.acc, f1));
            f2 = self.force(wrap_sub(&spec.acc, f2));
        }
        // 双裸 Rigid 同级自反
        if let (Val::Rigid(x1, sp1), Val::Rigid(x2, sp2)) = (&f1, &f2) {
            if sp1.is_empty() && sp2.is_empty() && x1 == x2 {
                return Ok(());
            }
        }
        // 单侧裸 Rigid → 精化解累积进 σ（旧 `update_cxt` 的显式替换形态）
        if let Val::Rigid(x, sp) = &f1 {
            if sp.is_empty() {
                return Self::spec_refine(cxt, *x, f2.clone(), t_span, spec);
            }
        }
        if let Val::Rigid(x, sp) = &f2 {
            if sp.is_empty() {
                return Self::spec_refine(cxt, *x, f1.clone(), t_span, spec);
            }
        }
        match (&f1, &f2) {
            (
                Val::SumCase { typ: t1, case_name: n1, datas: d1, .. },
                Val::SumCase { typ: t2, case_name: n2, datas: d2, .. },
            ) => {
                if n1 == n2 {
                    // **比 Sum 头名字**（L07/L10 同款，2026-09-18 评审修复 4）：
                    // 跨 enum 重名构造子（E1.c / E2.c）是两个不同值，同
                    // case_name 不足以判定身份——头名不同直接失败。**不比
                    // typ 的值**：typ 的索引槽就是这些值自身的构造子形态，
                    // 比值必然在互相引用上深递归；索引等式的比较在外层
                    // Sum-Sum 的参数 zip 里。
                    if let (Val::Sum(na, ..), Val::Sum(nb, ..)) = (
                        self.force((**t1).clone()),
                        self.force((**t2).clone()),
                    ) {
                        if na.data != nb.data {
                            return Err(Error(t_span.map(|_| "".to_string())));
                        }
                    }
                    for (x, y) in d1.iter().zip(d2.iter()) {
                        self.unify_pm(
                            cxt,
                            x.1.as_ref().clone(),
                            y.1.as_ref().clone(),
                            t_span,
                            spec,
                        )?;
                    }
                    Ok(())
                } else {
                    Err(Error(t_span.map(|_| "".to_string())))
                }
            }
            (Val::Sum(n1, d1, ..), Val::Sum(n2, d2, ..)) => {
                if n1 == n2 {
                    for (x, y) in d1.iter().zip(d2.iter()) {
                        self.unify_pm(
                            cxt,
                            x.1.as_ref().clone(),
                            y.1.as_ref().clone(),
                            t_span,
                            spec,
                        )?;
                    }
                    Ok(())
                } else {
                    Err(Error(t_span.map(|_| "".to_string())))
                }
            }
            // 其余落常规合一（spec 穿参：途中的 bare rigid 继续累积进 σ）
            (u, v) => {
                let r = self.unify(cxt.lvl, cxt, u.clone(), v.clone(), Some(spec));
                r.map_err(|_| {
                    let err = format!(
                        "can't unify\n      find: {}\n  expected: {}",
                        pretty_tm(0, cxt.names(), &self.quote(cxt.lvl, u.clone())),
                        pretty_tm(0, cxt.names(), &self.quote(cxt.lvl, v.clone())),
                    );
                    Error(t_span.map(|_| err.clone()))
                })
            }
        }
    }
    /// 一条特化解 `x := v` 累积进 σ（旧 `Cxt::update_cxt` 的单步）。守卫：
    /// Flex 不精化（旧直通）；越界 / 全局层级无操作（旧 `lvl2ix` +
    /// `change_n` 越界同款）；浅 occurs 失败 = Err（臂不可达）。
    fn spec_refine(
        cxt: &Cxt,
        x: Lvl,
        v: Val,
        t_span: Span<()>,
        spec: &mut SpecSolve<'_>,
    ) -> Result<(), Error> {
        if matches!(v, Val::Flex(..)) {
            return Ok(());
        }
        if x.0 >= cxt.lvl.0 {
            return Ok(());
        }
        if val_mentions_lvl(&v, x) {
            return Err(Error(t_span.map(|_| "".to_string())));
        }
        spec.acc = Subst::extend(&spec.acc, x, v);
        Ok(())
    }
    pub fn check_universe(&mut self, cxt: &Cxt, t: Raw) -> Result<(Tm, u32), Error> {
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

                // if the spine was non-linear, we check that the non-linear arguments
                // can be pruned from the meta type (i.e. that the pruned solution will
                // be well-typed)
                if let Some(pr) = prune_non_linear {
                    self.prune_ty(&pr, mty.clone()).map_err(|_| Error(t_span.map(|_| "prune failed".to_owned())))?; // 掩码反转在 prune_ty 内完成
                }

                if pren.dom.0 == 0 {
                    match self.force(mty.clone()) {
                        Val::U(x) => {//TODO:x?
                            self.meta[m.0 as usize] = MetaEntry::Solved(Val::U(0), mty);
                            Ok((t_inferred, 0))
                        },
                        _ => {
                            let err_typ = self.force(mty);
                            Err(Error(t_span.map(|_|  format!("meta type {:?} is not a universe", err_typ))))
                        },
                    }
                } else {
                    let rhs = self.rename(
                        &PartialRenaming {
                            occ: Some(m),
                            ..pren
                        },
                        Val::U(0),
                    ).map_err(|_| Error(t_span.map(|_| "when check universe, try to rename failed".to_string())))?;
                    let solution = self.eval(&List::new(), self.lams(pren.dom, mty.clone(), rhs));
                    self.meta[m.0 as usize] = MetaEntry::Solved(solution, mty);

                    Ok((t_inferred, 0))
                    //Err(Error(format!("when check universe, get pren {}", pren.dom.0)))
                }
            }
            _ => Err(Error(t_span.map(|_| format!("expected universe, got {:?}", inferred_type)))),
        }
    }
    pub fn check(&mut self, cxt: &Cxt, t: Raw, a: Val) -> Result<Tm, Error> {
        //println!("{} {:?} {} {:?}", "check".blue(), t, "==".blue(), a);
        match (t, self.force(a)) {
            // Check lambda expressions
            (Raw::Lam(x, i, t), Val::Pi(x_t, i_t, a, b_closure))
                if (i.clone(), i_t) == (Either::Name(x_t.clone()), Icit::Impl)
                    || i == Either::Icit(i_t) =>
            {
                let body = self.check(
                    &cxt.bind(x.clone(), self.quote(cxt.lvl, *a.clone()), *a),
                    *t,
                    self.closure_apply(&b_closure, Val::vvar(cxt.lvl)),
                )?;
                Ok(Tm::Lam(x, i_t, Box::new(body)))
            }
            (t, Val::Pi(x, Icit::Impl, a, b_closure)) => {
                let body = self.check(
                    &cxt.new_binder(x.clone(), self.quote(cxt.lvl, *a)),
                    t,
                    self.closure_apply(&b_closure, Val::vvar(cxt.lvl)),
                )?;
                Ok(Tm::Lam(x, Icit::Impl, Box::new(body)))
            }
            // Check let bindings
            (Raw::Let(x, a, t, u), a_prime) => {
                let (a_checked, _) = self.check_universe(cxt, *a)?;
                let va = self.eval(&cxt.env, a_checked.clone());
                let t_checked = self.check(cxt, *t, va.clone())?;
                let vt = self.eval(&cxt.env, t_checked.clone());
                let u_checked = self.check(
                    &cxt.define(x.clone(), t_checked.clone(), vt, a_checked.clone(), va),
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

            // Handle holes
            (Raw::Hole, a) => Ok(self.fresh_meta(cxt, a)),

            (Raw::Match(expr, clause), expected) => {
                let expr_span = expr.to_span();
                let (tm, typ) = self.infer_expr(cxt, *expr)?;
                let mut compiler = Compiler::new(expected);
                let error = compiler.compile(self, typ, &clause, cxt, self.eval(&cxt.env, tm.clone()))?;
                if !error.is_empty() {
                    Err(Error(expr_span.map(|_| format!("{error:?}"))))
                } else {
                    /*let tree = ret
                        .iter()
                        .map(|x| (x.1, x.0.clone()))
                        .collect::<HashMap<_, _>>();
                    let t = clause
                        .into_iter()
                        .enumerate()
                        .map(|(idx, x)| (pattern_to_detail(cxt, x.0), tree.get(&idx).unwrap().clone()))
                        .collect();*/
                    /*if let Some(ret_type) = compiler.ret_type.clone() {
                        println!("get match ret: {:?}", ret_type);
                    }*/
                    Ok(
                        Tm::Match(Box::new(tm), compiler.pats)
                    ) //if there is any posible that has no return type?
                }
            }

            // General case: infer type and unify
            (t, expected) => {
                let t_span = t.to_span();
                let x = self.infer_expr(cxt, t);
                let (t_inferred, inferred_type) = self.insert(cxt, x)?;
                self.unify_catch(cxt, expected, inferred_type, t_span)?;
                Ok(t_inferred)
            }
        }
    }
    pub fn infer(&mut self, cxt: &Cxt, t: Decl) -> Result<(DeclTm, Val, Cxt), Error> {
        match t {
            Decl::Def {
                name,
                params,
                ret_type,
                body,
            } => {
                let ret_cxt = cxt;
                let typ = params.iter().rev().fold(ret_type.clone(), |a, b| {
                    Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                });
                let bod = params.iter().rev().fold(body.clone(), |a, b| {
                    Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a))
                });
                let ret_cxt = {
                    let global_idx = Lvl(self.global.len() as u32);
                    let (typ_tm, _) = self.check_universe(ret_cxt, typ)?;
                    let vtyp = self.eval(&ret_cxt.env, typ_tm.clone());
                    //println!("------------------->");
                    //println!("{:?}", vtyp);
                    //println!("-------------------<");
                    let fake_cxt = self.fake_bind(ret_cxt, name.clone(), vtyp.clone(), global_idx);
                    self.global.insert(global_idx, Val::vvar(global_idx + 1919810));
                    let t_tm = self.check(&fake_cxt, bod, vtyp.clone())?;
                    //println!("begin vt {}", "------".green());
                    let vt = self.eval(&fake_cxt.env, t_tm.clone());
                    self.global.insert(global_idx, vt.clone());
                    self.define_global(ret_cxt, name.clone(), t_tm, vt, typ_tm, vtyp)
                };
                Ok((
                    DeclTm::Def {
                        /*name: name.clone(),
                        params: param,
                        ret_type: result_u,
                        body: body_u,*/
                    },
                    //vt,
                    Val::U(0),
                    ret_cxt,
                )) //TODO:vt may be wrong
            }
            Decl::Println(t) => Ok((
                DeclTm::Println(self.infer_expr(cxt, t)?.0),
                Val::U(0),
                cxt.clone(),
            )),
            Decl::Enum {
                name,
                params,
                cases,
            } => {
                // 隐式参数是类型参数：无标注（Hole）的域钉为 U(0)。域洞若保留，
                // 第 2+ 个参数的域经 fresh_meta 的 AppPruning 成为部分应用
                // meta（`?m A`），使用点显式供给枚举隐式实参（`P1[Nat][Bool]`）
                // 需解 `?m A := U(0)`，invert 对非变量 spine 实参（如 Nat 的
                // 值）直接 Err → 误报 can't unify（L07/L08 黑盒三轮修复的
                // L09 形态；check_universe 只解洞的类型 meta，域值 meta 仍
                // 未解，触发链完整）。钉 U(0)（L09 的全局默认层级，与
                // check_universe 的 meta 解 U(0) 同口径）从声明处消除该
                // meta；宇宙扫描对 U(0) 域贡献 lvl 0 = max 恒等，不扰动
                // universe_lvl。用户显式标注的域（`[A : Type 1]`）与显式
                // 索引不动——需高层级实例化时显式标注即可。
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
                let mut universe_lvl = 0;
                for p in params.iter() {
                    if let Ok((Tm::U(lvl), _)) = self.infer_expr(cxt, p.1.clone()) {
                        universe_lvl = max(lvl, universe_lvl);
                    }
                }
                for case in cases.iter() {
                    for c in case.1.iter() {
                        if let Ok((_, lvl)) = self.check_universe(cxt, c.1.clone()) {
                            universe_lvl = max(lvl, universe_lvl);
                        }
                    }
                }
                let new_params: Vec<_> = params
                    .iter()
                    .map(|x| (x.0.clone(), x.2, Raw::Var(x.0.clone())))
                    .collect();
                let default_ret = params
                    .iter()
                    .filter(|x| x.2 == Icit::Impl)
                    .fold(Raw::Var(name.clone()), |ret, x| {
                        Raw::App(Box::new(ret), Box::new(Raw::Var(x.0.clone())), super::parser::syntax::Either::Icit(x.2))
                    });
                let new_cases = cases
                    .clone()
                    .into_iter()
                    .map(|(case_name, p, bind)| (
                        case_name,
                        params
                            .iter()
                            .filter(|x| x.2 == Icit::Impl)
                            .cloned()
                            .chain(p)
                            .rev()
                            .fold(bind.unwrap_or(default_ret.clone()), |ret, x| {
                                Raw::Pi(x.0.clone(), x.2, Box::new(x.1.clone()), Box::new(ret))
                            })
                    ))//良构性由 check_ctor_wf 在构造子注册期检查（2026-09-18）
                    .collect::<Vec<_>>();
                let sum = Raw::Sum(
                    name.clone(),
                    new_params.clone(),
                    new_cases.iter().map(|x| x.0.clone()).collect(),
                    universe_lvl,
                );
                let typ = params.iter().rev().fold(Raw::U(universe_lvl), |a, b| {
                    Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                });
                let bod = params.iter().rev().fold(sum.clone(), |a, b| {
                    Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a))
                });
                let mut cxt = {
                    let global_idx = Lvl(self.global.len() as u32);
                    let (typ_tm, _) = self.check_universe(cxt, typ)?;
                    let vtyp = self.eval(&cxt.env, typ_tm.clone());
                    let fake_cxt = self.fake_bind(cxt, name.clone(), vtyp.clone(), global_idx);
                    self.global.insert(global_idx, Val::vvar(global_idx + 1919810));
                    let t_tm = self.check(&fake_cxt, bod, vtyp.clone())?;
                    let vt = self.eval(&fake_cxt.env, t_tm.clone());
                    self.global.insert(global_idx, vt.clone());
                    self.define_global(cxt, name.clone(), t_tm, vt, typ_tm, vtyp)
                };
                for (c, typ) in cases.iter().zip(new_cases.clone().into_iter()) {
                    let body_ret_type = Raw::SumCase {
                        typ: Box::new(c.2.clone().unwrap_or(default_ret.clone())),
                        case_name: c.0.clone(),
                        datas: /*params
                            .iter()
                            .map(|x| (x.0.clone(), Icit::Impl))*/
                            //.chain(
                                c.1.iter()
                                    .map(|(name, _, icit)| (name.clone(), *icit))
                            //)
                            .map(|x| (x.0.clone(), Raw::Var(x.0), x.1))
                            .collect(),
                    };
                    let bod =
                        params
                            .iter()
                            .filter(|x| match x.2 {
                                Icit::Impl => true,
                                Icit::Expl => false,
                            })
                            .cloned()
                            .chain(c.1.clone().into_iter()/*.enumerate().map(|(idx, x)| {
                                (empty_span(format!("_{idx}")), x.clone(), Icit::Expl)
                            })*/)
                            .rev()
                            .fold(
                                body_ret_type,
                                |a, b| Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a)),
                            );
                    let typ = typ.1;
                    cxt = {
                        let (typ_tm, _) = self.check_universe(&cxt, typ)?;
                        let vtyp = self.eval(&cxt.env, typ_tm.clone());
                        // 构造子良构性（L07 2026-09-18 评审修复 6 的同步移植）：
                        // ret 必须是本 enum 的 Sum 且参数位是 telescope 内的
                        // bare rigid
                        self.check_ctor_wf(&cxt, &name.data, &c.0.data, &vtyp)?;
                        let t_tm = self.check(&cxt, bod, vtyp.clone())?;
                        let vt = self.eval(&cxt.env, t_tm.clone());
                        self.define_global(&cxt, c.0.clone(), t_tm, vt, typ_tm, vtyp)
                    };
                }
                Ok((DeclTm::Enum {}, Val::U(0), cxt))
            }
        }
    }
    /// 构造子返回类型良构性（L07 2026-09-18 评审修复 6 的同步移植）：
    /// 实例化构造子类型的全部绑定器后，ret 的 WHNF 必须是 `enum_name` 的
    /// `Sum`，且其隐式参数位逐一等于 telescope 内的 bare rigid。允许构造
    /// 子重绑定参数（`p[A,B](a,b) -> Pack[A][B] a b`——使用点经特化方程
    /// 解回枚举参数），拒绝参数位为非变量的特化（`c -> Foo[Bool]`）与非
    /// 本 enum 的 ret（`c -> Nat`）：后者向构造子名字空间注入永不匹配任
    /// 何模式的 phantom 值，对覆盖检查完备的 match 在封闭输入上卡死。
    fn check_ctor_wf(
        &mut self,
        cxt: &Cxt,
        enum_name: &str,
        ctor_name: &str,
        ctor_vtyp: &Val,
    ) -> Result<(), Error> {
        let base = cxt.lvl.0;
        let mut ty = ctor_vtyp.clone();
        let mut bound = 0u32;
        let ret = loop {
            match self.force(ty.clone()) {
                Val::Pi(_, _, _, closure) => {
                    let u = Val::vvar(Lvl(base + bound));
                    bound += 1;
                    ty = self.closure_apply(&closure, u);
                }
                ret => break ret,
            }
        };
        let ret_sum = match self.force(ret) {
            s @ Val::Sum(..) => s,
            _ => {
                return Err(Error(empty_span(()).map(|_| {
                    format!("构造子 {ctor_name} 的返回类型不是和类型")
                })))
            }
        };
        let (sname, sparams) = match &ret_sum {
            Val::Sum(n, ps, _) => (n, ps),
            _ => unreachable!(),
        };
        if sname.data != enum_name {
            return Err(Error(empty_span(()).map(|_| {
                format!(
                    "构造子 {ctor_name} 的返回类型是 {}，不是 {enum_name}",
                    sname.data
                )
            })));
        }
        let non_rigid = sparams
            .iter()
            .filter(|(_, _, _, i)| *i == Icit::Impl)
            .map(|(_, v, _, _)| v.as_ref())
            .find(|v| {
                !matches!(v, Val::Rigid(l, sp) if l.0 >= base && l.0 < base + bound && sp.is_empty())
            });
        if let Some(_) = non_rigid {
            return Err(Error(empty_span(()).map(|_| {
                format!(
                    "构造子 {ctor_name} 的返回类型参数必须是 {enum_name} 的参数变量（参数不得特化，特化请用显式索引）"
                )
            })));
        }
        Ok(())
    }

    pub fn infer_expr(&mut self, cxt: &Cxt, t: Raw) -> Result<(Tm, Val), Error> {
        /*println!(
            "{} {:?} in {}",
            "infer".red(),
            t,
            cxt.types
                .iter()
                .map(|x| format!("{x:?}"))
                .reduce(|a, b| a + "\n" + &b)
                .unwrap_or(String::new())
        );*/
        let t_span = t.to_span();
        match t {
            // 变量：局部 `src_names`（内建 + 当前 def 的 binder/let，遮蔽）
            // 优先，回落 `Infer::global_names`（顶层 def/enum/构造子，
            // append-only、不随 Cxt 克隆）；都缺即 not in scope。
            Raw::Var(x) => match cxt
                .src_names
                .get(&x.data)
                .or_else(|| self.global_names.get(&x.data).map(|(l, t)| (l, t)))
            {
                Some((x, a)) => Ok((Tm::Var(lvl2ix(cxt.lvl, *x)), (**a).clone())),
                None => Err(Error(x.map(|x| format!("error name not in scope: {}", x)))),
            },

            Raw::Obj(x, t) => {
                if t.data == "mk" {
                    if let Raw::Var(sum_name) = x.as_ref() {
                        return self.infer_expr(cxt, Raw::Var(sum_name.clone().map(|n| format!("{n}.mk"))))
                    }
                }
                let (tm, a) = self.infer_expr(cxt, *x)?;
                match (tm, self.force(a.clone())) {
                    (tm, Val::Sum(_, params, cases)) => {
                        let mut c = None;
                        if cases.len() == 1 {
                            if let Some(case) = cases.first() {
                                if case.data.contains(".mk") {
                                    let (_, case_typ) = self.infer_expr(cxt, Raw::Var(case.clone()))?;
                                    let mut ret = vec![];
                                    let mut typ = case_typ;
                                    // struct 隐式参数的实例值（按声明序；只取
                                    // Impl——显式索引不占槽，与 L08 同款）
                                    let mut param: Vec<_> = params
                                        .iter()
                                        .filter(|(_, _, _, i)| *i == Icit::Impl)
                                        .map(|(_, v, _, _)| v.as_ref().clone())
                                        .collect();
                                    param.reverse();
                                    // 剥 mk 构造子类型链取字段类型。隐式 binder 用
                                    // 头部 Sum 实参实例化；**显式字段 binder 用接收者
                                    // 的卡住投影实例化**（eval(Obj(接收者项, 字段名))，
                                    // L08 评审修复回移——旧实现以 U(0) 占位会让依赖在
                                    // 前字段的在后字段出现在检查位时假拒：
                                    // `P e.witness` vs `P (U 0)` 合一失败）。
                                    while let Val::Pi(name, icit, ty, closure) = self.force(typ.clone()) {
                                        if icit == Icit::Expl {
                                            let val = self.eval(
                                                &cxt.env,
                                                Tm::Obj(Box::new(tm.clone()), name.clone()),
                                            );
                                            ret.push((name, *ty));
                                            typ = self.closure_apply(&closure, val);
                                        } else {
                                            let val = param.pop()
                                                .unwrap_or(Val::U(0));
                                            ret.push((name, *ty));
                                            typ = self.closure_apply(&closure, val);
                                        }
                                    }
                                    c = Some(ret);
                                }
                            }
                        }
                        Ok((
                            Tm::Obj(Box::new(tm.clone()), t.clone()),
                            c.and_then(|params| {
                                params.into_iter()
                                    .find(|(fields_name, _)| fields_name == &t)
                                    .map(|(_, ty)| ty)
                            }).or(
                            params
                                .into_iter()
                                .find(|(fields_name, _, _, _)| fields_name == &t)
                                .map(|(_, _, ty, _)| super::rc_take(ty))
                            )
                                .ok_or_else(|| Error(t.map(|t| format!(
                                    "`{}`: {:?} has no object `{}`",
                                    super::pretty_tm(0, cxt.names(), &tm),
                                    a,
                                    t,
                                ))))?
                        ))
                    }
                    (tm, Val::SumCase { datas: params, .. }) => {
                        Ok((
                            Tm::Obj(Box::new(tm.clone()), t.clone()),
                            params
                                .into_iter()
                                .find(|(fields_name, _, _)| fields_name == &t)
                                .map(|(_, ty, _)| super::rc_take(ty))
                                .ok_or_else(|| Error(t.map(|t| format!(
                                    "`{}`: {:?} has no object `{}`",
                                    super::pretty_tm(0, cxt.names(), &tm),
                                    a,
                                    t,
                                ))))?
                        ))
                    }
                    (tm, _) => Err(Error(t.map(|t| format!(
                        "`{}` has no object `{}`",
                        super::pretty_tm(0, cxt.names(), &tm),
                        t,
                    )))),
                }
            },

            // Infer lambda expressions
            Raw::Lam(x, Either::Icit(i), t) => {
                let new_meta = self.fresh_meta(cxt, Val::U(0));
                let a = self.eval(&cxt.env, new_meta);
                //TODO:below may be wrong
                let new_cxt = cxt.bind(x.clone(), self.quote(cxt.lvl, a.clone()), a.clone());
                let infered = self.infer_expr(&new_cxt, *t);
                let (t_inferred, b) = self.insert(&new_cxt, infered)?;
                let b_closure = self.close_val(cxt, b);
                Ok((
                    Tm::Lam(x.clone(), i, Box::new(t_inferred)),
                    Val::Pi(x, i, Box::new(a), b_closure),
                ))
            }

            Raw::Lam(x, Either::Name(_), t) => Err(Error(x.map(|_| "infer named lambda".to_owned()))),

            // Infer function applications
            Raw::App(t, u, i) => {
                let t_span = t.to_span();
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
                //println!("{} {:?} -> {:?}", "infer___".red(), t, tty); //debug
                let (a, b_closure) = match self.force(tty) {
                    Val::Pi(_, i_t, a, b_closure) => {
                        if i == i_t {
                            (*a, b_closure)
                        } else {
                            return Err(Error(t_span.map(|_| format!("icit mismatch {:?} {:?}", i, i_t))));
                        }
                    }
                    tty => {
                        let new_meta = self.fresh_meta(cxt, Val::U(0));
                        let a = self.eval(&cxt.env, new_meta);
                        let b_closure = Closure(
                            cxt.env.clone(),
                            Rc::new(self.fresh_meta(
                                &cxt.bind(
                                    empty_span("x".to_string()),
                                    self.quote(cxt.lvl, a.clone()),
                                    a.clone(),
                                ),
                                Val::U(0),
                            )),
                        );
                        self.unify_catch(
                            cxt,
                            Val::Pi(
                                empty_span("x".to_string()),
                                i,
                                Box::new(a.clone()),
                                b_closure.clone(),
                            ),
                            tty,
                            t_span,
                        )?;
                        (a, b_closure)
                    }
                };
                let u_checked = self.check(cxt, *u, a)?;
                Ok((
                    Tm::App(Box::new(t), Box::new(u_checked.clone()), i),
                    self.closure_apply(&b_closure, self.eval(&cxt.env, u_checked)),
                ))
            }

            // Infer universe type
            Raw::U(x) => Ok((Tm::U(x), Val::U(x + 1))),

            // Infer dependent function types
            Raw::Pi(x, i, a, b) => {
                let mut universe = 0;
                let (a_checked, lvl) = self.check_universe(cxt, *a)?;
                universe = max(universe, lvl);
                let a_eval = self.eval(&cxt.env, a_checked.clone());
                let (b_checked, lvl) = self.check_universe(
                    &cxt.bind(x.clone(), self.quote(cxt.lvl, a_eval.clone()), a_eval),
                    *b,
                )?;
                universe = max(universe, lvl);
                Ok((
                    Tm::Pi(x, i, Box::new(a_checked), Box::new(b_checked)),
                    Val::U(universe),
                ))
            }

            // Infer let bindings
            Raw::Let(x, a, t, u) => {
                let (a_checked, _) = self.check_universe(cxt, *a)?;
                let va = self.eval(&cxt.env, a_checked.clone());
                let t_checked = self.check(cxt, *t, va.clone())?;
                let vt = self.eval(&cxt.env, t_checked.clone());
                let (u_inferred, b) = self.infer_expr(
                    &cxt.define(
                        x.clone(),
                        t_checked.clone(),
                        vt.clone(),
                        a_checked.clone(),
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

            // Infer holes
            Raw::Hole => {
                let new_meta = self.fresh_meta(cxt, Val::U(0));
                let a = self.eval(&cxt.env, new_meta);
                let t = self.fresh_meta(cxt, a.clone());
                Ok((t, a))
            }

            Raw::LiteralIntro(literal) => Ok((Tm::LiteralIntro(literal), Val::LiteralType)),

            Raw::Match(_, _) => Err(Error(t_span.map(|_| "try to infer match".to_owned()))),

            Raw::Sum(name, params, cases, universe) => {
                let new_params = params
                    .iter()
                    .map(|ty| {
                        let (ty_checked, typ_val) = self.infer_expr(cxt, ty.2.clone())?;
                        let typ = self.quote(cxt.lvl, typ_val.clone());
                        Ok((ty.0.clone(), ty_checked, typ, ty.1))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                //TODO: universe need to consider cases?
                Ok((Tm::Sum(name, new_params, cases), Val::U(universe)))
            }

            Raw::SumCase {
                typ,
                case_name,
                datas,
            } => {
                let (typ_checked, _) = self.infer_expr(cxt, *typ)?;
                let typ_val = self.eval(&cxt.env, typ_checked.clone());
                let datas = datas
                    .into_iter()
                    .map(|x| {
                        let (tm, _) = self.infer_expr(cxt, x.1)?;
                        Ok((x.0, tm, x.2))
                    })
                    .collect::<Result<_, _>>()?;
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
