use std::rc::Rc;

use crate::parser_lib::Span;

use super::{
    empty_span, lvl2ix, parser::syntax::{Decl, Either, Icit, Raw}, Closure, Cxt, DeclEntry, DeclTm, Error, Infer, Tm, VTy, Val
};

impl Infer {
    fn insert_go(&mut self, cxt: &Cxt, t: Tm, va: &Rc<Val>) -> (Tm, Rc<VTy>) {
        let va = self.force(va);
        match va.as_ref() {
            Val::Pi(_, Icit::Impl, a, b) => {
                let m = self.fresh_meta(cxt, a);
                let mv = self.eval(&cxt.env, &m);
                self.insert_go(
                    cxt,
                    Tm::App(Box::new(t), Box::new(m), Icit::Impl),
                    &self.closure_apply(&b, mv),
                )
            }
            _ => (t, va),
        }
    }
    fn insert_t(&mut self, cxt: &Cxt, act: Result<(Tm, Rc<VTy>), Error>) -> Result<(Tm, Rc<VTy>), Error> {
        act.map(|(t, va)| self.insert_go(cxt, t, &va))
    }
    fn insert(&mut self, cxt: &Cxt, act: Result<(Tm, Rc<VTy>), Error>) -> Result<(Tm, Rc<VTy>), Error> {
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
        va: &Rc<Val>,
    ) -> Result<(Tm, Rc<VTy>), Error> {
        match self.force(va).as_ref() {
            Val::Pi(x, Icit::Impl, a, b) => {
                if x.data == name.data {
                    Ok((t, Val::Pi(x.clone(), Icit::Impl, a.clone(), b.clone()).into()))
                } else {
                    let m = self.fresh_meta(cxt, a);
                    let mv = self.eval(&cxt.env, &m);
                    self.insert_until_go(
                        cxt,
                        name,
                        Tm::App(Box::new(t), Box::new(m), Icit::Impl),
                        &self.closure_apply(&b, mv),
                    )
                }
            }
            _ => Err(Error(format!("no named implicit arg {:?}", name))),
        }
    }
    fn insert_until_name(
        &mut self,
        cxt: &Cxt,
        name: Span<String>,
        act: Result<(Tm, Rc<VTy>), Error>,
    ) -> Result<(Tm, Rc<VTy>), Error> {
        act.and_then(|(t, va)| self.insert_until_go(cxt, name, t, &va))
    }
    fn check(&mut self, cxt: &Cxt, t: Raw, a: &Rc<Val>) -> Result<Tm, Error> {
        //println!("{} {:?} {} {:?}", "check".blue(), t, "==".blue(), a);
        let a = self.force(a);
        match (t, a.as_ref()) {
            // Check lambda expressions
            (Raw::Lam(x, i, t), Val::Pi(x_t, i_t, a, b_closure))
                if (i.clone(), i_t) == (Either::Name(x_t.clone()), &Icit::Impl)
                    || i == Either::Icit(*i_t) =>
            {
                let body = self.check(
                    &cxt.bind(x.clone(), self.quote(cxt.lvl, a), a.clone()),
                    *t,
                    &self.closure_apply(&b_closure, Val::vvar(cxt.lvl).into()),
                )?;
                Ok(Tm::Lam(x, *i_t, Box::new(body)))
            }
            (t, Val::Pi(x, Icit::Impl, a, b_closure)) => {
                let body = self.check(
                    &cxt.new_binder(x.clone(), self.quote(cxt.lvl, a)),
                    t,
                    &self.closure_apply(&b_closure, Val::vvar(cxt.lvl).into()),
                )?;
                Ok(Tm::Lam(x.clone(), Icit::Impl, Box::new(body)))
            }
            // Check let bindings
            (Raw::Let(x, a_, t, u), _) => {
                let a_checked = self.check_ty(cxt, *a_)?;
                let va = self.eval(&cxt.env, &a_checked);
                let t_checked = self.check(cxt, *t, &va)?;
                let vt = self.eval(&cxt.env, &t_checked);
                let u_checked = self.check(
                    &cxt.define(x.clone(), t_checked.clone(), vt, a_checked.clone(), va),
                    *u,
                    &a,
                )?;
                Ok(Tm::Let(
                    x,
                    Box::new(a_checked),
                    Box::new(t_checked),
                    Box::new(u_checked),
                ))
            }

            // Handle holes
            (Raw::Hole, _) => Ok(self.fresh_meta(cxt, &a)),

            // General case: infer type and unify
            (t, _) => {
                let x = self.infer_expr(cxt, t);
                let (t_inferred, inferred_type) = self.insert(cxt, x)?;
                self.unify_catch(cxt, &a, &inferred_type)?;
                Ok(t_inferred)
            }
        }
    }
    /// 类型注解的 universe 结构预检（L13 `check_universe` 的轻量移植，
    /// 零副作用）：`LiteralIntro` 恒非类型；`Var` 在名字表且类型已确定
    /// （非 U、非未解 meta）→ 定向报错。洞 / 未解 meta / 其余形态放行——
    /// 可解与否交主检查路径（预检不推断、不造 meta，?N 编号不受扰动）。
    fn ty_precheck(&self, cxt: &Cxt, t: &Raw) -> Result<(), Error> {
        match t {
            Raw::LiteralIntro(_) => Err(Error("expected universe, got LiteralType".to_owned())),
            Raw::Var(x) => match cxt.src_names.get(&x.data) {
                Some((_, va)) => match self.force(va).as_ref() {
                    // force 已展开已解 meta；留下的 Flex 必是未解 → 放行
                    Val::U | Val::Flex(_, _) => Ok(()),
                    other => Err(Error(format!("expected universe, got {:?}", other))),
                },
                None => Ok(()), // 未知名：主检查报 name-not-in-scope（原路径）
            },
            _ => Ok(()),
        }
    }

    /// 类型注解的检查入口（Def 类型 / let 注解 / Π 域与余域）：结构预检
    /// 后回落原 `check(…, Val::U)`；Π 链逐段预检——域检查后在绑定上下文
    /// 里预检余域（与原 Pi 臂同构，域/余域各只检查一次，无额外 meta）。
    fn check_ty(&mut self, cxt: &Cxt, t: Raw) -> Result<Tm, Error> {
        if let Raw::Pi(x, i, a, b) = &t {
            self.ty_precheck(cxt, a)?;
            let a_checked = self.check(cxt, *a.clone(), &Val::U.into())?;
            let a_eval = self.eval(&cxt.env, &a_checked);
            let cxt2 = cxt.bind(x.clone(), self.quote(cxt.lvl, &a_eval), a_eval);
            self.ty_precheck(&cxt2, b)?;
            let b_checked = self.check(&cxt2, *b.clone(), &Val::U.into())?;
            Ok(Tm::Pi(x.clone(), *i, Box::new(a_checked), Box::new(b_checked)))
        } else {
            self.ty_precheck(cxt, &t)?;
            self.check(cxt, t, &Val::U.into())
        }
    }
    pub fn infer(&mut self, cxt: &Cxt, t: Decl) -> Result<(DeclTm, Val, Cxt), Error> {
        match t {
            Decl::Def {
                name,
                params,
                ret_type,
                body
            } => {
                let typ = params.iter().rev().fold(ret_type.clone(), |a, b| {
                    Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                });
                let bod = params
                    .iter()
                    .rev()
                    .fold(body.clone(), |a, b| Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a)));
                let ret_cxt = {
                    let typ_tm = self.check_ty(cxt, typ)?;
                    let vtyp = self.eval(&cxt.env, &typ_tm);
                    // 重定义检查（L13 `fake_bind` 的移植）：名字已登记
                    // （builtin / 先前 def）→ 定向报错，不再静默覆盖。
                    // 先类型后重定义，与 L13 的检查顺序一致（类型错误
                    // 优先于重定义报出）。
                    if self.decls.contains_key(&name.data) {
                        return Err(Error(format!("redefine {}", name.data)));
                    }
                    let t_tm = self.check(cxt, bod, &vtyp)?;
                    let vt = self.eval(&cxt.env, &t_tm);
                    // Decl-table entry: top-level defs become runtime
                    // name-lookups (`string_to_global_type`), mirroring
                    // L13's `cxt.decl(...)` at Def elaboration.
                    self.decls.insert(name.data.clone(), DeclEntry {
                        vt: vt.clone(),
                        va: vtyp.clone(),
                        prim: None,
                    });
                    cxt.define(name.clone(), t_tm, vt, typ_tm, vtyp)
                };
                // 首个元素是 decl 层"类型"占位（run/bench 均不消费）
                Ok((DeclTm::Def, Val::U, ret_cxt))
            },
            Decl::Println(t) => {
                Ok((
                    DeclTm::Println(self.infer_expr(cxt, t)?.0),
                    Val::U,
                    cxt.clone(),
                ))
            }
        }
    }
    pub fn infer_expr(&mut self, cxt: &Cxt, t: Raw) -> Result<(Tm, Rc<Val>), Error> {
        match t {
            // Infer variable types
            Raw::Var(x) => {
                match cxt.src_names.get(&x.data) {
                    Some((x, a)) => Ok((Tm::Var(lvl2ix(cxt.lvl, *x)), a.clone())),
                    None => Err(Error(format!("error name not in scope: {:?}", x))),
                }
            }

            // Infer lambda expressions
            Raw::Lam(x, Either::Icit(i), t) => {
                let new_meta = self.fresh_meta(cxt, &Val::U.into());
                let a = self.eval(&cxt.env, &new_meta);
                let new_cxt = cxt.bind(x.clone(), self.quote(cxt.lvl, &a), a.clone());
                let infered = self.infer_expr(&new_cxt, *t);
                let (t_inferred, b) = self.insert(&new_cxt, infered)?;
                let b_closure = self.close_val(cxt, &b);
                Ok((
                    Tm::Lam(x.clone(), i, Box::new(t_inferred)),
                    Val::Pi(x, i, a, b_closure).into(),
                ))
            }

            Raw::Lam(_, Either::Name(_), _) => Err(Error("infer named lambda".to_owned())),

            // Infer function applications
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
                let tty = self.force(&tty);
                let (a, b_closure) = match tty.as_ref() {
                    Val::Pi(_, i_t, a, b_closure) => {
                        if i == *i_t {
                            (a.clone(), b_closure.clone())
                        } else {
                            return Err(Error(format!("icit mismatch {:?} {:?}", i, i_t)));
                        }
                    }
                    _ => {
                        let new_meta = self.fresh_meta(cxt, &Val::U.into());
                        let a = self.eval(&cxt.env, &new_meta);
                        let b_closure = Closure(
                            cxt.env.clone(),
                            Rc::new(self.fresh_meta(
                                &cxt.bind(
                                    empty_span("x".to_string()),
                                    self.quote(cxt.lvl, &a),
                                    a.clone(),
                                ),
                                &Val::U.into(),
                            )),
                        );
                        self.unify_catch(
                            cxt,
                            &Val::Pi(
                                empty_span("x".to_string()),
                                i,
                                a.clone(),
                                b_closure.clone(),
                            ).into(),
                            &tty,
                        )?;
                        (a, b_closure)
                    }
                };
                let u_checked = self.check(cxt, *u, &a)?;
                Ok((
                    Tm::App(Box::new(t), Box::new(u_checked.clone()), i),
                    self.closure_apply(&b_closure, self.eval(&cxt.env, &u_checked)),
                ))
            }

            // Infer universe type
            Raw::U => Ok((Tm::U, Val::U.into())),

            // Infer dependent function types
            Raw::Pi(x, i, a, b) => {
                let a_checked = self.check_ty(cxt, *a)?;
                let a_eval = self.eval(&cxt.env, &a_checked);
                let b_checked = self.check_ty(
                    &cxt.bind(x.clone(), self.quote(cxt.lvl, &a_eval), a_eval),
                    *b,
                )?;
                Ok((
                    Tm::Pi(x, i, Box::new(a_checked), Box::new(b_checked)),
                    Val::U.into(),
                ))
            }

            // Infer let bindings
            Raw::Let(x, a, t, u) => {
                let a_checked = self.check_ty(cxt, *a)?;
                let va = self.eval(&cxt.env, &a_checked);
                let t_checked = self.check(cxt, *t, &va)?;
                let vt = self.eval(&cxt.env, &t_checked);
                let (u_inferred, b) = self.infer_expr(
                    &cxt.define(x.clone(), t_checked.clone(), vt.clone(), a_checked.clone(), va),
                    *u
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
                let new_meta = self.fresh_meta(cxt, &Val::U.into());
                let a = self.eval(&cxt.env, &new_meta);
                let t = self.fresh_meta(cxt, &a);
                Ok((t, a))
            }

            Raw::LiteralIntro(literal) => {
                Ok((Tm::LiteralIntro(literal), Val::LiteralType.into()))
            }
        }
    }
}
