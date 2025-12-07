use std::rc::Rc;

use colored::Colorize;

use crate::parser_lib::Span;

use super::{
    cxt::NameOrigin, empty_span, lvl2ix, parser::syntax::{Decl, Either, Icit, Raw}, Closure, Cxt, DeclTm, Error, Infer, Ix, Tm, VTy, Val
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
                let a_checked = self.check(cxt, *a_, &Val::U.into())?;
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
    pub fn infer(&mut self, cxt: &Cxt, t: Decl) -> Result<(DeclTm, Val, Cxt), Error> {
        match t {
            Decl::Def {
                name,
                params,
                ret_type,
                body
            } => {
                let ret_cxt = cxt;
                /*let mut cxt = cxt.clone();
                let param: Vec<Param<usize>> = params
                    .iter()
                    .map(|x| {
                        let (typ, _) = self.infer_expr(&cxt, &x.1)?;
                        let vtyp = self.eval(cxt.env.clone(), typ.clone());
                        cxt = cxt.bind(x.0.clone(), vtyp); //TODO: last param may not vtyp
                        Ok(Param(x.0.clone(), Box::new(typ)))
                    })
                    .collect::<Result<_, _>>()?;
                let result_u = check(&cxt, &result, &Value::U)?;
                let ret_val = eval(cxt.env.clone(), result_u.clone());
                let body_u = check(&cxt, body, &ret_val)?;
                let vt = eval(cxt.env.clone(), body_u.clone());*/
                //tele.iter().for_each(|x| cxt = cxt.bind(x.0, x.1));
                let typ = params.iter().rev().fold(ret_type.clone(), |a, b| {
                    Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                });
                let bod = params
                    .iter()
                    .rev()
                    .fold(body.clone(), |a, b| Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a)));
                let ret_cxt = {
                    let typ_tm = self.check(ret_cxt, typ, &Val::U.into())?;
                    let vtyp = self.eval(&ret_cxt.env, &typ_tm);
                    //println!("------------------->");
                    //println!("{:?}", vtyp);
                    //println!("-------------------<");
                    let t_tm = self.check(ret_cxt, bod, &vtyp)?;
                    //println!("begin vt {}", "------".green());
                    let vt = self.eval(&ret_cxt.env, &t_tm);
                    ret_cxt.define(name.clone(), t_tm, vt, typ_tm, vtyp)
                };
                Ok((
                    DeclTm::Def {
                        /*name: name.clone(),
                        params: param,
                        ret_type: result_u,
                        body: body_u,*/
                    },
                    //vt,
                    Val::U,
                    ret_cxt,
                )) //TODO:vt may be wrong
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
                //TODO:below may be wrong
                let new_cxt = cxt.bind(x.clone(), self.quote(cxt.lvl, &a), a.clone());
                let infered = self.infer_expr(&new_cxt, *t);
                let (t_inferred, b) = self.insert(&new_cxt, infered)?;
                let b_closure = self.close_val(cxt, &b);
                Ok((
                    Tm::Lam(x.clone(), i, Box::new(t_inferred)),
                    Val::Pi(x, i, a, b_closure).into(),
                ))
            }

            Raw::Lam(x, Either::Name(_), t) => Err(Error("infer named lambda".to_owned())),

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
                //println!("{} {:?} -> {:?}", "infer___".red(), t, tty); //debug
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
                let a_checked = self.check(cxt, *a, &Val::U.into())?;
                let a_eval = self.eval(&cxt.env, &a_checked);
                let b_checked = self.check(
                    &cxt.bind(x.clone(), self.quote(cxt.lvl, &a_eval), a_eval),
                    *b,
                    &Val::U.into(),
                )?;
                Ok((
                    Tm::Pi(x, i, Box::new(a_checked), Box::new(b_checked)),
                    Val::U.into(),
                ))
            }

            // Infer let bindings
            Raw::Let(x, a, t, u) => {
                let a_checked = self.check(cxt, *a, &Val::U.into())?;
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
