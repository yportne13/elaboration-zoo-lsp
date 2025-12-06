use std::collections::HashMap;

use colored::Colorize;

use crate::{list::List, parser_lib::Span};

use super::{
    Closure, Cxt, DeclTm, Error, Infer, Ix, Tm, VTy, Val,
    cxt::NameOrigin, Lvl,
    empty_span, lvl2ix,
    parser::syntax::{Decl, Either, Icit, Raw, Pattern},
    pattern_match::Compiler,
    PatternDetail,
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
            _ => Err(Error(format!("no named implicit arg {:?}", name))),
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
    pub fn check_pm_final(&mut self, cxt: &Cxt, t: Raw, a: Val, ori: Val) -> Result<(Tm, Cxt), Error> {
        let x = self.infer_expr(cxt, t);
        let (t_inferred, inferred_type) = self.insert(cxt, x)?;
        let new_cxt = self.unify_pm(cxt, a, inferred_type)?;
        let new_cxt = self.unify_pm(&new_cxt, ori, self.eval(&new_cxt.env, t_inferred.clone()))?;
        Ok((t_inferred, new_cxt))
    }
    pub fn check_pm(&mut self, cxt: &Cxt, t: Raw, a: Val) -> Result<(Tm, Cxt), Error> {
        let x = self.infer_expr(cxt, t);
        let (t_inferred, inferred_type) = self.insert(cxt, x)?;
        let new_cxt = self.unify_pm(cxt, a, inferred_type)?;
        Ok((t_inferred, new_cxt))
    }
    fn unify_pm(&mut self, cxt: &Cxt, t: Val, t_prime: Val) -> Result<Cxt, Error> {
        //println!("  {}", self.meta.len());
        //println!("{:?} == {:?}", t, t_prime);
        match (self.force(t), self.force(t_prime)) {
            (Val::Rigid(x, sp), v) if sp.is_empty() => { 
                Ok(cxt.update_cxt(self, x, v))
            }
            (v, Val::Rigid(x, sp)) if sp.is_empty() => { 
                Ok(cxt.update_cxt(self, x, v))
            }
            (
                Val::SumCase { case_name: name1, datas: d1, .. },
                Val::SumCase { case_name: name2, datas: d2, .. },
            ) => {
                if name1 == name2 {
                    let mut cxt = cxt.clone();
                    for (x, y) in d1.iter().zip(d2.iter()) {
                        cxt = self.unify_pm(&cxt, x.1.clone(), y.1.clone())?;
                    }
                    Ok(cxt)
                } else {
                    Err(Error("".to_string()))
                }
            }
            (
                //Val::SumCase { case_name: name1, datas: d1, .. },
                //Val::SumCase { case_name: name2, datas: d2, .. },
                Val::Sum(name1, d1, ..),
                Val::Sum(name2, d2, ..),
            ) => {
                if name1 == name2 {
                    let mut cxt = cxt.clone();
                    for (x, y) in d1.iter().zip(d2.iter()) {
                        cxt = self.unify_pm(&cxt, x.1.clone(), y.1.clone())?;
                    }
                    Ok(cxt)
                } else {
                    Err(Error("".to_string()))
                }
            }
            (u, v) => {
                self.unify_catch(cxt, u, v)
                    .map(|_| cxt.clone())
            }
        }
    }
    pub fn check(&mut self, cxt: &Cxt, t: Raw, a: Val) -> Result<Tm, Error> {
        //println!("{} {:?} {} {:?}", "check".blue(), t, "==".blue(), a);
        //println!("{} {:?} {} {}", "check".blue(), t, "==".blue(), super::pretty::pretty_tm(0, cxt.names(), &self.quote(cxt.lvl, a.clone())));
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
                let a_checked = self.check(cxt, *a, Val::U)?;
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
                let (tm, typ) = self.infer_expr(cxt, *expr)?;
                let mut compiler = Compiler::new(expected);
                let (ret, error) = compiler.compile(self, typ, &clause, cxt, self.eval(&cxt.env, tm.clone()))?;
                if !error.is_empty() {
                    Err(Error(format!("{error:?}")))
                } else {
                    let tree = ret
                        .iter()
                        .map(|x| (x.1, x.0.clone()))
                        .collect::<HashMap<_, _>>();
                    let t = clause
                        .into_iter()
                        .enumerate()
                        .map(|(idx, x)| (pattern_to_detail(cxt, x.0), tree.get(&idx).unwrap().clone()))
                        .collect();
                    /*if let Some(ret_type) = compiler.ret_type.clone() {
                        println!("get match ret: {:?}", ret_type);
                    }*/
                    Ok(
                        Tm::Match(Box::new(tm), t)
                    ) //if there is any posible that has no return type?
                }
            }

            // General case: infer type and unify
            (t, expected) => {
                let x = self.infer_expr(cxt, t);
                let (t_inferred, inferred_type) = self.insert(cxt, x)?;
                self.unify_catch(cxt, expected, inferred_type)?;
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
                    let typ_tm = self.check(ret_cxt, typ, Val::U)?;
                    let vtyp = self.eval(&ret_cxt.env, typ_tm.clone());
                    //println!("------------------->");
                    //println!("{:?}", vtyp);
                    //println!("-------------------<");
                    let fake_cxt = ret_cxt.fake_bind(name.clone(), typ_tm.clone(), vtyp.clone(), global_idx);
                    self.global.insert(global_idx, Val::vvar(global_idx + 1919810));
                    //println!("begin to check {}", name.data.red());
                    let t_tm = self.check(&fake_cxt, bod, vtyp.clone())?;
                    //println!("begin vt {}", "------".green());
                    let vt = self.eval(&fake_cxt.env, t_tm.clone());
                    self.global.insert(global_idx, vt.clone());
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
            }
            Decl::Println(t) => Ok((
                DeclTm::Println(self.infer_expr(cxt, t)?.0),
                Val::U,
                cxt.clone(),
            )),
            Decl::Enum {
                name,
                params,
                cases,
            } => {
                let new_params: Vec<_> = params
                    .iter()
                    .map(|x| (x.0.clone(), x.2, Raw::Var(x.0.clone())))
                    .collect();
                let default_ret = params
                    .iter()
                    .filter(|x| x.2 == Icit::Impl)
                    //.rev()
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
                    ))//TODO: need to check the basic ret is this sum type or not
                    .collect::<Vec<_>>();
                let sum = Raw::Sum(
                    name.clone(),
                    new_params.clone(),
                    new_cases.iter().map(|x| x.0.clone()).collect(),
                );
                let typ = params.iter().rev().fold(Raw::U, |a, b| {
                    Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                });
                let bod = params.iter().rev().fold(sum.clone(), |a, b| {
                    Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a))
                });
                let mut cxt = {
                    let global_idx = Lvl(self.global.len() as u32);
                    let typ_tm = self.check(cxt, typ, Val::U)?;
                    let vtyp = self.eval(&cxt.env, typ_tm.clone());
                    let fake_cxt = cxt.fake_bind(name.clone(), typ_tm.clone(), vtyp.clone(), global_idx);
                    self.global.insert(global_idx, Val::vvar(global_idx + 1919810));
                    let t_tm = self.check(&fake_cxt, bod, vtyp.clone())?;
                    let vt = self.eval(&fake_cxt.env, t_tm.clone());
                    self.global.insert(global_idx, vt.clone());
                    cxt.define(name.clone(), t_tm, vt, typ_tm, vtyp)
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
                        let typ_tm = self.check(&cxt, typ, Val::U)?;
                        let vtyp = self.eval(&cxt.env, typ_tm.clone());
                        let t_tm = self.check(&cxt, bod, vtyp.clone())?;
                        let vt = self.eval(&cxt.env, t_tm.clone());
                        cxt.define(c.0.clone(), t_tm, vt, typ_tm, vtyp)
                    };
                }
                Ok((DeclTm::Enum {}, Val::U, cxt))
            }
        }
    }
    pub fn infer_expr(&mut self, cxt: &Cxt, t: Raw) -> Result<(Tm, Val), Error> {
        /*println!(
            "{} {:?} in\n{}",
            "infer".red(),
            t,
            cxt.env
                .iter()
                .map(|x| super::pretty_tm(0, cxt.names(), &self.quote(cxt.lvl, x.clone())))
                .map(|x| format!("    {x}"))
                //.map(|x| format!("{x:?}"))
                .reduce(|a, b| a + "\n" + &b)
                .unwrap_or(String::new())
        );*/
        match t {
            // Infer variable types
            Raw::Var(x) => match cxt.src_names.get(&x.data) {
                Some((x, a)) => Ok((Tm::Var(lvl2ix(cxt.lvl, *x)), a.clone())),
                None => Err(Error(format!("error name not in scope: {:?}", x))),
            },

            Raw::Obj(x, t) => {
                let (tm, a) = self.infer_expr(cxt, *x)?;
                match (tm, self.force(a)) {
                    (tm, Val::Sum(_, params, _)) => {
                        Ok((
                            Tm::Obj(Box::new(tm), t.clone()),
                            params
                                .into_iter()
                                .find(|(fields_name, _, _, _)| fields_name == &t)
                                .map(|(_, _, ty, _)| ty)
                                .ok_or_else(|| Error("error in obj".to_owned()))?
                        ))
                    }
                    (tm, Val::SumCase { datas: params, .. }) => {
                        Ok((
                            Tm::Obj(Box::new(tm), t.clone()),
                            params
                                .into_iter()
                                .find(|(fields_name, _, _)| fields_name == &t)
                                .map(|(_, ty, _)| ty)
                                .ok_or_else(|| Error("error in obj".to_owned()))?
                        ))
                    }
                    _ => Err(Error("error in obj".to_owned())),
                }
            },

            // Infer lambda expressions
            Raw::Lam(x, Either::Icit(i), t) => {
                let new_meta = self.fresh_meta(cxt, Val::U);
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
                let (a, b_closure) = match self.force(tty) {
                    Val::Pi(_, i_t, a, b_closure) => {
                        if i == i_t {
                            (*a, b_closure)
                        } else {
                            return Err(Error(format!("icit mismatch {:?} {:?}", i, i_t)));
                        }
                    }
                    tty => {
                        let new_meta = self.fresh_meta(cxt, Val::U);
                        let a = self.eval(&cxt.env, new_meta);
                        let b_closure = Closure(
                            cxt.env.clone(),
                            Box::new(self.fresh_meta(
                                &cxt.bind(
                                    empty_span("x".to_string()),
                                    self.quote(cxt.lvl, a.clone()),
                                    a.clone(),
                                ),
                                Val::U,
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
            Raw::U => Ok((Tm::U, Val::U)),

            // Infer dependent function types
            Raw::Pi(x, i, a, b) => {
                let a_checked = self.check(cxt, *a, Val::U)?;
                let a_eval = self.eval(&cxt.env, a_checked.clone());
                let b_checked = self.check(
                    &cxt.bind(x.clone(), self.quote(cxt.lvl, a_eval.clone()), a_eval),
                    *b,
                    Val::U,
                )?;
                Ok((
                    Tm::Pi(x, i, Box::new(a_checked), Box::new(b_checked)),
                    Val::U,
                ))
            }

            // Infer let bindings
            Raw::Let(x, a, t, u) => {
                let a_checked = self.check(cxt, *a, Val::U)?;
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
                let new_meta = self.fresh_meta(cxt, Val::U);
                let a = self.eval(&cxt.env, new_meta);
                let t = self.fresh_meta(cxt, a.clone());
                Ok((t, a))
            }

            Raw::LiteralIntro(literal) => Ok((Tm::LiteralIntro(literal), Val::LiteralType)),

            Raw::Match(_, _) => Err(Error("try to infer match".to_owned())),

            Raw::Sum(name, params, cases) => {
                let new_params = params
                    .iter()
                    .map(|ty| {
                        let (ty_checked, typ_val) = self.infer_expr(cxt, ty.2.clone())?;
                        let typ = self.quote(cxt.lvl, typ_val.clone());
                        Ok((ty.0.clone(), ty_checked, typ, ty.1))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                /*let new_cases = cases
                    .iter()
                    .map(|(name, ty)| {
                        Ok((
                            name.clone(),
                            self.infer_expr(&cxt, ty.clone())?.0,
                        ))
                    })
                    .collect::<Result<Vec<_>, _>>()?;*/
                Ok((Tm::Sum(name, new_params, cases), Val::U))
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
                    .collect::<Result<_, _>>()?;//TODO:this need new cxt
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

fn pattern_to_detail(cxt: &Cxt, pattern: Pattern) -> PatternDetail {
    let mut all_constr_name = cxt.env.iter()
        .flat_map(|x| match x {
            Val::Sum(_, _, x) => Some(
                x.iter().map(|x| x.data.clone()).collect::<Vec<_>>()
            ),
            Val::Lam(_, _, c) => {
                let mut tm = &c.1;
                let mut ret = None;
                loop {
                    match tm.as_ref() {
                        Tm::Sum(_, _, x) => {
                            ret = Some(x.iter().map(|x| x.data.clone()).collect::<Vec<_>>());
                            break;
                        }
                        Tm::Lam(_, _, c) => {
                            tm = c;
                        }
                        _ => {break;}
                    }
                }
                ret
            }
            _ => None,
        })
        .flatten()
        .collect::<std::collections::HashSet<_>>();
    match pattern {
        Pattern::Any(name, _) => PatternDetail::Any(name),
        Pattern::Con(name, params, _) if params.is_empty() && !all_constr_name.contains(&name.data) => {
            PatternDetail::Bind(name)
        },
        Pattern::Con(name, params, _) => {
            let new_params = params
                .into_iter()
                .map(|x| pattern_to_detail(cxt, x))
                .collect();
            PatternDetail::Con(name, new_params)
        }
    }
}
