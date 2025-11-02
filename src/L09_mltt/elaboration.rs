use std::{cmp::max, collections::HashMap};

use colored::Colorize;

use crate::{list::List, parser_lib::Span};

use super::{
    Closure, Cxt, DeclTm, Error, Infer, Tm, VTy, Val,
    empty_span, lvl2ix,
    parser::syntax::{Decl, Either, Icit, Raw, Pattern},
    pattern_match::Compiler, MetaEntry,
    PatternDetail,
    unification::PartialRenaming,
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
    pub fn check_pm_final(&mut self, cxt: &Cxt, t: Raw, a: Val, ori: Val) -> Result<(Tm, Cxt), Error> {
        let t_span = t.to_span();
        let x = self.infer_expr(cxt, t);
        let (t_inferred, inferred_type) = self.insert(cxt, x)?;
        let new_cxt = self.unify_pm(cxt, a, inferred_type, t_span)?;
        let new_cxt = self.unify_pm(&new_cxt, ori, self.eval(&new_cxt.env, t_inferred.clone()), t_span)?;
        Ok((t_inferred, new_cxt))
    }
    pub fn check_pm(&mut self, cxt: &Cxt, t: Raw, a: Val) -> Result<(Tm, Cxt), Error> {
        let t_span = t.to_span();
        let x = self.infer_expr(cxt, t);
        let (t_inferred, inferred_type) = self.insert(cxt, x)?;
        let new_cxt = self.unify_pm(cxt, a, inferred_type, t_span)?;
        Ok((t_inferred, new_cxt))
    }
    fn unify_pm(&mut self, cxt: &Cxt, t: Val, t_prime: Val, t_span: Span<()>) -> Result<Cxt, Error> {
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
                //Val::SumCase { case_name: name1, datas: d1, .. },
                //Val::SumCase { case_name: name2, datas: d2, .. },
                Val::Sum(name1, d1, ..),
                Val::Sum(name2, d2, ..),
            ) => {
                if name1 == name2 {
                    let mut cxt = cxt.clone();
                    for (x, y) in d1.iter().zip(d2.iter()) {
                        cxt = self.unify_pm(&cxt, x.1.clone(), y.1.clone(), t_span)?;
                    }
                    Ok(cxt)
                } else {
                    Err(Error(t_span.map(|_| "".to_string())))
                }
            }
            (u, v) => {
                self.unify_catch(cxt, u, v, t_span)
                    .map(|_| cxt.clone())
            }
        }
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
                    self.prune_ty(&pr, mty.clone()).map_err(|_| Error(t_span.map(|_| "prune failed".to_owned())))?; //TODO:revPruning?
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
                let (ret, error) = compiler.compile(self, typ, &clause, cxt, self.eval(&cxt.env, tm.clone()))?;
                if !error.is_empty() {
                    Err(Error(expr_span.map(|_| format!("{error:?}"))))
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
                    let (typ_tm, _) = self.check_universe(ret_cxt, typ)?;
                    let vtyp = self.eval(&ret_cxt.env, typ_tm.clone());
                    //println!("------------------->");
                    //println!("{:?}", vtyp);
                    //println!("-------------------<");
                    let fake_cxt = ret_cxt.fake_bind(name.clone(), vtyp.clone());
                    self.global.insert(cxt.lvl, Val::vvar(cxt.lvl + 1919810));
                    let t_tm = self.check(&fake_cxt, bod, vtyp.clone())?;
                    //println!("begin vt {}", "------".green());
                    let vt = self.eval(&fake_cxt.env, t_tm.clone());
                    self.global.insert(cxt.lvl, vt.clone());
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
                    ))//TODO: need to check the basic ret is this sum type or not
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
                    let (typ_tm, _) = self.check_universe(cxt, typ)?;
                    let vtyp = self.eval(&cxt.env, typ_tm.clone());
                    let fake_cxt = cxt.fake_bind(name.clone(), vtyp.clone());
                    self.global.insert(cxt.lvl, Val::vvar(cxt.lvl + 1919810));
                    let t_tm = self.check(&fake_cxt, bod, vtyp.clone())?;
                    let vt = self.eval(&fake_cxt.env, t_tm.clone());
                    self.global.insert(cxt.lvl, vt.clone());
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
                        let (typ_tm, _) = self.check_universe(&cxt, typ)?;
                        let vtyp = self.eval(&cxt.env, typ_tm.clone());
                        let t_tm = self.check(&cxt, bod, vtyp.clone())?;
                        let vt = self.eval(&cxt.env, t_tm.clone());
                        cxt.define(c.0.clone(), t_tm, vt, typ_tm, vtyp)
                    };
                }
                Ok((DeclTm::Enum {}, Val::U(0), cxt))
            }
        }
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
            // Infer variable types
            Raw::Var(x) => match cxt.src_names.get(&x.data) {
                Some((x, a)) => Ok((Tm::Var(lvl2ix(cxt.lvl, *x)), a.clone())),
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
                                    let mut param = params.clone();
                                    param.reverse();
                                    while let Val::Pi(name, icit, ty, closure) = typ {
                                        if icit == Icit::Expl {
                                            ret.push((name, *ty));
                                            typ = self.closure_apply(&closure, Val::U(0));//TODO:not Val::U(0)
                                        } else {
                                            let val = param.pop()
                                                .map(|x| x.1)
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
                                .map(|(_, _, ty, _)| ty)
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
                                .map(|(_, ty, _)| ty)
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
                            Box::new(self.fresh_meta(
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
        Pattern::Any(name) => PatternDetail::Any(name),
        Pattern::Con(name, params) if params.is_empty() && !all_constr_name.contains(&name.data) => {
            PatternDetail::Bind(name)
        },
        Pattern::Con(name, params) => {
            let new_params = params
                .into_iter()
                .map(|x| pattern_to_detail(cxt, x))
                .collect();
            PatternDetail::Con(name, new_params)
        }
    }
}
