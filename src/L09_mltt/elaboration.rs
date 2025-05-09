use std::{cmp::max, collections::HashMap};

use colored::Colorize;

use crate::{list::List, parser_lib::Span, L09_mltt::{pattern_match::Compiler, MetaEntry}};

use super::{
    Closure, Cxt, DeclTm, Error, Infer, Ix, Tm, VTy, Val,
    cxt::NameOrigin,
    empty_span, lvl2ix,
    parser::syntax::{Decl, Either, Icit, Raw},
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
    pub fn check_universe(&mut self, cxt: &Cxt, t: Raw) -> Result<(Tm, u32), Error> {
        let x = self.infer_expr(cxt, t);
        let (t_inferred, inferred_type) = self.insert(cxt, x)?;
        match inferred_type {
            Val::U(u) => Ok((t_inferred, u)),
            Val::Flex(m, sp) => {
                let (pren, prune_non_linear) = self.invert(cxt.lvl, sp.clone())
                    .map_err(|_| Error("invert failed".to_owned()))?;
                let mty = match self.meta[m.0 as usize] {
                    MetaEntry::Unsolved(ref a) => a.clone(),
                    _ => unreachable!(),
                };

                // if the spine was non-linear, we check that the non-linear arguments
                // can be pruned from the meta type (i.e. that the pruned solution will
                // be well-typed)
                if let Some(pr) = prune_non_linear {
                    self.prune_ty(&pr, mty.clone()).map_err(|_| Error("prune failed".to_owned()))?; //TODO:revPruning?
                }

                if pren.dom.0 == 0 {
                    match self.force(mty.clone()) {
                        Val::U(x) => {//TODO:x?
                            self.meta[m.0 as usize] = MetaEntry::Solved(Val::U(0), mty);
                            Ok((t_inferred, 0))
                        },
                        _ => Err(Error(format!("meta type {:?} is not a universe", self.force(mty)))),
                    }
                } else {
                    Err(Error(format!("when check universe, get pren {}", pren.dom.0)))
                }
            }
            _ => Err(Error(format!("expected universe, got {:?}", inferred_type))),
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
                    let (typ_tm, _) = self.check_universe(ret_cxt, typ)?;
                    let vtyp = self.eval(&ret_cxt.env, typ_tm.clone());
                    //println!("------------------->");
                    //println!("{:?}", vtyp);
                    //println!("-------------------<");
                    let fake_cxt = ret_cxt.fake_bind(name.clone(), typ_tm.clone(), vtyp.clone());
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
                        if let Ok((_, lvl)) = self.check_universe(cxt, c.clone()) {
                            universe_lvl = max(lvl, universe_lvl);
                        }
                    }
                }
                let new_params: Vec<_> = params.iter().map(|x| Raw::Var(x.0.clone())).collect();
                let sum = Raw::Sum(name.clone(), new_params.clone(), cases.clone());
                let typ = params.iter().rev().fold(Raw::U(universe_lvl), |a, b| {
                    Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                });
                let bod = params.iter().rev().fold(sum.clone(), |a, b| {
                    Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a))
                });
                let mut cxt = {
                    let (typ_tm, _) = self.check_universe(cxt, typ)?;
                    let vtyp = self.eval(&cxt.env, typ_tm.clone());
                    let fake_cxt = cxt.bind(name.clone(), typ_tm.clone(), vtyp.clone());
                    let t_tm = self.check(&fake_cxt, bod, vtyp.clone())?;
                    let vt = self.eval(&fake_cxt.env, t_tm.clone());
                    cxt.define(name.clone(), t_tm, vt, typ_tm, vtyp)
                };
                for c in cases.clone() {
                    let typ =
                        params
                            .iter()
                            .cloned()
                            .chain(c.1.iter().enumerate().map(|(idx, x)| {
                                (empty_span(format!("_{idx}")), x.clone(), Icit::Expl)
                            }))
                            .rev()
                            .fold(sum.clone(), |a, b| {
                                Raw::Pi(b.0, b.2, Box::new(b.1), Box::new(a))
                            });
                    let bod =
                        params
                            .iter()
                            .cloned()
                            .chain(c.1.iter().enumerate().map(|(idx, x)| {
                                (empty_span(format!("_{idx}")), x.clone(), Icit::Expl)
                            }))
                            .rev()
                            .fold(
                                Raw::SumCase {
                                    sum_name: name.clone(),
                                    params: new_params.clone(),
                                    cases: cases.clone(),
                                    case_name: c.0.clone(),
                                    datas: params
                                        .iter()
                                        .map(|x| x.0.clone())
                                        .chain(
                                            c.1.iter()
                                                .enumerate()
                                                .map(|(idx, _)| empty_span(format!("_{idx}"))),
                                        )
                                        .map(Raw::Var)
                                        .collect(),
                                },
                                |a, b| Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a)),
                            );
                    cxt = {
                        let (typ_tm, _) = self.check_universe(&cxt, typ)?;
                        let vtyp = self.eval(&cxt.env, typ_tm.clone());
                        let t_tm = self.check(&cxt, bod, vtyp.clone())?;
                        let vt = self.eval(&cxt.env, t_tm.clone());
                        cxt.define(c.0, t_tm, vt, typ_tm, vtyp)
                    };
                }
                Ok((DeclTm::Enum {}, Val::U(0), cxt))
            }
            Decl::Struct {
                name,
                params,
                fields,
            } => {
                let mut universe_lvl = 0;
                for p in params.iter() {
                    if let Ok((Tm::U(lvl), _)) = self.infer_expr(cxt, p.1.clone()) {
                        universe_lvl = max(lvl, universe_lvl);
                    }
                }
                for field in fields.iter() {
                    if let Ok((_, lvl)) = self.check_universe(cxt, field.1.clone()) {
                        universe_lvl = max(lvl, universe_lvl);
                    }
                }
                let new_params: Vec<_> = params.iter().map(|x| Raw::Var(x.0.clone())).collect();
                let sum = Raw::StructType(name.clone(), new_params.clone(), fields.clone());
                let typ = params.iter().rev().fold(Raw::U(universe_lvl), |a, b| {
                    Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                });
                let bod = params.iter().rev().fold(sum.clone(), |a, b| {
                    Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a))
                });
                let cxt = {
                    let (typ_tm, _) = self.check_universe(cxt, typ)?;
                    let vtyp = self.eval(&cxt.env, typ_tm.clone());
                    let fake_cxt = cxt.bind(name.clone(), typ_tm.clone(), vtyp.clone());
                    let t_tm = self.check(&fake_cxt, bod, vtyp.clone())?;
                    let vt = self.eval(&fake_cxt.env, t_tm.clone());
                    cxt.define(name.clone(), t_tm, vt, typ_tm, vtyp)
                };

                let new_fields: Vec<_> = fields.iter().map(|x| (x.0.clone(), Raw::Var(x.0.clone()))).collect();
                let data = Raw::StructData(name.clone(), new_params.clone(), new_fields.clone());
                let typ = params.iter().cloned().chain(
                    fields.iter().cloned().map(|(a, b)| (a, b, Icit::Expl))
                ).rev().fold(sum, |a, b| {
                    Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                });
                let bod = params.iter().cloned().chain(
                    fields.iter().cloned().map(|(a, b)| (a, b, Icit::Expl))
                ).rev().fold(data.clone(), |a, b| {
                    Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a))
                });
                let cxt = {
                    let (typ_tm, _) = self.check_universe(&cxt, typ)?;
                    let vtyp = self.eval(&cxt.env, typ_tm.clone());
                    let fake_cxt = cxt.bind(name.clone(), typ_tm.clone(), vtyp.clone());
                    let t_tm = self.check(&fake_cxt, bod, vtyp.clone())?;
                    let vt = self.eval(&fake_cxt.env, t_tm.clone());
                    cxt.define(name.map(|x| format!("{x}.apply")), t_tm, vt, typ_tm, vtyp)
                };
                Ok((DeclTm::Struct {}, Val::U(0), cxt))
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
        match t {
            // Infer variable types
            Raw::Var(x) => match cxt.src_names.get(&x.data) {
                Some((x, a)) => Ok((Tm::Var(lvl2ix(cxt.lvl, *x)), a.clone())),
                None => Err(Error(format!("error name not in scope: {:?}", x))),
            },

            Raw::Obj(x, t) => {
                let (tm, a) = self.infer_expr(cxt, *x)?;
                match (tm, a) {
                    (tm, Val::StructType(_, _, fields)) => {
                        Ok((
                            Tm::Obj(Box::new(tm), t.clone()),
                            fields
                                .into_iter()
                                .find(|(fields_name, _)| fields_name == &t)
                                .map(|(_, ty)| ty)
                                .ok_or_else(|| Error("error in obj".to_owned()))?
                        ))
                    }
                    (tm, Val::StructData(_, _, fields)) => {
                        Ok((
                            Tm::Obj(Box::new(tm), t.clone()),
                            fields
                                .into_iter()
                                .find(|(fields_name, _)| fields_name == &t)
                                .map(|(_, ty)| ty)
                                .ok_or_else(|| Error("error in obj".to_owned()))?
                        ))
                    }
                    _ => Err(Error("error in obj".to_owned())),
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

            Raw::Match(expr, clause) => {
                let (tm, typ) = self.infer_expr(cxt, *expr)?;
                let mut compiler = Compiler::new();
                let (ret, error) = compiler.compile(self, tm.clone(), typ, &clause, cxt)?;
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
                        .map(|(idx, x)| (x.0, tree.get(&idx).unwrap().clone()))
                        .collect();
                    Ok((
                        Tm::Match(Box::new(tm), t),
                        compiler.ret_type.unwrap_or(Val::U(0)),
                    )) //if there is any posible that has no return type?
                }
            }

            Raw::Sum(name, params, cases) => {
                let mut universe = 0;
                let new_params = params
                    .iter()
                    .map(|ty| {
                        let (ty_checked, lvl) = self.check_universe(cxt, ty.clone())?;
                        universe = max(universe, lvl);
                        Ok(ty_checked)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                for case in cases.iter() {
                    let (_, case_params) = case;
                    for c in case_params {
                        let (_, lvl) = self.check_universe(cxt, c.clone())?;
                        universe = max(universe, lvl);
                    }
                }
                //TODO: universe need to consider cases?
                Ok((Tm::Sum(name, new_params, cases), Val::U(universe)))
            }

            Raw::SumCase {
                sum_name,
                params,
                cases,
                case_name,
                datas,
            } => {
                let new_params = params
                    .iter()
                    .map(|ty| {
                        let (ty_checked, _) = self.check_universe(cxt, ty.clone())?;
                        let ty_checked = self.eval(&cxt.env, ty_checked);
                        Ok(ty_checked)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let datas = datas
                    .into_iter()
                    .map(|x| self.infer_expr(cxt, x).map(|x| x.0))
                    .collect::<Result<_, _>>()?;
                Ok((
                    Tm::SumCase {
                        sum_name: sum_name.clone(),
                        case_name,
                        params: datas,
                        cases_name: cases.iter().map(|x| x.0.clone()).collect(),
                    },
                    Val::Sum(sum_name, new_params, cases),
                ))
            }

            Raw::StructType(name, params, fields) => {
                let mut universe = 0;
                let new_params = params
                    .iter()
                    .map(|ty| {
                        let (ty_checked, lvl) = self.check_universe(cxt, ty.clone())?;
                        universe = max(universe, lvl);
                        Ok(ty_checked)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let new_fields = fields
                    .into_iter()
                    .map(|(name, ty)| {
                        let (ty_checked, lvl) = self
                            .check_universe(cxt, ty)?;
                        universe = max(universe, lvl);
                        Ok((name, ty_checked))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok((Tm::StructType(name, new_params, new_fields), Val::U(universe)))
            }
            Raw::StructData(name, params, fields) => {
                let new_params = params
                    .iter()
                    .map(|ty| {
                        let (ty_checked, _) = self.check_universe(cxt, ty.clone())?;
                        Ok(ty_checked)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let params_type = new_params.iter()
                    .map(|x| self.eval(&cxt.env, x.clone()))
                    .collect();
                let (new_fields_data, new_fields_type) = fields
                    .into_iter()
                    .map(|(name, ty)| {
                        let (tm, ty_checked) = self
                            .infer_expr(cxt, ty)?;
                        Ok(((name.clone(), tm), (name, ty_checked)))
                    })
                    .collect::<Result<(Vec<_>, Vec<_>), _>>()?;
                Ok((Tm::StructData(name.clone(), new_params, new_fields_data), Val::StructType(name, params_type, new_fields_type)))
            }
        }
    }
}
