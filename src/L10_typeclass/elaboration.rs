use std::{cmp::max, rc::Rc};

use colored::Colorize;

use crate::{list::List, parser_lib::Span};

use super::{
    Closure, Cxt, DeclTm, Error, Infer, Tm, VTy, Val,
    Lvl,
    empty_span, lvl2ix,
    parser::syntax::{Decl, Either, Icit, Raw},
    pattern_match::Compiler, MetaEntry,
    typeclass::Instance,
    unification::PartialRenaming,
    typeclass::Assertion,
};

impl Infer {
    fn insert_go(&mut self, cxt: &Cxt, t: Rc<Tm>, va: Rc<Val>) -> (Rc<Tm>, Rc<VTy>) {
        let va = self.force(&va);
        match va.as_ref() {
            Val::Pi(_, Icit::Impl, a, b) => {
                let m = self.fresh_meta(cxt, a.clone());
                let mv = self.eval(&cxt.env, &m);
                self.insert_go(
                    cxt,
                    Tm::App(t, m, Icit::Impl).into(),
                    self.closure_apply(b, mv),
                )
            }
            _ => (t, va),
        }
    }
    fn insert_t(&mut self, cxt: &Cxt, act: Result<(Rc<Tm>, Rc<VTy>), Error>) -> Result<(Rc<Tm>, Rc<VTy>), Error> {
        act.map(|(t, va)| self.insert_go(cxt, t, va))
    }
    fn insert(&mut self, cxt: &Cxt, act: Result<(Rc<Tm>, Rc<VTy>), Error>) -> Result<(Rc<Tm>, Rc<VTy>), Error> {
        act.and_then(|x| if let Tm::Lam(_, Icit::Impl, _) = x.0.as_ref() {
            Ok(x)
        } else {
            self.insert_t(cxt, Ok(x))
        })
    }
    fn insert_until_go(
        &mut self,
        cxt: &Cxt,
        name: Span<String>,
        t: Rc<Tm>,
        va: Rc<Val>,
    ) -> Result<(Rc<Tm>, Rc<VTy>), Error> {
        match self.force(&va).as_ref() {
            Val::Pi(x, Icit::Impl, a, b) => {
                if x.data == name.data {
                    Ok((t, Val::Pi(x.clone(), Icit::Impl, a.clone(), b.clone()).into()))
                } else {
                    let m = self.fresh_meta(cxt, a.clone());
                    let mv = self.eval(&cxt.env, &m);
                    self.insert_until_go(
                        cxt,
                        name,
                        Tm::App(t, m, Icit::Impl).into(),
                        self.closure_apply(b, mv),
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
        act: Result<(Rc<Tm>, Rc<VTy>), Error>,
    ) -> Result<(Rc<Tm>, Rc<VTy>), Error> {
        act.and_then(|(t, va)| self.insert_until_go(cxt, name, t, va))
    }
    pub fn check_pm_final(&mut self, cxt: &Cxt, t: Raw, a: Rc<Val>, ori: Rc<Val>) -> Result<(Rc<Tm>, Cxt), Error> {
        let t_span = t.to_span();
        let x = self.infer_expr(cxt, t);
        let (t_inferred, inferred_type) = self.insert(cxt, x)?;
        let new_cxt = self.unify_pm(cxt, &a, &inferred_type, t_span)?;
        let new_cxt = self.unify_pm(&new_cxt, &ori, &self.eval(&new_cxt.env, &t_inferred), t_span).unwrap_or(new_cxt);
        Ok((t_inferred, new_cxt))
    }
    pub fn check_pm(&mut self, cxt: &Cxt, t: Raw, a: Rc<Val>) -> Result<(Rc<Tm>, Cxt), Error> {
        let t_span = t.to_span();
        let x = self.infer_expr(cxt, t);
        let (t_inferred, inferred_type) = self.insert(cxt, x)?;
        let new_cxt = self.unify_pm(cxt, &a, &inferred_type, t_span)?;
        Ok((t_inferred, new_cxt))
    }
    fn unify_pm(&mut self, cxt: &Cxt, t: &Rc<Val>, t_prime: &Rc<Val>, t_span: Span<()>) -> Result<Cxt, Error> {
        //println!("  {}", self.meta.len());
        //println!("{:?} == {:?}", t, t_prime);
        let t = self.force(t);
        let t_prime = self.force(t_prime);
        match (t.as_ref(), t_prime.as_ref()) {
            (Val::Rigid(x, sp), _) if sp.is_empty() => { 
                Ok(cxt.update_cxt(self, *x, t_prime))
            }
            (_, Val::Rigid(x, sp)) if sp.is_empty() => { 
                Ok(cxt.update_cxt(self, *x, t))
            }
            (
                Val::SumCase { case_name: name1, datas: d1, .. },
                Val::SumCase { case_name: name2, datas: d2, .. },
            ) => {
                if name1 == name2 {
                    let mut cxt = cxt.clone();
                    for (x, y) in d1.iter().zip(d2.iter()) {
                        cxt = self.unify_pm(&cxt, &x.1, &y.1, t_span)?;
                    }
                    Ok(cxt)
                } else {
                    Err(Error(t_span.map(|_| "".to_string())))
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
                        cxt = self.unify_pm(&cxt, &x.1, &y.1, t_span)?;
                    }
                    Ok(cxt)
                } else {
                    Err(Error(t_span.map(|_| "".to_string())))
                }
            }
            (_, _) => {
                self.unify_catch(cxt, &t, &t_prime, t_span)
                    .map(|_| cxt.clone())
            }
        }
    }
    pub fn check_universe(&mut self, cxt: &Cxt, t: Raw) -> Result<(Rc<Tm>, u32), Error> {
        let t_span = t.to_span();
        let x = self.infer_expr(cxt, t);
        let (t_inferred, inferred_type) = self.insert(cxt, x)?;
        match inferred_type.as_ref() {
            Val::U(u) => Ok((t_inferred, *u)),
            Val::Flex(m, sp) => {
                let (pren, prune_non_linear) = self.invert(cxt.lvl, sp)
                    .map_err(|_| Error(t_span.map(|_| "invert failed".to_owned())))?;
                let mty = match self.meta[m.0 as usize] {
                    MetaEntry::Unsolved(ref a) => a.clone(),
                    _ => unreachable!(),
                };

                // if the spine was non-linear, we check that the non-linear arguments
                // can be pruned from the meta type (i.e. that the pruned solution will
                // be well-typed)
                if let Some(pr) = prune_non_linear {
                    self.prune_ty(&pr, &mty).map_err(|_| Error(t_span.map(|_| "prune failed".to_owned())))?; //TODO:revPruning?
                }

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
                        &PartialRenaming {
                            occ: Some(*m),
                            ..pren
                        },
                        &Val::U(0).into(),
                    ).map_err(|_| Error(t_span.map(|_| "when check universe, try to rename failed".to_string())))?;
                    let solution = self.eval(&List::new(), &self.lams(pren.dom, &mty, rhs));
                    self.meta[m.0 as usize] = MetaEntry::Solved(solution, mty);

                    Ok((t_inferred, 0))
                    //Err(Error(format!("when check universe, get pren {}", pren.dom.0)))
                }
            }
            _ => Err(Error(t_span.map(|_| format!("expected universe, got {:?}", inferred_type)))),
        }
    }
    pub fn check(&mut self, cxt: &Cxt, t: Raw, a: &Rc<Val>) -> Result<Rc<Tm>, Error> {
        //println!("{} {:?} {} {:?}", "check".blue(), t, "==".blue(), a);
        let a = self.force(a);
        match (t, a.as_ref()) {
            // Check lambda expressions
            (Raw::Lam(x, i, t), Val::Pi(x_t, i_t, a, b_closure))
                if (i.clone(), *i_t) == (Either::Name(x_t.clone()), Icit::Impl)
                    || i == Either::Icit(*i_t) =>
            {
                let body = self.check(
                    &cxt.bind(x.clone(), self.quote(cxt.lvl, a), a.clone()),
                    *t,
                    &self.closure_apply(b_closure, Val::vvar(cxt.lvl).into()),
                )?;
                Ok(Tm::Lam(x.clone(), *i_t, body).into())
            }
            (t, Val::Pi(x, Icit::Impl, a, b_closure)) => {
                let body = self.check(
                    &cxt.new_binder(x.clone(), self.quote(cxt.lvl, a)),
                    t,
                    &self.closure_apply(b_closure, Val::vvar(cxt.lvl).into()),
                )?;
                Ok(Tm::Lam(x.clone(), Icit::Impl, body).into())
            }
            // Check let bindings
            (Raw::Let(x, ret_typ, t, u), _) => {
                let (a_checked, _) = self.check_universe(cxt, *ret_typ)?;
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
                    a_checked,
                    t_checked,
                    u_checked,
                ).into())
            }

            // Handle holes
            (Raw::Hole, _) => Ok(self.fresh_meta(cxt, a)),

            (Raw::Match(expr, clause), _) => {
                let expr_span = expr.to_span();
                let (tm, typ) = self.infer_expr(cxt, *expr)?;
                let mut compiler = Compiler::new(a);
                let error = compiler.compile(self, typ, &clause, cxt, self.eval(&cxt.env, &tm))?;
                if !error.is_empty() {
                    Err(Error(expr_span.map(|_| format!("{error:?}"))))
                } else {
                    Ok(
                        Tm::Match(tm, compiler.pats).into()
                    ) //if there is any posible that has no return type?
                }
            }

            // General case: infer type and unify
            (t, _) => {
                let t_span = t.to_span();
                let x = self.infer_expr(cxt, t);
                let (t_inferred, inferred_type) = self.insert(cxt, x)?;
                self.unify_catch(cxt, &a, &inferred_type, t_span)?;
                Ok(t_inferred)
            }
        }
    }
    pub fn infer(&mut self, cxt: &Cxt, t: Decl) -> Result<(DeclTm, Rc<Val>, Cxt), Error> {
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
                let (ret_cxt, vty, vt, vtyp_pretty, vt_pretty) = {
                    let global_idx = Lvl(self.global.len() as u32);
                    let (typ_tm, _) = self.check_universe(ret_cxt, typ)?;
                    let vtyp = self.eval(&ret_cxt.env, &typ_tm);
                    //println!("------------------->");
                    //println!("{:?}", vtyp);
                    //println!("-------------------<");
                    let fake_cxt = ret_cxt.fake_bind(name.clone(), vtyp.clone(), global_idx);
                    self.global.insert(global_idx, Val::vvar(global_idx + 1919810).into());
                    let t_tm = self.check(&fake_cxt, bod, &vtyp)?;
                    self.solve_multi_trait(&fake_cxt, super::MetaVar(0)).unwrap();
                    let vtyp_pretty = super::pretty_tm(0, ret_cxt.names(), &self.nf(&ret_cxt.env, &typ_tm));
                    let vt_pretty = super::pretty_tm(0, fake_cxt.names(), &self.nf(&fake_cxt.env, &t_tm));
                    //println!("begin vt {}", "------".green());
                    let vt = self.eval(&fake_cxt.env, &t_tm);
                    self.global.insert(global_idx, vt.clone());
                    (
                        ret_cxt.define(name.clone(), t_tm, vt.clone(), typ_tm, vtyp.clone()),
                        vtyp,
                        vt,
                        vtyp_pretty,
                        vt_pretty,
                    )
                };
                Ok((
                    DeclTm::Def {
                        name: name.clone(),
                        typ: vty,
                        body: vt,
                        typ_pretty: vtyp_pretty,
                        body_pretty: vt_pretty,
                    },
                    //vt,
                    Val::U(0).into(),
                    ret_cxt,
                )) //TODO:vt may be wrong
            }
            Decl::Println(t) => Ok((
                DeclTm::Println(self.infer_expr(cxt, t)?.0),
                Val::U(0).into(),
                cxt.clone(),
            )),
            Decl::Enum {
                is_trait,
                name,
                params,
                cases,
            } => {
                let mut universe_lvl = 0;
                for p in params.iter() {
                    let u = self.infer_expr(cxt, p.1.clone());
                    if let Ok(t) = u {
                        if let Tm::U(lvl) = t.0.as_ref() {
                            universe_lvl = max(*lvl, universe_lvl);
                        }
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
                    universe_lvl,
                    is_trait,
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
                    let vtyp = self.eval(&cxt.env, &typ_tm);
                    let fake_cxt = cxt.fake_bind(name.clone(), vtyp.clone(), global_idx);
                    self.global.insert(global_idx, Val::vvar(global_idx + 1919810).into());
                    let t_tm = self.check(&fake_cxt, bod, &vtyp)?;
                    let vt = self.eval(&fake_cxt.env, &t_tm);
                    self.global.insert(global_idx, vt.clone());
                    cxt.define(name.clone(), t_tm, vt, typ_tm, vtyp)
                };
                for (c, typ) in cases.iter().zip(new_cases.clone().into_iter()) {
                    let body_ret_type = Raw::SumCase {
                        is_trait,
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
                        let vtyp = self.eval(&cxt.env, &typ_tm);
                        let t_tm = self.check(&cxt, bod, &vtyp)?;
                        let vt = self.eval(&cxt.env, &t_tm);
                        cxt.define(c.0.clone(), t_tm, vt, typ_tm, vtyp)
                    };
                }
                Ok((DeclTm::Enum {}, Val::U(0).into(), cxt))
            }
            Decl::ImplDecl { name, params, trait_name, trait_params, methods } => {
                let span = name.to_span();
                let mut cxt = cxt.clone();
                for (x, a, _) in params {
                    let (a_checked, _) = self.check_universe(&cxt, a)?;
                    let a_eval = self.eval(&cxt.env, &a_checked);
                    cxt = cxt.bind(x.clone(), self.quote(cxt.lvl, &a_eval), a_eval);
                }
                let typ = self.check_universe(&cxt, name.clone())?.0;
                let typ = self.eval(&cxt.env, &typ)
                    .to_typ()
                    .ok_or_else(|| Error(span.map(|_| "Not a type".to_string())))?;
                let mut trait_param = vec![typ.clone()];
                for a in trait_params.clone() {
                    let (a_checked, _) = self.check_universe(&cxt, a)?;
                    let a_eval = self.eval(&cxt.env, &a_checked);
                    match a_eval.to_typ() {
                        Some(x) => trait_param.push(x),
                        None => return Err(Error(span.map(|_| "Not a type".to_string()))),
                    };
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
                };
                // HAdd.hAdd.{u, v, w} {α : Type u} {β : Type v} {γ : outParam (Type w)} [self : HAdd α β γ] : α → β → γ
                // HAdd.{u, v, w} (α : Type u) (β : Type v) (γ : outParam (Type w)) : Type (max (max u v) w)
                self.trait_solver.impl_trait_for(trait_name.data.clone(), inst);
                let mut ret = std::iter::once(name)
                    .chain(trait_params)
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
                                    .fold(body, |ret, x| Raw::Lam(x.0.clone(), Either::Icit(x.2), Box::new(ret)))
                                )
                            )),
                            Either::Icit(Icit::Expl),
                        );
                    }
                }
                let (_, _, c) = self.infer(&cxt, Decl::Def {
                    name: trait_name.map(|_| typ_name.clone()),
                    params: vec![],
                    ret_type: Raw::Hole,
                    body: ret,
                })?;
                cxt = c;
                Ok((DeclTm::TraitImpl {}, Val::U(0).into(), cxt.clone()))
            },
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
                if let Ok((_, _, c)) = self.infer(&cxt, Decl::Enum {
                    is_trait: true,
                    name: name.clone(),
                    params: param,
                    cases: vec![(
                        name.map(|x| format!("{x}.mk")),
                        methods
                            .into_iter()
                            .map(|x| (
                                x.0.clone(),
                                std::iter::once((x.0.clone().map(|_| "this".to_owned()), Raw::Var(x.0.map(|_| "Self".to_owned())), Icit::Expl))
                                    .chain(x.1.into_iter())
                                    .rev()
                                    .fold(x.2, |a, b| {
                                        Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                                    }),
                                Icit::Expl,
                            ))
                            .collect(),
                        None,
                    )],
                }) {
                    cxt = c;
                }
                Ok((DeclTm::Trait {}, Val::U(0).into(), cxt.clone()))
            },
        }
    }
    pub fn infer_expr(&mut self, cxt: &Cxt, t: Raw) -> Result<(Rc<Tm>, Rc<Val>), Error> {
        /*println!(
            "{} {}",
            "infer".red(),
            t,
        );*/
        let t_span = t.to_span();
        match t {
            // Infer variable types
            Raw::Var(x) => match cxt.src_names.get(&x.data) {
                Some((x, a)) => Ok((Tm::Var(lvl2ix(cxt.lvl, *x)).into(), a.clone())),
                None => Err(Error(x.map(|x| format!("error name not in scope: {}", x)))),
            },

            Raw::Obj(x, t) => {
                if t.data == "mk" {
                    if let Raw::Var(sum_name) = x.as_ref() {
                        return self.infer_expr(cxt, Raw::Var(sum_name.clone().map(|n| format!("{n}.mk"))))
                    }
                }
                let (tm, a) = self.infer_expr(cxt, *x.clone())?;
                let a = self.force(&a);
                match (tm, a.as_ref()) {
                    (tm, Val::Sum(_, params, cases, _)) => {
                        let mut c = None;
                        if cases.len() == 1 {
                            if let Some(case) = cases.first() {
                                if case.data.contains(".mk") {
                                    let (_, case_typ) = self.infer_expr(cxt, Raw::Var(case.clone()))?;
                                    let mut ret = vec![];
                                    let mut typ = case_typ;
                                    let mut param = params.clone();
                                    param.reverse();
                                    while let Val::Pi(name, icit, ty, closure) = typ.as_ref().clone() {
                                        if icit == Icit::Expl {
                                            ret.push((name, ty.clone()));
                                            typ = self.closure_apply(&closure, Val::U(0).into())//TODO:not Val::U(0)
                                        } else {
                                            let val = param.pop()
                                                .map(|x| x.1)
                                                .unwrap_or(Val::U(0).into());
                                            ret.push((name, ty.clone()));
                                            typ = self.closure_apply(&closure, val)
                                        }
                                    }
                                    c = Some(ret);
                                }
                            }
                        }
                        if let Some(val) = c.and_then(|params| {
                                params.into_iter()
                                    .find(|(fields_name, _)| fields_name == &t)
                                    .map(|(_, ty)| ty)
                            }).or(
                            params
                                .iter()
                                .find(|(fields_name, _, _, _)| fields_name == &t)
                                .map(|(_, _, ty, _)| ty)
                                .cloned()
                            ) {
                                Ok((
                                    Tm::Obj(tm, t).into(),
                                    val,
                                ))
                            } else {
                                self.trait_wrap(cxt, t, a, x, tm)
                            }
                    }
                    (tm, Val::SumCase { datas: params, .. }) => {
                        if let Some(val) = params
                            .iter()
                            .find(|(fields_name, _, _)| fields_name == &t)
                            .map(|(_, ty, _)| ty) {
                                Ok((
                                    Tm::Obj(tm, t).into(),
                                    val.clone(),
                                ))
                            } else {
                                self.trait_wrap(cxt, t, a, x, tm)
                            }
                    }
                    (tm, _) => self.trait_wrap(cxt, t, a, x, tm),
                }
            },

            // Infer lambda expressions
            Raw::Lam(x, Either::Icit(i), t) => {
                let new_meta = self.fresh_meta(cxt, Val::U(0).into());
                let a = self.eval(&cxt.env, &new_meta);
                //TODO:below may be wrong
                let new_cxt = cxt.bind(x.clone(), self.quote(cxt.lvl, &a), a.clone());
                let infered = self.infer_expr(&new_cxt, *t);
                let (t_inferred, b) = self.insert(&new_cxt, infered)?;
                let b_closure = self.close_val(cxt, &b);
                Ok((
                    Tm::Lam(x.clone(), i, t_inferred).into(),
                    Val::Pi(x, i, a, b_closure).into(),
                ))
            }

            Raw::Lam(x, Either::Name(_), _) => Err(Error(x.map(|_| "infer named lambda".to_owned()))),

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
                let tty = self.force(&tty);
                let (a, b_closure) = match tty.as_ref() {
                    Val::Pi(_, i_t, a, b_closure) => {
                        if i == *i_t {
                            (a.clone(), b_closure.clone())
                        } else {
                            return Err(Error(t_span.map(|_| format!("icit mismatch {:?} {:?}", i, i_t))));
                        }
                    }
                    _ => {
                        let new_meta = self.fresh_meta(cxt, Val::U(0).into());
                        let a = self.eval(&cxt.env, &new_meta);
                        let b_closure = Closure(
                            cxt.env.clone(),
                            self.fresh_meta(
                                &cxt.bind(
                                    empty_span("x".to_string()),
                                    self.quote(cxt.lvl, &a),
                                    a.clone(),
                                ),
                                Val::U(0).into(),
                            ),
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
                            t_span,
                        )?;
                        (a, b_closure)
                    }
                };
                let u_checked = self.check(cxt, *u, &a)?;
                let ret_type = self.closure_apply(&b_closure, self.eval(&cxt.env, &u_checked));
                Ok((
                    Tm::App(t, u_checked, i).into(),
                    ret_type,
                ))
            }

            // Infer universe type
            Raw::U(x) => Ok((Tm::U(x).into(), Val::U(x + 1).into())),

            // Infer dependent function types
            Raw::Pi(x, i, a, b) => {
                let mut universe = 0;
                let (a_checked, lvl) = self.check_universe(cxt, *a)?;
                universe = max(universe, lvl);
                let a_eval = self.eval(&cxt.env, &a_checked);
                let (b_checked, lvl) = self.check_universe(
                    &cxt.bind(x.clone(), self.quote(cxt.lvl, &a_eval), a_eval),
                    *b,
                )?;
                universe = max(universe, lvl);
                Ok((
                    Tm::Pi(x, i, a_checked, b_checked).into(),
                    Val::U(universe).into(),
                ))
            }

            // Infer let bindings
            Raw::Let(x, a, t, u) => {
                let (a_checked, _) = self.check_universe(cxt, *a)?;
                let va = self.eval(&cxt.env, &a_checked);
                let t_checked = self.check(cxt, *t, &va)?;
                let vt = self.eval(&cxt.env, &t_checked);
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
                        a_checked,
                        t_checked,
                        u_inferred,
                    ).into(),
                    b,
                ))
            }

            // Infer holes
            Raw::Hole => {
                let new_meta = self.fresh_meta(cxt, Val::U(0).into());
                let a = self.eval(&cxt.env, &new_meta);
                let t = self.fresh_meta(cxt, a.clone());
                Ok((t, a))
            }

            Raw::LiteralIntro(literal) => Ok((Tm::LiteralIntro(literal).into(), Val::LiteralType.into())),

            Raw::Match(_, _) => Err(Error(t_span.map(|_| "try to infer match".to_owned()))),

            Raw::Sum(name, params, cases, universe, is_trait) => {
                let new_params = params
                    .iter()
                    .map(|ty| {
                        let (ty_checked, typ_val) = self.infer_expr(cxt, ty.2.clone())?;
                        let typ = self.quote(cxt.lvl, &typ_val);
                        Ok((ty.0.clone(), ty_checked, typ, ty.1))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                //TODO: universe need to consider cases?
                Ok((Tm::Sum(name, new_params, cases, is_trait).into(), Val::U(universe).into()))
            }

            Raw::SumCase {
                is_trait,
                typ,
                case_name,
                datas,
            } => {
                let (typ_checked, _) = self.infer_expr(cxt, *typ)?;
                let typ_val = self.eval(&cxt.env, &typ_checked);
                let datas = datas
                    .into_iter()
                    .map(|x| {
                        let (tm, _) = self.infer_expr(cxt, x.1)?;
                        Ok((x.0, tm, x.2))
                    })
                    .collect::<Result<_, _>>()?;
                Ok((
                    Tm::SumCase {
                        is_trait,
                        typ: typ_checked,
                        case_name,
                        datas,
                    }.into(),
                    typ_val,
                ))
            }
        }
    }
    fn trait_wrap(&mut self, cxt: &Cxt, t: Span<String>, a: Rc<Val>, x: Box<Raw>, tm: Rc<Tm>) -> Result<(Rc<Tm>, Rc<Val>), Error> {
        if let Some(typ) = a.to_typ() {
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
                    let mut args = vec![super::typeclass::Typ::Any; len];
                    args[0] = typ.clone();
                    self.trait_solver.clean();
                    self.trait_solver
                        .synth(Assertion {
                            name: x.to_string(),
                            arguments: args,
                        })
                        .is_some()
                })
                .map(|(trait_name, trait_params, _, (methods_name, methods_params, ret_type))| (
                    trait_name.clone(),
                    {
                        let params = {
                            let mut params = trait_params.clone();
                            params.push((
                                methods_name.clone().map(|_| "$this".to_owned()),
                                Raw::Var(methods_name.clone().map(|_| "Self".to_owned())),
                                Icit::Expl
                            ));
                            params.append(&mut methods_params.clone());
                            params.push((
                                methods_name.clone().map(|_| "$$".to_owned()),
                                trait_params.iter()
                                    .map(|x| x.0.clone())
                                    .fold(
                                        Raw::Var(methods_name.clone().map(|_| trait_name.clone())),
                                        |ret, x| Raw::App(Box::new(ret), Box::new(Raw::Var(x)), Either::Icit(Icit::Impl))
                                    ),
                                Icit::Impl
                            ));
                            params
                        };
                        let body = std::iter::once(Raw::Var(methods_name.clone().map(|_| "$this".to_owned())))
                            .chain(methods_params.iter().map(|x| Raw::Var(x.0.clone())))
                            .fold(
                                Raw::Obj(
                                    Box::new(Raw::Var(methods_name.clone().map(|_| "$$".to_owned()))),
                                    methods_name.clone(),
                                ),
                                |ret, x| Raw::App(Box::new(ret), Box::new(x), Either::Icit(Icit::Expl))
                            );
                        Raw::Let(
                            methods_name.clone().map(|x| format!("${x}")),
                            Box::new(params.iter().rev().fold(ret_type.clone(), |a, b| {
                                Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                            })),
                            Box::new(params.iter().rev().fold(body.clone(), |a, b| {
                                Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a))
                            })),
                            Box::new(Raw::App(
                                Box::new(Raw::Var(methods_name.clone().map(|x| format!("${x}")))),
                                x.clone(),
                                Either::Icit(Icit::Expl),
                            )),
                        )
                    }
                ))
                .collect::<Vec<_>>();
            //TODO: if traits.len() > 1, return err
            let traits = traits.first().and_then(|(_, decl)| {
                    self.infer_expr(cxt, decl.clone()).ok()
                });
            if let Some(ret) = traits {
                //println!("{}", super::pretty_tm(0, cxt.names(), &ret.0));
                Ok(ret)
            } else {
                Err(Error(t.clone().map(|t| format!(
                    "`{}`: {:?} has no object `{}`",
                    super::pretty_tm(0, cxt.names(), &tm),
                    a,
                    t,
                ))))
            }
        } else {
            Err(Error(t.clone().map(|t| format!(
                "`{}`: {:?} has no object `{}`",
                super::pretty_tm(0, cxt.names(), &tm),
                a,
                t,
            ))))
        }
    }
}
