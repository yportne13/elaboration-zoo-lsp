use std::cmp::max;

use colored::Colorize;
use smol_str::SmolStr;

use crate::{list::List, parser_lib::{Span, ToSpan}};

use super::{
    Closure, Cxt, DeclTm, Error, Infer, PrimFunc, Tm, VTy, Val,
    Lvl, Rc, MetaVar,
    empty_span, lvl2ix,
    parser::syntax::{Decl, Either, Icit, Raw},
    pattern_match::Compiler, MetaEntry,
    typeclass::Instance,
    unification::PartialRenaming,
    typeclass::Assertion,
};

/// Prefix a declaration's names with the given package prefix.
fn prefix_decl_name(d: Decl, prefix: &SmolStr) -> Decl {
    match d {
        Decl::Def { name, params, ret_type, body } => Decl::Def {
            name: name.map(|n| SmolStr::new(format!("{prefix}.{n}"))),
            params,
            ret_type,
            body,
        },
        Decl::Println(_) => d,
        Decl::Enum { is_trait, name, params, cases } => Decl::Enum {
            is_trait,
            name: name.map(|n| SmolStr::new(format!("{prefix}.{n}"))),
            params,
            cases, // case names are NOT prefixed — they get prefixed by the enum elaboration
        },
        Decl::TraitDecl { name, params, supertraits, methods, assoc_defaults } => Decl::TraitDecl {
            name: name.map(|n| SmolStr::new(format!("{prefix}.{n}"))),
            params,
            supertraits,
            methods: methods.into_iter().map(|(mn, mparams, mret, mbody)| {
                (mn.map(|n| SmolStr::new(format!("{prefix}.{n}"))), mparams, mret, mbody)
            }).collect(),
            assoc_defaults,
        },
        Decl::ImplDecl { name, params, trait_name, trait_params, methods, need_create } => Decl::ImplDecl {
            name,
            params,
            trait_name,
            trait_params,
            methods: methods.into_iter().map(|(m, is_static)| (prefix_decl_name(m, prefix), is_static)).collect(),
            need_create,
        },
        Decl::Package { path } => Decl::Package {
            path: path.into_iter().map(|s| s.map(|n| SmolStr::new(format!("{prefix}.{n}")))).collect(),
        },
        Decl::Import { .. } => d,
        Decl::Derive { traits, decl } => Decl::Derive {
            traits,
            decl: Box::new(prefix_decl_name(*decl, prefix)),
        },
    }
}

impl Infer {
    fn insert_go(&mut self, cxt: &Cxt, t: Rc<Tm>, va: Rc<Val>) -> (Rc<Tm>, Rc<VTy>) {
        let va = self.force(&cxt.decl, &va);
        match va.as_ref() {
            Val::Pi(_, Icit::Impl, a, b) => {
                //println!("insert {:?}", a);
                let m = self.fresh_meta(cxt, a.clone());
                let mv = self.eval(&cxt.decl, &cxt.env, &m);
                self.insert_go(
                    cxt,
                    Tm::App(t, m, Icit::Impl).into(),
                    self.closure_apply(&cxt.decl, b, mv),
                )
            }
            _ => (t, va),
        }
    }
    fn insert_t(&mut self, cxt: &Cxt, act: Result<(Rc<Tm>, Rc<VTy>), Error>) -> Result<(Rc<Tm>, Rc<VTy>), Error> {
        act.map(|(t, va)| self.insert_go(cxt, t, va))
    }
    pub fn insert(&mut self, cxt: &Cxt, act: Result<(Rc<Tm>, Rc<VTy>), Error>) -> Result<(Rc<Tm>, Rc<VTy>), Error> {
        act.and_then(|x| if let Tm::Lam(_, Icit::Impl, _) = x.0.as_ref() {
            Ok(x)
        } else {
            self.insert_t(cxt, Ok(x))
        })
    }
    fn insert_until_go(
        &mut self,
        cxt: &Cxt,
        name: Span<SmolStr>,
        t: Rc<Tm>,
        va: Rc<Val>,
    ) -> Result<(Rc<Tm>, Rc<VTy>), Error> {
        match self.force(&cxt.decl, &va).as_ref() {
            Val::Pi(x, Icit::Impl, a, b) => {
                if x.data == name.data {
                    Ok((t, Val::Pi(x.clone(), Icit::Impl, a.clone(), b.clone()).into()))
                } else {
                    let m = self.fresh_meta(cxt, a.clone());
                    let mv = self.eval(&cxt.decl, &cxt.env, &m);
                    self.insert_until_go(
                        cxt,
                        name,
                        Tm::App(t, m, Icit::Impl).into(),
                        self.closure_apply(&cxt.decl, b, mv),
                    )
                }
            }
            _ => Err(Error(name.map(|x| format!("no named implicit arg {}", x)), vec![])),
        }
    }
    fn insert_until_name(
        &mut self,
        cxt: &Cxt,
        name: Span<SmolStr>,
        act: Result<(Rc<Tm>, Rc<VTy>), Error>,
    ) -> Result<(Rc<Tm>, Rc<VTy>), Error> {
        act.and_then(|(t, va)| self.insert_until_go(cxt, name, t, va))
    }
    pub fn check_pm_final(&mut self, cxt: &Cxt, t: Raw, a: Rc<Val>, ori: Rc<Val>) -> Result<(Rc<Tm>, Cxt), Error> {
        let t_span = t.to_span();
        let x = self.infer_expr(cxt, t);
        let (t_inferred, inferred_type) = self.insert(cxt, x)?;
        let new_cxt = self.unify_pm(cxt, &a, &inferred_type, t_span)?;
        let new_cxt = self.unify_pm(&new_cxt, &ori, &self.eval(&new_cxt.decl, &new_cxt.env, &t_inferred), t_span).unwrap_or(new_cxt);
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
        let t = self.force(&cxt.decl, t);
        let t_prime = self.force(&cxt.decl, t_prime);
        match (t.as_ref(), t_prime.as_ref()) {
            (Val::Rigid(x1, sp1), Val::Rigid(x2, sp2)) if sp1.is_empty() && sp2.is_empty() && x1 == x2 => {
                Ok(cxt.update_cxt(self, *x1, t_prime, false))
            }
            (Val::Rigid(x, sp), _) if sp.is_empty() => { 
                Ok(cxt.update_cxt(self, *x, t_prime, true))
            }
            (_, Val::Rigid(x, sp)) if sp.is_empty() => { 
                Ok(cxt.update_cxt(self, *x, t, true))
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
                    Err(Error(t_span.map(|_| "".to_string()), vec![]))
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
                    Err(Error(t_span.map(|_| "".to_string()), vec![]))
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
                let (pren, prune_non_linear) = self.invert(cxt.lvl, &cxt.decl, sp)
                    .map_err(|_| Error(t_span.map(|_| "invert failed".to_owned()), vec![]))?;
                let mty = match self.meta[m.0 as usize] {
                    MetaEntry::Unsolved(ref a, _, _) => a.clone(),
                    _ => unreachable!(),
                };

                // if the spine was non-linear, we check that the non-linear arguments
                // can be pruned from the meta type (i.e. that the pruned solution will
                // be well-typed)
                if let Some(pr) = prune_non_linear {
                    self.prune_ty(&cxt.decl, &pr, &mty).map_err(|_| Error(t_span.map(|_| "prune failed".to_owned()), vec![]))?; //TODO:revPruning?
                }

                if pren.dom.0 == 0 {
                    let mty = self.force(&cxt.decl, &mty);
                    match mty.as_ref() {
                        Val::U(x) => {//TODO:x?
                            self.meta[m.0 as usize] = MetaEntry::Solved(Val::U(0).into(), mty);
                            Ok((t_inferred, 0))
                        },
                        _ => {
                            let err_typ = self.force(&cxt.decl, &mty);
                            Err(Error(t_span.map(|_| format!("meta type {:?} is not a universe", err_typ)), vec![]))
                        },
                    }
                } else {
                    let rhs = self.rename(
                        &cxt.decl,
                        &PartialRenaming {
                            occ: Some(*m),
                            ..pren
                        },
                        &Val::U(0).into(),
                    ).map_err(|_| Error(t_span.map(|_| "when check universe, try to rename failed".to_string()), vec![]))?;
                    let solution = self.eval(&cxt.decl, &List::new(), &self.lams(pren.dom, &cxt.decl, &mty, rhs));
                    self.meta[m.0 as usize] = MetaEntry::Solved(solution, mty);

                    Ok((t_inferred, 0))
                    //Err(Error(format!("when check universe, get pren {}", pren.dom.0)))
                }
            }
            _ => Err(Error(t_span.map(|_| format!("expected universe, got {:?}", inferred_type)), vec![])),
        }
    }
    fn check_app_obj_direct<const CANONICAL: bool>(
        &mut self, cxt: &Cxt,
        lhs: &Raw, op: &Span<SmolStr>, rhs: &Raw, target: &Rc<Val>,
    ) -> Option<Result<Rc<Tm>, Error>> {
        let target_head = super::typeclass::head_key(target)?;
        for ns_entry in cxt.namespace.iter() {
            if !ns_entry.1.contains(&op.data) { continue; }
            let key = SmolStr::new(format!("{}{}", ns_entry.2.to_string(), op.data));
            let (_, _, _, _, vty, _) = cxt.decl.get(&key)?;
            let vty = self.force(&cxt.decl, vty);
            let self_ty = match vty.as_ref() {
                Val::Pi(_, Icit::Impl, dom, _) => dom.clone(),
                _ => continue,
            };
            let mut mty = vty.clone();
            while let Val::Pi(_, Icit::Impl, _, cod) = mty.as_ref() {
                mty = self.closure_apply(&cxt.decl, cod, Val::Rigid(Lvl(u32::MAX), List::new()).into());
            }
            let (param_ty, ret_ty) = match mty.as_ref() {
                Val::Pi(_, _, p, cod) => {
                    (p.clone(), self.closure_apply(&cxt.decl, cod, Val::Rigid(Lvl(u32::MAX), List::new()).into()))
                }
                _ => continue,
            };
            if super::typeclass::head_key(&ret_ty) != Some(target_head.clone()) {
                continue;
            }
            let lhs_tm = match self.check::<CANONICAL>(cxt, lhs.clone(), &self_ty) {
                Ok(tm) => tm,
                Err(e) => return Some(Err(e)),
            };
            let rhs_tm = match self.check::<CANONICAL>(cxt, rhs.clone(), &param_ty) {
                Ok(tm) => tm,
                Err(e) => return Some(Err(e)),
            };
            return Some(Ok(Tm::App(
                Tm::Obj(lhs_tm, op.clone()).into(),
                rhs_tm,
                super::parser::syntax::Icit::Expl,
            ).into()));
        }
        None
    }
    pub fn check<const CANONICAL: bool>(&mut self, cxt: &Cxt, t: Raw, a: &Rc<Val>) -> Result<Rc<Tm>, Error> {
        //println!("{} {:?} {} {:?}", "check".blue(), t, "==".blue(), a);
        let a = self.force(&cxt.decl, a);
        // Fast path: for App(Obj(lhs, op), rhs) with known target type,
        // resolve method directly via decl table, bypassing trait_wrap
        if CANONICAL {
            match &t {
                Raw::App(raw_obj, raw_rhs, _) => match raw_obj.as_ref() {
                    Raw::Obj(raw_lhs, Some(raw_op)) => {
                        if let Some(result) = self.check_app_obj_direct::<CANONICAL>(
                            cxt, raw_lhs.as_ref(), raw_op, raw_rhs.as_ref(), &a
                        ) {
                            return result;
                        }
                    }
                    _ => {}
                },
                _ => {}
            }
        }
        match (t, a.as_ref()) {
            // Check lambda expressions
            (Raw::Lam(x, i, t), Val::Pi(x_t, i_t, a, b_closure))
                if (i.clone(), *i_t) == (Either::Name(x_t.clone()), Icit::Impl)
                    || i == Either::Icit(*i_t) =>
            {
                let body = self.check::<CANONICAL>(
                    &cxt.bind(x.clone(), self.quote(&cxt.decl, cxt.lvl, a), a.clone()),
                    *t,
                    &self.closure_apply(&cxt.decl, b_closure, Val::vvar(cxt.lvl).into()),
                )?;
                Ok(Tm::Lam(x.clone(), *i_t, body).into())
            }
            (t, Val::Pi(x, Icit::Impl, a, b_closure)) => {
                let body = self.check::<CANONICAL>(
                    &cxt.new_binder(x.clone(), self.quote(&cxt.decl, cxt.lvl, a)),
                    t,
                    &self.closure_apply(&cxt.decl, b_closure, Val::vvar(cxt.lvl).into()),
                )?;
                Ok(Tm::Lam(x.clone(), Icit::Impl, body).into())
            }
            // Check let bindings
            (Raw::Let(x, ret_typ, t, u), _) => {
                let (a_checked, _) = self.check_universe(cxt, *ret_typ)?;
                let va = self.eval(&cxt.decl, &cxt.env, &a_checked);
                let t_checked = self.check::<CANONICAL>(cxt, *t, &va)?;
                let vt = self.eval(&cxt.decl, &cxt.env, &t_checked);
                self.hover_table.push((x.to_span(), x.to_span(), crate::L13_namespace::cxt::HoverCxt { lvl: cxt.lvl, locals: cxt.locals.clone(), decl: cxt.decl.clone() }, va.clone()));
                let u_checked = self.check::<CANONICAL>(
                    &cxt.define(x.clone(), t_checked.clone(), vt, a_checked.clone(), va.clone()),
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
            (Raw::Hole(_), _) => Ok(self.fresh_meta(cxt, a)),

            (Raw::Match(expr, clause), _) => {
                let expr_span = expr.to_span();
                let (tm, typ) = self.infer_expr(cxt, *expr)?;
                let mut compiler = Compiler::new(a);
                match compiler.compile(self, typ, &clause, cxt, self.eval(&cxt.decl, &cxt.env, &tm)) {
                    Ok(warnings) => {
                        if !warnings.is_empty() {
                            let msg = warnings.iter().map(|w| w.to_string()).collect::<Vec<_>>().join("; ");
                            Err(Error(expr_span.map(|_| msg.clone()), vec![]))
                        } else {
                            Ok(
                                Tm::Match(tm, compiler.pats).into()
                            ) //if there is any posible that has no return type?
                        }
                    }
                    Err(errors) => {
                        // 把第一个错误通过 Err 正常传播，其余存入 accumulated_errors 变成独立诊断
                        let mut errors_iter = errors.into_iter();
                        let first = errors_iter.next().unwrap();
                        self.accumulated_errors.extend(errors_iter);
                        Err(first)
                    }
                }
            }

            // General case: infer type and unify
            (t, _) => {
                let t_span = t.to_span();
                let x = self.infer_expr(cxt, t);
                let (t_inferred, inferred_type) = self.insert(cxt, x)?;
                if CANONICAL {
                    self.unify(cxt.lvl, cxt, &a, &inferred_type, 100).map_err(|e| {
                        let err = match e {
                            super::UnifyError::Basic | super::UnifyError::Stuck => format!(
                                //"can't unify {:?} == {:?}",
                                "can't unify\n  expected: {}\n      find: {}",
                                super::pretty_tm(0, cxt.names(), &self.quote(&cxt.decl, cxt.lvl, &a)),
                                super::pretty_tm(0, cxt.names(), &self.quote(&cxt.decl, cxt.lvl, &inferred_type)),
                            ),
                            super::UnifyError::Trait(e) => e,
                        };
                        Error(t_span.map(|_| err.clone()), vec![])
                        //Error(format!("can't unify {:?} == {:?}", t, t_prime))
                    })?;
                } else {
                    self.unify_catch(cxt, &a, &inferred_type, t_span)?;
                }
                Ok(t_inferred)
            }
        }
    }
    pub fn infer(&mut self, cxt: &Cxt, t: Decl) -> Result<(DeclTm, Rc<Val>, Cxt), Error> {
        // Apply package prefix if active (unless the declaration itself sets the prefix)
        let t = match &t {
            Decl::Package { .. } | Decl::Import { .. } => t,
            _ => if let Some(ref prefix) = cxt.namespace_prefix {
                prefix_decl_name(t, prefix)
            } else { t },
        };
        match t {
            Decl::Def {
                name,
                params,
                ret_type,
                body,
            } => {
                let ret_cxt = cxt;
                let this_meta = self.meta.len();
                let typ = params.iter().rev().fold(ret_type.clone(), |a, b| {
                    Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                });
                let bod = params.iter().rev().fold(body.clone(), |a, b| {
                    Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a))
                });
                let (ret_cxt, vty, vt, vtyp_pretty, vt_pretty) = {
                    let (typ_tm, _) = self.check_universe(ret_cxt, typ)?;
                    /*let typ_nf_tm = self.nf(&ret_cxt.decl, &ret_cxt.env, &typ_tm);
                    if !typ_nf_tm.no_metas() {
                        return Err(Error(typ.to_span().map(|_| format!("find unsolved meta in {}", pretty_tm(0, ret_cxt.names(), &typ_nf_tm)))));
                    }*/
                    let vtyp = self.eval(&ret_cxt.decl, &ret_cxt.env, &typ_tm);
                    //println!("------------------->");
                    //println!("{:?}", vtyp);
                    //println!("-------------------<");
                    let fake_cxt = ret_cxt.fake_bind(name.clone(), typ_tm.clone(), vtyp.clone())?;
                    let t_tm = self.check::<false>(&fake_cxt, bod.clone(), &vtyp)?;
                    let t_tm = Rc::new(super::wrap_match_in_call(name.data.clone(), &t_tm, 0));
                    self.solve_multi_trait(&fake_cxt, super::MetaVar(this_meta as u32), true)
                        .map_err(|e| Error(name.to_span().map(|_| format!("{:?}", e)), vec![]))?;
                    //let t_tm_nf = self.nf(&ret_cxt.decl, &fake_cxt.env, &t_tm);
                    if let Some((meta_cxt, oty)) = t_tm.no_metas(self, &cxt.decl, cxt.lvl) {
                        // --- Try Nat defaulting (Lean-style fallback) ---
                        // When there are unsolved type metas, try defaulting them to Nat
                        // and re-attempt trait resolution, before giving up.
                        let saved_meta: Vec<_> = self.meta.clone();
                        let nat_tm: Rc<Tm> = Tm::Decl(empty_span(SmolStr::new("Nat"))).into();
                        let nat_val: Rc<Val> = self.eval(&cxt.decl, &cxt.env, &nat_tm);
                        let nat_ok = matches!(
                            self.force(&cxt.decl, &nat_val).as_ref(),
                            Val::Sum(..) | Val::Decl(..)
                        );
                        let nat_solved = if nat_ok {
                            // Phase 1: collect indices of type-valued unsolved metas (immutable borrow)
                            let to_default: Vec<usize> = self.meta.iter().enumerate()
                                .filter(|(_, entry)| matches!(entry, MetaEntry::Unsolved(ty, _, _)
                                    if matches!(self.force(&cxt.decl, ty).as_ref(), Val::U(_))))
                                .map(|(i, _)| i)
                                .collect();
                            if to_default.is_empty() {
                                false
                            } else {
                                // Phase 2: mutate those metas (mutable borrow)
                                for &idx in &to_default {
                                    if let MetaEntry::Unsolved(ty, _, _) = &self.meta[idx] {
                                        self.meta[idx] = MetaEntry::Solved(nat_val.clone(), ty.clone());
                                    }
                                }
                                let _ = self.solve_multi_trait(&fake_cxt, MetaVar(this_meta as u32), false);
                                if t_tm.no_metas(self, &cxt.decl, cxt.lvl).is_none() {
                                    true
                                } else {
                                    // Restore original meta state for proper error reporting
                                    self.meta = saved_meta;
                                    false
                                }
                            }
                        } else {
                            false
                        };

                        if !nat_solved {
                            let err_msg = format!(
                                "find unsolved meta with type `{}`",//\n{:?}",
                                super::pretty_tm(0, meta_cxt.names(), &self.quote(&meta_cxt.decl, meta_cxt.lvl, &oty)),
                                //super::pretty::pretty_tm(0, cxt.names(), &t_tm),
                            );
                            let infer = self.clone();
                            /*println!("{:?}", meta_cxt.pruning);
                            println!(
                                "{}",
                                super::pretty_tm(0, cxt.names(), &self.quote(&cxt.decl, cxt.lvl, &meta_ty)),
                            );*/
                            //let prune_ty = self.prune_ty(&meta_cxt.decl, &meta_cxt.pruning, &meta_ty).unwrap();//TODO:do not unwrap
                            //let meta_ty = self.eval(&meta_cxt.decl, &List::new(), &prune_ty);
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
                        }
                    }
                    let vtyp_pretty = super::pretty_tm(0, ret_cxt.names(), &self.nf(&ret_cxt.decl, &ret_cxt.env, &typ_tm));
                    let vt_pretty = String::new();//super::pretty_tm(0, fake_cxt.names(), &t_tm_nf);
                    //println!("begin vt {}", "------".green());
                    let vt = self.eval(&fake_cxt.decl, &fake_cxt.env, &t_tm);
                    self.hover_table.push((name.to_span(), name.to_span(), crate::L13_namespace::cxt::HoverCxt { lvl: cxt.lvl, locals: cxt.locals.clone(), decl: cxt.decl.clone() }, vtyp.clone()));
                    (
                        ret_cxt.decl(name.clone(), t_tm, vt.clone(), typ_tm, vtyp.clone(), None)?,
                        vtyp,
                        vt,
                        vtyp_pretty,
                        vt_pretty,
                    )
                };
                Ok((
                    DeclTm::Def {
                        name,
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
                {
                    let span = t.to_span();
                    let tm = self.infer_expr(cxt, t)?.0;
                    let t_pretty = super::pretty_tm(0, cxt.names(), &self.nf(&cxt.decl, &cxt.env, &tm));
                    DeclTm::Println(tm, t_pretty, span)
                },
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
                    let (typ_tm, _) = self.check_universe(cxt, typ)?;
                    let vtyp = self.eval(&cxt.decl, &cxt.env, &typ_tm);
                    let fake_cxt = cxt.fake_bind(name.clone(), typ_tm.clone(), vtyp.clone())?;
                    let t_tm = self.check::<false>(&fake_cxt, bod, &vtyp)?;
                    let vt = self.eval(&cxt.decl, &fake_cxt.env, &t_tm);
                    cxt.decl(name.clone(), t_tm, vt, typ_tm, vtyp, None)?
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
                        let vtyp = self.eval(&cxt.decl, &cxt.env, &typ_tm);
                        let t_tm = self.check::<false>(&cxt, bod, &vtyp)?;
                        let vt = self.eval(&cxt.decl, &cxt.env, &t_tm);
                        // Store as EnumName.caseName only — no bare caseName alias
                        let case_key = c.0.clone().map(|n| SmolStr::new(format!("{}.{}", name.data, n)));
                        cxt.decl(case_key, t_tm, vt, typ_tm, vtyp, None)?
                    };
                }
                Ok((DeclTm::Enum {}, Val::U(0).into(), cxt))
            }
            Decl::ImplDecl { name, params, trait_name, trait_params, methods, need_create } => {
                let span = name.to_span();
                let mut cxt = cxt.clone();
                if need_create {
                    let name_raw = params.iter()
                        .rev()
                        .fold(name.clone(), |a, b| Raw::Pi(
                            b.0.clone(),
                            b.2,
                            Box::new(b.1.clone()),
                            Box::new(a)
                        ));
                    let (name_t, _) = self.infer_expr(&cxt, name_raw.clone())?;
                    let name_v = self.eval(&cxt.decl, &cxt.env, &name_t);
                    //cxt = new_cxt;
                    cxt.namespace = cxt.namespace.prepend((name_v, methods.iter().flat_map(|(x, _)| match x {
                        Decl::Def { name, .. } => Some(name.data.clone()),
                        _ => None
                    }).collect(), name_raw.clone()));
                    for (decl, is_static) in methods.iter() {
                        match decl {
                            Decl::Def { name: name_d, params: p, ret_type, body } => {
                                if !is_static {
                                    let prefix_name = name_raw.to_string();
                                    let t = self.infer(&cxt, Decl::Def {
                                        name: name_d.clone().map(|x| SmolStr::new(format!("{}{x}", prefix_name))),
                                        params: params.iter()
                                            .cloned()
                                            .chain(std::iter::once((
                                                name_d.to_span().map(|_| SmolStr::new("this")),
                                                name.clone(),
                                                Icit::Expl,
                                            )))
                                            .chain(p.iter().cloned())
                                            .collect(),
                                        ret_type: ret_type.clone(),
                                        body: body.clone(),
                                    })?;
                                    cxt = t.2;
                                } else {
                                    let type_name = raw_ctor_name(&name).unwrap_or_else(|| {
                                        SmolStr::new(format!("{}", name_raw.to_string().chars().filter(|c| c.is_alphanumeric() || *c == '.').collect::<String>()))
                                    });
                                    let static_name = format!("{}.{}", type_name, name_d.data);
                                    let t = self.infer(&cxt, Decl::Def {
                                        name: name_d.clone().map(|_| SmolStr::new(static_name.clone())),
                                        params: params.iter()
                                            .cloned()
                                            .chain(p.iter().cloned())
                                            .collect(),
                                        ret_type: ret_type.clone(),
                                        body: body.clone(),
                                    })?;
                                    cxt = t.2;
                                }
                            },
                            _ => {
                                todo!()
                            },
                        }
                    }
                } else {
                    let mut temp_cxt = cxt.clone();
                    for (x, a, _) in params.clone() {
                        let (a_checked, _) = self.check_universe(&temp_cxt, a)?;
                        let a_eval = self.eval(&temp_cxt.decl, &temp_cxt.env, &a_checked);
                        temp_cxt = temp_cxt.bind(x.clone(), self.quote(&temp_cxt.decl, temp_cxt.lvl, &a_eval), a_eval);
                    }
                    let (typ_tm, _) = self.check_universe(&temp_cxt, name.clone())?;
                    let typ_val = self.eval(&temp_cxt.decl, &temp_cxt.env, &typ_tm);
                    let mut trait_param: Vec<Rc<Val>> = vec![self.force(&cxt.decl, &typ_val)];
                    for a in trait_params.clone() {
                        let (a_checked, _) = self.infer_expr(&temp_cxt, a)?;
                        let a_eval = self.eval(&temp_cxt.decl, &temp_cxt.env, &a_checked);
                        trait_param.push(self.force(&cxt.decl, &a_eval));
                    }
                    let out_param = self.trait_out_param.get(&trait_name.data)
                        .ok_or(Error(trait_name.clone().map(|n| format!("trait `{}` not declared", n)), vec![]))?;
                    // Keep ALL params (including outParam) so the solver can distinguish instances
                    // that differ only in output params (e.g., Into[String] vs Into[Bool] for the same type)
                    let typ_name = SmolStr::new(format!("{:?}{:?}", trait_name.data, trait_param));
                    let inst = Instance {
                        assertion: Assertion { name: trait_name.data.clone(), arguments: trait_param },
                        dependencies: List::new(),
                        lvl: trait_name.to_span().map(|_| typ_name.clone()),
                    };
                    self.trait_solver.impl_trait_for(trait_name.data.clone(), inst);
                    // Fill in missing methods with default bodies from the trait definition
                    let mut methods = methods;
                    if let Some((_, _, _, trait_methods)) = self.trait_definition.get(&trait_name.data).cloned() {
                        for (tm_name, tm_params, tm_ret, tm_default_body) in trait_methods {
                            let has_impl = methods.iter().any(|(decl, _)| match decl {
                                Decl::Def { name, .. } => name.data == tm_name.data,
                                _ => false,
                            });
                            if !has_impl {
                                if let Some(default_body) = tm_default_body {
                                    methods.push((
                                        Decl::Def {
                                            name: tm_name,
                                            params: tm_params,
                                            ret_type: tm_ret,
                                            body: default_body,
                                        },
                                        false,
                                    ));
                                } else {
                                    return Err(Error(
                                        tm_name.map(|n| format!("method `{}` has no default implementation", n)),
                                        vec![],
                                    ));
                                }
                            }
                        }
                    }
                    // Fill in missing associated type params with defaults
                    let mut trait_params = trait_params;
                    if let Some((trait_params_def, _, _, _)) = self.trait_definition.get(&trait_name.data) {
                        // Collect associated type indices (params declared as `type ...`)
                        let assoc_names: Vec<(usize, SmolStr)> = trait_params_def.iter()
                            .enumerate()
                            .filter_map(|(i, (name, _, _))| {
                                if self.assoc_defaults.contains_key(&(trait_name.data.clone(), name.data.clone())) {
                                    Some((i, name.data.clone()))
                                } else {
                                    None
                                }
                            })
                            .collect();
                        if !assoc_names.is_empty() {
                            // trait_params_def includes Self at index 0, then explicit params, then assoc types
                            let expected_total = trait_params_def.len() - 1;  // exclude Self
                            let expected_explicit = expected_total - assoc_names.len();
                            let provided_total = trait_params.len();
                            let provided_assoc = provided_total.saturating_sub(expected_explicit);
                            let missing_count = assoc_names.len().saturating_sub(provided_assoc);
                            if missing_count > 0 {
                                // Missing assoc types are the trailing ones (provided in order)
                                for (_, aname) in assoc_names.iter().skip(provided_assoc) {
                                    if let Some(default_type) = self.assoc_defaults.get(&(trait_name.data.clone(), aname.clone())) {
                                        trait_params.push(default_type.clone().unwrap_or(Raw::Hole(empty_span(()))));
                                    } else {
                                        return Err(Error(
                                            empty_span(format!("associated type `{}` has no default value", aname)),
                                            vec![],
                                        ));
                                    }
                                }
                            }
                        }
                    }
                    let mut ret = std::iter::once(name.clone())
                        .chain(trait_params.clone())
                        .fold(Raw::Var(trait_name.clone().map(|x| SmolStr::new(format!("{x}.mk")))), |ret, x| {
                            Raw::App(Box::new(ret), Box::new(x), Either::Icit(Icit::Impl))
                        });
                    for (decl, _) in methods {
                        if let Decl::Def { name: def_name, params, ret_type: _, body } = decl {
                            ret = Raw::App(
                                Box::new(ret),
                                Box::new(Raw::Lam(
                                    def_name.map(|_| SmolStr::new("this")),
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
                        name: trait_name.to_span().map(|_| typ_name.clone()),
                        params,
                        ret_type: trait_params.into_iter()
                            .fold(Raw::App(
                                Raw::Var(trait_name).into(),
                                name.into(),
                                Either::Icit(Icit::Impl)
                            ), |a, b| Raw::App(Box::new(a), Box::new(b), Either::Icit(Icit::Impl))),
                        body: ret,
                    })?;
                    cxt = c;
                }
                Ok((DeclTm::TraitImpl {}, Val::U(0).into(), cxt.clone()))
            },
            Decl::TraitDecl { name, mut params, supertraits, methods, assoc_defaults } => {
                // Transitive supertrait method resolution with cycle detection
                let mut all_methods = methods.clone();
                let mut visited = std::collections::HashSet::<SmolStr>::new();
                visited.insert(name.data.clone());
                let mut stack: Vec<SmolStr> = supertraits.iter().map(|s| s.data.clone()).collect();
                while let Some(st_name) = stack.pop() {
                    if visited.contains(&st_name) {
                        return Err(Error(empty_span(format!("cyclic supertrait: `{}` appears twice in the chain", st_name)), vec![]));
                    }
                    visited.insert(st_name.clone());
                    if let Some((_, _, st_sts, st_methods)) = self.trait_definition.get(&st_name) {
                        // Add supertrait's supertraits to the stack (detect cycles)
                        for st_st in st_sts {
                            if visited.contains(&st_st.data) {
                                return Err(Error(empty_span(format!("cyclic supertrait: `{}` appears twice in the chain", st_st.data)), vec![]));
                            }
                            stack.push(st_st.data.clone());
                        }
                        // Add supertrait's methods (avoiding duplicates)
                        for st_m in st_methods {
                            let name_exists = all_methods.iter().any(|(mn, _, _, _)| mn.data == st_m.0.data);
                            if !name_exists {
                                all_methods.push(st_m.clone());
                            }
                        }
                    }
                }
                self.trait_solver.new_trait(name.data.clone());
                let mut param = vec![(name.clone().map(|_| SmolStr::new("Self")), Raw::Hole(name.to_span()), Icit::Impl)];
                param.append(&mut params);
                let out_param = param.iter().map(|x| match &x.1 {
                        Raw::App(t, ..) if matches!(t.as_ref(), Raw::Var(d) if d.data == "outParam") => true,
                        _ => false,
                    }).collect::<Vec<_>>();
                self.trait_solver.set_trait_out_params(name.data.clone(), out_param.clone());
                self.trait_definition.insert(name.data.clone(), (param.clone(), out_param.clone(), supertraits.clone(), all_methods.clone()));
                self.trait_out_param.insert(name.data.clone(), out_param);
                // Store associated type defaults
                for (aname, adefault) in &assoc_defaults {
                    self.assoc_defaults.insert((name.data.clone(), aname.clone()), adefault.clone());
                }
                let mut cxt = cxt.clone();
                let (_, _, c) = self.infer(&cxt, Decl::Enum {
                    is_trait: true,
                    name: name.clone(),
                    params: param,
                    cases: vec![(
                        name.map(|x| SmolStr::new(format!("{x}.mk"))),
                        all_methods
                            .into_iter()
                            .map(|(mn, mparams, mret, _mbody)| (
                                mn.clone(),
                                std::iter::once((mn.clone().map(|_| SmolStr::new("this")), Raw::Var(mn.map(|_| SmolStr::new("Self"))), Icit::Expl))
                                    .chain(mparams.into_iter())
                                    .rev()
                                    .fold(mret, |a, b| {
                                        Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                                    }),
                                Icit::Expl,
                            ))
                            .collect(),
                        None,
                    )],
                })?;
                cxt = c;
                Ok((DeclTm::Trait {}, Val::U(0).into(), cxt.clone()))
            },
            Decl::Package { path } => {
                let pkg_path = path.iter().map(|s| s.data.as_str()).collect::<Vec<_>>().join(".");
                let mut cxt = cxt.clone();
                cxt.namespace_prefix = Some(SmolStr::new(&pkg_path));
                Ok((DeclTm::Package, Val::U(0).into(), cxt))
            },
            Decl::Import { prefix, names, wildcard } => {
                let prefix_str = prefix.join(".");
                let mut cxt = cxt.clone();
                if wildcard {
                    let prefix_search = format!("{}.", prefix_str);
                    let to_insert: Vec<(SmolStr, _)> = cxt.decl.iter()
                        .filter(|(k, _)| k.starts_with(&prefix_search))
                        .map(|(k, v)| (SmolStr::new(k.strip_prefix(&prefix_search).unwrap()), v.clone()))
                        .collect();
                    let decl_map = Rc::make_mut(&mut cxt.decl);
                    for (stripped, v) in to_insert {
                        decl_map.insert(stripped, v);
                    }
                    // Also bring the prefix itself if it's a decl
                    if let Some(v) = decl_map.get(&SmolStr::new(&prefix_str)).cloned() {
                        let last = prefix.last().unwrap().clone();
                        decl_map.insert(last, v);
                    }
                } else {
                    let decl_map = Rc::make_mut(&mut cxt.decl);
                    for n in names {
                        let full_name = if prefix.is_empty() {
                            n.clone()
                        } else {
                            SmolStr::new(format!("{}.{}", prefix_str, n))
                        };
                        if let Some(v) = decl_map.get(&full_name).cloned() {
                            decl_map.insert(n, v);
                        }
                    }
                }
                Ok((DeclTm::Import, Val::U(0).into(), cxt))
            },
            Decl::Derive { .. } => {
                panic!("Derive should have been expanded before elaboration")
            },
        }
    }
    pub fn infer_expr(&mut self, cxt: &Cxt, t: Raw) -> Result<(Rc<Tm>, Rc<Val>), Error> {
        /*println!(
            "{} {}",
            "infer".red(),
            t,
        );*/
        #[cfg(feature = "sampler")]
        crate::sampler::tick();
        let t_span = t.to_span();
        match t {
            // Infer variable types
            Raw::Var(name) => match cxt.src_names.get(&name.data) {
                Some((x, a)) => {
                    self.hover_table.push((t_span, a.0, crate::L13_namespace::cxt::HoverCxt { lvl: cxt.lvl, locals: cxt.locals.clone(), decl: cxt.decl.clone() }, a.1.clone()));
                    Ok((Tm::Var(lvl2ix(cxt.lvl, *x)).into(), a.1.clone()))
                },
                None => match cxt.decl.get(&name.data) {
                    Some((def, _, _, _, vty, _)) => {
                        self.hover_table.push((t_span, *def, crate::L13_namespace::cxt::HoverCxt { lvl: cxt.lvl, locals: cxt.locals.clone(), decl: cxt.decl.clone() }, vty.clone()));
                        Ok((Tm::Decl(name).into(), vty.clone()))
                    },
                    None => {
                        // Try namespace prefix resolution
                        if let Some(ref prefix) = cxt.namespace_prefix {
                            let qualified = SmolStr::new(format!("{}.{}", prefix, name.data));
                            if let Some((def, _, _, _, vty, _)) = cxt.decl.get(&qualified) {
                                self.hover_table.push((t_span, *def, crate::L13_namespace::cxt::HoverCxt { lvl: cxt.lvl, locals: cxt.locals.clone(), decl: cxt.decl.clone() }, vty.clone()));
                                return Ok((Tm::Decl(empty_span(qualified)).into(), vty.clone()));
                            }
                        }
                        // Try qualified fallback: find a decl entry `TypeName.name`
                        let fallback = format!(".{}", name.data);
                        let match_entry: Option<(SmolStr, _)> = cxt.decl.iter()
                            .find(|(k, _)| k.ends_with(&fallback) && k.len() > fallback.len())
                            .map(|(k, v)| (k.clone(), v.clone()));
                        if let Some((full_key, (def_span, _, _, _, vty, _))) = match_entry {
                            self.hover_table.push((t_span, def_span, crate::L13_namespace::cxt::HoverCxt { lvl: cxt.lvl, locals: cxt.locals.clone(), decl: cxt.decl.clone() }, vty.clone()));
                            return Ok((Tm::Decl(empty_span(full_key)).into(), vty.clone()));
                        }
                        Err(Error(name.map(|x| format!("error name not in scope: {}", x)), vec![]))
                    }
                },
            },

            Raw::Obj(x, t) => {
                let t = t.unwrap_or(empty_span(SmolStr::new("")));
                if t.data == "mk" {
                    if let Raw::Var(sum_name) = x.as_ref() {
                        return self.infer_expr(cxt, Raw::Var(sum_name.clone().map(|n| SmolStr::new(format!("{n}.mk")))))
                    }
                }
                // Check namespace-qualified access: build full path and look up in decl table
                if !t.data.is_empty() {
                    let full_path = qualified_path_str(x.as_ref(), &t.data);
                    if let Some(qual) = full_path {
                        // Try the path as-is first
                        if let Some((def_span, _, _, _, vty, _)) = cxt.decl.get(&qual) {
                            self.hover_table.push((t_span, *def_span, crate::L13_namespace::cxt::HoverCxt { lvl: cxt.lvl, locals: cxt.locals.clone(), decl: cxt.decl.clone() }, vty.clone()));
                            return Ok((Tm::Decl(empty_span(qual)).into(), vty.clone()));
                        }
                        // If not found, try with namespace prefix (for access inside a package)
                        if let Some(ref prefix) = cxt.namespace_prefix {
                            let prefixed = SmolStr::new(format!("{prefix}.{qual}"));
                            if let Some((def_span, _, _, _, vty, _)) = cxt.decl.get(&prefixed) {
                                self.hover_table.push((t_span, *def_span, crate::L13_namespace::cxt::HoverCxt { lvl: cxt.lvl, locals: cxt.locals.clone(), decl: cxt.decl.clone() }, vty.clone()));
                                return Ok((Tm::Decl(empty_span(prefixed)).into(), vty.clone()));
                            }
                        }
                    }
                }
                let (tm, a) = self.infer_expr(cxt, *x.clone())?;
                let a = self.force(&cxt.decl, &a);
                match (tm, a.as_ref()) {
                    (tm, Val::Sum(_, params, cases, _)) => {
                        let mut c = None;
                        if cases.len() == 1 {
                            if let Some(case) = cases.first() {
                                if case.data.contains(".mk") {
                                    let (_, case_typ) = self.infer_expr(cxt, Raw::Var(case.clone()))?;
                                    let mut ret = vec![];
                                    let mut typ = case_typ;
                                    let mut param: Vec<_> = params.iter().cloned().collect();
                                    param.reverse();
                                    while let Val::Pi(name, icit, ty, closure) = typ.as_ref().clone() {
                                        if icit == Icit::Expl {
                                            ret.push((name.clone(), ty.clone()));
                                            typ = self.closure_apply(
                                                &cxt.decl,
                                                &closure,
                                                Val::Obj(self.eval(&cxt.decl, &cxt.env, &tm), name, List::new()).into()
                                            )
                                        } else {
                                            let val = param.pop()
                                                .map(|x| x.1)
                                                .unwrap_or(Val::Obj(self.eval(&cxt.decl, &cxt.env, &tm), name.clone(), List::new()).into());
                                            ret.push((name, ty.clone()));
                                            typ = self.closure_apply(&cxt.decl, &closure, val)
                                        }
                                    }
                                    c = Some(ret);
                                }
                            }
                        }
                        if t.data.is_empty() {
                            c.iter()
                                .flatten()
                                .map(|x| (t_span, x.0.data.clone()))
                                .chain(
                                    params
                                        .iter()
                                        .map(|x| (t_span, x.0.data.clone()))
                                )
                                .for_each(|x| self.completion_table.push(x));
                        }
                        let field_info = c.and_then(|params| {
                                params.into_iter()
                                    .find(|(fields_name, _)| fields_name == &t)
                                    .map(|(name, ty)| (name.to_span(), ty))
                            }).or_else(|| {
                            params
                                .iter()
                                .find(|(fields_name, _, _, _)| fields_name == &t)
                                .map(|(name, _, ty, _)| (name.to_span(), ty.clone()))
                            });
                        if let Some((def_span, val)) = field_info {
                            self.hover_table.push((t.to_span(), def_span, crate::L13_namespace::cxt::HoverCxt { lvl: cxt.lvl, locals: cxt.locals.clone(), decl: cxt.decl.clone() }, val.clone()));
                            Ok((
                                Tm::Obj(tm, t).into(),
                                val,
                            ))
                        } else {
                            self.trait_wrap(cxt, t, a, x, tm, t_span)
                            }
                    }
                    (tm, Val::SumCase { datas: params, .. }) => {
                        if let Some((def_span, val)) = params
                            .iter()
                            .find(|(fields_name, _, _)| fields_name == &t)
                            .map(|(name, ty, _)| (name.to_span(), ty)) {
                                self.hover_table.push((t.to_span(), def_span, crate::L13_namespace::cxt::HoverCxt { lvl: cxt.lvl, locals: cxt.locals.clone(), decl: cxt.decl.clone() }, val.clone()));
                                Ok((
                                    Tm::Obj(tm, t).into(),
                                    val.clone(),
                                ))
                            } else {
                                self.trait_wrap(cxt, t, a, x, tm, t_span)
                            }
                    }
                    (tm, _) => self.trait_wrap(cxt, t, a, x, tm, t_span),
                }
            },

            // Infer lambda expressions
            Raw::Lam(x, Either::Icit(i), t) => {
                let new_meta = self.fresh_meta(cxt, Val::U(0).into());
                let a = self.eval(&cxt.decl, &cxt.env, &new_meta);
                //TODO:below may be wrong
                let new_cxt = cxt.bind(x.clone(), self.quote(&cxt.decl, cxt.lvl, &a), a.clone());
                let infered = self.infer_expr(&new_cxt, *t);
                let (t_inferred, b) = self.insert(&new_cxt, infered)?;
                let b_closure = self.close_val(cxt, &b);
                Ok((
                    Tm::Lam(x.clone(), i, t_inferred).into(),
                    Val::Pi(x, i, a, b_closure).into(),
                ))
            }

            Raw::Lam(x, Either::Name(_), _) => Err(Error(x.map(|_| "infer named lambda".to_owned()), vec![])),

            // Infer function applications
            Raw::App(t, u, i) => {
                let t_span = t.to_span();
                let t_raw = t.as_ref().clone();
                let u_raw = u.as_ref().clone();
                let is_expl = matches!(i, Either::Icit(Icit::Expl));
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
                let tty = self.force(&cxt.decl, &tty);
                let (a, b_closure) = match tty.as_ref() {
                    Val::Pi(_, i_t, a, b_closure) => {
                        if i == *i_t {
                            (a.clone(), b_closure.clone())
                        } else {
                            return Err(Error(t_span.map(|_| format!("icit mismatch {:?} {:?}", i, i_t)), vec![]));
                        }
                    }
                    _ => {
                        // Scala-style apply: if the expression's type is not a function type,
                        // try desugaring `expr(args)` into `expr.apply(args)`,
                        // preserving the icit (explicit/implicit) of the original call.
                        // `a[7]` (implicit) → `a.apply[7]`  works for type-parameter-based apply.
                        // `a(7)` (explicit) → `a.apply(7)` only works if apply takes explicit args.
                        let meta_before = self.meta.len();
                        let apply_obj = Raw::Obj(Box::new(t_raw), Some(empty_span(SmolStr::new("apply"))));
                        let apply_call = Raw::App(Box::new(apply_obj), Box::new(u_raw), Either::Icit(i));
                        if let Ok(result) = self.infer_expr(cxt, apply_call) {
                            return Ok(result);
                        }
                        self.meta.truncate(meta_before);

                        let new_meta = self.fresh_meta(cxt, Val::U(0).into());
                        let a = self.eval(&cxt.decl, &cxt.env, &new_meta);
                        let b_closure = Closure(
                            cxt.env.clone(),
                            self.fresh_meta(
                                &cxt.bind(
                                    empty_span(SmolStr::new("x")),
                                    self.quote(&cxt.decl, cxt.lvl, &a),
                                    a.clone(),
                                ),
                                Val::U(0).into(),
                            ),
                        );
                        self.unify_catch(
                            cxt,
                            &Val::Pi(
                                empty_span(SmolStr::new("x")),
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
                let u_checked = self.check::<false>(cxt, *u, &a)?;
                let ret_type = self.closure_apply(&cxt.decl, &b_closure, self.eval(&cxt.decl, &cxt.env, &u_checked));
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
                let a_eval = self.eval(&cxt.decl, &cxt.env, &a_checked);
                let (b_checked, lvl) = self.check_universe(
                    &cxt.bind(x.clone(), self.quote(&cxt.decl, cxt.lvl, &a_eval), a_eval),
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
                let va = self.eval(&cxt.decl, &cxt.env, &a_checked);
                let t_checked = self.check::<false>(cxt, *t, &va)?;
                let vt = self.eval(&cxt.decl, &cxt.env, &t_checked);
                self.hover_table.push((x.to_span(), x.to_span(), crate::L13_namespace::cxt::HoverCxt { lvl: cxt.lvl, locals: cxt.locals.clone(), decl: cxt.decl.clone() }, va.clone()));
                let (u_inferred, b) = self.infer_expr(
                    &cxt.define(
                        x.clone(),
                        t_checked.clone(),
                        vt,
                        a_checked.clone(),
                        va.clone(),
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
            Raw::Hole(_) => {
                let new_meta = self.fresh_meta(cxt, Val::U(0).into());
                let a = self.eval(&cxt.decl, &cxt.env, &new_meta);
                let t = self.fresh_meta(cxt, a.clone());
                Ok((t, a))
            }

            Raw::LiteralIntro(literal) => Ok((Tm::LiteralIntro(literal).into(), Val::LiteralType.into())),

            Raw::Nat(n) => {
                let nat_type = cxt.decl.get("Nat").map(|x| x.2.clone())
                    .unwrap_or_else(|| Val::U(0).into());
                let nat_val = super::cxt::build_nat(n, &nat_type);
                let nat_tm = self.quote(&cxt.decl, cxt.lvl, &nat_val);
                Ok((nat_tm, nat_type))
            }

            Raw::Match(_, _) => Err(Error(t_span.map(|_| "try to infer match".to_owned()), vec![])),

            Raw::Sum(name, params, cases, universe, is_trait) => {
                let new_params = Rc::new(params
                    .iter()
                    .map(|ty| {
                        let (ty_checked, typ_val) = self.infer_expr(cxt, ty.2.clone())?;
                        let typ = self.quote(&cxt.decl, cxt.lvl, &typ_val);
                        Ok((ty.0.clone(), ty_checked, typ, ty.1))
                    })
                    .collect::<Result<Vec<_>, _>>()?);
                //TODO: universe need to consider cases?
                Ok((Tm::Sum(name, new_params, Rc::new(cases), is_trait).into(), Val::U(universe).into()))
            }

            Raw::SumCase {
                is_trait,
                typ,
                case_name,
                datas,
            } => {
                let (typ_checked, _) = self.infer_expr(cxt, *typ)?;
                let typ_val = self.eval(&cxt.decl, &cxt.env, &typ_checked);
                let datas = Rc::new(datas
                    .into_iter()
                    .map(|x| {
                        let (tm, _) = self.infer_expr(cxt, x.1)?;
                        Ok((x.0, tm, x.2))
                    })
                    .collect::<Result<Vec<_>, _>>()?);
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
    fn trait_wrap(&mut self, cxt: &Cxt, t: Span<SmolStr>, a: Rc<Val>, x: Box<Raw>, tm: Rc<Tm>, t_span: Span<()>) -> Result<(Rc<Tm>, Rc<Val>), Error> {
        let typ_raw = self.eval(&cxt.decl, &cxt.env, &self.quote(&cxt.decl, cxt.lvl, &a));
        let typ_raw_head = super::typeclass::head_key(&typ_raw);

        if t.data.is_empty() {
            // Collect completions: find traits whose first non-out param could match typ_raw
            let completions: Vec<_> = self.trait_definition.iter()
                .filter(|(x, (_, _, _, _))| self.trait_solver.can_satisfy(x, &typ_raw))
                .flat_map(|x| x.1.3.clone())
                .collect();
            for method_decl in &completions {
                self.completion_table.push((t_span, method_decl.0.data.clone()));
            }
        }
        // --- Namespace method lookup with meta cleanup ---
        // Collect matching namespaces entries (clone to avoid borrow conflicts)
        let ns_entries: Vec<_> = cxt.namespace.iter()
            .filter(|x| x.1.contains(&t.data))
            .cloned()
            .collect();
        let ns_result = {
            let mut result: Vec<_> = vec![];
            for ns_entry in &ns_entries {
                // Pre-filter: skip entries whose trait has no instance for this Self type
                if let Some(ref head) = typ_raw_head {
                    if let Val::Pi(_, Icit::Impl, dom, _) = ns_entry.0.as_ref() {
                        if let Val::Sum(trait_name, _, _, true) = dom.as_ref() {
                            if !self.trait_solver.can_satisfy(&trait_name.data, &typ_raw) {
                                continue;
                            }
                        }
                    }
                }
                let meta_before = self.meta.len();
                let mut check_typ = ns_entry.0.clone();
                while let Val::Pi(_, Icit::Impl, dom, cod) = check_typ.as_ref() {
                    let u = self.fresh_meta(&cxt, dom.clone());
                    let u = self.eval(&cxt.decl, &cxt.env, &u);
                    check_typ = self.closure_apply(&cxt.decl, cod, u);
                }
                if self.unify_catch(cxt, &check_typ, &typ_raw, t_span).is_ok() {
                    result.push(ns_entry.clone());
                }
                // Clean up metas created by this failed namespace entry
                self.meta.truncate(meta_before);
            }
            result
        };
        if ns_result.len() > 1 {
            let names: Vec<SmolStr> = ns_result.iter()
                .filter_map(|e| {
                    if let Val::Pi(_, Icit::Impl, dom, _) = e.0.as_ref() {
                        if let Val::Sum(trait_name, _, _, true) = dom.as_ref() {
                            return Some(trait_name.data.clone());
                        }
                    }
                    None
                })
                .collect();
            return Err(Error(t.clone().map(|m| format!(
                "ambiguous method `{}`: found in traits {}",
                m,
                names.iter().map(|n| format!("`{}`", n)).collect::<Vec<_>>().join(", "),
            )), vec![]));
        }
        if let Some(ns_entry) = ns_result.into_iter().next() {
            return self.infer_expr(cxt, Raw::app(
                Raw::Var(t_span.map(|_| SmolStr::new(format!("{}{}", ns_entry.2, t.data)))),
                *x.clone(),
            ));
        }
        {
            let traits = self.trait_definition
                .iter()
                .flat_map(|(trait_name, (trait_params, out_param, _st, methods))| {
                    methods.iter()
                        .find(|x| x.0.data == t.data)
                        .map(|x| (trait_name, trait_params, out_param, x))
                })
                .filter(|(x, _, _, _)| self.trait_solver.can_satisfy(x, &typ_raw))
                .map(|(trait_name, trait_params, _, (methods_name, methods_params, ret_type, _default_body))| (
                    trait_name.clone(),
                    {
                        let params = {
                            let mut params = trait_params.clone();
                            // $$ (trait instance) must come before $this (Expl) so that
                            // insert_go fills both Self and $$ before reaching $this.
                            // When Self is still Flex, solve_trait in fresh_meta defers
                            // $$ resolution to trait_metas; solve_multi_trait fires after
                            // $this unifies Self with the concrete receiver type.
                            params.push((
                                methods_name.clone().map(|_| SmolStr::new("$$")),
                                trait_params.iter()
                                    .map(|x| x.0.clone())
                                    .fold(
                                        Raw::Var(methods_name.clone().map(|_| trait_name.clone())),
                                        |ret, x| Raw::App(Box::new(ret), Box::new(Raw::Var(x)), Either::Icit(Icit::Impl))
                                    ),
                                Icit::Impl
                            ));
                            params.push((
                                methods_name.clone().map(|_| SmolStr::new("$this")),
                                Raw::Var(methods_name.clone().map(|_| SmolStr::new("Self"))),
                                Icit::Expl
                            ));
                            params.append(&mut methods_params.clone());
                            params
                        };
                        let body = std::iter::once((Raw::Var(methods_name.clone().map(|_| SmolStr::new("$this"))), Icit::Expl))
                            .chain(methods_params.iter().map(|x| (Raw::Var(x.0.clone()), x.2)))
                            .fold(
                                Raw::Obj(
                                    Box::new(Raw::Var(methods_name.clone().map(|_| SmolStr::new("$$")))),
                                    Some(methods_name.clone()),
                                ),
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
                                x.clone(),
                                Either::Icit(Icit::Expl),
                            )),
                        )
                    }
                ))
                .collect::<Vec<_>>();
            if traits.len() > 1 {
                let trait_names: Vec<&SmolStr> = traits.iter().map(|(n, _)| n).collect();
                return Err(Error(t.clone().map(|m| format!(
                    "ambiguous method `{}`: found in traits {}",
                    m,
                    trait_names.iter().map(|n| format!("`{}`", n)).collect::<Vec<_>>().join(", "),
                )), vec![]));
            }
            if let Some((_, decl)) = traits.first() {
                self.infer_expr(cxt, decl.clone())
            } else {
                Err(Error(t.clone().map(|t| format!(
                    "`{}`: {} has no object `{}`",
                    super::pretty_tm(0, cxt.names(), &tm),
                    super::pretty_tm(0, cxt.names(), &self.nf(&cxt.decl, &cxt.env, &self.quote(&cxt.decl, cxt.lvl, &a))),
                    t,
                )), vec![]))
            }
        }
    }
}

/// Build a dotted path string from a chain of Raw::Obj expressions.
/// e.g., Raw::Obj(Raw::Obj(Raw::Var("a"), Some("b")), Some("c")) → Some("a.b.c")
fn qualified_path_str(x: &Raw, field: &str) -> Option<SmolStr> {
    match x {
        Raw::Var(name) => Some(SmolStr::new(format!("{}.{}", name.data, field))),
        Raw::Obj(inner, Some(seg)) => {
            qualified_path_str(inner.as_ref(), &seg.data).map(|p| SmolStr::new(format!("{p}.{field}")))
        }
        _ => None,
    }
}

/// Extract the head constructor name from a Raw type expression.
/// e.g., `Product[A, B]` → `"Product"`, `Maybe[T]` → `"Maybe"`, `String` → `"String"`
fn raw_ctor_name(raw: &Raw) -> Option<SmolStr> {
    match raw {
        Raw::Var(name) => Some(name.data.clone()),
        Raw::App(head, _, _) => raw_ctor_name(head),
        _ => None,
    }
}

