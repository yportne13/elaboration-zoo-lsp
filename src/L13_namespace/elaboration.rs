use std::cmp::max;

use colored::Colorize;
use smol_str::SmolStr;

use crate::{list::List, parser_lib::{Span, ToSpan}};

use super::{
    Closure, Cxt, DeclTm, Error, Infer, Ix, PrimFunc, Tm, VTy, Val,
    Lvl, Rc, MetaVar,
    empty_span, lvl2ix,
    parser::syntax::{ClassItem, Decl, Either, Icit, Raw},
    pattern_match::Compiler, MetaEntry,
    typeclass::Instance,
    unification::PartialRenaming,
    typeclass::Assertion,
};

/// True when both values are the same sum type with identical (by pointer)
/// parameters — used by the constructor-chain fast path to confirm a
/// constructor's domain matches the type a term is checked against.
/// Conservative: any doubt returns false and the caller falls back to the
/// general (recursive) path.
fn same_sum_name(a: &Rc<Val>, b: &Rc<Val>) -> bool {
    match (a.as_ref(), b.as_ref()) {
        (Val::Sum(n1, p1, _, _), Val::Sum(n2, p2, _, _)) => {
            n1.data == n2.data
                && p1.len() == p2.len()
                && p1.iter().zip(p2.iter()).all(|((_, v1, _, _), (_, v2, _, _))| Rc::ptr_eq(v1, v2))
        }
        _ => false,
    }
}

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
            // Method names are kept as written — `trait_wrap` dispatches
            // `x.method` by the written name and the trait-impl method matching
            // compares written names; prefixing them would break both.
            methods: methods.into_iter().map(|(mn, mparams, mret, mbody)| {
                (mn, mparams, mret, mbody)
            }).collect(),
            assoc_defaults,
        },
        Decl::ImplDecl { name, params, trait_name, trait_params, methods, inherent, from_class } => Decl::ImplDecl {
            name,
            params,
            trait_name,
            trait_params,
            // Method names are kept as written: inherent methods are wrapped as
            // `TypeName.method` and dispatched by written name; trait impl
            // methods are matched against the (also written) trait methods.
            methods,
            inherent,
            from_class,
        },
        Decl::Package { path } => Decl::Package {
            path: path.into_iter().map(|s| s.map(|n| SmolStr::new(format!("{prefix}.{n}")))).collect(),
        },
        Decl::Import { .. } => d,
        Decl::Derive { traits, decl } => Decl::Derive {
            traits,
            decl: Box::new(prefix_decl_name(*decl, prefix)),
        },
        Decl::Class { name, params, items, traits } => Decl::Class {
            name: name.map(|n| SmolStr::new(format!("{prefix}.{n}"))),
            params,
            items,
            traits,
        },
    }
}

/// Tuple-arity of a name like `Tuple2` (sans `.mk` suffix); None if the name
/// is not a builtin tuple type name.
fn tuple_n_arity(name: &str) -> Option<usize> {
    let digits = name.strip_prefix("Tuple")?;
    if digits.is_empty() || !digits.chars().all(|c| c.is_ascii_digit()) {
        return None;
    }
    digits.parse().ok()
}

/// True when `head` is the function part of a tuple literal construction
/// `TupleN.mk e0 … en`: either the parser sugar `(e0, …)` — a `Raw::Var`
/// named `TupleN.mk` whose span covers the whole parenthesized element list —
/// or an explicit `TupleN.mk` member access (`Raw::Obj` with a `.mk` field).
/// Used to give each tuple element its own hover-table entry so hovering an
/// element shows the element's type instead of the whole tuple's.
fn is_tuple_mk_head(head: &Raw) -> bool {
    let mut cur = head;
    loop {
        match cur {
            Raw::App(f, _, _) => cur = f.as_ref(),
            _ => break,
        }
    }
    match cur {
        Raw::Var(n) => n.data
            .strip_suffix(".mk")
            .and_then(tuple_n_arity)
            .is_some(),
        Raw::Obj(base, Some(m)) if m.data == "mk" => {
            let mut cur = base.as_ref();
            loop {
                match cur {
                    Raw::App(f, _, _) => cur = f.as_ref(),
                    _ => break,
                }
            }
            matches!(cur, Raw::Var(n) if tuple_n_arity(&n.data).is_some())
        }
        _ => false,
    }
}

impl Infer {
    /// Peel the leading Π-layers of `vtyp`, returning the codomain (return type)
    /// together with the quote level that resolves the fresh rigids introduced
    /// for the peeled parameters (so dependent return types print as `Vec Nat n`).
    fn peel_pi(&self, cxt: &Cxt, vtyp: &Rc<Val>) -> (Rc<Val>, Lvl) {
        let mut t = vtyp.clone();
        let mut lvl = cxt.lvl;
        while let Val::Pi(_, _, _, cod) = self.force(&cxt.decl, &t).as_ref() {
            t = self.closure_apply(&cxt.decl, cod, Val::vvar(lvl).into());
            lvl = lvl + 1;
        }
        (t, lvl)
    }

    /// Record an inlay hint `: <type>` at `offset`, skipping types that still
    /// contain unsolved metas and truncating over-long labels.
    fn push_inlay_hint(&mut self, cxt: &Cxt, offset: u32, val: &Rc<Val>) {
        let lvl = cxt.lvl;
        let tm = self.quote(&cxt.decl, lvl, val);
        if tm.no_metas(self, &cxt.decl, lvl).is_some() {
            return; // skip hints whose type is not yet known
        }
        let mut label = format!(": {}", super::pretty_tm(0, cxt.names(), &tm));
        const MAX_LEN: usize = 80;
        if label.chars().count() > MAX_LEN {
            let truncated: String = label.chars().take(MAX_LEN.saturating_sub(1)).collect();
            label = format!("{}…", truncated);
        }
        self.inlay_hint_table.push((offset, label));
    }

    /// Check if a type is the special `BindingName` struct type.
    /// When an implicit parameter has this type, the compiler synthesizes
    /// the current let-binding name instead of creating a metavariable.
    fn is_binding_name_type(&self, decl: &std::collections::HashMap<SmolStr, (Span<()>, Rc<Tm>, Rc<Val>, Rc<Tm>, Rc<VTy>, Option<PrimFunc>)>, a: &Rc<Val>) -> bool {
        let a_forced = self.force(decl, a);
        match a_forced.as_ref() {
            Val::Sum(name, _, _, _) if name.data == "BindingName" => true,
            Val::Decl(name, sp) if name.data == "BindingName" && sp.is_empty() => true,
            _ => false,
        }
    }

    fn insert_go(&mut self, cxt: &Cxt, t: Rc<Tm>, va: Rc<Val>, span: Span<()>) -> (Rc<Tm>, Rc<VTy>) {
        let va = self.force(&cxt.decl, &va);
        match va.as_ref() {
            Val::Pi(_, Icit::Impl, a, b) => {
                // Special case: if the implicit parameter type is `BindingName`,
                // synthesize the current let-binding name automatically.
                if self.is_binding_name_type(&*cxt.decl, a) {
                    let name_str = cxt.binding_name.clone().unwrap_or_else(|| SmolStr::new(""));
                    // Find the correct decl key for BindingName.mk (may be double-qualified)
                    let mk_key = if cxt.decl.contains_key("BindingName.mk") {
                        SmolStr::new("BindingName.mk")
                    } else {
                        cxt.decl.keys()
                            .find(|k| k.ends_with(".BindingName.mk"))
                            .cloned()
                            .unwrap_or_else(|| SmolStr::new("BindingName.mk"))
                    };
                    let bn_tm: Rc<Tm> = Tm::App(
                        Tm::Decl(empty_span(mk_key)).into(),
                        Tm::LiteralIntro(empty_span(name_str.to_string())).into(),
                        Icit::Expl,
                    ).into();
                    let bn_val = self.eval(&cxt.decl, &cxt.env, &bn_tm);
                    return self.insert_go(
                        cxt,
                        Tm::App(t, bn_tm, Icit::Impl).into(),
                        self.closure_apply(&cxt.decl, b, bn_val),
                        span,
                    );
                }
                //println!("insert {:?}", a);
                let m = self.fresh_meta(cxt, a.clone(), span);
                let mv = self.eval(&cxt.decl, &cxt.env, &m);
                self.insert_go(
                    cxt,
                    Tm::App(t, m, Icit::Impl).into(),
                    self.closure_apply(&cxt.decl, b, mv),
                    span,
                )
            }
            _ => (t, va),
        }
    }
    fn insert_t(&mut self, cxt: &Cxt, act: Result<(Rc<Tm>, Rc<VTy>), Error>, span: Span<()>) -> Result<(Rc<Tm>, Rc<VTy>), Error> {
        act.map(|(t, va)| self.insert_go(cxt, t, va, span))
    }
    pub fn insert(&mut self, cxt: &Cxt, act: Result<(Rc<Tm>, Rc<VTy>), Error>, span: Span<()>) -> Result<(Rc<Tm>, Rc<VTy>), Error> {
        act.and_then(|x| if let Tm::Lam(_, Icit::Impl, _) = x.0.as_ref() {
            Ok(x)
        } else {
            self.insert_t(cxt, Ok(x), span)
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
                    let m = self.fresh_meta(cxt, a.clone(), name.to_span());
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
        let a = match ori.as_ref() {
            Val::SumCase { typ, .. } => typ.clone(),
            _ => a,
        };
        let (t_inferred, cxt) = self.check_pm(cxt, t, a)?;
        let tmv = self.eval(&cxt.decl, &cxt.env, &t_inferred);
        let new_cxt = self.unify_pm(&cxt, &ori, &tmv, t_span).unwrap_or(cxt);
        Ok((t_inferred, new_cxt))
    }
    /// Pattern-matching version of `infer_expr`.
    ///
    /// For `Raw::App` arguments, uses `check_pm` (→ `unify_pm`) instead of
    /// `check::<false>` (→ `unify_catch`), so that Rigid pattern variables
    /// get refined rather than unified through the regular solver.
    ///
    /// Non-`App` forms delegate to the regular `infer_expr`.
    ///
    /// Forms a mutually-recursive cycle with `check_pm`:
    /// ```text
    /// check_pm → infer_expr_pm → (App) → check_pm → infer_expr_pm → …
    /// ```
    pub fn infer_expr_pm(&mut self, cxt: &Cxt, t: Raw) -> Result<(Rc<Tm>, Rc<Val>, Cxt), Error> {
        match t {
            Raw::App(t, u, i) => {
                let t_span = t.to_span();
                let t_raw = t.as_ref().clone();
                let u_raw = u.as_ref().clone();
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
                        let (t, tty) = self.insert_t(cxt, infered, t_span)?;
                        (Icit::Expl, t, tty)
                    }
                };
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
                        let meta_before = self.meta.len();
                        let apply_obj = Raw::Obj(Box::new(t_raw), Some(empty_span(SmolStr::new("apply"))));
                        let apply_call = Raw::App(Box::new(apply_obj), Box::new(u_raw), Either::Icit(i));
                        if let Ok(result) = self.infer_expr(cxt, apply_call) {
                            return Ok((result.0, result.1, cxt.clone()));
                        }
                        self.meta.truncate(meta_before);

                        let new_meta = self.fresh_meta(cxt, Val::U(0).into(), t_span);
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
                                t_span,
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
                // KEY DIFFERENCE: use check_pm instead of check::<false>
                let (u_checked, cxt) = self.check_pm(cxt, *u, a.clone())?;
                let ret_type = self.closure_apply(&cxt.decl, &b_closure, self.eval(&cxt.decl, &cxt.env, &u_checked));
                Ok((
                    Tm::App(t, u_checked, i).into(),
                    ret_type,
                    cxt,
                ))
            }
            _ => self.infer_expr(cxt, t).map(|(tm, ty)| (tm, ty, cxt.clone())),
        }
    }
    pub fn check_pm(&mut self, cxt: &Cxt, t: Raw, a: Rc<Val>) -> Result<(Rc<Tm>, Cxt), Error> {
        let t_span = t.to_span();
        let (t_inferred, inferred_type, refined_cxt) = self.infer_expr_pm(cxt, t)?;
        let (t_inferred, inferred_type) = self.insert(&refined_cxt, Ok((t_inferred, inferred_type)), t_span)?;
		let new_cxt = self.unify_pm(&refined_cxt, &a, &inferred_type, t_span)?;
        Ok((t_inferred, new_cxt))
    }
    pub(super) fn unify_pm(&mut self, cxt: &Cxt, t: &Rc<Val>, t_prime: &Rc<Val>, t_span: Span<()>) -> Result<Cxt, Error> {
        //println!("  {}", self.meta.len());
        let t = self.force(&cxt.decl, t);
        let t_prime = self.force(&cxt.decl, t_prime);
        match (t.as_ref(), t_prime.as_ref()) {
            (Val::Rigid(x1, sp1), Val::Rigid(x2, sp2)) if sp1.is_empty() && sp2.is_empty() && x1 == x2 => {
                Ok(cxt.update_cxt(self, *x1, t_prime, false))
            }
            // Two different Rigids with empty spines: one may have already been
            // refined by matching a previous field's constructor while the other
            // is a freshly-created pattern variable (env is still a self-reference).
            // Update the UNREFINED one so earlier refinements are preserved.
            (Val::Rigid(x1, sp1), Val::Rigid(x2, sp2))
                if sp1.is_empty() && sp2.is_empty() && x1 != x2 =>
            {
                let x1_ix = lvl2ix(cxt.lvl, *x1).0 as usize;
                let x2_ix = lvl2ix(cxt.lvl, *x2).0 as usize;
                let x1_is_self = cxt.env.iter().nth(x1_ix)
                    .map(|ev| matches!(ev.as_ref(), Val::Rigid(rx, rs) if *rx == *x1 && rs.is_empty()))
                    .unwrap_or(true);
                let x2_is_self = cxt.env.iter().nth(x2_ix)
                    .map(|ev| matches!(ev.as_ref(), Val::Rigid(rx, rs) if *rx == *x2 && rs.is_empty()))
                    .unwrap_or(true);
                if x1_is_self && !x2_is_self {
                    Ok(cxt.update_cxt(self, *x1, t_prime, true))
                } else if x2_is_self && !x1_is_self {
                    Ok(cxt.update_cxt(self, *x2, t, true))
                } else {
                    Ok(cxt.update_cxt(self, *x1, t_prime, true))
                }
            }
            (Val::Rigid(x, sp), _) if sp.is_empty() => {
                // If this Rigid has already been refined (env entry is no longer
                // the self-reference), unify the old refinement with the new value
                // instead of blindly overwriting.  This propagates constraints
                // such as n = succ _l9 from an earlier field onto n = succ _l17
                // from a later one, triggering _l9 = _l17.
                let x_prime = lvl2ix(cxt.lvl, *x).0 as usize;
                let already_refined = cxt.env.iter().nth(x_prime)
                    .map(|cur| !matches!(cur.as_ref(), Val::Rigid(rx, _) if *rx == *x))
                    .unwrap_or(false);
                if already_refined {
                    let cur = cxt.env.iter().nth(x_prime).unwrap().clone();
                    self.unify_pm(cxt, &cur, &t_prime, t_span)
                } else {
                    Ok(cxt.update_cxt(self, *x, t_prime, true))
                }
            }
            (_, Val::Rigid(x, sp)) if sp.is_empty() => {
                let x_prime = lvl2ix(cxt.lvl, *x).0 as usize;
                let already_refined = cxt.env.iter().nth(x_prime)
                    .map(|cur| !matches!(cur.as_ref(), Val::Rigid(rx, _) if *rx == *x))
                    .unwrap_or(false);
                if already_refined {
                    let cur = cxt.env.iter().nth(x_prime).unwrap().clone();
                    self.unify_pm(cxt, &t, &cur, t_span)
                } else {
                    Ok(cxt.update_cxt(self, *x, t, true))
                }
            }
            (
                Val::SumCase { index: name1, datas: d1, .. },
                Val::SumCase { index: name2, datas: d2, .. },
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
        let _g = super::prof_enter(&super::FUNC_PROF.check_universe.0, &super::FUNC_PROF.check_universe.1);
        let t_span = t.to_span();
        let x = self.infer_expr(cxt, t);
        let (t_inferred, inferred_type) = self.insert(cxt, x, t_span)?;
        match inferred_type.as_ref() {
            Val::U(u) => Ok((t_inferred, *u)),
            Val::Flex(m, sp) => {
                let (pren, prune_non_linear) = self.invert(cxt.lvl, &cxt.decl, sp)
                    .map_err(|_| Error(t_span.map(|_| "invert failed".to_owned()), vec![]))?;
                let mty = match self.meta[m.0 as usize] {
                    MetaEntry::Unsolved(ref a, _, _, _) => a.clone(),
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
                        Val::U(x) => {
                            let x = *x;
                            self.meta[m.0 as usize] = MetaEntry::Solved(Val::U(x).into(), mty);
                            Ok((t_inferred, x))
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
            // Dotless method key (`Pointsum`), matching the inherent impl's
            // registration; see trait_wrap for why keys stay dotless.
            let key = SmolStr::new(format!("{}.{}", ns_entry.2, op.data));
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
        let _g = super::prof_enter(&super::FUNC_PROF.check.0, &super::FUNC_PROF.check.1);
        //println!("{} {:?} {} {:?}", "check".blue(), t, "==".blue(), a);
        let a = self.force(&cxt.decl, a);
        // Pre-checked value (class Phase-B reuse): the term was fully checked
        // in Phase A against the same context layout (same binding order and
        // levels).  Re-eval drives the chain's side effects (module-tree
        // globals) and well-formedness, and the annotation check re-verifies
        // the Phase-A type — while the inner values are not re-elaborated.
        //
        // The unannotated-field case (Hole annotation): the fresh meta is
        // solved DIRECTLY with the Phase-A type instead of a full unify.  A
        // full unify's flex_flex would rebuild the meta's CLOSED type (which
        // closes over the let-bound field values — the whole create chain)
        // as a lambda spine, producing phantom `(bn) => ...` solutions whose
        // pruning (created inside the trait-wrapper lets) exceeds the eval
        // environment and panics `v_app_pruning`.
        if let Raw::Tm(tm, ty) = &t {
            let _ = self.eval(&cxt.decl, &cxt.env, tm);
            match a.as_ref() {
                Val::Flex(m, sp)
                    if sp.is_empty() && matches!(self.meta[m.0 as usize], MetaEntry::Unsolved(..)) =>
                {
                    let mty = match &self.meta[m.0 as usize] {
                        MetaEntry::Unsolved(ty, _, _, _) => ty.clone(),
                        _ => unreachable!(),
                    };
                    self.meta[m.0 as usize] = MetaEntry::Solved(ty.clone(), mty);
                }
                _ => {
                    self.unify_catch(cxt, &a, ty, t.to_span())?;
                }
            }
            return Ok(tm.clone());
        }
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
                // A `Raw::Tm` annotation is a Phase-A pre-checked type from a
                // class create/tree body: its (checked type Tm, eval'd type)
                // were already produced by check_universe in Phase A, and the
                // context layout is identical, so reuse them instead of
                // re-running check_universe + eval.
                let (a_checked, va) = if let Raw::Tm(tm, ty) = ret_typ.as_ref() {
                    (tm.clone(), ty.clone())
                } else {
                    let (a, _) = self.check_universe(cxt, *ret_typ)?;
                    let v = self.eval(&cxt.decl, &cxt.env, &a);
                    (a, v)
                };
                // Set binding_name so implicit BindingName params get the let-binding's name
                let cxt_named = cxt.with_binding_name(x.data.clone());
                let t_checked = self.check::<CANONICAL>(&cxt_named, *t, &va)?;
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
            (Raw::Hole(span), _) => Ok(self.fresh_meta(cxt, a, span)),

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
                // Fast path: deep chains of unary constructor applications
                // (e.g. big `Nat` literals like `succ (succ ... zero)`) are
                // elaborated iteratively so the native stack is not consumed
                // one frame per constructor.  Returns `None` for non-chains,
                // which then take the general path below unchanged.
                if let Some(result) = self.check_constructor_chain::<CANONICAL>(cxt, &t, &a, t_span) {
                    return result;
                }
                let x = self.infer_expr(cxt, t);
        let (t_inferred, inferred_type) = self.insert(cxt, x, t_span)?;
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
    /// Fast path for checking a deep chain of constructor applications (e.g.
    /// big `Nat` literals like `succ (succ ... zero)`): the chain is
    /// elaborated iteratively instead of consuming one native stack frame per
    /// constructor.  Returns `None` when `t` is not such a chain so the
    /// caller falls back to the general path (behaviour unchanged for all
    /// existing programs).
    fn check_constructor_chain<const CANONICAL: bool>(
        &mut self,
        cxt: &Cxt,
        t: &Raw,
        a: &Rc<Val>,
        t_span: Span<()>,
    ) -> Option<Result<Rc<Tm>, Error>> {
        struct Node {
            name: Span<SmolStr>,
            def_span: Span<()>,
            vty: Rc<Val>,
            head_tm: Rc<Tm>,
            head_val: Rc<Val>,
            ret_closure: Closure,
        }
        // Walk the chain: `t` must be `App(Var(constr), arg)` with `constr`
        // an unshadowed constructor declaration, and the chain continues in
        // `arg`.  Each constructor's (forced) domain must be the same sum as
        // the type the argument is being checked against.
        let mut nodes: Vec<Node> = Vec::new();
        let mut expected: Rc<Val> = a.clone();
        let mut cur = t;
        loop {
            match cur {
                Raw::App(f, u, Either::Icit(Icit::Expl)) => {
                    let name = match f.as_ref() {
                        Raw::Var(name) if cxt.src_names.get(&name.data).is_none() => name.clone(),
                        _ => break,
                    };
                    let entry = cxt.decl.get(&name.data)?;
                    let vty = self.force(&cxt.decl, &entry.4);
                    let (dom, ret_closure) = match vty.as_ref() {
                        Val::Pi(_, Icit::Expl, dom, ret_closure) => (dom.clone(), ret_closure.clone()),
                        _ => break,
                    };
                    if !same_sum_name(&self.force(&cxt.decl, &dom), &self.force(&cxt.decl, &expected)) {
                        break;
                    }
                    // The general path runs `insert` on the head's type to
                    // solve metas; only take the fast path when the
                    // constructor type is already meta-free.
                    if entry.3.no_metas(self, &cxt.decl, cxt.lvl).is_some() {
                        break;
                    }
                    nodes.push(Node {
                        name: name.clone(),
                        def_span: entry.0,
                        vty: vty.clone(),
                        head_tm: Tm::Decl(name).into(),
                        head_val: entry.2.clone(),
                        ret_closure,
                    });
                    expected = dom;
                    cur = u.as_ref();
                }
                _ => break,
            }
        }
        // Only deep chains take the fast path; short chains (all existing
        // source code) keep the exact general-path behaviour.
        if nodes.len() < 512 {
            return None;
        }
        // Check the innermost leaf against the innermost constructor's domain.
        let leaf_tm = match self.check::<CANONICAL>(cxt, cur.clone(), &expected) {
            Ok(t) => t,
            Err(e) => return Some(Err(e)),
        };
        // Build the chain from the inside out, tracking the value (needed for
        // dependent return types) and the final return type.
        let mut tm = leaf_tm;
        let mut val = self.eval(&cxt.decl, &cxt.env, &tm);
        let mut ret: Rc<Val> = expected;
        for node in nodes.iter().rev() {
            ret = self.closure_apply(&cxt.decl, &node.ret_closure, val.clone());
            val = self.v_app(&cxt.decl, &node.head_val, val, Icit::Expl);
            tm = Tm::App(node.head_tm.clone(), tm, Icit::Expl).into();
        }
        // Report hover entries for each constructor, mirroring `infer_expr`
        // on `Raw::Var`.
        for node in &nodes {
            self.hover_table.push((
                node.name.to_span(),
                node.def_span,
                crate::L13_namespace::cxt::HoverCxt { lvl: cxt.lvl, locals: cxt.locals.clone(), decl: cxt.decl.clone() },
                node.vty.clone(),
            ));
        }
        let result = if CANONICAL {
            self.unify(cxt.lvl, cxt, a, &ret, 100).map_err(|e| {
                let err = match e {
                    super::UnifyError::Basic | super::UnifyError::Stuck => format!(
                        "can't unify\n  expected: {}\n      find: {}",
                        super::pretty_tm(0, cxt.names(), &self.quote(&cxt.decl, cxt.lvl, a)),
                        super::pretty_tm(0, cxt.names(), &self.quote(&cxt.decl, cxt.lvl, &ret)),
                    ),
                    super::UnifyError::Trait(e) => e,
                };
                Error(t_span.map(|_| err.clone()), vec![])
            }).map(|_| tm)
        } else {
            self.unify_catch(cxt, a, &ret, t_span).map(|_| tm)
        };
        Some(result)
    }
    pub fn infer(&mut self, cxt: &Cxt, t: Decl) -> Result<(DeclTm, Rc<Val>, Cxt), Error> {
        // Apply package prefix if active (unless the declaration itself sets the prefix)
        let t = match &t {
            Decl::Package { .. } | Decl::Import { .. } => t,
            _ => if let Some(ref prefix) = cxt.namespace_prefix {
                prefix_decl_name(t, prefix)
            } else { t },
        };
        self.infer_after_prefix(cxt, t)
    }
    /// The per-declaration elaboration, run on an already-prefixed decl.
    /// Split out so the class elaboration (which expands a class into its
    /// four phase-B decls with concrete field types) can recurse without
    /// re-applying the namespace prefix.
    fn infer_after_prefix(&mut self, cxt: &Cxt, t: Decl) -> Result<(DeclTm, Rc<Val>, Cxt), Error> {
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
                    if let Some((meta_cxt, oty, meta_span)) = t_tm.no_metas(self, &cxt.decl, cxt.lvl) {
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
                                .filter(|(_, entry)| matches!(entry, MetaEntry::Unsolved(ty, _, _, _)
                                    if matches!(self.force(&cxt.decl, ty).as_ref(), Val::U(_))))
                                .map(|(i, _)| i)
                                .collect();
                            if to_default.is_empty() {
                                false
                            } else {
                                // Phase 2: mutate those metas (mutable borrow)
                                for &idx in &to_default {
                                    if let MetaEntry::Unsolved(ty, _, _, _) = &self.meta[idx] {
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
                            let err_msg = if let Val::Sum(name, params, _, true) = oty.as_ref() {
                                let has_flex = params.iter().any(|(_, val, _, _)| {
                                    matches!(self.force(&cxt.decl, val).as_ref(), Val::Flex(..))
                                });
                                let instances = self.trait_solver.class_instances.get(&name.data);
                                if has_flex {
                                    format!(
                                        "cannot infer typeclass `{}`: type parameter is unknown",
                                        name.data,
                                    )
                                } else if params.is_empty() {
                                    format!("no instance of typeclass `{}`", name.data)
                                } else {
                                    let pretty_val = |val: &Rc<Val>| {
                                        super::pretty_tm(0, meta_cxt.names(), &self.quote(&meta_cxt.decl, meta_cxt.lvl, val))
                                    };
                                    let first = pretty_val(&params[0].1);
                                    let rest: Vec<String> = params[1..].iter()
                                        .map(|(_, v, _, _)| pretty_val(v))
                                        .collect();
                                    let trait_repr = if rest.is_empty() {
                                        name.data.to_string()
                                    } else {
                                        format!("{}[{}]", name.data, rest.join(", "))
                                    };
                                    // `Into` mismatch — the common `a := b` /
                                    // `a <> b` type error. Report in user terms
                                    // (source → target conversion) instead of
                                    // the internal instance list, and point at
                                    // width differences (the usual mistake).
                                    if name.data == "Into" && params.len() >= 2 {
                                        let source = pretty_val(&params[0].1);
                                        let target = pretty_val(&params[1].1);
                                        let mut msg = format!(
                                            "cannot convert `{}` to `{}` (for `:=` / `<>`): no `Into[{}]` instance for `{}`",
                                            source, target, target, source
                                        );
                                        // Width hint: UInt/Bits/SInt with
                                        // different widths — the classic slip.
                                        let width_of = |val: &Rc<Val>| -> Option<String> {
                                            match self.force(&cxt.decl, val).as_ref() {
                                                Val::Sum(n, ps, _, _)
                                                    if n.data == "UInt" || n.data == "SInt" || n.data == "Bits" =>
                                                {
                                                    ps.iter().find_map(|(_, v, _, _)| Some(pretty_val(v)))
                                                }
                                                _ => None,
                                            }
                                        };
                                        if let (Some(w1), Some(w2)) = (width_of(&params[0].1), width_of(&params[1].1)) {
                                            if w1 != w2 {
                                                msg += &format!(
                                                    " — widths differ ({} vs {}); use `resize` to change the width explicitly",
                                                    w1, w2
                                                );
                                            }
                                        }
                                        msg
                                    } else if instances.map_or(true, |i| i.is_empty()) {
                                        format!("no instance of typeclass `{}` for types `{}`", trait_repr, first)
                                    } else {
                                        let insts = instances.unwrap();
                                        format!(
                                            "no matching instance of typeclass `{}` for types `{}`\navailable instances: {}",
                                            trait_repr, first,
                                            insts.iter().map(|i| i.lvl.data.to_string()).collect::<Vec<_>>().join(", "),
                                        )
                                    }
                                }
                            } else {
                                format!(
                                    "find unsolved meta with type `{}`",
                                    super::pretty_tm(0, meta_cxt.names(), &self.quote(&meta_cxt.decl, meta_cxt.lvl, &oty)),
                                )
                            };
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
                            return Err(Error(meta_span.map(|_|
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
                // Inlay hint: def without explicit return type → show inferred return type.
                if matches!(ret_type, Raw::Hole(_)) {
                    let (ret_val, ret_lvl) = self.peel_pi(&ret_cxt, &vty);
                    let ret_tm = self.quote(&ret_cxt.decl, ret_lvl, &ret_val);
                    if ret_tm.no_metas(self, &ret_cxt.decl, ret_lvl).is_none() {
                        let label = format!(": {}", super::pretty_tm(0, ret_cxt.names(), &ret_tm));
                        // Anchor the hint after the parameter list (last param's end),
                        // so `def foo[A](a: A)` gets `: T` between `)` and `=`.
                        // For parameterless defs (`def g = ...`) keep it right after the name.
                        let pos = params
                            .last()
                            .map(|p| p.1.to_span().end_offset + 1)
                            .unwrap_or_else(|| name.to_span().end_offset);
                        self.inlay_hint_table.push((pos, label));
                    }
                }
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
                    if self.defer_println {
                        self.println_jobs.push(super::PrintlnJob {
                            tm: tm.clone(),
                            span,
                            decl: cxt.decl.clone(),
                            env: cxt.env.clone(),
                            names: cxt.names(),
                        });
                        DeclTm::Println(tm, String::new(), span)
                    } else {
                        let t_pretty = super::pretty_tm(0, cxt.names(), &self.nf(&cxt.decl, &cxt.env, &tm));
                        DeclTm::Println(tm, t_pretty, span)
                    }
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
            Decl::ImplDecl { name, params, trait_name, trait_params, methods, inherent, from_class } => {
                let span = name.to_span();
                let mut cxt = cxt.clone();
                if inherent {
                    // ── Inherent impl (`impl Foo { ... }`) ──
                    // Register `Foo.method` defs in the type's namespace so
                    // `x.method` member lookup dispatches to them. Each instance
                    // method takes `this: Foo` as its first explicit param;
                    // static methods are registered as `Foo.method` (qualified
                    // access only, excluded from instance dispatch).
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
                    // Clean type-head prefix: `Adder.name` for `class Adder[w]`
                    // (not the Display of the whole Pi chain).
                    let type_name = raw_ctor_name(&name).unwrap_or_else(|| {
                        SmolStr::new(format!("{}", name_raw.to_string().chars().filter(|c| c.is_alphanumeric() || *c == '.').collect::<String>()))
                    });
                    // Only instance methods participate in `x.method` dispatch.
                    let method_names: std::collections::HashSet<SmolStr> = methods.iter()
                        .filter(|(_, is_static)| !is_static)
                        .flat_map(|(x, _)| match x {
                            Decl::Def { name, .. } => Some(name.data.clone()),
                            _ => None
                        })
                        .collect();
                    cxt.namespace = cxt.namespace.prepend((name_v, method_names, type_name.clone()));
                    for (decl, is_static) in methods.iter() {
                        match decl {
                            Decl::Def { name: name_d, params: p, ret_type, body } => {
                                if !is_static {
                                    // Operator-symbol registration (inherent impl):
                                    // an operator-named method whose body is a direct
                                    // helper application (`helper this that`) records
                                    // (helper, arity) → operator so `quote` can restore
                                    // the infix form of the inlined helper call.
                                    if is_operator_method_name(&name_d.data) {
                                        if let Some(head) = raw_ctor_name(&body) {
                                            self.symbol_table.insert(
                                                (head, params.len() + 1 + p.len()),
                                                name_d.data.clone(),
                                            );
                                        }
                                    }
                                    // `infer_after_prefix` (not `infer`): the
                                    // method name `TypeName.method` is already
                                    // fully qualified; re-running the package
                                    // prefix would double-prefix it.
                                    let t = self.infer_after_prefix(&cxt, Decl::Def {
                                        name: name_d.clone().map(|x| SmolStr::new(format!("{}.{x}", type_name))),
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
                                    let static_name = format!("{}.{}", type_name, name_d.data);
                                    let t = self.infer_after_prefix(&cxt, Decl::Def {
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
                                return Err(Error(span.map(|_| "unsupported method declaration in inherent impl".to_string()), vec![]));
                            },
                        }
                    }
                } else {
                    // I3b: resolve the trait name through the file's namespace
                    // prefix — a trait declared in `package mylib` is registered
                    // as `mylib.HasVal`, but the impl writes the bare `HasVal`.
                    let trait_full: SmolStr = {
                        let bare = trait_name.data.clone();
                        if self.trait_out_param.contains_key(&bare) {
                            bare
                        } else if let Some(ref prefix) = cxt.namespace_prefix {
                            let qualified = SmolStr::new(format!("{}.{}", prefix, bare));
                            if self.trait_out_param.contains_key(&qualified) {
                                qualified
                            } else {
                                bare
                            }
                        } else {
                            bare
                        }
                    };
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
                    let out_param = self.trait_out_param.get(&trait_full)
                        .ok_or(Error(trait_name.clone().map(|n| format!("trait `{}` not declared", n)), vec![]))?;
                    // ── Goto-definition / hover for the impl header ──
                    // The typeclass name token (`XXX` in `impl XXX for xx`) is a
                    // USE of the trait, not a defining occurrence: resolve it to
                    // the trait declaration (`trait XXX`), whose def span lives in
                    // the decl table under the (possibly package-prefixed) full
                    // name — across files too (e.g. `IMasterSlave` declared in the
                    // prelude's hdl-bus.typort). Without this entry the click
                    // resolved to the impl instance def below, whose synthetic
                    // name span was the trait-name token itself (jump-to-self).
                    if let Some((trait_def_span, _, _, _, trait_vty, _)) = cxt.decl.get(&trait_full) {
                        self.hover_table.push((
                            trait_name.to_span(),
                            *trait_def_span,
                            crate::L13_namespace::cxt::HoverCxt {
                                lvl: cxt.lvl,
                                locals: cxt.locals.clone(),
                                decl: cxt.decl.clone(),
                            },
                            trait_vty.clone(),
                        ));
                    }
                    // Similarly, each method name token in the impl body
                    // (`def m` implementing a trait method) resolves to the
                    // method's declaration in the trait — its name span is
                    // recorded in `trait_definition` (including methods
                    // inherited from supertraits, whose spans point at the
                    // supertrait's declaration). The hover value is the impl
                    // method's own type (params → ret), evaluated in the
                    // impl-parameter context.
                    if let Some((_, _, _, trait_methods)) = self.trait_definition.get(&trait_full).cloned() {
                        for (decl, _) in methods.iter() {
                            if let Decl::Def { name: def_name, params: m_params, ret_type: m_ret, .. } = decl {
                                if let Some((tm_name, _, _, _)) = trait_methods.iter().find(|(mn, _, _, _)| mn.data == def_name.data) {
                                    let mty = m_params.iter().rev().fold(m_ret.clone(), |a, b| {
                                        Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                                    });
                                    let mty_val = self.infer_expr(&temp_cxt, mty)
                                        .map(|(t, _)| self.eval(&temp_cxt.decl, &temp_cxt.env, &t))
                                        .unwrap_or_else(|_| Val::U(0).into());
                                    self.hover_table.push((
                                        def_name.to_span(),
                                        tm_name.to_span(),
                                        crate::L13_namespace::cxt::HoverCxt {
                                            lvl: temp_cxt.lvl,
                                            locals: temp_cxt.locals.clone(),
                                            decl: temp_cxt.decl.clone(),
                                        },
                                        mty_val,
                                    ));
                                }
                            }
                        }
                    }
                    // Keep ALL params (including outParam) so the solver can distinguish instances
                    // that differ only in output params (e.g., Into[String] vs Into[Bool] for the same type)
                    let typ_name = SmolStr::new(format!("{:?}{:?}", trait_full, trait_param));
                    let inst = Instance {
                        assertion: Assertion { name: trait_full.clone(), arguments: trait_param },
                        dependencies: List::new(),
                        lvl: trait_name.to_span().map(|_| typ_name.clone()),
                    };
                    self.trait_solver.impl_trait_for(trait_full.clone(), inst);
                    // Fill in missing methods with default bodies from the trait definition
                    let mut methods = methods;
                    // Number of methods provided by the class itself (after the
                    // from_class filter): those are referenced as `TypeName.method`
                    // namespace defs below. Default bodies appended afterwards are
                    // still elaborated as record lambdas.
                    let mut class_method_count = methods.len();
                    if let Some((_, _, _, trait_methods)) = self.trait_definition.get(&trait_full).cloned() {
                        // For class-generated impls, drop methods the trait does not declare
                        // (those are kept in the class's inherent impl instead) and drop
                        // static methods — a static class method does not implement a
                        // trait method; the trait's default (if any) applies instead.
                        if from_class {
                            methods.retain(|(decl, is_static)| !is_static && match decl {
                                Decl::Def { name, .. } => trait_methods.iter().any(|(tm, _, _, _)| tm.data == name.data),
                                _ => false,
                            });
                        }
                        class_method_count = methods.len();
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
                    if let Some((trait_params_def, _, _, _)) = self.trait_definition.get(&trait_full) {
                        // Collect associated type indices (params declared as `type ...`)
                        let assoc_names: Vec<(usize, SmolStr)> = trait_params_def.iter()
                            .enumerate()
                            .filter_map(|(i, (name, _, _))| {
                                if self.assoc_defaults.contains_key(&(trait_full.clone(), name.data.clone())) {
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
                                    if let Some(default_type) = self.assoc_defaults.get(&(trait_full.clone(), aname.clone())) {
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
                        .fold(Raw::Var(empty_span(SmolStr::new(format!("{}.mk", trait_full)))), |ret, x| {
                            Raw::App(Box::new(ret), Box::new(x), Either::Icit(Icit::Impl))
                        });
                    // For class-generated impls the methods were already elaborated
                    // as `TypeName.method` defs by the class's inherent impl (which
                    // is expanded first). Reference those defs instead of
                    // re-elaborating the bodies as lambdas — a single elaboration
                    // and a single semantic source, so trait method bodies may
                    // also call sibling methods through `this`.
                    let class_type_name = if from_class { raw_ctor_name(&name) } else { None };
                    for (i, (decl, _)) in methods.into_iter().enumerate() {
                        if let Decl::Def { name: def_name, params, ret_type: _, body } = decl {
                            // Operator-symbol registration (trait impl): an
                            // operator-named method whose body is a direct helper
                            // application (`helper this that`) records
                            // (helper, arity) → operator so `quote` can restore the
                            // infix form of the inlined helper call. Class methods
                            // were already registered by the inherent impl.
                            if is_operator_method_name(&def_name.data) {
                                if let Some(head) = raw_ctor_name(&body) {
                                    if class_type_name.is_none() {
                                        self.symbol_table.insert(
                                            (head, params.len() + 1),
                                            def_name.data.clone(),
                                        );
                                    }
                                }
                            }
                            // Only the class's own methods (i < class_method_count)
                            // exist as namespace defs; trait default bodies must be
                            // elaborated as record lambdas.
                            let method_expr = match &class_type_name {
                                Some(ty) if i < class_method_count =>
                                    Raw::Var(def_name.map(|n| SmolStr::new(format!("{}.{}", ty, n)))),
                                _ => Raw::Lam(
                                    def_name.map(|_| SmolStr::new("this")),
                                    Either::Icit(Icit::Expl),
                                    Box::new(params.into_iter().rev()
                                        .fold(body, |ret, x| Raw::Lam(x.0.clone(), Either::Icit(x.2), Box::new(ret)))
                                    )
                                ),
                            };
                            ret = Raw::App(
                                Box::new(ret),
                                Box::new(method_expr),
                                Either::Icit(Icit::Expl),
                            );
                        }
                    }
                    // Register the impl instance (`trait_full(typ)`) under a
                    // synthetic name with an EMPTY span: the name never appears
                    // in source, so the def's self-hover entry must not claim
                    // any real token — otherwise clicking the typeclass name
                    // in the impl header would "goto" back into this impl
                    // instead of the trait declaration (see the entry pushed
                    // above for `trait_name`).
                    let (_, _, c) = self.infer_after_prefix(&cxt, Decl::Def {
                        name: empty_span(typ_name),
                        params,
                        ret_type: trait_params.into_iter()
                            .fold(Raw::App(
                                Raw::Var(empty_span(trait_full)).into(),
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
                // X3: resolve supertrait names through the file's namespace
                // prefix — a supertrait declared in the same `package mylib`
                // registers as `mylib.A` while `trait B: A` writes the bare `A`.
                // Prelude traits keep their bare name (already registered).
                let resolved_supertraits: Vec<Span<SmolStr>> = supertraits.iter().map(|s| {
                    let bare = s.data.clone();
                    let resolved = if self.trait_definition.contains_key(&bare) {
                        bare
                    } else if let Some(ref prefix) = cxt.namespace_prefix {
                        let qualified = SmolStr::new(format!("{}.{}", prefix, bare));
                        if self.trait_definition.contains_key(&qualified) { qualified } else { bare }
                    } else {
                        bare
                    };
                    s.clone().map(|_| resolved.clone())
                }).collect();
                // Transitive supertrait method resolution with cycle detection.
                // Cycle detection tracks the current DFS *path* (not the set of
                // all visited traits) so that diamond inheritance (A: B, C;
                // B: D; C: D) is not misreported as a cycle.
                let mut all_methods = methods.clone();
                let mut stack: Vec<(SmolStr, std::collections::HashSet<SmolStr>)> = resolved_supertraits
                    .iter()
                    .map(|s| {
                        let mut path = std::collections::HashSet::new();
                        path.insert(name.data.clone());
                        (s.data.clone(), path)
                    })
                    .collect();
                while let Some((st_name, path)) = stack.pop() {
                    if path.contains(&st_name) {
                        return Err(Error(empty_span(format!("cyclic supertrait: `{}` appears twice in the chain", st_name)), vec![]));
                    }
                    let mut path = path;
                    path.insert(st_name.clone());
                    if let Some((_, _, st_sts, st_methods)) = self.trait_definition.get(&st_name) {
                        // Add supertrait's supertraits to the stack (detect cycles)
                        for st_st in st_sts {
                            if path.contains(&st_st.data) {
                                return Err(Error(empty_span(format!("cyclic supertrait: `{}` appears twice in the chain", st_st.data)), vec![]));
                            }
                            stack.push((st_st.data.clone(), path.clone()));
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
                self.trait_definition.insert(name.data.clone(), (param.clone(), out_param.clone(), resolved_supertraits.clone(), all_methods.clone()));
                self.trait_out_param.insert(name.data.clone(), out_param);
                // Store associated type defaults
                for (aname, adefault) in &assoc_defaults {
                    self.assoc_defaults.insert((name.data.clone(), aname.clone()), adefault.clone());
                }
                let mut cxt = cxt.clone();
                // Re-elaborate the trait as its record enum WITHOUT re-applying
                // the package prefix: the trait name was already prefixed by
                // `prefix_decl_name` at the `infer` entry, and going through
                // `infer` again would double-prefix it (`mylib.mylib.HasVal`).
                let (_, _, c) = self.infer_after_prefix(&cxt, Decl::Enum {
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
                // G6: record the declared package as a visible namespace for
                // the suffix-fallback scoping.
                Rc::make_mut(&mut cxt.namespaces).insert(SmolStr::new(&pkg_path));
                Ok((DeclTm::Package, Val::U(0).into(), cxt))
            },
            Decl::Import { prefix, names, wildcard } => {
                let prefix_str = prefix.join(".");
                let mut cxt = cxt.clone();
                // G6: record the imported namespace as visible for the
                // suffix-fallback scoping (imports also resolve via import_map).
                if !prefix_str.is_empty() {
                    Rc::make_mut(&mut cxt.namespaces).insert(SmolStr::new(&prefix_str));
                }
                // G4: reject single-name imports (`import foo`) — a bare name
                // is not unique and cannot be traced back to a provider file.
                if prefix.is_empty() && !names.is_empty() {
                    return Err(Error(empty_span(format!(
                        "single-name import `{}` is not supported; import a package namespace instead (e.g. `import ns.{}`)",
                        names.join(", "), names.join(", ")
                    )), vec![]));
                }
                // Collect (alias, full-qualified-key) pairs WITHOUT touching
                // `cxt.decl` — import aliases are file-local visibility, kept in
                // `self.import_map` and resolved during variable lookup.
                let mut aliases: Vec<(SmolStr, SmolStr)> = vec![];
                if wildcard {
                    let prefix_search = format!("{}.", prefix_str);
                    let matched: Vec<SmolStr> = cxt.decl.keys()
                        .filter(|k| k.starts_with(&prefix_search))
                        .map(|k| k.clone())
                        .collect();
                    if matched.is_empty() {
                        return Err(Error(empty_span(format!(
                            "cannot import '{}': no such namespace in scope", prefix_str
                        )), vec![]));
                    }
                    for full in matched {
                        let stripped = SmolStr::new(full.strip_prefix(&prefix_search).unwrap());
                        aliases.push((stripped, full));
                    }
                    // Also bring the prefix itself if it's a decl (`import mylib.Tree`
                    // where `mylib.Tree` is a type), so `Tree` resolves.
                    if let Some((k, _)) = cxt.decl.iter().find(|(k, _)| k.as_str() == prefix_str) {
                        let last = prefix.last().unwrap().clone();
                        aliases.push((last, k.clone()));
                    }
                } else {
                    for n in names {
                        let full_name = SmolStr::new(format!("{}.{}", prefix_str, n));
                        if !cxt.decl.contains_key(&full_name) {
                            return Err(Error(empty_span(format!(
                                "cannot import '{}': not in scope", full_name
                            )), vec![]));
                        }
                        aliases.push((n.clone(), full_name.clone()));
                        // Dotted aliases for the imported member's own members:
                        // `import mylib.Tree` brings `Tree.mk`, `Tree.leaf`, ...
                        // so the `.mk` shorthand (`Tree.mk` → Raw::Var("Tree.mk"))
                        // and qualified member access keep working.
                        let member_prefix = format!("{}.", full_name);
                        let members: Vec<SmolStr> = cxt.decl.keys()
                            .filter(|k| k.starts_with(&member_prefix))
                            .map(|k| k.clone())
                            .collect();
                        for full in members {
                            let stripped = full.strip_prefix(&member_prefix).unwrap();
                            aliases.push((SmolStr::new(format!("{}.{}", n, stripped)), full));
                        }
                    }
                }
                // I1: insert into import_map, rejecting conflicting aliases.
                for (alias, full) in aliases {
                    if let Some(existing) = self.import_map.get(&alias) {
                        if existing != &full {
                            return Err(Error(empty_span(format!(
                                "ambiguous import: '{}' refers to both '{}' and '{}'",
                                alias, existing, full
                            )), vec![]));
                        }
                    } else {
                        self.import_map.insert(alias, full);
                    }
                }
                Ok((DeclTm::Import, Val::U(0).into(), cxt))
            },
            Decl::Derive { .. } => {
                panic!("Derive should have been expanded before elaboration")
            },
            Decl::Class { name, params, items, traits } => {
                // ══ Phase A: infer each field value's type in the create's
                // parameter context — BEFORE the struct exists. ══
                // Bind the create's parameters: class params first, then the
                // implicit `bn: BindingName` for Module classes (mirrors the
                // create's ctor params so inferred types quote to the same
                // names/levels the create will use).
                let mut a_cxt = cxt.clone();
                for (pname, pty, _) in params.iter() {
                    let (a_checked, _) = self.check_universe(&a_cxt, pty.clone())?;
                    let a_eval = self.eval(&a_cxt.decl, &a_cxt.env, &a_checked);
                    a_cxt = a_cxt.bind(pname.clone(), self.quote(&a_cxt.decl, a_cxt.lvl, &a_eval), a_eval);
                }
                if traits.iter().any(|(t, _)| t.data == "Module") {
                    let (a_checked, _) = self.check_universe(&a_cxt, Raw::Var(empty_span(SmolStr::new("BindingName"))))?;
                    let a_eval = self.eval(&a_cxt.decl, &a_cxt.env, &a_checked);
                    a_cxt = a_cxt.bind(empty_span(SmolStr::new("bn")), self.quote(&a_cxt.decl, a_cxt.lvl, &a_eval), a_eval);
                }
                // Walk the items in declaration order: later fields may
                // reference earlier ones (the create binds all of them, with
                // shadowing).  Each field value is checked here — against the
                // fresh meta for unannotated fields (which the check solves to
                // the value's inferred type, closed or
                // class-parameter-dependent) and against the annotation for
                // annotated ones — and bound with its real value, exactly like
                // the create body's own let chain.  The inferred type becomes
                // the struct field type, so the struct never holds a Hole slot
                // whose meta would later be instantiated with the create's
                // fresh implicit arguments (the old "can't unify for unsolved
                // meta" failure).  Annotated fields keep their annotation
                // verbatim as the struct field type.
                let mut struct_field_types: Vec<(Span<SmolStr>, Raw)> = Vec::new();
                // Phase-A reuse data: (name, checked value, value type,
                // checked annotation) per class item (fields + statements,
                // declaration order), plus whether the value references the
                // create-only `bn` binding.
                let mut prechecked: Vec<(Span<SmolStr>, Rc<Tm>, Rc<Val>, Rc<Tm>)> = Vec::new();
                let mut bn_refs: Vec<bool> = Vec::new();
                let mut stmt_idx = 0usize;
                let mut bind_idx = 0usize;
                for item in items.iter() {
                    let (n, ty, val) = match item {
                        ClassItem::Field(n, t, v) => (n.clone(), t.clone(), v.clone()),
                        ClassItem::Stmt(expr) => {
                            let n = empty_span(SmolStr::new(format!("_s{stmt_idx}")));
                            stmt_idx += 1;
                            (n.clone(), Raw::Hole(n.to_span()), expr.clone())
                        }
                        ClassItem::Method(_, _) => continue,
                    };
                    let (a_checked, _) = self.check_universe(&a_cxt, ty.clone())?;
                    let va = self.eval(&a_cxt.decl, &a_cxt.env, &a_checked);
                    // Check the value — against the fresh meta for unannotated
                    // fields (which the check solves to the value's inferred
                    // type), against the annotation for annotated ones — and
                    // bind the real value so later fields referencing it (as a
                    // value or through member access) elaborate identically to
                    // the create body's own let chain.
                    let cxt_named = a_cxt.with_binding_name(n.data.clone());
                    let t_checked = self.check::<false>(&cxt_named, val, &va)?;
                    let vt = self.eval(&a_cxt.decl, &a_cxt.env, &t_checked);
                    let raw_ty = if matches!(ty, Raw::Hole(_)) {
                        // Unannotated: the struct field type is the inferred
                        // type.  Re-express it as a Raw annotation; fall back
                        // to the original Hole when the type cannot be
                        // expressed in Raw (e.g. a string literal's
                        // `LiteralType`).
                        let field_ty = self.force(&a_cxt.decl, &va);
                        self.tm_to_raw_type(&a_cxt, &self.quote(&a_cxt.decl, a_cxt.lvl, &field_ty))
                            .unwrap_or_else(|| Raw::Hole(n.to_span()))
                    } else {
                        // Annotated: keep the annotation verbatim.
                        ty.clone()
                    };
                    if matches!(item, ClassItem::Field(..)) {
                        struct_field_types.push((n.clone(), raw_ty));
                    }
                    // `bn_refs` must use the ACTUAL binding index (non-method
                    // items only, in binding order) — the same index that gives
                    // the item's context level — not the raw enumerate index:
                    // a class that declares a method BEFORE a field would
                    // otherwise miscompute the bn-reference test.
                    bn_refs.push(Self::tm_refs_bn(&t_checked, bind_idx));
                    bind_idx += 1;
                    a_cxt = a_cxt.define(n.clone(), t_checked.clone(), vt, a_checked.clone(), va.clone());
                    prechecked.push((n, t_checked, va, a_checked));
                }

                // ══ Phase B: assemble the struct from the inferred
                // (name, type) pairs, then formally elaborate the create
                // (whose let chain re-checks the field values against the now
                // concrete struct field types), the methods' inherent impl and
                // the trait impls — the exact decl sequence the parser-level
                // expansion used to produce.  The create/tree bodies reuse the
                // Phase-A checked terms (no re-elaboration). ══
                let prechecked = super::parser::PrecheckedItems {
                    items: prechecked,
                    bn_refs,
                };
                let decls = super::parser::expand_class_decls(
                    name, params, items, traits, struct_field_types, Some(&prechecked),
                );
                let mut cxt = cxt.clone();
                for d in decls {
                    let (_, _, c) = self.infer_after_prefix(&cxt, d)?;
                    cxt = c;
                }
                Ok((DeclTm::Class {}, Val::U(0).into(), cxt))
            },
        }
    }
    /// True when `tm` — the checked value of the `i`-th BOUND class item
    /// (fields + statements, methods excluded, checked at level
    /// params + `bn` + i) — references the implicit `bn: BindingName` binding
    /// (level params + `bn`).  `bn` is in scope in the create (which declares
    /// it) but NOT in method bodies such as `tree`; reusing such a value in a
    /// method would silently shift the reference onto `this`, so the method
    /// chain reuse must be skipped when any reused value references `bn`.
    ///
    /// The rule: a Var(ix) at binder-depth `d` inside the value references the
    /// binding at level (check_level + d − ix − 1); `bn`'s level is
    /// check_level − i − 1, so a `bn` reference is exactly `ix == i + d`.
    fn tm_refs_bn(tm: &Tm, i: usize) -> bool {
        fn go(tm: &Tm, i: u32, d: u32) -> bool {
            match tm {
                Tm::Var(ix) => *ix == Ix(i + d),
                Tm::Obj(t, _) => go(t, i, d),
                Tm::Lam(_, _, b) => go(b, i, d + 1),
                Tm::App(f, a, _) => go(f, i, d) || go(a, i, d),
                Tm::AppPruning(t, _) => go(t, i, d),
                Tm::U(_) | Tm::Decl(_) | Tm::Meta(_) | Tm::LiteralType | Tm::LiteralIntro(_) => false,
                Tm::Pi(_, _, a, b) => go(a, i, d) || go(b, i, d + 1),
                Tm::Let(_, ty, v, b) => go(ty, i, d) || go(v, i, d) || go(b, i, d + 1),
                Tm::Sum(_, params, _, _) => params.iter().any(|(_, v, ty, _)| go(v, i, d) || go(ty, i, d)),
                Tm::SumCase { typ, datas, .. } => {
                    go(typ, i, d) || datas.iter().any(|(_, t, _)| go(t, i, d))
                }
                Tm::Match(s, cases) => go(s, i, d) || cases.iter().any(|(_, b)| go(b, i, d + 1)),
                // Call/OpCall bodies are inlined def bodies; field values never
                // contain them, so over-counting depth only costs the
                // optimization (fallback), never a mis-fire.
                Tm::Call(_, args, body) => {
                    args.iter().any(|(a, _)| go(a, i, d)) || go(body, i, d + 1)
                }
                Tm::OpCall { args, body, .. } => {
                    args.iter().any(|(a, _)| go(a, i, d)) || go(body, i, d + 1)
                }
            }
        }
        go(tm, i as u32, 0)
    }

    /// Convert a quoted type term back to a `Raw` type expression, resolving
    /// de Bruijn variables through the context's local names (the class params
    /// and earlier fields, bound in declaration order).  Returns `None` when
    /// the type cannot be re-expressed as `Raw` (unsolved metas, literal
    /// types, calls, ...) — the caller falls back to the original annotation.
    fn tm_to_raw_type(&self, cxt: &Cxt, tm: &Rc<Tm>) -> Option<Raw> {
        let names = cxt.names();
        fn go(tm: &Rc<Tm>, names: &List<SmolStr>) -> Option<Raw> {
            match tm.as_ref() {
                // Tm::Var(ix) sits at level (quote level − ix − 1); the local
                // at that level is names[ix] (names[0] = most recent binding).
                Tm::Var(ix) => {
                    let name = names.iter().nth(ix.0 as usize)?;
                    Some(Raw::Var(empty_span(name.clone())))
                }
                Tm::Decl(n) => Some(Raw::Var(n.clone())),
                Tm::Obj(f, n) => Some(Raw::Obj(Box::new(go(f, names)?), Some(n.clone()))),
                Tm::App(f, a, i) => Some(Raw::App(
                    Box::new(go(f, names)?),
                    Box::new(go(a, names)?),
                    Either::Icit(*i),
                )),
                Tm::AppPruning(f, _) => go(f, names),
                Tm::Lam(x, i, b) => Some(Raw::Lam(
                    x.clone(),
                    Either::Icit(*i),
                    Box::new(go(b, &names.prepend(x.data.clone()))?),
                )),
                Tm::Pi(x, i, a, b) => Some(Raw::Pi(
                    x.clone(),
                    *i,
                    Box::new(go(a, names)?),
                    Box::new(go(b, &names.prepend(x.data.clone()))?),
                )),
                Tm::U(u) => Some(Raw::U(*u)),
                // A (possibly partially applied) sum type: rebuild the
                // application `Name[arg0][arg1]...` from the applied params.
                Tm::Sum(name, params, _, _) => {
                    let mut acc = Raw::Var(name.clone());
                    for (_, v, _, i) in params.iter() {
                        acc = Raw::App(Box::new(acc), Box::new(go(&v, names)?), Either::Icit(*i));
                    }
                    Some(acc)
                }
                // A constructor value inside a type index (`other[8]`): recover
                // the case name from the quoted sum's case list by position.
                Tm::SumCase { is_trait, typ, index, datas } => {
                    let case_name = match typ.as_ref() {
                        Tm::Sum(_, _, cases, _) => cases.iter().nth(*index as usize)?.clone(),
                        _ => return None,
                    };
                    let datas = datas
                        .iter()
                        .map(|(n, d, i)| Some((n.clone(), go(d, names)?, *i)))
                        .collect::<Option<Vec<_>>>()?;
                    Some(Raw::SumCase {
                        is_trait: *is_trait,
                        typ: Box::new(go(typ, names)?),
                        case_name,
                        datas,
                    })
                }
                // Term-only / non-expressible nodes: caller falls back to Hole.
                _ => None,
            }
        }
        go(tm, &names)
    }

    /// L5: push hover entries for the intermediate prefixes of a qualified
    /// access (`mylib.Foo.mk` also hovers the type `mylib.Foo` on its `Foo`
    /// token, and the constructor on `mk`).  Each entry is keyed to that
    /// segment's own span; prefixes that do not resolve to a decl are skipped.
    fn push_qualified_hover(&mut self, cxt: &Cxt, x: &Raw) {
        let mut cur = x;
        loop {
            match cur {
                Raw::Obj(inner, Some(seg)) => {
                    if let Some(full) = qualified_path_str(inner.as_ref(), &seg.data) {
                        if let Some((def_span, _, _, _, vty, _)) = cxt.decl.get(&full) {
                            self.hover_table.push((
                                seg.to_span(),
                                *def_span,
                                crate::L13_namespace::cxt::HoverCxt {
                                    lvl: cxt.lvl,
                                    locals: cxt.locals.clone(),
                                    decl: cxt.decl.clone(),
                                },
                                vty.clone(),
                            ));
                        }
                    }
                    cur = inner.as_ref();
                }
                _ => break,
            }
        }
    }

    pub fn infer_expr(&mut self, cxt: &Cxt, t: Raw) -> Result<(Rc<Tm>, Rc<Val>), Error> {
        let _g = super::prof_enter(&super::FUNC_PROF.infer_expr.0, &super::FUNC_PROF.infer_expr.1);
        /*println!(
            "{} {}",
            "infer".red(),
            t,
        );*/
        #[cfg(feature = "sampler")]
        crate::sampler::tick();
        let t_span = t.to_span();
        match t {
            // A pre-checked term has no inferable Raw structure; `check`
            // intercepts it before this point, so this is unreachable.
            Raw::Tm(_, _) => Err(Error(empty_span("internal: cannot infer a pre-checked term".to_string()), vec![])),
            // Infer variable types
            Raw::Var(name) => match cxt.src_names.get(&name.data) {
                Some((x, a)) => {
                    self.hover_table.push((t_span, a.0, crate::L13_namespace::cxt::HoverCxt { lvl: cxt.lvl, locals: cxt.locals.clone(), decl: cxt.decl.clone() }, a.1.clone()));
                    // After GADT pattern matching, `update_cxt` may have refined Rigid index
                    // variables in the environment.  The stored type `a.1` still references the
                    // ORIGINAL Rigid levels, so we re-quote and re-eval in the current env to
                    // pick up the refined values (e.g. `Fin (succ len)` → `Fin 1` when
                    // `len := 0`).  This is critical for struct fields whose types depend on
                    // an index that was refined by matching a *different* field's constructor.
                    let ty = if cxt.is_refined() {
                        // Re-evaluate in refined env to resolve GADT refinements
                        let quoted = self.quote(&cxt.decl, cxt.lvl, &a.1);
                        self.eval(&cxt.decl, &cxt.env, &quoted)
                    } else {
                        a.1.clone()
                    };
                    Ok((Tm::Var(lvl2ix(cxt.lvl, *x)).into(), ty))
                },
                None => match cxt.decl.get(&name.data) {
                    Some((def, _, _, _, vty, _)) => {
                        self.hover_table.push((t_span, *def, crate::L13_namespace::cxt::HoverCxt { lvl: cxt.lvl, locals: cxt.locals.clone(), decl: cxt.decl.clone() }, vty.clone()));
                        Ok((Tm::Decl(name).into(), vty.clone()))
                    },
                    None => {
                        // Try file-local import aliases (`import mylib.add` makes
                        // bare `add` resolve to the full decl key `mylib.add`).
                        // Priority: exact decl (incl. prelude aliases) > import_map
                        // > namespace_prefix > suffix fallback.
                        if let Some(full) = self.import_map.get(&name.data) {
                            if let Some((def, _, _, _, vty, _)) = cxt.decl.get(full) {
                                self.hover_table.push((t_span, *def, crate::L13_namespace::cxt::HoverCxt { lvl: cxt.lvl, locals: cxt.locals.clone(), decl: cxt.decl.clone() }, vty.clone()));
                                return Ok((Tm::Decl(empty_span(full.clone())).into(), vty.clone()));
                            }
                        }
                        // Try namespace prefix resolution
                        if let Some(ref prefix) = cxt.namespace_prefix {
                            let qualified = SmolStr::new(format!("{}.{}", prefix, name.data));
                            if let Some((def, _, _, _, vty, _)) = cxt.decl.get(&qualified) {
                                self.hover_table.push((t_span, *def, crate::L13_namespace::cxt::HoverCxt { lvl: cxt.lvl, locals: cxt.locals.clone(), decl: cxt.decl.clone() }, vty.clone()));
                                return Ok((Tm::Decl(empty_span(qualified)).into(), vty.clone()));
                            }
                        }
                        // Try qualified fallback: find decl entries `TypeName.name`.
                        // Collect all matches and require exactly one — HashMap
                        // iteration order is non-deterministic, so picking an
                        // arbitrary match would silently resolve the wrong
                        // constructor when several types share the name.
                        //
                        // Namespace-registered instance methods (`TypeHead.method`,
                        // e.g. `Bool.mux`) are excluded: this fallback exists for
                        // constructors (bare `mux` in patterns must resolve to the
                        // `Expr.mux` constructor), and instance methods are never
                        // called by bare name — only through `x.method` dispatch.
                        let fallback = format!(".{}", name.data);
                        let ns_method_keys: std::collections::HashSet<SmolStr> = cxt.namespace.iter()
                            .flat_map(|ns| ns.1.iter().map(move |m| SmolStr::new(format!("{}.{}", ns.2, m))))
                            .collect();
                        let matches: Vec<(SmolStr, _)> = cxt.decl.iter()
                            .filter(|(k, _)| k.ends_with(&fallback) && k.len() > fallback.len())
                            .filter(|(k, _)| {
                                // G6: the candidate's head must hang off a
                                // first-level type/namespace that is itself a
                                // decl key (`Expr.mux` → `Expr`, `Add.Add.mk` →
                                // `Add`) or a namespace this file can see
                                // (declared `package mylib` / imported) —
                                // `mylib.foo` must be imported to resolve by
                                // bare name, never via the global fallback.
                                match k.rfind('.') {
                                    Some(dot) => {
                                        let head = &k[..dot];
                                        let first = head.split('.').next().unwrap_or(head);
                                        cxt.decl.contains_key(first)
                                            || cxt.namespaces.contains(first)
                                    }
                                    None => false,
                                }
                            })
                            .filter(|(k, _)| !ns_method_keys.contains(*k))
                            .map(|(k, v)| (k.clone(), v.clone()))
                            .collect();
                        if matches.len() == 1 {
                            let (full_key, (def_span, _, _, _, vty, _)) = &matches[0];
                            self.hover_table.push((t_span, *def_span, crate::L13_namespace::cxt::HoverCxt { lvl: cxt.lvl, locals: cxt.locals.clone(), decl: cxt.decl.clone() }, vty.clone()));
                            return Ok((Tm::Decl(empty_span(full_key.clone())).into(), vty.clone()));
                        } else if matches.len() > 1 {
                            let names = matches.iter().map(|(k, _)| k.as_str()).collect::<Vec<_>>().join(", ");
                            // L1: offer an import fix per candidate to disambiguate.
                            let fixes: Vec<Box<dyn Fn() -> Option<String> + Send + Sync>> = matches.iter()
                                .map(|(k, _)| {
                                    let full = k.clone();
                                    Box::new(move || Some(format!("add `import {}`", full)))
                                        as Box<dyn Fn() -> Option<String> + Send + Sync>
                                })
                                .collect();
                            return Err(Error(name.map(|x| format!("ambiguous name `{}`: could refer to {}", x, names)), fixes));
                        }
                        // L1: when a unique `TypeName.name` exists in the global
                        // decl, suggest an import to bring it into scope (mirrors
                        // the suffix fallback, excluding instance methods).
                        let fixes: Vec<Box<dyn Fn() -> Option<String> + Send + Sync>> = {
                            let fallback = format!(".{}", name.data);
                            let ns_method_keys: std::collections::HashSet<SmolStr> = cxt.namespace.iter()
                                .flat_map(|ns| ns.1.iter().map(move |m| SmolStr::new(format!("{}.{}", ns.2, m))))
                                .collect();
                            let matches: Vec<String> = cxt.decl.iter()
                                .filter(|(k, _)| k.ends_with(&fallback) && k.len() > fallback.len())
                                .filter(|(k, _)| !ns_method_keys.contains(*k))
                                .map(|(k, _)| k.to_string())
                                .collect();
                            if matches.len() == 1 {
                                let full = matches.into_iter().next().unwrap();
                                let fix = move || Some(format!("add `import {}`", full));
                                vec![Box::new(fix)]
                            } else {
                                vec![]
                            }
                        };
                        Err(Error(name.map(|x| format!("error name not in scope: {}", x)), fixes))
                    }
                },
            },

            Raw::Obj(x, t) => {
                let receiver_span = x.to_span();
                let t = t.unwrap_or(empty_span(SmolStr::new("")));
                if t.data == "mk" {
                    if let Raw::Var(sum_name) = x.as_ref() {
                        return self.infer_expr(cxt, Raw::Var(sum_name.clone().map(|n| SmolStr::new(format!("{n}.mk")))))
                    }
                }
                // Diagnostic: asMaster/asSlave chained on an already-directed
                // bundle (`X.create.asMaster.asSlave`). Both methods REBUILD
                // the bundle with directed ports; applying a second one to the
                // result would declare every port twice (input + output of the
                // same name) — invalid Verilog. The check covers direct
                // chaining; an indirect chain through a `let` binding is
                // equivalent nonsense but not statically visible here.
                if t.data == "asMaster" || t.data == "asSlave" {
                    if let Raw::Obj(inner, Some(prev)) = x.as_ref() {
                        if prev.data == "asMaster" || prev.data == "asSlave" {
                            return Err(Error(t_span.map(|_| format!(
                                "`{}` on an already-directed bundle: `asMaster`/`asSlave` rebuild the bundle's ports, so chaining them (`...{}.{}`) would declare every port twice (input + output of the same name) — call them on a fresh `TypeName.create` result instead",
                                t.data, prev.data, t.data
                            )), vec![]));
                        }
                    }
                }
                // Check namespace-qualified access: build full path and look up in decl table
                if !t.data.is_empty() {
                    let full_path = qualified_path_str(x.as_ref(), &t.data);
                    if let Some(qual) = full_path {
                        // L5: hover entries for the intermediate prefixes of a
                        // qualified access (`mylib.Foo.mk` also hovers the type
                        // `mylib.Foo` on its `Foo` token).
                        self.push_qualified_hover(cxt, x.as_ref());
                        // Try the path as-is first
                        if let Some((def_span, _, _, _, vty, _)) = cxt.decl.get(&qual) {
                            self.hover_table.push((t_span, *def_span, crate::L13_namespace::cxt::HoverCxt { lvl: cxt.lvl, locals: cxt.locals.clone(), decl: cxt.decl.clone() }, vty.clone()));
                            return Ok((Tm::Decl(empty_span(qual)).into(), vty.clone()));
                        }
                        // Try resolving the first path segment through file-local
                        // import aliases (`import mylib.Tree` makes `Tree.leaf`
                        // resolve to `mylib.Tree.leaf`). Additive: only after the
                        // full path fails as-is, so pattern-side fully-qualified
                        // constructor paths (built from `Val::Sum` full names) and
                        // `mylib.Tree.leaf` fully-qualified access are unaffected.
                        if let Some((head, rest)) = split_first_segment(&qual) {
                            if let Some(full_head) = self.import_map.get(&head) {
                                let resolved = SmolStr::new(format!("{}.{}", full_head, rest));
                                if let Some((def_span, _, _, _, vty, _)) = cxt.decl.get(&resolved) {
                                    self.hover_table.push((t_span, *def_span, crate::L13_namespace::cxt::HoverCxt { lvl: cxt.lvl, locals: cxt.locals.clone(), decl: cxt.decl.clone() }, vty.clone()));
                                    return Ok((Tm::Decl(empty_span(resolved)).into(), vty.clone()));
                                }
                            }
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
                let (mut tm, mut a) = self.infer_expr(cxt, *x.clone())?;
                a = self.force(&cxt.decl, &a);
                // Unfold implicit `BindingName` params of the receiver so
                // qualified access like `Test.create.tree` works even when the
                // constructor takes the implicit `bn` (the module macro's class
                // constructors all do). Non-BindingName implicits are left for
                // the trait/field path below.
                while let Val::Pi(_, Icit::Impl, dom, cod) = a.as_ref() {
                    if !self.is_binding_name_type(&*cxt.decl, dom) { break; }
                    let name_str = cxt.binding_name.clone().unwrap_or_else(|| SmolStr::new(""));
                    let mk_key = if cxt.decl.contains_key("BindingName.mk") {
                        SmolStr::new("BindingName.mk")
                    } else {
                        cxt.decl.keys()
                            .find(|k| k.ends_with(".BindingName.mk"))
                            .cloned()
                            .unwrap_or_else(|| SmolStr::new("BindingName.mk"))
                    };
                    let bn_tm: Rc<Tm> = Tm::App(
                        Tm::Decl(empty_span(mk_key)).into(),
                        Tm::LiteralIntro(empty_span(name_str.to_string())).into(),
                        Icit::Expl,
                    ).into();
                    let bn_val = self.eval(&cxt.decl, &cxt.env, &bn_tm);
                    tm = Tm::App(tm, bn_tm, Icit::Impl).into();
                    a = self.force(&cxt.decl, &self.closure_apply(&cxt.decl, cod, bn_val));
                }
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
                                    while let Val::Pi(name, icit, ty, closure) = typ.as_ref() {
                                        if *icit == Icit::Expl {
                                            ret.push((name.clone(), ty.clone()));
                                            typ = self.closure_apply(
                                                &cxt.decl,
                                                closure,
                                                Val::Obj(self.eval(&cxt.decl, &cxt.env, &tm), name.clone(), List::new()).into()
                                            )
                                        } else {
                                            let val = param.pop()
                                                .map(|x| x.1)
                                                .unwrap_or(Val::Obj(self.eval(&cxt.decl, &cxt.env, &tm), name.clone(), List::new()).into());
                                            ret.push((name.clone(), ty.clone()));
                                            typ = self.closure_apply(&cxt.decl, closure, val)
                                        }
                                    }
                                    c = Some(ret);
                                }
                            }
                        }
        // Completion candidates for the receiver's fields and type params,
        // keyed to the RECEIVER's span, not the whole access's span.  The
        // filter matches a candidate when the receiver's span ends exactly at
        // the `.` directly before the cursor's member prefix (`p.`, `p.x`,
        // `outer.inner.`), so a shorter access inside a nested chain can never
        // leak its receiver's fields into a sibling dot: in `outer.inner.` the
        // inner `inner` access keys to `outer` (which ends before the outer
        // dot) while the trailing empty member keys to `outer.inner`.
        let field_info = c.as_ref().and_then(|params| {
                params.iter()
                    .find(|(fields_name, _)| fields_name == &t)
                    .map(|(name, ty)| (name.to_span(), ty.clone()))
            }).or_else(|| {
                            params
                                .iter()
                                .find(|(fields_name, _, _, _)| fields_name == &t)
                                .map(|(name, _, ty, _)| (name.to_span(), ty.clone()))
                            });
                        if let Some((def_span, val)) = field_info {
                            self.hover_table.push((t.to_span(), def_span, crate::L13_namespace::cxt::HoverCxt { lvl: cxt.lvl, locals: cxt.locals.clone(), decl: cxt.decl.clone() }, val.clone()));
                            // Successful member access — a type-ahead completion
                            // site (`p.x` with the cursor on/after the typed
                            // name).  Keyed to the receiver's span so it stays
                            // out of any enclosing empty-member completion.
                            c.iter()
                                .flatten()
                                .map(|x| (receiver_span, x.0.data.clone()))
                                .chain(params.iter().map(|x| (receiver_span, x.0.data.clone())))
                                .for_each(|x| self.completion_table.push(x));
                            Ok((
                                Tm::Obj(tm, t).into(),
                                val,
                            ))
                        } else {
                            // Completion site: empty member (`p.`) or an
                            // unresolvable partial prefix (`p.x`).  Offer the
                            // receiver's fields + type params keyed to the
                            // receiver's span (same keying rule as the success
                            // path above).
                            c.iter()
                                .flatten()
                                .map(|x| (receiver_span, x.0.data.clone()))
                                .chain(params.iter().map(|x| (receiver_span, x.0.data.clone())))
                                .for_each(|x| self.completion_table.push(x));
                            self.trait_wrap(cxt, t, a, x, tm, t_span, receiver_span)
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
                                // Completion site: empty member (`p.`) or an
                                // unresolvable partial prefix (`p.x`).  Offer
                                // this case's field names on the failure path,
                                // keyed to the receiver's span like the Sum arm.
                                for (fields_name, _, _) in params.iter() {
                                    self.completion_table.push((receiver_span, fields_name.data.clone()));
                                }
                                self.trait_wrap(cxt, t, a, x, tm, t_span, receiver_span)
                            }
                    }
                    (tm, _) => self.trait_wrap(cxt, t, a, x, tm, t_span, receiver_span),
                }
            },

            // Infer lambda expressions
            Raw::Lam(x, Either::Icit(i), t) => {
                let new_meta = self.fresh_meta(cxt, Val::U(0).into(), x.to_span());
                let a = self.eval(&cxt.decl, &cxt.env, &new_meta);
                //TODO:below may be wrong
                let new_cxt = cxt.bind(x.clone(), self.quote(&cxt.decl, cxt.lvl, &a), a.clone());
                let infered = self.infer_expr(&new_cxt, *t);
                let (t_inferred, b) = self.insert(&new_cxt, infered, x.to_span())?;
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
                let u_span = u.to_span();
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
                        let (t, tty) = self.insert_t(cxt, infered, t_span)?;
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
                        let apply_obj = Raw::Obj(Box::new(t_raw.clone()), Some(empty_span(SmolStr::new("apply"))));
                        let apply_call = Raw::App(Box::new(apply_obj), Box::new(u_raw), Either::Icit(i));
                        if let Ok(result) = self.infer_expr(cxt, apply_call) {
                            return Ok(result);
                        }
                        self.meta.truncate(meta_before);

                        let new_meta = self.fresh_meta(cxt, Val::U(0).into(), t_span);
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
                                t_span,
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
                // Tuple literal `(e0, …, en)` desugars to `TupleN.mk e0 … en`;
                // give each element its own hover entry (span = element span,
                // type = element type) so hovering an element shows the
                // element's type instead of the whole tuple's.  The LSP side
                // prefers the most specific (smallest) span, so these entries
                // win over the `TupleN.mk` entry whose span covers the whole
                // element list.  Sub-expressions inside an element (e.g. a
                // bare variable) keep their own narrower entries.
                if is_tuple_mk_head(&t_raw) {
                    self.hover_table.push((u_span, u_span, crate::L13_namespace::cxt::HoverCxt { lvl: cxt.lvl, locals: cxt.locals.clone(), decl: cxt.decl.clone() }, a.clone()));
                }
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
                let a_is_hole = matches!(a.as_ref(), Raw::Hole(_));
                // A `Raw::Tm` annotation is a cached, already-checked type
                // (trait-method Pi chain from a prior call with the same
                // receiver type): reuse it instead of re-running check_universe.
                let (a_checked, va) = if let Raw::Tm(tm, ty) = a.as_ref() {
                    (tm.clone(), ty.clone())
                } else {
                    let (a, _) = self.check_universe(cxt, *a)?;
                    let v = self.eval(&cxt.decl, &cxt.env, &a);
                    (a, v)
                };
                // Set binding_name so implicit BindingName params get the let-binding's name
                let cxt_named = cxt.with_binding_name(x.data.clone());
                let t_checked = self.check::<false>(&cxt_named, *t, &va)?;
                let vt = self.eval(&cxt.decl, &cxt.env, &t_checked);
                // Inlay hint: let without type annotation → show inferred value type.
                if a_is_hole {
                    self.push_inlay_hint(cxt, x.to_span().end_offset, &vt);
                }
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
            Raw::Hole(span) => {
                let new_meta = self.fresh_meta(cxt, Val::U(0).into(), span);
                let a = self.eval(&cxt.decl, &cxt.env, &new_meta);
                let t = self.fresh_meta(cxt, a.clone(), span);
                Ok((t, a))
            }

            Raw::LiteralIntro(literal) => Ok((Tm::LiteralIntro(literal).into(), Val::LiteralType.into())),

            Raw::Nat(n) => {
                let nat_type = cxt.decl.get("Nat").map(|x| x.2.clone())
                    .unwrap_or_else(|| Val::U(0).into());
                let nat_val = super::cxt::build_nat(n.data, n.to_span(), &nat_type);
                let nat_tm = self.quote(&cxt.decl, cxt.lvl, &nat_val);
                Ok((nat_tm, nat_type))
            }

            Raw::Match(expr, clause) => {
                let a_meta = self.fresh_meta(cxt, Val::U(0).into(), expr.to_span());
                let a = self.eval(&cxt.decl, &cxt.env, &a_meta);
                let tm = self.check::<false>(cxt, Raw::Match(expr, clause), &a)?;
                Ok((tm, a))
            }

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
                let index = match typ_val.as_ref() {
                    Val::Sum(_, _, cases, _) => cases.iter()
                        .position(|c| c == &case_name)
                        .ok_or_else(|| Error(
                            case_name.map(|x| format!("no such constructor `{}`", x)),
                            vec![],
                        ))? as u32,
                    _ => {
                        return Err(Error(
                            case_name.map(|_| format!("expected a sum type, got {:?}", typ_val)),
                            vec![],
                        ));
                    }
                };
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
                        index,
                        datas,
                    }.into(),
                    typ_val,
                ))
            }
        }
    }
    fn trait_wrap(&mut self, cxt: &Cxt, t: Span<SmolStr>, a: Rc<Val>, x: Box<Raw>, tm: Rc<Tm>, t_span: Span<()>, receiver_span: Span<()>) -> Result<(Rc<Tm>, Rc<Val>), Error> {
        let typ_raw = self.eval(&cxt.decl, &cxt.env, &self.quote(&cxt.decl, cxt.lvl, &a));
        let typ_raw_head = super::typeclass::head_key(&typ_raw);

        // --- Namespace method lookup with meta cleanup ---
        // Collect matching namespaces entries (clone to avoid borrow conflicts)
        let ns_entries: Vec<_> = cxt.namespace.iter()
            .filter(|x| x.1.contains(&t.data))
            .cloned()
            .collect();
        let ns_result = {
            if ns_entries.is_empty() {
                vec![]
            } else {
                // Snapshot full inference state: the probe may solve metas in the
                // receiver type whose solutions reference the temporary metas created
                // below. truncate() would leave those solutions dangling, so roll
                // back the entire meta / trait_metas state after the probe instead.
                // The snapshot is only taken when there are entries to probe — it
                // costs O(meta_len) per call, and most member accesses have no
                // namespace match at all.
                let meta_snapshot = self.meta.clone();
                let trait_metas_snapshot = self.trait_metas.clone();
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
                    // Cheap head pre-filter: the candidate's first EXPLICIT
                    // parameter (the receiver) must have the same type head as
                    // the receiver's type — otherwise the unify probe below can
                    // only fail.  Skips the whole meta snapshot + fresh_meta +
                    // unify_catch cost for mismatched candidates (the common
                    // case: many types share a method name).  A Flex/generic
                    // parameter head keeps the candidate.
                    if let Some(ref head) = typ_raw_head {
                        let mut self_ty = ns_entry.0.clone();
                        while let Val::Pi(_, Icit::Impl, _, cod) = self_ty.as_ref() {
                            self_ty = self.closure_apply(&cxt.decl, cod, Val::Rigid(Lvl(u32::MAX), List::new()).into());
                        }
                        if let Val::Pi(_, Icit::Expl, dom, _) = self_ty.as_ref() {
                            if let Some(param_head) = super::typeclass::head_key(&self.force(&cxt.decl, dom)) {
                                if param_head != *head {
                                    continue;
                                }
                            }
                        }
                    }
                    let mut check_typ = ns_entry.0.clone();
                    while let Val::Pi(_, Icit::Impl, dom, cod) = check_typ.as_ref() {
                        let u = self.fresh_meta(&cxt, dom.clone(), t_span);
                        let u = self.eval(&cxt.decl, &cxt.env, &u);
                        check_typ = self.closure_apply(&cxt.decl, cod, u);
                    }
                    if self.unify_catch(cxt, &check_typ, &typ_raw, t_span).is_ok() {
                        result.push(ns_entry.clone());
                    }
                    // Clean up metas created by this failed namespace entry
                    self.meta = meta_snapshot.clone();
                    self.trait_metas = trait_metas_snapshot.clone();
                }
                result
            }
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
            // Method key: `TypeHead.method` — the same dotted key the inherent
            // impl registered. Dotted method keys are safe because the bare-name
            // fallback in `infer_expr` excludes namespace-registered methods, so
            // `case mux(...)` still resolves only constructor `Expr.mux`.
            let qname = SmolStr::new(format!("{}.{}", ns_entry.2, t.data));
            let def_span = cxt.decl.get(&qname)
                .map(|(def, _, _, _, _, _)| *def)
                .unwrap_or(t.to_span());
            let result = self.infer_expr(cxt, Raw::app(
                Raw::Var(t_span.map(|_| qname.clone())),
                *x.clone(),
            ))?;
            self.hover_table.push((
                t.to_span(),
                def_span,
                crate::L13_namespace::cxt::HoverCxt { lvl: cxt.lvl, locals: cxt.locals.clone(), decl: cxt.decl.clone() },
                result.1.clone(),
            ));
            return Ok(result);
        }
        {
            let mut traits = self.trait_definition
                .iter()
                .flat_map(|(trait_name, (trait_params, out_param, _st, methods))| {
                    methods.iter()
                        .find(|x| x.0.data == t.data)
                        .map(|x| (trait_name, trait_params, out_param, x))
                })
                .filter(|(x, _, _, _)| self.trait_solver.can_satisfy(x, &typ_raw))
                .map(|(trait_name, trait_params, _, (methods_name, methods_params, ret_type, _default_body))| {
                    // Count explicit parameters: used to disambiguate same-named
                    // unary/binary operators (e.g. Neg.- (0 args) vs Sub.- (1 arg)).
                    let argc = methods_params.iter().filter(|p| p.2 == Icit::Expl).count();
                    let def_span = methods_name.to_span();
                    // Use the call-site method name span instead of the trait definition span
                    // so that error locations point to the user's code, not the trait definition.
                    let call_span: Span<SmolStr> = t.clone();
                    (
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
                                call_span.clone().map(|_| SmolStr::new("$$")),
                                trait_params.iter()
                                    .map(|x| x.0.clone())
                                    .fold(
                                        Raw::Var(call_span.clone().map(|_| trait_name.clone())),
                                        |ret, x| Raw::App(Box::new(ret), Box::new(Raw::Var(x)), Either::Icit(Icit::Impl))
                                    ),
                                Icit::Impl
                            ));
                            params.push((
                                call_span.clone().map(|_| SmolStr::new("$this")),
                                Raw::Var(call_span.clone().map(|_| SmolStr::new("Self"))),
                                Icit::Expl
                            ));
                            params.append(&mut methods_params.clone());
                            params
                        };
                        let body = std::iter::once((Raw::Var(call_span.clone().map(|_| SmolStr::new("$this"))), Icit::Expl))
                            .chain(methods_params.iter().map(|x| (Raw::Var(x.0.clone()), x.2)))
                            .fold(
                                Raw::Obj(
                                    Box::new(Raw::Var(call_span.clone().map(|_| SmolStr::new("$$")))),
                                    Some(call_span.clone()),
                                ),
                                |ret, (x, icit)| Raw::App(Box::new(ret), Box::new(x), Either::Icit(icit))
                            );
                        Raw::Let(
                            call_span.clone().map(|x| SmolStr::new(format!("${x}"))),
                            Box::new(params.iter().rev().fold(ret_type.clone(), |a, b| {
                                Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                            })),
                            Box::new(params.iter().rev().fold(body.clone(), |a, b| {
                                Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a))
                            })),
                            Box::new(Raw::App(
                                Box::new(Raw::Var(call_span.clone().map(|x| SmolStr::new(format!("${x}"))))),
                                x.clone(),
                                Either::Icit(Icit::Expl),
                            )),
                        )
                    },
                    def_span,
                    argc,
                )
                })
                .collect::<Vec<_>>();
            if traits.len() > 1 {
                // Disambiguate same-named operators by explicit-argument count:
                // an infix call (e.g. `a - b`) always has ≥1 argument, so prefer
                // the unique candidate that expects ≥1 explicit argument over the
                // zero-argument ones (e.g. Neg.- vs Sub.-). If ambiguous even by
                // arity, report the ambiguity.
                let nonzero: Vec<_> = traits.iter()
                    .filter(|(_, _, _, argc)| *argc > 0)
                    .collect();
                if nonzero.len() == 1 && nonzero.len() < traits.len() {
                    traits = nonzero.into_iter().cloned().collect();
                } else {
                    let trait_names: Vec<&SmolStr> = traits.iter().map(|(n, _, _, _)| n).collect();
                    return Err(Error(t.clone().map(|m| format!(
                        "ambiguous method `{}`: found in traits {}",
                        m,
                        trait_names.iter().map(|n| format!("`{}`", n)).collect::<Vec<_>>().join(", "),
                    )), vec![]));
                }
            }
            if let Some((_, decl, def_span, _)) = traits.first() {
                // Trait-method elaboration cache: when the same operator is
                // elaborated again on a structurally-equal receiver type, reuse
                // the already-checked Pi chain AND method-body lambda (via
                // Raw::Tm annotations) so infer_expr skips both the
                // check_universe of the Pi chain and the body re-elaboration.
                let cache_key = val_cache_key(&a, 0).map(|k| (t.data.clone(), k));
                let result = match &cache_key {
                    Some(key) => match self.trait_method_cache.get(key).cloned() {
                        Some((a_checked, va, t_checked)) => {
                            let new_decl = if let Raw::Let(n, _, _, u) = decl {
                                Raw::Let(
                                    n.clone(),
                                    Box::new(Raw::Tm(a_checked.clone(), va.clone())),
                                    Box::new(Raw::Tm(t_checked.clone(), va.clone())),
                                    u.clone(),
                                )
                            } else {
                                decl.clone()
                            };
                            self.infer_expr(cxt, new_decl)?
                        }
                        None => {
                            let result = self.infer_expr(cxt, decl.clone())?;
                            // Cache the checked Pi chain + body only when both
                            // are fully meta-free: a cached term referencing
                            // per-call metas would use stale indices on a later
                            // call with the same receiver-type key.
                            if let Tm::Let(_, a_checked, t_checked, _) = result.0.as_ref() {
                                let clean = a_checked.no_metas(self, &cxt.decl, cxt.lvl).is_none()
                                    && t_checked.no_metas(self, &cxt.decl, cxt.lvl).is_none();
                                if clean {
                                    let va = self.eval(&cxt.decl, &cxt.env, a_checked);
                                    self.trait_method_cache.insert(key.clone(), (a_checked.clone(), va, t_checked.clone()));
                                }
                            }
                            result
                        }
                    },
                    None => self.infer_expr(cxt, decl.clone())?,
                };
                self.hover_table.push((
                    t.to_span(),
                    *def_span,
                    crate::L13_namespace::cxt::HoverCxt { lvl: cxt.lvl, locals: cxt.locals.clone(), decl: cxt.decl.clone() },
                    result.1.clone(),
                ));
                Ok(result)
            } else {
                // The member did not resolve — this is a completion site: the
                // `p.` empty-member state or a partially-typed prefix `p.z`.
                // Collect trait methods satisfiable by typ_raw plus
                // namespace-registered methods (inherent impls) whose receiver
                // type matches.  Only the failure path collects, so successful
                // calls like `a + b` or `x.not` pay no probing cost.
                let completions: Vec<_> = self.trait_definition.iter()
                    .filter(|(x, (_, _, _, _))| self.trait_solver.can_satisfy(x, &typ_raw))
                    .flat_map(|x| x.1.3.clone().into_iter().map(move |m| (x.0.clone(), m)))
                    .collect();
                for (_, method_decl) in &completions {
                    self.completion_table.push((receiver_span, method_decl.0.data.clone()));
                }
                // Namespace methods: the same receiver-type probe as the
                // resolution path above, but without the typed-name filter.
                // The probe may solve metas whose solutions reference the
                // temporary metas created here, so roll back the whole meta /
                // trait_metas state after each entry.
                {
                    // Lazy snapshot: only taken when at least one entry survives
                    // the pre-filter and actually runs a probe.
                    let mut meta_snapshot: Option<Vec<_>> = None;
                    let mut trait_metas_snapshot: Option<Vec<_>> = None;
                    for ns_entry in cxt.namespace.iter() {
                        // Pre-filter: skip entries whose trait has no instance
                        // for this Self type (same rule as the resolution path).
                        if let Some(ref head) = typ_raw_head {
                            if let Val::Pi(_, Icit::Impl, dom, _) = ns_entry.0.as_ref() {
                                if let Val::Sum(trait_name, _, _, true) = dom.as_ref() {
                                    if !self.trait_solver.can_satisfy(&trait_name.data, &typ_raw) {
                                        continue;
                                    }
                                }
                            }
                        }
                        let meta_snapshot = meta_snapshot.get_or_insert_with(|| self.meta.clone());
                        let trait_metas_snapshot = trait_metas_snapshot.get_or_insert_with(|| self.trait_metas.clone());
                        let mut check_typ = ns_entry.0.clone();
                        while let Val::Pi(_, Icit::Impl, dom, cod) = check_typ.as_ref() {
                            let u = self.fresh_meta(&cxt, dom.clone(), t_span);
                            let u = self.eval(&cxt.decl, &cxt.env, &u);
                            check_typ = self.closure_apply(&cxt.decl, cod, u);
                        }
                        if self.unify_catch(cxt, &check_typ, &typ_raw, t_span).is_ok() {
                            for method_name in ns_entry.1.iter() {
                                self.completion_table.push((receiver_span, method_name.clone()));
                            }
                        }
                        self.meta = meta_snapshot.clone();
                        self.trait_metas = trait_metas_snapshot.clone();
                    }
                }
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

/// Deterministic structural key for a type value, used to key the
/// trait-method Pi-chain cache.  Returns `None` for types that are not
/// cacheable: per-call metas (`Flex`), open/context-dependent types (`Rigid`,
/// `Decl` spines, lambdas/functions), or structures deeper than `depth` (a
/// runaway Nat literal).  Equal closed types (e.g. `UInt[8]` built at
/// different sites) produce the same key, so the cache hits across separate
/// elaborations — unlike a pointer key.
fn val_cache_key(v: &Val, depth: u32) -> Option<SmolStr> {
    if depth > 64 {
        return None;
    }
    match v {
        Val::U(n) => Some(SmolStr::new(format!("u{}", n))),
        Val::LiteralType => Some(SmolStr::new("lt")),
        Val::LiteralIntro(s) => Some(SmolStr::new(format!("l:{}", s.data))),
        Val::Sum(name, params, _, _) => {
            let mut s = String::from(name.data.as_str());
            s.push('(');
            for (i, (_, pv, _, _)) in params.iter().enumerate() {
                if i > 0 {
                    s.push(',');
                }
                s.push_str(&val_cache_key(pv, depth + 1)?);
            }
            s.push(')');
            Some(SmolStr::new(s))
        }
        Val::SumCase { index, datas, .. } => {
            let mut s = format!("sc{}({}", index, datas.len());
            for (_, dv, _) in datas.iter() {
                s.push(',');
                s.push_str(&val_cache_key(dv, depth + 1)?);
            }
            s.push(')');
            Some(SmolStr::new(s))
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

/// Split a dotted path at its first segment: `"a.b.c"` → Some(("a", "b.c")).
/// Used to resolve the head of a qualified access through `import_map`
/// (`Tree.leaf` → `Tree` is an alias for `mylib.Tree`).
fn split_first_segment(path: &SmolStr) -> Option<(SmolStr, SmolStr)> {
    let s = path.as_str();
    let dot = s.find('.')?;
    Some((SmolStr::new(&s[..dot]), SmolStr::new(&s[dot + 1..])))
}
/// True when `name` starts with an operator character, i.e. it is an
/// operator method (`+`, `<=`, `:=`, ...) rather than an identifier method.
fn is_operator_method_name(name: &str) -> bool {
    name.chars().next().map(super::is_operator_char).unwrap_or(false)
}

