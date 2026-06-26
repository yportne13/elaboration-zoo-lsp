use std::{
    collections::{BTreeSet, HashMap, HashSet},
};

use smol_str::SmolStr;

use crate::parser_lib::{Span, ToSpan};

use super::{
    Env, Error, Infer, Tm, Val,
    cxt::Cxt, Rc, Decl,
    empty_span, Either,
    parser::syntax::{Pattern, Raw, Icit},
    PatternDetail,
};

type Var = i32;

type Constructor = Span<SmolStr>;

#[derive(Debug, Clone)]
pub enum Warning {
    Unreachable(Raw),
    Unmatched(Pattern),
}

impl std::fmt::Display for Warning {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Warning::Unreachable(body) => write!(f, "unreachable pattern: {}", body),
            Warning::Unmatched(pat) => write!(f, "non-exhaustive pattern: `{}` not covered", pat),
        }
    }
}

#[derive(Debug, Clone)]
struct PatConstructor {
    data: Vec<(usize, Vec<PatternDetail>)>,
}

impl PatConstructor {
    fn new() -> Self {
        PatConstructor { data: vec![(2, vec![])] }
    }

    fn clean(mut self) -> Self {
        // Never pop the root level (data[0]), matching the guard in to_raw()
        while self.data.len() > 1 && self.data.last().map(|(num, x)| x.len() == *num) == Some(true) {
            let (_, t) = self.data.pop().unwrap();
            self.data
                .last_mut()
                .map(|x| {
                    x.1.last_mut()
                        .map(|x| match x {
                            PatternDetail::Con(_, x) => {*x = t;},
                            _ => {},
                        })
                });
        }
        self
    }

    fn push(self, detail: PatternDetail) -> Self {
        let mut ret = self.clean();
        ret.data.last_mut().map(|(_, x)| x.push(detail));
        ret
    }

    fn new_level(mut self, index: usize) -> Self {
        self.data.push((index, vec![]));
        self
    }

    /// Convert the accumulated pattern-constructor tree to a `Raw` expression.
    ///
    /// This differs from `Pattern::to_raw()` because it also includes the
    /// **implicit** parameters that were discovered during matching (e.g. the
    /// `l` in `cons[l](x, xs)` or the `n` in `fsucc[n](i)`).  Those were
    /// pushed as `PatternDetail::Any` entries and get emitted as Implicit
    /// `Raw::App` arguments, so that `check_pm_final`'s inference reuses the
    /// already-bound Rigids instead of creating independent fresh metas.
    fn to_raw(&self) -> Raw {
        // Collapse inner levels to embed children into parent Con nodes,
        // but NEVER pop the root level (data[0]) so we always have something
        // to convert.
        let mut pat = self.clone();
        while pat.data.len() > 1 {
            if let Some(true) = pat.data.last().map(|(num, x)| x.len() == *num) {
                let (_, t) = pat.data.pop().unwrap();
                pat.data.last_mut().map(|x| {
                    x.1.last_mut().map(|x| match x {
                        PatternDetail::Con(_, x) => { *x = t; },
                        _ => {},
                    })
                });
            } else {
                break;
            }
        }
        match pat.root_detail() {
            Some(d) => Self::detail_to_raw(d),
            None => Raw::Hole(empty_span(())),
        }
    }

    /// Extract the root constructor detail from the fully-cleaned stack.
    fn root_detail(&self) -> Option<&PatternDetail> {
        // The stack bottoms out at index 0 with the root Con.
        // If the stack is empty (all levels cleaned), the caller should not
        // have called us — but if it does, return None.
        if self.data.is_empty() || self.data[0].1.is_empty() {
            return None;
        }
        Some(&self.data[0].1[0])
    }

    fn detail_to_raw(d: &PatternDetail) -> Raw {
        match d {
            PatternDetail::Con(name, subs) => {
                // Each sub-detail becomes an argument to `name`.
                //   Any(Impl) → named implicit [pi_param=var]
                //   Any(Expl) → expl arg (handles the not-necessary case)
                //   Bind → expl,  Con → expl
                subs.iter()
                    .fold(Raw::Var(name.clone()), |acc, sub| {
                        let icit = match sub {
                            PatternDetail::Any(name, Icit::Impl) => {
                                if name.data.is_empty() {
                                    // Unnamed implicit → let elaborator auto-fill.
                                    Either::Icit(Icit::Impl)
                                } else {
                                    // Named implicit: [pi_param=var] so insert_go
                                    // auto-fills preceding Impl params and only
                                    // binds this one by name.
                                    Either::Name(name.clone().map(|s| SmolStr::new(&s[1..])))
                                }
                            }
                            PatternDetail::Any(_, Icit::Expl) => Either::Icit(Icit::Expl),
                            PatternDetail::Bind(_) => Either::Icit(Icit::Expl),
                            PatternDetail::Con(_, _) => Either::Icit(Icit::Expl),
                        };
                        Raw::App(Box::new(acc), Box::new(Self::detail_to_raw(sub)), icit)
                    })
            }
            PatternDetail::Any(name, _) | PatternDetail::Bind(name) => {
                if name.data.is_empty() {
                    Raw::Hole(empty_span(()))
                } else {
                    Raw::Var(name.clone())
                }
            }
        }
    }
}

pub struct Compiler {
    warnings: Vec<Warning>,
    reachable: HashMap<usize, ()>,
    checked_ret: HashSet<Raw>,
    pub pats: Vec<(PatternDetail, Rc<Tm>)>,
    ret_type: Rc<Val>,
    /// Collected type errors from branch bodies; all branches are checked
    /// even if some fail, so we can report every error at once.
    errors: Vec<Error>,
}

impl Compiler {
    pub fn new(ret_type: Rc<Val>) -> Self {
        Compiler {
            warnings: Vec::new(),
            reachable: HashMap::new(),
            checked_ret: HashSet::new(),
            pats: Vec::new(),
            ret_type,
            errors: Vec::new(),
        }
    }

    fn fill_context(ctx: &MatchContext, pat: &Pattern) -> Pattern {
        match ctx {
            MatchContext::Outermost => pat.clone(),
            MatchContext::InCons {
                parent,
                constr,
                icit,
                before,
                after,
            } => {
                let mut new_before = before.clone();
                new_before.reverse();
                new_before.push(pat.clone());
                new_before.extend(after.clone());
                Self::fill_context(parent, &Pattern::Con(constr.clone(), new_before, Either::Icit(*icit)))
            }
        }
    }

    fn next_hole(&self, ctx: &MatchContext, pat: &Pattern) -> MatchContext {
        match ctx {
            MatchContext::Outermost => MatchContext::Outermost,
            MatchContext::InCons {
                parent,
                constr,
                icit,
                before,
                after,
            } => match after[..] {
                [] => self.next_hole(parent, &Pattern::Con(constr.clone(), before.clone(), Either::Icit(*icit))),
                _ => MatchContext::InCons {
                    parent: parent.clone(),
                    constr: constr.clone(),
                    icit: *icit,
                    before: vec![pat.clone()],
                    after: after[1..].to_vec(),
                },
            },
        }
    }

    fn filter_accessible_constrs<'a>(
        &mut self,
        infer: &mut Infer,
        cxt: &Cxt,
        typ: &Rc<Val>, // The specific type of the matched term, e.g., Val for `Vec (Succ n)`
        all_constrs: &'a [Constructor],
    ) -> Result<
        Vec<(&'a Constructor, Vec<(Span<SmolStr>, Rc<Val>, Icit)>, Cxt)>,
        Error,
    > {
        let mut accessible = Vec::new();
        let before_fac = infer.meta_len();

        let typ = infer.force(&cxt.decl, typ);
        let forced_type = match typ.as_ref() {
            Val::Sum(..) => typ,
            _ => {
                for constr_def in all_constrs {
                    accessible.push((constr_def, vec![], cxt.clone()));
                }
                infer.meta.truncate(before_fac);
                return Ok(accessible)
            }
        };

        // Get the Sum type name for qualified constructor access
        let sum_name = match forced_type.as_ref() {
            Val::Sum(name, ..) => name.data.clone(),
            _ => SmolStr::new(""),
        };

        // Fast path: sum types without explicit (index) parameters have all
        // constructors always accessible (e.g. Expr, Option, Bool).
        // Only Vec-like indexed types (e.g. Vec[A](len: Nat)) need the full
        // GADT-style reachability check.
        let has_indices = match forced_type.as_ref() {
            Val::Sum(_, params, ..) => params.iter().any(|p| p.3 == Icit::Expl),
            _ => false,
        };
        if !has_indices {
            for constr_def in all_constrs {
                accessible.push((constr_def, vec![], cxt.clone()));
            }
            infer.meta.truncate(before_fac);
            return Ok(accessible);
        }

        for constr_def @ constr_name in all_constrs {
            // We create a temporary, throwaway inference state for the unification check
            // to avoid polluting the main inference state with temporary metavariables.

            // 1. Create fresh metavariables for the constructor's own arguments.
            //    We need their types first, which are given as raw syntax.
            // Use qualified name TypeName.constructor for lookup
            let mut to_check = if sum_name.is_empty() {
                Raw::Var(constr_name.clone())
            } else {
                Raw::Obj(Box::new(Raw::Var(empty_span(sum_name.clone()))), Some(constr_name.clone()))
            };
            let mut params = vec![];
            let mut cxt = cxt.clone();
            loop {
                let (_, typ) = infer.infer_expr(&cxt, to_check.clone())?;
                match typ.as_ref() {
                    Val::Pi(name, icit, ty, _) => {
                        if *icit == Icit::Expl { // Only explicit args matter for the structure 
                            params.push((name.clone(), ty.clone(), *icit));
                        }
                        to_check = Raw::App(Box::new(to_check), Box::new(Raw::Hole(name.to_span())), super::Either::Icit(*icit));
                        cxt = cxt.bind(name.clone(), infer.quote(&cxt.decl, cxt.lvl, ty), ty.clone());
                    },
                    _ => {break;}
                }
            }
            /*for (_, _, icit) in constr_arg_tys_raw {
                if *icit == Icit::Expl { // Only explicit args matter for the structure 
                    to_check = Raw::App(Box::new(to_check), Box::new(Raw::Hole), super::Either::Icit(Icit::Expl));
                }
            }*/

            //let mut temp_infer = infer.clone();
            // 4. Try to unify it with the type of the matched term.
            if let Ok((_, cxt)) = infer.check_pm(&cxt, to_check.clone(), forced_type.clone()) {
                // If unification succeeds, the constructor is accessible.
                accessible.push((constr_def, params, cxt));
            }
        }

        infer.meta.truncate(before_fac);
        Ok(accessible)
    }

    fn compile_aux(
        &mut self,
        infer: &mut Infer,
        heads: &[(Rc<Val>, Span<SmolStr>, Icit)],
        arms: &[(MatchArm, usize, Cxt, Cxt, Raw, Rc<Val>, Rc<Val>, PatConstructor)],
        context: &MatchContext,
    ) -> Result<bool, Error> {
        match heads {
            [] => match arms {
                [(arm, idx, cxt, _, raw, target_typ, ori, patcon), ..] if arm.pats.is_empty() || arm.pats.get(0).map(|x| matches!(x, Pattern::Any(Span { data: false, .. }, _))) == Some(true) => {
                    let patcon_raw = patcon.clone().to_raw();
                    // Try patcon_raw first (includes GADT implicits);
                    // fall back to the original `raw` on failure.
                    let result = infer.check_pm_final(cxt, patcon_raw, target_typ.clone(), ori.clone());
                    let (_, cxt) = match result {
                        Ok(x) => x,
                        Err(_) => match infer.check_pm_final(cxt, raw.clone(), target_typ.clone(), ori.clone()) {
                            Ok(x) => x,
                            Err(e) => {
                                self.errors.push(e);
                                return Ok(false);
                            }
                        }
                    };
                    self.reachable.insert(*idx, ());
                    if self.checked_ret.contains(raw) {
                        return Ok(true)
                    }
                    //println!("prepare to check {:?}", arm.body);
                    //println!(" == {}", super::pretty::pretty_tm(0, cxt_global.names(), &infer.quote(cxt_global.lvl, self.ret_type.clone())));
                    let ret_type = match self.ret_type.as_ref() {
                        Val::Flex(_, _) => &self.ret_type,
                        _ => {
                            let ret_type = infer.quote(&cxt.decl, cxt.lvl, &self.ret_type);
                            &infer.eval(&cxt.decl, &cxt.env, &ret_type)
                        },
                    };
                    let ret = match infer.check::<false>(&cxt, arm.body.0.clone(), ret_type) {
                        Ok(ret) => ret,
                        Err(e) => {
                            // Collect the type error but continue checking other branches
                            self.errors.push(e);
                            self.checked_ret.insert(raw.clone());
                            return Ok(false);
                        }
                    };
                    self.checked_ret.insert(raw.clone());
                    let patcon = patcon.clone().clean();
                    //TODO:check patcon is clean
                    if !patcon.data.is_empty() {
                        self.pats.push((patcon.data[0].1[0].clone(), ret));
                    }
                    Ok(true)
                },
                [arm, ..] => Err(Error(match &arm.0.pats[0] {
                    Pattern::Any(span, _) => span.map(|_| "invalid pattern".to_owned()),
                    Pattern::Con(span, _, _) => span.clone().map(|x| format!("invalid pattern {}", x)),
                }, vec![])),
                [] => Ok(false)
            },
            [(typ, head_name, icit), heads_rest @ ..] => {
                let not_necessary = arms
                    .iter()
                    .all(|arm| matches!(arm.0.pats[..], [Pattern::Any(_, ref i), ..] if &i.to_icit() == icit));
                if not_necessary {
                    let new_context = self.next_hole(context, &Pattern::Any(empty_span(true), Either::Icit(*icit)));
                    let new_arms = arms
                        .iter()
                        .map(|arm| {
                            let cxt = &arm.2;
                            (
                                MatchArm {
                                    pats: arm.0.pats.get(1..).map(|x| x.to_vec()).unwrap_or(vec![]),
                                    body: arm.0.body.clone(),
                                },
                                arm.1,
                                if let Some(Pattern::Any(Span { data: false, .. }, _)) = arm.0.pats.first() {
                                    cxt.clone()
                                } else {
                                    cxt.bind(head_name.clone().map(|x| SmolStr::new(format!("_{}", x))), infer.quote(&cxt.decl, cxt.lvl, typ), typ.clone())
                                },
                                arm.3.bind(head_name.clone().map(|x| SmolStr::new(format!("_{}", x))), infer.quote(&arm.3.decl, arm.3.lvl, typ), typ.clone()),
                                arm.4.clone(),
                                arm.5.clone(),
                                arm.6.clone(),
                                if let Some(Pattern::Any(Span { data: false, .. }, _)) = arm.0.pats.first() {
                                    if *icit == Icit::Impl {
                                        arm.7.clone().clean().push(PatternDetail::Any(head_name.clone().map(|x| SmolStr::new(format!("_{}", x))), *icit))
                                    } else {
                                        arm.7.clone().clean().push(PatternDetail::Any(empty_span(SmolStr::new("")), *icit))
                                    }
                                } else {
                                    arm.7.clone().clean().push(PatternDetail::Any(head_name.clone().map(|x| SmolStr::new(format!("_{}", x))), *icit))
                                },
                            )
                        })
                        .collect::<Vec<_>>();
                    self.compile_aux(infer, heads_rest, &new_arms, &new_context)
                } else {
                    //println!(" -- {}", infer.meta.len());
                    //println!("  {:?}", typ);
                    //let typ = infer.force(typ);
                    let (param, constrs) = match typ.as_ref() {
                        Val::Sum(_, param, cases, _) => (param.clone(), cases.clone()),
                        _ => (Rc::new(vec![]), Rc::new(vec![empty_span(SmolStr::new("$any$"))])),
                    };

                    let constrs_name = constrs
                        .iter()
                        .map(|x| x.data.clone())
                        .collect::<BTreeSet<_>>();

                    let decision_tree_branches = constrs
                        .iter()
                        .map(|constr| {
                            // Lifting: compute accessibility once per constr,
                            // not once per (constr, arm) pair.
                            // Result depends only on typ (type indices), not on
                            // per-arm context — same for all arms.
                            let constr_accessible = if constr.data == "$any$" {
                                true
                            } else {
                                arms.first()
                                    .and_then(|(_, _, _, cxt_for_filter, _, _, _, _)| {
                                        self.filter_accessible_constrs(
                                            infer,
                                            cxt_for_filter,
                                            typ,
                                            &constrs[..],
                                        )
                                        .ok()
                                    })
                                    .map(|accessible_constrs| {
                                        accessible_constrs.into_iter().any(|x| x.0 == constr)
                                    })
                                    .unwrap_or(false)
                            };

                            let remaining_arms = arms
                                .iter()
                                .filter_map(|(arm, idx, cxt, cxt_for_filter, raw, target_typ, ori, patcon)| {
                                    let mut new_heads = vec![];
                                    if !constr_accessible {
                                        return Some(None);
                                    }
                                    if constr.data != "$any$" {

                                        // Use qualified name TypeName.constructor for lookup
                                        let sum_name = match typ.as_ref() {
                                            Val::Sum(name, ..) => name.data.clone(),
                                            _ => SmolStr::new(""),
                                        };
                                        let constr_raw = if sum_name.is_empty() {
                                            Raw::Var(constr.clone())
                                        } else {
                                            Raw::Obj(Box::new(Raw::Var(empty_span(sum_name))), Some(constr.clone()))
                                        };
                                        let (_, typ) = infer.infer_expr(cxt_for_filter, constr_raw).ok()?;
                                        let mut param = param.iter().filter(|x| x.3 == Icit::Impl).cloned().collect::<Vec<_>>();
                                        param.reverse();
                                        let mut typ = typ;
                                        while let Val::Pi(name, icit, ty, closure) = typ.as_ref() {
                                            if !param.is_empty() {
                                                let val = param.pop()
                                                    .map(|x| x.1)
                                                    .unwrap_or(Val::U(0).into());
                                                typ = infer.closure_apply(&cxt_for_filter.decl, closure, val);
                                            } else {
                                                new_heads.push((ty.clone(), name.clone(), *icit));
                                                typ = infer.closure_apply(&cxt_for_filter.decl, closure, Val::vvar(cxt.lvl + new_heads.len() as u32 - 1).into());
                                            }
                                        }
                                    }
                                    let new_heads_len = new_heads.len();
                                    match &arm.pats[..] {
                                        [Pattern::Any(x, i), ..] if &i.to_icit() == icit => Some(Some((
                                            MatchArm {
                                                pats: [
                                                    new_heads
                                                        .iter()
                                                        .map(|n| Pattern::Any(x.to_span().map(|_| false), Either::Icit(n.2)))
                                                        .collect::<Vec<_>>(),
                                                    arm.pats[1..].to_vec(),
                                                ].concat(),
                                                body: arm.body.clone(),
                                            },
                                            *idx,
                                            if !x.data {
                                                cxt.clone()
                                            } else {
                                                cxt.bind(head_name.clone().map(|x| SmolStr::new(format!("_{}", x))), infer.quote(&cxt.decl, cxt.lvl, typ), typ.clone())
                                            },
                                            cxt_for_filter.bind(head_name.clone().map(|x| SmolStr::new(format!("_{}", x))), infer.quote(&cxt_for_filter.decl, cxt_for_filter.lvl, typ), typ.clone()),
                                            new_heads,
                                            raw.clone(),
                                            target_typ.clone(),
                                            ori.clone(),
                                            if !x.data {
                                                patcon.clone().clean().push(PatternDetail::Any(empty_span(SmolStr::new("")), *icit))
                                            } else {
                                                patcon.clone().clean().push(PatternDetail::Any(head_name.clone().map(|x| SmolStr::new(format!("_{}", x))), *icit))
                                            },
                                            false,
                                        ))),
                                        [Pattern::Con(constr_, item_pats, i), ..]
                                            if &i.to_icit() == icit && (constr.data == "$any$" || !constrs_name.contains(&constr_.data)) =>
                                        {
                                            Some(Some((
                                                MatchArm {
                                                    pats: [
                                                        new_heads
                                                            .iter()
                                                            .map(|n| Pattern::Any(constr_.to_span().map(|_| false), Either::Icit(n.2)))
                                                            .collect::<Vec<_>>(),
                                                        arm.pats[1..].to_vec(),
                                                    ].concat(),
                                                    body: arm.body.clone(),
                                                },
                                                *idx,
                                                cxt.bind(constr_.clone(), infer.quote(&cxt.decl, cxt.lvl, typ), typ.clone()),
                                                cxt_for_filter.bind(constr_.clone(), infer.quote(&cxt_for_filter.decl, cxt_for_filter.lvl, typ), typ.clone()),
                                                new_heads,
                                                raw.clone(),
                                                target_typ.clone(),
                                                ori.clone(),
                                                patcon.clone().clean().push(PatternDetail::Bind(constr_.clone())),
                                                false,
                                            )))
                                        }
                                        [Pattern::Con(constr_, item_pats, i), ..] if &i.to_icit() == icit && (constr_ == constr) => {
                                            Some(Some((
                                                MatchArm {
                                                    pats: item_pats
                                                        .iter()
                                                        .chain(&arm.pats[1..])
                                                        .cloned()
                                                        .collect(),
                                                    body: arm.body.clone(),
                                                },
                                                *idx,
                                                cxt.clone(),
                                                cxt_for_filter.clone(),
                                                new_heads,
                                                raw.clone(),
                                                target_typ.clone(),
                                                ori.clone(),
                                                patcon.clone().clean().push(PatternDetail::Con(constr_.clone(), vec![])).new_level(new_heads_len),
                                                false,
                                            )))
                                        }
                                        _ => if *icit == Icit::Impl {
                                            Some(Some((
                                                MatchArm {
                                                    pats: arm.pats.clone(),
                                                    body: arm.body.clone(),
                                                },
                                                *idx,
                                                cxt.bind(head_name.clone().map(|x| SmolStr::new(format!("_{}", x))), infer.quote(&cxt.decl, cxt.lvl, typ), typ.clone()),
                                                cxt_for_filter.bind(head_name.clone().map(|x| SmolStr::new(format!("_{}", x))), infer.quote(&cxt_for_filter.decl, cxt_for_filter.lvl, typ), typ.clone()),
                                                vec![],
                                                raw.clone(),
                                                target_typ.clone(),
                                                ori.clone(),
                                                patcon.clone().clean().push(PatternDetail::Any(head_name.clone().map(|x| SmolStr::new(format!("_{}", x))), Icit::Impl)),
                                                true,
                                            )))
                                        } else {None},
                                    }
                                })
                                .collect::<Vec<_>>();

                            let valid_tree = if remaining_arms.is_empty() {
                                let unmatched = Self::fill_context(
                                    context,
                                    &Pattern::Con(
                                        constr.clone(),
                                        vec![],
                                        Either::Icit(*icit),
                                    ),
                                );
                                self.warnings.push(Warning::Unmatched(unmatched));
                                false
                            } else if remaining_arms
                                        .iter()
                                        .flatten()
                                        .map(|_| ())
                                        .collect::<Vec<_>>().is_empty() {
                                return Ok(false)
                            } else {
                                let new_heads = remaining_arms
                                    .first()
                                    .and_then(|x| x.as_ref().map(|y| y.4.clone()))
                                    .unwrap_or(vec![]);
                                let is_impl = remaining_arms
                                    .first()
                                    .and_then(|x| x.as_ref().map(|y| y.9))
                                    .unwrap_or(false);
                                let context_ = if new_heads.is_empty() {
                                    if heads_rest.is_empty() || is_impl {
                                        context.clone()
                                    } else {
                                        self.next_hole(
                                            context,
                                            &Pattern::Con(constr.clone(), vec![], Either::Icit(*icit)),
                                        )
                                    }
                                } else {
                                    MatchContext::InCons {
                                        parent: context.clone().into(),
                                        constr: constr.clone(),
                                        icit: *icit,
                                        before: vec![],
                                        after: vec![
                                            Pattern::Any(empty_span(true), Either::Icit(*icit));
                                            new_heads.len() - 1
                                        ],
                                    }
                                };
                                self.compile_aux(
                                    infer,
                                    &new_heads
                                        .iter()
                                        .chain(heads_rest)
                                        .cloned()
                                        .collect::<Vec<_>>(),
                                    &remaining_arms
                                        .into_iter()
                                        .flatten()
                                        .map(|x| (x.0, x.1, x.2, x.3, x.5, x.6, x.7, x.8))
                                        .collect::<Vec<_>>(),
                                    &context_,
                                )?
                            };

                            Ok(valid_tree)
                        })
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter()
                        .any(|x| x);

                    Ok(decision_tree_branches)
                }
            }
        }
    }

	    pub fn compile(
	        &mut self,
	        infer: &mut Infer,
	        typ: Rc<Val>,
	        arms: &[(Pattern, Raw)],
	        cxt: &Cxt,
	        target_val: Rc<Val>,
	    ) -> Result<Vec<Warning>, Vec<Error>> {
	        self.warnings = Vec::new();
	        self.reachable = HashMap::new();
	        self.errors = Vec::new();
	        let typ = infer.force(&cxt.decl, &typ);
	        // 收集所有编译阶段的错误，而不是遇到第一个就停止
	        if let Err(e) = self.compile_aux(
	            infer,
	            &[(typ.clone(), empty_span(SmolStr::new("")), Icit::Expl)],
	            &arms
	                .iter()
	                .enumerate()
	                .map(|(idx, (pat, body))| {
	                    (
	                        MatchArm {
	                            pats: vec![pat.clone()],
	                            body: (body.clone(), idx),
	                        },
	                        idx,
	                        cxt.clone(),
	                        cxt.clone(),
	                        pat.to_raw(),
	                        typ.clone(),
	                        target_val.clone(),
	                        PatConstructor::new(),
	                    )
	                })
	                .collect::<Vec<_>>(),
	            &MatchContext::Outermost,
	        ) {
	            self.errors.push(e);
	        }

	        // 检查是否有不可达分支
	        let unreachable = arms
	            .iter()
	            .enumerate()
	            .filter_map(|(idx, (_, body))| {
	                if !self.reachable.contains_key(&idx) {
	                    Some(Warning::Unreachable(body.clone()))
	                } else {
	                    None
	                }
	            })
	            .collect::<Vec<_>>();

	        let warnings: Vec<Warning> = unreachable
	            .into_iter()
	            .chain(self.warnings.clone())
	            .collect();

	        if !self.errors.is_empty() {
	            Err(std::mem::take(&mut self.errors))
	        } else {
	            Ok(warnings)
	        }
	    }

    pub fn eval_aux(
        infer: &Infer,
        heads: &Rc<Val>,
        decl: &Decl,
        cxt: &Env,
        arms: &[(PatternDetail, Rc<Tm>)],
    ) -> Option<(Rc<Tm>, Env)> {
        let head = infer.force(decl, heads);
        let (case_name, params) = match head.as_ref() {
            Val::SumCase {
                is_trait: _,
                typ: _,
                case_name,
                datas,
            } => (case_name, datas.clone()),
            //_ => panic!("by now only can match a sum type, but get {:?}", heads),
            _ => (&empty_span(SmolStr::new("$unknown$")), Rc::new(vec![])),
        };

        arms.iter()
            .filter_map(|(pattern, body)| match pattern {
                PatternDetail::Con(constr_, item_pats) if constr_ == case_name => {
                    params.iter()
                        //.filter(|x| x.2 == Icit::Expl)
                        .map(|x| &x.1)
                        .zip(item_pats.iter())
                        .try_fold(
                            (body.clone(), cxt.clone()),
                            |(body, cxt), (param, pat): (&Rc<Val>, &PatternDetail)| {
                                Self::eval_aux(infer, param, decl, &cxt, &[(pat.clone(), body)])
                            },
                        )
                }
                _ => None,
            })
            .next()
            .or_else(|| {
                arms.iter()
                    .filter_map(|(pattern, body)| match pattern {
                        PatternDetail::Any(_, _) => Some((body.clone(), cxt.prepend(heads.clone()))),
                        PatternDetail::Bind(_) => Some((body.clone(), cxt.prepend(heads.clone()))),
                        PatternDetail::Con(..) => None,
                    })
                    .next()
            })
    }
}

#[derive(Debug, Clone)]
enum MatchContext {
    Outermost,
    InCons {
        parent: Rc<MatchContext>,
        constr: Constructor,
        icit: Icit,
        before: Vec<Pattern>,
        after: Vec<Pattern>,
    },
}

#[derive(Debug, Clone)]
struct MatchArm {
    pats: Vec<Pattern>,
    body: (Raw, usize),
}
