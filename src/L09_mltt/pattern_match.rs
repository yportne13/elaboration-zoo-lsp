use std::{
    collections::{BTreeSet, HashMap},
    rc::Rc,
};

use crate::parser_lib::{Span, ToSpan};

use super::{
    Env, Error, Infer, Tm, Val,
    cxt::Cxt,
    empty_span,
    parser::syntax::{Pattern, Raw, Icit},
    PatternDetail,
};

type Var = i32;

type MatchBody = (Tm, usize);
type TypeName = Span<String>;
type Constructor = Span<String>;

#[derive(Debug, Clone)]
pub enum DecisionTree {
    Fail,
    Leaf(MatchBody),
    Branch(
        TypeName,
        Var,
        Vec<(Constructor, Vec<Var>, Box<DecisionTree>)>,
    ),
}

impl DecisionTree {
    pub fn iter(&self) -> Box<dyn Iterator<Item = &MatchBody> + '_> {
        match self {
            DecisionTree::Fail => Box::new(std::iter::empty()),
            DecisionTree::Leaf(x) => Box::new(std::iter::once(x)),
            DecisionTree::Branch(_, _, items) => Box::new(items.iter().flat_map(|x| x.2.iter())),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Warning {
    Unreachable(Raw),
    Unmatched(Pattern),
}

pub struct Compiler {
    warnings: Vec<Warning>,
    reachable: HashMap<usize, ()>,
    seed: i32,
    ret_type: Val,
}

impl Compiler {
    pub fn new(ret_type: Val) -> Self {
        Compiler {
            warnings: Vec::new(),
            reachable: HashMap::new(),
            seed: 0,
            ret_type,
        }
    }

    fn fresh(&mut self) -> i32 {
        self.seed += 1;
        self.seed
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
                Self::fill_context(parent, &Pattern::Con(constr.clone(), new_before, *icit))
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
                [] => self.next_hole(parent, &Pattern::Con(constr.clone(), before.clone(), *icit)),
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
        typ: &Val, // The specific type of the matched term, e.g., Val for `Vec (Succ n)`
        all_constrs: &'a [Constructor],
    ) -> Result<
        Vec<(&'a Constructor, Vec<(Span<String>, Val, Icit)>, Cxt)>,
        Error,
    > {
        let mut accessible = Vec::new();

        let forced_type = match infer.force(typ.clone()) {
            x @ Val::Sum(..) => x,
            _ => {
                for constr_def in all_constrs {
                    accessible.push((constr_def, vec![], cxt.clone()));
                }
                return Ok(accessible)
            }
        };

        for constr_def @ constr_name in all_constrs {
            // We create a temporary, throwaway inference state for the unification check
            // to avoid polluting the main inference state with temporary metavariables.

            // 1. Create fresh metavariables for the constructor's own arguments.
            //    We need their types first, which are given as raw syntax.
            let mut to_check = Raw::Var(constr_name.clone());
            let mut params = vec![];
            let mut cxt = cxt.clone();
            loop {
                let (_, typ) = infer.infer_expr(&cxt, to_check.clone())?;
                match typ {
                    Val::Pi(name, icit, ty, _) => {
                        if icit == Icit::Expl { // Only explicit args matter for the structure 
                            params.push((name.clone(), *ty.clone(), icit));
                        }
                        to_check = Raw::App(Box::new(to_check), Box::new(Raw::Hole), super::Either::Icit(icit));
                        cxt = cxt.bind(name, infer.quote(cxt.lvl, *ty.clone()), *ty);
                    },
                    _ => {break;}
                }
            }
            /*for (_, _, icit) in constr_arg_tys_raw {
                if *icit == Icit::Expl { // Only explicit args matter for the structure 
                    to_check = Raw::App(Box::new(to_check), Box::new(Raw::Hole), super::Either::Icit(Icit::Expl));
                }
            }*/

            let mut temp_infer = infer.clone();
            // 4. Try to unify it with the type of the matched term.
            if let Ok((_, cxt)) = temp_infer.check_pm(&cxt, to_check.clone(), forced_type.clone()) {
                // If unification succeeds, the constructor is accessible.
                accessible.push((constr_def, params, cxt));
            }
        }

        Ok(accessible)
    }

    fn compile_aux(
        &mut self,
        infer: &mut Infer,
        heads: &[(Var, Val, Span<String>, Icit)],
        arms: &[(MatchArm, usize, Cxt, Raw, Val, Val)],
        context: &MatchContext,
    ) -> Result<Box<DecisionTree>, Error> {
        /*println!(
            " arms: {}\nheads: {}",
            arms
                .iter()
                .map(|x| format!("{:?}\n", x.0))
                .reduce(|a, b| a + &b)
                .unwrap_or("".to_owned()),
            heads
                .iter()
                .map(|x| format!("{:?}\n", x))
                .reduce(|a, b| a + &b)
                .unwrap_or("".to_owned()),
        );*/
        match heads {
            [] => match arms {
                [(arm, idx, cxt, raw, target_typ, ori), ..] if arm.pats.is_empty() => {
                    let (_, cxt) = infer.check_pm_final(cxt, raw.clone(), target_typ.clone(), ori.clone()).unwrap();
                    self.reachable.insert(*idx, ());
                    //println!("prepare to check {:?}", arm.body);
                    //println!(" == {}", super::pretty::pretty_tm(0, cxt_global.names(), &infer.quote(cxt_global.lvl, self.ret_type.clone())));
                    let ret_type = match self.ret_type.clone() {
                        t @ Val::Flex(_, _) => t,
                        ret_type => {
                            let ret_type = infer.quote(cxt.lvl, ret_type);
                            infer.eval(&cxt.env, ret_type)
                        },
                    };
                    let ret = infer.check(&cxt, arm.body.0.clone(), ret_type)?;
                    Ok(Box::new(DecisionTree::Leaf((ret, arm.body.1))))
                }
                _ => Ok(Box::new(DecisionTree::Fail)),
            },
            [(var, typ, head_name, icit), heads_rest @ ..] => {
                let not_necessary = arms
                    .iter()
                    .all(|arm| matches!(arm.0.pats[..], [Pattern::Any(_, i), ..] if &i == icit));

                if not_necessary {
                    let new_context = self.next_hole(context, &Pattern::Any(empty_span(()), *icit));
                    let new_arms = arms
                        .iter()
                        .map(|arm| {
                            (
                                MatchArm {
                                    pats: arm.0.pats.get(1..).map(|x| x.to_vec()).unwrap_or(vec![]),
                                    body: arm.0.body.clone(),
                                },
                                arm.1,
                                arm.2.clone(),
                                arm.3.clone(),
                                arm.4.clone(),
                                arm.5.clone(),
                            )
                        })
                        .collect::<Vec<_>>();
                    self.compile_aux(infer, heads_rest, &new_arms, &new_context)
                } else {
                    //println!(" -- {}", infer.meta.len());
                    //println!("  {:?}", typ);
                    let (typename, param, constrs) = match infer.force(typ.clone()) {
                        Val::Sum(span, param, cases) => (span, param, cases),
                        _ => {
                            //(empty_span("$unknown$".to_owned()), vec![], vec![(empty_span("$unknown$".to_owned()), Val::U)])
                            (empty_span("$unknown$".to_owned()), vec![], vec![empty_span("$any$".to_owned())])
                        }
                    };

                    let constrs_name = constrs
                        .iter()
                        .map(|x| x.data.clone())
                        .collect::<BTreeSet<_>>();

                    let decision_tree_branches = constrs
                        .iter()
                        .map(|constr| {
                            let remaining_arms = arms
                                .iter()
                                .filter_map(|(arm, idx, cxt, raw, target_typ, ori)| {
                                    let mut new_heads = vec![];
                                    if constr.data != "$any$" {
                                        let accessible_constrs = self.filter_accessible_constrs(
                                            infer,
                                            cxt,
                                            typ,
                                            &constrs,
                                        ).ok()?;
                                        if !accessible_constrs.into_iter().any(|x| x.0 == constr) {
                                            return Some(None);
                                        }

                                        let (_, typ) = infer.infer_expr(cxt, Raw::Var(constr.clone())).ok()?;
                                        let mut param = param.iter().filter(|x| x.3 == Icit::Impl).cloned().collect::<Vec<_>>();
                                        param.reverse();
                                        let mut typ = typ;
                                        while let Val::Pi(name, icit, ty, closure) = typ {
                                            if !param.is_empty() {
                                                let val = param.pop()
                                                    .map(|x| x.1)
                                                    .unwrap_or(Val::U(0));
                                                typ = infer.closure_apply(&closure, val);
                                            } else {
                                                new_heads.push((self.fresh(), *ty, name, icit));
                                                typ = infer.closure_apply(&closure, Val::vvar(cxt.lvl + new_heads.len() as u32 - 1));
                                            }
                                        }
                                    }
                                    match &arm.pats[..] {
                                        [Pattern::Any(x, i), ..] if i == icit => Some(Some((
                                            MatchArm {
                                                pats: new_heads.iter().map(|t| Pattern::Any(*x, t.3))
                                                    .chain(arm.pats[1..].iter().cloned())
                                                    .collect(),
                                                body: arm.body.clone(),
                                            },
                                            *idx,
                                            cxt.clone(),
                                            new_heads,
                                            raw.clone(),
                                            target_typ.clone(),
                                            ori.clone(),
                                            false,
                                        ))),
                                        [Pattern::Con(constr_, item_pats, i), ..]
                                            if i == icit && (constr.data == "$any$" || !constrs_name.contains(&constr_.data)) =>
                                        {
                                            Some(Some((
                                                MatchArm {
                                                    pats: new_heads.iter().map(|t| Pattern::Any(constr_.to_span(), t.3))
                                                    .chain(arm.pats[1..].iter().cloned())
                                                    .collect(),
                                                    body: arm.body.clone(),
                                                },
                                                *idx,
                                                cxt.bind(constr_.clone(), infer.quote(cxt.lvl, typ.clone()), typ.clone()),
                                                new_heads,
                                                raw.clone(),
                                                target_typ.clone(),
                                                ori.clone(),
                                                false,
                                            )))
                                        }
                                        [Pattern::Con(constr_, item_pats, i), ..] if i == icit && (constr_ == constr) => {
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
                                                new_heads,
                                                raw.clone(),
                                                target_typ.clone(),
                                                ori.clone(),
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
                                                cxt.bind(head_name.clone().map(|x| format!("_{}", x)), infer.quote(cxt.lvl, typ.clone()), typ.clone()),
                                                vec![],
                                                raw.clone(),
                                                target_typ.clone(),
                                                ori.clone(),
                                                true,
                                            )))
                                        } else {None},
                                    }
                                })
                                .collect::<Vec<_>>();

                            let mut new_heads_ret = vec![];
                            let subtree = if remaining_arms.is_empty() {
                                let unmatched = Self::fill_context(
                                    context,
                                    &Pattern::Con(
                                        constr.clone(),
                                        vec![Pattern::Any(empty_span(()), Icit::Expl); 999],
                                        *icit,
                                    ),
                                );
                                self.warnings.push(Warning::Unmatched(unmatched));
                                Box::new(DecisionTree::Fail)
                            } else if remaining_arms
                                        .iter()
                                        .flatten()
                                        .map(|_| ())
                                        .collect::<Vec<_>>().is_empty() {
                                return Ok(None)
                            } else {
                                let new_heads = remaining_arms
                                    .first()
                                    .and_then(|x| x.as_ref().map(|y| y.3.clone()))
                                    .unwrap_or(vec![]);
                                let is_impl = remaining_arms
                                    .first()
                                    .and_then(|x| x.as_ref().map(|y| y.7))
                                    .unwrap_or(false);
                                new_heads_ret = new_heads.clone();
                                let context_ = if new_heads.is_empty() {
                                    if heads_rest.is_empty() || is_impl {
                                        context.clone()
                                    } else {
                                        self.next_hole(
                                            context,
                                            &Pattern::Con(constr.clone(), vec![], *icit),
                                        )
                                    }
                                } else {
                                    MatchContext::InCons {
                                        parent: context.clone().into(),
                                        constr: constr.clone(),
                                        icit: *icit,
                                        before: vec![],
                                        after: vec![
                                            Pattern::Any(empty_span(()), *icit);
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
                                        .map(|x| (x.0, x.1, x.2, x.4, x.5, x.6))
                                        .collect::<Vec<_>>(),
                                    &context_,
                                )?
                            };

                            Ok(Some((
                                constr.clone(),
                                new_heads_ret.iter().map(|(var, _, _, _)| *var).collect(),
                                subtree,
                            )))
                        })
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter()
                        .flatten()
                        .collect();

                    Ok(Box::new(DecisionTree::Branch(
                        typename.clone(),
                        *var,
                        decision_tree_branches,
                    )))
                }
            }
        }
    }

    pub fn compile(
        &mut self,
        infer: &mut Infer,
        typ: Val,
        arms: &[(Pattern, Raw)],
        cxt: &Cxt,
        target_val: Val,
    ) -> Result<(Box<DecisionTree>, Vec<Warning>), Error> {
        self.warnings = Vec::new();
        self.reachable = HashMap::new();
        let tree = self.compile_aux(
            infer,
            &[(0, typ.clone(), empty_span("".to_owned()), Icit::Expl)],
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
                        pat.to_raw(),
                        typ.clone(),
                        target_val.clone(),
                    )
                })
                .collect::<Vec<_>>(),
            &MatchContext::Outermost,
        )?;

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

        Ok((
            tree,
            unreachable
                .into_iter()
                .chain(self.warnings.clone())
                .collect(),
        ))
    }

    pub fn eval_aux(
        infer: &Infer,
        heads: Val,
        cxt: &Env,
        arms: &[(PatternDetail, Tm)],
    ) -> Option<(Tm, Env)> {
        let (case_name, params, constrs_name) = match infer.force(heads.clone()) {
            Val::SumCase {
                typ,
                case_name,
                datas: params,
            } => (case_name, params, match *typ {
                Val::Sum(_, _, cases) => cases,
                _ => panic!("by now only can match a sum type, but get {:?}", heads),
            }),
            //_ => panic!("by now only can match a sum type, but get {:?}", heads),
            _ => (empty_span("$unknown$".to_owned()), vec![], vec![])
        };

        arms.iter()
            .filter_map(|(pattern, body)| match pattern {
                PatternDetail::Any(_) => Some((body.clone(), cxt.clone())),
                PatternDetail::Bind(_) => {
                    Some((body.clone(), cxt.prepend(heads.clone())))
                }
                PatternDetail::Con(constr_, item_pats) if !constrs_name.contains(&constr_) => {
                    /*if cxt.src_names.contains_key(&constr_.data) {
                        //return Err(Error(format!("match fail: {:?}", constr_)))
                        todo!()
                    } else */
                    {
                        //TODO: item_pats should be zero
                        Some((body.clone(), cxt.prepend(heads.clone())))
                    }
                }
                PatternDetail::Con(constr_, item_pats) if constr_ == &case_name => {
                    params.iter()
                        .filter(|x| x.2 == Icit::Expl)
                    .map(|x| &x.1)
                        .zip(item_pats.iter())
                        .try_fold(
                        (body.clone(), cxt.clone()),
                        |(body, cxt), (param, pat): (&Val, &PatternDetail)| {
                            Self::eval_aux(infer, param.clone(), &cxt, &[(pat.clone(), body)])
                        },
                    )
                }
                _ => None,
            })
            .next()
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
