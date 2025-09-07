use std::{
    collections::{BTreeSet, HashMap},
    rc::Rc,
};

use crate::{parser_lib::{Span, ToSpan}, L07a_depend_pm::{parser::syntax::Icit, Ix}};

use super::{
    Env, Error, Infer, Lvl, Tm, Val,
    cxt::Cxt,
    empty_span,
    parser::syntax::{Pattern, Raw},
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
                before,
                after,
            } => {
                let mut new_before = before.clone();
                new_before.reverse();
                new_before.push(pat.clone());
                new_before.extend(after.clone());
                Self::fill_context(parent, &Pattern::Con(constr.clone(), new_before))
            }
        }
    }

    fn next_hole(&self, ctx: &MatchContext, pat: &Pattern) -> MatchContext {
        match ctx {
            MatchContext::Outermost => MatchContext::Outermost,
            MatchContext::InCons {
                parent,
                constr,
                before,
                after,
            } => match after[..] {
                [] => self.next_hole(parent, &Pattern::Con(constr.clone(), before.clone())),
                _ => MatchContext::InCons {
                    parent: parent.clone(),
                    constr: constr.clone(),
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
        all_constrs: &'a [(
            Constructor,
            Vec<(Span<String>, Val, Icit)>, // Constructor argument types
            Vec<(Span<String>, Val)>, // Constructor return type arguments
        )],
    ) -> Result<
        Vec<(&'a (
            Constructor,
            Vec<(Span<String>, Val, Icit)>,
            Vec<(Span<String>, Val)>,
        ), Cxt)>,
        Error,
    > {
        let mut accessible = Vec::new();

        let forced_type = match infer.force(typ.clone()) {
            x @ Val::Sum(..) => x,
            _ => {
                for constr_def in all_constrs {
                    accessible.push((constr_def, cxt.clone()));
                }
                return Ok(accessible)
            }
        };

        for constr_def @ (constr_name, constr_arg_tys_raw, _) in all_constrs {
            // We create a temporary, throwaway inference state for the unification check
            // to avoid polluting the main inference state with temporary metavariables.
            let mut temp_infer = infer.clone();

            // 1. Create fresh metavariables for the constructor's own arguments.
            //    We need their types first, which are given as raw syntax.
            let mut to_check = Raw::Var(constr_name.clone());
            for (_, _, icit) in constr_arg_tys_raw {
                if *icit == Icit::Expl { // Only explicit args matter for the structure 
                    to_check = Raw::App(Box::new(to_check), Box::new(Raw::Hole), super::Either::Icit(Icit::Expl));
                }
            }

            // 4. Try to unify it with the type of the matched term.
            if let Ok((_, cxt)) = temp_infer.check_pm(cxt, to_check.clone(), forced_type.clone()) {
                // If unification succeeds, the constructor is accessible.
                accessible.push((constr_def, cxt));
            }
        }

        Ok(accessible)
    }

    fn compile_aux(
        &mut self,
        infer: &mut Infer,
        heads: &[(Var, Tm, Val)],
        arms: &[(MatchArm, usize, Cxt)],
        context: &MatchContext,
        cxt_global: &Cxt,
    ) -> Result<Box<DecisionTree>, Error> {
        match heads {
            [] => match arms {
                [(arm, idx, cxt), ..] if arm.pats.is_empty() => {
                    self.reachable.insert(*idx, ());
                    //println!("prepare to check {:?}", arm.body);
                    //println!(" == {}", super::pretty::pretty_tm(0, cxt_global.names(), &infer.quote(cxt_global.lvl, self.ret_type.clone())));
                    let ret = infer.check(cxt, arm.body.0.clone(), self.ret_type.clone())?;
                    Ok(Box::new(DecisionTree::Leaf((ret, arm.body.1))))
                }
                _ => panic!("impossible"),
            },
            [(var, tm, typ), heads_rest @ ..] => {
                let is_necessary = arms
                    .iter()
                    .any(|arm| matches!(arm.0.pats[..], [Pattern::Con(..), ..]));

                if !is_necessary {
                    let new_context = self.next_hole(context, &Pattern::Any(empty_span(())));
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
                            )
                        })
                        .collect::<Vec<_>>();
                    self.compile_aux(infer, heads_rest, &new_arms, &new_context, cxt_global)
                } else {
                    //println!(" -- {}", infer.meta.len());
                    //println!("  {:?}", typ);
                    let (typename, param, constrs) = match infer.force(typ.clone()) {
                        Val::Sum(span, param, cases) => (span, param, cases),
                        _ => {
                            (empty_span("$unknown$".to_owned()), vec![], vec![(empty_span("$unknown$".to_owned()), vec![], vec![])])
                        }
                    };
                    let cxt_global = param
                        .iter()
                        .filter(|x| x.3 == Icit::Impl)
                        .fold(cxt_global.clone(), |cxt, (x, a, b, _)| {
                            //cxt.define(x.clone(), infer.quote(cxt.lvl, a.clone()), a.clone(), Tm::Var(Ix(0)), Val::vvar(cxt.lvl))
                            cxt.define(x.clone(), infer.quote(cxt.lvl, a.clone()), a.clone(), infer.quote(cxt.lvl, b.clone()), b.clone())
                            //cxt.bind(x.clone(), infer.quote(cxt.lvl, a.clone()), a.clone())
                        });

                    let constrs_name = constrs
                        .iter()
                        .map(|x| x.0.data.clone())
                        .collect::<BTreeSet<_>>();

                    let accessible_constrs = self.filter_accessible_constrs(
                        infer,
                        &cxt_global,
                        typ,
                        &constrs,
                    )?;
                    /*cxt_global.env
                        .iter()
                        .for_each(|x|
                            println!(
                                "{x:?}\n  {}",
                                super::pretty_tm(0, cxt_global.names(), &infer.quote(cxt_global.lvl, x.clone())),
                            )
                        );
                    println!("----------------");*/

                    let decision_tree_branches = accessible_constrs
                        .iter()
                        .map(|((constr, item_typs, ret_bind), cxt_global)| {
                            /*cxt_global.env
                                .iter()
                                .for_each(|x|
                                    println!("{:?}", x)
                                );*/
                            let mut cxt_param = cxt_global.clone();//TODO: sum should be closure. use cxt in closure
                            let new_heads = item_typs
                                .iter()
                                .flat_map(|x| match x.2 {
                                    Icit::Impl => {
                                        let tm = infer.quote(cxt_param.lvl, x.1.clone());
                                        cxt_param = cxt_param.bind(x.0.clone(), tm, x.1.clone());
                                        None
                                    }
                                    Icit::Expl => {
                                        let tm = infer.quote(cxt_param.lvl, x.1.clone());
                                        cxt_param = cxt_param.bind(x.0.clone(), tm.clone(), x.1.clone());
                                        Some((self.fresh(), tm, x.1.clone()))
                                    },
                                })
                                .collect::<Vec<_>>();
                            let remaining_arms = arms
                                .iter()
                                .map(|(arm, idx, cxt)| (
                                    arm,
                                    idx,
                                    param
                                        .iter()
                                        .filter(|x| x.3 == Icit::Impl)
                                        .fold(cxt.clone(), |cxt, (x, a, b, _)| {
                                            //cxt.define(x.clone(), infer.quote(cxt.lvl, a.clone()), a.clone(), Tm::Var(Ix(0)), Val::vvar(cxt.lvl))
                                            cxt.define(x.clone(), infer.quote(cxt.lvl, a.clone()), a.clone(), infer.quote(cxt.lvl, b.clone()), b.clone())
                                            //cxt.bind(x.clone(), infer.quote(cxt.lvl, a.clone()), a.clone())
                                        })
                                ))
                                .filter_map(|(arm, idx, cxt)| match &arm.pats[..] {
                                    [Pattern::Any(x), ..] => Some((
                                        MatchArm {
                                            pats: vec![Pattern::Any(*x); item_typs.len()]
                                                .into_iter()
                                                .chain(arm.pats[1..].iter().cloned())
                                                .collect(),
                                            body: arm.body.clone(),
                                        },
                                        *idx,
                                        cxt.clone(),
                                    )),
                                    [Pattern::Con(constr_, item_pats), ..]
                                        if !constrs_name.contains(&constr_.data) =>
                                    {
                                        //println!("bind {} -> {}", constr_.data, super::pretty::pretty_tm(0, cxt.names(), tm));
                                        //println!("bind {} -> {}", constr_.data, super::pretty::pretty_tm(0, cxt.names(), &infer.quote(cxt.lvl, typ.clone())));
                                        Some((
                                            MatchArm {
                                                pats: vec![
                                                    Pattern::Any(constr_.to_span());
                                                    item_typs.iter().filter(|x| x.2 == Icit::Expl).count()
                                                ]
                                                .into_iter()
                                                .chain(arm.pats[1..].iter().cloned())
                                                .collect(),
                                                body: arm.body.clone(),
                                            },
                                            *idx,
                                            cxt.bind(constr_.clone(), tm.clone(), typ.clone()),
                                        ))
                                    }
                                    [Pattern::Con(constr_, item_pats), ..] if constr_ == constr => {
                                        Some((
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
                                        ))
                                    }
                                    _ => None,
                                })
                                .collect::<Vec<_>>();

                            let subtree = if remaining_arms.is_empty() {
                                let unmatched = Self::fill_context(
                                    context,
                                    &Pattern::Con(
                                        constr.clone(),
                                        vec![Pattern::Any(empty_span(())); item_typs.len()],
                                    ),
                                );
                                self.warnings.push(Warning::Unmatched(unmatched));
                                Box::new(DecisionTree::Fail)
                            } else {
                                let context_ = if new_heads.is_empty() {
                                    if heads_rest.is_empty() {
                                        context.clone()
                                    } else {
                                        self.next_hole(
                                            context,
                                            &Pattern::Con(constr.clone(), vec![]),
                                        )
                                    }
                                } else {
                                    MatchContext::InCons {
                                        parent: context.clone().into(),
                                        constr: constr.clone(),
                                        before: vec![],
                                        after: vec![
                                            Pattern::Any(empty_span(()));
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
                                    &remaining_arms,
                                    &context_,
                                    &cxt_global,
                                )?
                            };

                            Ok((
                                constr.clone(),
                                new_heads.iter().map(|(var, _, _)| *var).collect(),
                                subtree,
                            ))
                        })
                        .collect::<Result<Vec<_>, _>>()?;

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
        tm: Tm,
        typ: Val,
        arms: &[(Pattern, Raw)],
        cxt: &Cxt,
    ) -> Result<(Box<DecisionTree>, Vec<Warning>), Error> {
        self.warnings = Vec::new();
        self.reachable = HashMap::new();
        let tree = self.compile_aux(
            infer,
            &[(0, tm, typ)],
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
                    )
                })
                .collect::<Vec<_>>(),
            &MatchContext::Outermost,
            cxt,
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
        let (case_name, global_prarams, params, constrs_name) = match infer.force(heads.clone()) {
            Val::SumCase {
                sum_name: _,
                case_name,
                global_params,
                datas: params,
                cases_name,
            } => (case_name, global_params, params, cases_name),
            //_ => panic!("by now only can match a sum type, but get {:?}", heads),
            _ => (empty_span("$unknown$".to_owned()), vec![], vec![], vec![])
        };

        let cxt_new = global_prarams
            .into_iter()
            .filter(|x| x.3 == Icit::Impl)
            .fold(cxt.clone(), |cxt, (name, val, vty, _)| {
                cxt.prepend(val)
            });

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
                    .map(|x| &x.1).zip(item_pats.iter()).try_fold(
                        (body.clone(), cxt_new.clone()),
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
        before: Vec<Pattern>,
        after: Vec<Pattern>,
    },
}

#[derive(Debug, Clone)]
struct MatchArm {
    pats: Vec<Pattern>,
    body: (Raw, usize),
}
