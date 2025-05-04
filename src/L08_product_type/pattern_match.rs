use std::{
    collections::{BTreeSet, HashMap},
    rc::Rc,
};

use crate::parser_lib::{Span, ToSpan};

use super::{
    Env, Error, Infer, Lvl, Tm, Val,
    cxt::Cxt,
    empty_span,
    parser::syntax::{Pattern, Raw},
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
    pub ret_type: Option<Val>,
}

impl Compiler {
    pub fn new() -> Self {
        Compiler {
            warnings: Vec::new(),
            reachable: HashMap::new(),
            seed: 0,
            ret_type: None,
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
            //MatchContext::Outermost => panic!("next_hole"),
            MatchContext::Outermost => MatchContext::Outermost, //TODO: is this correct?
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
                    match &self.ret_type {
                        Some(ret_type) => {
                            let ret = infer.check(cxt, arm.body.0.clone(), ret_type.clone())?;
                            Ok(Box::new(DecisionTree::Leaf((ret, arm.body.1))))
                        }
                        None => {
                            let ret = infer.infer_expr(cxt, arm.body.0.clone())?;
                            self.ret_type = Some(ret.1);
                            Ok(Box::new(DecisionTree::Leaf((ret.0, arm.body.1))))
                        }
                    }
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
                                    pats: arm.0.pats[1..].to_vec(),
                                    body: arm.0.body.clone(),
                                },
                                arm.1,
                                arm.2.clone(),
                            )
                        })
                        .collect::<Vec<_>>();
                    self.compile_aux(infer, heads_rest, &new_arms, &new_context, cxt_global)
                } else {
                    let new_typ = match typ {
                        rigid @ Val::Rigid(_, _) => {
                            let new_tm = infer.quote(cxt_global.lvl, rigid.clone());
                            infer.eval(&cxt_global.env, new_tm)
                        }
                        x => x.clone(),
                    };
                    let (typename, constrs) = match new_typ {
                        Val::Sum(span, _, cases) => (span, cases),
                        //_ => panic!("by now only can match a sum type, but get {:?}", typ),
                        _ => {
                            //let idx = arms[0].1;
                            //self.reachable.insert(idx, ());
                            (empty_span("$unknown$".to_owned()), vec![(empty_span("$unknown$".to_owned()), vec![])])
                        }
                    };

                    let constrs_name = constrs
                        .iter()
                        .map(|x| x.0.data.clone())
                        .collect::<BTreeSet<_>>();

                    let decision_tree_branches = constrs
                        .iter()
                        .map(|(constr, item_typs)| {
                            let new_heads = item_typs
                                .iter()
                                .map(|typ| {
                                    let tm = infer.check(cxt_global, typ.clone(), Val::U).unwrap();//TODO:do not unwrap
                                    let val = infer.eval(&cxt_global.env, tm.clone());
                                    (
                                        self.fresh(),
                                        tm,
                                        val,
                                    )
                                })
                                .collect::<Vec<_>>();
                            let remaining_arms = arms
                                .iter()
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
                                        if cxt.src_names.contains_key(&constr_.data) {
                                            //return Err(Error(format!("match fail: {:?}", constr_)))
                                            todo!()
                                        } else {
                                            Some((
                                                MatchArm {
                                                    pats: vec![
                                                        Pattern::Any(constr_.to_span());
                                                        item_typs.len()
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
                                    cxt_global,
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
        let reachable = HashMap::new();
        self.reachable = reachable;
        self.warnings = Vec::new();

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
        arms: &[(Pattern, Tm)],
    ) -> Option<(Tm, Env)> {
        let new_typ = match heads.clone() {
            rigid @ Val::Rigid(_, _) => {
                println!("{:?}: {}", rigid, cxt.iter().count());
                println!("{:?}", cxt.iter().nth(1));
                let new_tm = infer.quote(Lvl(cxt.iter().count() as u32), rigid.clone()); //TODO: can here lvl get from env?
                infer.eval(cxt, new_tm)
            }
            x => x.clone(),
        };
        let (case_name, params, constrs_name) = match new_typ {
            Val::SumCase {
                sum_name,
                case_name,
                params,
                cases_name,
            } => (case_name, params, cases_name),
            //_ => panic!("by now only can match a sum type, but get {:?}", heads),
            _ => (empty_span("$unknown$".to_owned()), vec![], vec![])
        };

        arms.iter()
            .filter_map(|(pattern, body)| match pattern {
                Pattern::Any(_) => Some((body.clone(), cxt.clone())),
                Pattern::Con(constr_, item_pats) if !constrs_name.contains(&constr_) => {
                    /*if cxt.src_names.contains_key(&constr_.data) {
                        //return Err(Error(format!("match fail: {:?}", constr_)))
                        todo!()
                    } else */
                    {
                        //TODO: item_pats should be zero
                        //println!("-----  {:?}", heads);
                        Some((body.clone(), cxt.prepend(heads.clone())))
                    }
                }
                Pattern::Con(constr_, item_pats) if constr_ == &case_name => {
                    params.iter().zip(item_pats.iter()).try_fold(
                        (body.clone(), cxt.clone()),
                        |(body, cxt), (param, pat): (&Val, &Pattern)| {
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
