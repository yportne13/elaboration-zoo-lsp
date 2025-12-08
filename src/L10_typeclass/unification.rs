use colored::Colorize;

use crate::list::List;

use super::{
    Error, Infer, Lvl, MetaEntry, MetaVar, Spine, Tm, UnifyError, VTy, Val, cxt::Cxt, lvl2ix,
    parser::syntax::Icit, syntax::Pruning, empty_span, pretty::pretty_tm, typeclass::Assertion, Raw,
};

use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone)]
pub struct PartialRenaming {
    pub occ: Option<MetaVar>,
    pub dom: Lvl,               // size of Γ
    pub cod: Lvl,               // size of Δ
    pub ren: HashMap<u32, Lvl>, // mapping from Δ vars to Γ vars
}

fn lift(pr: &PartialRenaming) -> PartialRenaming {
    let mut new_ren = pr.ren.clone();
    new_ren.insert(pr.cod.0, pr.dom);

    PartialRenaming {
        occ: pr.occ,
        dom: pr.dom + 1, // increment dom
        cod: pr.cod + 1, // increment cod
        ren: new_ren,    // update ren with the new mapping
    }
}

fn skip(pr: &PartialRenaming) -> PartialRenaming {
    PartialRenaming {
        occ: pr.occ,
        dom: pr.dom,         // decrement dom
        cod: pr.cod + 1,     // decrement cod
        ren: pr.ren.clone(), // no change in ren
    }
}

#[derive(Debug, Clone, Copy)]
enum SpinePruneStatus {
    OKRenaming,
    OKNonRenaming,
    NeedsPruning,
}

impl Infer {
    fn invert_go(
        &self,
        sp: Spine,
    ) -> Result<(Lvl, HashMap<u32, Lvl>, HashSet<u32>, List<(Lvl, Icit)>), UnifyError> {
        match sp {
            List { head: None } => Ok((Lvl(0), HashMap::new(), HashSet::new(), List::new())),
            a => {
                let (dom, mut ren, mut nlvars, fsp) = self.invert_go(a.tail())?;
                match self.force(a.head().unwrap().0.clone()) {
                    Val::Rigid(x, List { head: None }) => {
                        if ren.contains_key(&x.0) || nlvars.contains(&x.0) {
                            ren.remove(&x.0);
                            nlvars.insert(x.0);
                            Ok((dom + 1, ren, nlvars, fsp.prepend((x, a.head().unwrap().1))))
                        } else {
                            ren.insert(x.0, dom);
                            Ok((dom + 1, ren, nlvars, fsp.prepend((x, a.head().unwrap().1))))
                        }
                    }
                    _ => Err(UnifyError::Basic),
                }
            }
        }
    }
    pub fn invert(
        &self,
        gamma: Lvl,
        sp: Spine,
    ) -> Result<(PartialRenaming, Option<Pruning>), UnifyError> {
        //println!("{} {:?} {:?}", "invert".green(), gamma, sp);
        let (dom, ren, nlvars, fsp) = self.invert_go(sp)?;

        Ok((
            PartialRenaming {
                occ: None,
                dom,
                cod: gamma,
                ren,
            },
            if nlvars.is_empty() {
                None
            } else {
                Some(fsp.map(|(x, i)| {
                    if nlvars.contains(&x.0) {
                        None
                    } else {
                        Some(*i)
                    }
                }))
            },
        ))
    }
    fn prune_ty_go(
        &mut self,
        pr: &Pruning,
        pren: &PartialRenaming,
        a: Val,
    ) -> Result<Tm, UnifyError> {
        match (pr, self.force(a)) {
            (List { head: None }, a) => self.rename(pren, a),
            (list, Val::Pi(x, i, a, b)) if list.head().unwrap().is_some() => {
                let a = self.rename(pren, *a)?;
                let b = self.closure_apply(&b, Val::vvar(pren.cod));
                let b = self.prune_ty_go(&list.tail(), &lift(pren), b)?;
                Ok(Tm::Pi(x, i, Box::new(a), Box::new(b)))
            }
            (list, Val::Pi(x, i, a, b)) if list.head().unwrap().is_none() => {
                let b = self.closure_apply(&b, Val::vvar(pren.cod));
                self.prune_ty_go(&list.tail(), &skip(pren), b)
            }
            _ => Err(UnifyError::Basic), // impossible case
        }
    }
    pub fn prune_ty(&mut self, pr: &Pruning, a: Val) -> Result<Tm, UnifyError> {
        self.prune_ty_go(
            pr,
            &PartialRenaming {
                occ: None,
                dom: Lvl(0),
                cod: Lvl(0),
                ren: HashMap::new(),
            },
            a,
        )
    }
    fn prune_meta(&mut self, pruning: Pruning, m: MetaVar) -> Result<MetaVar, UnifyError> {
        let mty = match self.meta[m.0 as usize] {
            MetaEntry::Unsolved(ref a) => a.clone(),
            _ => unreachable!(),
        };

        let prune_ty = self.prune_ty(&pruning, mty.clone())?;
        let prunedty = self.eval(&List::new(), prune_ty); //TODO:revPruning
        let m_prime = MetaVar(self.new_meta(prunedty));

        let solution = self.eval(
            &List::new(),
            self.lams(
                Lvl(pruning.iter().count() as u32), // Assuming Lvl is based on length of pruning
                mty.clone(),
                Tm::AppPruning(Box::new(Tm::Meta(m_prime)), pruning),
            ),
        );

        self.meta[m.0 as usize] = MetaEntry::Solved(solution, mty);
        Ok(m_prime)
    }
    fn prune_vflex_go(
        &mut self,
        pren: &PartialRenaming,
        sp: Spine,
    ) -> Result<(List<(Option<Tm>, Icit)>, SpinePruneStatus), UnifyError> {
        if sp.head().is_none() {
            Ok((List::new(), SpinePruneStatus::OKRenaming))
        } else {
            let (sp_rest, status) = self.prune_vflex_go(pren, sp.tail())?;
            match self.force(sp.head().unwrap().0.clone()) {
                Val::Rigid(x, List { head: None }) => match (pren.ren.get(&x.0), status) {
                    (Some(x), _) => Ok((
                        sp_rest
                            .prepend((Some(Tm::Var(lvl2ix(pren.dom, *x))), sp.head().unwrap().1)),
                        status,
                    )),
                    (None, SpinePruneStatus::OKNonRenaming) => Err(UnifyError::Basic),
                    (None, _) => Ok((
                        sp_rest.prepend((None, sp.head().unwrap().1)),
                        SpinePruneStatus::NeedsPruning,
                    )),
                },
                t => match status {
                    SpinePruneStatus::NeedsPruning => Err(UnifyError::Basic),
                    _ => {
                        let t = self.rename(pren, t)?;
                        Ok((
                            sp_rest.prepend((Some(t), sp.head().unwrap().1)),
                            SpinePruneStatus::OKNonRenaming,
                        ))
                    }
                },
            }
        }
    }
    fn prune_vflex(
        &mut self,
        pren: &PartialRenaming,
        m: MetaVar,
        sp: Spine,
    ) -> Result<Tm, UnifyError> {
        let (sp, status) = self.prune_vflex_go(pren, sp)?;

        let m_prime = match status {
            SpinePruneStatus::OKRenaming => {
                match self.meta[m.0 as usize] {
                    MetaEntry::Unsolved(_) => m,
                    //_ => return Err(Error::Impossible),
                    _ => unreachable!(),
                }
            }
            SpinePruneStatus::OKNonRenaming => {
                match self.meta[m.0 as usize] {
                    MetaEntry::Unsolved(_) => m,
                    //_ => return Err(Error::Impossible),
                    _ => unreachable!(),
                }
            }
            SpinePruneStatus::NeedsPruning => {
                self.prune_meta(sp.map(|(mt, i)| mt.as_ref().map(|_| i.clone())), m)?
            }
        };

        let t = sp.iter().fold(Tm::Meta(m_prime), |t, (mu, i)| {
            if let Some(u) = mu {
                Tm::App(Box::new(t), Box::new(u.clone()), i.clone())
            } else {
                t
            }
        }); //TODO:need rev()?

        Ok(t)
    }
    fn rename_sp(&mut self, pren: &PartialRenaming, t: Tm, sp: &Spine) -> Result<Tm, UnifyError> {
        match sp {
            List { head: None } => Ok(t),
            a => {
                let t = self.rename_sp(pren, t, &a.tail())?;
                let u = self.rename(pren, a.head().unwrap().0.clone())?;
                Ok(Tm::App(Box::new(t), Box::new(u), a.head().unwrap().1))
            }
        }
    }
    pub fn rename(&mut self, pren: &PartialRenaming, t: Val) -> Result<Tm, UnifyError> {
        match self.force(t) {
            Val::Flex(m_prime, sp) => match pren.occ {
                Some(m) if m == m_prime => Err(UnifyError::Basic),
                _ => self.prune_vflex(pren, m_prime, sp),
            },
            Val::Rigid(x, sp) => match pren.ren.get(&x.0) {
                None => if x.0 <= 1919810 {
                    Err(UnifyError::Basic)
                } else {
                    let t = Tm::Var(lvl2ix(pren.dom, x));
                    self.rename_sp(pren, t, &sp)
                }, // scope error
                Some(x_prime) => {
                    let t = Tm::Var(lvl2ix(pren.dom, *x_prime));
                    self.rename_sp(pren, t, &sp)
                }
            },
            Val::Obj(x, name, sp) => {
                let t = self.rename(pren, *x)?;
                let t = Tm::Obj(Box::new(t), name.clone());
                self.rename_sp(pren, t, &sp)
            },
            Val::Lam(x, i, closure) => {
                let t = self.rename(
                    &lift(pren),
                    self.closure_apply(&closure, Val::vvar(pren.cod)),
                )?;
                Ok(Tm::Lam(x, i, Box::new(t)))
            }
            Val::Pi(x, i, a, closure) => {
                let a = self.rename(pren, *a)?;
                let b = self.rename(
                    &lift(pren),
                    self.closure_apply(&closure, Val::vvar(pren.cod)),
                )?;
                Ok(Tm::Pi(x, i, Box::new(a), Box::new(b)))
            }
            Val::U(x) => Ok(Tm::U(x)),
            Val::LiteralType => Ok(Tm::LiteralType),
            Val::LiteralIntro(x) => Ok(Tm::LiteralIntro(x.clone())),
            Val::Prim => Ok(Tm::Prim),
            Val::Sum(x, params, cases, is_trait) => {
                let new_params = params
                    .into_iter()
                    .map(|x| {
                        match (self.rename(pren, x.1), self.rename(pren, x.2)) {
                            (Ok(a), Ok(b)) => Ok((x.0, a, b, x.3)),
                            (Err(x), _) | (_, Err(x)) => Err(x),
                        }
                    })
                    .collect::<Result<_, _>>()?;
                Ok(Tm::Sum(x, new_params, cases, is_trait))
            }
            Val::SumCase {
                is_trait,
                typ,
                case_name,
                datas: params,
            } => {
                let typ = self.rename(pren, *typ)?;
                let params = params
                    .into_iter()
                    .map(|p| {
                        let z = self.rename(pren, p.1)?;
                        Ok((p.0, z, p.2))
                    })
                    .collect::<Result<_, _>>()?;
                Ok(Tm::SumCase {
                    is_trait,
                    typ: Box::new(typ),
                    case_name,
                    datas: params,
                })
            }
            Val::Match(val, env, cases) => {
                let val = self.rename(pren, *val)?;
                let cases = cases
                    .into_iter()
                    .map(|(pat, tm)| {
                        let (env, pren) = (0..pat.bind_count())
                            .fold((env.clone(), pren.clone()), |(env, pren), _| (
                                env.prepend(Val::vvar(pren.cod)),
                                lift(&pren),
                            ));
                        let mut avoid_recursive = self.clone();
                        avoid_recursive.global
                            .iter_mut()
                            .for_each(|x| *x.1 = Val::Rigid(*x.0 + 1919810, List::new()));
                        let body = self.rename(
                            &pren,
                            avoid_recursive.eval(&env, tm),
                        )?;
                        Ok((pat, body))
                    })
                    .collect::<Result<_, _>>()?;
                Ok(Tm::Match(Box::new(val), cases))
            }
        }
    }
    fn lams_go(&self, l: Lvl, t: Tm, a: VTy, l_prime: Lvl) -> Tm {
        if l == l_prime {
            t
        } else {
            match self.force(a) {
                Val::Pi(span, icit, val, closure) if span.data == "_" => {
                    let var_name = format!("x{}", l_prime.0);
                    Tm::Lam(
                        empty_span(var_name),
                        icit,
                        Box::new(self.lams_go(
                            l,
                            t,
                            self.closure_apply(&closure, Val::Rigid(l_prime, List::new())),
                            l_prime + 1,
                        )),
                    )
                }
                Val::Pi(span, icit, val, closure) => Tm::Lam(
                    span,
                    icit,
                    Box::new(self.lams_go(
                        l,
                        t,
                        self.closure_apply(&closure, Val::Rigid(l_prime, List::new())),
                        l_prime + 1,
                    )),
                ),
                _ => unreachable!(),
            }
        }
    }
    pub fn lams(&self, l: Lvl, a: VTy, t: Tm) -> Tm {
        self.lams_go(l, t, a, Lvl(0))
    }
    fn solve(&mut self, gamma: Lvl, m: MetaVar, sp: Spine, rhs: Val) -> Result<(), UnifyError> {
        /*println!(
            "{} {:?} {:?} {:?}\n  rhs: {:?}",
            "solve".red(),
            gamma,
            m,
            sp,
            rhs
        );*/
        let (pren, prune_non_linear) = self.invert(gamma, sp.clone())?;
        self.solve_with_pren(m, pren, prune_non_linear, rhs)
    }
    fn solve_with_pren(
        &mut self,
        m: MetaVar,
        pren: PartialRenaming,
        prune_non_linear: Option<Pruning>,
        rhs: Val,
    ) -> Result<(), UnifyError> {
        let mty = match self.meta[m.0 as usize] {
            MetaEntry::Unsolved(ref a) => a.clone(),
            _ => unreachable!(),
        };

        // if the spine was non-linear, we check that the non-linear arguments
        // can be pruned from the meta type (i.e. that the pruned solution will
        // be well-typed)
        if let Some(pr) = prune_non_linear {
            self.prune_ty(&pr, mty.clone())?; //TODO:revPruning?
        }

        let rhs = self.rename(
            &PartialRenaming {
                occ: Some(m),
                ..pren
            },
            rhs,
        )?;
        let solution = self.eval(&List::new(), self.lams(pren.dom, mty.clone(), rhs));
        self.meta[m.0 as usize] = MetaEntry::Solved(solution, mty);

        Ok(())
    }
    fn solve_multi_trait(&mut self, cxt: &Cxt, m: MetaVar) -> Result<(), UnifyError>{
        let prepare = self.meta.get(m.0 as usize ..)
            .iter()
            .flat_map(|x| x.iter())
            .enumerate()
            .flat_map(|x| if let MetaEntry::Unsolved(v) = x.1 { Some((x.0, v.clone())) } else { None })
            .collect::<Vec<_>>();
        for (idx, x) in prepare {
            let typ = self.solve_trait(cxt, &x)
                .map_err(UnifyError::Trait)?;
            if let Some((_, val)) = typ {
                //println!("solve trait {:?}\nmeta: {}\n{:?}", val, idx, self.meta[idx + m.0 as usize]);
                self.meta[idx + m.0 as usize] = MetaEntry::Solved(val, x);
            }
        }
        Ok(())
    }
    pub fn solve_trait(&mut self, cxt: &Cxt, x: &Val) -> Result<Option<(Tm, Val)>, String> {
        /*let mut x = x.clone();
        let mut lvl = cxt.lvl;
        while let Val::Pi(_, _, _, clos) = x {
            x = self.closure_apply(&clos, Val::vvar(lvl));
            lvl = lvl + 1;
        }*/
        if let Val::Sum(name, params, _, true) = &x {
            let params = params
                .iter()
                .flat_map(|(_, tm, _, _)| self.force(tm.clone()).to_typ())
                .collect::<Vec<_>>();
            self.trait_solver.clean();
            if let Some(a) = self.trait_solver.synth(Assertion {
                name: name.data.clone(),
                arguments: params.clone(),
            }) {
                let (tm, _) = self.infer_expr(cxt, Raw::Var(name.clone().map(|_| format!("{:?}{:?}", a.name, a.arguments))))
                    .map_err(|e| e.0.data)?;
                let val = self.eval(&cxt.env, tm.clone());
                Ok(Some((tm, val)))
            } else {
                Err(format!("solve trait failed: {:?}", params))?
            }
        } else {
            Ok(None)
        }
    }
    fn unify_sp(
        &mut self,
        l: Lvl,
        cxt: &Cxt,
        sp: &Spine,
        sp_prime: &Spine,
    ) -> Result<(), UnifyError> {
        match (sp, sp_prime) {
            (List { head: None }, List { head: None }) => Ok(()), // Both spines are empty
            (a, b) if matches!(a.head(), Some(_)) && matches!(b.head(), Some(_)) => {
                self.unify_sp(l, cxt, &a.tail(), &b.tail())?; // Recursively unify the rest of the spines
                self.unify(
                    l,
                    cxt,
                    a.head().unwrap().0.clone(),
                    b.head().unwrap().0.clone(),
                ) // Unify the current values
            }
            _ => Err(UnifyError::Basic), // Rigid mismatch error
        }
    }

    fn flex_flex(
        &mut self,
        gamma: Lvl,
        cxt: &Cxt,
        m: MetaVar,
        sp: Spine,
        m_prime: MetaVar,
        sp_prime: Spine,
    ) -> Result<(), UnifyError> {
        let mut go =
            |m: MetaVar, sp: Spine, m_prime: MetaVar, sp_prime: Spine| -> Result<(), UnifyError> {
                match self.invert(gamma, sp.clone()) {
                    Err(_) => {
                        self.solve(gamma, m_prime, sp_prime, Val::Flex(m, sp))?;
                        self.solve_multi_trait(cxt, m_prime)
                    },
                    Ok((pren, p1)) => {
                        self.solve_with_pren(m, pren, p1, Val::Flex(m_prime, sp_prime))
                    }
                }
            };

        if sp.iter().count() < sp_prime.iter().count() {
            go(m_prime, sp_prime, m, sp)
        } else {
            go(m, sp, m_prime, sp_prime)
        }
    }

    fn intersect_go(&mut self, sp: Spine, sp_prime: Spine) -> Option<List<Option<Icit>>> {
        match (sp, sp_prime) {
            (List { head: None }, List { head: None }) => Some(List::new()),
            (a, b) if a.head().is_some() && b.head().is_some() => {
                match (
                    self.force(a.head().unwrap().0.clone()),
                    self.force(b.head().unwrap().0.clone()),
                ) {
                    (
                        Val::Rigid(x, List { head: None }),
                        Val::Rigid(x_prime, List { head: None }),
                    ) => self.intersect_go(a.tail(), b.tail()).map(|l| {
                        l.prepend(if x == x_prime {
                            Some(a.head().unwrap().1)
                        } else {
                            None
                        })
                    }),
                    _ => None,
                }
            }
            _ => unreachable!(),
        }
    }
    fn intersect(
        &mut self,
        l: Lvl,
        cxt: &Cxt,
        m: MetaVar,
        sp: Spine,
        sp_prime: Spine,
    ) -> Result<(), UnifyError> {
        match self.intersect_go(sp.clone(), sp_prime.clone()) {
            None => self.unify_sp(l, cxt, &sp, &sp_prime),
            Some(pr) if pr.iter().any(|x| x.is_none()) => {
                self.prune_meta(pr, m)?;
                Ok(())
            }
            Some(_) => Ok(()),
        }
    }
    pub fn unify(&mut self, l: Lvl, cxt: &Cxt, t: Val, u: Val) -> Result<(), UnifyError> {
        //println!("unify: {t:?} {u:?}");
        let t = self.force(t);
        let u = self.force(u);
        /*println!(
            "uni {}\n == {}",
            pretty_tm(0, cxt.names(), &self.quote(l, t.clone())),
            pretty_tm(0, cxt.names(), &self.quote(l, u.clone())),
        );*/

        match (&t, &u) {
            (Val::U(x), Val::U(y)) if x == y => Ok(()),
            (Val::Pi(x, i, a, b), Val::Pi(_, i_prime, a_prime, b_prime)) if i == i_prime => {
                self.unify(l, cxt, *a.clone(), *a_prime.clone())?;
                self.unify(
                    l + 1,
                    &cxt.bind(x.clone(), self.quote(cxt.lvl, *a.clone()), *a.clone()),
                    self.closure_apply(b, Val::vvar(l)),
                    self.closure_apply(b_prime, Val::vvar(l)),
                )
            }
            (Val::Rigid(x, sp), Val::Rigid(x_prime, sp_prime)) if x == x_prime => {
                self.unify_sp(l, cxt, sp, sp_prime)
            }
            (Val::Flex(m, sp), Val::Flex(m_prime, sp_prime)) if m == m_prime => {
                self.intersect(l, cxt, *m, sp.clone(), sp_prime.clone())
            }
            (Val::Flex(m, sp), Val::Flex(m_prime, sp_prime)) => {
                self.flex_flex(l, cxt, *m, sp.clone(), *m_prime, sp_prime.clone())
            }
            (Val::Lam(_, _, t), Val::Lam(_, _, t_prime)) => self.unify(
                l + 1,
                cxt,
                self.closure_apply(t, Val::vvar(l)),
                self.closure_apply(t_prime, Val::vvar(l)),
            ),
            (t, Val::Lam(_, i, t_prime)) => self.unify(
                l + 1,
                cxt,
                self.v_app(t.clone(), Val::vvar(l), *i),
                self.closure_apply(t_prime, Val::vvar(l)),
            ),
            (Val::Lam(_, i, t), t_prime) => self.unify(
                l + 1,
                cxt,
                self.closure_apply(t, Val::vvar(l)),
                self.v_app(t_prime.clone(), Val::vvar(l), *i),
            ),
            (Val::Flex(m, sp), t)
                | (t, Val::Flex(m, sp)) => {
                self.solve(l, *m, sp.clone(), t.clone())?;
                self.solve_multi_trait(cxt, *m)
            }
            (Val::LiteralType, Val::LiteralType) => Ok(()),
            (Val::LiteralType, Val::Prim) => Ok(()),
            (Val::Prim, Val::LiteralType) => Ok(()),
            (Val::Sum(a, params_a, _, _), Val::Sum(b, params_b, _, _)) if a.data == b.data => {
                // params_a.len() always equal to params_b.len()?
                for (a, b) in params_a.iter().zip(params_b.iter()) {
                    self.unify(l, cxt, a.1.clone(), b.1.clone())?;
                }
                Ok(())
            }
            (
                Val::SumCase { is_trait: _, typ: a, case_name: ca, datas: params_a },
                Val::SumCase { is_trait: _, typ: b, case_name: cb, datas: params_b },
            ) if ca.data == cb.data => {
                // params_a.len() always equal to params_b.len()?
                self.unify(l, cxt, *a.clone(), *b.clone())?;
                for (a, b) in params_a.iter().zip(params_b.iter()) {
                    self.unify(l, cxt, a.1.clone(), b.1.clone())?;
                }
                Ok(())
            }
            (Val::Match(s1, env1, cases1), Val::Match(s2, env2, cases2)) => {
                // 1. 合一 scrutinees
                self.unify(l, cxt, *s1.clone(), *s2.clone())?;

                // 2. 检查分支数量是否相同
                if cases1.len() != cases2.len() {
                    return Err(UnifyError::Basic);
                }

                // 3. 遍历并合一每一个对应的分支
                for ((p1, clos1), (p2, clos2)) in cases1.iter().zip(cases2.iter()) {
                    // 3a. 检查模式是否完全相同。
                    // 这里我们假设 Pattern 可以通过 `PartialEq` 进行比较。
                    // 如果模式的结构更复杂（例如包含类型信息），你可能需要一个递归的模式合一函数。
                    // 对于你目前的定义，`PartialEq` 应该是足够的。
                    if p1 != p2 {
                        return Err(UnifyError::Basic);
                    }

                    let count = p1.bind_count();

                    let env1 = (0..count).fold(env1.clone(), |env, idx| {
                        env.prepend(Val::vvar(l + idx))
                    });

                    let env2 = (0..count).fold(env2.clone(), |env, idx| {
                        env.prepend(Val::vvar(l + idx))
                    });

                    /*println!(
                        "unify {:?}\n   == {:?}",
                        pretty_tm(0, cxt.names(), clos1),
                        pretty_tm(0, cxt.names(), clos2),
                    );*/
                    //let body1_val = self.eval(&bind_env, clos1.clone());
                    //let body2_val = self.eval(&bind_env, clos2.clone());
                    let mut avoid_recursive = self.clone();
                    avoid_recursive.global
                        .iter_mut()
                        .for_each(|x| *x.1 = Val::Rigid(*x.0 + 1919810, List::new()));
                    let body1_val = avoid_recursive.eval(&env1, clos1.clone());
                    let body2_val = avoid_recursive.eval(&env2, clos2.clone());

                    /*println!(
                        "-> {:?}\n== {:?}",
                        pretty_tm(0, cxt.names(), &self.quote(l, body1_val.clone())),
                        pretty_tm(0, cxt.names(), &self.quote(l, body2_val.clone())),
                    );*/
                    self.unify(l + count, cxt, body1_val, body2_val)?;

                    // 使用你在上一步中实现的 apply_match_closure (或类似逻辑)
                    // 来实例化两个闭包的 body。这会用新的局部变量 (vvar) 替换掉模式绑定的变量。
                    /*let body1_val = self.apply_match_closure(lvl, clos1.clone(), num_binders);
                    let body2_val = self.apply_match_closure(lvl, clos2.clone(), num_binders);

                    // 现在，我们在一个扩展了 num_binders 个变量的上下文中，对实例化后的 body进行合一。
                    // 这个扩展的上下文是通过将 level 增加 num_binders 来表示的。
                    self.unify(l + num_binders, cxt, body1_val, body2_val)?;*/
                    //TODO:todo!()
                }

                // 如果所有检查都通过，则合一成功
                Ok(())
            }
            _ => Err(UnifyError::Basic), // Rigid mismatch error
        }
    }
}
