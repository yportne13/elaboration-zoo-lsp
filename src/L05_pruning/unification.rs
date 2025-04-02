use colored::Colorize;

use crate::{L05_pruning::empty_span, list::List};

use super::{
    Error, Infer, Lvl, MetaEntry, MetaVar, Spine, Tm, UnifyError, VTy, Val, lvl2ix,
    parser::syntax::Icit, syntax::Pruning,
};

use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone)]
struct PartialRenaming {
    occ: Option<MetaVar>,
    dom: Lvl,               // size of Γ
    cod: Lvl,               // size of Δ
    ren: HashMap<u32, Lvl>, // mapping from Δ vars to Γ vars
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
                    _ => Err(UnifyError),
                }
            }
        }
    }
    fn invert(
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
            _ => Err(UnifyError), // impossible case
        }
    }
    fn prune_ty(&mut self, pr: &Pruning, a: Val) -> Result<Tm, UnifyError> {
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
                    (None, SpinePruneStatus::OKNonRenaming) => Err(UnifyError),
                    (None, _) => Ok((
                        sp_rest.prepend((None, sp.head().unwrap().1)),
                        SpinePruneStatus::NeedsPruning,
                    )),
                },
                t => match status {
                    SpinePruneStatus::NeedsPruning => Err(UnifyError),
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
    fn rename(&mut self, pren: &PartialRenaming, t: Val) -> Result<Tm, UnifyError> {
        match self.force(t) {
            Val::Flex(m_prime, sp) => match pren.occ {
                Some(m) if m == m_prime => Err(UnifyError),
                _ => self.prune_vflex(pren, m_prime, sp),
            },
            Val::Rigid(x, sp) => match pren.ren.get(&x.0) {
                None => Err(UnifyError), // scope error
                Some(x_prime) => {
                    let t = Tm::Var(lvl2ix(pren.dom, *x_prime));
                    self.rename_sp(pren, t, &sp)
                }
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
            Val::U => Ok(Tm::U),
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
    fn lams(&self, l: Lvl, a: VTy, t: Tm) -> Tm {
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
    fn unify_sp(&mut self, l: Lvl, sp: &Spine, sp_prime: &Spine) -> Result<(), UnifyError> {
        match (sp, sp_prime) {
            (List { head: None }, List { head: None }) => Ok(()), // Both spines are empty
            (a, b) if matches!(a.head(), Some(_)) && matches!(b.head(), Some(_)) => {
                self.unify_sp(l, &a.tail(), &b.tail())?; // Recursively unify the rest of the spines
                self.unify(l, a.head().unwrap().0.clone(), b.head().unwrap().0.clone()) // Unify the current values
            }
            _ => Err(UnifyError), // Rigid mismatch error
        }
    }

    fn flex_flex(
        &mut self,
        gamma: Lvl,
        m: MetaVar,
        sp: Spine,
        m_prime: MetaVar,
        sp_prime: Spine,
    ) -> Result<(), UnifyError> {
        let mut go =
            |m: MetaVar, sp: Spine, m_prime: MetaVar, sp_prime: Spine| -> Result<(), UnifyError> {
                match self.invert(gamma, sp.clone()) {
                    Err(UnifyError) => self.solve(gamma, m_prime, sp_prime, Val::Flex(m, sp)),
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
        m: MetaVar,
        sp: Spine,
        sp_prime: Spine,
    ) -> Result<(), UnifyError> {
        match self.intersect_go(sp.clone(), sp_prime.clone()) {
            None => self.unify_sp(l, &sp, &sp_prime),
            Some(pr) if pr.iter().any(|x| x.is_none()) => {
                self.prune_meta(pr, m)?;
                Ok(())
            }
            Some(_) => Ok(()),
        }
    }
    pub fn unify(&mut self, l: Lvl, t: Val, u: Val) -> Result<(), UnifyError> {
        let t = self.force(t);
        let u = self.force(u);

        match (&t, &u) {
            (Val::U, Val::U) => Ok(()),
            (Val::Pi(x, i, a, b), Val::Pi(x_prime, i_prime, a_prime, b_prime)) if i == i_prime => {
                self.unify(l, *a.clone(), *a_prime.clone())?;
                self.unify(
                    l + 1,
                    self.closure_apply(&b, Val::vvar(l)),
                    self.closure_apply(&b_prime, Val::vvar(l)),
                )
            }
            (Val::Rigid(x, sp), Val::Rigid(x_prime, sp_prime)) if x == x_prime => {
                self.unify_sp(l, sp, sp_prime)
            }
            (Val::Flex(m, sp), Val::Flex(m_prime, sp_prime)) if m == m_prime => {
                self.intersect(l, *m, sp.clone(), sp_prime.clone())
            }
            (Val::Flex(m, sp), Val::Flex(m_prime, sp_prime)) => {
                self.flex_flex(l, *m, sp.clone(), *m_prime, sp_prime.clone())
            }
            (Val::Lam(_, _, t), Val::Lam(_, _, t_prime)) => self.unify(
                l + 1,
                self.closure_apply(&t, Val::vvar(l)),
                self.closure_apply(&t_prime, Val::vvar(l)),
            ),
            (t, Val::Lam(_, i, t_prime)) => self.unify(
                l + 1,
                self.v_app(t.clone(), Val::vvar(l), *i),
                self.closure_apply(&t_prime, Val::vvar(l)),
            ),
            (Val::Lam(_, i, t), t_prime) => self.unify(
                l + 1,
                self.closure_apply(&t, Val::vvar(l)),
                self.v_app(t_prime.clone(), Val::vvar(l), *i),
            ),
            (Val::Flex(m, sp), t_prime) => self.solve(l, *m, sp.clone(), t_prime.clone()),
            (t, Val::Flex(m_prime, sp_prime)) => {
                self.solve(l, *m_prime, sp_prime.clone(), t.clone())
            }
            _ => Err(UnifyError), // Rigid mismatch error
        }
    }
}
