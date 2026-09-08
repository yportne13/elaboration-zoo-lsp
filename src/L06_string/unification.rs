use crate::{L06_string::empty_span, list::List};

use super::{
    Infer, Lvl, MetaEntry, MetaVar, Spine, Tm, UnifyError, VTy, Val, lvl2ix,
    parser::syntax::Icit, syntax::Pruning,
};

use std::{collections::{HashMap, HashSet}, rc::Rc};

/// η 展开的可应用性守卫：只有中性值（Flex/Rigid/Decl 头）能吃 η 新变量。
/// `string_to_global_type` 把 def 的登记值（可以是 λ）当"动态类型"返回后，
/// λ 值会以**类型身份**流入 unify（源码级可达：`def f : U -> U = x => x`
/// 之后 `get_global "f"` 的类型就是 f 的 λ 值）——对字面量/U/Π 做 η 应用
/// 会命中 `v_app` 的 impossible panic。改为直接判失败（λ 与非函数值的
/// 比较无从展开，最小惊讶；快版 `unify_iter` 的 η 臂同款守卫）。
fn v_applicable(v: &Val) -> bool {
    matches!(v, Val::Flex(_, _) | Val::Rigid(_, _) | Val::Decl(_, _))
}

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
            List { head: None, .. } => Ok((Lvl(0), HashMap::new(), HashSet::new(), List::new())),
            a => {
                let (dom, mut ren, mut nlvars, fsp) = self.invert_go(a.tail())?;
                match self.force(&a.head().unwrap().0).as_ref() {
                    Val::Rigid(x, List { head: None, .. }) => {
                        if ren.contains_key(&x.0) || nlvars.contains(&x.0) {
                            ren.remove(&x.0);
                            nlvars.insert(x.0);
                            Ok((dom + 1, ren, nlvars, fsp.prepend((*x, a.head().unwrap().1))))
                        } else {
                            ren.insert(x.0, dom);
                            Ok((dom + 1, ren, nlvars, fsp.prepend((*x, a.head().unwrap().1))))
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
        rev: &[Option<Icit>],
        pren: &PartialRenaming,
        a: &Rc<Val>,
    ) -> Result<Tm, UnifyError> {
        let a = self.force(a);
        match (rev.split_first(), a.as_ref()) {
            (None, _) => self.rename(pren, &a),
            (Some((Some(_), rest)), Val::Pi(x, i, a, b)) => {
                let a = self.rename(pren, a)?;
                let b = self.closure_apply(&b, Val::vvar(pren.cod).into());
                let b = self.prune_ty_go(rest, &lift(pren), &b)?;
                Ok(Tm::Pi(x.clone(), *i, Box::new(a), Box::new(b)))
            }
            (Some((None, rest)), Val::Pi(_, _, _, b)) => {
                let b = self.closure_apply(&b, Val::vvar(pren.cod).into());
                self.prune_ty_go(rest, &skip(pren), &b)
            }
            _ => Err(UnifyError), // impossible case
        }
    }
    /// 上游 `pruneTy (revPruning pr) a`：掩码**外→内**配对 Π 层。
    /// 传入的掩码（invert / intersect / pruneVFlex 的产出）头 = 最内层，
    /// 先反转成头 = 最外层再逐层剥 Π。
    fn prune_ty(&mut self, pr: &Pruning, a: &Rc<Val>) -> Result<Tm, UnifyError> {
        let mut rev: Vec<Option<Icit>> = pr.iter().copied().collect();
        rev.reverse();
        self.prune_ty_go(
            &rev,
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

        let prune_ty = self.prune_ty(&pruning, &mty)?;
        let prunedty = self.eval(&List::new(), &prune_ty);
        let m_prime = MetaVar(self.new_meta(prunedty));

        let solution = self.eval(
            &List::new(),
            &self.lams(
                Lvl(pruning.iter().count() as u32), // Assuming Lvl is based on length of pruning
                &mty,
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
            let t = self.force(&sp.head().unwrap().0);
            match t.as_ref() {
                Val::Rigid(x, List { head: None, .. }) => match (pren.ren.get(&x.0), status) {
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
                _ => match status {
                    SpinePruneStatus::NeedsPruning => Err(UnifyError),
                    _ => {
                        let t = self.rename(pren, &t)?;
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
                self.prune_meta(sp.map(|(mt, i)| mt.as_ref().map(|_| *i)), m)?
            }
        };

        // 上游 `foldr (\(mu, i) t -> maybe t (\u -> App t u i) mu) (Meta m') sp`：
        // foldr 从尾（最外层）起 = 最外层实参先应用（修正旧移植 `iter().fold`
        // 从内层起导致的倒序——sp 头 = 最内层，直接 fold 会把内层包在最外）。
        let mut slots: Vec<(Option<Tm>, Icit)> = sp.iter().cloned().collect();
        slots.reverse();
        let mut t = Tm::Meta(m_prime);
        for (mu, i) in slots {
            if let Some(u) = mu {
                t = Tm::App(Box::new(t), Box::new(u), i);
            }
        }

        Ok(t)
    }
    fn rename_sp(&mut self, pren: &PartialRenaming, t: Tm, sp: &Spine) -> Result<Tm, UnifyError> {
        match sp {
            List { head: None, .. } => Ok(t),
            a => {
                let t = self.rename_sp(pren, t, &a.tail())?;
                let u = self.rename(pren, &a.head().unwrap().0)?;
                Ok(Tm::App(Box::new(t), Box::new(u), a.head().unwrap().1))
            }
        }
    }
    fn rename(&mut self, pren: &PartialRenaming, t: &Rc<Val>) -> Result<Tm, UnifyError> {
        match self.force(t).as_ref() {
            Val::Flex(m_prime, sp) => match pren.occ.as_ref() {
                Some(m) if m == m_prime => Err(UnifyError),
                _ => self.prune_vflex(pren, *m_prime, sp.clone()),
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
                    &self.closure_apply(&closure, Val::vvar(pren.cod).into()),
                )?;
                Ok(Tm::Lam(x.clone(), *i, Box::new(t)))
            }
            Val::Pi(x, i, a, closure) => {
                let a = self.rename(pren, a)?;
                let b = self.rename(
                    &lift(pren),
                    &self.closure_apply(&closure, Val::vvar(pren.cod).into()),
                )?;
                Ok(Tm::Pi(x.clone(), *i, Box::new(a), Box::new(b)))
            }
            Val::U => Ok(Tm::U),
            Val::LiteralType => Ok(Tm::LiteralType),
            Val::LiteralIntro(x) => Ok(Tm::LiteralIntro(x.clone())),
            Val::Decl(name, sp) => self.rename_sp(pren, Tm::Decl(name.clone()), &sp),
        }
    }
    fn lams_go(&self, l: Lvl, t: Tm, a: &Rc<VTy>, l_prime: Lvl) -> Tm {
        if l == l_prime {
            t
        } else {
            match self.force(a).as_ref() {
                Val::Pi(span, icit, val, closure) if span.data == "_" => {
                    let var_name = format!("x{}", l_prime.0);
                    Tm::Lam(
                        empty_span(var_name),
                        *icit,
                        Box::new(self.lams_go(
                            l,
                            t,
                            &self.closure_apply(&closure, Val::Rigid(l_prime, List::new()).into()),
                            l_prime + 1,
                        )),
                    )
                }
                Val::Pi(span, icit, val, closure) => Tm::Lam(
                    span.clone(),
                    *icit,
                    Box::new(self.lams_go(
                        l,
                        t,
                        &self.closure_apply(&closure, Val::Rigid(l_prime, List::new()).into()),
                        l_prime + 1,
                    )),
                ),
                _ => unreachable!(),
            }
        }
    }
    fn lams(&self, l: Lvl, a: &Rc<VTy>, t: Tm) -> Tm {
        self.lams_go(l, t, a, Lvl(0))
    }
    fn solve(&mut self, gamma: Lvl, m: MetaVar, sp: Spine, rhs: &Rc<Val>) -> Result<(), UnifyError> {
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
        rhs: &Rc<Val>,
    ) -> Result<(), UnifyError> {
        let mty = match self.meta[m.0 as usize] {
            MetaEntry::Unsolved(ref a) => a.clone(),
            _ => unreachable!(),
        };

        // if the spine was non-linear, we check that the non-linear arguments
        // can be pruned from the meta type (i.e. that the pruned solution will
        // be well-typed)
        if let Some(pr) = prune_non_linear {
            self.prune_ty(&pr, &mty)?;
        }

        let rhs = self.rename(
            &PartialRenaming {
                occ: Some(m),
                ..pren
            },
            rhs,
        )?;
        let solution = self.eval(&List::new(), &self.lams(pren.dom, &mty, rhs));
        self.meta[m.0 as usize] = MetaEntry::Solved(solution, mty);

        Ok(())
    }
    fn unify_sp(&mut self, l: Lvl, sp: &Spine, sp_prime: &Spine) -> Result<(), UnifyError> {
        match (sp, sp_prime) {
            (List { head: None, .. }, List { head: None, .. }) => Ok(()), // Both spines are empty
            (a, b) if a.head().is_some() && b.head().is_some() => {
                self.unify_sp(l, &a.tail(), &b.tail())?; // Recursively unify the rest of the spines
                self.unify(l, &a.head().unwrap().0, &b.head().unwrap().0) // Unify the current values
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
                    Err(UnifyError) => self.solve(gamma, m_prime, sp_prime, &Val::Flex(m, sp).into()),
                    Ok((pren, p1)) => {
                        self.solve_with_pren(m, pren, p1, &Val::Flex(m_prime, sp_prime).into())
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
            (List { head: None, .. }, List { head: None, .. }) => Some(List::new()),
            (a, b) if a.head().is_some() && b.head().is_some() => {
                match (
                    self.force(&a.head().unwrap().0).as_ref(),
                    self.force(&b.head().unwrap().0).as_ref(),
                ) {
                    (
                        Val::Rigid(x, List { head: None, .. }),
                        Val::Rigid(x_prime, List { head: None, .. }),
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
            // 长度失配：同一 meta 以不同 arity 出现——优雅回落 `intersect`
            // 的 `None => unify_sp` 逐实参比较（不可 `unreachable!()`）
            _ => None,
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
    pub fn unify(&mut self, l: Lvl, t: &Rc<Val>, u: &Rc<Val>) -> Result<(), UnifyError> {
        let t = self.force(t);
        let u = self.force(u);

        match (t.as_ref(), u.as_ref()) {
            (Val::U, Val::U) => Ok(()),
            (Val::Pi(_, i, a, b), Val::Pi(_, i_prime, a_prime, b_prime)) if i == i_prime => {
                self.unify(l, a, a_prime)?;
                self.unify(
                    l + 1,
                    &self.closure_apply(&b, Val::vvar(l).into()),
                    &self.closure_apply(&b_prime, Val::vvar(l).into()),
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
                &self.closure_apply(&t, Val::vvar(l).into()),
                &self.closure_apply(&t_prime, Val::vvar(l).into()),
            ),
            (_, Val::Lam(_, i, t_prime)) if v_applicable(t.as_ref()) => self.unify(
                l + 1,
                &self.v_app(t, Val::vvar(l).into(), *i),
                &self.closure_apply(&t_prime, Val::vvar(l).into()),
            ),
            (Val::Lam(_, i, t), _) if v_applicable(u.as_ref()) => self.unify(
                l + 1,
                &self.closure_apply(&t, Val::vvar(l).into()),
                &self.v_app(u, Val::vvar(l).into(), *i),
            ),
            (Val::Flex(m, sp), _) => self.solve(l, *m, sp.clone(), &u),
            (_, Val::Flex(m_prime, sp_prime)) => {
                self.solve(l, *m_prime, sp_prime.clone(), &t)
            }
            (Val::LiteralType, Val::LiteralType) => Ok(()),
            // 卡住的按名头与 String 宽松合一——get_global 族动态余定义域
            // (string_to_global_type 对未登记名卡住)的逃逸舱口;但只对
            // decl 表**未登记**的名字放行,已登记名按登记类型把关(U 型
            // builtin 的卡住值不再冒充 String 型)
            (Val::LiteralType, Val::Decl(x, _)) | (Val::Decl(x, _), Val::LiteralType) => {
                match self.decls.get(&x.data) {
                    None => Ok(()),
                    Some(entry) => {
                        let va = entry.va.clone();
                        self.unify(l, &Val::LiteralType.into(), &va)
                    }
                }
            }
            // 同名卡住 decl 按刚性风格逐实参合一
            (Val::Decl(x, sp), Val::Decl(x_prime, sp_prime)) if x == x_prime => {
                self.unify_sp(l, sp, sp_prime)
            }
            _ => Err(UnifyError), // Rigid mismatch error
        }
    }
}
