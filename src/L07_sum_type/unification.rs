//! Unification。骨架 = elaboration-zoo 07 的 meta 求解器（invert / prune /
//! rename / solve / intersect），在此基础上：
//! - 全局引用 `Val::Decl` 作为中性头参与（与 Rigid 同型处理）；
//! - Sum / SumCase 按参数逐槽合一（索引等式在此生效）；
//! - 卡住的 `Val::Match`：先尝试归约（scrutinee 是构造子值时用 `eval_aux`
//!   消掉 match），再接受严格的 eta（每个分支都是通配且分支体就是
//!   scrutinee 本身），其余失败——防止把任意 `f x` 证成 `x`；
//! - `rename` 对 Match 的分支体做"fresh rigid 槽 + 简化 decl 表求值再
//!   rename"（L07 在这里是 TODO/透传，是正确的关键）。

use std::collections::{HashMap, HashSet};

use crate::list::List;

use super::{
    Infer, Lvl, MetaEntry, MetaVar, PatternDetail, Spine, Tm, UnifyError, Val, VTy,
    cxt::{Cxt, Decls},
    lvl2ix,
    parser::syntax::Icit,
    syntax::Pruning,
    Compiler, Ix,
};

#[derive(Debug, Clone)]
struct PartialRenaming {
    occ: Option<MetaVar>,
    dom: Lvl,               // Γ 的大小
    cod: Lvl,               // Δ 的大小
    ren: HashMap<u32, Lvl>, // Δ 变量 → Γ 变量
}

fn lift(pr: &PartialRenaming) -> PartialRenaming {
    let mut new_ren = pr.ren.clone();
    new_ren.insert(pr.cod.0, pr.dom);
    PartialRenaming {
        occ: pr.occ,
        dom: pr.dom + 1,
        cod: pr.cod + 1,
        ren: new_ren,
    }
}

fn skip(pr: &PartialRenaming) -> PartialRenaming {
    PartialRenaming {
        occ: pr.occ,
        dom: pr.dom,
        cod: pr.cod + 1,
        ren: pr.ren.clone(),
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
        decl: &Decls,
        sp: Spine,
    ) -> Result<(Lvl, HashMap<u32, Lvl>, HashSet<u32>, List<(Lvl, Icit)>), UnifyError> {
        match sp {
            List { head: None, .. } => Ok((Lvl(0), HashMap::new(), HashSet::new(), List::new())),
            a => {
                let (dom, mut ren, mut nlvars, fsp) = self.invert_go(decl, a.tail())?;
                match self.force(decl, a.head().unwrap().0.clone()) {
                    Val::Rigid(x, List { head: None, .. }) => {
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
        decl: &Decls,
        gamma: Lvl,
        sp: Spine,
    ) -> Result<(PartialRenaming, Option<Pruning>), UnifyError> {
        let (dom, ren, nlvars, fsp) = self.invert_go(decl, sp)?;
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
        decl: &Decls,
        pr: &Pruning,
        pren: &PartialRenaming,
        a: Val,
    ) -> Result<Tm, UnifyError> {
        match (pr, self.force(decl, a)) {
            (List { head: None, .. }, a) => self.rename(decl, pren, a),
            (list, Val::Pi(x, i, a, b)) if list.head().unwrap().is_some() => {
                let a = self.rename(decl, pren, *a)?;
                let b = self.closure_apply(decl, &b, Val::vvar(pren.cod));
                let b = self.prune_ty_go(decl, &list.tail(), &lift(pren), b)?;
                Ok(Tm::Pi(x, i, Box::new(a), Box::new(b)))
            }
            (list, Val::Pi(x, i, _, b)) if list.head().unwrap().is_none() => {
                let b = self.closure_apply(decl, &b, Val::vvar(pren.cod));
                self.prune_ty_go(decl, &list.tail(), &skip(pren), b)
            }
            _ => Err(UnifyError),
        }
    }

    fn prune_ty(&mut self, decl: &Decls, pr: &Pruning, a: Val) -> Result<Tm, UnifyError> {
        self.prune_ty_go(
            decl,
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

    fn prune_meta(&mut self, decl: &Decls, pruning: Pruning, m: MetaVar) -> Result<MetaVar, UnifyError> {
        let mty = match self.meta[m.0 as usize] {
            MetaEntry::Unsolved(ref a) => a.clone(),
            _ => unreachable!(),
        };

        let prune_ty = self.prune_ty(decl, &pruning, mty.clone())?;
        let prunedty = self.eval(decl, &List::new(), prune_ty);
        let m_prime = self.new_meta(prunedty);

        let solution = self.eval(
            decl,
            &List::new(),
            self.lams(
                decl,
                Lvl(pruning.len() as u32),
                mty.clone(),
                Tm::AppPruning(Box::new(Tm::Meta(m_prime)), pruning),
            ),
        );

        self.meta[m.0 as usize] = MetaEntry::Solved(solution, mty);
        Ok(m_prime)
    }

    fn prune_vflex_go(
        &mut self,
        decl: &Decls,
        pren: &PartialRenaming,
        sp: Spine,
    ) -> Result<(List<(Option<Tm>, Icit)>, SpinePruneStatus), UnifyError> {
        if sp.head().is_none() {
            Ok((List::new(), SpinePruneStatus::OKRenaming))
        } else {
            let (sp_rest, status) = self.prune_vflex_go(decl, pren, sp.tail())?;
            match self.force(decl, sp.head().unwrap().0.clone()) {
                Val::Rigid(x, List { head: None, .. }) => match (pren.ren.get(&x.0), status) {
                    (Some(x), _) => Ok((
                        sp_rest.prepend((Some(Tm::Var(lvl2ix(pren.dom, *x))), sp.head().unwrap().1)),
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
                        let t = self.rename(decl, pren, t)?;
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
        decl: &Decls,
        pren: &PartialRenaming,
        m: MetaVar,
        sp: Spine,
    ) -> Result<Tm, UnifyError> {
        let (sp, status) = self.prune_vflex_go(decl, pren, sp)?;

        let m_prime = match status {
            SpinePruneStatus::OKRenaming | SpinePruneStatus::OKNonRenaming => {
                match self.meta[m.0 as usize] {
                    MetaEntry::Unsolved(_) => m,
                    _ => unreachable!(),
                }
            }
            SpinePruneStatus::NeedsPruning => {
                self.prune_meta(decl, sp.map(|(mt, i)| mt.as_ref().map(|_| *i)), m)?
            }
        };

        let t = sp.iter().fold(Tm::Meta(m_prime), |t, (mu, i)| {
            if let Some(u) = mu {
                Tm::App(Box::new(t), Box::new(u.clone()), *i)
            } else {
                t
            }
        });

        Ok(t)
    }

    fn rename_sp(&mut self, decl: &Decls, pren: &PartialRenaming, t: Tm, sp: &Spine) -> Result<Tm, UnifyError> {
        match sp {
            List { head: None, .. } => Ok(t),
            a => {
                let t = self.rename_sp(decl, pren, t, &a.tail())?;
                let u = self.rename(decl, pren, a.head().unwrap().0.clone())?;
                Ok(Tm::App(Box::new(t), Box::new(u), a.head().unwrap().1))
            }
        }
    }

    fn rename(&mut self, decl: &Decls, pren: &PartialRenaming, t: Val) -> Result<Tm, UnifyError> {
        match self.force(decl, t) {
            Val::Flex(m_prime, sp) => match pren.occ {
                Some(m) if m == m_prime => Err(UnifyError),
                _ => self.prune_vflex(decl, pren, m_prime, sp),
            },
            Val::Rigid(x, sp) => match pren.ren.get(&x.0) {
                None => Err(UnifyError), // scope error
                Some(x_prime) => {
                    let t = Tm::Var(lvl2ix(pren.dom, *x_prime));
                    self.rename_sp(decl, pren, t, &sp)
                }
            },
            Val::Decl(name, sp) => self.rename_sp(decl, pren, Tm::Decl(name), &sp),
            Val::Obj(x, name, sp) => {
                let t = Tm::Obj(Box::new(self.rename(decl, pren, *x)?), name);
                self.rename_sp(decl, pren, t, &sp)
            }
            Val::Lam(x, i, closure) => {
                let t = self.rename(
                    decl,
                    &lift(pren),
                    self.closure_apply(decl, &closure, Val::vvar(pren.cod)),
                )?;
                Ok(Tm::Lam(x, i, Box::new(t)))
            }
            Val::Pi(x, i, a, closure) => {
                let a = self.rename(decl, pren, *a)?;
                let b = self.rename(
                    decl,
                    &lift(pren),
                    self.closure_apply(decl, &closure, Val::vvar(pren.cod)),
                )?;
                Ok(Tm::Pi(x, i, Box::new(a), Box::new(b)))
            }
            Val::U => Ok(Tm::U),
            Val::LiteralType => Ok(Tm::LiteralType),
            Val::LiteralIntro(x) => Ok(Tm::LiteralIntro(x)),
            Val::Prim => Ok(Tm::Prim),
            Val::Sum(name, params, cases) => {
                let new_params = params
                    .into_iter()
                    .map(|(n, v, t, i)| {
                        Ok((n, self.rename(decl, pren, v)?, self.rename(decl, pren, t)?, i))
                    })
                    .collect::<Result<_, UnifyError>>()?;
                Ok(Tm::Sum(name, new_params, cases))
            }
            Val::SumCase {
                typ,
                case_name,
                datas,
            } => {
                let typ = self.rename(decl, pren, *typ)?;
                let datas = datas
                    .into_iter()
                    .map(|(n, v, i)| Ok((n, self.rename(decl, pren, v)?, i)))
                    .collect::<Result<_, UnifyError>>()?;
                Ok(Tm::SumCase {
                    typ: Box::new(typ),
                    case_name,
                    datas,
                })
            }
            Val::Match(val, env, cases) => {
                // 分支体是裸 Tm：先在"捕获 env + fresh rigid 槽"下重新求值
                // （简化 decl 表防重展开），再在 lift 过的 renaming 下 rename
                let val = self.rename(decl, pren, *val)?;
                let declb = super::simpl_decl(decl);
                let cases = cases
                    .iter()
                    .map(|(pat, tm)| {
                        let count = pat.bind_count();
                        let (env, pren) = (0..count).fold(
                            (env.clone(), pren.clone()),
                            |(env, pren), _| (env.prepend(Val::vvar(pren.cod)), lift(&pren)),
                        );
                        let body = self.rename(decl, &pren, self.eval(&declb, &env, tm.clone()))?;
                        Ok((pat.clone(), body))
                    })
                    .collect::<Result<_, UnifyError>>()?;
                Ok(Tm::Match(Box::new(val), cases))
            }
        }
    }

    fn lams_go(&self, decl: &Decls, l: Lvl, t: Tm, a: VTy, l_prime: Lvl) -> Tm {
        if l == l_prime {
            t
        } else {
            match self.force(decl, a) {
                Val::Pi(span, icit, _, closure) => Tm::Lam(
                    span,
                    icit,
                    Box::new(self.lams_go(
                        decl,
                        l,
                        t,
                        self.closure_apply(decl, &closure, Val::vvar(l_prime)),
                        l_prime + 1,
                    )),
                ),
                _ => unreachable!(),
            }
        }
    }

    fn lams(&self, decl: &Decls, l: Lvl, a: VTy, t: Tm) -> Tm {
        self.lams_go(decl, l, t, a, Lvl(0))
    }

    fn solve(&mut self, decl: &Decls, gamma: Lvl, m: MetaVar, sp: Spine, rhs: Val) -> Result<(), UnifyError> {
        let (pren, prune_non_linear) = self.invert(decl, gamma, sp)?;
        self.solve_with_pren(decl, m, pren, prune_non_linear, rhs)
    }

    fn solve_with_pren(
        &mut self,
        decl: &Decls,
        m: MetaVar,
        pren: PartialRenaming,
        prune_non_linear: Option<Pruning>,
        rhs: Val,
    ) -> Result<(), UnifyError> {
        let mty = match self.meta[m.0 as usize] {
            MetaEntry::Unsolved(ref a) => a.clone(),
            _ => unreachable!(),
        };

        // spine 非线性时，检查这些参数能从 meta 类型里剪掉（保证解是良型的）
        if let Some(pr) = prune_non_linear {
            self.prune_ty(decl, &pr, mty.clone())?;
        }

        let rhs = self.rename(
            decl,
            &PartialRenaming {
                occ: Some(m),
                ..pren
            },
            rhs,
        )?;
        let solution = self.eval(decl, &List::new(), self.lams(decl, pren.dom, mty.clone(), rhs));
        self.meta[m.0 as usize] = MetaEntry::Solved(solution, mty);

        Ok(())
    }

    fn unify_sp(
        &mut self,
        decl: &Decls,
        l: Lvl,
        cxt: &Cxt,
        sp: &Spine,
        sp_prime: &Spine,
    ) -> Result<(), UnifyError> {
        match (sp, sp_prime) {
            (List { head: None, .. }, List { head: None, .. }) => Ok(()),
            (a, b) if a.head().is_some() && b.head().is_some() => {
                self.unify_sp(decl, l, cxt, &a.tail(), &b.tail())?;
                self.unify(
                    decl,
                    l,
                    cxt,
                    a.head().unwrap().0.clone(),
                    b.head().unwrap().0.clone(),
                )
            }
            _ => Err(UnifyError),
        }
    }

    fn flex_flex(
        &mut self,
        decl: &Decls,
        gamma: Lvl,
        m: MetaVar,
        sp: Spine,
        m_prime: MetaVar,
        sp_prime: Spine,
    ) -> Result<(), UnifyError> {
        let mut go = |this: &mut Self,
                      m: MetaVar,
                      sp: Spine,
                      m_prime: MetaVar,
                      sp_prime: Spine|
         -> Result<(), UnifyError> {
            match this.invert(decl, gamma, sp.clone()) {
                Err(UnifyError) => this.solve(decl, gamma, m_prime, sp_prime, Val::Flex(m, sp)),
                Ok((pren, p1)) => this.solve_with_pren(decl, m, pren, p1, Val::Flex(m_prime, sp_prime)),
            }
        };

        // 先试一方，失败再试另一方。只按 spine 长度选一个方向，会在
        // "长 spine 含非 rigid 项（变量槽被精化成构造子值）"时漏掉
        // 可行方向（test5 的内层 match 场景）。
        // 第一次尝试可能已 solve 部分 meta 才失败，反向尝试前回滚。
        let snap = self.meta.clone();
        let (m1, sp1, m2, sp2) = if sp.len() <= sp_prime.len() {
            (m, sp, m_prime, sp_prime)
        } else {
            (m_prime, sp_prime, m, sp)
        };
        match go(self, m1, sp1.clone(), m2, sp2.clone()) {
            Ok(()) => Ok(()),
            Err(_) => {
                self.meta = snap;
                match go(self, m2, sp2, m1, sp1) {
                    Ok(()) => Ok(()),
                    Err(e) => Err(e),
                }
            }
        }
    }

    fn intersect_go(&mut self, decl: &Decls, sp: Spine, sp_prime: Spine) -> Option<List<Option<Icit>>> {
        match (sp, sp_prime) {
            (List { head: None, .. }, List { head: None, .. }) => Some(List::new()),
            (a, b) if a.head().is_some() && b.head().is_some() => {
                match (
                    self.force(decl, a.head().unwrap().0.clone()),
                    self.force(decl, b.head().unwrap().0.clone()),
                ) {
                    (
                        Val::Rigid(x, List { head: None, .. }),
                        Val::Rigid(x_prime, List { head: None, .. }),
                    ) => self.intersect_go(decl, a.tail(), b.tail()).map(|l| {
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
        decl: &Decls,
        l: Lvl,
        cxt: &Cxt,
        m: MetaVar,
        sp: Spine,
        sp_prime: Spine,
    ) -> Result<(), UnifyError> {
        match self.intersect_go(decl, sp.clone(), sp_prime.clone()) {
            None => self.unify_sp(decl, l, cxt, &sp, &sp_prime),
            Some(pr) if pr.iter().any(|x| x.is_none()) => {
                self.prune_meta(decl, pr, m)?;
                Ok(())
            }
            Some(_) => Ok(()),
        }
    }

    pub fn unify(
        &mut self,
        decl: &Decls,
        l: Lvl,
        cxt: &Cxt,
        t: Val,
        u: Val,
    ) -> Result<(), UnifyError> {
        // 递归深度防护：索引槽互相嵌入的构造子值比较会无限递归
        let fuel = self.unify_fuel.get();
        if fuel == 0 {
            return Err(UnifyError);
        }
        self.unify_fuel.set(fuel - 1);
        let t = self.force(decl, t);
        let u = self.force(decl, u);

        match (&t, &u) {
            (Val::U, Val::U) => Ok(()),
            (Val::Pi(x, i, a, b), Val::Pi(x_prime, i_prime, a_prime, b_prime)) if i == i_prime => {
                self.unify(decl, l, cxt, (**a).clone(), (**a_prime).clone())?;
                self.unify(
                    decl,
                    l + 1,
                    &cxt.bind(x.clone(), self.quote(decl, cxt.lvl, (**a).clone()), (**a).clone()),
                    self.closure_apply(decl, b, Val::vvar(l)),
                    self.closure_apply(decl, b_prime, Val::vvar(l)),
                )
            }
            (Val::Rigid(x, sp), Val::Rigid(x_prime, sp_prime)) if x == x_prime => {
                self.unify_sp(decl, l, cxt, sp, sp_prime)
            }
            // 全局引用：同名比 spine，不同名失败（force 已展开可展开的）
            (Val::Decl(a, sp), Val::Decl(b, sp_prime)) if a == b => {
                self.unify_sp(decl, l, cxt, sp, sp_prime)
            }
            (Val::Flex(m, sp), Val::Flex(m_prime, sp_prime)) if m == m_prime => {
                self.intersect(decl, l, cxt, *m, sp.clone(), sp_prime.clone())
            }
            (Val::Flex(m, sp), Val::Flex(m_prime, sp_prime)) => {
                self.flex_flex(decl, l, *m, sp.clone(), *m_prime, sp_prime.clone())
            }
            (Val::Lam(_, _, b), Val::Lam(_, _, b_prime)) => self.unify(
                decl,
                l + 1,
                cxt,
                self.closure_apply(decl, b, Val::vvar(l)),
                self.closure_apply(decl, b_prime, Val::vvar(l)),
            ),
            (t, Val::Lam(_, i, b_prime)) => self.unify(
                decl,
                l + 1,
                cxt,
                self.v_app(decl, t.clone(), Val::vvar(l), *i),
                self.closure_apply(decl, b_prime, Val::vvar(l)),
            ),
            (Val::Lam(_, i, b), t_prime) => self.unify(
                decl,
                l + 1,
                cxt,
                self.closure_apply(decl, b, Val::vvar(l)),
                self.v_app(decl, t_prime.clone(), Val::vvar(l), *i),
            ),
            (Val::Flex(m, sp), _) => self.solve(decl, l, *m, sp.clone(), u.clone()),
            (_, Val::Flex(m_prime, sp_prime)) => self.solve(decl, l, *m_prime, sp_prime.clone(), t.clone()),
            (Val::LiteralType, Val::LiteralType) => Ok(()),
            // 字符串字面量与内建 Prim 的宽松比较（保持 L07 时代行为）
            (Val::LiteralType, Val::Prim) | (Val::Prim, Val::LiteralType) => Ok(()),
            (Val::Prim, Val::Prim) => Ok(()),
            // Sum：同名即逐参数（含索引）合一
            (Val::Sum(a, params_a, _), Val::Sum(b, params_b, _)) if a.data == b.data => {
                for (a, b) in params_a.iter().zip(params_b.iter()) {
                    self.unify(decl, l, cxt, a.1.clone(), b.1.clone())?;
                }
                Ok(())
            }
            // SumCase：同构造子才比；只比 datas（L07a 同款）。**不比 typ**：
            // typ 的索引槽就是这些值自身的构造子形态（succ ?l 的 typ 里
            // len 槽是 succ ?l），比 typ 必然在互相引用上深递归；
            // 索引等式的比较发生在**外层 Sum-Sum 的参数 zip**里。
            (
                Val::SumCase {
                    case_name: ca,
                    datas: params_a,
                    ..
                },
                Val::SumCase {
                    case_name: cb,
                    datas: params_b,
                    ..
                },
            ) if ca.data == cb.data => {
                for (a, b) in params_a.iter().zip(params_b.iter()) {
                    self.unify(decl, l, cxt, a.1.clone(), b.1.clone())?;
                }
                Ok(())
            }
            // 卡住的 match vs 卡住的 match：scrutinee 合一 + 分支一一对应
            (Val::Match(s1, env1, cases1), Val::Match(s2, env2, cases2)) => {
                self.unify(decl, l, cxt, (**s1).clone(), (**s2).clone())?;
                if cases1.len() != cases2.len() {
                    return Err(UnifyError);
                }
                let declb = super::simpl_decl(decl);
                for ((p1, b1), (p2, b2)) in cases1.iter().zip(cases2.iter()) {
                    if p1 != p2 {
                        return Err(UnifyError);
                    }
                    let count = p1.bind_count();
                    let env1 = (0..count)
                        .fold(env1.clone(), |env, i| env.prepend(Val::vvar(l + i)));
                    let env2 = (0..count)
                        .fold(env2.clone(), |env, i| env.prepend(Val::vvar(l + i)));
                    let v1 = self.eval(&declb, &env1, b1.clone());
                    let v2 = self.eval(&declb, &env2, b2.clone());
                    self.unify(decl, l + count, cxt, v1, v2)?;
                }
                Ok(())
            }
            // 卡住的 match vs 其它：先尝试归约，再接受严格 eta
            (Val::Match(s, env_m, cases), other) | (other, Val::Match(s, env_m, cases)) => {
                let s_forced = self.force(decl, (**s).clone());
                if matches!(s_forced, Val::SumCase { .. }) {
                    if let Some((tm, env)) =
                        Compiler::eval_aux(self, decl, s_forced.clone(), env_m, cases)
                    {
                        let reduced = self.eval(decl, &env, tm);
                        return self.unify(decl, l, cxt, reduced, other.clone());
                    }
                }
                match (s_forced, other) {
                    // 只接受真 eta：每个分支都是通配且分支体就是 scrutinee 本身。
                    // 无条件接受会把 `f x` 证成 `x`。
                    (Val::Rigid(x, sp), Val::Rigid(y, sp2))
                        if x == *y && sp.is_empty() && sp2.is_empty() =>
                    {
                        let is_eta = !cases.is_empty()
                            && cases.iter().all(|(pat, body)| {
                                matches!(pat, PatternDetail::Any(..) | PatternDetail::Bind(_))
                                    && matches!(body, Tm::Var(Ix(0)))
                            });
                        if is_eta {
                            Ok(())
                        } else {
                            Err(UnifyError)
                        }
                    }
                    _ => Err(UnifyError),
                }
            }
            _ => Err(UnifyError),
        }
    }
}
