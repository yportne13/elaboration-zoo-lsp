use colored::Colorize;

use crate::{L04_implicit::empty_span, list::List};

use super::{
    Infer, Lvl, MetaEntry, MetaVar, Spine, Tm, UnifyError, Val, lvl2ix, parser::syntax::Icit,
};

use std::collections::HashMap;

#[derive(Debug, Clone)]
struct PartialRenaming {
    dom: Lvl,               // size of Γ
    cod: Lvl,               // size of Δ
    ren: HashMap<u32, Lvl>, // mapping from Δ vars to Γ vars
}

fn lift(pr: PartialRenaming) -> PartialRenaming {
    let mut new_ren = pr.ren.clone();
    new_ren.insert(pr.cod.0, pr.dom);

    PartialRenaming {
        dom: pr.dom + 1, // increment dom
        cod: pr.cod + 1, // increment cod
        ren: new_ren,    // update ren with the new mapping
    }
}

fn lams(l: List<Icit>, t: Tm) -> Tm {
    fn go(x: u32, l: List<Icit>, t: Tm) -> Tm {
        if l.head().is_none() {
            t
        } else {
            let var_name = format!("x{}", x + 1);
            Tm::Lam(
                empty_span(var_name),
                *l.head().unwrap(),
                Box::new(go(x + 1, l.tail(), t)),
            )
        }
    }
    go(0, l, t)
}

impl Infer {
    fn invert_go(&self, sp: Spine) -> Result<(Lvl, HashMap<u32, Lvl>), UnifyError> {
        match sp {
            List { head: None } => Ok((Lvl(0), HashMap::new())),
            a => {
                let (dom, mut ren) = self.invert_go(a.tail())?;
                match self.force(a.head().unwrap().0.clone()) {
                    Val::Rigid(x, List { head: None }) if !ren.contains_key(&x.0) => {
                        ren.insert(x.0, dom);
                        Ok((dom + 1, ren))
                    }
                    _ => Err(UnifyError)
                }
            }
        }
    }
    fn invert(&self, gamma: Lvl, sp: Spine) -> Result<PartialRenaming, UnifyError> {
        //println!("{} {:?} {:?}", "invert".green(), gamma, sp);
        let (dom, ren) = self.invert_go(sp)?;

        Ok(PartialRenaming {
            dom,
            cod: gamma,
            ren,
        })
    }
    fn rename_go_sp(
        &self,
        m: MetaVar,
        pren: &PartialRenaming,
        t: Tm,
        sp: &Spine,
    ) -> Result<Tm, UnifyError> {
        match sp {
            List { head: None } => Ok(t),
            a => {
                let t = self.rename_go_sp(m, pren, t, &a.tail())?;
                let u = self.rename_go(m, pren, a.head().unwrap().0.clone())?;
                Ok(Tm::App(Box::new(t), Box::new(u), a.head().unwrap().1))
            }
        }
    }
    fn rename_go(&self, m: MetaVar, pren: &PartialRenaming, t: Val) -> Result<Tm, UnifyError> {
        match self.force(t) {
            Val::Flex(m_prime, sp) if m == m_prime => Err(UnifyError), // occurs check
            Val::Flex(m_prime, sp) => {
                let t = Tm::Meta(m_prime);
                self.rename_go_sp(m, pren, t, &sp)
            }
            Val::Rigid(x, sp) => match pren.ren.get(&x.0) {
                None => Err(UnifyError), // scope error
                Some(x_prime) => {
                    let t = Tm::Var(lvl2ix(pren.dom, *x_prime));
                    self.rename_go_sp(m, pren, t, &sp)
                }
            },
            Val::Lam(x, i, closure) => {
                let t = self.rename_go(
                    m,
                    &lift(pren.clone()),
                    self.closure_apply(&closure, Val::vvar(pren.cod)),
                )?;
                Ok(Tm::Lam(x, i, Box::new(t)))
            }
            Val::Pi(x, i, a, closure) => {
                let a = self.rename_go(m, pren, *a)?;
                let b = self.rename_go(
                    m,
                    &lift(pren.clone()),
                    self.closure_apply(&closure, Val::vvar(pren.cod)),
                )?;
                Ok(Tm::Pi(x, i, Box::new(a), Box::new(b)))
            }
            Val::U => Ok(Tm::U),
        }
    }

    fn rename(&self, m: MetaVar, pren: PartialRenaming, v: Val) -> Result<Tm, UnifyError> {
        //println!("{} {:?} {:?} {:?}", "rename".green(), m, pren, v);
        self.rename_go(m, &pren, v)
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
        let pren = self.invert(gamma, sp.clone())?;
        let rhs = self.rename(m, pren.clone(), rhs)?;
        let solution = self.eval(
            &List::new(),
            lams(
                sp.iter()//TODO:this may be wrong?
                    .map(|x| x.1)
                    .fold(List::new(), |acc, x| acc.prepend(x)),
                rhs,
            ),
        );
        self.meta[m.0 as usize] = MetaEntry::Solved(solution);
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

    pub fn unify(&mut self, l: Lvl, t: Val, u: Val) -> Result<(), UnifyError> {
        //println!("{} {:?} {} {:?}", "unify".yellow(), t, "==".yellow(), u); //debug
        let t = self.force(t);
        let u = self.force(u);
        /*println!(
            "{} {:?} {} {:?}",
            "unify after force".yellow(),
            t,
            "==".yellow(),
            u
        );*/
 //debug

        match (&t, &u) {
            // Lambda cases
            (Val::Lam(_, _, t_closure), Val::Lam(_, _, u_closure)) => self.unify(
                l + 1,
                self.closure_apply(t_closure, Val::vvar(l)),
                self.closure_apply(u_closure, Val::vvar(l)),
            ),
            (t, Val::Lam(_, i, u_closure)) => self.unify(
                l + 1,
                self.v_app(t.clone(), Val::vvar(l), *i),
                self.closure_apply(u_closure, Val::vvar(l)),
            ),
            (Val::Lam(_, i, t_closure), t_t) => self.unify(
                l + 1,
                self.closure_apply(t_closure, Val::vvar(l)),
                self.v_app(u.clone(), Val::vvar(l), *i),
            ),

            // Universe case
            (Val::U, Val::U) => Ok(()),

            // Pi case
            (Val::Pi(x, i, a, b_closure), Val::Pi(x_prime, i_prime, a_prime, b_prime_closure))
                if i == i_prime =>
            {
                self.unify(l, *a.clone(), *a_prime.clone())?;
                self.unify(
                    l + 1,
                    self.closure_apply(b_closure, Val::vvar(l)),
                    self.closure_apply(b_prime_closure, Val::vvar(l)),
                )
            }

            // Rigid variables
            (Val::Rigid(x, sp), Val::Rigid(x_prime, sp_prime)) if x == x_prime => {
                self.unify_sp(l, sp, sp_prime)
            }

            // Flexible variables
            (Val::Flex(m, sp), Val::Flex(m_prime, sp_prime)) if m == m_prime => {
                self.unify_sp(l, sp, sp_prime)
            }

            // Solve cases
            (Val::Flex(m, sp), _) => self.solve(l, *m, sp.clone(), u),
            (_, Val::Flex(m_prime, sp_prime)) => self.solve(l, *m_prime, sp_prime.clone(), t),

            // Default case
            _ => Err(UnifyError), // Rigid mismatch error
        }
    }
}
