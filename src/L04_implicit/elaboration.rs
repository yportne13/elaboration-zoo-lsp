use colored::Colorize;

use crate::parser_lib::Span;

use super::{cxt::NameOrigin, empty_span, parser::syntax::{Either, Icit, Raw}, Closure, Cxt, Error, Infer, Ix, Tm, VTy, Val};



impl Infer {
    fn insert_go(&mut self, cxt: &Cxt, t: Tm, va: Val) -> (Tm, VTy) {
        match self.force(va) {
            Val::Pi(_, Icit::Impl, _, b) => {
                let m = self.fresh_meta(cxt);
                let mv = self.eval(&cxt.env, m.clone());
                self.insert_go(cxt, Tm::App(Box::new(t), Box::new(m), Icit::Impl), self.closure_apply(&b, mv))
            },
            va => (t, va)
        }
    }
    fn insert_t(&mut self, cxt: &Cxt, act: Result<(Tm, VTy), Error>) -> Result<(Tm, VTy), Error> {
        act.map(|(t, va)| {
            self.insert_go(cxt, t, va)
        })
    }
    fn insert(&mut self, cxt: &Cxt, act: Result<(Tm, VTy), Error>) -> Result<(Tm, VTy), Error> {
        act.and_then(|x| match x {
            (t @ Tm::Lam(_, Icit::Impl, _), va) => Ok((t, va)),
            (t, va) => self.insert_t(cxt, Ok((t, va))),
        })
    }
    fn insert_until_go(&mut self, cxt: &Cxt, name: Span<String>, t: Tm, va: Val) -> Result<(Tm, VTy), Error> {
        match self.force(va) {
            Val::Pi(x, Icit::Impl, a, b) => {
                if x.data == name.data {
                    Ok((t, Val::Pi(x, Icit::Impl, a, b)))
                } else {
                    let m = self.fresh_meta(cxt);
                    let mv = self.eval(&cxt.env, m.clone());
                    self.insert_until_go(cxt, name, Tm::App(Box::new(t), Box::new(m), Icit::Impl), self.closure_apply(&b, mv))
                }
            },
            _ => Err(Error(format!("no named implicit arg {:?}", name))),
        }
    }
    fn insert_until_name(&mut self, cxt: &Cxt, name: Span<String>, act: Result<(Tm, VTy), Error>) -> Result<(Tm, VTy), Error> {
        act.and_then(|(t, va)| self.insert_until_go(cxt, name, t, va))
    }
    fn check(&mut self, cxt: &Cxt, t: Raw, a: Val) -> Result<Tm, Error> {
        //println!("{} {:?} {} {:?}", "check".blue(), t, "==".blue(), a);
        match (t, self.force(a)) {
            // Check lambda expressions
            (
                Raw::Lam(x, i, t),
                Val::Pi(x_t, i_t, a, b_closure)
            ) if (i.clone(), i_t) == (Either::Name(x_t.clone()), Icit::Impl) || i == Either::Icit(i_t) => {
                let body = self.check(
                    &cxt.bind(x.clone(), *a),
                    *t,
                    self.closure_apply(&b_closure, Val::vvar(cxt.lvl)),
                )?;
                Ok(Tm::Lam(x, i_t, Box::new(body)))
            },
            (t, Val::Pi(x, Icit::Impl, a, b_closure)) => {
                let body = self.check(
                    &cxt.new_binder(x.clone(), *a),
                    t,
                    self.closure_apply(&b_closure, Val::vvar(cxt.lvl)),
                )?;
                Ok(Tm::Lam(x, Icit::Impl, Box::new(body)))
            },
            // Check let bindings
            (Raw::Let(x, a, t, u), a_prime) => {
                let a_checked = self.check(cxt, *a, Val::U)?;
                let va = self.eval(&cxt.env, a_checked.clone());
                let t_checked = self.check(cxt, *t, va.clone())?;
                let vt = self.eval(&cxt.env, t_checked.clone());
                let u_checked = self.check(&cxt.define(x.clone(), vt, va), *u, a_prime)?;
                Ok(Tm::Let(
                    x,
                    Box::new(a_checked),
                    Box::new(t_checked),
                    Box::new(u_checked),
                ))
            }

            // Handle holes
            (Raw::Hole, a) => Ok(self.fresh_meta(cxt)),

            // General case: infer type and unify
            (t, expected) => {
                let x = self.infer(cxt, t);
                let (t_inferred, inferred_type) = self.insert(cxt, x)?;
                self.unify_catch(cxt, expected, inferred_type)?;
                Ok(t_inferred)
            }
        }
    }
    pub fn infer(&mut self, cxt: &Cxt, t: Raw) -> Result<(Tm, Val), Error> {
        /*println!(
            "{} {:?} in {}",
            "infer".red(),
            t,
            cxt.types
                .iter()
                .map(|x| format!("{x:?}"))
                .reduce(|a, b| a + "\n" + &b)
                .unwrap_or(String::new())
        );*/
        match t {
            // Infer variable types
            Raw::Var(x) => {
                for (ix, (x_prime, name, a)) in cxt.types.iter().enumerate() {
                    if x == *x_prime && *name == NameOrigin::Source {
                        return Ok((Tm::Var(Ix(ix as u32)), a.clone()));
                    }
                }
                //Err(Error::NameNotInScope(x))
                Err(Error(format!("error name not in scope: {:?}", x)))
            }

            // Infer lambda expressions
            Raw::Lam(x, Either::Icit(i), t) => {
                let new_meta = self.fresh_meta(cxt);
                let a = self.eval(&cxt.env, new_meta);
                //TODO:below may be wrong
                let new_cxt = cxt.bind(x.clone(), a.clone());
                let infered = self.infer(&new_cxt, *t);
                let (t_inferred, b) = self.insert(&new_cxt, infered)?;
                let b_closure = self.close_val(cxt, b);
                Ok((
                    Tm::Lam(x.clone(), i, Box::new(t_inferred)),
                    Val::Pi(x, i, Box::new(a), b_closure),
                ))
            }

            Raw::Lam(x, Either::Name(_), t) => {
                Err(Error("infer named lambda".to_owned()))
            }

            // Infer function applications
            Raw::App(t, u, i) => {
                let (i, t, tty) = match i {
                    Either::Name(name) => {
                        let infered = self.infer(cxt, *t);
                        let (t, tty) = self.insert_until_name(cxt, name, infered)?;
                        (Icit::Impl, t, tty)
                    },
                    Either::Icit(Icit::Impl) => {
                        let (t, tty) = self.infer(cxt, *t)?;
                        (Icit::Impl, t, tty)
                    }
                    Either::Icit(Icit::Expl) => {
                        let infered = self.infer(cxt, *t);
                        let (t, tty) = self.insert_t(cxt, infered)?;
                        (Icit::Expl, t, tty)
                    }
                };
                //println!("{} {:?} -> {:?}", "infer___".red(), t, tty); //debug
                let (a, b_closure) = match self.force(tty) {
                    Val::Pi(_, i_t, a, b_closure) => if i == i_t {
                        (*a, b_closure)
                    } else {
                        return Err(Error(format!("icit mismatch {:?} {:?}", i, i_t)));
                    },
                    tty => {
                        let new_meta = self.fresh_meta(cxt);
                        let a = self.eval(&cxt.env, new_meta);
                        let b_closure = Closure(
                            cxt.env.clone(),
                            Box::new(
                                self.fresh_meta(&cxt.bind(empty_span("x".to_string()), a.clone())),
                            ),
                        );
                        self.unify_catch(
                            cxt,
                            Val::Pi(
                                empty_span("x".to_string()),
                                i,
                                Box::new(a.clone()),
                                b_closure.clone(),
                            ),
                            tty,
                        )?;
                        (a, b_closure)
                    }
                };
                let u_checked = self.check(cxt, *u, a)?;
                Ok((
                    Tm::App(Box::new(t), Box::new(u_checked.clone()), i),
                    self.closure_apply(&b_closure, self.eval(&cxt.env, u_checked)),
                ))
            }

            // Infer universe type
            Raw::U => Ok((Tm::U, Val::U)),

            // Infer dependent function types
            Raw::Pi(x, i, a, b) => {
                let a_checked = self.check(cxt, *a, Val::U)?;
                let b_checked = self.check(
                    &cxt.bind(x.clone(), self.eval(&cxt.env, a_checked.clone())),
                    *b,
                    Val::U,
                )?;
                Ok((Tm::Pi(x, i, Box::new(a_checked), Box::new(b_checked)), Val::U))
            }

            // Infer let bindings
            Raw::Let(x, a, t, u) => {
                let a_checked = self.check(cxt, *a, Val::U)?;
                let va = self.eval(&cxt.env, a_checked.clone());
                let t_checked = self.check(cxt, *t, va.clone())?;
                let vt = self.eval(&cxt.env, t_checked.clone());
                let (u_inferred, b) = self.infer(&cxt.define(x.clone(), vt.clone(), va), *u)?;
                Ok((
                    Tm::Let(
                        x,
                        Box::new(a_checked),
                        Box::new(t_checked),
                        Box::new(u_inferred),
                    ),
                    b,
                ))
            }

            // Infer holes
            Raw::Hole => {
                let new_meta = self.fresh_meta(cxt);
                let a = self.eval(&cxt.env, new_meta);
                let t = self.fresh_meta(cxt);
                Ok((t, a))
            }
        }
    }
}