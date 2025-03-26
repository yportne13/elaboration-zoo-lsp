use colored::Colorize;
use parser::syntax::Raw;

use crate::list::List;
use crate::parser_lib::Span;

mod parser;
/*
#[derive(Debug, Clone, Copy, PartialEq)]
struct MetaVar(u32);

#[derive(Debug)]
enum MetaEntry {
    Solved(Val),
    Unsolved,
}

#[derive(Debug, Clone, Copy)]
struct Ix(u32);

#[derive(Debug, Clone)]
enum BD {
    Bound,
    Defined,
}

#[derive(Debug, Clone)]
enum Tm {
    Var(Ix),
    Lam(Span<String>, Box<Tm>),
    App(Box<Tm>, Box<Tm>),
    U,
    Pi(Span<String>, Box<Ty>, Box<Ty>),
    Let(Span<String>, Box<Ty>, Box<Tm>, Box<Tm>),
    Meta(MetaVar),
    InsertedMeta(MetaVar, List<BD>),
}

type Ty = Tm;

#[derive(Debug, Clone, Copy, PartialEq)]
struct Lvl(u32);

impl Add<u32> for Lvl {
    type Output = Lvl;
    fn add(self, rhs: u32) -> Lvl {
        Lvl(self.0 + rhs)
    }
}

type Env = List<Val>;
type Spine = List<Val>;

#[derive(Debug, Clone)]
struct Closure(Env, Box<Tm>);

#[derive(Debug, Clone)]
enum Val {
    Flex(MetaVar, Spine),
    Rigid(Lvl, Spine),
    Lam(Span<String>, Closure),
    Pi(Span<String>, Box<Val>, Closure),
    U,
}

type VTy = Val;

impl Val {
    fn vvar(x: Lvl) -> Self {
        Val::Rigid(x, List::new())
    }

    fn vmeta(m: MetaVar) -> Self {
        Val::Flex(m, List::new())
    }
}

fn lvl2ix(l: Lvl, x: Lvl) -> Ix {
    Ix(l.0 - x.0 - 1)
}

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
        dom: Lvl(pr.dom.0 + 1), // increment dom
        cod: Lvl(pr.cod.0 + 1), // increment cod
        ren: new_ren,           // update ren with the new mapping
    }
}

use std::ops::Add;

#[derive(Debug)]
struct UnifyError;

fn empty_span<T>(data: T) -> Span<T> {
    Span {
        data,
        start_offset: 0,
        end_offset: 0,
        path_id: 0,
    }
}

#[derive(Debug)]
pub struct Error(String);

fn lams(l: Lvl, t: Tm) -> Tm {
    fn go(x: u32, l: Lvl, t: Tm) -> Tm {
        if x == l.0 {
            t
        } else {
            let var_name = format!("x{}", x + 1);
            Tm::Lam(empty_span(var_name), Box::new(go(x + 1, l, t)))
        }
    }
    go(0, l, t)
}

type Types = List<(Span<String>, Val)>;

#[derive(Debug)]
struct Cxt {
    env: Env,      // Used for evaluation
    lvl: Lvl,      // Used for unification
    types: Types,  // Used for raw name lookup and pretty printing
    bds: List<BD>, // Used for fresh meta creation
}

impl Cxt {
    fn empty() -> Self {
        Cxt {
            env: List::new(),
            lvl: Lvl(0),
            types: List::new(),
            bds: List::new(),
        }
    }

    fn bind(&self, x: Span<String>, a: Val) -> Self {
        //println!("{} {x:?} {a:?} at {}", "bind".bright_purple(), self.lvl.0);
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl)),
            lvl: self.lvl + 1,
            types: self.types.prepend((x, a)),
            bds: self.bds.prepend(BD::Bound),
        }
    }

    fn define(&self, x: Span<String>, t: Val, a: Val) -> Self {
        Cxt {
            env: self.env.prepend(t),
            lvl: self.lvl + 1,
            types: self.types.prepend((x, a)),
            bds: self.bds.prepend(BD::Defined),
        }
    }
}

struct Infer {
    meta: Vec<MetaEntry>,
}

impl Infer {
    pub fn new() -> Self {
        Self { meta: vec![] }
    }
    fn fresh_meta(&mut self, cxt: &Cxt) -> Tm {
        self.meta.push(MetaEntry::Unsolved);
        Tm::InsertedMeta(MetaVar(self.meta.len() as u32 - 1), cxt.bds.clone())
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
        let pren = self.invert(gamma, sp)?;
        let rhs = self.rename(m, pren.clone(), rhs)?;
        let solution = self.eval(&List::new(), lams(pren.dom, rhs));
        self.meta[m.0 as usize] = MetaEntry::Solved(solution);
        Ok(())
    }
    fn lookup_meta(&self, m: MetaVar) -> &MetaEntry {
        &self.meta[m.0 as usize]
    }
    fn force(&self, t: Val) -> Val {
        //println!("{} {:?}", "force".red(), t);
        match t {
            Val::Flex(m, sp) => match self.lookup_meta(m) {
                MetaEntry::Solved(t_solved) => self.force(self.v_app_sp(t_solved.clone(), sp)),
                MetaEntry::Unsolved => Val::Flex(m, sp),
            },
            _ => t,
        }
    }
    fn v_meta(&self, m: MetaVar) -> Val {
        match self.lookup_meta(m) {
            MetaEntry::Solved(v) => v.clone(),
            MetaEntry::Unsolved => Val::vmeta(m),
        }
    }

    fn closure_apply(&self, closure: &Closure, u: Val) -> Val {
        //println!("{} {:?} {:?}", "closure apply".yellow(), closure, u);
        self.eval(&closure.0.prepend(u), *closure.1.clone())
    }

    fn v_app(&self, t: Val, u: Val) -> Val {
        match t {
            Val::Lam(_, closure) => self.closure_apply(&closure, u),
            Val::Flex(m, sp) => Val::Flex(m, sp.prepend(u)),
            Val::Rigid(x, sp) => Val::Rigid(x, sp.prepend(u)),
            _ => panic!("impossible"),
        }
    }

    fn v_app_sp(&self, t: Val, spine: Spine) -> Val {
        spine.iter().fold(t, |acc, u| self.v_app(acc, u.clone()))
    }

    fn v_app_bds(&self, env: &Env, v: Val, bds: &List<BD>) -> Val {
        //println!("{} {:?} {:?}", "v_app_bds".green(), v, bds);
        match (env, bds) {
            (List { head: None }, List { head: None }) => v,
            (a, b) if a.head().is_some() && matches!(b.head(), Some(BD::Bound)) => self.v_app(
                self.v_app_bds(&a.tail(), v, &bds.tail()),
                a.head().unwrap().clone(),
            ),
            (a, b) if a.head().is_some() && matches!(b.head(), Some(BD::Defined)) => {
                self.v_app_bds(&a.tail(), v, &bds.tail())
            }
            _ => panic!("impossible"),
        }
    }

    fn invert(&self, gamma: Lvl, sp: Spine) -> Result<PartialRenaming, UnifyError> {
        //println!("{} {:?} {:?}", "invert".green(), gamma, sp);
        let (dom, ren) = sp
            .iter()
            .try_fold((Lvl(0), HashMap::new()), |(dom, mut ren), t| {
                match self.force(t.clone()) {
                    Val::Rigid(x, List { head: None }) if !ren.contains_key(&x.0) => {
                        ren.insert(x.0, dom);
                        Ok((dom + 1, ren))
                    }
                    _ => Err(UnifyError),
                }
            })?;

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
        sp: &List<Val>,
    ) -> Result<Tm, UnifyError> {
        match sp {
            List { head: None } => Ok(t),
            a => {
                let t = self.rename_go_sp(m, pren, t, &a.tail())?;
                let u = self.rename_go(m, pren, a.head().unwrap().clone())?;
                Ok(Tm::App(Box::new(t), Box::new(u)))
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
            Val::Lam(x, closure) => {
                let t = self.rename_go(
                    m,
                    &lift(pren.clone()),
                    self.closure_apply(&closure, Val::vvar(pren.cod)),
                )?;
                Ok(Tm::Lam(x, Box::new(t)))
            }
            Val::Pi(x, a, closure) => {
                let a = self.rename_go(m, pren, *a)?;
                let b = self.rename_go(
                    m,
                    &lift(pren.clone()),
                    self.closure_apply(&closure, Val::vvar(pren.cod)),
                )?;
                Ok(Tm::Pi(x, Box::new(a), Box::new(b)))
            }
            Val::U => Ok(Tm::U),
        }
    }

    fn rename(&self, m: MetaVar, pren: PartialRenaming, v: Val) -> Result<Tm, UnifyError> {
        //println!("{} {:?} {:?} {:?}", "rename".green(), m, pren, v);
        self.rename_go(m, &pren, v)
    }

    fn eval(&self, env: &Env, tm: Tm) -> Val {
        //println!("{} {:?}", "eval".yellow(), tm);
        match tm {
            Tm::Var(x) => env.iter().nth(x.0 as usize).unwrap().clone(),
            Tm::App(t, u) => self.v_app(self.eval(env, *t), self.eval(env, *u)),
            Tm::Lam(x, t) => Val::Lam(x, Closure(env.clone(), t)),
            Tm::Pi(x, a, b) => Val::Pi(x, Box::new(self.eval(env, *a)), Closure(env.clone(), b)),
            Tm::Let(_, _, t, u) => {
                let t_val = self.eval(env, *t);
                self.eval(&env.prepend(t_val), *u)
            }
            Tm::U => Val::U,
            Tm::Meta(m) => self.v_meta(m),
            Tm::InsertedMeta(m, bds) => self.v_app_bds(env, self.v_meta(m), &bds),
        }
    }

    fn quote_sp(&self, l: Lvl, t: Tm, spine: Spine) -> Tm {
        spine.iter().fold(t, |acc, u| {
            Tm::App(Box::new(acc), Box::new(self.quote(l, u.clone())))
        })
    }

    fn quote(&self, l: Lvl, t: Val) -> Tm {
        //println!("{} {:?}", "quote".green(), t);
        let t = self.force(t);
        match t {
            Val::Flex(m, sp) => self.quote_sp(l, Tm::Meta(m), sp),
            Val::Rigid(x, sp) => self.quote_sp(l, Tm::Var(lvl2ix(l, x)), sp),
            Val::Lam(x, closure) => Tm::Lam(
                x,
                Box::new(self.quote(l + 1, self.closure_apply(&closure, Val::vvar(l)))),
            ),
            Val::Pi(x, a, closure) => Tm::Pi(
                x,
                Box::new(self.quote(l, *a)),
                Box::new(self.quote(l + 1, self.closure_apply(&closure, Val::vvar(l)))),
            ),
            Val::U => Tm::U,
        }
    }

    pub fn nf(&self, env: &Env, t: Tm) -> Tm {
        let l = Lvl(env.iter().count() as u32);
        self.quote(l, self.eval(env, t))
    }

    fn close_val(&self, cxt: &Cxt, t: Val) -> Closure {
        Closure(cxt.env.clone(), Box::new(self.quote(cxt.lvl + 1, t)))
    }

    fn unify_catch(&mut self, cxt: &Cxt, t: Val, t_prime: Val) -> Result<(), Error> {
        self.unify(cxt.lvl, t.clone(), t_prime.clone())
            .map_err(|_| {
                /*Error::CantUnify(
                    cxt.clone(),
                    self.quote(cxt.lvl, t),
                    self.quote(cxt.lvl, t_prime),
                )*/
                //Error(format!("can't unify {:?} == {:?}", self.quote(cxt.lvl, t), self.quote(cxt.lvl, t_prime)))
                Error(format!("can't unify {:?} == {:?}", t, t_prime))
            })
    }

    fn unify_sp(&mut self, l: Lvl, sp: &List<Val>, sp_prime: &List<Val>) -> Result<(), UnifyError> {
        match (sp, sp_prime) {
            (List { head: None }, List { head: None }) => Ok(()), // Both spines are empty
            (a, b) if matches!(a.head(), Some(_)) && matches!(b.head(), Some(_)) => {
                self.unify_sp(l, &a.tail(), &b.tail())?; // Recursively unify the rest of the spines
                self.unify(l, a.head().unwrap().clone(), b.head().unwrap().clone()) // Unify the current values
            }
            _ => Err(UnifyError), // Rigid mismatch error
        }
    }

    fn unify(&mut self, l: Lvl, t: Val, u: Val) -> Result<(), UnifyError> {
        //println!("{} {:?} {} {:?}", "unify".yellow(), t, "==".yellow(), u); //debug
        let t = self.force(t);
        let u = self.force(u);
        /*println!(
            "{} {:?} {} {:?}",
            "unify after force".yellow(),
            t,
            "==".yellow(),
            u
        );*/ //debug

        match (&t, &u) {
            // Lambda cases
            (Val::Lam(_, t_closure), Val::Lam(_, u_closure)) => self.unify(
                l + 1,
                self.closure_apply(t_closure, Val::vvar(l)),
                self.closure_apply(u_closure, Val::vvar(l)),
            ),
            (_, Val::Lam(_, u_closure)) => self.unify(
                l + 1,
                self.v_app(t.clone(), Val::vvar(l)),
                self.closure_apply(u_closure, Val::vvar(l)),
            ),
            (Val::Lam(_, t_closure), _) => self.unify(
                l + 1,
                self.closure_apply(t_closure, Val::vvar(l)),
                self.v_app(u.clone(), Val::vvar(l)),
            ),

            // Universe case
            (Val::U, Val::U) => Ok(()),

            // Pi case
            (Val::Pi(x, a, b_closure), Val::Pi(x_prime, a_prime, b_prime_closure)) => {
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
                for (ix, (x_prime, a)) in cxt.types.iter().enumerate() {
                    if x == *x_prime {
                        return Ok((Tm::Var(Ix(ix as u32)), a.clone()));
                    }
                }
                //Err(Error::NameNotInScope(x))
                Err(Error(format!("error name not in scope: {:?}", x)))
            }

            // Infer lambda expressions
            Raw::Lam(x, t) => {
                let new_meta = self.fresh_meta(cxt);
                let a = self.eval(&cxt.env, new_meta);
                let (t_inferred, b) = self.infer(&cxt.bind(x.clone(), a.clone()), *t)?;
                let b_closure = self.close_val(cxt, b);
                Ok((
                    Tm::Lam(x.clone(), Box::new(t_inferred)),
                    Val::Pi(x, Box::new(a), b_closure),
                ))
            }

            // Infer function applications
            Raw::App(t, u) => {
                let (t_inferred, tty) = self.infer(cxt, *t.clone())?;
                println!("{} {:?} -> {:?}", "infer___".red(), t, tty); //debug
                let (a, b_closure) = match self.force(tty) {
                    Val::Pi(_, a, b_closure) => (*a, b_closure),
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
                                Box::new(a.clone()),
                                b_closure.clone(),
                            ),
                            tty,
                        )?;
                        (a, b_closure)
                    }
                };
                let u_checked = self.check(cxt, *u, a)?;
                let b_applied =
                    self.closure_apply(&b_closure, self.eval(&cxt.env, u_checked.clone()));
                Ok((
                    Tm::App(Box::new(t_inferred), Box::new(u_checked)),
                    b_applied,
                ))
            }

            // Infer universe type
            Raw::U => Ok((Tm::U, Val::U)),

            // Infer dependent function types
            Raw::Pi(x, a, b) => {
                let a_checked = self.check(cxt, *a, Val::U)?;
                let b_checked = self.check(
                    &cxt.bind(x.clone(), self.eval(&cxt.env, a_checked.clone())),
                    *b,
                    Val::U,
                )?;
                Ok((Tm::Pi(x, Box::new(a_checked), Box::new(b_checked)), Val::U))
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
    fn check(&mut self, cxt: &Cxt, t: Raw, a: Val) -> Result<Tm, Error> {
        //println!("{} {:?} {} {:?}", "check".blue(), t, "==".blue(), a);
        match (t, self.force(a)) {
            // Check lambda expressions
            (Raw::Lam(x, t), Val::Pi(_, a_pi, b_closure)) => {
                let body = self.check(
                    &cxt.bind(x.clone(), *a_pi),
                    *t,
                    self.closure_apply(&b_closure, Val::vvar(cxt.lvl)),
                )?;
                Ok(Tm::Lam(x, Box::new(body)))
            }

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
                let (t_inferred, inferred_type) = self.infer(cxt, t)?;
                self.unify_catch(cxt, expected, inferred_type)?;
                Ok(t_inferred)
            }
        }
    }
}

#[test]
fn test() {
    let input = r#"
let id : (A : _) -> A -> A
  = \A x. x;

let List : U -> U
  = \A. (L : _) -> (A -> L -> L) -> L -> L;

let nil : (A : _) -> List A
  = \A L cons nil. nil;

let cons : (A : _) -> A -> List A -> List A
  = \A x xs L cons nil. cons x (xs _ cons nil);

let Bool : U
  = (B : _) -> B -> B -> B;

let true : Bool
  = \B t f. t;

let false : Bool
  = \B t f. f;

let not : Bool -> Bool
  = \b B t f. b B f t;

let list1 : List Bool
  = cons _ (id _ true) (nil _);

let Eq : (A : _) -> A -> A -> U
  = \A x y. (P : A -> U) -> P x -> P y;

let refl : (A : _)(x : A) -> Eq A x x
  = \A x P px. px;

let list1 : List Bool
  = cons _ true (cons _ false (nil _));

let Nat  : U = (N : U) -> (N -> N) -> N -> N;
let five : Nat = \N s z. s (s (s (s (s z))));
let add  : Nat -> Nat -> Nat = \a b N s z. a N s (b N s z);
let mul  : Nat -> Nat -> Nat = \a b N s z. a N (b N s) z;

let ten      : Nat = add five five;
let hundred  : Nat = mul ten ten;
let thousand : Nat = mul ten hundred;

let eqTest : Eq _ hundred hundred = refl _ _;

U
"#;
    let ast = crate::L04_implicit::parser::parser(input, 0).unwrap();
    let typ = Infer::new().infer(&Cxt::empty(), ast).unwrap();
    println!("{:#?}", typ);
}*/
