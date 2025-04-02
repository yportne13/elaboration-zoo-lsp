use colored::Colorize;
use cxt::Cxt;
use parser::syntax::{Either, Icit, Raw};
use syntax::{close_ty, Pruning};

use crate::list::List;
use crate::parser_lib::Span;

mod parser;
mod elaboration;
mod cxt;
mod unification;
mod syntax;

#[derive(Debug, Clone, Copy, PartialEq)]
struct MetaVar(u32);

#[derive(Debug)]
enum MetaEntry {
    Solved(Val, VTy),
    Unsolved(VTy),
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
    Lam(Span<String>, Icit, Box<Tm>),
    App(Box<Tm>, Box<Tm>, Icit),
    AppPruning(Box<Tm>, Pruning),
    U,
    Pi(Span<String>, Icit, Box<Ty>, Box<Ty>),
    Let(Span<String>, Box<Ty>, Box<Tm>, Box<Tm>),
    Meta(MetaVar),
}

type Ty = Tm;

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Lvl(u32);

impl Add<u32> for Lvl {
    type Output = Lvl;
    fn add(self, rhs: u32) -> Lvl {
        Lvl(self.0 + rhs)
    }
}

type Env = List<Val>;
type Spine = List<(Val, Icit)>;

#[derive(Debug, Clone)]
struct Closure(Env, Box<Tm>);

#[derive(Debug, Clone)]
enum Val {
    Flex(MetaVar, Spine),
    Rigid(Lvl, Spine),
    Lam(Span<String>, Icit, Closure),
    Pi(Span<String>, Icit, Box<VTy>, Closure),
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

pub struct Infer {
    meta: Vec<MetaEntry>,
}

impl Infer {
    pub fn new() -> Self {
        Self { meta: vec![] }
    }
    fn new_meta(&mut self, a: VTy) -> u32 {
        self.meta.push(MetaEntry::Unsolved(a));
        self.meta.len() as u32 - 1
    }
    fn fresh_meta(&mut self, cxt: &Cxt, a: VTy) -> Tm {
        let closed = self.eval(&List::new(), close_ty(cxt.locals.clone(), self.quote(cxt.lvl, a)));
        let m = self.new_meta(closed);
        Tm::AppPruning(Box::new(Tm::Meta(MetaVar(m))), cxt.pruning.clone())
    }
    fn lookup_meta(&self, m: MetaVar) -> &MetaEntry {
        &self.meta[m.0 as usize]
    }
    fn force(&self, t: Val) -> Val {
        //println!("{} {:?}", "force".red(), t);
        match t {
            Val::Flex(m, sp) => match self.lookup_meta(m) {
                MetaEntry::Solved(t_solved, _) => self.force(self.v_app_sp(t_solved.clone(), sp)),
                MetaEntry::Unsolved(_) => Val::Flex(m, sp),
            },
            _ => t,
        }
    }
    fn v_meta(&self, m: MetaVar) -> Val {
        match self.lookup_meta(m) {
            MetaEntry::Solved(v, _) => v.clone(),
            MetaEntry::Unsolved(_) => Val::vmeta(m),
        }
    }

    fn closure_apply(&self, closure: &Closure, u: Val) -> Val {
        //println!("{} {:?} {:?}", "closure apply".yellow(), closure, u);
        self.eval(&closure.0.prepend(u), *closure.1.clone())
    }

    fn v_app(&self, t: Val, u: Val, i: Icit) -> Val {
        match t {
            Val::Lam(_, _, closure) => self.closure_apply(&closure, u),
            Val::Flex(m, sp) => Val::Flex(m, sp.prepend((u, i))),
            Val::Rigid(x, sp) => Val::Rigid(x, sp.prepend((u, i))),
            _ => panic!("impossible"),
        }
    }

    fn v_app_sp(&self, t: Val, spine: Spine) -> Val {
        //spine.iter().rev().fold(t, |acc, (u, i)| self.v_app(acc, u.clone(), *i))
        match spine {
            List { head: None } => t,
            a => {
                let (u, i) = a.head().unwrap();
                self.v_app(self.v_app_sp(t, a.tail()), u.clone(), *i)
            },
        }
    }

    fn v_app_pruning(&self, env: &Env, v: Val, pr: &Pruning) -> Val {
        //println!("{} {:?} {:?}", "v_app_bds".green(), v, bds);
        match (env, pr) {
            (List { head: None }, List { head: None }) => v,
            (a, b) if a.head().is_some() && matches!(b.head(), Some(Some(_))) => self.v_app(
                self.v_app_pruning(&a.tail(), v, &b.tail()),
                a.head().unwrap().clone(),
                b.head().unwrap().unwrap(),
            ),
            (a, b) if a.head().is_some() && matches!(b.head(), Some(None)) => {
                self.v_app_pruning(&a.tail(), v, &b.tail())
            }
            _ => panic!("impossible"),
        }
    }

    fn eval(&self, env: &Env, tm: Tm) -> Val {
        //println!("{} {:?}", "eval".yellow(), tm);
        match tm {
            Tm::Var(x) => env.iter().nth(x.0 as usize).unwrap().clone(),
            Tm::App(t, u, i) => self.v_app(self.eval(env, *t), self.eval(env, *u), i),
            Tm::Lam(x, i, t) => Val::Lam(x, i, Closure(env.clone(), t)),
            Tm::Pi(x, i, a, b) => Val::Pi(x, i, Box::new(self.eval(env, *a)), Closure(env.clone(), b)),
            Tm::Let(_, _, t, u) => {
                let t_val = self.eval(env, *t);
                self.eval(&env.prepend(t_val), *u)
            }
            Tm::U => Val::U,
            Tm::Meta(m) => self.v_meta(m),
            Tm::AppPruning(t, pr) => self.v_app_pruning(env, self.eval(env, *t), &pr),
        }
    }

    fn quote_sp(&self, l: Lvl, t: Tm, spine: Spine) -> Tm {
        spine.iter().fold(t, |acc, u| {
            Tm::App(Box::new(acc), Box::new(self.quote(l, u.0.clone())), u.1)
        })
    }

    fn quote(&self, l: Lvl, t: Val) -> Tm {
        //println!("{} {:?}", "quote".green(), t);
        let t = self.force(t);
        match t {
            Val::Flex(m, sp) => self.quote_sp(l, Tm::Meta(m), sp),
            Val::Rigid(x, sp) => self.quote_sp(l, Tm::Var(lvl2ix(l, x)), sp),
            Val::Lam(x, i, closure) => Tm::Lam(
                x,
                i,
                Box::new(self.quote(l + 1, self.closure_apply(&closure, Val::vvar(l)))),
            ),
            Val::Pi(x, i, a, closure) => Tm::Pi(
                x,
                i,
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
                Error(format!("can't unify {:?} == {:?}", self.quote(cxt.lvl, t), self.quote(cxt.lvl, t_prime)))
                //Error(format!("can't unify {:?} == {:?}", t, t_prime))
            })
    }
}

#[test]
fn test() {
    let input = r#"
let Eq : {A : U} -> A -> A -> U
    = \ {A} x y. (P : A -> U) -> P x -> P y;
let refl : {A : U}{x : A} -> Eq {A} x x
    = \ _ px. px;

let the : (A : U) -> A -> A = \ _ x. x;

let m : (A : U)(B : U) -> U -> U -> U = _;
let test = \ a b. the (Eq (m a a) (\ x y. y)) refl;

let m : U -> U -> U -> U = _;
let test = \ a b c. the (Eq (m a b c) (m c b a)) refl;


let pr1 = \ f x. f x;
let pr2 = \ f x y. f x y;
let pr3 = \ f. f U;

U

"#;
    let ast = crate::L05_pruning::parser::parser(input, 0).unwrap();
    let typ = Infer::new().infer(&Cxt::empty(), ast).unwrap();
    println!("{:?}", typ.0);
    println!("success");
}
