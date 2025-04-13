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

#[derive(Clone, Debug)]
pub enum DeclTm {
    Def {
        /*name: Span<String>,
        params: Vec<(Span<String>, Tm, Icit)>,
        ret_type: Tm,
        body: Tm,*/
    },
    Println(Tm),
    Enum {
        //TODO:
    },
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
    LiteralType,
    LiteralIntro(Span<String>),
    Prim,
    Sum(Span<String>, Vec<Ty>, Vec<(Span<String>, Vec<Tm>)>),
    SumCase {
        sum_name: Span<String>,
        case_name: Span<String>,
    },//TODO:
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
    LiteralType,
    LiteralIntro(Span<String>),
    Prim,
    Sum(Span<String>, Vec<Val>, Vec<(Span<String>, Vec<Tm>)>),
    SumCase {
        sum_name: Span<String>,
        case_name: Span<String>,
    },//TODO:
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
            Tm::LiteralIntro(x) => Val::LiteralIntro(x),
            Tm::LiteralType => Val::LiteralType,
            Tm::Prim => match (env.iter().nth(1).unwrap(), env.iter().nth(0).unwrap()) {
                (Val::LiteralIntro(a), Val::LiteralIntro(b)) => {
                    Val::LiteralIntro(a.clone().map(|x| format!("{x}{}", b.data)))
                },
                _ => Val::Prim,
            },
            Tm::Sum(name, params, cases) => {
                let new_params = params.into_iter().map(|x| {
                    self.eval(&env.clone(), x)
                }).collect();
                Val::Sum(name, new_params, cases)
            },
            Tm::SumCase { sum_name, case_name } => Val::SumCase { sum_name, case_name },
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
            Val::LiteralIntro(x) => Tm::LiteralIntro(x),
            Val::LiteralType => Tm::LiteralType,
            Val::Prim => Tm::Prim,
            Val::Sum(name, params, cases) => {
                let new_params = params.into_iter().map(|x| {
                    self.quote(l, x)
                }).collect();
                Tm::Sum(name, new_params, cases)
            },
            Val::SumCase { sum_name, case_name } => Tm::SumCase { sum_name, case_name },
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

pub fn run(input: &str, path_id: u32) -> Result<String, Error> {
    let mut infer = Infer::new();
    let ast = parser::parser(input, path_id).unwrap();
    let mut cxt = Cxt::new();
    let mut ret = String::new();
    for tm in ast {
        let (x, _, new_cxt) = infer.infer(&cxt, tm.clone())?;
        cxt = new_cxt;
        if let DeclTm::Println(x) = x {
            ret += &format!("{:?}", infer.nf(&cxt.env, x));
            ret += "\n";
        }
    }
    Ok(ret)
}

#[test]
fn test2() {
    let input = r#"
enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(Nat)
}

enum List[A] {
    nil
    cons(A, List[A])
}

def listid(x: List[Bool]): List[Bool] = x

def create0: List[Bool] = nil

def create1: List[Bool] = cons true nil

def create2: List[Bool] = cons true (cons false nil)

def two = succ (succ zero)

def add(x: Nat, y: Nat): Nat =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def four = add two two

println four

"#;
    println!("{}", run(input, 0).unwrap());
    println!("success");
}

#[test]
fn test() {
    let input = r#"
def Eq[A : U](x: A, y: A): U = (P : A -> U) -> P x -> P y
def refl[A : U, x: A]: Eq[A] x x = _ => px => px

def the(A : U)(x: A): A = x

def m(A : U)(B : U): U -> U -> U = _
def test = a => b => the (Eq (m a a) (x => y => y)) refl

def m : U -> U -> U -> U = _
def test = a => b => c => the (Eq (m a b c) (m c b a)) refl


def pr1 = f => x => f x
def pr2 = f => x => y => f x y
def pr3 = f => f U

def Nat : U =
    (N : U) -> (N -> N) -> N -> N
def mul : Nat -> Nat -> Nat =
    a => b => N => s => z => a _ (b _ s) z
def ten : Nat =
    N => s => z => s (s (s (s (s (s (s (s (s (s z)))))))))
def hundred = mul ten ten

println hundred

def mystr = "hello world"

def add_tail(x: String): String = string_concat x "!"

def mystr2 = add_tail mystr

println mystr2

enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(Nat)
}

def two = succ (succ zero)

def add(x: Nat, y: Nat): Nat =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def four = add two two

println four

"#;
    println!("{}", run(input, 0).unwrap());
    println!("success");
}


pub fn run1(input: &str, path_id: u32) -> Result<String, Error> {
    let mut infer = Infer::new();
    let ast = parser::parser(input, path_id).unwrap();
    let mut cxt = Cxt::new();
    let mut ret = String::new();
    for tm in ast {
        let (x, _, new_cxt) = infer.infer(&cxt, tm.clone())?;
        cxt = new_cxt;
        if let DeclTm::Println(x) = x {
            ret += &format!("{:?}", infer.nf(&cxt.env, x));
            ret += "\n";
        }
    }
    println!("{:?}", cxt);
    Ok(ret)
}

#[test]
fn test1() {
    let input = r#"
def str_id(x: String, y: String): String = "builtin"

"#;
    println!("{}", run1(input, 0).unwrap());
    let input = r#"
def str_id(x: String, y: String): String = x

"#;
    println!("{}", run1(input, 0).unwrap());
    let input = r#"
def str_id: String = string_concat "hello " "world"

println str_id

"#;
    println!("{}", run1(input, 0).unwrap());
    println!("success");
}
