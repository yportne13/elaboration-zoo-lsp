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
mod pretty;

#[derive(Debug, Clone, Copy, PartialEq)]
struct MetaVar(u32);

#[derive(Debug)]
enum MetaEntry {
    Solved(Rc<Val>, Rc<VTy>),
    Unsolved(Rc<VTy>),
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

type Env = List<Rc<Val>>;
type Spine = List<(Rc<Val>, Icit)>;

#[derive(Debug, Clone)]
struct Closure(Env, Rc<Tm>);

#[derive(Debug, Clone)]
enum Val {
    Flex(MetaVar, Spine),
    Rigid(Lvl, Spine),
    Lam(Span<String>, Icit, Closure),
    Pi(Span<String>, Icit, Rc<VTy>, Closure),
    U,
    LiteralType,
    LiteralIntro(Span<String>),
    Prim,
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
use std::rc::Rc;

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
    fn new_meta(&mut self, a: Rc<VTy>) -> u32 {
        self.meta.push(MetaEntry::Unsolved(a));
        self.meta.len() as u32 - 1
    }
    fn fresh_meta(&mut self, cxt: &Cxt, a: &Rc<VTy>) -> Tm {
        let closed = self.eval(&List::new(), &close_ty(cxt.locals.clone(), self.quote(cxt.lvl, a)));
        let m = self.new_meta(closed);
        Tm::AppPruning(Box::new(Tm::Meta(MetaVar(m))), cxt.pruning.clone())
    }
    fn lookup_meta(&self, m: &MetaVar) -> &MetaEntry {
        &self.meta[m.0 as usize]
    }
    fn force(&self, t: &Rc<Val>) -> Rc<Val> {
        //println!("{} {:?}", "force".red(), t);
        match t.as_ref() {
            Val::Flex(m, sp) => match self.lookup_meta(m) {
                MetaEntry::Solved(t_solved, _) => self.force(&self.v_app_sp(t_solved.clone(), sp.clone())),
                MetaEntry::Unsolved(_) => Val::Flex(*m, sp.clone()).into(),
            },
            _ => t.clone(),
        }
    }
    fn v_meta(&self, m: &MetaVar) -> Rc<Val> {
        match self.lookup_meta(m) {
            MetaEntry::Solved(v, _) => v.clone(),
            MetaEntry::Unsolved(_) => Val::vmeta(*m).into(),
        }
    }

    fn closure_apply(&self, closure: &Closure, u: Rc<Val>) -> Rc<Val> {
        //println!("{} {:?} {:?}", "closure apply".yellow(), closure, u);
        self.eval(&closure.0.prepend(u), &closure.1)
    }

    fn v_app(&self, t: Rc<Val>, u: Rc<Val>, i: Icit) -> Rc<Val> {
        match t.as_ref() {
            Val::Lam(_, _, closure) => self.closure_apply(&closure, u),
            Val::Flex(m, sp) => Val::Flex(*m, sp.prepend((u, i))).into(),
            Val::Rigid(x, sp) => Val::Rigid(*x, sp.prepend((u, i))).into(),
            _ => panic!("impossible"),
        }
    }

    fn v_app_sp(&self, t: Rc<Val>, spine: Spine) -> Rc<Val> {
        //spine.iter().rev().fold(t, |acc, (u, i)| self.v_app(acc, u.clone(), *i))
        match spine {
            List { head: None } => t,
            a => {
                let (u, i) = a.head().unwrap();
                self.v_app(self.v_app_sp(t, a.tail()), u.clone(), *i)
            },
        }
    }

    fn v_app_pruning(&self, env: &Env, v: Rc<Val>, pr: &Pruning) -> Rc<Val> {
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

    fn eval(&self, env: &Env, tm: &Tm) -> Rc<Val> {
        //println!("{} {:?}", "eval".yellow(), tm);
        match tm {
            Tm::Var(x) => env.iter().nth(x.0 as usize).unwrap().clone(),
            Tm::App(t, u, i) => self.v_app(self.eval(env, t), self.eval(env, u), *i),
            Tm::Lam(x, i, t) => Val::Lam(x.clone(), *i, Closure(env.clone(), t.clone().into())).into(),//TODO:use reference?
            Tm::Pi(x, i, a, b) => Val::Pi(x.clone(), *i, self.eval(env, a), Closure(env.clone(), b.clone().into())).into(),//TODO:use reference?
            Tm::Let(_, _, t, u) => {
                let t_val = self.eval(env, t);
                self.eval(&env.prepend(t_val), u)
            }
            Tm::U => Val::U.into(),
            Tm::Meta(m) => self.v_meta(m),
            Tm::AppPruning(t, pr) => self.v_app_pruning(env, self.eval(env, t), &pr),
            Tm::LiteralIntro(x) => Val::LiteralIntro(x.clone()).into(),
            Tm::LiteralType => Val::LiteralType.into(),
            Tm::Prim => match (env.iter().nth(1).unwrap().as_ref(), env.iter().nth(0).unwrap().as_ref()) {
                (Val::LiteralIntro(a), Val::LiteralIntro(b)) => {
                    Val::LiteralIntro(a.clone().map(|x| format!("{x}{}", b.data))).into()
                },
                _ => Val::Prim.into(),
            },
        }
    }

    fn quote_sp(&self, l: Lvl, t: Tm, spine: Spine) -> Tm {
        /*spine.iter().fold(t, |acc, u| {
            Tm::App(Box::new(acc), Box::new(self.quote(l, u.0.clone())), u.1)
        })*/
        match spine {
            List { head: None } => t,
            _ => {
                let head = spine.head().unwrap();
                Tm::App(Box::new(self.quote_sp(l, t, spine.tail())), Box::new(self.quote(l, &head.0)), head.1)
            }
        }
    }

    fn quote(&self, l: Lvl, t: &Rc<Val>) -> Tm {
        //println!("{} {:?}", "quote".green(), t);
        let t = self.force(t);
        match t.as_ref() {
            Val::Flex(m, sp) => self.quote_sp(l, Tm::Meta(*m), sp.clone()),
            Val::Rigid(x, sp) => self.quote_sp(l, Tm::Var(lvl2ix(l, *x)), sp.clone()),
            Val::Lam(x, i, closure) => Tm::Lam(
                x.clone(),
                *i,
                Box::new(self.quote(l + 1, &self.closure_apply(&closure, Val::vvar(l).into()))),
            ),
            Val::Pi(x, i, a, closure) => Tm::Pi(
                x.clone(),
                *i,
                Box::new(self.quote(l, a)),
                Box::new(self.quote(l + 1, &self.closure_apply(&closure, Val::vvar(l).into()))),
            ),
            Val::U => Tm::U,
            Val::LiteralIntro(x) => Tm::LiteralIntro(x.clone()),
            Val::LiteralType => Tm::LiteralType,
            Val::Prim => Tm::Prim,
        }
    }

    pub fn nf(&self, env: &Env, t: Tm) -> Tm {
        let l = Lvl(env.iter().count() as u32);
        self.quote(l, &self.eval(env, &t))
    }

    fn close_val(&self, cxt: &Cxt, t: &Rc<Val>) -> Closure {
        Closure(cxt.env.clone(), Rc::new(self.quote(cxt.lvl + 1, t)))
    }

    fn unify_catch(&mut self, cxt: &Cxt, t: &Rc<Val>, t_prime: &Rc<Val>) -> Result<(), Error> {
        self.unify(cxt.lvl, t, t_prime)
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
    let ast = parser::parser(&preprocess(input), path_id).unwrap();
    let mut cxt = Cxt::new();
    let mut ret = String::new();
    for tm in ast {
        let (x, _, new_cxt) = infer.infer(&cxt, tm.clone())?;
        cxt = new_cxt;
        if let DeclTm::Println(x) = x {
            //ret += &format!("{:?}", infer.nf(&cxt.env, x));
            ret += &pretty::pretty_tm(0, cxt.names(), &infer.nf(&cxt.env, x));
            ret += "\n";
        }
    }
    Ok(ret)
}

pub fn preprocess(s: &str) -> String {
    let s = s.split("/*")
        .map(|x| {
            x.split_once("*/")
                .map(|(a, b)| a.replace(|c: char| !c.is_whitespace(), " ") + "  " + b)
                .unwrap_or(x.to_owned())
        })
        .reduce(|a, b| a + "  " + &b)
        .unwrap_or(s.to_owned());
    s.lines()
        .map(|x| {
            x.split_once("//")
                .map(|(a, b)| a.to_owned() + "  " + &b.replace(|c: char| !c.is_whitespace(), " "))
                .unwrap_or(x.to_owned())
        })
        .reduce(|a, b| a + "\n" + &b)
        .unwrap_or(s.to_owned())
}

#[test]
fn test() {
    let input = r#"
def Eq[A : U](x: A, y: A): U = (P : A -> U) -> P x -> P y
def refl[A : U, x: A]: Eq[A] x x = _ => px => px
def symmetry [A : U] (a: A, b: A) (eqab : Eq a b) : Eq b a =
  eqab (bb => (Eq bb a)) refl

def the(A : U)(x: A): A = x

def m(A : U)(B : U): U -> U -> U = _
def test = a => b => the (Eq (m a a) (x => y => y)) refl

def m : U -> U -> U -> U = _
def test = a => b => c => the (Eq (m a b c) (m c b a)) refl


def pr1 = f => x => f x
def pr2 = f => x => y => f x y
def pr3 = f => f U

def Nat : U
    = (N : U) -> (N -> N) -> N -> N
def mul : Nat -> Nat -> Nat
    = a => b => N => s => z => a _ (b _ s) z
def ten : Nat
    = N => s => z => s (s (s (s (s (s (s (s (s (s z)))))))))
def hundred = mul ten ten

println hundred

def mystr = "hello world"

def add_tail(x: String): String = string_concat x "!"

def mystr2 = add_tail mystr

/*
multi line comment
*/

//final
println mystr2

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
