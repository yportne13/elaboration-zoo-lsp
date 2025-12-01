use colored::Colorize;
use cxt::Cxt;
use parser::syntax::{Either, Icit, Pattern, Raw};
use pattern_match::{Compiler, DecisionTree};
use syntax::{Pruning, close_ty};
use pretty::pretty_tm;

use crate::list::List;
use crate::parser_lib::Span;

mod cxt;
mod elaboration;
mod parser;
mod pattern_match;
mod syntax;
mod unification;
mod typeclass;
mod pretty;

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct MetaVar(u32);

#[derive(Debug, Clone)]
enum MetaEntry {
    Solved(Val, VTy),
    Unsolved(VTy),
}

#[derive(Debug, Clone, Copy)]
pub struct Ix(u32);

#[derive(Debug, Clone)]
enum BD {
    Bound,
    Defined,
}

#[derive(Clone, Debug)]
pub enum DeclTm {
    Def {
        name: Span<String>,
        typ: Val,
        body: Val,
        typ_pretty: String,
        body_pretty: String,
    },
    Println(Tm),
    Enum {
        //TODO:
    },
    Trait {
        //TODO:
    },
    TraitImpl {
        //TODO:
    },
}

#[derive(Debug, Clone)]
pub enum Tm {
    Var(Ix),
    Obj(Box<Tm>, Span<String>),
    Lam(Span<String>, Icit, Box<Tm>),
    App(Box<Tm>, Box<Tm>, Icit),
    AppPruning(Box<Tm>, Pruning),
    U(u32),
    Pi(Span<String>, Icit, Box<Ty>, Box<Ty>),
    Let(Span<String>, Box<Ty>, Box<Tm>, Box<Tm>),
    Meta(MetaVar),
    LiteralType,
    LiteralIntro(Span<String>),
    Prim,
    Sum(Span<String>, Vec<(Span<String>, Tm, Ty, Icit)>, Vec<Span<String>>, bool),
    SumCase {
        typ: Box<Tm>,
        case_name: Span<String>,
        datas: Vec<(Span<String>, Tm, Icit)>,
        is_trait: bool,
    },
    Match(Box<Tm>, Vec<(PatternDetail, Tm)>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum PatternDetail {
    Any(Span<()>),
    Bind(Span<String>),
    Con(Span<String>, Vec<PatternDetail>),
}

impl PatternDetail {
    fn bind_count(&self) -> u32 {
        match self {
            PatternDetail::Any(_) => 0,
            PatternDetail::Bind(_) => 1,
            PatternDetail::Con(_, pattern_details) => {
                pattern_details.iter().map(|pattern_detail| pattern_detail.bind_count()).sum::<u32>()
            },
        }
    }
}

type Ty = Tm;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd)]
pub struct Lvl(u32);

impl Add<u32> for Lvl {
    type Output = Lvl;
    fn add(self, rhs: u32) -> Lvl {
        Lvl(self.0 + rhs)
    }
}

impl Sub<u32> for Lvl {
    type Output = Lvl;
    fn sub(self, rhs: u32) -> Lvl {
        Lvl(self.0 - rhs)
    }
}

type Env = List<Val>;
type Spine = List<(Val, Icit)>;

#[derive(Clone)]
pub struct Closure(Env, Box<Tm>);

impl std::fmt::Debug for Closure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Closure(.., {:?})", self.1)
    }
}

#[derive(Debug, Clone)]
pub enum Val {
    Flex(MetaVar, Spine),
    Rigid(Lvl, Spine),
    Obj(Box<Val>, Span<String>, Spine),
    Lam(Span<String>, Icit, Closure),
    Pi(Span<String>, Icit, Box<VTy>, Closure),
    U(u32),
    LiteralType,
    LiteralIntro(Span<String>),
    Prim,
    Sum(
        Span<String>,
        Vec<(Span<String>, Val, VTy, Icit)>,
        Vec<Span<String>>,
        bool,
    ),
    SumCase {
        is_trait: bool,
        typ: Box<Val>,
        case_name: Span<String>,
        datas: Vec<(Span<String>, Val, Icit)>,
    },
    Match(Box<Val>, Env, Vec<(PatternDetail, Tm)>),
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
    if x.0 > 1919810 {
        Ix(x.0)
    } else {
        Ix(l.0 - x.0 - 1)
    }
}

use std::{
    collections::HashMap,
    ops::{Add, Sub},
};

#[derive(Debug)]
enum UnifyError {
    Basic,
    Trait(String),
}

fn empty_span<T>(data: T) -> Span<T> {
    Span {
        data,
        start_offset: 0,
        end_offset: 0,
        path_id: 0,
    }
}

#[derive(Debug)]
pub struct Error(pub Span<String>);

#[derive(Clone)]
pub struct Infer {
    meta: Vec<MetaEntry>,
    global: HashMap<Lvl, VTy>,
    trait_solver: typeclass::Synth,
    trait_definition: HashMap<String, (Vec<(Span<String>, Raw, Icit)>, Vec<(Span<String>, Vec<(Span<String>, Raw, Icit)>, Raw)>)>,
}

impl Infer {
    pub fn new() -> Self {
        Self {
            meta: vec![],
            global: HashMap::new(),
            trait_solver: Default::default(),
            trait_definition: Default::default(),
        }
    }
    fn new_meta(&mut self, a: VTy) -> u32 {
        self.meta.push(MetaEntry::Unsolved(a));
        self.meta.len() as u32 - 1
    }
    fn fresh_meta(&mut self, cxt: &Cxt, a: VTy) -> Tm {
        if let Ok(Some((a, _))) = self.solve_trait(cxt, &a) {
            a
        } else {
            let closed = self.eval(
                &List::new(),
                close_ty(cxt.locals.clone(), self.quote(cxt.lvl, a)),
            );
            let m = self.new_meta(closed);
            Tm::AppPruning(Box::new(Tm::Meta(MetaVar(m))), cxt.pruning.clone())
        }
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
            Val::Obj(x, a, b) => {
                Val::Obj(Box::new(self.force(*x)), a, b)
            }
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
        //println!("v_app {t:?} {u:?}");
        match t {
            Val::Lam(_, _, closure) => self.closure_apply(&closure, u),
            Val::Flex(m, sp) => Val::Flex(m, sp.prepend((u, i))),
            Val::Rigid(x, sp) => Val::Rigid(x, sp.prepend((u, i))),
            Val::Obj(x, name, sp) => Val::Obj(x, name, sp.prepend((u, i))),
            x => panic!("impossible apply\n  {:?}\nto\n  {:?}", x, u),
        }
    }

    fn v_app_sp(&self, t: Val, spine: Spine) -> Val {
        //spine.iter().rev().fold(t, |acc, (u, i)| self.v_app(acc, u.clone(), *i))
        match spine {
            List { head: None } => t,
            a => {
                let (u, i) = a.head().unwrap();
                self.v_app(self.v_app_sp(t, a.tail()), u.clone(), *i)
            }
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
            _ => panic!("impossible {v:?}"),
        }
    }

    fn eval(&self, env: &Env, tm: Tm) -> Val {
        //println!("{} {:?}", "eval".yellow(), tm);
        match tm {
            Tm::Var(x) => match env.iter().nth(x.0 as usize) {
                Some(v) => v.clone(),
                None => self.global.get(&Lvl(x.0 - 1919810)).unwrap().clone(),
            },
            Tm::Obj(tm, name) => {
                match self.eval(env, *tm) {
                    Val::Sum(_, params, cases, _) => {
                        params.into_iter()
                            .find(|(f_name, _, _, _)| f_name == &name)
                            .unwrap().1
                    },
                    Val::SumCase { datas, typ, .. } => {
                        (match *typ {
                            Val::Sum(_, params, _, _) => params,
                            _ => panic!("impossible {typ:?}"),
                        }).into_iter()
                            .map(|x| (x.0, x.1, x.3))
                            .chain(datas)
                        //datas.into_iter()
                            .find(|(f_name, _, _)| f_name == &name)
                            .unwrap().1
                    },
                    x @ Val::Rigid(_, _) | x @ Val::Flex(_, _) => {
                        Val::Obj(Box::new(x), name, List::new())
                    }
                    x => panic!("impossible {x:?}"),
                }
            }
            Tm::App(t, u, i) => self.v_app(self.eval(env, *t), self.eval(env, *u), i),
            Tm::Lam(x, i, t) => Val::Lam(x, i, Closure(env.clone(), t)),
            Tm::Pi(x, i, a, b) => {
                Val::Pi(x, i, Box::new(self.eval(env, *a)), Closure(env.clone(), b))
            }
            Tm::Let(_, _, t, u) => {
                let t_val = self.eval(env, *t);
                self.eval(&env.prepend(t_val), *u)
            }
            Tm::U(x) => Val::U(x),
            Tm::Meta(m) => self.v_meta(m),
            Tm::AppPruning(t, pr) => self.v_app_pruning(env, self.eval(env, *t), &pr),
            Tm::LiteralIntro(x) => Val::LiteralIntro(x),
            Tm::LiteralType => Val::LiteralType,
            Tm::Prim => match (env.iter().nth(1).unwrap(), env.iter().nth(0).unwrap()) {
                (Val::LiteralIntro(a), Val::LiteralIntro(b)) => {
                    Val::LiteralIntro(a.clone().map(|x| format!("{x}{}", b.data)))
                }
                _ => Val::Prim,
            },
            Tm::Sum(name, params, cases, is_trait) => {
                let new_params = params
                    .into_iter()
                    .map(|x| (x.0, self.eval(env, x.1), self.eval(env, x.2), x.3))
                    .collect();
                Val::Sum(name, new_params, cases, is_trait)
            }
            Tm::SumCase {
                is_trait,
                typ,
                case_name,
                datas,
            } => {
                let datas = datas
                    .into_iter()
                    .map(|p| (p.0, self.eval(env, p.1), p.2))
                    .collect();
                let typ = self.eval(env, *typ);
                Val::SumCase {
                    is_trait,
                    typ: Box::new(typ),
                    case_name,
                    datas,
                }
            }
            Tm::Match(tm, cases) => {
                let val = self.eval(env, *tm);
                let val = self.force(val);
                match val {
                    val @ Val::SumCase { .. } => {
                        let (tm, env) = Compiler::eval_aux(self, val, env, &cases).unwrap();
                        self.eval(&env, tm)
                    }
                    neutral => {
                        Val::Match(Box::new(neutral), env.clone(), cases)
                    }
                }
            }
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
                Tm::App(Box::new(self.quote_sp(l, t, spine.tail())), Box::new(self.quote(l, head.0.clone())), head.1)
            }
        }
    }

    fn quote(&self, l: Lvl, t: Val) -> Tm {
        //println!("{} {:?}", "quote".green(), t);
        let t = self.force(t);
        match t {
            Val::Flex(m, sp) => self.quote_sp(l, Tm::Meta(m), sp),
            Val::Rigid(x, sp) => self.quote_sp(l, Tm::Var(lvl2ix(l, x)), sp),
            Val::Obj(x, name, sp) => self.quote_sp(l, Tm::Obj(Box::new(self.quote(l, *x)), name), sp),
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
            Val::U(x) => Tm::U(x),
            Val::LiteralIntro(x) => Tm::LiteralIntro(x),
            Val::LiteralType => Tm::LiteralType,
            Val::Prim => Tm::Prim,
            Val::Sum(name, params, cases, is_trait) => {
                let new_params = params.into_iter()
                    .map(|x| {
                        (x.0, self.quote(l, x.1), self.quote(l, x.2), x.3)
                    })
                    .collect();
                Tm::Sum(name, new_params, cases, is_trait)
            }
            Val::SumCase {
                is_trait,
                typ,
                case_name,
                datas,
            } => {
                let datas = datas
                    .into_iter()
                    .map(|p| {
                        (p.0, self.quote(l, p.1), p.2)
                    })
                    .collect();
                Tm::SumCase {
                    is_trait,
                    typ: Box::new(self.quote(l, *typ)),
                    case_name,
                    datas,
                }
            }
            Val::Match(val, env, cases) => {
                /*TODO:let tm_cases = cases
                    .into_iter()
                    .map(|(p, clos)| {
                        let binders_count = p.count_binders();
                        let body_tm = self.quote(l + binders_count, self.closure_apply_pats(&clos, l, &p));
                        (p, body_tm)
                    })
                    .collect();*/
                let tm_cases = cases
                    .into_iter()
                    .map(|x| (
                        x.0.clone(),
                        {
                            let env = (0..x.0.bind_count())
                                .fold(env.clone(), |env, _| env.prepend(Val::vvar(Lvl(env.len() as u32))));
                            let mut avoid_recursive = self.clone();
                            avoid_recursive.global
                                .iter_mut()
                                .for_each(|x| *x.1 = Val::Rigid(*x.0 + 1919810, List::new()));
                            let tm = avoid_recursive.eval(&env, x.1);
                            self.quote(l+x.0.bind_count(), tm)
                        }
                    ))
                    .collect();
                Tm::Match(Box::new(self.quote(l, *val)), tm_cases)
            }
        }
    }

    pub fn nf(&self, env: &Env, t: Tm) -> Tm {
        let l = Lvl(env.iter().count() as u32);
        self.quote(l, self.eval(env, t))
    }

    fn close_val(&self, cxt: &Cxt, t: Val) -> Closure {
        Closure(cxt.env.clone(), Box::new(self.quote(cxt.lvl + 1, t)))
    }

    fn unify_catch(&mut self, cxt: &Cxt, t: Val, t_prime: Val, span: Span<()>) -> Result<(), Error> {
        self.unify(cxt.lvl, cxt, t.clone(), t_prime.clone())
            .map_err(|e| {
                /*Error::CantUnify(
                    cxt.clone(),
                    self.quote(cxt.lvl, t),
                    self.quote(cxt.lvl, t_prime),
                )*/
                //println!("{:?} == {:?}", t, t_prime);
                //println!("{:?}", self.eval(&cxt.env, self.quote(cxt.lvl, t_prime.clone())));
                /*panic!(
                    //"can't unify {:?} == {:?}",
                    "can't unify\n      find: {}\n  expected: {}",
                    pretty_tm(0, cxt.names(), &self.quote(cxt.lvl, t)),
                    pretty_tm(0, cxt.names(), &self.quote(cxt.lvl, t_prime)),
                );*/
                let err = match e {
                    UnifyError::Basic => format!(
                        //"can't unify {:?} == {:?}",
                        "can't unify\n      find: {}\n  expected: {}",
                        pretty_tm(0, cxt.names(), &self.quote(cxt.lvl, t)),
                        pretty_tm(0, cxt.names(), &self.quote(cxt.lvl, t_prime)),
                    ),
                    UnifyError::Trait(e) => e,
                };
                Error(span.map(|_| err.clone()))
                //Error(format!("can't unify {:?} == {:?}", t, t_prime))
            })
    }
}

#[allow(unused)]
pub fn run(input: &str, path_id: u32) -> Result<String, Error> {
    let mut infer = Infer::new();
    let ast = parser::parser(&preprocess(input), path_id).unwrap();
    let mut cxt = Cxt::new();
    let mut ret = String::new();
    for tm in ast {
        match &tm {
            parser::syntax::Decl::Def { name, .. }
            | parser::syntax::Decl::Enum { name, .. }
            | parser::syntax::Decl::TraitDecl { name, .. } => {
                println!("> {}", name.data);
                //cxt.print_env(&infer);
            },
            parser::syntax::Decl::Println(raw) => {},
            parser::syntax::Decl::ImplDecl { .. } => {
                println!("> impl");
            }
        }
        let (x, _, new_cxt) = infer.infer(&cxt, tm.clone())?;
        cxt = new_cxt;
        if let DeclTm::Println(x) = x {
            //ret += &format!("{:?}", infer.nf(&cxt.env, x));
            ret += &pretty::pretty_tm(0, cxt.names(), &infer.nf(&cxt.env, x));
            ret += "\n";
        }
    }
    /*cxt.env
        .iter()
        .zip(cxt.names().iter())
        .for_each(|(ty, name)| {
            println!("{}: {}", name, pretty::pretty_tm(0, cxt.names(), &infer.quote(cxt.lvl, ty.clone())));
            //println!("{:?}\n", ty);
        });*/
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
fn test_trait() {
    let input = r#"
enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

def two = succ (succ zero)

def not(x: Bool): Bool =
    match x {
        case true => false
        case false => true
    }

println (not true)

trait ToString {
    def to_string: String
}

impl ToString for Bool {
    def to_string: String =
        match this {
            case true => "true"
            case false => "false"
        }
}

def t[T][s: ToString[T]](x: T): String =
    s.to_string x

println (t true)

trait Add[T] {
    def add(that: T): Self
}

impl Add[Nat] for Nat {
    def add(that: Nat): Nat =
        match that {
            case zero => this
            case succ(n) => succ (n.add this)
        }
}

def mul(x: Nat, y: Nat) = match x {
    case zero => zero
    case succ(n) => y.add (mul n y)
}

def four = two.add two

println four

struct Point[T] {
    x: T
    y: T
}

def get_x[T](p: Point[T]): T = p.x

impl Add[Point[Nat]] for Point[Nat] {
    def add(that: Point[Nat]): Point[Nat] =
        new Point(this.x.add that.x, this.y.add that.y)
}

impl Add[Nat] for Point[Nat] {
    def add(that: Nat): Point[Nat] =
        new Point(this.x.add that, this.y.add that)
}

def start_point = new Point(zero, four)

def end_point = new Point(four, two)

println (get_x start_point)

println (start_point.add end_point)

def test0: Type 1 = Type 0

def test1: Type 2 = Type 1 -> Type 0

enum HighLvl[A] {
    case1(a: A)
    case2(a: test1)
}

def test2: HighLvl[Nat] = case1 zero

def test3: Type 2 = HighLvl[Nat]

enum HighLvl2[A: Type 2] {
    case2_1(x: A)
    case2_2(x: Nat)
}

def test1_2: HighLvl2[HighLvl[Nat]] = case2_1 test2

def test1_3: Type 2 = HighLvl2[HighLvl[Nat]]

enum HighLvl3[A: Type 2] {
    case3_1
    case3_2(x: Nat)
}

def test2_2: HighLvl3[HighLvl[Nat]] = case3_1

def test2_3: Type 2 = HighLvl3[HighLvl[Nat]]

def Eq[A](x: A, y: A) = (P : A -> Type 0) -> P x -> P y

def refl[A, x: A]: Eq[A] x x = _ => px => px

struct Bits {
    name: String
    size: Nat
}

def get_name(x: Bits) = x.name

def assign(a: Bits, b: Bits)(eq: Eq[Nat] a.size b.size): String = a.name

def sigA = new Bits("A", four)

def sigB = new Bits("B", four)

def sigC = new Bits("C", two)

def sigD = new Bits("D", two)

def ab = assign sigA sigB refl

def cd = assign sigC sigD refl

"#;
    println!("{}", run(input, 0).unwrap());
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
    succ(x: Nat)
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

def listid(x: List[Bool]): List[Bool] = x

def create0: List[Bool] = nil

def create1: List[Bool] = cons true nil

def create2: List[Bool] = cons true (cons false nil)

def two = succ (succ zero)

def not(x: Bool): Bool =
    match x {
        case true => false
        case false => true
    }

println (not true)

def add(x: Nat, y: Nat) =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def mul(x: Nat, y: Nat) = match x {
    case zero => zero
    case succ(n) => add y (mul n y)
}

def four = add two two

println four

struct Point[T] {
    x: T
    y: T
}

def get_x[T](p: Point[T]): T = p.x

def point_add(p1: Point[Nat], p2: Point[Nat]): Point[Nat] =
    new Point((add p1.x p2.x), (add p1.y p2.y))

def start_point = new Point(zero, four)

def end_point = new Point(four, two)

println (get_x start_point)

println (point_add start_point end_point)

def test0: Type 1 = Type 0

def test1: Type 2 = Type 1 -> Type 0

enum HighLvl[A] {
    case1(a: A)
    case2(a: test1)
}

def test2: HighLvl[Nat] = case1 zero

def test3: Type 2 = HighLvl[Nat]

enum HighLvl2[A: Type 2] {
    case2_1(x: A)
    case2_2(x: Nat)
}

def test1_2: HighLvl2[HighLvl[Nat]] = case2_1 test2

def test1_3: Type 2 = HighLvl2[HighLvl[Nat]]

enum HighLvl3[A: Type 2] {
    case3_1
    case3_2(x: Nat)
}

def test2_2: HighLvl3[HighLvl[Nat]] = case3_1

def test2_3: Type 2 = HighLvl3[HighLvl[Nat]]

def Eq[A](x: A, y: A) = (P : A -> Type 0) -> P x -> P y

def refl[A, x: A]: Eq[A] x x = _ => px => px

struct Bits {
    name: String
    size: Nat
}

def get_name(x: Bits) = x.name

def assign(a: Bits, b: Bits)(eq: Eq[Nat] a.size b.size): String = a.name

def sigA = new Bits("A", four)

def sigB = new Bits("B", four)

def sigC = new Bits("C", two)

def sigD = new Bits("D", two)

def ab = assign sigA sigB refl

def cd = assign sigC sigD refl

"#;
    println!("{}", run(input, 0).unwrap());
    let input = r#"
enum Nat {
    zero
    succ(x: Nat)
}

def test1: Type 2 = Type 1 -> Type 0

struct HighLvl[A] {
    case1: A
    case2: test1
}

def test2_t: Type 1 -> Type 0 = t => Nat

def test2: HighLvl[Nat] = new HighLvl(zero, test2_t)

def test3: Type 2 = HighLvl[Nat]

struct HighLvl2[A: Type 2] {
    case2_1: A
    case2_2: Nat
}

def test1_2: HighLvl2[HighLvl[Nat]] = new HighLvl2(test2, zero)

def test1_3: Type 2 = HighLvl2[HighLvl[Nat]]

struct HighLvl3[A: Type 2] {
    case3_1: Nat
    case3_2: Nat
}

def test2_2: HighLvl3[HighLvl[Nat]] = new HighLvl3(zero, zero)

def test2_3: Type 2 = HighLvl3[HighLvl[Nat]]
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
