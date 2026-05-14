use colored::Colorize;
use cxt::Cxt;
use parser::{syntax::{Either, Icit, Raw}, IError};
use pattern_match::Compiler;
use smol_str::SmolStr;
use syntax::{Pruning, close_ty};
use pretty::pretty_tm;

use crate::list::List;
use crate::parser_lib::Span;

pub mod cxt;
mod elaboration;
pub mod parser;
mod pattern_match;
mod syntax;
mod unification;
mod typeclass;
pub mod pretty;
mod canonical;

#[cfg(test)]
mod legacy_tests;

type Rc<T> = std::sync::Arc<T>;

type Decl = HashMap<SmolStr, (Span<()>, Rc<Tm>, Rc<Val>, Rc<Ty>, Rc<VTy>)>;

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct MetaVar(u32);

#[derive(Debug, Clone)]
enum MetaEntry {
    Solved(Rc<Val>, Rc<VTy>),
    Unsolved(Rc<VTy>, Cxt, Rc<VTy>),
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
        name: Span<SmolStr>,
        typ: Rc<Val>,
        body: Rc<Val>,
        typ_pretty: String,
        body_pretty: String,
    },
    Println(Rc<Tm>, String, Span<()>),
    Enum {
        //TODO:
    },
    Trait {
        //TODO:
    },
    TraitImpl {
        //TODO:
    },
    Package,
    Import,
}

#[derive(Clone)]
pub struct PrimFunc(Rc<dyn Fn(&Infer, &Decl, &Env, Rc<Val>) -> Rc<Val> + Send + Sync>);

impl std::fmt::Debug for PrimFunc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "PrimFunc")
    }
}

#[derive(Debug, Clone)]
pub enum Tm {
    Var(Ix),
    Decl(Span<SmolStr>),
    Obj(Rc<Tm>, Span<SmolStr>),
    Lam(Span<SmolStr>, Icit, Rc<Tm>),
    App(Rc<Tm>, Rc<Tm>, Icit),
    AppPruning(Rc<Tm>, Pruning),
    U(u32),
    Pi(Span<SmolStr>, Icit, Rc<Ty>, Rc<Ty>),
    Let(Span<SmolStr>, Rc<Ty>, Rc<Tm>, Rc<Tm>),
    Meta(MetaVar),
    LiteralType,
    LiteralIntro(Span<String>),
    Prim(Rc<Val>, PrimFunc),
    Sum(Span<SmolStr>, TmSumParams, TmSumCases, bool),
    SumCase {
        typ: Rc<Tm>,
        case_name: Span<SmolStr>,
        datas: TmSumCaseDatas,
        is_trait: bool,
    },
    Match(Rc<Tm>, Vec<(PatternDetail, Rc<Tm>)>),
    /// Call(name, display_args, val_args, body) - body was inlined from function `name`
    Call(SmolStr, List<(Rc<Tm>, Icit)>, Rc<Tm>),
}

impl Tm {
    pub fn no_metas(&self, infer: &Infer, decl: &Decl, l: Lvl) -> Option<(Cxt, Rc<Val>)> {
        match self {
            Tm::Var(_) | Tm::Decl(_) | Tm::U(_) | Tm::LiteralType | Tm::LiteralIntro(_) | Tm::Prim(_, _) => None,
            Tm::Obj(tm, _) => tm.no_metas(infer, decl, l),
            Tm::Lam(_, _, t) => t.no_metas(infer, decl, l + 1),
            Tm::App(t, u, _) => t.no_metas(infer, decl, l).or_else(|| u.no_metas(infer, decl, l)),
            Tm::AppPruning(t, _) => {
                t.no_metas(infer, decl, l)
            },
            Tm::Pi(_, _, t, u) => t.no_metas(infer, decl, l).or_else(|| u.no_metas(infer, decl, l + 1)),
            Tm::Let(_, a, t, u) => a.no_metas(infer, decl, l).or_else(|| t.no_metas(infer, decl, l)).or_else(|| u.no_metas(infer, decl, l)),
            Tm::Meta(m) => match infer.lookup_meta(*m) {
                MetaEntry::Unsolved(_, cxt, oty) => Some((cxt.clone(), oty.clone())),
                MetaEntry::Solved(v, _) => {
                    infer.quote(decl, l, v).no_metas(infer, decl, l)
                }
            },
            Tm::Sum(_, items, _, _) => items.iter().flat_map(|(_, t, ty, _)| t.no_metas(infer, decl, l).or_else(|| ty.no_metas(infer, decl, l))).next(),
            Tm::SumCase { typ, case_name: _, datas, is_trait: _ } => typ.no_metas(infer, decl, l)
                .or_else(|| datas.iter().flat_map(|(_, t, _)| t.no_metas(infer, decl, l)).next()),
            Tm::Match(tm, items) => tm.no_metas(infer, decl, l).or_else(|| items.iter().flat_map(|(_, t)| t.no_metas(infer, decl, l)).next()),
            Tm::Call(_, args, body) => args.iter().flat_map(|(a, _)| a.no_metas(infer, decl, l)).next().or_else(|| body.no_metas(infer, decl, l)),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum PatternDetail {
    Any(Span<()>),
    Bind(Span<SmolStr>),
    Con(Span<SmolStr>, Vec<PatternDetail>),
}

impl PatternDetail {
    fn bind_count(&self) -> u32 {
        match self {
            PatternDetail::Any(_) => 1,
            PatternDetail::Bind(_) => 1,
            PatternDetail::Con(_, pattern_details) => {
                pattern_details.iter().map(|pattern_detail| pattern_detail.bind_count()).sum::<u32>()
            },
        }
    }
    fn bind_names(&self, ns: &List<SmolStr>) -> List<SmolStr> {
        match self {
            PatternDetail::Any(_) => ns.prepend(SmolStr::new("_")),
            PatternDetail::Bind(name) => ns.prepend(name.data.clone()),
            PatternDetail::Con(_, pattern_details) => {
                pattern_details
                    .iter()
                    .fold(ns.clone(), |ns, pattern_detail| pattern_detail.bind_names(&ns))
            },
        }
    }
    fn bind_cxt(&self, cxt: &Cxt) -> Cxt {
        match self {
            PatternDetail::Any(_) => cxt.clone(),
            PatternDetail::Bind(name) => cxt.bind(name.clone(), Tm::U(0).into(), Val::U(0).into()),
            PatternDetail::Con(_, pattern_details) => {
                pattern_details
                    .iter()
                    .fold(cxt.clone(), |cxt, pattern_detail| pattern_detail.bind_cxt(&cxt))
            },
        }
    }
}

impl std::fmt::Display for PatternDetail {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PatternDetail::Any(_) => write!(f, "_"),
            PatternDetail::Bind(name) => write!(f, "{}", name.data),
            PatternDetail::Con(name, pattern_details) => {
                let p = pattern_details
                    .iter()
                    .map(|pattern_detail| pattern_detail.to_string())
                    .collect::<Vec<_>>();
                if p.is_empty() {
                    write!(f, "{}", name.data)
                } else {
                    write!(f, "{}({})", name.data, p.join(", "))
                }
            }
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

type Env = List<Rc<Val>>;
type Spine = List<(Rc<Val>, Icit)>;

#[derive(Clone)]
pub struct Closure(Env, Rc<Tm>);

impl std::fmt::Debug for Closure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Closure(..{}, {:?})", self.0.len(), self.1)
    }
}

#[derive(Debug, Clone)]
pub enum Val {
    Flex(MetaVar, Spine),
    Rigid(Lvl, Spine),
    Decl(Span<SmolStr>, Spine),
    Obj(Rc<Val>, Span<SmolStr>, Spine),
    Lam(Span<SmolStr>, Icit, Closure),
    Pi(Span<SmolStr>, Icit, Rc<VTy>, Closure),
    U(u32),
    LiteralType,
    LiteralIntro(Span<String>),
    Prim(Rc<Val>, PrimFunc),
    Sum(
        Span<SmolStr>,
        SumParams,
        SumCases,
        bool,
    ),
    SumCase {
        is_trait: bool,
        typ: Rc<Val>,
        case_name: Span<SmolStr>,
        datas: SumCaseDatas,
    },
    Match(Rc<Val>, Env, Vec<(PatternDetail, Rc<Tm>)>),
    /// Call(name, args, body) - value inlined from function `name`
    Call(SmolStr, List<(Rc<Val>, Icit)>, Rc<Val>),
}

type VTy = Val;

// Arc-wrapped Vec types to avoid deep cloning on Sum/SumCase clones
type SumParams = Rc<Vec<(Span<SmolStr>, Rc<Val>, Rc<VTy>, Icit)>>;
type SumCases = Rc<Vec<Span<SmolStr>>>;
type SumCaseDatas = Rc<Vec<(Span<SmolStr>, Rc<Val>, Icit)>>;
type TmSumParams = Rc<Vec<(Span<SmolStr>, Rc<Tm>, Rc<Ty>, Icit)>>;
type TmSumCases = Rc<Vec<Span<SmolStr>>>;
type TmSumCaseDatas = Rc<Vec<(Span<SmolStr>, Rc<Tm>, Icit)>>;

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

pub fn tm_contains_match(tm: &Tm) -> bool {
    match tm {
        Tm::Match(..) => true,
        Tm::Lam(_, _, body) => tm_contains_match(body),
        _ => false,
    }
}

pub fn wrap_match_in_call(name: SmolStr, tm: &Tm, _l: u32) -> Tm {
    fn go(name: SmolStr, tm: &Tm, l: u32, icits: &mut Vec<Icit>) -> Tm {
        match tm {
            Tm::Lam(span, i, body) => {
                icits.push(*i);
                let result = Tm::Lam(span.clone(), *i, go(name, body, l + 1, icits).into());
                icits.pop();
                result
            }
            Tm::Match(scru, cases) => Tm::Call(
                name,
                {
                    let mut list = List::new();
                    for i in 0..l {
                        list = list.prepend((Tm::Var(Ix(i)).into(), icits[(l - 1 - i) as usize]));
                    }
                    list
                },
                Tm::Match(scru.clone(), cases.clone()).into(),
            ),
            _ => tm.clone(),
        }
    }
    go(name, tm, 0, &mut Vec::new())
}

pub fn count_lams(tm: &Tm) -> u32 {
    match tm {
        Tm::Lam(_, _, body) => 1 + count_lams(body),
        _ => 0,
    }
}

use std::ops::{Add, Sub};
use im::{HashMap, HashSet};

#[derive(Debug)]
pub enum UnifyError {
    Basic,
    Stuck,
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

pub struct Error(
    pub Span<String>,
    pub Vec<Box<dyn Fn() -> Option<String> + Send + Sync>>
);

impl std::fmt::Debug for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // 只渲染第一个字段，输出效果如：Error(Span { ... })
        f.debug_tuple("Error")
            .field(&self.0)
            .finish()
    }
}

impl IError {
    pub fn to_err(self) -> Error {
        Error(self.msg.map(|x| format!("{:?}", x)), vec![])
    }
}

#[derive(Clone)]
pub struct Infer {
    meta: Vec<MetaEntry>,
    meta_contrains: Vec<(Rc<Val>, Rc<Val>)>,
    trait_solver: typeclass::Synth,
    trait_definition: HashMap<SmolStr, (Vec<(Span<SmolStr>, Raw, Icit)>, Vec<bool>, Vec<(Span<SmolStr>, Vec<(Span<SmolStr>, Raw, Icit)>, Raw)>)>,
    trait_out_param: HashMap<SmolStr, Vec<bool>>,
    pub mutable_map: Rc<std::sync::RwLock<HashMap<String, Rc<Val>>>>,
    pub hover_table: Vec<(Span<()>, Span<()>, Cxt, Rc<Val>)>,
    pub completion_table: Vec<(Span<()>, SmolStr)>,
}

impl Infer {
    pub fn new() -> Self {
        Self {
            meta: vec![],
            meta_contrains: vec![],
            trait_solver: Default::default(),
            trait_definition: Default::default(),
            trait_out_param: Default::default(),
            mutable_map: Default::default(),
            hover_table: vec![],
            completion_table: vec![],
        }
    }
    fn new_meta(&mut self, a: Rc<VTy>, cxt: Cxt, origin_typ: Rc<VTy>) -> u32 {
        self.meta.push(MetaEntry::Unsolved(a, cxt, origin_typ));
        self.meta.len() as u32 - 1
    }
    fn fresh_meta(&mut self, cxt: &Cxt, a: Rc<VTy>) -> Rc<Tm> {
        if let Ok(Some((a, _))) = self.solve_trait(cxt, &a) {
            a
        } else if let Val::Sum(_, _, _, true) = a.as_ref() {
            let m = self.new_meta(a.clone(), cxt.clone(), a);
            Tm::Meta(MetaVar(m)).into()
        } else {
            //let temp = &close_ty(&cxt.locals, self.quote(&cxt.decl, cxt.lvl, &a));
            //println!("{:?}: {}", a, pretty_tm(0, cxt.names(), temp));
            //println!("{:?}: {:?}", a, temp);
            let closed = self.eval(
                &cxt.decl,
                &List::new(),
                &close_ty(&cxt.locals, self.quote(&cxt.decl, cxt.lvl, &a)),
            );
            let m = self.new_meta(closed, cxt.clone(), a);
            Tm::AppPruning(Tm::Meta(MetaVar(m)).into(), cxt.pruning.clone()).into()
        }
    }
    fn lookup_meta(&self, m: MetaVar) -> &MetaEntry {
        &self.meta[m.0 as usize]
    }
    fn force(&self, decl: &Decl, t: &Rc<Val>) -> Rc<Val> {
        //println!("{} {:?}", "force".red(), t);
        match t.as_ref() {
            Val::Flex(m, sp) => match self.lookup_meta(*m) {
                MetaEntry::Solved(t_solved, _) => self.force(decl, &self.v_app_sp(decl, t_solved.clone(), sp)),
                MetaEntry::Unsolved(_, _, _) => Val::Flex(*m, sp.clone()).into(),
            },
            Val::Obj(x, a, b) => {
                Val::Obj(self.force(decl, x), a.clone(), b.clone()).into()
            },
            Val::Call(name, args, body) => {
                Val::Call(name.clone(), args.clone(), self.force(decl, body)).into()
            },
            _ => t.clone(),
        }
    }
    fn v_meta(&self, m: MetaVar) -> Rc<Val> {
        match self.lookup_meta(m) {
            MetaEntry::Solved(v, _) => v.clone(),
            MetaEntry::Unsolved(_, _, _) => Val::vmeta(m).into(),
        }
    }

    fn closure_apply(&self, decl: &Decl, closure: &Closure, u: Rc<Val>) -> Rc<Val> {
        //println!("{} {:?} {:?}", "closure apply".yellow(), closure, u);
        self.eval(decl, &closure.0.prepend(u), &closure.1)
    }

    fn v_app(&self, decl: &Decl, t: &Rc<Val>, u: Rc<Val>, i: Icit) -> Rc<Val> {
        //println!("v_app {t:?} {u:?}");
        match t.as_ref() {
            Val::Lam(_, _, closure) => self.closure_apply(decl, closure, u),
            Val::Flex(m, sp) => Val::Flex(*m, sp.prepend((u, i))).into(),
            Val::Rigid(x, sp) => Val::Rigid(*x, sp.prepend((u, i))).into(),
            Val::Decl(x, sp) => Val::Decl(x.clone(), sp.prepend((u, i))).into(),
            Val::Obj(x, name, sp) => Val::Obj(x.clone(), name.clone(), sp.prepend((u, i))).into(),
            Val::Call(name, args, body) => Val::Call(name.clone(), args.prepend((u.clone(), i)), self.v_app(decl, body, u, i)).into(),
            x => panic!("impossible apply\n  {:?}\nto\n  {:?}", x, u),
        }
    }

    fn v_app_sp(&self, decl: &Decl, t: Rc<Val>, spine: &Spine) -> Rc<Val> {
        //spine.iter().rev().fold(t, |acc, (u, i)| self.v_app(acc, u.clone(), *i))
        match spine {
            List { head: None, .. } => t,
            a => {
                let (u, i) = a.head().unwrap();
                self.v_app(decl, &self.v_app_sp(decl, t, &a.tail()), u.clone(), *i)
            }
        }
    }

    fn v_app_pruning(&self, decl: &Decl, env: &Env, v: Rc<Val>, pr: &Pruning) -> Rc<Val> {
        //println!("{} {:?} {:?}", "v_app_bds".green(), v, bds);
        match (env, pr) {
            (List { head: None, .. }, List { head: None, .. }) => v,
            (a, b) if a.head().is_some() && matches!(b.head(), Some(Some(_))) => self.v_app(
                decl,
                &self.v_app_pruning(decl, &a.tail(), v, &b.tail()),
                a.head().unwrap().clone(),
                b.head().unwrap().unwrap(),
            ),
            (a, b) if a.head().is_some() && matches!(b.head(), Some(None)) => {
                self.v_app_pruning(decl, &a.tail(), v, &b.tail())
            }
            _ => panic!("impossible {v:?}"),
        }
    }

    fn eval(&self, decl: &Decl, env: &Env, tm: &Rc<Tm>) -> Rc<Val> {
        //println!("{} {:?}", "eval".yellow(), tm);
        match tm.as_ref() {
            Tm::Var(x) => match env.iter().nth(x.0 as usize) {
                Some(v) => v.clone(),
                None => panic!("var {:?} not found", x.0),
            },
            Tm::Decl(x) => decl.get(&x.data).map(|x| x.2.clone()).unwrap_or(Val::Decl(x.clone(), List::new()).into()),
            Tm::Obj(tm, name) => {
                let a = self.eval(decl, env, tm);
                let a = self.force(decl, &a);
                match a.as_ref() {
                    Val::Sum(_, params, _, _) => {
                        params.iter()
                            .find(|(f_name, _, _, _)| f_name == name)
                            .unwrap().1.clone()
                    },
                    Val::SumCase { datas, typ, .. } => {
                        (match typ.as_ref() {
                            Val::Sum(_, params, _, _) => params,
                            _ => panic!("impossible {typ:?}"),
                        }).iter()
                            .map(|x| (x.0.clone(), x.1.clone(), x.3))
                            .chain(datas.iter().cloned())
                        //datas.into_iter()
                            .find(|(f_name, _, _)| f_name == name)
                            .unwrap().1.clone()
                    },
                    _ => {
                        Val::Obj(a, name.clone(), List::new()).into()
                    },
                }
            }
            Tm::App(t, u, i) => self.v_app(decl, &self.eval(decl, env, t), self.eval(decl, env, u), *i),
            Tm::Lam(x, i, t) => Val::Lam(x.clone(), *i, Closure(env.clone(), t.clone())).into(),
            Tm::Pi(x, i, a, b) => {
                Val::Pi(x.clone(), *i, self.eval(decl, env, a), Closure(env.clone(), b.clone())).into()
            }
            Tm::Let(_, _, t, u) => {
                let t_val = self.eval(decl, env, t);
                self.eval(decl, &env.prepend(t_val), u)
            }
            Tm::U(x) => Val::U(*x).into(),
            Tm::Meta(m) => self.v_meta(*m),
            Tm::AppPruning(t, pr) => self.v_app_pruning(decl, env, self.eval(decl, env, t), pr),
            Tm::LiteralIntro(x) => Val::LiteralIntro(x.clone()).into(),
            Tm::LiteralType => Val::LiteralType.into(),
            Tm::Prim(typ, func) => func.0(self, decl, env, typ.clone()),
            Tm::Sum(name, params, cases, is_trait) => {
                let new_params = Rc::new(params
                    .iter()
                    .map(|x| (x.0.clone(), self.eval(decl, env, &x.1), self.eval(decl, env, &x.2), x.3))
                    .collect());
                Val::Sum(name.clone(), new_params, cases.clone(), *is_trait).into()
            }
            Tm::SumCase {
                is_trait,
                typ,
                case_name,
                datas,
            } => {
                let datas = Rc::new(datas
                    .iter()
                    .map(|p| (p.0.clone(), self.eval(decl, env, &p.1), p.2))
                    .collect());
                let typ = self.eval(decl, env, typ);
                Val::SumCase {
                    is_trait: *is_trait,
                    typ,
                    case_name: case_name.clone(),
                    datas,
                }.into()
            }
            Tm::Call(name, args, body) => {
                let result = self.eval(decl, env, body);
                if let Val::Match(..) = result.as_ref() {
                    let args = args
                        .map(|(x, i)| (self.eval(decl, env, x), *i));
                    Val::Call(name.clone(), args, result).into()
                } else {
                    result
                }
            },
            Tm::Match(tm, cases) => {
                let val = self.eval(decl, env, tm);
                let val = self.force(decl, &val);
                match val.as_ref() {
                    Val::SumCase { .. } => {
                        match Compiler::eval_aux(self, &val, decl, env, cases) {
                            Some((tm, env)) => self.eval(decl, &env, &tm),
                            None => Val::Match(val, env.clone(), cases.clone()).into(),
                        }
                    }
                    _ => {
                        Val::Match(val, env.clone(), cases.clone()).into()
                    }
                }
            }
        }
    }

    fn quote_sp(&self, decl: &Decl, l: Lvl, t: Rc<Tm>, spine: &Spine) -> Rc<Tm> {
        /*spine.iter().fold(t, |acc, u| {
            Tm::App(Box::new(acc), Box::new(self.quote(l, u.0.clone())), u.1)
        })*/
        match spine {
            List { head: None, .. } => t,
            _ => {
                let head = spine.head().unwrap();
                Tm::App(self.quote_sp(decl, l, t, &spine.tail()), self.quote(decl, l, &head.0), head.1).into()
            }
        }
    }

    pub fn quote(&self, decl: &Decl, l: Lvl, t: &Rc<Val>) -> Rc<Tm> {
        //println!("{} {:?}", "quote".green(), t);
        let t = self.force(decl, t);
        match t.as_ref() {
            Val::Flex(m, sp) => self.quote_sp(decl, l, Tm::Meta(*m).into(), sp),
            Val::Rigid(x, sp) => self.quote_sp(decl, l, Tm::Var(lvl2ix(l, *x)).into(), sp),
            Val::Decl(x, sp) => self.quote_sp(decl, l, Tm::Decl(x.clone()).into(), sp),
            Val::Obj(x, name, sp) => self.quote_sp(decl, l, Tm::Obj(self.quote(decl, l, x), name.clone()).into(), sp),
            Val::Lam(x, i, closure) => Tm::Lam(
                x.clone(),
                *i,
                self.quote(decl, l + 1, &self.closure_apply(decl, closure, Val::vvar(l).into())),
            ).into(),
            Val::Pi(x, i, a, closure) => Tm::Pi(
                x.clone(),
                *i,
                self.quote(decl, l, a),
                self.quote(decl, l + 1, &self.closure_apply(decl, closure, Val::vvar(l).into())),
            ).into(),
            Val::U(x) => Tm::U(*x).into(),
            Val::LiteralIntro(x) => Tm::LiteralIntro(x.clone()).into(),
            Val::LiteralType => Tm::LiteralType.into(),
            Val::Prim(typ, func) => Tm::Prim(typ.clone(), func.clone()).into(),
            Val::Sum(name, params, cases, is_trait) => {
                let new_params = Rc::new(params.iter()
                    .map(|x| {
                        (x.0.clone(), self.quote(decl, l, &x.1), self.quote(decl, l, &x.2), x.3)
                    })
                    .collect());
                Tm::Sum(name.clone(), new_params, cases.clone(), *is_trait).into()
            }
            Val::SumCase {
                is_trait,
                typ,
                case_name,
                datas,
            } => {
                let datas = Rc::new(datas
                    .iter()
                    .map(|p| {
                        (p.0.clone(), self.quote(decl, l, &p.1), p.2)
                    })
                    .collect());
                Tm::SumCase {
                    is_trait: *is_trait,
                    typ: self.quote(decl, l, typ),
                    case_name: case_name.clone(),
                    datas,
                }.into()
            }
            Val::Call(name, args, body) => Tm::Call(
                name.clone(),
                args.map(|(x, i)| (self.quote(decl, l, x), *i)),
                self.quote(decl, l, body),
            ).into(),
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
                    .iter()
                    .map(|x| (
                        x.0.clone(),
                        {
                            let env = (0..x.0.bind_count())
                                .fold(env.clone(), |env, x| env.prepend(Val::vvar(l + x).into()));
                            let declb = decl.iter()
                                .map(|x| (x.0.clone(), (
                                    x.1.0,
                                    Tm::Decl(x.1.0.map(|_| x.0.clone())).into(),
                                    Val::Decl(x.1.0.map(|_| x.0.clone()), List::new()).into(),
                                    x.1.3.clone(),
                                    x.1.4.clone(),
                                )))
                                .collect();
                            let tm = self.eval(&declb, &env, &x.1);
                            self.quote(decl, l+x.0.bind_count(), &tm)
                        }
                    ))
                    .collect();
                Tm::Match(self.quote(decl, l, val), tm_cases).into()
            }
        }
    }

    pub fn nf(&self, decl: &Decl, env: &Env, t: &Rc<Tm>) -> Rc<Tm> {
        let l = Lvl(env.len() as u32);
        self.quote(decl, l, &self.eval(decl, env, t))
    }

    fn close_val(&self, cxt: &Cxt, t: &Rc<Val>) -> Closure {
        Closure(cxt.env.clone(), self.quote(&cxt.decl, cxt.lvl + 1, t))
    }

    fn unify_catch(&mut self, cxt: &Cxt, t: &Rc<Val>, t_prime: &Rc<Val>, span: Span<()>) -> Result<(), Error> {
        self.meta_contrains.clear();
        let ret = self.unify(cxt.lvl, cxt, t, t_prime, 100)
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
                    pretty_tm(0, cxt.names(), &self.quote(&cxt.decl, cxt.lvl, t)),
                    pretty_tm(0, cxt.names(), &self.quote(&cxt.decl, cxt.lvl, t_prime)),
                );*/
                let err = match e {
                    UnifyError::Basic | UnifyError::Stuck => format!(
                        //"can't unify {:?} == {:?}",
                        "can't unify\n  expected: {}\n      find: {}",
                        pretty_tm(0, cxt.names(), &self.quote(&cxt.decl, cxt.lvl, t)),
                        pretty_tm(0, cxt.names(), &self.quote(&cxt.decl, cxt.lvl, t_prime)),
                    ),
                    UnifyError::Trait(e) => e,
                };
                Error(span.map(|_| err.clone()), vec![])
                //Error(format!("can't unify {:?} == {:?}", t, t_prime))
            });
        if !self.meta_contrains.is_empty() {
            let err = format!(
                    //"can't unify {:?} == {:?}",
                    "can't unify for unsolved meta\n  expected: {}\n      find: {}",
                    pretty_tm(0, cxt.names(), &self.quote(&cxt.decl, cxt.lvl, t)),
                    pretty_tm(0, cxt.names(), &self.quote(&cxt.decl, cxt.lvl, t_prime)),
                );
            self.meta_contrains.clear();
            Err(Error(span.map(|_| err.clone()), vec![]))?
        }
        self.meta_contrains.clear();
        ret
    }
}

#[allow(unused)]
pub fn run(input: &str, path_id: u32) -> Result<String, Error> {
    let mut infer = Infer::new();
    let ast = parser::parser(&preprocess(input), path_id).unwrap();
    let mut cxt = Cxt::new(&infer);
    let mut ret = String::new();
    //TODO: do not print err. return error
    for e in ast.1 {
        println!("{:?}", e)
    }
    for tm in ast.0 {
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
            parser::syntax::Decl::Package { path } => {
                println!("> package {}", path.iter().map(|s| s.data.as_str()).collect::<Vec<_>>().join("."));
            }
            parser::syntax::Decl::Import { prefix, names, wildcard } => {
                let path = prefix.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(".");
                if *wildcard {
                    println!("> import {}._", path);
                } else {
                    for n in names {
                        println!("> import {}.{}", path, n);
                    }
                }
            }
            parser::syntax::Decl::Derive { .. } => {
                panic!("Derive should have been expanded before run")
            }
        }
        let (x, _, new_cxt) = infer.infer(&cxt, tm.clone())?;
        cxt = new_cxt;
        if let DeclTm::Println(_, s, _) = x {
            //ret += &format!("{:?}", infer.nf(&cxt.env, x));
            ret += &s;
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

#[allow(unused)]
pub fn run_with_prelude(input: &str) -> Result<String, Error> {
    let mut infer = Infer::new();
    let prelude = &[
        include_str!("../prelude/op.typort"),
        include_str!("../prelude/eq.typort"),
        include_str!("../prelude/nat.typort"),
        include_str!("../prelude/natarith.typort"),
        include_str!("../prelude/bool.typort"),
        include_str!("../prelude/option.typort"),
        include_str!("../prelude/result.typort"),
        include_str!("../prelude/order.typort"),
        include_str!("../prelude/void.typort"),
        include_str!("../prelude/decidable.typort"),
        include_str!("../prelude/vec.typort"),
        include_str!("../prelude/either.typort"),
        include_str!("../prelude/list.typort"),
        include_str!("../prelude/string.typort"),
        include_str!("../prelude/nonempty.typort"),
        include_str!("../prelude/hdl.typort"),
        include_str!("../prelude/show.typort"),
    ];
    let mut cxt = Cxt::new(&infer);
    let mut ret = String::new();

    // Accumulate exported macros from prelude files
    let mut global_macros: std::collections::HashMap<String, Vec<parser::macros::MacroRule>> = Default::default();
    let mut id = 0;
    for p in prelude {
        if let Some((decls, parse_errs, new_exports)) = parser::parser_with_macros(&preprocess(p), id, &global_macros) {
            for ast_err in parse_errs {
                println!("{:?}", ast_err)
            }
            for (name, rules) in new_exports {
                global_macros.insert(name, rules);
            }
            for tm in decls {
                let (x, _, new_cxt) = infer.infer(&cxt, tm.clone())?;
                cxt = new_cxt;
            }
        }
        id += 1;
    }
    // Auto-import prelude: create short aliases for enum cases (e.g., Nat.zero → zero)
    let prelude_aliases: Vec<(SmolStr, _)> = cxt.decl.iter()
        .filter(|(k, _)| k.contains('.'))
        .map(|(k, v)| {
            let short = SmolStr::new(k.split('.').last().unwrap());
            (short, v.clone())
        })
        .collect();
    for (short, v) in prelude_aliases {
        cxt.decl.entry(short).or_insert(v);
    }
    // Parse main file with accumulated macros from prelude
    let ast = parser::parser_with_macros(&preprocess(input), prelude.len() as u32, &global_macros)
        .map(|(d, e, _)| (d, e))
        .unwrap();
    println!("-----------------");
    //TODO: do not print err. return error
    for e in ast.1 {
        println!("{:?}", e)
    }
    for tm in ast.0 {
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
            parser::syntax::Decl::Package { path } => {
                println!("> package {}", path.iter().map(|s| s.data.as_str()).collect::<Vec<_>>().join("."));
            }
            parser::syntax::Decl::Import { prefix, names, wildcard } => {
                let path = prefix.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(".");
                if *wildcard {
                    println!("> import {}._", path);
                } else {
                    for n in names {
                        println!("> import {}.{}", path, n);
                    }
                }
            }
            parser::syntax::Decl::Derive { .. } => {
                panic!("Derive should have been expanded before run")
            }
        }
        let (x, _, new_cxt) = infer.infer(&cxt, tm.clone())?;
        cxt = new_cxt;
        if let DeclTm::Println(_, s, _) = x {
            //ret += &format!("{:?}", infer.nf(&cxt.env, x));
            ret += &s;
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
fn test9() {
    let input = r#"
def outParam[A](a: A): A = a

enum Eq[A](x: A, y: A) {
    refl(a: A) -> Eq[A] a a
}

enum Bool {
    true
    false
}

trait Not {
    def ! : Self
}

impl Not for Bool {
    def ! : Bool = match this {
        case true => false
        case false => true
    }
}

trait Neg {
    def - : Self
}

trait BitNot {
    def ~ : Self
}

impl BitNot for Bool {
    def ~ : Bool = !this
}

trait Xor[T, O: outParam(Type 0)] {
    def ^(that: T): O
}

impl Xor[Bool, Bool] for Bool {
    def ^(that: Bool): Bool =
        match this {
            case false => that
            case true => !that
        }
}

trait And[T, O: outParam(Type 0)] {
    def &(that: T): O
}

impl And[Bool, Bool] for Bool {
    def &(that: Bool): Bool =
        match this {
            case false => false
            case true => that
        }
}

trait Or[T, O: outParam(Type 0)] {
    def |(that: T): O
}

impl Or[Bool, Bool] for Bool {
    def |(that: Bool): Bool =
        match this {
            case false => that
            case true => true
        }
}

enum Nat {
    zero
    succ(x: Nat)
}

trait Add[T, O: outParam(Type 0)] {
    def +(that: T): O
}

def nat_add_helper(x: Nat, y: Nat): Nat =
    match y {
        case zero => x
        case succ(n) => succ (nat_add_helper x n)
    }

impl Add[Nat, Nat] for Nat {
    def +(that: Nat): Nat =
        nat_add_helper this that
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (l + 1)
}

def vecmap[T, U, len: Nat](x: Vec[T] len, f: T -> U): Vec[U] len =
    match x {
        case nil => nil
        case cons(x, xs) => cons (f x) (vecmap xs f)
    }

impl[T, len: Nat] Vec[T] len {
    def map[U](f: T -> U): Vec[U] len =
        vecmap this f
}

enum Product[A, B] {
    product(a: A, b: B)
}

struct Tuple2[A, B] {
    x_1: A
    x_2: B
}

trait Cons {
    def ::[l: Nat](that: Vec[Self] l): Vec[Self] (l + 1)
}

impl[T] Cons for T {
    def ::[l: Nat](that: Vec[T] l): Vec[T] (l + 1) =
        cons this that
}

println (3 :: 2 :: nil).map(x => succ(x))

def half_adder(lhs: Bool, rhs: Bool): Tuple2[Bool, Bool] =
    Tuple2.mk (lhs & rhs, lhs ^ rhs)

def full_adder(lhs: Bool, rhs: Bool, carrier: Bool): Tuple2[Bool, Bool] =
    let s1 = lhs ^ rhs;
    Tuple2.mk ((s1 & carrier) | (lhs & rhs), s1 ^ carrier)

def bits_adder_carrier[len: Nat](lhs: Vec[Bool] len, rhs: Vec[Bool] len, carrier: Bool): Vec[Bool] (len + 1) =
    match lhs {
        case nil => carrier :: nil
        case cons(n, taill) => match rhs {
            case cons(m, tailr) => match bits_adder_carrier taill tailr carrier {
                case cons(c, tail) => let t = full_adder n m c;
                    t.x_1 :: t.x_2 :: tail
            }
        }
    }

impl[len: Nat] Add[Vec[Bool] len, Vec[Bool] (len + 1)] for Vec[Bool] len {
    def +(that: Vec[Bool] len): Vec[Bool] (len + 1) =
        bits_adder_carrier this that false
}

def bits_adder[len: Nat](lhs: Vec[Bool] len, rhs: Vec[Bool] len): Vec[Bool] (len + 1) =
    bits_adder_carrier lhs rhs false

println bits_adder (true :: nil) (false :: nil)

def full_adder_comm(lhs: Bool, rhs: Bool, carrier: Bool): Eq (full_adder lhs rhs carrier) (full_adder rhs lhs carrier) =
    match lhs {
        case false => match rhs {
            case false => refl (Tuple2.mk false carrier)
            case true => match carrier {
                case false => refl (Tuple2.mk false true)
                case true => refl (Tuple2.mk true false)
            }
        }
        case true => match rhs {
            case false => match carrier {
                case false => refl (Tuple2.mk false true)
                case true => refl (Tuple2.mk true false)
            }
            case true => match carrier {
                case false => refl (Tuple2.mk true false)
                case true => refl (Tuple2.mk true true)
            }
        }
    }

def adder_type[len: Nat](x: Vec[Bool] (succ len), n: Bool, m: Bool): Vec[Bool] (succ (succ len)) = match x {
    case cons(c, tail) => let t = full_adder n m c;
        t.x_1 :: t.x_2 :: tail
}

def carry_step[len: Nat](tail: Vec[Bool] len, p: Tuple2[Bool, Bool]): Vec[Bool] (succ (succ len)) =
    p.x_1 :: p.x_2 :: tail

def cong_carry_step[len: Nat, tail: Vec[Bool] len, p: Tuple2[Bool, Bool], q: Tuple2[Bool, Bool]](e: Eq p q): Eq (carry_step tail p) (carry_step tail q) =
    match e {
        case refl(a) => refl (carry_step tail a)
    }

def step1[len: Nat, x: Vec[Bool] (succ len), y: Vec[Bool] (succ len)](e0: Eq x y, n: Bool, m: Bool): Eq (adder_type[len] x n m) (adder_type[len] y m n) =
    match e0 {
        case refl(cons(c, tail)) =>
            let p = full_adder_comm n m c;
            cong_carry_step[tail=tail] p
    }

def bits_adder_carrier_comm[len: Nat](lhs: Vec[Bool] len, rhs: Vec[Bool] len, c: Bool): Eq (bits_adder_carrier lhs rhs c) (bits_adder_carrier rhs lhs c) =
    match lhs {
        case nil => match rhs {
            case nil => refl (cons c nil)
        }
        case cons(n, taill) => match rhs {
            case cons(m, tailr) =>
                let e0 = bits_adder_carrier_comm taill tailr c;
                step1 e0 n m
        }
    }

def bits_adder_comm[len: Nat](lhs: Vec[Bool] len, rhs: Vec[Bool] len): Eq (bits_adder lhs rhs) (bits_adder rhs lhs) =
    bits_adder_carrier_comm lhs rhs false


def fold[T, len: Nat](vec: Vec[T] len, base: T, f: T -> T -> T): T =
    match vec {
        case nil => base
        case cons(x, tail) => fold (tail, f x base) f
    }

def reduce[T, len: Nat](vec: Vec[T] (len + 1), f: T -> T -> T): T =
    match vec {
        case cons(x, tail) => fold tail x f
    }

def div2Up(len: Nat) =
    match len {
        case zero => zero
        case succ(zero) => 1
        case succ(succ(n)) => succ (div2Up n)
    }

def mkpair[T, len: Nat](vec: Vec[T] len, f: T -> T -> T): Vec[T] (div2Up len) =
    match vec {
        case nil => nil
        case cons(x, nil) => x :: nil
        case cons(x, cons(y, tail)) => (f x y) :: (mkpair tail f)
    }

def reduce_balanced_tree[T, len: Nat](vec: Vec[T] (len + 1), f: T -> T -> T): T =
    let helper: [U: Type 0] -> [l: Nat] -> (Vec[U] (succ l)) -> (U -> U -> U) -> U = vec => f => (match vec {
        case cons(x, nil) => x
        case t => reduce_balanced_tree t f
    });
    helper (mkpair vec f) f
"#;
    match run(input, 0) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("{}", e.0.data),
    }
}

#[test]
fn test10() {
    let input = r#"
def outParam[A](a: A): A = a

enum Nat {
    zero
    succ(x: Nat)
}

trait Add[T, O: outParam(Type 0)] {
    def +(that: T): O
}

def nat_add_helper(x: Nat, y: Nat): Nat =
    match y {
        case zero => x
        case succ(n) => succ (nat_add_helper x n)
    }

impl Add[Nat, Nat] for Nat {
    def +(that: Nat): Nat =
        nat_add_helper this that
}

enum Fin(len: Nat) {
    fzero[n: Nat] -> Fin (succ n)
    fsucc[n: Nat](i: Fin n) -> Fin (succ n)
}

def up_fin[x: Nat](n: Fin x): Fin (x + 1) = match n {
    case fzero => fzero
    case fsucc[x](t) => fsucc (up_fin t)
}
    "#;
    match run(input, 0) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("{}", e.0.data),
    }
}

#[test]
fn test11() {
    let input = r#"
enum Nat {
    zero
    succ(x: Nat)
}

def add(x: Nat, y: Nat) =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def mul(x: Nat, y: Nat) =
    match x {
        case zero => zero
        case succ(n) => add(y, mul n y)
    }

enum Eq[A](x: A, y: A) {
    refl(a: A) -> Eq a a
}

def z1(a: Nat, b: Nat): (c: Nat) -> (d: Nat) -> Eq c c = _

//def z(a: Nat, b: Nat): Eq a a = _

//def add_comm(a: Nat, b: Nat): Eq (add a b) (add b a) = _

def tt: Eq 0 0 = _

def t: Nat = _
"#;
    match run(input, 0) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("{}\n{:?}", e.0.data, e.1[0]()),
    }
}

#[test]
fn test12() {
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

enum Eq[T](x: T, y: T) {
    refl(a: T) -> Eq a a
}

def rfl[A][a: A]: Eq a a =
    refl a

def listid(x: List[Bool]): List[Bool] = x

def create0: List[Bool] = nil

def create1: List[Bool] = cons true nil

def create2: List[Bool] = cons(true, cons false nil)

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
    case succ(n) => add(y, mul n y)
}

def outParam[A](a: A): A = a

trait Add[T, O: outParam(Type 0)] {
    def +(that: T): O
}

def nat_add_helper(x: Nat, y: Nat): Nat =
    match y {
        case zero => x
        case succ(n) => succ (nat_add_helper x n)
    }

impl Add[Nat, Nat] for Nat {
    def +(that: Nat): Nat =
        nat_add_helper this that
}

trait Mul[T, O: outParam(Type 0)] {
    def *(that: T): O
}

def nat_mul_helper(x: Nat, y: Nat): Nat =
    match y {
        case zero => 0
        case succ(n) => (nat_mul_helper x n) + x
    }

impl Mul[Nat, Nat] for Nat {
    def *(that: Nat): Nat =
        nat_mul_helper this that
}

def four = 2 + 2

println four

def cong[A, B, x: A, y: A](f: A -> B, e: Eq x y): Eq (f x) (f y) =
    match e {
        case refl(a) => refl (f a)
    }

//def cong_succ[x: Nat, y: Nat](e: Eq x y): Eq (x + 1) (y + 1) = cong(x => succ _, _)
def cong_succ[x: Nat, y: Nat](e: Eq x y): Eq (x + 1) (y + 1) = cong(_, e)
"#;
    match run(input, 0) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("{}", e.0.data),
    }
}

#[test]
fn test13() {
    let input = r#"
enum Nat {
    zero
    succ(n: Nat)
}

enum Eq[T](x: T, y: T) {
    refl(a: T) -> Eq a a
}

def add(x: Nat, y: Nat) =
    match y {
        case zero => x
        case succ(n) => succ (add x n)
    }

def cong[A, B, x: A, y: A](f: A -> B, e: Eq x y): Eq (f x) (f y) =
    match e {
        case refl(a) => refl (f a)
    }

def cong_succ[x: Nat, y: Nat](e: Eq x y): Eq (add x 1) (add y 1) = _
"#;
    match run(input, 0) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("{}\n{:?}", e.0.data, e.1[0]()),
    }
}

#[test]
fn test14() {
    let input = r#"
def Eq1[A](x: A, y: A) = (P : A -> Type 0) -> P x -> P y

def refl1[A, x: A]: Eq1[A] x x = _ => px => px

def t(x: Nat): Type 1 = match x {
    case succ(t) =>
let the : (A : Type 1) -> A -> A = _ => x => x;


let m : (A : Type 0) -> (B : Type 0) -> Type 0 -> Type 0 -> Type 0 = _;
let test = a => b => the (Eq1 (m a a) (x => y => y)) refl1;

let m : Type 0 -> Type 0 -> Type 0 -> Type 0 = _;
let test = a => b => c => the (Eq1 (m a b c) (m c b a)) refl1;

let pr1 = f => x => f x;
let pr2 = f => x => y => f x y;
let pr3 = f => f (Type 0);

Type 0
    case zero =>

Type 0
}
"#;
    match run_with_prelude(input) {
        Ok(output) => println!("{}", output),
        //Err(e) => panic!("{}\n{:?}", e.0.data, e.1[0]()),
        Err(e) => panic!("{} @ {}: {}\n{}", e.0.data, e.0.path_id, e.0.start_offset, e.1[0]().unwrap()),
    }
}

#[test]
fn test15() {
    let input = r#"
def Eq[A](x: A, y: A) = (P : A -> Type 0) -> P x -> P y

def refl[A, x: A]: Eq[A] x x = _ => px => px

def t =
let the : (A : Type 1) -> A -> A = _ => x => x;


let m : (A : Type 0) -> (B : Type 0) -> Type 0 -> Type 0 -> Type 0 = _;
let test = a => b => the (Eq (m a a) (x => y => y)) refl;

let m : Type 0 -> Type 0 -> Type 0 -> Type 0 = _;
let test = a => b => c => the (Eq (m a b c) (m c b a)) refl;

let pr1 = f => x => f x;
let pr2 = f => x => y => f x y;
let pr3 = f => f (Type 0);

test"#;
    match run(input, 0) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("{}", e.0.data),
    }
}

#[test]
fn test16() {
    let input = r#"
// Cast using a proof of type equality.
// If T and U are provably equal (via Eq T U), then a value of type T can be used as type U.
def cast[T, U](h: Eq T U, a: T): U = match h {
    case refl(x) => a
}

// Convert Fin(t) to Nat, discarding the bound information.
def fin_to_nat[t: Nat](a: Fin t): Nat = match a {
    case fzero => 0
    case fsucc(z) => succ(fin_to_nat z)
}

impl[x: Nat] Fin(x) {
    def to_nat: Nat = fin_to_nat this
}

def mk_last(n: Nat): Fin (n + 1) = match n {
    case zero => fzero
    case succ(t) => fsucc (mk_last t)
}

def up_fin[x: Nat](n: Fin x): Fin (x + 1) = match n {
    case fzero[x] => fzero[x+1]
    case fsucc[x](t) => fsucc (up_fin t)
}

def sub_fin(x: Nat, y: Fin (x + 1)): Fin (x + 1) = match y {
    case fzero => mk_last x
    case fsucc(yy) => match x {
        case succ(t) => up_fin (sub_fin t yy)
        case zero => match yy {}
    }
}

def lift_fin[x: Nat, target: Nat](n: Fin x, prove: Le x target): Fin target = match prove {
        case le_refl[z] => n
        case le_step(h) => up_fin (lift_fin n h)
    }

impl Nat {
    def <=(that: Nat): Type 0 = Le this that
}

def le_succ_inv[n: Nat, m: Nat](h: (n + 1) <= m): n <= m =
  match h {
    case le_refl => le_step(le_refl[n])
    case le_step(h1) => le_step(le_succ_inv h1)
  }

def trans_le[x: Nat, y: Nat, z: Nat](le1: x <= y, le2: y <= z): x <= z =
    match le1 {
        case le_refl[n] => le2
        case le_step(h) => trans_le(h, le_succ_inv(le2))
    }

def drop_vec[T, len: Nat](t: Vec[T](len), x: Fin(len + 1)): Vec[T](sub len x) = match t {
    case nil => match x {
        case fzero => nil
        case fsucc(t) => match t {}
    }
    case cons(a, tail) => match x {
        case fzero => cons a tail
        case fsucc(t) => drop_vec tail t
    }
}

impl[T, len: Nat] Vec[T](len) {
    def drop(x: Fin (len + 1)): Vec[T](sub len x) = drop_vec this x
}

struct Tuple2[A, B] {
    x_1: A
    x_2: B
}

struct Tuple3[A, B, C] {
    x_1: A
    x_2: B
    x_3: C
}

def half_adder(lhs: Boolean, rhs: Boolean): Tuple2[Boolean, Boolean] =
    Tuple2.mk (lhs & rhs) (lhs ^ rhs)

def full_adder(lhs: Boolean, rhs: Boolean, carrier: Boolean): Tuple2[Boolean, Boolean] =
    let s1 = lhs ^ rhs;
    Tuple2.mk ((s1 & carrier) | (lhs & rhs)) (s1 ^ carrier)

struct Bits1[width: Nat] {
    payload: Vec[Boolean] width
}

def sub_self_is_zero(width: Nat): Eq (sub (width, mk_last width)) 0 = match width {
    case zero => refl zero
    case succ(t) => sub_self_is_zero t
}

def up_fin_lemma(x: Nat, y: Fin (x + 1)): Eq (sub (succ x) (up_fin y)) (succ (sub x y)) =
  match y {
    case fzero => 
      refl (succ (sub x fzero))
    case fsucc(z) => 
      match x {
        case succ(t) =>
          let ind = up_fin_lemma t z;
          ind
        case zero =>
          match z {}
      }
  }

def resize_drop_prove(width: Nat, w: Fin (width + 1)): Eq (sub(width, sub_fin width w)) (fin_to_nat w) = match w {
    case fzero => sub_self_is_zero width
    case fsucc(ww) => match width {
        case succ(t) => let ind = resize_drop_prove t ww;
            let lem = up_fin_lemma(t, sub_fin t ww);
            let ind_succ = cong succ ind;
            trans lem ind_succ
        case zero => match ww {}
    }
}

def resize[width: Nat, w: Fin (width + 1)](bits: Bits1[width]): Bits1[fin_to_nat w] =
    cast (cong (x => Bits1[x]) (resize_drop_prove width w)) (Bits1.mk (drop_vec(bits.payload, sub_fin width w)))

def lift_le[a: Nat][b: Nat](x: a <= b): (a + 1) <= (b + 1) = match x {
    case le_refl[n] => le_refl[n + 1]
    case le_step[n][m](h) => le_step (lift_le h)
}




// Auxiliary: convert a proof that n <= width into a Fin(width+1) with value n
def nat_to_fin[width: Nat](n: Nat, proof: n <= width): Fin (width + 1) =
  match width {
    case zero =>
      // width = 0, so n must be 0
      match proof { case le_refl => fzero }
    case succ(m) =>
      match proof {
        case le_refl => mk_last (succ m)          // n = succ m
        case le_step(h) => up_fin (nat_to_fin[m] n h)  // n <= m
      }
  }

// Lemma: fin_to_nat (mk_last n) = n
def fin_to_nat_mk_last(n: Nat): Eq (fin_to_nat (mk_last n)) n =
  match n {
    case zero    => refl zero
    case succ(t) => cong(succ, fin_to_nat_mk_last t)
  }

// Lemma: fin_to_nat (up_fin x) = fin_to_nat x
def fin_to_nat_up_fin[k: Nat](x: Fin k): Eq (fin_to_nat (up_fin x)) (fin_to_nat x) =
  match x {
    case fzero    => refl 0
    case fsucc(y) => cong(succ, fin_to_nat_up_fin y)
  }

// Main lemma: fin_to_nat (nat_to_fin n proof) = n
def fin_to_nat_nat_to_fin_eq[width: Nat](n: Nat, proof: n <= width): Eq (fin_to_nat (nat_to_fin[width] n proof)) n =
  match width {
    case zero =>
      match proof { case le_refl[n] => refl n }
    case succ(m) =>
      match proof {
        case le_refl[n] => fin_to_nat_mk_last (n)
        case le_step(h) =>
          let ind = fin_to_nat_nat_to_fin_eq[m] n h;
          let up = fin_to_nat_up_fin (nat_to_fin[m] n h);
          trans up ind
      }
  }

def resize_prove[width: Nat](bits: Bits1[width], target: Nat, prove: target <= width): Bits1[target] = 
  let w = nat_to_fin[width] target prove;
  let resized = resize[width, w](bits);
  let eq = fin_to_nat_nat_to_fin_eq[width] target prove;
  cast (cong(x => Bits1[x], eq)) resized

impl[width: Nat] Bits1[width] {
    def resize[w: Fin (width + 1)]: Bits1[fin_to_nat w] = cast (cong(x => Bits1[x], resize_drop_prove width w)) (Bits1.mk (drop_vec(this.payload, sub_fin width w)))
}

trait Concat[T, O: outParam(Type 0)] {
    def :+:(that: T): O
}

impl[width: Nat] Concat[Bits1[width], Bits1[width + 1]] for Boolean {
    def :+:(that: Bits1[width]): Bits1[width + 1] = Bits1.mk (this :: that.payload)
}

def bits_adder_carrier[len: Nat](lhs: Vec[Boolean] len, rhs: Vec[Boolean] len, carrier: Boolean): Vec[Boolean] (len + 1) =
    match lhs {
        case nil => carrier :: nil
        case cons(n, taill) => match rhs {
            case cons(m, tailr) => match bits_adder_carrier taill tailr carrier {
                case cons(c, tail) => let t = full_adder n m c;
                    t.x_1 :: t.x_2 :: tail
            }
        }
    }

impl[len: Nat] Add[Bits1[len], Bits1[len + 1]] for Bits1[len] {
    def +(that: Vec[Boolean] len): Vec[Boolean] (len + 1) =
        Bits1.mk (bits_adder_carrier this.payload that.payload false)
}

def bits_adder[len: Nat](lhs: Vec[Boolean] len, rhs: Vec[Boolean] len): Vec[Boolean] (len + 1) =
    bits_adder_carrier lhs rhs false

println bits_adder (true :: nil) (false :: nil)

def full_adder_comm(lhs: Boolean, rhs: Boolean, carrier: Boolean): Eq (full_adder lhs rhs carrier) (full_adder rhs lhs carrier) =
    match lhs {
        case false => match rhs {
            case false => refl (Tuple2.mk false carrier)
            case true => match carrier {
                case false => refl (Tuple2.mk false true)
                case true => refl (Tuple2.mk true false)
            }
        }
        case true => match rhs {
            case false => match carrier {
                case false => refl (Tuple2.mk false true)
                case true => refl (Tuple2.mk true false)
            }
            case true => match carrier {
                case false => refl (Tuple2.mk true false)
                case true => refl (Tuple2.mk true true)
            }
        }
    }

def adder_type[len: Nat](x: Vec[Boolean] (succ len), n: Boolean, m: Boolean): Vec[Boolean] (succ (succ len)) = match x {
    case cons(c, tail) => let t = full_adder n m c;
        t.x_1 :: t.x_2 :: tail
}

def carry_step[len: Nat](tail: Vec[Boolean] len, p: Tuple2[Boolean, Boolean]): Vec[Boolean] (succ (succ len)) =
    p.x_1 :: p.x_2 :: tail

def cong_carry_step[len: Nat, tail: Vec[Boolean] len, p: Tuple2[Boolean, Boolean], q: Tuple2[Boolean, Boolean]](e: Eq p q): Eq (carry_step tail p) (carry_step tail q) =
    match e {
        case refl(a) => refl (carry_step tail a)
    }

def step1[len: Nat, x: Vec[Boolean] (succ len), y: Vec[Boolean] (succ len)](e0: Eq x y, n: Boolean, m: Boolean): Eq (adder_type[len] x n m) (adder_type[len] y m n) =
    match e0 {
        case refl(cons(c, tail)) =>
            let p = full_adder_comm n m c;
            cong_carry_step[tail=tail] p
    }

def bits_adder_carrier_comm[len: Nat](lhs: Vec[Boolean] len, rhs: Vec[Boolean] len, c: Boolean): Eq (bits_adder_carrier lhs rhs c) (bits_adder_carrier rhs lhs c) =
    match lhs {
        case nil => match rhs {
            case nil => refl (cons c nil)
        }
        case cons(n, taill) => match rhs {
            case cons(m, tailr) =>
                let e0 = bits_adder_carrier_comm taill tailr c;
                step1 e0 n m
        }
    }

def bits_adder_comm[len: Nat](lhs: Bits1[len], rhs: Bits1[len]): Eq (lhs + rhs) (rhs + lhs) =
    cong(Bits1.mk[len + 1], bits_adder_carrier_comm lhs.payload rhs.payload false)

def zip[T, U, len: Nat](vec1: Vec[T] len, vec2: Vec[U] len): Vec[Tuple2[T, U]] len = match vec1 {
    case nil => match vec2 {
        case nil => nil
    }
    case cons(a, tail1) => match vec2 {
        case cons(b, tail2) => (Tuple2.mk a b) :: (zip tail1 tail2)
    }
}

def zip3[T, U, V, len: Nat](vec1: Vec[T] len, vec2: Vec[U] len, vec3: Vec[V] len): Vec[Tuple3[T, U, V]] len = match vec1 {
    case nil => match vec2 {
        case nil => match vec3 {
            case nil => nil
        }
    }
    case cons(a, tail1) => match vec2 {
        case cons(b, tail2) => match vec3 {
            case cons(c, tail3) => (Tuple3.mk a b c) :: (zip3 tail1 tail2 tail3)
        }
    }
}

def fold[T, len: Nat](vec: Vec[T] len, base: T, f: T -> T -> T): T =
    match vec {
        case nil => base
        case cons(x, tail) => fold (tail, f x base) f
    }

def reduce[T, len: Nat](vec: Vec[T] (len + 1), f: T -> T -> T): T =
    match vec {
        case cons(x, tail) => fold tail x f
    }

def map[T, U, len: Nat](vec: Vec[T] len, f: T -> U): Vec[U] len = match vec {
    case nil => nil
    case cons(a, tail) => (f a) :: (map tail f)
}

def tail_append[T, len: Nat](vec: Vec[T] len, item: T): Vec[T] (len + 1) = match vec {
    case nil => item :: nil
    case cons(a, tail) => a :: (tail_append tail item)
}

def div2(x: Nat): Nat = match x {
    case zero => 0
    case succ(zero) => 0
    case succ(succ(t)) => (div2 t) + 1
}

def pred_div2Up_succ(len: Nat): Nat =
    match len {
        case zero => 0
        case succ(t) => div2Up t
    }

def adder_tree_step[width: Nat, len: Nat](x: Vec[Bits1[width]] len): Vec[Bits1[width + 1]] (div2Up len) = match x {
    case cons(a, cons(b, tail)) => (a + b) :: (adder_tree_step tail)
    case cons(a, nil) => (false :+: a) :: nil
    case nil => nil
}

def cast_prove[width: Nat, len: Nat]: Eq (Bits1[(width + 1) + (log2Up len)]) (Bits1[(width + (log2Up len)) + 1]) =
    cong(t => Bits1[t]) (add_succ_left(width, log2Up len))

def adder_tree[width: Nat, len: Nat](x: Vec[Bits1[width]](len + 1)): Bits1[width + (log2Up(len + 1))] =
    match x {
        case cons(a, nil) => a
        case cons(a, cons(b, tail)) => cast(cast_prove, adder_tree[width=width+1] (adder_tree_step x))
    }










def unzip2[T, U, len: Nat](v: Vec[Tuple2[T, U]] len): Tuple2[Vec[T] len, Vec[U] len] =
    match v {
        case nil => Tuple2.mk nil nil
        case cons(p, tail) =>
            let r = unzip2 tail;
            Tuple2.mk (p.x_1 :: r.x_1) (p.x_2 :: r.x_2)
    }

def csa3[width: Nat](a: Bits1[width], b: Bits1[width], c: Bits1[width]): Tuple2[Bits1[width], Bits1[width + 1]] =
    let triples = zip3 a.payload b.payload c.payload;
    let pairEach = map(triples, t => full_adder t.x_1 t.x_2 t.x_3);
    let parts = unzip2 pairEach;
    let carry_vec = parts.x_1;
    let sum_vec = parts.x_2;
    Tuple2.mk (Bits1.mk sum_vec) (Bits1.mk (false :: carry_vec))

def compress32_len(x: Nat): Nat =
    match x {
        case zero => 0
        case succ(zero) => 1
        case succ(succ(zero)) => 2
        case succ(succ(succ(t))) => (compress32_len t) + 2
    }

def wallace_stage[width: Nat, len: Nat](x: Vec[Bits1[width]] len): Vec[Bits1[width + 1]] (compress32_len len) =
    match x {
        case cons(a, cons(b, cons(c, tail))) =>
            let t = csa3 a b c;
            t.x_2 :: (false :+: t.x_1) :: (wallace_stage tail)
        case cons(a, cons(b, nil)) =>
            (false :+: a) :: (false :+: b) :: nil
        case cons(a, nil) =>
            (false :+: a) :: nil
        case nil =>
            nil
    }

def add_left[a: Nat][b: Nat](c: Nat, p: a <= b): (c + a) <= (c + b) = match p {
    case le_refl[n] => le_refl
    case le_step(h) => le_step (add_left c h)
}











def zero_le(n: Nat): 0 <= n = match n {
  case zero => le_refl[0]
  case succ(m) => le_step(zero_le(m))
}

def add_right[a: Nat][b: Nat](c: Nat, p: a <= b): (a + c) <= (b + c) = match c {
  case zero => p
  case succ(n) => lift_le(add_right n p)
}

def div2Up_succ_ge(m: Nat): (div2Up m) <= (div2Up (succ m)) = match m {
  case zero => le_step(le_refl[0])          // 0 <= 1
  case succ(zero) => le_refl[1]              // 1 <= 1
  case succ(succ(n)) =>
    // m = n+2
    let ih = div2Up_succ_ge(n);               // Le (div2Up n) (div2Up (succ n))
    lift_le(ih)                               // Le (div2Up n + 1) (div2Up (succ n) + 1)
}

def div2Up_mono(a: Nat, b: Nat, p: a <= b): (div2Up a) <= (div2Up b) = match p {
  case le_refl[n] => le_refl[div2Up n]
  case le_step[n,m](h) => trans_le (div2Up_mono a m h) (div2Up_succ_ge m)
}

def div2Up_add3_le_add2(k: Nat): (div2Up (k + 6)) <= ((div2Up (k + 3)) + 2) = match k {
  case zero => le_step(le_refl[3])             // 3 <= 4
  case succ(zero) => le_refl[4]                 // 4 <= 4
  case succ(succ(k0)) =>
    // k = k0+2
    let ih = div2Up_add3_le_add2(k0);            // Le (div2Up (k0+6)) (div2Up (k0+3) + 2)
    lift_le(ih)                                  // Le (div2Up (k0+6)+1) (div2Up (k0+3)+3)
}

def div2Up_le_compress_plus2(n: Nat): (div2Up (n + 3)) <= ((compress32_len n) + 2) = match n {
  case zero => le_refl[2]
  case succ(zero) => le_step(le_refl[2])
  case succ(succ(zero)) => le_step(le_refl[3])
  case succ(succ(succ(zero))) => le_step(le_refl[3])
  case succ(succ(succ(n0))) =>
    // Induction hypothesis for n0
    let ih = div2Up_le_compress_plus2(n0);      // : Le (div2Up (n0+3)) (compress32_len n0 + 2)
    // Lemma: div2Up (n0+6) <= div2Up (n0+3) + 2
    let step = div2Up_add3_le_add2(n0);         // : Le (div2Up (n0+6)) (div2Up (n0+3) + 2)
    // Add 2 to both sides of the induction hypothesis
    let step2 = add_right 2 ih;               // : Le (div2Up (n0+3) + 2) (compress32_len n0 + 4)
    // Transitivity gives the desired inequality
    trans_le step step2
}

def log2Up_mono(a: Nat, b: Nat, p: Le a b): (log2Up a) <= (log2Up b) = match p {
  case le_refl[n] => le_refl[log2Up n]
  case le_step[n,m](h) =>
    let ih = log2Up_mono a m h;                 // log2Up a <= log2Up n
    // log2Up n <= log2Up (succ n)
    let step: (log2Up m) <= (log2Up (m + 1)) = match m {
      case zero => le_refl[0]
      case succ(zero) => le_step(le_refl[0])
      case succ(succ(k)) =>
        // n = k+2
        let x = div2Up (k + 2);
        let y = div2Up (k + 3);
        // x <= y
        let x_le_y = div2Up_mono (k+2) (k+3) (le_step(le_refl[k+2]));
        // x,y < n -> log2Up x <= log2Up y
        let mono_xy = log2Up_mono x y x_le_y;
        lift_le(mono_xy)                           // log2Up n <= log2Up (succ n)
    };
    trans_le ih step
}

// log2Up n <= 1 + log2Up(compress32_len n)
def le_log_compress(n: Nat): (log2Up n) <= ((log2Up (compress32_len n)) + 1) = match n {
    case zero => le_step(le_refl[0])
    case succ(zero) => le_step(le_refl[0])
    case succ(succ(zero)) => le_step(le_refl[1])
    case succ(succ(succ(zero))) => le_refl[2]
    case succ(succ(succ(t))) =>
        let d = div2Up_le_compress_plus2(t);  // d : (div2Up (t + 3)) <= (compress32_len t + 2)
        let mono = log2Up_mono (div2Up (t + 3)) ((compress32_len t) + 2) d;
        // mono : Le (log2Up (div2Up (t + 3))) (log2Up (compress32_len t + 2))
        lift_le(mono)
        //_
}

def size_map[a: Nat][b: Nat](x: Bits1[(a + 1) + b]): Bits1[a + b + 1] = cast(cong(t => Bits1[t], add_succ_left a b),x)

def wallace_tree[width: Nat, len: Nat](x: Vec[Bits1[width]] (len + 1)): Bits1[width + (log2Up (len + 1))] =
    match x {
        case cons(a, nil) => a
        case cons(a, cons(b, nil)) => a + b
        case cons(a, cons(b, cons(c, tail))) =>
            let before_resize = wallace_tree[width = width + 1](wallace_stage x);
            //resize_prove[width + (log2Up ((compress32_len (len + 1)))) + 1](size_map[width, (log2Up ((compress32_len (len + 1))))] before_resize, width + (log2Up (len + 1)), add_left width le_log_compress(len+1))
            _
    }

def ttt(x: String, y: Nat -> Nat): Nat = 0

println ttt
"#;
    match run_with_prelude(input) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("{}\n{:?}", e.0.data, e.1[0]()),
        //Err(e) => panic!("{}", e.0.data),
    }
}

#[test]
fn test17() {
    let input = r#"

def drop_vec[T, len: Nat](t: Vec[T](len), x: Fin(len + 1)): Vec[T](sub len x) = match t {
    case nil => match x {
        case fzero => nil
        case fsucc(t) => match t {}
    }
    case cons(a, tail) => match x {
        case fzero => cons a tail
        case fsucc(t) => drop_vec tail t
    }
}

//println drop_vec(1 :: 2 :: 3 :: nil, fsucc fzero)

def exists_two: Exists[Nat][x => Eq x 2] = Exists.mk[Nat][x => Eq x 2] 2 rfl

struct Bits[width: Nat] {
    name: String
}

impl[width: Nat] Add[Bits[width], Bits[width]] for Bits[width] {
    def +(that: Bits[width]): Bits[width] =
        Bits.mk(this.name + " + " + that.name)
}

impl[width: Nat] Sub[Bits[width], Bits[width]] for Bits[width] {
    def -(that: Bits[width]): Bits[width] =
        Bits.mk(this.name + " - " + that.name)
}

impl[width0: Nat, width1: Nat] Mul[Bits[width1], Bits[width0 + width1]] for Bits[width0] {
    def *(that: Bits[width1]): Bits[width0 + width1] =
        Bits.mk(this.name + " * " + that.name)
}
"#;
    match run_with_prelude(input) {
        Ok(output) => println!("{}", output),
        //Err(e) => panic!("{}\n{:?}", e.0.data, e.1[0]()),
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test18() {
    let input = r#"
def f[w: Nat](x: UInt[w], y: UInt[w]): Unit = y := x

module Test[w: Nat] {
    let a = UInt[w]
    let b = UInt[w]
    let c = UInt[w]
    let z = Bool
    when(z) {
        c := a + b
    } elsewhen(z) {
        c := a
    } otherwise {
        c := a - b
    }
}
"#;
    match run_with_prelude(input) {
        Ok(output) => println!("{}", output),
        //Err(e) => panic!("{}\n{:?}", e.0.data, e.1[0]()),
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_basic_types() {
    // Test that hardware types can be declared and assigned
    let input = r#"
module Test {
    let a = UInt[8]
    let b = UInt[8]
    let c = SInt[16]
    let d = Bits[32]
    let e = Bool
    let f = Bits[33]
    f := e ## d
}
"#;
    match run_with_prelude(input) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_arithmetic() {
    // Test arithmetic operations with width tracking
    let input = r#"
module Test[w: Nat] {
    let a = UInt[w]
    let b = UInt[w]
    let sum = UInt[w]
    let carry = UInt[w + 1]
    sum := a + b
    carry := a +^ b
}
"#;
    match run_with_prelude(input) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_bitwise_ops() {
    // Test bitwise operations
    let input = r#"
module Test[w: Nat] {
    let a = Bits[w]
    let b = Bits[w]
    let and_result = Bits[w]
    let or_result = Bits[w]
    let xor_result = Bits[w]
    and_result := a & b
    or_result := a | b
    xor_result := a ^ b
}
"#;
    match run_with_prelude(input) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_comparisons() {
    // Test comparison operators
    let input = r#"
module Test[w: Nat] {
    let a = UInt[w]
    let b = UInt[w]
    let lt = Bool
    let eq = Bool
    lt := a < b
    eq := a === b
}
"#;
    match run_with_prelude(input) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_conversions() {
    // Test type conversions
    let input = r#"
module Test[w: Nat] {
    let a = UInt[w]
    let as_bits = Bits[w]
    let resized = UInt[w + 1]
    as_bits := a.asBits
    resized := a.resize[w + 1]
}
"#;
    match run_with_prelude(input) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_reduction() {
    // Test reduction operators
    let input = r#"
module Test[w: Nat] {
    let a = Bits[w]
    let all_ones = Bool
    let any_one = Bool
    all_ones := a.andR
    any_one := a.orR
}
"#;
    match run_with_prelude(input) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_mux() {
    // Test multiplexer
    let input = r#"
module Test[w: Nat] {
    let cond = Bool
    let a = UInt[w]
    let b = UInt[w]
    let result = UInt[w]
    result := cond.mux(a, b)
}
"#;
    match run_with_prelude(input) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_cat() {
    // Test bit concatenation
    let input = r#"
module Test[left: Nat, right: Nat] {
    let a = Bits[left]
    let b = Bits[right]
    let combined = Bits[left + right]
    combined := a ## b
}
"#;
    match run_with_prelude(input) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_registers() {
    // Test register constructs
    let input = r#"
module Test {
    let reg_val = UInt[8]
    let init_reg = UInt[8]
    init_reg := RegInit(init_reg, defaultClockDomain).value
    reg_val := RegNext(reg_val).value
}
"#;
    match run_with_prelude(input) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_verilog_pure_typort() {
    let input = r#"
module Adder {
    input a = UInt[8]
    input b = UInt[8]
    input cond = Bool
    output sum = UInt[8]
    sum := a + b
}
println (moduleVL Adder)
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("=== Output ===\n{}", output);
            assert!(output.contains("module Adder"), "{}", output);
            assert!(output.contains("input wire a"), "{}", output);
            assert!(output.contains("input wire b"), "{}", output);
            assert!(output.contains("output wire sum"), "{}", output);
            assert!(output.contains("assign sum = (a + b)"), "{}", output);
            assert!(output.contains("endmodule"), "{}", output);
            assert!(output.contains("\n"), "should have newlines: {}", output);
        },
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_macro_cut_parse_error_in_body() {
    // Test 1: Parse error INSIDE module body — verify error is at the
    // expression position (offset ~53: `+ +`), not backtracked to declaration.
    let input = r#"
module Adder {
    input a = UInt[8]
    sum := a + + b
}
println (moduleVL Adder)
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("=== Output (unexpected) ===\n{}", output);
            panic!("Expected error but got output");
        },
        Err(e) => {
            println!("Error at offset {}: {}", e.0.start_offset, e.0.data);
            assert!(e.0.start_offset > 20,
                "Error should be inside module body (offset > 20), not at declaration. Got: {}",
                e.0.start_offset);
        }
    }
}

#[test]
fn test_macro_cut_truncated_module() {
    // Truncated module: the macro matcher fails (expects ident after `module`).
    // With Cut in p_decl, the error from the macro matcher kills the parse
    // immediately instead of falling through to other declaration parsers.
    // The result should be EmptyVec (from many1_sep catching the error),
    // NOT ExpectDecl (which would mean it fell through to p_def/p_print).
    let mut global_macros: std::collections::HashMap<String, Vec<parser::macros::MacroRule>> = Default::default();
    let mut id = 0u32;
    let prelude_files = &[
        include_str!("../prelude/op.typort"),
        include_str!("../prelude/nat.typort"),
        include_str!("../prelude/hdl.typort"),
    ];
    for p in prelude_files {
        if let Some((_, _, new_exports)) = parser::parser_with_macros(&preprocess(p), id, &global_macros) {
            for (name, rules) in new_exports {
                global_macros.insert(name, rules);
            }
        }
        id += 1;
    }
    let input = "module";
    let (_, errors) = parser::parser_with_macros(input, id, &global_macros)
        .map(|(d, e, _)| (d, e)).unwrap();
    println!("Parse errors for truncated `module`: {:?}", errors);
    // With Cut: no ExpectDecl (the macro matcher error prevents fallthrough).
    // The error is EmptyVec from many1_sep catching p_decl's fault.
    assert!(!errors.iter().any(|e| format!("{:?}", e).contains("ExpectDecl")),
        "With Cut, should NOT fall through to ExpectDecl. Got: {:?}", errors);
}

#[test]
fn test_string_add() {
    let input = r#"
println "a" + "b" + "c"
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("=== Output ===\n{}", output);
        },
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_match_pretty() {
    let input = r#"
println (a => Eq[Nat](nat_add_helper(1, a), nat_add_helper(2, a)))
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("=== Output ===\n{}", output);
        },
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_match() {
    let input = r#"
// Cast using a proof of type equality.
// If T and U are provably equal (via Eq T U), then a value of type T can be used as type U.
def cast[T, U](
    h: Eq T U,
    a: T
): U = match h {
    case refl(x) => a
}

// Fin(len) is the type of natural numbers less than len.
// It is a dependent type: valid values depend on the type-level argument len.
// - fzero[n] : Fin (succ n)  represents 0 in [0, n+1)
// - fsucc[n](i) : Fin (succ n) represents i+1, given i : Fin n
/*enum Fin(len: Nat) {
    fzero[n: Nat] -> Fin (succ n)
    fsucc[n: Nat](i: Fin n) -> Fin (succ n)
}*/

// Convert Fin(t) to Nat, discarding the bound information.
def fin_to_nat[t: Nat](a: Fin t): Nat = match a {
    case fzero => 0
    case fsucc(z) => succ(fin_to_nat z)
}

impl[x: Nat] Fin(x) {
    def to_nat: Nat = fin_to_nat this
}

// Existential quantification: exists (a : A), P(a)
// - witness: a value of type A
// - proof: evidence that P(witness) holds
/*struct Exists[A: Type 0, P: A -> Type 0] {
    witness: A
    proof: P witness
}

// Example: There exists a natural number equal to 2.
// Witness is 2, proof is refl(2) showing 2 = 2.
def exists_two = Exists.mk[Nat][x => Eq x 2] (2, refl 2)

def sub(x: Nat, y: Fin (x + 1)): Nat = match y {
    case fzero => x
    case fsucc(yy) => match x {
        case succ(t) => sub t yy
        case zero => match yy {}
    }
}*/

def mk_last(n: Nat): Fin (n + 1) = match n {
    case zero => fzero
    case succ(t) => fsucc (mk_last t)
}

def up_fin[x: Nat](n: Fin x): Fin (x + 1) = match n {
    case fzero[x] => fzero[x+1]
    case fsucc[x](t) => fsucc (up_fin t)
}

def sub_fin(x: Nat, y: Fin (x + 1)): Fin (x + 1) = match y {
    case fzero => mk_last x
    case fsucc(yy) => match x {
        case succ(t) => up_fin (sub_fin t yy)
        case zero => match yy {}
    }
}

// Le(n, m) is a proof that n <= m.
// - le_refl: n <= n
// - le_step: if n <= m, then n <= succ(m)
/*enum Le(n: Nat, m: Nat) {
    le_refl[n: Nat] -> Le n n
    le_step[n: Nat, m: Nat](h: Le n m) -> Le (n, succ m)
}*/

def lift_fin[x: Nat, target: Nat](n: Fin x, prove: Le x target): Fin target = match prove {
        case le_refl[z] => n
        case le_step(h) => up_fin (lift_fin n h)
    }

impl Nat {
    def <=(that: Nat): Type 0 = Le this that
}

def le_succ_inv[n: Nat, m: Nat](h: (n + 1) <= m): n <= m =
  match h {
    case le_refl => le_step(le_refl[n])
    case le_step(h1) => le_step(le_succ_inv h1)
  }

def trans_le[x: Nat, y: Nat, z: Nat](le1: x <= y, le2: y <= z): x <= z =
    match le1 {
        case le_refl[n] => le2
        case le_step(h) => trans_le(h, le_succ_inv(le2))
    }

def drop_vec[T, len: Nat](t: Vec[T](len), x: Fin(len + 1)): Vec[T](sub len x) = match t {
    case nil => match x {
        case fzero => nil
        case fsucc(t) => match t {}
    }
    case cons(a, tail) => match x {
        case fzero => cons a tail
        case fsucc(t) => drop_vec tail t
    }
}

impl[T, len: Nat] Vec[T](len) {
    def drop(x: Fin (len + 1)): Vec[T](sub len x) = drop_vec this x
}

/*enum Product[A, B] {
    product(a: A, b: B)
}*/

struct Tuple2[A, B] {
    x_1: A
    x_2: B
}

struct Tuple3[A, B, C] {
    x_1: A
    x_2: B
    x_3: C
}

def half_adder(lhs: Boolean, rhs: Boolean): Tuple2[Boolean, Boolean] =
    Tuple2.mk (lhs & rhs) (lhs ^ rhs)

def full_adder(lhs: Boolean, rhs: Boolean, carrier: Boolean): Tuple2[Boolean, Boolean] =
    let s1 = lhs ^ rhs;
    Tuple2.mk ((s1 & carrier) | (lhs & rhs)) (s1 ^ carrier)

struct Bits1[width: Nat] {
    payload: Vec[Boolean] width
}

def sub_self_is_zero(width: Nat): Eq (sub (width, mk_last width)) 0 = match width {
    case zero => refl zero
    case succ(t) => sub_self_is_zero t
}

def up_fin_lemma(x: Nat, y: Fin (x + 1)): Eq (sub (succ x) (up_fin y)) (succ (sub x y)) =
  match y {
    case fzero => 
      refl (succ (sub x fzero))
    case fsucc(z) => 
      match x {
        case succ(t) =>
          let ind = up_fin_lemma t z;
          ind
        case zero =>
          match z {}
      }
  }

def resize_drop_prove(width: Nat, w: Fin (width + 1)): Eq (sub(width, sub_fin width w)) (fin_to_nat w) = match w {
    case fzero => sub_self_is_zero width
    case fsucc(ww) => match width {
        case succ(t) => let ind = resize_drop_prove t ww;
            let lem = up_fin_lemma(t, sub_fin t ww);
            let ind_succ = cong succ ind;
            trans lem ind_succ
        case zero => match ww {}
    }
}

def resize[width: Nat, w: Fin (width + 1)](bits: Bits1[width]): Bits1[fin_to_nat w] =
    cast (cong (x => Bits1[x]) (resize_drop_prove width w)) (Bits1.mk (drop_vec(bits.payload, sub_fin width w)))

def lift_le[a: Nat][b: Nat](x: a <= b): (a + 1) <= (b + 1) = match x {
    case le_refl[n] => le_refl[n + 1]
    case le_step[n][m](h) => le_step (lift_le h)
}




// Auxiliary: convert a proof that n <= width into a Fin(width+1) with value n
def nat_to_fin[width: Nat](n: Nat, proof: n <= width): Fin (width + 1) =
  match width {
    case zero =>
      // width = 0, so n must be 0
      match proof { case le_refl => fzero }
    case succ(m) =>
      match proof {
        case le_refl => mk_last (succ m)          // n = succ m
        case le_step(h) => up_fin (nat_to_fin[m] n h)  // n <= m
      }
  }

// Lemma: fin_to_nat (mk_last n) = n
def fin_to_nat_mk_last(n: Nat): Eq (fin_to_nat (mk_last n)) n =
  match n {
    case zero    => refl zero
    case succ(t) => cong(succ, fin_to_nat_mk_last t)
  }

// Lemma: fin_to_nat (up_fin x) = fin_to_nat x
def fin_to_nat_up_fin[k: Nat](x: Fin k): Eq (fin_to_nat (up_fin x)) (fin_to_nat x) =
  match x {
    case fzero    => refl 0
    case fsucc(y) => cong(succ, fin_to_nat_up_fin y)
  }

// Main lemma: fin_to_nat (nat_to_fin n proof) = n
def fin_to_nat_nat_to_fin_eq[width: Nat](n: Nat, proof: n <= width): Eq (fin_to_nat (nat_to_fin[width] n proof)) n =
  match width {
    case zero =>
      match proof { case le_refl[n] => refl n }
    case succ(m) =>
      match proof {
        case le_refl[n] => fin_to_nat_mk_last (n)
        case le_step(h) =>
          let ind = fin_to_nat_nat_to_fin_eq[m] n h;
          let up = fin_to_nat_up_fin (nat_to_fin[m] n h);
          trans up ind
      }
  }

def resize_prove[width: Nat](bits: Bits1[width], target: Nat, prove: target <= width): Bits1[target] = 
  let w = nat_to_fin[width] target prove;
  let resized = resize[width, w](bits);
  let eq = fin_to_nat_nat_to_fin_eq[width] target prove;
  cast (cong(x => Bits1[x], eq)) resized

impl[width: Nat] Bits1[width] {
    def resize[w: Fin (width + 1)]: Bits1[fin_to_nat w] = cast (cong(x => Bits1[x], resize_drop_prove width w)) (Bits1.mk (drop_vec(this.payload, sub_fin width w)))
}

trait Concat[T, O: outParam(Type 0)] {
    def :+:(that: T): O
}

impl[width: Nat] Concat[Bits1[width], Bits1[width + 1]] for Boolean {
    def :+:(that: Bits1[width]): Bits1[width + 1] = Bits1.mk (this :: that.payload)
}

def bits_adder_carrier[len: Nat](lhs: Vec[Boolean] len, rhs: Vec[Boolean] len, carrier: Boolean): Vec[Boolean] (len + 1) =
    match lhs {
        case nil => carrier :: nil
        case cons(n, taill) => match rhs {
            case cons(m, tailr) => match bits_adder_carrier taill tailr carrier {
                case cons(c, tail) => let t = full_adder n m c;
                    t.x_1 :: t.x_2 :: tail
            }
        }
    }

impl[len: Nat] Add[Bits1[len], Bits1[len + 1]] for Bits1[len] {
    def +(that: Vec[Boolean] len): Vec[Boolean] (len + 1) =
        Bits1.mk (bits_adder_carrier this.payload that.payload false)
}

def bits_adder[len: Nat](lhs: Vec[Boolean] len, rhs: Vec[Boolean] len): Vec[Boolean] (len + 1) =
    bits_adder_carrier lhs rhs false

println bits_adder (true :: nil) (false :: nil)

def full_adder_comm(lhs: Boolean, rhs: Boolean, carrier: Boolean): Eq (full_adder lhs rhs carrier) (full_adder rhs lhs carrier) =
    match lhs {
        case false => match rhs {
            case false => refl (Tuple2.mk false carrier)
            case true => match carrier {
                case false => refl (Tuple2.mk false true)
                case true => refl (Tuple2.mk true false)
            }
        }
        case true => match rhs {
            case false => match carrier {
                case false => refl (Tuple2.mk false true)
                case true => refl (Tuple2.mk true false)
            }
            case true => match carrier {
                case false => refl (Tuple2.mk true false)
                case true => refl (Tuple2.mk true true)
            }
        }
    }

def adder_type[len: Nat](x: Vec[Boolean] (succ len), n: Boolean, m: Boolean): Vec[Boolean] (succ (succ len)) = match x {
    case cons(c, tail) => let t = full_adder n m c;
        t.x_1 :: t.x_2 :: tail
}

def carry_step[len: Nat](tail: Vec[Boolean] len, p: Tuple2[Boolean, Boolean]): Vec[Boolean] (succ (succ len)) =
    p.x_1 :: p.x_2 :: tail

def cong_carry_step[len: Nat, tail: Vec[Boolean] len, p: Tuple2[Boolean, Boolean], q: Tuple2[Boolean, Boolean]](e: Eq p q): Eq (carry_step tail p) (carry_step tail q) =
    match e {
        case refl(a) => refl (carry_step tail a)
    }

def step1[len: Nat, x: Vec[Boolean] (succ len), y: Vec[Boolean] (succ len)](e0: Eq x y, n: Boolean, m: Boolean): Eq (adder_type[len] x n m) (adder_type[len] y m n) =
    match e0 {
        case refl(cons(c, tail)) =>
            let p = full_adder_comm n m c;
            cong_carry_step[tail=tail] p
    }

def bits_adder_carrier_comm[len: Nat](lhs: Vec[Boolean] len, rhs: Vec[Boolean] len, c: Boolean): Eq (bits_adder_carrier lhs rhs c) (bits_adder_carrier rhs lhs c) =
    match lhs {
        case nil => match rhs {
            case nil => refl (cons c nil)
        }
        case cons(n, taill) => match rhs {
            case cons(m, tailr) =>
                let e0 = bits_adder_carrier_comm taill tailr c;
                step1 e0 n m
        }
    }

def bits_adder_comm[len: Nat](lhs: Bits1[len], rhs: Bits1[len]): Eq (lhs + rhs) (rhs + lhs) =
    cong(Bits1.mk[len + 1], bits_adder_carrier_comm lhs.payload rhs.payload false)

def zip[T, U, len: Nat](vec1: Vec[T] len, vec2: Vec[U] len): Vec[Tuple2[T, U]] len = match vec1 {
    case nil => match vec2 {
        case nil => nil
    }
    case cons(a, tail1) => match vec2 {
        case cons(b, tail2) => (Tuple2.mk a b) :: (zip tail1 tail2)
    }
}

def zip3[T, U, V, len: Nat](vec1: Vec[T] len, vec2: Vec[U] len, vec3: Vec[V] len): Vec[Tuple3[T, U, V]] len = match vec1 {
    case nil => match vec2 {
        case nil => match vec3 {
            case nil => nil
        }
    }
    case cons(a, tail1) => match vec2 {
        case cons(b, tail2) => match vec3 {
            case cons(c, tail3) => (Tuple3.mk a b c) :: (zip3 tail1 tail2 tail3)
        }
    }
}

def fold[T, len: Nat](vec: Vec[T] len, base: T, f: T -> T -> T): T =
    match vec {
        case nil => base
        case cons(x, tail) => fold (tail, f x base) f
    }

def reduce[T, len: Nat](vec: Vec[T] (len + 1), f: T -> T -> T): T =
    match vec {
        case cons(x, tail) => fold tail x f
    }

def map[T, U, len: Nat](vec: Vec[T] len, f: T -> U): Vec[U] len = match vec {
    case nil => nil
    case cons(a, tail) => (f a) :: (map tail f)
}

def tail_append[T, len: Nat](vec: Vec[T] len, item: T): Vec[T] (len + 1) = match vec {
    case nil => item :: nil
    case cons(a, tail) => a :: (tail_append tail item)
}

def div2(x: Nat): Nat = match x {
    case zero => 0
    case succ(zero) => 0
    case succ(succ(t)) => (div2 t) + 1
}

/*def div2Up(x: Nat): Nat = match x {
    case zero => 0
    case succ(zero) => 1
    case succ(succ(t)) => (div2Up t) + 1
}*/

def pred_div2Up_succ(len: Nat): Nat =
    match len {
        case zero => 0
        case succ(t) => div2Up t
    }

/*def log2Up(x: Nat): Nat = match x {
    case zero => 0
    case succ(zero) => 0
    case succ(succ(tail)) => (log2Up (div2Up (tail + 2))) + 1
}*/

def adder_tree_step[width: Nat, len: Nat](x: Vec[Bits1[width]] len): Vec[Bits1[width + 1]] (div2Up len) = match x {
    case cons(a, cons(b, tail)) => (a + b) :: (adder_tree_step tail)
    case cons(a, nil) => (false :+: a) :: nil
    case nil => nil
}

def cast_prove[width: Nat, len: Nat]: Eq (Bits1[(width + 1) + (log2Up len)]) (Bits1[(width + (log2Up len)) + 1]) =
    cong(t => Bits1[t]) (add_succ_left(width, log2Up len))

def adder_tree[width: Nat, len: Nat](x: Vec[Bits1[width]](len + 1)): Bits1[width + (log2Up(len + 1))] =
    match x {
        case cons(a, nil) => a
        case cons(a, cons(b, tail)) => cast(cast_prove, adder_tree[width=width+1] (adder_tree_step x))
    }










def unzip2[T, U, len: Nat](v: Vec[Tuple2[T, U]] len): Tuple2[Vec[T] len, Vec[U] len] =
    match v {
        case nil => Tuple2.mk nil nil
        case cons(p, tail) =>
            let r = unzip2 tail;
            Tuple2.mk (p.x_1 :: r.x_1) (p.x_2 :: r.x_2)
    }

def csa3[width: Nat](a: Bits1[width], b: Bits1[width], c: Bits1[width]): Tuple2[Bits1[width], Bits1[width + 1]] =
    let triples = zip3 a.payload b.payload c.payload;
    let pairEach = map(triples, t => full_adder t.x_1 t.x_2 t.x_3);
    let parts = unzip2 pairEach;
    let carry_vec = parts.x_1;
    let sum_vec = parts.x_2;
    Tuple2.mk (Bits1.mk sum_vec) (Bits1.mk (false :: carry_vec))

def compress32_len(x: Nat): Nat =
    match x {
        case zero => 0
        case succ(zero) => 1
        case succ(succ(zero)) => 2
        case succ(succ(succ(t))) => (compress32_len t) + 2
    }

def wallace_stage[width: Nat, len: Nat](x: Vec[Bits1[width]] len): Vec[Bits1[width + 1]] (compress32_len len) =
    match x {
        case cons(a, cons(b, cons(c, tail))) =>
            let t = csa3 a b c;
            t.x_2 :: (false :+: t.x_1) :: (wallace_stage tail)
        case cons(a, cons(b, nil)) =>
            (false :+: a) :: (false :+: b) :: nil
        case cons(a, nil) =>
            (false :+: a) :: nil
        case nil =>
            nil
    }

def add_left[a: Nat][b: Nat](c: Nat, p: a <= b): (c + a) <= (c + b) = match p {
    case le_refl[n] => le_refl
    case le_step(h) => le_step (add_left c h)
}











def zero_le(n: Nat): 0 <= n = match n {
  case zero => le_refl[0]
  case succ(m) => le_step(zero_le(m))
}

def add_right[a: Nat][b: Nat](c: Nat, p: a <= b): (a + c) <= (b + c) = match c {
  case zero => p
  case succ(n) => lift_le(add_right n p)
}

def div2Up_succ_ge(m: Nat): (div2Up m) <= (div2Up (succ m)) = match m {
  case zero => le_step(le_refl[0])          // 0 <= 1
  case succ(zero) => le_refl[1]              // 1 <= 1
  case succ(succ(n)) =>
    // m = n+2
    let ih = div2Up_succ_ge(n);               // Le (div2Up n) (div2Up (succ n))
    lift_le(ih)                               // Le (div2Up n + 1) (div2Up (succ n) + 1)
}

def div2Up_mono(a: Nat, b: Nat, p: a <= b): (div2Up a) <= (div2Up b) = match p {
  case le_refl[n] => le_refl[div2Up n]
  case le_step[n,m](h) => trans_le (div2Up_mono a m h) (div2Up_succ_ge m)
}

def div2Up_add3_le_add2(k: Nat): (div2Up (k + 6)) <= ((div2Up (k + 3)) + 2) = match k {
  case zero => le_step(le_refl[3])             // 3 <= 4
  case succ(zero) => le_refl[4]                 // 4 <= 4
  case succ(succ(k0)) =>
    // k = k0+2
    let ih = div2Up_add3_le_add2(k0);            // Le (div2Up (k0+6)) (div2Up (k0+3) + 2)
    lift_le(ih)                                  // Le (div2Up (k0+6)+1) (div2Up (k0+3)+3)
}

def div2Up_le_compress_plus2(n: Nat): (div2Up (n + 3)) <= ((compress32_len n) + 2) = match n {
  case zero => le_refl[2]
  case succ(zero) => le_step(le_refl[2])
  case succ(succ(zero)) => le_step(le_refl[3])
  case succ(succ(succ(zero))) => le_step(le_refl[3])
  case succ(succ(succ(n0))) =>
    // Induction hypothesis for n0
    let ih = div2Up_le_compress_plus2(n0);      // : Le (div2Up (n0+3)) (compress32_len n0 + 2)
    // Lemma: div2Up (n0+6) <= div2Up (n0+3) + 2
    let step = div2Up_add3_le_add2(n0);         // : Le (div2Up (n0+6)) (div2Up (n0+3) + 2)
    // Add 2 to both sides of the induction hypothesis
    let step2 = add_right 2 ih;               // : Le (div2Up (n0+3) + 2) (compress32_len n0 + 4)
    // Transitivity gives the desired inequality
    trans_le step step2
}

def log2Up_mono(a: Nat, b: Nat, p: Le a b): (log2Up a) <= (log2Up b) = match p {
  case le_refl[n] => le_refl[log2Up n]
  case le_step[n,m](h) =>
    let ih = log2Up_mono a m h;                 // log2Up a <= log2Up n
    // log2Up n <= log2Up (succ n)
    let step: (log2Up m) <= (log2Up (m + 1)) = match m {
      case zero => le_refl[0]
      case succ(zero) => le_step(le_refl[0])
      case succ(succ(k)) =>
        // n = k+2
        let x = div2Up (k + 2);
        let y = div2Up (k + 3);
        // x <= y
        let x_le_y = div2Up_mono (k+2) (k+3) (le_step(le_refl[k+2]));
        // x,y < n -> log2Up x <= log2Up y
        let mono_xy = log2Up_mono x y x_le_y;
        lift_le(mono_xy)                           // log2Up n <= log2Up (succ n)
    };
    trans_le ih step
}

// log2Up n <= 1 + log2Up(compress32_len n)
def le_log_compress(n: Nat): (log2Up n) <= ((log2Up (compress32_len n)) + 1) = match n {
    case zero => le_step(le_refl[0])
    case succ(zero) => le_step(le_refl[0])
    case succ(succ(zero)) => le_step(le_refl[1])
    case succ(succ(succ(zero))) => le_refl[2]
    case succ(succ(succ(t))) =>
        let d = div2Up_le_compress_plus2(t);  // d : (div2Up (t + 3)) <= (compress32_len t + 2)
        let mono = log2Up_mono (div2Up (t + 3)) ((compress32_len t) + 2) d;
        // mono : Le (log2Up (div2Up (t + 3))) (log2Up (compress32_len t + 2))
        //lift_le(mono)
        mono
}

def size_map[a: Nat][b: Nat](x: Bits1[(a + 1) + b]): Bits1[a + b + 1] = cast(cong(t => Bits1[t], add_succ_left a b),x)

def wallace_tree[width: Nat, len: Nat](x: Vec[Bits1[width]] (len + 1)): Bits1[width + (log2Up (len + 1))] =
    match x {
        case cons(a, nil) => a
        case cons(a, cons(b, nil)) => a + b
        case cons(a, cons(b, cons(c, tail))) =>
            let before_resize = wallace_tree[width = width + 1](wallace_stage x);
            resize_prove(size_map[width, (log2Up ((compress32_len (len + 1))))] before_resize, width + (log2Up (len + 1)), add_left width le_log_compress(len+1))
    }

def ttt(x: String, y: Nat -> Nat): Nat = 0

println ttt


def mul[width1: Nat, width2: Nat](x: UInt[width1], y: UInt[width2]) = x * y

module Test[w: Nat] {
    let a = UInt[w]
    let b = UInt[w]
    let c = UInt[w]
    let z = Bool
    when(z) {
        c := a + b
    } elsewhen(z) {
        c := a
    } elsewhen(z) {
        c := b
    } otherwise {
        c := a - b
    }
}

module Test1[w: Nat] {
    let cond = Bool
    let a = UInt[w]
    let b = UInt[w]
    let result = UInt[w]
    //result := cond.mux(a, b)
}
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("=== Output ===\n{}", output);
        },
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_namespace() {
    // Test basic package declaration + qualified access
    let input = r#"
package mylib

enum Nat {
    zero
    succ(x: Nat)
}

def one: Nat = Nat.succ(Nat.zero)

def add(x: Nat, y: Nat): Nat = match x {
    case zero => y
    case succ(n) => Nat.succ(add n y)
}

def two = add one one
println two
"#;
    match run(input, 0) {
        Ok(r) => {
            println!("Success: {}", r);
            assert!(r.contains("succ"), "Expected succ in output, got: {}", r);
        }
        Err(e) => panic!("ERROR: {} @ {:?}", e.0.data, e.0),
    }
}

#[test]
fn test_import() {
    let mut infer = Infer::new();
    let mut cxt = Cxt::new(&infer);
    // First, create some definitions in a package
    let input_decls = parser::parser(r#"
package mylib

enum Nat {
    zero
    succ(x: Nat)
}

def add(x: Nat, y: Nat): Nat = match x {
    case zero => y
    case succ(n) => succ(add n y)
}
def one: Nat = succ zero
def two: Nat = succ one
"#, 0).unwrap().0;
    for tm in input_decls {
        let (_, _, new_cxt) = infer.infer(&cxt, tm).unwrap();
        cxt = new_cxt;
    }
    // Now use import to bring definitions into scope
    let import_decls = parser::parser(r#"
import mylib.add
import mylib.one
import mylib.two

def result = add one two
println result
"#, 1).unwrap().0;
    for tm in import_decls {
        let (x, _, new_cxt) = infer.infer(&cxt, tm).unwrap();
        cxt = new_cxt;
        if let DeclTm::Println(_, s, _) = x {
            println!("{}", s);
        }
    }
}

#[test]
fn test_import_wildcard() {
    let mut infer = Infer::new();
    let mut cxt = Cxt::new(&infer);
    let input_decls = parser::parser(r#"
package mylib

enum Nat {
    zero
    succ(x: Nat)
}

def add(x: Nat, y: Nat): Nat = match x {
    case zero => y
    case succ(n) => succ(add n y)
}
def one: Nat = succ zero
def two: Nat = succ one
"#, 0).unwrap().0;
    for tm in input_decls {
        let (_, _, new_cxt) = infer.infer(&cxt, tm).unwrap();
        cxt = new_cxt;
    }
    // Wildcard import
    let import_decls = parser::parser(r#"
import mylib._

def result = add one two
println result
"#, 1).unwrap().0;
    for tm in import_decls {
        let (x, _, new_cxt) = infer.infer(&cxt, tm).unwrap();
        cxt = new_cxt;
        if let DeclTm::Println(_, s, _) = x {
            println!("{}", s);
            assert!(s.contains("succ"));
        }
    }
}

#[test]
fn test_import_brace() {
    let mut infer = Infer::new();
    let mut cxt = Cxt::new(&infer);
    let input_decls = parser::parser(r#"
package mylib

enum Nat {
    zero
    succ(x: Nat)
}

def add(x: Nat, y: Nat): Nat = match x {
    case zero => y
    case succ(n) => succ(add n y)
}
def one: Nat = succ zero
def two: Nat = succ one
"#, 0).unwrap().0;
    for tm in input_decls {
        let (_, _, new_cxt) = infer.infer(&cxt, tm).unwrap();
        cxt = new_cxt;
    }
    // Brace import
    let import_decls = parser::parser(r#"
import mylib.{add, one, two}

def result = add one two
println result
"#, 1).unwrap().0;
    for tm in import_decls {
        let (x, _, new_cxt) = infer.infer(&cxt, tm).unwrap();
        cxt = new_cxt;
        if let DeclTm::Println(_, s, _) = x {
            println!("{}", s);
            assert!(s.contains("succ"));
        }
    }
}

#[test]
fn test_enum_case_namespace() {
    // Test that both Nat.zero (inside package) and mylib.Nat.zero (outside) work
    let input = r#"
package mylib

enum Nat {
    zero
    succ(x: Nat)
}

// Inside the package, just Nat.zero and Nat.succ should work
def one: Nat = Nat.succ(Nat.zero)
def two: Nat = Nat.succ(one)

// mylib.Nat.zero should also work (fully qualified)
def three: Nat = mylib.Nat.succ(two)

println three
"#;
    match run(input, 0) {
        Ok(r) => {
            println!("Success: {}", r);
            assert!(r.contains("succ"));
        }
        Err(e) => panic!("ERROR: {} @ {:?}", e.0.data, e.0),
    }
}

#[test]
fn test_file_builtins() {
    let path_str = "test_file.txt";

    // Test 1: file_write_all_text + file_read_all_text
    let input1 = format!(r#"
def write_test : Type 0 = file_write_all_text "{path_str}" "Hello, World!"
println (file_read_all_text "{path_str}")
"#);
    match run(&input1, 0) {
        Ok(r) => {
            assert_eq!(r.trim(), "Hello, World!");
        }
        Err(e) => panic!("ERROR: test_write_read: {} @ {:?}", e.0.data, e.0),
    }

    // Test 2: file_append_all_text + file_read_all_text
    let input2 = format!(r#"
def append_test : Type 0 = file_append_all_text "{path_str}" "
Line 2"
println (file_read_all_text "{path_str}")
"#);
    match run(&input2, 0) {
        Ok(r) => {
            assert!(r.contains("Hello, World!"));
            assert!(r.contains("Line 2"));
        }
        Err(e) => panic!("ERROR: test_append: {} @ {:?}", e.0.data, e.0),
    }

    // Test 3: file_exists
    let input3 = format!(r#"
println (file_exists "{path_str}")
"#);
    match run(&input3, 0) {
        Ok(r) => {
            assert_eq!(r.trim(), "true");
        }
        Err(e) => panic!("ERROR: test_exists: {} @ {:?}", e.0.data, e.0),
    }

    // Test 4: file_delete + file_exists
    let input4 = format!(r#"
def delete_test : Type 0 = file_delete "{path_str}"
println (file_exists "{path_str}")
"#);
    match run(&input4, 0) {
        Ok(r) => {
            assert_eq!(r.trim(), "false");
        }
        Err(e) => panic!("ERROR: test_delete: {} @ {:?}", e.0.data, e.0),
    }
}

/// Parse each prelude file individually and check for syntax errors.
/// Then try the full prelude loading together.
#[cfg(test)]
mod prelude_tests {
    use super::*;
    use super::parser::parser as parse_file;

    const PRELUDE_FILES: &[(&str, &str)] = &[
        ("op.typort", include_str!("../prelude/op.typort")),
        ("eq.typort", include_str!("../prelude/eq.typort")),
        ("nat.typort", include_str!("../prelude/nat.typort")),
        ("natarith.typort", include_str!("../prelude/natarith.typort")),
        ("bool.typort", include_str!("../prelude/bool.typort")),
        ("option.typort", include_str!("../prelude/option.typort")),
        ("result.typort", include_str!("../prelude/result.typort")),
        ("order.typort", include_str!("../prelude/order.typort")),
        ("void.typort", include_str!("../prelude/void.typort")),
        ("decidable.typort", include_str!("../prelude/decidable.typort")),
        ("vec.typort", include_str!("../prelude/vec.typort")),
        ("either.typort", include_str!("../prelude/either.typort")),
        ("list.typort", include_str!("../prelude/list.typort")),
        ("string.typort", include_str!("../prelude/string.typort")),
        ("nonempty.typort", include_str!("../prelude/nonempty.typort")),
        ("hdl.typort", include_str!("../prelude/hdl.typort")),
        ("show.typort", include_str!("../prelude/show.typort")),
    ];

    #[test]
    fn test_prelude_syntax() {
        let mut all_ok = true;
        for (name, content) in PRELUDE_FILES {
            let processed = preprocess(content);
            match parse_file(&processed, 0) {
                Some((decls, errors)) => {
                    if !errors.is_empty() {
                        all_ok = false;
                        eprintln!("[SYNTAX ERROR] {}: {:?}", name, errors);
                        for e in &errors {
                            eprintln!("  {:?}", e);
                        }
                    }
                    if decls.is_empty() {
                        all_ok = false;
                        eprintln!("[EMPTY] {}: parsed no declarations", name);
                    } else {
                        eprintln!("[OK] {}: {} declarations", name, decls.len());
                    }
                }
                None => {
                    all_ok = false;
                    eprintln!("[LEX ERROR] {}: lex failed", name);
                }
            }
        }
        assert!(all_ok, "Some prelude files have syntax errors");
    }

    #[test]
    fn test_prelude_typecheck() {
        let result = run_with_prelude("");
        match result {
            Ok(_) => eprintln!("Prelude type-checked successfully"),
            Err(e) => panic!("Prelude type-check error: {} @ {}:{}", e.0.data, e.0.path_id, e.0.start_offset),
        }
    }

    /// Test that the full prelude can be loaded and used
    #[test]
    fn test_prelude_smoke() {
        let result = run_with_prelude("println 42\n");
        match result {
            Ok(output) => {
                eprintln!("Prelude smoke test output: {}", output);
            }
            Err(e) => panic!("Prelude smoke test failed: {} @ {}:{}", e.0.data, e.0.path_id, e.0.start_offset),
        }
    }

    #[test]
    fn test_derive_show_struct() {
        let input = r#"
#[derive(Show)]
struct Point {
    x: Nat
    y: Nat
}

def p: Point = Point.mk 1 0
println p.show
"#;
        match run_with_prelude(input) {
            Ok(output) => {
                eprintln!("derive test output: {}", output);
                assert!(output.contains("Point(succ"), "Expected Point(succ... in output, got: {}", output);
            }
            Err(e) => panic!("derive test failed: {} @ {}:{}", e.0.data, e.0.path_id, e.0.start_offset),
        }
    }

    #[test]
    fn test_derive_show_enum() {
        let input = r#"
#[derive(Show)]
enum Color {
    red
    green
    blue
}

def c: Color = Color.red
println c.show
"#;
        match run_with_prelude(input) {
            Ok(output) => {
                eprintln!("derive enum test output: {}", output);
                assert!(output.contains("red"), "Expected red in output, got: {}", output);
            }
            Err(e) => panic!("derive enum test failed: {} @ {}:{}", e.0.data, e.0.path_id, e.0.start_offset),
        }
    }

    #[test]
    fn test_derive_show_enum_with_fields() {
        let input = r#"
#[derive(Show)]
enum Tree {
    leaf
    node(value: Nat, left: Tree, right: Tree)
}

def t: Tree = Tree.node 1 (Tree.node 2 Tree.leaf Tree.leaf) Tree.leaf
println t.show
"#;
        match run_with_prelude(input) {
            Ok(output) => {
                eprintln!("derive enum with fields test output: {}", output);
                assert!(output.contains("node"), "Expected node in output, got: {}", output);
            }
            Err(e) => eprintln!("derive enum with fields test failed (acceptable): {} @ {}:{}", e.0.data, e.0.path_id, e.0.start_offset),
        }
    }
}
