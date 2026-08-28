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

type Rc<T> = std::sync::Arc<T>;

type Decl = HashMap<SmolStr, (Span<()>, Rc<Tm>, Rc<Val>, Rc<Ty>, Rc<VTy>)>;

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct MetaVar(u32);

#[derive(Debug, Clone)]
enum MetaEntry {
    Solved(Rc<Val>, Rc<VTy>),
    Unsolved(Rc<VTy>, std::sync::Arc<Cxt>, Rc<VTy>),
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
    Sum(Span<SmolStr>, Vec<(Span<SmolStr>, Rc<Tm>, Rc<Ty>, Icit)>, Vec<Span<SmolStr>>, bool),
    SumCase {
        typ: Rc<Tm>,
        case_name: Span<SmolStr>,
        datas: Vec<(Span<SmolStr>, Rc<Tm>, Icit)>,
        is_trait: bool,
    },
    Match(Rc<Tm>, Vec<(PatternDetail, Rc<Tm>)>),
    /// Call(name, display_args, val_args, body) - body was inlined from function `name`
    Call(SmolStr, Vec<Rc<Tm>>, Vec<Rc<Val>>, Rc<Tm>),
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
                MetaEntry::Unsolved(_, cxt, oty) => Some((cxt.as_ref().clone(), oty.clone())),
                MetaEntry::Solved(v, _) => {
                    infer.quote(decl, l, v).no_metas(infer, decl, l)
                }
            },
            Tm::Sum(_, items, _, _) => items.iter().flat_map(|(_, t, ty, _)| t.no_metas(infer, decl, l).or_else(|| ty.no_metas(infer, decl, l))).next(),
            Tm::SumCase { typ, case_name: _, datas, is_trait: _ } => typ.no_metas(infer, decl, l)
                .or_else(|| datas.iter().flat_map(|(_, t, _)| t.no_metas(infer, decl, l)).next()),
            Tm::Match(tm, items) => tm.no_metas(infer, decl, l).or_else(|| items.iter().flat_map(|(_, t)| t.no_metas(infer, decl, l)).next()),
            Tm::Call(_, args, _, body) => args.iter().flat_map(|a| a.no_metas(infer, decl, l)).next().or_else(|| body.no_metas(infer, decl, l)),
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
        Vec<(Span<SmolStr>, Rc<Val>, Rc<VTy>, Icit)>,
        Vec<Span<SmolStr>>,
        bool,
    ),
    SumCase {
        is_trait: bool,
        typ: Rc<Val>,
        case_name: Span<SmolStr>,
        datas: Vec<(Span<SmolStr>, Rc<Val>, Icit)>,
    },
    Match(Rc<Val>, Env, Vec<(PatternDetail, Rc<Tm>)>, Option<(SmolStr, Vec<Rc<Val>>)>),
    /// Call(name, args, body) - value inlined from function `name`
    Call(SmolStr, Vec<Rc<Tm>>, Rc<Val>),
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

fn lookup_function_by_cases(decl: &Decl, cases: &[(PatternDetail, Rc<Tm>)]) -> Option<SmolStr> {
    for (name, (_, body_tm, _, _, _)) in decl {
        if match_has_same_patterns(cases, body_tm) {
            return Some(name.clone());
        }
    }
    None
}

fn match_has_same_patterns(cases: &[(PatternDetail, Rc<Tm>)], tm: &Tm) -> bool {
    match tm {
        Tm::Match(_, inner_cases) => {
            cases.len() == inner_cases.len()
                && cases.iter().zip(inner_cases.iter()).all(|((p1, _), (p2, _))| p1 == p2)
        }
        Tm::Lam(_, _, inner) => match_has_same_patterns(cases, inner),
        _ => false,
    }
}

fn extract_decl_name(tm: &Tm) -> Option<Span<SmolStr>> {
    match tm {
        Tm::Decl(name) => Some(name.clone()),
        Tm::App(t, _, _) => extract_decl_name(t),
        _ => None,
    }
}

fn collect_app_args(tm: &Tm) -> Vec<Rc<Tm>> {
    match tm {
        Tm::App(t, u, _) => {
            let mut args = collect_app_args(t);
            args.push(u.clone());
            args
        }
        _ => vec![],
    }
}

use std::ops::{Add, Sub};
use std::collections::HashMap;

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
    pub Vec<Box<dyn Fn() -> Option<String>>>
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
        self.meta.push(MetaEntry::Unsolved(a, std::sync::Arc::new(cxt), origin_typ));
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
            Val::Call(_, _, body) => self.v_app(decl, body, u, i),
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
            Tm::Decl(x) => decl.get(&x.data).map(|x| x.2.clone()).unwrap_or(Val::Decl(x.clone(), List::new()).into()),//TODO:directly unwrap?
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
                let new_params = params
                    .iter()
                    .map(|x| (x.0.clone(), self.eval(decl, env, &x.1), self.eval(decl, env, &x.2), x.3))
                    .collect();
                Val::Sum(name.clone(), new_params, cases.clone(), *is_trait).into()
            }
            Tm::SumCase {
                is_trait,
                typ,
                case_name,
                datas,
            } => {
                let datas = datas
                    .iter()
                    .map(|p| (p.0.clone(), self.eval(decl, env, &p.1), p.2))
                    .collect();
                let typ = self.eval(decl, env, typ);
                Val::SumCase {
                    is_trait: *is_trait,
                    typ,
                    case_name: case_name.clone(),
                    datas,
                }.into()
            }
            Tm::Call(name, _, val_args, body) => {
                let result = self.eval(decl, env, body);
                if let Val::Match(scrut, env, cases, _) = result.as_ref() {
                    Val::Match(scrut.clone(), env.clone(), cases.clone(), Some((name.clone(), val_args.clone()))).into()
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
                            None => Val::Match(val, env.clone(), cases.clone(), None).into(),
                        }
                    }
                    _ => {
                        Val::Match(val, env.clone(), cases.clone(), None).into()
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
                let new_params = params.iter()
                    .map(|x| {
                        (x.0.clone(), self.quote(decl, l, &x.1), self.quote(decl, l, &x.2), x.3)
                    })
                    .collect();
                Tm::Sum(name.clone(), new_params, cases.clone(), *is_trait).into()
            }
            Val::SumCase {
                is_trait,
                typ,
                case_name,
                datas,
            } => {
                let datas = datas
                    .iter()
                    .map(|p| {
                        (p.0.clone(), self.quote(decl, l, &p.1), p.2)
                    })
                    .collect();
                Tm::SumCase {
                    is_trait: *is_trait,
                    typ: self.quote(decl, l, typ),
                    case_name: case_name.clone(),
                    datas,
                }.into()
            }
            Val::Call(name, args, body) => {
                let quoted_body = self.quote(decl, l, body);
                Tm::Call(name.clone(), args.clone(), vec![], quoted_body).into()
            },
            Val::Match(val, env, cases, origin) => {
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
                let quoted_match = Tm::Match(self.quote(decl, l, val), tm_cases).into();
                let effective_origin = match origin {
                    Some((n, a)) => Some((n.clone(), a.clone())),
                    None => lookup_function_by_cases(decl, cases).map(|name| (name, vec![val.clone()])),
                };
                if let Some((name, arg_vals)) = effective_origin {
                    let display_args: Vec<Rc<Tm>> = arg_vals.iter()
                        .map(|v| self.quote(decl, l, v))
                        .collect();
                    Tm::Call(name.clone(), display_args, arg_vals.clone(), quoted_match).into()
                } else {
                    quoted_match
                }
            }
        }
    }

    pub fn nf(&self, decl: &Decl, env: &Env, t: &Rc<Tm>) -> Rc<Tm> {
        let l = Lvl(env.iter().count() as u32);
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
        include_str!("../prelude/core/op.typort"),
        include_str!("../prelude/core/eq.typort"),
        include_str!("../prelude/core/nat.typort"),
        include_str!("../prelude/core/bool.typort"),
        include_str!("../prelude/data/option.typort"),
        include_str!("../prelude/data/result.typort"),
        include_str!("../prelude/data/order.typort"),
        include_str!("../prelude/core/void.typort"),
        include_str!("../prelude/data/decidable.typort"),
        include_str!("../prelude/data/vec.typort"),
        include_str!("../prelude/data/either.typort"),
        include_str!("../prelude/data/list.typort"),
        include_str!("../prelude/data/string.typort"),
        include_str!("../prelude/data/nonempty.typort"),
        include_str!("../prelude/hdl/hdl-core.typort"),
        include_str!("../prelude/hdl/hdl-types.typort"),
        include_str!("../prelude/hdl/hdl-ops.typort"),
        include_str!("../prelude/hdl/hdl-clock.typort"),
        include_str!("../prelude/hdl/hdl-bus.typort"),
        include_str!("../prelude/hdl/hdl-signals.typort"),
        include_str!("../prelude/hdl/hdl-macros.typort"),
        include_str!("../prelude/hdl/hdl-verilog.typort"),
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
fn test_trait() {
    let input = r#"
def outParam[A](a: A): A = a

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

trait Say {
    def say(x: Nat): String
}

impl[T] Say for T {
    def say(x: Nat): String = "hello"
}

println (zero.say zero)

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

def mul(x: Nat, y: Nat) = match x {
    case zero => zero
    case succ(n) => y + (mul n y)
}

def four = two + two

println four

struct Point[T] {
    x: T
    y: T
}

def get_x[T](p: Point[T]): T = p.x

impl Add[Point[Nat], Point[Nat]] for Point[Nat] {
    def +(that: Point[Nat]): Point[Nat] =
        new Point(this.x + that.x, this.y + that.y)
}

impl Add[Nat, Point[Nat]] for Point[Nat] {
    def +(that: Nat): Point[Nat] =
        new Point(this.x + that, this.y + that)
}

def start_point = new Point(zero, four)

def end_point = new Point(four, two)

println (get_x start_point)

println (start_point + end_point)

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
    let result = run(input, 0).unwrap();
    println!("{}", result);
    assert!(result.contains("hello"));
    assert!(result.contains("Bool::false"));
    assert!(result.contains("true"));
    assert!(result.contains("4"));
    assert!(result.contains("0"));
    assert!(result.contains("Point[Nat]::Point.mk(4, 6)"));
}

#[test]
fn test5() {
    let input = r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

def t[len: Nat](x: Vec[Nat] len, y: Vec[Nat] len): Vec[Nat] (succ len) =
    match x {
        case nil => cons zero nil
        case cons(x, xs) => match y {
            case cons(y, ys) => cons(x, t xs ys)
        }
    }

impl[T, len: Nat] Vec[T](len) {
    def map[U](f: T -> U): Vec[U] len =
        match this {
            case nil => nil
            case cons(x, xs) => cons(f x, xs.map f)
        }
}

def tt = cons(zero, cons(zero, nil)).map[U=Nat](x => match x {
    case succ(z) => succ(zero)
    case zero => zero
})

def z[len: Nat](x: Vec[Nat]len) = match x {
    case nil => 1
    case cons[l=lll](x, xs) => lll
}

"#;
    println!("{}", run(input, 0).unwrap());
}

#[test]
fn test6() {
    let input = r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

def t[len: Nat](x: Vec[Nat] len, y: Vec[Nat] len): Vec[Nat] (succ len) =
    match x {
        case nil => cons zero nil
        case cons(x, xs) => match y {
            case cons(y, ys) => match t xs ys {
                case cons(z, zs) => cons(zero, cons zero zs)
            }
        }
    }

def ttt =
    let useless1 = create_global "Nat" 2;
    let useless2 = change_mutable("Nat", z => succ(z));
    get_global "Nat"

println ttt

println stringify t123

macro_rules module {
    ($name: ident $body: raw) => {def $name = string_concat(string_concat("module ", stringify $name), $body)};
    ($name: ident) => {def $name = string_concat("module ", stringify $name)};
}

module test1 " {}"

println test1

module test2

println test2

"#;
    println!("{}", run(input, 0).unwrap());
}

#[test]
fn test4() {
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

def rfl[A][a: A]: Eq a a =
    refl a

def cong[A, B, f: A -> B, x: A, y: A](e: Eq x y): Eq (f x) (f y) =
    match e {
        case refl(a) => refl (f a)
    }

def cong_succ[x: Nat, y: Nat](e: Eq x y): Eq (succ x) (succ y) =
    cong[Nat][Nat][succ][x][y] e

def add_zero_right(a: Nat): Eq (add a zero) a =
    match a {
        case zero => refl zero
        case succ(t) => cong_succ (add_zero_right t)
    }

def symm[A, x, y: A](e: Eq[A] x y): Eq[A] y x =
    match e {
        case refl(a) => refl[A] a
    }

def trans[A, x, y, z: A](e1: Eq[A] x y, e2: Eq[A] y z): Eq[A] x z =
    match e1 {
        case refl(a) => e2
    }

def add_succ_right (n: Nat, m: Nat): Eq (add (n, succ m)) (succ (add n m)) =
    match n {
        case zero => refl[Nat] (succ m)
        case succ(k) => cong_succ (add_succ_right k m)
    }

def add_comm (n: Nat, m: Nat): Eq (add n m) (add m n) =
    match n {
        case zero => symm (add_zero_right m)
        case succ(k) => trans (cong_succ (add_comm k m)) (symm (add_succ_right m k))
    }

def add_assoc (n: Nat, m: Nat, k: Nat): Eq (add (add n m) k) (add(n, add m k)) =
    match n {
        case zero => rfl
        case succ(l) => cong_succ (add_assoc l m k)
    }

def double(n: Nat): Nat = add n n

def double_pow(k: Nat, n: Nat): Nat =
    match k {
        case zero => n
        case succ(k) => double(double_pow k n)
    }

def double_add(a: Nat, b: Nat): Eq(double(add a b), add(double a, double b)) =
    let e1 = add_assoc(a, b, add a b);
    let e2 = cong[f=add a](add_comm (b, add a b));
    let e3 = symm (add_assoc (a, add a b, b));
    let e4 = symm (cong[f=x => add x b] (add_assoc a a b));
    let e5 = add_assoc (add a a) b b;
    trans(e1, trans(e2, trans(e3, trans e4 e5)))

def prove(k: Nat, a: Nat, b: Nat): Eq(double_pow(k, add a b), add (double_pow k a) (double_pow k b)) =
    match k {
        case zero => rfl
        case succ(kk) => let ih = prove kk a b;
            let ih1 = cong[f=double] ih;
            let ih2 = double_add(double_pow(kk, a), double_pow(kk, b));
            trans ih1 ih2
    }
"#;
    let result = run(input, 0).unwrap();
    println!("{}", result);
    println!("success");
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

def create2: List[Bool] = cons (true, cons false nil)

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
    case succ(n) => add (y, mul n y)
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
    let result = run(input, 0).unwrap();
    println!("{}", result);
    assert!(result.contains("Bool::false"));
    assert!(result.contains("4"));
    assert!(result.contains("0"));
    assert!(result.contains("Point[Nat]::Point.mk(4, 6)"));
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
    let result = run(input, 0).unwrap();
    println!("{}", result);
    println!("success");
}

#[test]
fn test0() {
    let input = r#"
enum Eq[A](x: A, y: A) {
    refl[a: A] -> Eq[A] a a
}

enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

enum Product[A, B] {
    product(a: A, b: B)
}

def half_adder(lhs: Bool, rhs: Bool): Product[Bool][Bool] =
    match lhs {
        case false => product false rhs
        case true => match rhs {
            case false => product false true
            case true => product true false
        }
    }

def full_adder(lhs: Bool, rhs: Bool, carrier: Bool): Product[Bool][Bool] =
    match lhs {
        case false => half_adder rhs carrier
        case true => match rhs {
            case false => half_adder true carrier
            case true => product true carrier
        }
    }

def bits_adder_carrier[len: Nat](lhs: Vec[Bool] len, rhs: Vec[Bool] len, carrier: Bool): Vec[Bool] (succ len) =
    match lhs {
        case nil => cons carrier nil
        case cons(n, taill) => match rhs {
            case cons(m, tailr) => match bits_adder_carrier taill tailr carrier {
                case cons(c, tail) => match full_adder n m c {
                    case product(a, b) => cons (a, cons b tail)
                }
            }
        }
    }

def bits_adder[len: Nat](lhs: Vec[Bool] len, rhs: Vec[Bool] len): Vec[Bool] (succ len) =
    bits_adder_carrier lhs rhs false

println bits_adder (cons true nil) (cons false nil)
"#;
    let result = run(input, 0).unwrap();
    println!("{}", result);
    assert!(result.contains("Vec[Bool]::cons(1, Bool::false, Vec[Bool]::cons(0, Bool::true, Vec[Bool]::nil)"));
}

#[test]
pub fn test_index() {
    let input = r#"
enum Eq[A](x: A, y: A) {
    refl[a: A] -> Eq[A] a a
}

enum Nat {
    zero
    succ(x: Nat)
}

def two = succ (succ zero)

def three = succ (succ (succ zero))

def test: Eq two two = refl

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

def t = cons (zero, cons(two, cons(three, cons two nil)))

println t.len

def head[T, L: Nat](x: Vec[T] (succ L)): T =
    match x {
        case cons(x, _) => x
    }

println (head (cons zero nil))

def length[T, l: Nat](x: (Vec[T] l)): Nat =
    match x {
        case nil => zero
        case cons(_, xs) => succ (xs.len)
    }

    "#;
    let result = run(input, 0).unwrap();
    println!("{}", result);
    assert!(result.contains("4"));
    assert!(result.contains("0"));
}

#[test]
fn test7() {
    let input = r#"
enum Eq[A](x: A, y: A) {
    refl[a: A] -> Eq[A] a a
}

enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

enum Product[A, B] {
    product(a: A, b: B)
}

def half_adder(lhs: Bool, rhs: Bool): Product[Bool][Bool] =
    match lhs {
        case false => product false rhs
        case true => match rhs {
            case false => product false true
            case true => product true false
        }
    }

def full_adder(lhs: Bool, rhs: Bool, carrier: Bool): Product[Bool][Bool] =
    match lhs {
        case false => half_adder rhs carrier
        case true => match rhs {
            case false => half_adder true carrier
            case true => product true carrier
        }
    }

def bits_adder_carrier[len: Nat](lhs: Vec[Bool] len, rhs: Vec[Bool] len, carrier: Bool): Vec[Bool] (succ len) =
    match lhs {
        case nil => cons carrier nil
        case cons[_](n, taill) => match rhs {
            case cons[_](m, tailr) => match bits_adder_carrier taill tailr carrier {
                case cons[_](c, tail) => match full_adder n m c {
                    case product(a, b) => cons(a, cons b tail)
                }
            }
        }
    }

def bits_adder[len: Nat](lhs: Vec[Bool] len, rhs: Vec[Bool] len): Vec[Bool] (succ len) =
    bits_adder_carrier lhs rhs false

println bits_adder (cons true nil) (cons false nil)"#;
    let result = run(input, 0).unwrap();
    println!("{}", result);
    assert!(result.contains("Vec[Bool]::cons(1, Bool::false, Vec[Bool]::cons(0, Bool::true, Vec[Bool]::nil)"));
}

#[test]
fn test8() {
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

def four = add two two

println four

def cong[A, B, f: A -> B, x: A, y: A](e: Eq x y): Eq (f x) (f y) =
    match e {
        case refl(a) => refl (f a)
    }

def cong_succ[x: Nat, y: Nat](e: Eq x y): Eq (succ x) (succ y) =
    cong[Nat][Nat][succ][x][y] e

def add_zero_right(a: Nat): Eq (add a zero) a =
    match a {
        case zero => refl zero
        case succ(t) => cong_succ (add_zero_right t)
    }

def symm[A, x, y: A](e: Eq[A] x y): Eq[A] y x =
    match e {
        case refl(a) => refl[A] a
    }

def trans[A, x, y, z: A](e1: Eq[A] x y, e2: Eq[A] y z): Eq[A] x z =
    match e1 {
        case refl(a) => e2
    }

def add_succ_right (n: Nat, m: Nat): Eq[Nat] (add(n, succ m)) (succ (add n m)) =
    match n {
        case zero => refl[Nat] (succ m)
        case succ(k) => cong_succ (add_succ_right k m)
    }

def add_comm (n: Nat, m: Nat): Eq[Nat] (add n m) (add m n) =
    match n {
        case zero => symm (add_zero_right m)
        case succ(k) => trans (cong_succ (add_comm k m)) (symm (add_succ_right m k))
    }

def add_assoc (n: Nat, m: Nat, k: Nat): Eq[Nat] (add (add n m) k) (add(n, add m k)) =
    match n {
        case zero => rfl
        case succ(l) => cong_succ (add_assoc l m k)
    }

def add_zero_left(m: Nat): Eq[Nat] (add zero m) m =
    rfl

def mul_zero_right(n: Nat): Eq[Nat] (mul n zero) zero =
    match n {
        case zero => rfl
        case succ(k) => trans (refl (add(zero, mul k zero))) (mul_zero_right k)
    }

def add_succ_zero_left(k: Nat): Eq[Nat] (add (succ zero) k) (succ k) =
    cong_succ (add_zero_left k)

def mul_one_right(n: Nat): Eq[Nat] (mul (n, succ zero)) n =
    match n {
        case zero => rfl[Nat][zero]
        case succ(k) =>
            let ih = mul_one_right k;
            let lemma: Eq[Nat] (add (succ zero) k) (succ k) = cong_succ (add_zero_left k);
            trans (cong[Nat][Nat][add (succ zero)][mul (k, succ zero)][k] ih) lemma
    }

struct Exists[A: Type 0, P: A -> Type 0] {
    witness: A
    proof: P witness
}

def exists_two: Exists[Nat][x => Eq x two] = Exists.mk[Nat][x => Eq x two] two rfl

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
    case1(x: A)
    case2(x: test1)
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

struct Bits {
    name: String
    size: Nat
}

def assign(a: Bits, b: Bits)(eq: Eq[Nat] a.size b.size): String = string_concat a.name b.name

def sigA = new Bits("A", four)

def sigB = new Bits("B", four)

def sigC = new Bits("C", two)

def sigD = new Bits("D", two)

def ab = assign sigA sigB rfl

def cd = assign sigC sigD rfl

def three = add(two, succ zero)

println 5
"#;
    let result = run(input, 0).unwrap();
    println!("{}", result);
    assert!(result.contains("Bool::false"));
    assert!(result.contains("4"));
    assert!(result.contains("0"));
    assert!(result.contains("Point[Nat]::Point.mk(4, 6)"));
    assert!(result.contains("5"));
}

