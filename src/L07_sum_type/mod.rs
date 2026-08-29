//! L07：和类型（enum，带类型参数与索引）+ 依赖模式匹配。
//!
//! 相对 L06 新增：`enum` 声明（参数 `[A]` / 索引 `(len: Nat)`、构造子字段、
//! `-> ret` 索引返回）、`match`（编译为 (模式, 分支体) 列表 + 运行时首匹配）、
//! 索引精化（`unify_pm` + `Cxt::update_cxt`）、卡住的 match 作为中性值参与
//! unification / quote / rename / 应用（splice）。
//!
//! 设计说明见本目录 README.md。

use std::{ops::{Add, Sub}, rc::Rc};


use cxt::{Cxt, DeclEntry, Decls};
use pretty::pretty_tm;
use syntax::{Pruning, close_ty};

use crate::{list::List, parser_lib::Span};
use smol_str::SmolStr;

mod cxt;
mod struct_eq;
mod elaboration;
mod parser;
mod pattern_match;
mod pretty;
mod syntax;
mod unification;

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct MetaVar(u32);

#[derive(Debug, Clone)]
pub enum MetaEntry {
    Solved(Val, VTy),
    Unsolved(VTy),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ix(u32);

#[derive(Debug, Clone)]
pub enum DeclTm {
    Def,
    Println(Tm),
    Enum,
}

#[derive(Debug, Clone)]
pub enum Tm {
    Var(Ix),
    /// 全局引用（def / enum / 构造子），求值时查 decl 表。
    Decl(SmolStr),
    /// `x.field` 投影。
    Obj(Box<Tm>, Span<String>),
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
    /// enum 类型本体（enum 声明 λ 链的体）。params = (参数名, 值项, 值的类型, icit)，
    /// 声明处值项即参数自身；实例化（`Vec[Nat] 3`）后值槽携带当前实参。
    Sum(Span<String>, Vec<(Span<String>, Tm, Ty, Icit)>, Vec<Span<String>>),
    /// 构造子值：typ 求值后必须是其所属的（已实例化的）`Val::Sum`，
    /// datas = 构造子自身绑定器的值（隐式在前，声明序）。
    SumCase {
        typ: Box<Tm>,
        case_name: Span<String>,
        datas: Vec<(Span<String>, Tm, Icit)>,
    },
    /// 已编译的 match：分支体是检查过的项，运行时按模式首匹配。
    Match(Box<Tm>, Vec<(PatternDetail, Tm)>),
}

/// 编译后的模式。bind_count = 该模式在运行时消耗的 env 槽数：
/// Any / Bind 各占 1 槽（整个 head 值），Con 占 1 槽（head 自身）加各子模式槽数。
#[derive(Clone, Debug, PartialEq)]
pub enum PatternDetail {
    Any(Span<()>),
    Bind(Span<String>),
    Con(Span<String>, Vec<PatternDetail>),
}

impl PatternDetail {
    pub fn bind_count(&self) -> u32 {
        match self {
            PatternDetail::Any(_) => 1,
            PatternDetail::Bind(_) => 1,
            PatternDetail::Con(_, subs) => 1 + subs.iter().map(|s| s.bind_count()).sum::<u32>(),
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
        write!(f, "Closure(..{}, {:?})", self.0.len(), self.1)
    }
}

#[derive(Debug, Clone)]
pub enum Val {
    Flex(MetaVar, Spine),
    Rigid(Lvl, Spine),
    /// 未展开的全局引用（递归定义的占位 / simplify 后的 decl 表）。
    Decl(SmolStr, Spine),
    /// 卡住的投影（被投影者还不是构造子值 / Sum 类型）。
    Obj(Box<Val>, Span<String>, Spine),
    Lam(Span<String>, Icit, Closure),
    Pi(Span<String>, Icit, Box<VTy>, Closure),
    U,
    LiteralType,
    LiteralIntro(Span<String>),
    Prim,
    Sum(
        Span<String>,
        Vec<(Span<String>, Val, VTy, Icit)>, // (参数名, 实参值, 实参的类型, icit)
        Vec<Span<String>>,
    ),
    SumCase {
        typ: Box<Val>,
        case_name: Span<String>,
        datas: Vec<(Span<String>, Val, Icit)>,
    },
    /// 卡住的 match：scrutinee 不是构造子值，等待 scrutinee 归约后再选分支。
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
    if x.0 >= l.0 {
        // 宽松处理：越界的 rigid 映射到 0（调用方多是显示/临时路径）。
        // 严格断言在依赖匹配的某些未收敛路径上会 panic；这里保守降级。
        Ix(0)
    } else {
        Ix(l.0 - x.0 - 1)
    }
}

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
    /// unify 递归深度防护（L13 同款做法）。每次外部配置（unify_catch /
    /// unify_pm 入口）充值；递归中递减，归零即 Err——防索引槽互相嵌入
    /// 的构造子值比较（SuccCase 的 typ 含索引、索引又是 SuccCase）无限递归。
    unify_fuel: std::cell::Cell<u32>,
}

const UNIFY_FUEL: u32 = 4096;

impl Infer {
    pub fn new() -> Self {
        Self {
            meta: vec![],
            unify_fuel: std::cell::Cell::new(UNIFY_FUEL),
        }
    }

    fn new_meta(&mut self, a: VTy) -> MetaVar {
        self.meta.push(MetaEntry::Unsolved(a));
        MetaVar(self.meta.len() as u32 - 1)
    }

    /// 生成一个元变量：类型按当前上下文封口，项形如 `?m <pruning>`（只取可见参数）。
    fn fresh_meta(&mut self, decl: &Decls, cxt: &Cxt, a: VTy) -> Tm {
        let closed = self.eval(
            decl,
            &List::new(),
            close_ty(cxt.locals.clone(), self.quote(decl, cxt.lvl, a)),
        );
        let m = self.new_meta(closed);
        Tm::AppPruning(Box::new(Tm::Meta(m)), cxt.pruning.clone())
    }

    fn lookup_meta(&self, m: MetaVar) -> &MetaEntry {
        &self.meta[m.0 as usize]
    }

    /// 元变量快照 / 回滚：模式编译的可达性探测在"临时状态"里做合一，
    /// 探测期间解出的 meta 全部丢弃。
    pub(crate) fn meta_snapshot(&self) -> Vec<MetaEntry> {
        self.meta.clone()
    }

    pub(crate) fn meta_restore(&mut self, snap: Vec<MetaEntry>) {
        self.meta = snap;
    }

    /// 给 unify/force 的共享 fuel 池充值（外层合一入口调用）。
    pub(crate) fn meta_refuel(&self) {
        self.unify_fuel.set(UNIFY_FUEL);
    }

    /// 当前 fuel 余量（调试）
    #[allow(unused)]
    /// 元变量探测 + decl 表展开 + 卡住投影的再投影。
    /// 深度防护：meta 解链可能形成间接环（solve 无跨 meta occurs check），
    /// 展开会无限递归——只在**展开递归**时消耗 fuel（高频直通路径不消耗），
    /// fuel 耗尽时停止展开，把值当作未解处理。
    pub fn force(&self, decl: &Decls, t: Val) -> Val {
        /// 展开燃料：每个展开步骤消耗 1，耗尽即停止（防环）。
        fn burn(cell: &std::cell::Cell<u32>) -> bool {
            let f = cell.get();
            if f == 0 {
                return false;
            }
            cell.set(f - 1);
            true
        }
        match t {
            Val::Flex(m, sp) => match self.lookup_meta(m) {
                MetaEntry::Solved(t_solved, _) if burn(&self.unify_fuel) => {
                    if std::env::var_os("L07_LOOP").is_some() && self.unify_fuel.get() < 2200 {
                        eprintln!("  force-expand meta {} (fuel {})", m.0, self.unify_fuel.get());
                    }
                    self.force(decl, self.v_app_sp(decl, t_solved.clone(), sp))
                }
                _ => Val::Flex(m, sp),
            },
            Val::Decl(name, sp) => match decl.get(&name) {
                // unfold 前先检查自引用占位（递归 def 的占位值与 simpl_decl
                // 的中性条目都是 `Decl(自身名, [])`）：v_app_sp 后仍是原值，
                // unfold 永无进展，只会自旋烧光 fuel 池。直接按中性返回。
                Some(e)
                    if !matches!(&e.val, Val::Decl(n2, s2) if *n2 == *name && s2.is_empty())
                        && burn(&self.unify_fuel) =>
                {
                    self.force(decl, self.v_app_sp(decl, e.val.clone(), sp))
                }
                None => Val::Decl(name, sp),
                _ => Val::Decl(name, sp),
            },
            Val::Obj(v, name, sp) => {
                let v = self.force(decl, *v);
                match project(&v, &name) {
                    Some(p) if burn(&self.unify_fuel) => {
                        self.force(decl, self.v_app_sp(decl, p, sp))
                    }
                    _ => Val::Obj(Box::new(v), name, sp),
                }
            }
            t => t,
        }
    }

    fn v_meta(&self, m: MetaVar) -> Val {
        match self.lookup_meta(m) {
            MetaEntry::Solved(v, _) => v.clone(),
            MetaEntry::Unsolved(_) => Val::vmeta(m),
        }
    }

    fn closure_apply(&self, decl: &Decls, closure: &Closure, u: Val) -> Val {
        self.eval(decl, &closure.0.prepend(u), *closure.1.clone())
    }

    /// 把 `u` 应用到 `t`。卡住的 match 吸收参数：把应用拼进每个分支体——
    /// scrutinee 归约后恰好命中一个分支，语义保持（否则卡住 match 无法被应用）。
    fn v_app(&self, decl: &Decls, t: Val, u: Val, i: Icit) -> Val {
        match t {
            Val::Lam(_, _, closure) => self.closure_apply(decl, &closure, u),
            Val::Flex(m, sp) => Val::Flex(m, sp.prepend((u, i))),
            Val::Rigid(x, sp) => Val::Rigid(x, sp.prepend((u, i))),
            Val::Decl(name, sp) => Val::Decl(name, sp.prepend((u, i))),
            Val::Obj(v, name, sp) => Val::Obj(v, name, sp.prepend((u, i))),
            Val::Match(val, env, cases) => {
                let l = Lvl(env.len() as u32);
                let u_tm = self.quote(decl, l, u);
                let cases = cases
                    .into_iter()
                    .map(|(p, b)| (p, Tm::App(Box::new(b), Box::new(u_tm.clone()), i)))
                    .collect();
                Val::Match(val, env, cases)
            }
            x => panic!("impossible apply\n  {x:?}\nto\n  {u:?}"),
        }
    }

    fn v_app_sp(&self, decl: &Decls, t: Val, spine: Spine) -> Val {
        match spine {
            List { head: None, .. } => t,
            a => {
                let (u, i) = a.head().unwrap();
                self.v_app(decl, self.v_app_sp(decl, t, a.tail()), u.clone(), *i)
            }
        }
    }

    fn v_app_pruning(&self, decl: &Decls, env: &Env, v: Val, pr: &Pruning) -> Val {
        match (env, pr) {
            (List { head: None, .. }, List { head: None, .. }) => v,
            (a, b) if a.head().is_some() && matches!(b.head(), Some(Some(_))) => self.v_app(
                decl,
                self.v_app_pruning(decl, &a.tail(), v, &b.tail()),
                a.head().unwrap().clone(),
                b.head().unwrap().unwrap(),
            ),
            (a, b) if a.head().is_some() && matches!(b.head(), Some(None)) => {
                self.v_app_pruning(decl, &a.tail(), v, &b.tail())
            }
            _ => panic!("impossible {v:?}"),
        }
    }

    fn eval(&self, decl: &Decls, env: &Env, tm: Tm) -> Val {
        match tm {
            Tm::Var(x) => match env.iter().nth(x.0 as usize) {
                Some(v) => v.clone(),
                None => panic!("unbound de Bruijn index {x:?}"),
            },
            Tm::Decl(name) => match decl.get(&name) {
                Some(e) => e.val.clone(),
                None => panic!("unbound global {name}"),
            },
            Tm::Obj(tm, name) => {
                let v = self.eval(decl, env, *tm);
                match project(&v, &name) {
                    Some(p) => p,
                    None => Val::Obj(Box::new(v), name, List::new()),
                }
            }
            Tm::App(t, u, i) => {
                let u_val = self.eval(decl, env, *u);
                self.v_app(decl, self.eval(decl, env, *t), u_val, i)
            }
            Tm::Lam(x, i, t) => Val::Lam(x, i, Closure(env.clone(), t)),
            Tm::Pi(x, i, a, b) => Val::Pi(x, i, Box::new(self.eval(decl, env, *a)), Closure(env.clone(), b)),
            Tm::Let(_, _, t, u) => {
                let t_val = self.eval(decl, env, *t);
                self.eval(decl, &env.prepend(t_val), *u)
            }
            Tm::U => Val::U,
            Tm::Meta(m) => self.v_meta(m),
            Tm::AppPruning(t, pr) => self.v_app_pruning(decl, env, self.eval(decl, env, *t), &pr),
            Tm::LiteralIntro(x) => Val::LiteralIntro(x),
            Tm::LiteralType => Val::LiteralType,
            Tm::Prim => match (env.iter().nth(1), env.iter().nth(0)) {
                (Some(Val::LiteralIntro(a)), Some(Val::LiteralIntro(b))) => {
                    Val::LiteralIntro(a.clone().map(|x| format!("{x}{}", b.data)))
                }
                _ => Val::Prim,
            },
            Tm::Sum(name, params, cases) => {
                let new_params = params
                    .into_iter()
                    .map(|(n, v, t, i)| {
                        (n, self.eval(decl, env, v), self.eval(decl, env, t), i)
                    })
                    .collect();
                Val::Sum(name, new_params, cases)
            }
            Tm::SumCase {
                typ,
                case_name,
                datas,
            } => {
                let typ = self.eval(decl, env, *typ);
                let datas = datas
                    .into_iter()
                    .map(|(n, v, i)| (n, self.eval(decl, env, v), i))
                    .collect();
                Val::SumCase {
                    typ: Box::new(typ),
                    case_name,
                    datas,
                }
            }
            Tm::Match(tm, cases) => {
                let val = self.force(decl, self.eval(decl, env, *tm));
                match val {
                    Val::SumCase { .. } => match Compiler::eval_aux(self, decl, val.clone(), env, &cases) {
                        Some((body, env)) => self.eval(decl, &env, body),
                        None => Val::Match(Box::new(val), env.clone(), cases),
                    },
                    neutral => Val::Match(Box::new(neutral), env.clone(), cases),
                }
            }
        }
    }

    fn quote_sp(&self, decl: &Decls, l: Lvl, t: Tm, spine: Spine) -> Tm {
        match spine {
            List { head: None, .. } => t,
            a => {
                let (u, i) = a.head().unwrap();
                Tm::App(
                    Box::new(self.quote_sp(decl, l, t, a.tail())),
                    Box::new(self.quote(decl, l, u.clone())),
                    *i,
                )
            }
        }
    }

    fn quote(&self, decl: &Decls, l: Lvl, t: Val) -> Tm {
        let t = self.force(decl, t);
        match t {
            Val::Flex(m, sp) => self.quote_sp(decl, l, Tm::Meta(m), sp),
            Val::Rigid(x, sp) => self.quote_sp(decl, l, Tm::Var(lvl2ix(l, x)), sp),
            Val::Decl(name, sp) => self.quote_sp(decl, l, Tm::Decl(name), sp),
            Val::Obj(v, name, sp) => {
                self.quote_sp(decl, l, Tm::Obj(Box::new(self.quote(decl, l, *v)), name), sp)
            }
            Val::Lam(x, i, closure) => Tm::Lam(
                x,
                i,
                Box::new(self.quote(decl, l + 1, self.closure_apply(decl, &closure, Val::vvar(l)))),
            ),
            Val::Pi(x, i, a, closure) => Tm::Pi(
                x,
                i,
                Box::new(self.quote(decl, l, *a)),
                Box::new(self.quote(decl, l + 1, self.closure_apply(decl, &closure, Val::vvar(l)))),
            ),
            Val::U => Tm::U,
            Val::LiteralIntro(x) => Tm::LiteralIntro(x),
            Val::LiteralType => Tm::LiteralType,
            Val::Prim => Tm::Prim,
            Val::Sum(name, params, cases) => Tm::Sum(
                name,
                params
                    .into_iter()
                    .map(|(n, v, t, i)| (n, self.quote(decl, l, v), self.quote(decl, l, t), i))
                    .collect(),
                cases,
            ),
            Val::SumCase {
                typ,
                case_name,
                datas,
            } => Tm::SumCase {
                typ: Box::new(self.quote(decl, l, *typ)),
                case_name,
                datas: datas
                    .into_iter()
                    .map(|(n, v, i)| (n, self.quote(decl, l, v), i))
                    .collect(),
            },
            Val::Match(val, env, cases) => {
                // 分支体在"捕获 env + fresh rigid 槽"下重新求值再 quote：
                // 这样 quote → eval 往返是恒等的（L07 没做完的关键一处）。
                // 求值用简化 decl 表（全局值换成中性 Decl 引用），避免分支体
                // 里的递归调用被重展开（正确性 + 性能）。
                let declb = Rc::new(simpl_decl(decl));
                let tm_cases = cases
                    .into_iter()
                    .map(|(p, b)| {
                        let count = p.bind_count();
                        let env = (0..count).fold(env.clone(), |env, i| env.prepend(Val::vvar(l + i)));
                        let tm = self.eval(&declb, &env, b);
                        // 分支体的 quote 也要用简化表：eval 产生的中性
                        // Decl(f, spine)（递归调用占位）若用真实表 quote，
                        // 入口 force 会再展开一层——每层 quote 多展开一层，
                        // 递归函数的卡住 match 直接发散。
                        (p, self.quote(&declb, l + count, tm))
                    })
                    .collect();
                Tm::Match(Box::new(self.quote(decl, l, *val)), tm_cases)
            }
        }
    }

    pub fn nf(&self, decl: &Decls, env: &Env, t: Tm) -> Tm {
        // quote → eval 会 force；一次 nf 充值 fuel 防循环解
        self.unify_fuel.set(UNIFY_FUEL);
        let l = Lvl(env.len() as u32);
        self.quote(decl, l, self.eval(decl, env, t))
    }

    fn close_val(&self, decl: &Decls, cxt: &Cxt, t: Val) -> Closure {
        Closure(cxt.env.clone(), Box::new(self.quote(decl, cxt.lvl + 1, t)))
    }

    fn unify_catch(&mut self, decl: &Decls, cxt: &Cxt, t: Val, t_prime: Val) -> Result<(), Error> {
        self.unify_fuel.set(UNIFY_FUEL);
        self.unify(decl, cxt.lvl, cxt, t.clone(), t_prime.clone())
            .map_err(|_| {
                let fuel_note = if self.unify_fuel.get() == 0 {
                    " (fuel exhausted)"
                } else {
                    ""
                };
                Error(format!(
                    "can't unify{} {} == {}",
                    fuel_note,
                    pretty_tm(0, cxt.names(), &self.quote(decl, cxt.lvl, t)),
                    pretty_tm(0, cxt.names(), &self.quote(decl, cxt.lvl, t_prime)),
                ))
            })
    }
}

/// `v.field` 的值级投影：Sum 取索引参数的值；SumCase 先查 typ 的参数（索引）再查构造子字段。
/// 其余（Rigid / Flex / Decl / 卡住的 Obj / 函数……）返回 None → 卡住成 `Val::Obj`。
fn project(v: &Val, name: &Span<String>) -> Option<Val> {
    match v {
        Val::Sum(_, params, _) => params
            .iter()
            .find(|(n, ..)| n == name)
            .map(|(_, v, _, _)| v.clone()),
        Val::SumCase { typ, datas, .. } => {
            let params = match typ.as_ref() {
                Val::Sum(_, params, _) => params,
                _ => return None,
            };
            params
                .iter()
                .find(|(n, ..)| n == name)
                .map(|(_, v, _, _)| v.clone())
                .or_else(|| datas.iter().find(|(n, _, _)| n == name).map(|(_, v, _)| v.clone()))
        }
        _ => None,
    }
}

/// quote/rename 卡住 match 的分支体时用的 decl 表：所有全局值换成指向自身的
/// 中性 `Val::Decl`，防止递归定义在求值分支体时被重展开。enum 类型本体的值
/// （`Val::Sum`）保持原样——构造子值的 `typ` 槽需要真实的 Sum 值。
fn simpl_decl(decl: &Decls) -> Decls {
    decl.iter()
        .map(|(k, e)| {
            let val = match &e.val {
                Val::Sum(..) => e.val.clone(),
                _ => Val::Decl(k.clone(), List::new()),
            };
            (k.clone(), DeclEntry { ty: e.ty.clone(), val })
        })
        .collect()
}

#[allow(unused)]
pub fn run(input: &str, path_id: u32) -> Result<String, Error> {
    let mut infer = Infer::new();
    let ast = parser::parser(&preprocess(input), path_id).unwrap();
    let mut cxt = Cxt::new();
    let mut ret = String::new();
    for tm in ast {
        if std::env::var_os("L07_DEBUG").is_some() {
            eprintln!("> {}", parser::syntax::Decl::name(&tm));
        }
        let (x, _, new_cxt) = infer.infer(&cxt, tm)?;
        cxt = new_cxt;
        if let DeclTm::Println(x) = x {
            ret += &pretty_tm(0, cxt.names(), &infer.nf(cxt.decl(), &cxt.env, x));
            ret += "\n";
        }
    }
    Ok(ret)
}

pub fn preprocess(s: &str) -> String {
    let s = s
        .split("/*")
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

use pattern_match::Compiler;

use parser::syntax::Icit;

/// 值树里是否包含卡住的 match（含 spine / Sum 参数 / SumCase 的 typ 与 datas）。
/// 闭包（Lam/Pi）内部不探查——那需要 eval 展开，且"期望类型依赖被匹配变量
/// 的形态"的场景（`Eq (add a zero) a`）在值树表层就可见。
pub(crate) fn val_contains_match(v: &Val) -> bool {
    fn spine(sp: &Spine) -> bool {
        sp.iter().any(|(v, _)| val_contains_match(v))
    }
    match v {
        Val::Match(..) => true,
        Val::Flex(_, sp) | Val::Rigid(_, sp) | Val::Decl(_, sp) => spine(sp),
        Val::Obj(x, _, sp) => val_contains_match(x) || spine(sp),
        Val::Sum(_, params, _) => params
            .iter()
            .any(|(_, v, t, _)| val_contains_match(v) || val_contains_match(t)),
        Val::SumCase { typ, datas, .. } => {
            val_contains_match(typ) || datas.iter().any(|(_, v, _)| val_contains_match(v))
        }
        Val::Lam(..)
        | Val::Pi(..)
        | Val::U
        | Val::LiteralType
        | Val::LiteralIntro(_)
        | Val::Prim => false,
    }
}

#[cfg(test)]
mod tests;
