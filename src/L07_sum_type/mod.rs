//! L07：和类型（enum，带类型参数与索引）+ 依赖模式匹配。
//!
//! 相对 L06 新增：`enum` 声明（参数 `[A]` / 索引 `(len: Nat)`、构造子字段、
//! `-> ret` 索引返回）、`match`（编译为 (模式, 分支体) 列表 + 运行时首匹配）、
//! 索引精化（`unify_pm` + `Cxt::update_cxt`）、卡住的 match 作为中性值参与
//! unification / quote / rename / 应用（splice）。
//!
//! 设计说明见本目录 README.md。

use std::{
    ops::{Add, Sub},
    rc::Rc,
    sync::{
        atomic::{AtomicBool, Ordering},
        LazyLock,
    },
};

/// `L07_LOOP` 调试开关（进程级，只读一次；热路径零 env 访问）。
pub(crate) static LOOP_DEBUG: LazyLock<AtomicBool> =
    LazyLock::new(|| AtomicBool::new(std::env::var("L07_LOOP").is_ok()));


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
    /// 内建函数体标记（携带名字：求值时卡成 `Val::Prim(name, env_spine)`）。
    Prim(SmolStr),
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
pub struct Lvl(pub u32);

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
    /// 卡住的内建应用：名字 + 已收实参 spine（头 = 最后应用的实参）。
    /// 全部实参字面量时在 `force` 归约（目前仅 string_concat），否则保持
    /// 中性参与 unify / quote / rename（名字 + 实参不可丢——丢实参的单元
    /// `Prim` 会把 `x ++ y ≡ x ++ z` 判成相等）。
    Prim(SmolStr, Spine),
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
    /// `pending` = 卡住期间累积的应用实参（值层保存，分支选中后在值层应用
    /// ——项层 splice 把实参 quote 进分支体时，实参的自由变量会引用到
    /// 错误的上下文，见 `v_app` 的 Match 臂）。
    Match(Box<Val>, Env, Vec<(PatternDetail, Tm)>, Vec<(Val, Icit)>),
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
        // 语义上不可达：值里出现了超出 quote 层级的 rigid。debug 构建下断言
        // 捕捉，release 保守降级到 0（只出现在显示路径上时会可见）。
        debug_assert!(false, "lvl2ix: {x:?} out of range at {l:?}");
        Ix(0)
    } else {
        Ix(l.0 - x.0 - 1)
    }
}

#[derive(Debug)]
pub(crate) struct UnifyError;

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
    /// pattern 编译入口）充值；递归中递减，归零即 Err——防索引槽互相嵌入
    /// 的构造子值比较（SuccCase 的 typ 含索引、索引又是 SuccCase）无限递归。
    unify_fuel: std::cell::Cell<u32>,
    /// 模式特化方程的解：子句变量 := 值。这是**分支局部的事实表**——
    /// 变量的层级、env 槽、运行时布局都不动，`force` 在读点惰性展开。
    /// 臂边界 / 可达性探测做快照回滚（`pm_mark` / `pm_restore`）。
    pm_defs: Vec<(Lvl, Val)>,
    /// 当前可被特化方程求解的 rigid 层级（= 当前子句的 bind 槽）。
    /// 只在模式走查与探测期间非空；分支体检查期间必须为空（常规转换
    /// 不得解假设——否则 `Eq x y` 会被"证成" `Eq y y`）。
    pm_solvable: Vec<Lvl>,
}

const UNIFY_FUEL: u32 = 4096;

impl Infer {
    pub fn new() -> Self {
        Self {
            meta: vec![],
            unify_fuel: std::cell::Cell::new(UNIFY_FUEL),
            pm_defs: Vec::new(),
            pm_solvable: Vec::new(),
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

    /// 模式精化状态的快照点（长度即可，回滚 = 截断）。
    pub(crate) fn pm_mark(&self) -> (usize, usize) {
        (self.pm_defs.len(), self.pm_solvable.len())
    }

    /// 回滚到快照点：臂边界 / 探测边界调用。本臂解出的 meta 不回滚
    /// （分支体 Tm 引用着它们；解在 rename 时已把精化"烘焙"为无 def 形式）。
    /// solvable 只在走查期间单调增长，截断即可回到快照长度。
    pub(crate) fn pm_restore(&mut self, mark: (usize, usize)) {
        self.pm_defs.truncate(mark.0);
        self.pm_solvable.truncate(mark.1);
    }

    pub(crate) fn pm_solvable_push(&mut self, l: Lvl) {
        self.pm_solvable.push(l);
    }

    /// 分支体检查前摘走可解集（体检查走常规转换语义，不得解假设），
    /// 检查完由调用侧 `pm_solvable_set` 原样放回。
    pub(crate) fn pm_solvable_take(&mut self) -> Vec<Lvl> {
        std::mem::take(&mut self.pm_solvable)
    }

    pub(crate) fn pm_solvable_set(&mut self, v: Vec<Lvl>) {
        self.pm_solvable = v;
    }

    pub(crate) fn pm_def(&self, x: Lvl) -> Option<&Val> {
        self.pm_defs
            .iter()
            .rev()
            .find(|(l, _)| *l == x)
            .map(|(_, v)| v)
    }

    pub(crate) fn pm_solvable_contains(&self, x: Lvl) -> bool {
        self.pm_solvable.contains(&x)
    }

    /// 记录一条特化解 `x := v`。环守卫：v 不得（结构上）提及 x——
    /// 闭包内部不探查，那里的环由 force 的 fuel 兜底。
    pub(crate) fn pm_solve(&mut self, x: Lvl, v: &Val) -> bool {
        if val_mentions_lvl(v, x) {
            return false;
        }
        self.pm_defs.push((x, v.clone()));
        true
    }

    /// 当前 fuel 余量（调试）
    /// 元变量探测 + decl 表展开 + 卡住投影的再投影 + 模式精化展开。
    /// 深度防护：meta 解链可能形成间接环（solve 无跨 meta occurs check），
    /// 展开会无限递归——只在**展开递归**时消耗 fuel（高频直通路径不消耗），
    /// fuel 耗尽时停止展开，把值当作未解处理。
    /// 合一器**参数视角**的 WHNF：与 `force` 相同，但不展开 pm_defs 精化、
    /// 不做 Match 重选。`invert` / `prune_vflex` 关心的是"元变量被应用在
    /// 哪些槽位上"——槽位引用（`Rigid(x)`）本身就是作用域事实，分支内的
    /// 精化等式（x := zero）不改变槽位的存在；在它们身上展开反而会把
    /// 可逆 spine 变成含构造子值的不可逆 spine。
    pub(crate) fn force_arg(&self, decl: &Decls, t: Val) -> Val {
        match &t {
            Val::Rigid(..) | Val::Match(..) => t,
            _ => self.force(decl, t),
        }
    }

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
                    if LOOP_DEBUG.load(Ordering::Relaxed) && self.unify_fuel.get() < 2200 {
                        eprintln!("  force-expand meta {} (fuel {})", m.0, self.unify_fuel.get());
                    }
                    self.force(decl, self.v_app_sp(decl, t_solved.clone(), sp))
                }
                _ => Val::Flex(m, sp),
            },
            // 模式精化：被特化的子句变量在**读点**展开。这是"惰性精化"的
            // 核心——层级、env 槽、既有值一概不动，所有消费者（unify/quote/
            // rename）经过 force 自动看到精化后的世界。
            Val::Rigid(x, List { head: None, .. }) => match self.pm_def(x) {
                Some(v) if burn(&self.unify_fuel) => self.force(decl, v.clone()),
                _ => Val::Rigid(x, List::new()),
            },
            // 卡住的 match：scrutinee 是在 match 创建之后才被特化/解出时，
            // 这里重新尝试选分支。没有这一步，精化无法传播进"卡住 match
            // 里面"（期望类型 `Eq (add a zero) a` 的 `add a zero` 就是它）。
            Val::Match(s, env, cases, pending) => {
                let s2 = self.force(decl, (*s).clone());
                if let Val::SumCase { .. } = &s2 {
                    if burn(&self.unify_fuel) {
                        if let Some((tm, env2)) =
                            Compiler::eval_aux(self, decl, s2, &env, &cases)
                        {
                            // 分支选中：先在值层应用卡住期累积的实参（值无需
                            // quote，作用域天然正确；项层 splice 会把实参的
                            // 自由变量引到错误上下文）。
                            let mut v = self.eval(decl, &env2, tm);
                            for (u, i) in pending.iter().cloned() {
                                v = self.v_app(decl, v, u, i);
                            }
                            return self.force(decl, v);
                        }
                    }
                }
                Val::Match(s, env, cases, pending)
            }
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
            // 卡住的内建：全部实参字面量时归约（目前仅 string_concat），
            // 否则保持卡住。名字 + 实参 spine 由 eval(Tm::Prim) 构造。
            Val::Prim(name, sp) => {
                let args: Vec<Val> = sp.iter().map(|(v, _)| v.clone()).collect();
                if name == "string_concat" && args.len() >= 2 && burn(&self.unify_fuel) {
                    match (&args[args.len() - 1], &args[args.len() - 2]) {
                        (Val::LiteralIntro(a), Val::LiteralIntro(b)) => {
                            return Val::LiteralIntro(
                                a.clone().map(|x| format!("{x}{}", b.data)),
                            );
                        }
                        _ => {}
                    }
                }
                Val::Prim(name, sp)
            }
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

    /// 把 `u` 应用到 `t`。卡住的 match 把实参收进 `pending`（值层保存）——
    /// scrutinee 归约选中分支后，由 `force` / `eval` 在**值层**逐个应用：
    /// 项层 splice 需要把实参 quote 成项，而实参的自由变量层级可能超出
    /// 捕获 env，无法引到正确上下文。
    fn v_app(&self, decl: &Decls, t: Val, u: Val, i: Icit) -> Val {
        match t {
            Val::Lam(_, _, closure) => self.closure_apply(decl, &closure, u),
            Val::Flex(m, sp) => Val::Flex(m, sp.prepend((u, i))),
            Val::Rigid(x, sp) => Val::Rigid(x, sp.prepend((u, i))),
            Val::Decl(name, sp) => Val::Decl(name, sp.prepend((u, i))),
            Val::Obj(v, name, sp) => Val::Obj(v, name, sp.prepend((u, i))),
            Val::Prim(name, sp) => Val::Prim(name, sp.prepend((u, i))),
            Val::Match(val, env, cases, mut pending) => {
                pending.push((u, i));
                Val::Match(val, env, cases, pending)
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
            Tm::Prim(name) => {
                // 实参经 Lam 链进 env（最内 = 最后应用）：卡成带名字与实参
                // spine 的 Prim。归约统一在 force（不在求值点按 env 触发——
                // quote → eval 往返时项已改成 `Prim 实参` 的应用形态，按
                // 现场 env 触发会把无关的字面量拼进来）。
                let mut args: Vec<(Val, Icit)> =
                    env.iter().map(|v| (v.clone(), Icit::Expl)).collect();
                args.reverse(); // 应用序 → spine 头 = 最后应用
                Val::Prim(
                    name,
                    args.into_iter().fold(List::new(), |acc, e| acc.prepend(e)),
                )
            }
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
                        None => Val::Match(Box::new(val), env.clone(), cases, Vec::new()),
                    },
                    neutral => Val::Match(Box::new(neutral), env.clone(), cases, Vec::new()),
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
            Val::Prim(name, sp) => self.quote_sp(decl, l, Tm::Prim(name), sp),
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
            Val::Match(val, env, cases, pending) => {
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
                // 卡住期累积的实参按应用序包在 Match 外（值层应用在
                // force/eval 的分支选中后做；quote → eval 往返由此保持）。
                // 实参的自由层级属当前上下文，quote 在调用方的 l 下正确。
                let m = Tm::Match(Box::new(self.quote(decl, l, *val)), tm_cases);
                pending.into_iter().fold(m, |acc, (u, i)| {
                    Tm::App(Box::new(acc), Box::new(self.quote(decl, l, u)), i)
                })
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

/// 值树里是否出现某层级（浅层结构扫描；闭包跳过——那里的环由 force 的
/// fuel 兜底）。特化解的环守卫（`pm_solve`）用。
fn val_mentions_lvl(v: &Val, x: Lvl) -> bool {
    fn spine(sp: &Spine, x: Lvl) -> bool {
        sp.iter().any(|(v, _)| val_mentions_lvl(v, x))
    }
    match v {
        Val::Rigid(y, sp) => *y == x || spine(sp, x),
        Val::Flex(_, sp) | Val::Decl(_, sp) => spine(sp, x),
        Val::Obj(o, _, sp) => val_mentions_lvl(o, x) || spine(sp, x),
        Val::Sum(_, params, _) => {
            params
                .iter()
                .any(|(_, v, t, _)| val_mentions_lvl(v, x) || val_mentions_lvl(t, x))
        }
        Val::SumCase { typ, datas, .. } => {
            val_mentions_lvl(typ, x) || datas.iter().any(|(_, v, _)| val_mentions_lvl(v, x))
        }
        Val::Match(s, env, _, pending) => {
            val_mentions_lvl(s, x)
                || env.iter().any(|v| val_mentions_lvl(v, x))
                || pending.iter().any(|(v, _)| val_mentions_lvl(v, x))
        }
        Val::Prim(_, sp) => spine(sp, x),
        Val::Lam(..) | Val::Pi(..) | Val::U | Val::LiteralType | Val::LiteralIntro(_) => false,
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
    let ast = match parser::parser(&preprocess(input), path_id) {
        Some(a) => a,
        None => return Err(Error("parse error".to_owned())),
    };
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

#[cfg(test)]
mod tests;
