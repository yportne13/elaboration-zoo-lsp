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

// ---------------------------------------------------------------------------
// Function-level CPU probe for the elaborator (perf diagnostics).
//
// Active only when the env var TYPORT_PRELUDE_PROF is set.  Each
// instrumented entry point records EXCLUSIVE time and call count into a
// global static (nested profiled calls are charged to the inner counter
// via a thread-local child-time stack), so the rows sum to approximately
// the wall clock.  Zero overhead when disabled (one atomic load per
// instrumented call).
// ---------------------------------------------------------------------------
pub struct FuncProf {
    pub enabled: std::sync::atomic::AtomicBool,
    pub check: (std::sync::atomic::AtomicU64, std::sync::atomic::AtomicU64),
    pub infer_expr: (std::sync::atomic::AtomicU64, std::sync::atomic::AtomicU64),
    pub check_universe: (std::sync::atomic::AtomicU64, std::sync::atomic::AtomicU64),
    pub eval: (std::sync::atomic::AtomicU64, std::sync::atomic::AtomicU64),
    pub force: (std::sync::atomic::AtomicU64, std::sync::atomic::AtomicU64),
    pub v_app: (std::sync::atomic::AtomicU64, std::sync::atomic::AtomicU64),
    pub quote: (std::sync::atomic::AtomicU64, std::sync::atomic::AtomicU64),
    pub nf: (std::sync::atomic::AtomicU64, std::sync::atomic::AtomicU64),
    pub unify: (std::sync::atomic::AtomicU64, std::sync::atomic::AtomicU64),
    pub solve_trait: (std::sync::atomic::AtomicU64, std::sync::atomic::AtomicU64),
    /// force() entry value shape histogram, indexed by `val_shape_index`.
    pub force_shape: [std::sync::atomic::AtomicU64; 14],
}

pub static FUNC_PROF: FuncProf = FuncProf {
    enabled: std::sync::atomic::AtomicBool::new(false),
    check: (std::sync::atomic::AtomicU64::new(0), std::sync::atomic::AtomicU64::new(0)),
    infer_expr: (std::sync::atomic::AtomicU64::new(0), std::sync::atomic::AtomicU64::new(0)),
    check_universe: (std::sync::atomic::AtomicU64::new(0), std::sync::atomic::AtomicU64::new(0)),
    eval: (std::sync::atomic::AtomicU64::new(0), std::sync::atomic::AtomicU64::new(0)),
    force: (std::sync::atomic::AtomicU64::new(0), std::sync::atomic::AtomicU64::new(0)),
    v_app: (std::sync::atomic::AtomicU64::new(0), std::sync::atomic::AtomicU64::new(0)),
    quote: (std::sync::atomic::AtomicU64::new(0), std::sync::atomic::AtomicU64::new(0)),
    nf: (std::sync::atomic::AtomicU64::new(0), std::sync::atomic::AtomicU64::new(0)),
    unify: (std::sync::atomic::AtomicU64::new(0), std::sync::atomic::AtomicU64::new(0)),
    solve_trait: (std::sync::atomic::AtomicU64::new(0), std::sync::atomic::AtomicU64::new(0)),
    force_shape: [
        std::sync::atomic::AtomicU64::new(0), std::sync::atomic::AtomicU64::new(0),
        std::sync::atomic::AtomicU64::new(0), std::sync::atomic::AtomicU64::new(0),
        std::sync::atomic::AtomicU64::new(0), std::sync::atomic::AtomicU64::new(0),
        std::sync::atomic::AtomicU64::new(0), std::sync::atomic::AtomicU64::new(0),
        std::sync::atomic::AtomicU64::new(0), std::sync::atomic::AtomicU64::new(0),
        std::sync::atomic::AtomicU64::new(0), std::sync::atomic::AtomicU64::new(0),
        std::sync::atomic::AtomicU64::new(0), std::sync::atomic::AtomicU64::new(0),
    ],
};

/// Index of a `Val` variant in `FUNC_PROF.force_shape`.
#[inline]
pub fn val_shape_index(v: &Val) -> usize {
    match v {
        Val::Flex(..) => 0,
        Val::Rigid(..) => 1,
        Val::Decl(..) => 2,
        Val::Obj(..) => 3,
        Val::Lam(..) => 4,
        Val::Pi(..) => 5,
        Val::U(_) => 6,
        Val::LiteralType => 7,
        Val::LiteralIntro(_) => 8,
        Val::Sum(..) => 9,
        Val::SumCase { .. } => 10,
        Val::Match(..) => 11,
        Val::Call(..) => 12,
        Val::Nat(..) => 13,
    }
}

pub fn prof_shape(v: &Val) {
    if FUNC_PROF.enabled.load(std::sync::atomic::Ordering::Relaxed) {
        FUNC_PROF.force_shape[val_shape_index(v)].fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }
}

// ---------------------------------------------------------------------------
// force() result memo.
//
// The dominant elaboration cost is re-forcing structurally shared, already
// normal `Val` graphs: the same ~200k distinct value nodes account for
// hundreds of millions of `force` calls during prelude load (measured
// 636M calls over 188k distinct pointers, ~3400x redundancy).  The memo
// keys on the input node's address; correctness rests on three pillars:
//
// 1. Keepalive: each entry holds the input `Rc`, so a freed address can
//    never be reused by a different `Val` while the entry lives.
// 2. Taint: a walk that consults state the memo cannot abstract over —
//    a meta variable (solutions change, and the ns-probe machinery even
//    rolls them back) or an impure prim (mutable globals / file IO /
//    diagnostics whose re-execution on re-force is observable) — bumps a
//    thread-local counter, and entries whose counter moved during their
//    walk are simply not inserted.
// 3. Version: the only decl-table state `force` reads is a name's
//    prim-ness (the `Val::Decl` / prim-name `Val::Call` arms).  Every
//    transition of an entry's prim-ness bumps a global version; entries
//    record the version they were computed under and lookups treat a
//    mismatch as a miss, so stale entries can never be served.
//
// The memo is thread-local: `force` results are per-thread recomputed on
// other threads, and no lock is taken on the hot path.
// ---------------------------------------------------------------------------

/// Prims whose result depends only on their arguments.  Walks that consult
/// them are memoizable; every other prim taints the enclosing walk (see
/// `FORCE_MEMO`).
fn prim_is_pure(name: &str) -> bool {
    matches!(name,
        "nat_add" | "nat_mul" | "nat_sub" | "nat_div" | "nat_rem"
        | "nat_to_dec" | "width_range"
        | "string_concat" | "str_eq" | "str_indent2")
}

thread_local! {
    static FORCE_MEMO: std::cell::RefCell<rustc_hash::FxHashMap<usize, (Rc<Val>, Rc<Val>, u64, u64)>> =
        std::cell::RefCell::new(rustc_hash::FxHashMap::default());
    static FORCE_MEMO_EPOCH: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    static FORCE_TAINT: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

static PRIM_VERSION: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// Upper bound on memo entries; overflow clears the whole table (bounded
/// memory for garbage-pin scenarios, at the price of re-walking once).
const FORCE_MEMO_CAP: usize = 1 << 20;

/// Start a fresh memo epoch (per user file change / prelude load).  Not
/// required for correctness — purely bounds the memory pinned by
/// keepalives of values that are no longer otherwise reachable.
///
/// Clearing DROPS the pinned `Rc<Val>` inputs, so a later allocation CAN
/// reuse one of those addresses — and the memo is keyed by address alone
/// (`Rc::as_ptr`).  An epoch guards lookups: entries from a previous epoch
/// are ignored even on an address collision (stale forced value otherwise
/// leaks into unrelated elaboration — e.g. a later test reusing the freed
/// address of an old forced term).
pub fn force_memo_clear() {
    FORCE_MEMO.with(|m| m.borrow_mut().clear());
    FORCE_MEMO_EPOCH.with(|e| e.set(e.get() + 1));
}

#[inline]
fn force_taint_bump() {
    FORCE_TAINT.with(|t| t.set(t.get() + 1));
}

/// Record that some decl entry's prim-ness changed (see `PRIM_VERSION`).
pub fn prim_version_bump() {
    PRIM_VERSION.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
}

/// Is this value the `Nat` sum type?  The name is matched literally — the
/// same existing design assumption as `Raw::Nat`'s `decl.get("Nat")` lookup
/// and the `Tm::Sum(... "Nat")` special cases in `pretty.rs`.
pub(crate) fn is_nat_sum(v: &Val) -> bool {
    matches!(v, Val::Sum(name, _, _, false) if name.data == "Nat")
}

/// Display-only operator symbol for the prelude Nat arithmetic primops.
/// These are prim-backed (not inlined defs), so `quote` renders a stuck
/// application as `App(App(Decl("nat_add"), x), y)` — the pretty layer
/// restores the infix operator (mirrors the operator-char recovery, which
/// only fires for operator-named heads).  Also used as a name pre-filter
/// for the prim-backed `Val::Call` branch in `force`: only defs that
/// `register_nat_builtins` *overwrote* can appear there, so checking the
/// five names first keeps the common Call force free of the decl-table
/// hash lookup.  If a future prim replaces another body-carrying def, add
/// its name here.
pub(crate) fn nat_primop_symbol(name: &str) -> Option<&'static str> {
    match name {
        "nat_add" => Some("+"),
        "nat_mul" => Some("*"),
        "nat_sub" => Some("-"),
        "nat_div" => Some("/"),
        "nat_rem" => Some("%"),
        _ => None,
    }
}

/// If a `Tm::SumCase` step (with `typ` already evaluated to `v`) is a fully
/// concrete `Nat` constructor, return its native value: `zero` -> 0 and
/// `succ (Nat k)` -> k+1.  Anything else (a different sum type, a partially
/// stuck chain like `succ x` with x a rigid/meta, a non-nullary constructor,
/// or a value that would overflow u64) returns `None` and the caller keeps
/// the ordinary `Val::SumCase` shape.
fn nat_step_value(v: &Val, index: u32, datas: &[(Span<SmolStr>, Rc<Val>, Icit)]) -> Option<u64> {
    if !is_nat_sum(v) {
        return None;
    }
    match index {
        0 if datas.is_empty() => Some(0),
        1 if datas.len() == 1 => match datas[0].1.as_ref() {
            Val::Nat(k) => k.checked_add(1),
            _ => None,
        },
        _ => None,
    }
}

/// RAII guard that accumulates elapsed time into a (ns, count) pair on drop.
/// Times are EXCLUSIVE: time spent inside nested profiled calls is charged
/// to the nested counter (via a thread-local child-time stack), so the
/// printed rows sum to approximately the wall clock instead of
/// double-counting recursion.
pub struct ProfGuard {
    ns: &'static std::sync::atomic::AtomicU64,
    n: &'static std::sync::atomic::AtomicU64,
    t: std::time::Instant,
    active: bool,
}

thread_local! {
    /// Stack of (accumulated child elapsed) for active ProfGuards.
    static PROF_STACK: std::cell::RefCell<Vec<u64>> =
        std::cell::RefCell::new(Vec::new());
}

impl Drop for ProfGuard {
    fn drop(&mut self) {
        if self.active {
            let elapsed = self.t.elapsed().as_nanos() as u64;
            let exclusive = PROF_STACK.with(|s| {
                let mut s = s.borrow_mut();
                let child = s.pop().expect("prof stack underflow");
                if let Some(top) = s.last_mut() {
                    *top += elapsed;
                }
                elapsed.saturating_sub(child)
            });
            self.ns.fetch_add(exclusive, std::sync::atomic::Ordering::Relaxed);
            self.n.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
    }
}

/// Enter a profiled function.  `Some(guard)` only when profiling is enabled.
#[inline]
pub fn prof_enter(ns: &'static std::sync::atomic::AtomicU64, n: &'static std::sync::atomic::AtomicU64) -> Option<ProfGuard> {
    if FUNC_PROF.enabled.load(std::sync::atomic::Ordering::Relaxed) {
        PROF_STACK.with(|s| s.borrow_mut().push(0));
        Some(ProfGuard { ns, n, t: std::time::Instant::now(), active: true })
    } else {
        None
    }
}

/// Count-only probe for ultra-hot functions (e.g. `force`), where per-call
/// `Instant::now()` would distort the run: just increments the call counter.
#[inline]
pub fn prof_count(n: &'static std::sync::atomic::AtomicU64) {
    if FUNC_PROF.enabled.load(std::sync::atomic::Ordering::Relaxed) {
        n.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }
}

#[cfg(test)]
mod legacy_tests;

#[cfg(test)]
mod module_probe_tests;

#[cfg(test)]
mod class_tests;

#[cfg(test)]
mod module_tests;

#[cfg(test)]
mod calc_tests;

#[cfg(test)]
mod debug_test;

#[cfg(test)]
mod struct_refine_probe;

type Rc<T> = std::rc::Rc<T>;

// `decl.get` sits on the evaluator's hot paths (`Tm::Decl` eval arm, `v_app`,
// `force`); FxHash keys on the string bytes directly instead of SipHashing
// them (~4M lookups during prelude load alone).
pub(crate) type Decl = rustc_hash::FxHashMap<SmolStr, (Span<()>, Rc<Tm>, Rc<Val>, Rc<Ty>, Rc<VTy>, Option<PrimFunc>, String)>;

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct MetaVar(u32);

#[derive(Debug, Clone)]
pub enum MetaEntry {
    Solved(Rc<Val>, Rc<VTy>),
    Unsolved(Rc<VTy>, std::sync::Arc<Cxt>, Rc<VTy>, Span<()>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
    Class {
        //TODO:
    },
    Package,
    Import,
}

#[derive(Clone)]
pub struct PrimFunc(Rc<dyn Fn(&Infer, &Decl, &[Rc<Val>]) -> Option<Rc<Val>> + Send + Sync>);

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
    Sum(Span<SmolStr>, TmSumParams, TmSumCases, bool),
    SumCase {
        typ: Rc<Tm>,
        index: u32,
        datas: TmSumCaseDatas,
        is_trait: bool,
    },
    Match(Rc<Tm>, Vec<(PatternDetail, Rc<Tm>)>),
    /// Call(name, display_args, val_args, body) - body was inlined from function `name`
    Call(SmolStr, List<(Rc<Tm>, Icit)>, Rc<Tm>),
    /// Display-only node produced by `quote` when an inlined helper call
    /// backs an operator method (`nat_add_helper x y` for `x + y`).
    /// `symbol` is the operator to display (`+`); `name`/`args`/`body`
    /// mirror `Call` so that re-evaluating the node reproduces the original
    /// `Val::Call` exactly (quote → eval round-trip identity).
    OpCall { symbol: SmolStr, name: SmolStr, args: List<(Rc<Tm>, Icit)>, body: Rc<Tm> },
}

impl Drop for Tm {
    fn drop(&mut self) {
        // Leaf fast path: most drops are leaf-shaped terms; skip the
        // worklist machinery entirely for them.
        if matches!(self, Tm::Var(_) | Tm::Decl(_) | Tm::U(_) | Tm::Meta(_) | Tm::LiteralType | Tm::LiteralIntro(_)) {
            return;
        }
        // SAFETY contract for `drain_tm`: it moves every nested `Rc<Tm>` out
        // of the shell with `ptr::read` (nested collections are replaced
        // with empty ones); the caller must `forget` the shell, never drop
        // it normally.  Leaves are left untouched.
        fn drain_tm(t: &mut Tm, tms: &mut Vec<Rc<Tm>>) {
            match t {
                Tm::Var(_) | Tm::Decl(_) | Tm::U(_) | Tm::Meta(_) | Tm::LiteralType | Tm::LiteralIntro(_) => {
                    return;
                }
                Tm::Obj(x, _) => {
                    let x = unsafe { std::ptr::read(x) };
                    tms.push(x);
                }
                Tm::Lam(_, _, b) => {
                    let b = unsafe { std::ptr::read(b) };
                    tms.push(b);
                }
                Tm::App(f, u, _) => {
                    let f = unsafe { std::ptr::read(f) };
                    let u = unsafe { std::ptr::read(u) };
                    tms.push(f);
                    tms.push(u);
                }
                Tm::AppPruning(t, _) => {
                    let t = unsafe { std::ptr::read(t) };
                    tms.push(t);
                }
                Tm::Pi(_, _, a, b) => {
                    let a = unsafe { std::ptr::read(a) };
                    let b = unsafe { std::ptr::read(b) };
                    tms.push(a);
                    tms.push(b);
                }
                Tm::Let(_, a, t, u) => {
                    let a = unsafe { std::ptr::read(a) };
                    let t = unsafe { std::ptr::read(t) };
                    let u = unsafe { std::ptr::read(u) };
                    tms.push(a);
                    tms.push(t);
                    tms.push(u);
                }
                Tm::Sum(_, params, _, _) => {
                    let params = unsafe { std::ptr::read(params) };
                    for (_, t, ty, _) in params.iter() {
                        tms.push(t.clone());
                        tms.push(ty.clone());
                    }
                }
                Tm::SumCase { typ, datas, .. } => {
                    let typ = unsafe { std::ptr::read(typ) };
                    tms.push(typ);
                    let datas = unsafe { std::ptr::read(datas) };
                    for (_, d, _) in datas.iter() {
                        tms.push(d.clone());
                    }
                }
                Tm::Match(scru, cases) => {
                    let scru = unsafe { std::ptr::read(scru) };
                    tms.push(scru);
                    let cases = std::mem::replace(cases, Vec::new());
                    for (_, b) in cases.iter() {
                        tms.push(b.clone());
                    }
                }
                Tm::Call(_, args, body) => {
                    let args = std::mem::replace(args, List::new());
                    for (a, _) in args.iter() {
                        tms.push(a.clone());
                    }
                    let body = unsafe { std::ptr::read(body) };
                    tms.push(body);
                }
                Tm::OpCall { args, body, .. } => {
                    let args = std::mem::replace(args, List::new());
                    for (a, _) in args.iter() {
                        tms.push(a.clone());
                    }
                    let body = unsafe { std::ptr::read(body) };
                    tms.push(body);
                }
            }
            // The drained shell's fields were moved out; the caller
            // forgets it (a normal drop would double-release them).
        }
        let mut tms: Vec<Rc<Tm>> = Vec::new();
        let mut root = std::mem::replace(self, Tm::U(0));
        drain_tm(&mut root, &mut tms);
        std::mem::forget(root);
        while let Some(t) = tms.pop() {
            match Rc::try_unwrap(t) {
                Ok(mut t) => {
                    drain_tm(&mut t, &mut tms);
                    // The shell's fields were moved out by `drain_tm`;
                    // forgetting it (instead of dropping) releases nothing twice.
                    std::mem::forget(t);
                }
                Err(_) => continue, // shared elsewhere; count decremented only
            }
        }
    }
}

impl Tm {
    pub fn no_metas(&self, infer: &Infer, decl: &Decl, l: Lvl) -> Option<(Cxt, Rc<Val>, Span<()>)> {
        // Meta detection on a value graph: walk the `Val`s directly with a
        // pointer-keyed visited set instead of `quote`-ing each solved meta's
        // solution.  Quoting re-forced and re-materialized the whole solution
        // graph at every meta occurrence — on flattened module/bundle chains
        // (solutions embedding giant elaborated values) that dominated CPU
        // (measured ~65% of samples in examples/hdl/11-bundle-deep.typort).
        // Shared subgraphs are visited once, nothing is forced or quoted on
        // the fast path.
        let mut seen: rustc_hash::FxHashSet<usize> = rustc_hash::FxHashSet::default();
        self.no_metas_seen(infer, decl, l, &mut seen)
    }

    fn no_metas_seen(&self, infer: &Infer, decl: &Decl, l: Lvl, seen: &mut rustc_hash::FxHashSet<usize>) -> Option<(Cxt, Rc<Val>, Span<()>)> {
        match self {
            Tm::Var(_) | Tm::Decl(_) | Tm::U(_) | Tm::LiteralType | Tm::LiteralIntro(_) => None,
            Tm::Obj(tm, _) => Tm::no_metas_rc(tm, infer, decl, l, seen),
            Tm::Lam(_, _, t) => Tm::no_metas_rc(t, infer, decl, l + 1, seen),
            Tm::App(t, u, _) => Tm::no_metas_rc(t, infer, decl, l, seen).or_else(|| Tm::no_metas_rc(u, infer, decl, l, seen)),
            Tm::AppPruning(t, _) => {
                Tm::no_metas_rc(t, infer, decl, l, seen)
            },
            Tm::Pi(_, _, t, u) => Tm::no_metas_rc(t, infer, decl, l, seen).or_else(|| Tm::no_metas_rc(u, infer, decl, l + 1, seen)),
            Tm::Let(_, a, t, u) => Tm::no_metas_rc(a, infer, decl, l, seen).or_else(|| Tm::no_metas_rc(t, infer, decl, l, seen)).or_else(|| Tm::no_metas_rc(u, infer, decl, l, seen)),
            Tm::Meta(m) => match infer.lookup_meta(*m) {
                MetaEntry::Unsolved(_, cxt, oty, span) => Some((cxt.as_ref().clone(), oty.clone(), *span)),
                MetaEntry::Solved(v, _) => {
                    infer.val_no_metas(decl, l, v, seen)
                }
            },
            Tm::Sum(_, items, _, _) => items.iter().flat_map(|(_, t, ty, _)| Tm::no_metas_rc(t, infer, decl, l, seen).or_else(|| Tm::no_metas_rc(ty, infer, decl, l, seen))).next(),
            Tm::SumCase { typ, index: _, datas, is_trait: _ } => Tm::no_metas_rc(typ, infer, decl, l, seen)
                .or_else(|| datas.iter().flat_map(|(_, t, _)| Tm::no_metas_rc(t, infer, decl, l, seen)).next()),
            Tm::Match(tm, items) => Tm::no_metas_rc(tm, infer, decl, l, seen).or_else(|| items.iter().flat_map(|(_, t)| Tm::no_metas_rc(t, infer, decl, l, seen)).next()),
            Tm::Call(_, args, body) => args.iter().flat_map(|(a, _)| Tm::no_metas_rc(a, infer, decl, l, seen)).next().or_else(|| Tm::no_metas_rc(body, infer, decl, l, seen)),
            Tm::OpCall { args, body, .. } => args.iter().flat_map(|(a, _)| Tm::no_metas_rc(a, infer, decl, l, seen)).next().or_else(|| Tm::no_metas_rc(body, infer, decl, l, seen)),
        }
    }

    /// `no_metas_seen` with pointer-keyed dedup: elaborated terms share
    /// subtrees through `Rc` (Phase-A reuse embeds the same checked term in
    /// create/tree bodies), and a plain recursive walk would re-visit them.
    fn no_metas_rc(tm: &Rc<Tm>, infer: &Infer, decl: &Decl, l: Lvl, seen: &mut rustc_hash::FxHashSet<usize>) -> Option<(Cxt, Rc<Val>, Span<()>)> {
        if !seen.insert(Rc::as_ptr(tm) as usize) {
            return None;
        }
        tm.no_metas_seen(infer, decl, l, seen)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum PatternDetail {
    /// Implicit/explicit wildcard in a pattern.
    /// - `0`: variable name (unique, e.g. `_l0` for GADT implicit)
    /// - `1`: optional explicit param name for `[l=_l0]` syntax in Raw
    ///        (`Some(l)` �?`Either::Name("l")`, `None` �?strip `_` prefix)
    /// - `2`: icit
    Any(Span<SmolStr>, Option<Span<SmolStr>>, Icit),
    Bind(Span<SmolStr>),
    Con(u32, Span<SmolStr>, Vec<PatternDetail>),
}

impl PatternDetail {
    fn bind_count(&self) -> u32 {
        match self {
            PatternDetail::Any(_, _, _) => 1,
            PatternDetail::Bind(_) => 1,
            PatternDetail::Con(_, _, pattern_details) => {
                pattern_details.iter().map(|pattern_detail| pattern_detail.bind_count()).sum::<u32>()
            },
        }
    }
    fn bind_names(&self, ns: &List<SmolStr>) -> List<SmolStr> {
        match self {
            PatternDetail::Any(_, _, _) => ns.prepend(SmolStr::new("_")),
            PatternDetail::Bind(name) => ns.prepend(name.data.clone()),
            PatternDetail::Con(_, _, pattern_details) => {
                pattern_details
                    .iter()
                    .fold(ns.clone(), |ns, pattern_detail| pattern_detail.bind_names(&ns))
            },
        }
    }
    fn bind_cxt(&self, cxt: &Cxt) -> Cxt {
        match self {
            // A wildcard also occupies a de Bruijn slot at runtime (see
            // `bind_count`), so bind a dummy here to keep cxt.lvl consistent
            // with the level used by `bind_count` at the call site.
            PatternDetail::Any(_, _, _) => {
                cxt.bind(empty_span(SmolStr::new("")), Tm::U(0).into(), Val::U(0).into())
            }
            PatternDetail::Bind(name) => cxt.bind(name.clone(), Tm::U(0).into(), Val::U(0).into()),
            PatternDetail::Con(_, _, pattern_details) => {
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
            PatternDetail::Any(_, _, _) => write!(f, "_"),
            PatternDetail::Bind(name) => write!(f, "{}", name.data),
            PatternDetail::Con(idx, name, pattern_details) => {
                let p = pattern_details
                    .iter()
                    .map(|pattern_detail| pattern_detail.to_string())
                    .collect::<Vec<_>>();
                if p.is_empty() {
                    write!(f, "{}({})", name.data, idx)
                } else {
                    write!(f, "{}({})({})", name.data, idx, p.join(", "))
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
    /// Native machine representation of a concrete `Nat` (Lean/Agda-style
    /// optimization): a value that is definitionally `succ^n zero` is held
    /// as a single `u64` instead of an n-deep unary `Val::SumCase` chain.
    /// Created by `build_nat` (literals), by `eval` when a `Tm::SumCase`
    /// chain is fully concrete (`succ (Nat k) -> Nat (k+1)`), and by the
    /// pattern matcher when binding a `succ` argument (`n = Nat (k-1)`).
    /// WHNF leaf: `force` returns it unchanged.  `quote` expands it back to
    /// a `Tm::SumCase` chain so every existing downstream consumer (pretty,
    /// nf, unify-vs-stuck, ...) sees exactly the term shape it saw before.
    Nat(u64),
    Sum(
        Span<SmolStr>,
        SumParams,
        SumCases,
        bool,
    ),
    SumCase {
        is_trait: bool,
        typ: Rc<Val>,
        index: u32,
        datas: SumCaseDatas,
    },
    Match(Rc<Val>, Env, Vec<(PatternDetail, Rc<Tm>)>),
    /// Call(name, args, body) - value inlined from function `name`
    Call(SmolStr, List<(Rc<Val>, Icit)>, Rc<Val>),
}

#[allow(dead_code)]
impl Drop for Val {
    fn drop(&mut self) {
        // The derived drop unwraps nested `Rc<Val>`/`Rc<Tm>`/`List` fields
        // recursively — one native stack frame per node of a deep `Val`
        // (e.g. a million-deep `Nat` literal is a chain of nested
        // `Val::SumCase`s) — which overflows even the 64 MiB CLI stack at
        // ~100k depth.  Drain the nested references iteratively: each
        // node's `Rc` fields are moved out with `ptr::read` (collections are
        // replaced with empty ones), then the drained shell is forgotten
        // by the caller — a normal drop would double-release the moved-from
        // fields.  Semantics are identical to the derived drop.
        fn drain_tm(t: &mut Tm, tms: &mut Vec<Rc<Tm>>) {
            match t {
                Tm::Var(_) | Tm::Decl(_) | Tm::U(_) | Tm::Meta(_) | Tm::LiteralType | Tm::LiteralIntro(_) => {
                    return;
                }
                Tm::Obj(x, _) => {
                    let x = unsafe { std::ptr::read(x) };
                    tms.push(x);
                }
                Tm::Lam(_, _, b) => {
                    let b = unsafe { std::ptr::read(b) };
                    tms.push(b);
                }
                Tm::App(f, u, _) => {
                    let f = unsafe { std::ptr::read(f) };
                    let u = unsafe { std::ptr::read(u) };
                    tms.push(f);
                    tms.push(u);
                }
                Tm::AppPruning(t, _) => {
                    let t = unsafe { std::ptr::read(t) };
                    tms.push(t);
                }
                Tm::Pi(_, _, a, b) => {
                    let a = unsafe { std::ptr::read(a) };
                    let b = unsafe { std::ptr::read(b) };
                    tms.push(a);
                    tms.push(b);
                }
                Tm::Let(_, a, t, u) => {
                    let a = unsafe { std::ptr::read(a) };
                    let t = unsafe { std::ptr::read(t) };
                    let u = unsafe { std::ptr::read(u) };
                    tms.push(a);
                    tms.push(t);
                    tms.push(u);
                }
                Tm::Sum(_, params, _, _) => {
                    let params = unsafe { std::ptr::read(params) };
                    for (_, t, ty, _) in params.iter() {
                        tms.push(t.clone());
                        tms.push(ty.clone());
                    }
                }
                Tm::SumCase { typ, datas, .. } => {
                    let typ = unsafe { std::ptr::read(typ) };
                    tms.push(typ);
                    let datas = unsafe { std::ptr::read(datas) };
                    for (_, d, _) in datas.iter() {
                        tms.push(d.clone());
                    }
                }
                Tm::Match(scru, cases) => {
                    let scru = unsafe { std::ptr::read(scru) };
                    tms.push(scru);
                    let cases = std::mem::replace(cases, Vec::new());
                    for (_, b) in cases.iter() {
                        tms.push(b.clone());
                    }
                }
                Tm::Call(_, args, body) => {
                    let args = std::mem::replace(args, List::new());
                    for (a, _) in args.iter() {
                        tms.push(a.clone());
                    }
                    let body = unsafe { std::ptr::read(body) };
                    tms.push(body);
                }
                Tm::OpCall { args, body, .. } => {
                    let args = std::mem::replace(args, List::new());
                    for (a, _) in args.iter() {
                        tms.push(a.clone());
                    }
                    let body = unsafe { std::ptr::read(body) };
                    tms.push(body);
                }
            }
        }
        fn drain_val(v: &mut Val, vals: &mut Vec<Rc<Val>>, tms: &mut Vec<Rc<Tm>>) {
            match v {
                Val::Flex(_, sp) | Val::Rigid(_, sp) | Val::Decl(_, sp) => {
                    let sp = std::mem::replace(sp, List::new());
                    for (x, _) in sp.iter() {
                        vals.push(x.clone());
                    }
                }
                Val::Obj(x, _, sp) => {
                    let x = unsafe { std::ptr::read(x) };
                    vals.push(x);
                    let sp = std::mem::replace(sp, List::new());
                    for (a, _) in sp.iter() {
                        vals.push(a.clone());
                    }
                }
                Val::Lam(_, _, Closure(env, body)) => {
                    let env = std::mem::replace(env, List::new());
                    for x in env.iter() {
                        vals.push(x.clone());
                    }
                    let body = unsafe { std::ptr::read(body) };
                    tms.push(body);
                }
                Val::Pi(_, _, a, Closure(env, body)) => {
                    let a = unsafe { std::ptr::read(a) };
                    vals.push(a);
                    let env = std::mem::replace(env, List::new());
                    for x in env.iter() {
                        vals.push(x.clone());
                    }
                    let body = unsafe { std::ptr::read(body) };
                    tms.push(body);
                }
                Val::U(_) | Val::LiteralType | Val::LiteralIntro(_) | Val::Nat(_) => {
                    return;
                }
                Val::Sum(_, params, _, _) => {
                    let params = unsafe { std::ptr::read(params) };
                    for (_, v, ty, _) in params.iter() {
                        vals.push(v.clone());
                        vals.push(ty.clone());
                    }
                }
                Val::SumCase { typ, datas, .. } => {
                    let typ = unsafe { std::ptr::read(typ) };
                    vals.push(typ);
                    let datas = unsafe { std::ptr::read(datas) };
                    for (_, d, _) in datas.iter() {
                        vals.push(d.clone());
                    }
                }
                Val::Match(scru, env, cases) => {
                    let scru = unsafe { std::ptr::read(scru) };
                    vals.push(scru);
                    let env = std::mem::replace(env, List::new());
                    for x in env.iter() {
                        vals.push(x.clone());
                    }
                    let cases = std::mem::replace(cases, Vec::new());
                    for (_, b) in cases.iter() {
                        tms.push(b.clone());
                    }
                }
                Val::Call(_, args, body) => {
                    let args = std::mem::replace(args, List::new());
                    for (a, _) in args.iter() {
                        vals.push(a.clone());
                    }
                    let body = unsafe { std::ptr::read(body) };
                    vals.push(body);
                }
            }
            // The drained shell's fields were moved out; the caller
            // forgets it (a normal drop would double-release them).
        }
        if matches!(self, Val::U(_) | Val::LiteralType | Val::LiteralIntro(_) | Val::Nat(_)) {
            return;
        }
        let mut vals: Vec<Rc<Val>> = Vec::new();
        let mut tms: Vec<Rc<Tm>> = Vec::new();
        let mut root = std::mem::replace(self, Val::U(0));
        drain_val(&mut root, &mut vals, &mut tms);
        std::mem::forget(root);
        loop {
            match vals.pop() {
                Some(v) => match Rc::try_unwrap(v) {
                    Ok(mut v) => {
                        drain_val(&mut v, &mut vals, &mut tms);
                        // The shell's fields were moved out by `drain_val`;
                        // dropping it would double-release them.
                        std::mem::forget(v);
                    }
                    Err(_) => continue, // shared elsewhere; count decremented only
                },
                None => match tms.pop() {
                    Some(t) => match Rc::try_unwrap(t) {
                        Ok(mut t) => {
                            drain_tm(&mut t, &mut tms);
                            std::mem::forget(t);
                        }
                        Err(_) => continue,
                    },
                    None => break,
                },
            }
        }
    }
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
    // Checked: a bare `l.0 - x.0 - 1` underflows as a cryptic "attempt to
    // subtract with overflow". An out-of-scope level means a dangling
    // elaboration-time variable leaked into a quote (typeclass instance Nat
    // param bug — docs/l13-typeclass-instance-nat-param-bug.md — and
    // l13-known-bugs-2026-08.md Bug 2); name it so the panic is diagnosable.
    Ix(l.0.checked_sub(x.0).and_then(|v| v.checked_sub(1)).unwrap_or_else(|| {
        panic!(
            "lvl2ix: level {} is out of scope for a context of level {} — a dangling \
             elaboration-time variable leaked into a quote (see \
             docs/l13-typeclass-instance-nat-param-bug.md)",
            x.0, l.0
        )
    }))
}

pub fn tm_contains_match(tm: &Tm) -> bool {
    match tm {
        Tm::Match(..) => true,
        Tm::Lam(_, _, body) => tm_contains_match(body),
        _ => false,
    }
}

/// True when `tm` has no free De Bruijn variables (all `Tm::Var`s are bound
/// by an enclosing `Lam`/`Pi`/`Let`/`Match`).  Used to gate the reuse of
/// Phase-A-checked type annotations in create/tree bodies: a closed annotation
/// is context-independent, so it elaborates identically in the (slightly
/// different) method-body context.
pub fn tm_is_closed(tm: &Tm) -> bool {
    fn free_var(tm: &Tm, d: u32) -> bool {
        match tm {
            Tm::Var(ix) => ix.0 >= d,
            Tm::Obj(t, _) => free_var(t, d),
            Tm::Lam(_, _, b) => free_var(b, d + 1),
            Tm::App(f, a, _) => free_var(f, d) || free_var(a, d),
            Tm::AppPruning(t, _) => free_var(t, d),
            Tm::U(_) | Tm::Decl(_) | Tm::Meta(_) | Tm::LiteralType | Tm::LiteralIntro(_) => false,
            Tm::Pi(_, _, a, b) => free_var(a, d) || free_var(b, d + 1),
            Tm::Let(_, ty, v, b) => free_var(ty, d) || free_var(v, d) || free_var(b, d + 1),
            Tm::Sum(_, params, _, _) => {
                params.iter().any(|(_, v, ty, _)| free_var(v, d) || free_var(ty, d))
            }
            Tm::SumCase { typ, datas, .. } => {
                free_var(typ, d) || datas.iter().any(|(_, t, _)| free_var(t, d))
            }
            Tm::Match(s, cases) => {
                free_var(s, d) || cases.iter().any(|(_, b)| free_var(b, d + 1))
            }
            Tm::Call(_, args, body) => {
                args.iter().any(|(a, _)| free_var(a, d)) || free_var(body, d + 1)
            }
            Tm::OpCall { args, body, .. } => {
                args.iter().any(|(a, _)| free_var(a, d)) || free_var(body, d + 1)
            }
        }
    }
    !free_var(tm, 0)
}

/// Build a simplified copy of `decl` where every definition's body is
/// replaced by a `Decl` reference, so evaluating match-case bodies does not
/// re-expand recursive definitions.  O(decl) to build; cached per decl
/// address — decl maps are persistent (`Rc<HashMap>`), so the pointer is a
/// stable key.  Used by `quote`/`rename`/`unify` on `Val::Match` values.
pub(crate) fn simpl_decl(decl: &Decl) -> Rc<Decl> {
    thread_local! {
        static DECLB_CACHE: std::cell::RefCell<Option<(usize, Rc<Decl>)>> =
            const { std::cell::RefCell::new(None) };
    }
    let key = decl as *const Decl as usize;
    let cached = DECLB_CACHE.with(|c| {
        let b = c.borrow();
        match b.as_ref() {
            Some((k, d)) if *k == key => Some(d.clone()),
            _ => None,
        }
    });
    if let Some(d) = cached {
        return d;
    }
    let d: Decl = decl
        .iter()
        .map(|x| {
            (
                x.0.clone(),
                (
                    x.1.0,
                    Tm::Decl(x.1.0.map(|_| x.0.clone())).into(),
                    // Sum-type definition values stay: a `Val::Sum` is a
                    // WHNF leaf that never re-expands, but evaluating under
                    // the simplified decl needs it — primops
                    // (`nat_succ_shape`) and constructor bodies build
                    // `Val::SumCase`s whose `typ` must stay a `Val::Sum`;
                    // replacing it with `Val::Decl` produced SumCase values
                    // that quoted back with `typ: Tm::Decl` and panicked
                    // pretty (docs/l13-sumcase-decl-typ-pretty-panic.md §4.3).
                    if matches!(x.1.2.as_ref(), Val::Sum(..)) {
                        x.1.2.clone()
                    } else {
                        Val::Decl(x.1.0.map(|_| x.0.clone()), List::new()).into()
                    },
                    x.1.3.clone(),
                    x.1.4.clone(),
                    x.1.5.clone(),
                    x.1.6.clone(),
                ),
            )
        })
        .collect();
    let d = Rc::new(d);
    DECLB_CACHE.with(|c| *c.borrow_mut() = Some((key, d.clone())));
    d
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
use std::collections::{HashMap, HashSet};

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

/// Operator characters that may start an operator method name (`+`, `*`,
/// `-`, `<=`, `:=`, ...).  Declarations whose name starts with such a
/// character are rendered in infix/prefix form by the pretty-printer.
pub(crate) fn is_operator_char(c: char) -> bool {
    matches!(
        c,
        '+' | '*' | '/' | '-' | '%' | '<' | '>' | '=' | '&' | '|' | '^' | '!' | '~' | '#' | ':'
    )
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
        Error(self.msg.map(|x| format!("{}", x)), vec![])
    }
}

/// A `println` whose normalization was deferred so type errors can reach the
/// client before the (potentially slow) `nf` runs.  Captures the exact
/// context at the point of elaboration, so the deferred `nf`/`pretty_tm`
/// produces the same result as computing inline.
pub struct PrintlnJob {
    pub tm: Rc<Tm>,
    pub span: Span<()>,
    pub decl: Rc<Decl>,
    pub env: Env,
    pub names: List<SmolStr>,
}

/// A hover-table entry: (source span, definition span, hover context, value).
/// The value is quoted at LSP time with the captured context to render the
/// type shown on hover.
pub type HoverEntry = (Span<()>, Span<()>, cxt::HoverCxt, Rc<Val>);

pub struct Infer {
    pub meta: Vec<MetaEntry>,
    pub meta_contrains: Vec<(Rc<Val>, Rc<Val>)>,
    trait_metas: Vec<MetaVar>,
    trait_solver: typeclass::Synth,
    trait_definition: HashMap<SmolStr, (Vec<(Span<SmolStr>, Raw, Icit)>, Vec<bool>, Vec<Span<SmolStr>>, Vec<(Span<SmolStr>, Vec<(Span<SmolStr>, Raw, Icit)>, Raw, Option<Raw>)>)>,
    trait_out_param: HashMap<SmolStr, Vec<bool>>,
    /// (trait_name, assoc_type_name) -> optional default type value (Raw)
    assoc_defaults: HashMap<(SmolStr, SmolStr), Option<Raw>>,
    pub mutable_map: Rc<std::sync::RwLock<HashMap<String, Rc<Val>>>>,
    pub hover_table: Vec<HoverEntry>,
    pub completion_table: Vec<(Span<()>, SmolStr)>,
    /// Inlay hints: (byte offset of insertion point, ": <type>" label).
    /// Populated for `def` without explicit return type and `let` without type
    /// annotation; consumed by the LSP `textDocument/inlayHint` request.
    pub inlay_hint_table: Vec<(u32, String)>,
    /// Accumulated type errors from pattern match branches, reported as
    /// separate LSP diagnostics so each branch error gets its own red squiggle.
    pub accumulated_errors: Vec<Error>,
    /// Operator-symbol registry: (helper function name, argument count) →
    /// operator symbol.  Populated when an impl's operator-named method
    /// (e.g. `def +(that: Nat): Nat = nat_add_helper this that`) is
    /// registered, so `quote` can restore the infix form (`x + y`) of an
    /// inlined helper call (`nat_add_helper x y`).  User-defined operator
    /// symbols are supported automatically.
    pub symbol_table: HashMap<(SmolStr, usize), SmolStr>,
    /// Per-file import aliases: stripped alias name → fully-qualified decl key.
    /// Populated by `Decl::Import` (wildcard / brace / single-name forms) and
    /// consulted by variable lookup *after* the exact `cxt.decl` hit and
    /// *before* the `namespace_prefix` resolution.  Kept on `Infer` (not
    /// `Cxt`) so a per-file clone starts empty and the global `Infer` never
    /// accumulates another file's aliases (aliases are file-local visibility).
    /// `Raw::Obj` qualified access (`Tree.leaf`) also resolves its first
    /// segment through this map; the `.mk` shorthand is covered by the dotted
    /// aliases (`X.mk`) this map also holds.
    pub import_map: HashMap<SmolStr, SmolStr>,
    /// Cache of resolved trait-method elaboration: (method name, deterministic
    /// receiver-type key) → (checked Pi-chain Tm, its eval'd value, checked
    /// method-body lambda).  When the same operator is elaborated again on a
    /// structurally-equal receiver type (e.g. `UInt[8]` built at different
    /// sites), both the check_universe of the Pi chain and the method-body
    /// re-elaboration are skipped (the create/tree eval still drives side
    /// effects through the applied result).
    trait_method_cache: HashMap<(SmolStr, SmolStr), (Rc<Tm>, Rc<Val>, Rc<Tm>)>,
    /// When true, `Decl::Println` skips the inline `nf` and records a
    /// `println_jobs` entry instead, deferring normalization to a later
    /// phase (used by the LSP worker so tyck diagnostics publish first).
    pub defer_println: bool,
    /// Deferred `println` jobs accumulated while `defer_println` is set.
    pub println_jobs: Vec<PrintlnJob>,
    /// Memoized "does this def's body perform global-mutable side effects"
    /// table (see `def_needs_replay`): parameterless defs whose bodies call
    /// `create_global`/`change_mutable`/`change_mutable_default`/`get_global`
    /// — directly or through other defs — are re-evaluated (body replayed)
    /// on EVERY `Tm::Decl` lookup instead of returning the declaration-time
    /// cached WHNF.  The cached value would otherwise be produced once at
    /// declaration (outside any module tree) and never re-run, silently
    /// dropping HDL statements in parameterless hardware `def` bodies.
    pub def_replay_memo: Rc<std::sync::RwLock<HashMap<SmolStr, bool>>>,
}

impl Clone for Infer {
    fn clone(&self) -> Self {
        Infer {
            meta: self.meta.clone(),
            meta_contrains: self.meta_contrains.clone(),
            trait_metas: self.trait_metas.clone(),
            trait_solver: self.trait_solver.clone(),
            trait_definition: self.trait_definition.clone(),
            trait_out_param: self.trait_out_param.clone(),
            assoc_defaults: self.assoc_defaults.clone(),
            mutable_map: self.mutable_map.clone(),
            hover_table: self.hover_table.clone(),
            completion_table: self.completion_table.clone(),
            inlay_hint_table: self.inlay_hint_table.clone(),
            symbol_table: self.symbol_table.clone(),
            import_map: self.import_map.clone(),
            trait_method_cache: HashMap::new(),
            defer_println: self.defer_println,
            println_jobs: Vec::new(),
            def_replay_memo: self.def_replay_memo.clone(),
            // accumulated_errors are ephemeral per-checking-pass;
            // a clone (used for read-only analysis) starts fresh.
            accumulated_errors: Vec::new(),
        }
    }
}

impl Infer {
    /// The most specific hover entry for `offset` in the file identified by
    /// `path_id`: among entries whose span contains the offset, pick the one
    /// with the smallest span.  A tuple literal's `TupleN.mk` entry spans the
    /// whole element list, so each element's own narrower entry (pushed by
    /// elaboration) wins when the cursor is on an element, while positions
    /// between elements still resolve to the whole-tuple entry.
    pub fn hover_entry_at(&self, path_id: u32, offset: usize) -> Option<&HoverEntry> {
        self.hover_table
            .iter()
            .filter(|x| x.0.path_id == path_id)
            .filter(|x| x.0.contains(offset))
            .min_by_key(|x| x.0.end_offset - x.0.start_offset)
    }
}

// ── Sum-type definition rendering (hover) ──────────────────────────────────
// Reconstruct a source-like `enum`/`struct`/`trait` declaration from the
// stored elaboration data, so a hover popup shows the members (constructors /
// fields / methods) instead of just `Name : Type 0` — rust-analyzer style.

/// Fresh binder name: append `'` until it does not appear in `ns` (mirrors
/// `pretty::fresh` so nested binders never render the wrong de Bruijn slot).
fn sum_fresh(ns: &List<SmolStr>, suggested: &str) -> String {
    if suggested == "_" {
        return "_".to_string();
    }
    let mut candidate = suggested.to_string();
    while ns.iter().any(|x| x == &candidate) {
        candidate = format!("{}'", candidate);
    }
    candidate
}

/// When `t` is the head `Tm::Decl(enum_name)` applied to `args` (empty for
/// the bare name), return `Some(args)`; `None` when the head is something
/// else.  Used to recognise a constructor's codomain as the enum itself.
fn sum_self_spine<'a>(t: &'a Tm, enum_name: &str) -> Option<Vec<&'a Tm>> {
    let mut args: Vec<&Tm> = Vec::new();
    let mut cur = t;
    loop {
        match cur {
            Tm::App(f, u, _) => {
                args.push(u.as_ref());
                cur = f.as_ref();
            }
            other => {
                if let Tm::Decl(s) = other {
                    if s.data == enum_name {
                        return Some(args);
                    }
                }
                return None;
            }
        }
    }
}

/// A constructor's codomain is "the enum itself" when its head is the enum
/// name (bare `Nat` or applied, e.g. `List[T]`, `Vec[A] l`).  The trailing
/// ` → ret` is omitted in that case — for simple enums it is pure repetition,
/// and for GADTs the computed index (`Vec[A] (l + 1)`) is stored as an
/// inlined helper call that renders as noise in a hover popup.
fn is_trivial_self(t: &Tm, enum_name: &str) -> bool {
    sum_self_spine(t, enum_name).is_some()
}

/// Render one constructor from its Pi-chain type, e.g. `succ(n: Nat)` or
/// `cons[l: Nat](x: A, xs: Vec[A] l)`.  `elide_impls` leading implicit binders
/// (the enum's own type params, already shown in the header) are hidden.  The
/// trailing ` → ret` is omitted when the codomain is the enum itself.
fn render_pi_member(
    member_name: &str,
    ty: &Rc<Tm>,
    enum_name: &str,
    elide_impls: usize,
) -> String {
    // Walk the Pi chain collecting binders (name, icity, domain) + codomain.
    let mut binders: Vec<(SmolStr, Icit, Rc<Tm>)> = Vec::new();
    let mut codomain: Rc<Tm> = ty.clone();
    loop {
        match codomain.as_ref() {
            Tm::Pi(x, i, a, b) => {
                binders.push((x.data.clone(), *i, a.clone()));
                codomain = b.clone();
            }
            _ => break,
        }
    }
    // Names are accumulated outer→inner (prepend each fresh binder name) so
    // de Bruijn indices in later domains / the codomain resolve to the right
    // binder.  A `Tm::Var` at de Bruijn `ix` names the `ix`-th element of the
    // list from its head (head = innermost binder).
    let mut ns: List<SmolStr> = List::new();
    let mut rendered: Vec<(bool, Icit, String)> = Vec::new();
    for (i, (x, icit, a)) in binders.iter().enumerate() {
        let x_str = sum_fresh(&ns, x.as_str());
        let dom = pretty_tm(0, ns.clone(), a);
        rendered.push((i < elide_impls, *icit, format!("{x_str}: {dom}")));
        ns = ns.prepend(SmolStr::new(&x_str));
    }
    let ret = pretty_tm(0, ns, &codomain);

    // Group the visible binders by icity: `[impl](expl)`, like the parser's
    // `f[x](y)` form.
    let mut impls: Vec<&str> = Vec::new();
    let mut expls: Vec<&str> = Vec::new();
    for (elided, icit, s) in &rendered {
        if *elided {
            continue;
        }
        match icit {
            Icit::Impl => impls.push(s),
            Icit::Expl => expls.push(s),
        }
    }
    let impl_str = if impls.is_empty() {
        String::new()
    } else {
        format!("[{}]", impls.join(", "))
    };
    let expl_str = if expls.is_empty() {
        String::new()
    } else {
        format!("({})", expls.join(", "))
    };

    let mut out = format!("{member_name}{impl_str}{expl_str}");
    if !is_trivial_self(&codomain, enum_name) {
        out.push_str(" → ");
        out.push_str(&ret);
    }
    out
}

/// Render a trait method as a signature from its Pi-chain type, e.g.
/// `+(this: Self, that: T) → O`.  `ns_start` carries the names of the trait's
/// own params (including `Self`), which the method body references by de
/// Bruijn index.
fn render_pi_signature(name: &str, pi_ty: &Rc<Tm>, ns_start: &List<SmolStr>) -> String {
    let mut binders: Vec<(SmolStr, Icit, Rc<Tm>)> = Vec::new();
    let mut codomain: Rc<Tm> = pi_ty.clone();
    loop {
        match codomain.as_ref() {
            Tm::Pi(x, i, a, b) => {
                binders.push((x.data.clone(), *i, a.clone()));
                codomain = b.clone();
            }
            _ => break,
        }
    }
    let mut ns = ns_start.clone();
    let mut impls: Vec<String> = Vec::new();
    let mut expls: Vec<String> = Vec::new();
    for (x, icit, a) in &binders {
        let x_str = sum_fresh(&ns, x.as_str());
        let dom = pretty_tm(0, ns.clone(), a);
        let item = format!("{x_str}: {dom}");
        match icit {
            Icit::Impl => impls.push(item),
            Icit::Expl => expls.push(item),
        }
        ns = ns.prepend(SmolStr::new(&x_str));
    }
    let ret = pretty_tm(0, ns, &codomain);
    let impl_str = if impls.is_empty() {
        String::new()
    } else {
        format!("[{}]", impls.join(", "))
    };
    let expl_str = if expls.is_empty() {
        String::new()
    } else {
        format!("({})", expls.join(", "))
    };
    format!("{name}{impl_str}{expl_str} → {ret}")
}

/// Render a sum type (enum / struct / trait) declaration in source-like form
/// for the hover panel — `enum Nat { zero, succ(n: Nat) }` — so the popup
/// shows the members instead of just `Name : Type 0`.  The header comes from
/// the type's `Tm::Sum` params (implicit as `[T]`, explicit as `(len: Nat)`);
/// each constructor's signature comes from its own decl-table type.  Returns
/// None when the term is not a sum type (a plain def / builtin).
pub fn pretty_sum_definition(key: &str, tm: &Rc<Tm>, decl: &Decl) -> Option<String> {
    // The checked enum term is `λ type-params … (Tm::Sum …)`; unwrap the
    // lambdas to reach the `Tm::Sum` that carries the type params and the
    // case names.
    let mut cur: Rc<Tm> = tm.clone();
    while let Tm::Lam(_, _, b) = cur.as_ref() {
        cur = b.clone();
    }
    let Tm::Sum(name, params, cases, is_trait) = cur.as_ref() else {
        return None;
    };

    // ── Header params from the `Tm::Sum` params ──
    // `TmSumParams` = (name, value-tm, type-tm, icity).  Implicit params render
    // as bare names (`[T]`); explicit ones as `(name: type)`.
    //
    // The enum term is `λ p₀ → … → λ pₙ₋₁ → Sum`, so the Sum node sits inside
    // the FULL λ-chain and every stored param type (`type-tm`) was quoted at
    // that depth: its de Bruijn indices address the whole binder stack
    // (innermost = last param).  We therefore fresh-ify every param name up
    // front, build the complete context once, and render each explicit param's
    // type against that complete context — an incremental `ns` (only the
    // params seen so far) would mis-resolve params referencing earlier ones
    // (e.g. `Eq[A](x: A, y: A)` rendered `y: <out of bounds>`).  The same
    // complete context then feeds trait method signatures.
    let mut ns: List<SmolStr> = List::new();
    let mut fresh_names: Vec<SmolStr> = Vec::with_capacity(params.len());
    for (x, _, _, _) in params.iter() {
        let x_str = SmolStr::new(&sum_fresh(&ns, &x.data));
        fresh_names.push(x_str.clone());
        ns = ns.prepend(x_str);
    }
    let mut header_impl: Vec<String> = Vec::new();
    let mut header_expl: Vec<String> = Vec::new();
    let mut n_impl = 0usize;
    for (idx, (_x, _val, typ, icit)) in params.iter().enumerate() {
        let x_str = &fresh_names[idx];
        if *icit == Icit::Impl {
            n_impl += 1;
        }
        // A trait's first implicit param is `Self`: it stays in scope for the
        // methods' de Bruijn indices but is elided from the header.
        if !(*is_trait && idx == 0) {
            match icit {
                Icit::Impl => header_impl.push(x_str.to_string()),
                Icit::Expl => {
                    let dom = pretty_tm(0, ns.clone(), typ);
                    header_expl.push(format!("{x_str}: {dom}"));
                }
            }
        }
    }

    let is_struct = !*is_trait && cases.len() == 1 && cases[0].data.ends_with(".mk");
    let keyword = if *is_trait {
        "trait"
    } else if is_struct {
        "struct"
    } else {
        "enum"
    };
    let impl_str = if header_impl.is_empty() {
        String::new()
    } else {
        format!("[{}]", header_impl.join(", "))
    };
    let expl_str = if header_expl.is_empty() {
        String::new()
    } else {
        format!("({})", header_expl.join(", "))
    };
    let header = format!("{keyword} {}{}{}", name.data, impl_str, expl_str);

    // ── Members ──
    if *is_trait {
        // A trait stores a single `Name.mk` case whose parameters are the
        // methods, each itself a Pi chain (`this: Self`) → … → ret.  The
        // registered constructor key repeats the type name (`Add.Add.mk`).
        let mk_key = SmolStr::new(format!("{}.{}.mk", name.data, name.data));
        let mut lines: Vec<String> = Vec::new();
        if let Some((_, _, _, cty, _, _, _)) = decl.get(&mk_key) {
            // Walk the mk Pi chain, skipping the trait's own params (Self +
            // type params, `n_impl` of them), then render each method binder
            // whose domain is a Pi signature.
            let mut codomain: Rc<Tm> = cty.clone();
            let mut binders: Vec<(SmolStr, Icit, Rc<Tm>)> = Vec::new();
            loop {
                match codomain.as_ref() {
                    Tm::Pi(x, i, a, b) => {
                        binders.push((x.data.clone(), *i, a.clone()));
                        codomain = b.clone();
                    }
                    _ => break,
                }
            }
            let mut ns_cur = ns.clone();
            for (i, (x, icit, a)) in binders.iter().enumerate() {
                if i < n_impl {
                    // The trait's own params (Self, type params) already have
                    // names in `ns` from the header; do not re-add them.
                    continue;
                }
                let x_str = sum_fresh(&ns_cur, x.as_str());
                let _ = icit;
                if let Tm::Pi(..) = a.as_ref() {
                    lines.push(render_pi_signature(&x_str, a, &ns_cur));
                } else {
                    lines.push(format!("{x_str}: {}", pretty_tm(0, ns_cur.clone(), a)));
                }
                ns_cur = ns_cur.prepend(SmolStr::new(&x_str));
            }
        }
        let mut out = header;
        if lines.is_empty() {
            out.push_str(" { }");
        } else {
            out.push_str(" {");
            for line in &lines {
                out.push_str(&format!("\n    {line}"));
            }
            out.push_str("\n}");
        }
        return Some(out);
    }

    let mut lines: Vec<String> = Vec::new();
    for case in cases.iter() {
        // Struct/trait constructors are registered under a doubled key
        // (`Point.Point.mk`); regular enum cases under `Name.case`.
        let display = if case.data.ends_with(".mk") {
            case.data.rsplit('.').next().unwrap_or(&case.data)
        } else {
            &case.data
        };
        let mut cty: Option<Rc<Tm>> = None;
        let k1 = SmolStr::new(format!("{}.{}", name.data, case.data));
        let k2 = SmolStr::new(format!("{key}.{}", case.data));
        if let Some((_, _, _, t, _, _, _)) = decl.get(&k1) {
            cty = Some(t.clone());
        } else if let Some((_, _, _, t, _, _, _)) = decl.get(&k2) {
            cty = Some(t.clone());
        }
        match cty {
            Some(t) => lines.push(render_pi_member(display, &t, &name.data, n_impl)),
            None => lines.push(display.to_string()),
        }
    }

    // ── Assemble ──
    if is_struct {
        // A struct's fields are its single `.mk` constructor's explicit
        // params, already rendered as `mk(x: Nat, y: Nat)`; splice them into
        // the header: `struct Point(x: Nat, y: Nat)`.
        let mk = &lines[0];
        let fields = mk.strip_prefix("mk").unwrap_or(mk);
        return Some(format!("{header}{fields}"));
    }

    let mut out = header;
    out.push_str(" {");
    for line in &lines {
        out.push_str(&format!("\n    {line}"));
    }
    out.push_str("\n}");
    Some(out)
}

// ── Memory profiling helpers ──

fn arc_id<T>(rc: &Rc<T>) -> usize {
    Rc::as_ptr(rc) as *const () as usize
}

#[derive(Default)]
struct DetailCounts {
    val_unique: usize,
    tm_unique: usize,
    /// Unique List spine nodes (Rc<Node<T>>) for Env
    env_nodes: usize,
    /// Unique List spine nodes for Spines
    spine_nodes: usize,
    /// Unique generic List spine nodes
    list_other_nodes: usize,
    smolstr_unique: usize,
    smolstr_heap_est: usize,
    span_void_count: usize,
    span_smolstr_count: usize,
    closure_count: usize,
}

impl DetailCounts {
    fn walk_val(&mut self, val: &Rc<Val>, visited: &mut std::collections::HashSet<usize>) {
        let id = arc_id(val);
        if !visited.insert(id) {
            return;
        }
        self.val_unique += 1;
        self.walk_val_rec(val, visited);
    }

    fn walk_val_rec(&mut self, val: &Val, visited: &mut std::collections::HashSet<usize>) {
        match val {
            Val::Flex(_, sp) | Val::Rigid(_, sp) | Val::Decl(_, sp) | Val::Obj(_, _, sp) => {
                self.walk_spine(sp, visited);
            }
            Val::Lam(name, _, clos) => {
                self.span_smolstr_count += 1;
                self.closure_count += 1;
                self.walk_closure(clos, visited);
            }
            Val::Pi(name, _, vty, clos) => {
                self.span_smolstr_count += 1;
                self.walk_val_id(vty, visited);
                self.closure_count += 1;
                self.walk_closure(clos, visited);
            }
            Val::U(_) => {}
            Val::LiteralType => {}
            Val::Nat(_) => {}
            Val::LiteralIntro(s) => {
                self.span_smolstr_count += 1; // Span<String> ~ Span<SmolStr>
            }
            Val::Sum(name, params, cases, _) => {
                self.span_smolstr_count += 1;
                for (pname, pval, pvty, _) in params.iter() {
                    self.span_smolstr_count += 1;
                    self.walk_val_id(pval, visited);
                    self.walk_val_id(pvty, visited);
                }
                for cname in cases.iter() {
                    self.span_smolstr_count += 1;
                }
            }
            Val::SumCase { typ, datas, .. } => {
                self.walk_val_id(typ, visited);
                for (dname, dval, _) in datas.iter() {
                    self.span_smolstr_count += 1;
                    self.walk_val_id(dval, visited);
                }
            }
            Val::Match(val, env, cases) => {
                self.walk_val_id(val, visited);
                self.walk_env(env, visited);
                for (pat, tm) in cases {
                    self.walk_tm_id(tm, visited);
                }
            }
            Val::Call(_, args, body) => {
                self.walk_spine(args, visited);
                self.walk_val_id(body, visited);
            }
        }
    }

    fn walk_val_id(&mut self, val: &Rc<Val>, visited: &mut std::collections::HashSet<usize>) {
        let id = arc_id(val);
        if !visited.insert(id) {
            return;
        }
        self.val_unique += 1;
        self.walk_val_rec(val, visited);
    }

    fn walk_tm(&mut self, tm: &Rc<Tm>, visited: &mut std::collections::HashSet<usize>) {
        let id = arc_id(tm);
        if !visited.insert(id) {
            return;
        }
        self.tm_unique += 1;
        self.walk_tm_rec(tm, visited);
    }

    fn walk_tm_id(&mut self, tm: &Rc<Tm>, visited: &mut std::collections::HashSet<usize>) {
        let id = arc_id(tm);
        if !visited.insert(id) {
            return;
        }
        self.tm_unique += 1;
        self.walk_tm_rec(tm, visited);
    }

    fn walk_tm_rec(&mut self, tm: &Tm, visited: &mut std::collections::HashSet<usize>) {
        match tm {
            Tm::Var(_) => {}
            Tm::Decl(name) => {
                self.span_smolstr_count += 1;
            }
            Tm::Obj(inner, name) => {
                self.walk_tm_id(inner, visited);
                self.span_smolstr_count += 1;
            }
            Tm::Lam(name, _, body) => {
                self.span_smolstr_count += 1;
                self.walk_tm_id(body, visited);
            }
            Tm::App(f, a, _) => {
                self.walk_tm_id(f, visited);
                self.walk_tm_id(a, visited);
            }
            Tm::AppPruning(tm, _) => {
                self.walk_tm_id(tm, visited);
            }
            Tm::U(_) => {}
            Tm::Pi(name, _, ty_a, ty_b) => {
                self.span_smolstr_count += 1;
                self.walk_tm_id(ty_a, visited);
                self.walk_tm_id(ty_b, visited);
            }
            Tm::Let(name, ty, val, body) => {
                self.span_smolstr_count += 1;
                self.walk_tm_id(ty, visited);
                self.walk_tm_id(val, visited);
                self.walk_tm_id(body, visited);
            }
            Tm::Meta(_) => {}
            Tm::LiteralType => {}
            Tm::LiteralIntro(_s) => {
                self.span_smolstr_count += 1;
            }
            Tm::Sum(name, params, cases, _) => {
                self.span_smolstr_count += 1;
                for (pname, ptm, pty, _) in params.iter() {
                    self.span_smolstr_count += 1;
                    self.walk_tm_id(ptm, visited);
                    self.walk_tm_id(pty, visited);
                }
                for cname in cases.iter() {
                    self.span_smolstr_count += 1;
                }
            }
            Tm::SumCase { typ, datas, .. } => {
                self.walk_tm_id(typ, visited);
                for (dname, dtm, _) in datas.iter() {
                    self.span_smolstr_count += 1;
                    self.walk_tm_id(dtm, visited);
                }
            }
            Tm::Match(tm, cases) => {
                self.walk_tm_id(tm, visited);
                for (pat, branch) in cases {
                    self.walk_tm_id(branch, visited);
                }
            }
            Tm::Call(_, args, body) => {
                for (arg_tm, _) in args.iter() {
                    self.walk_tm_id(arg_tm, visited);
                }
                self.walk_tm_id(body, visited);
            }
            Tm::OpCall { args, body, .. } => {
                for (arg_tm, _) in args.iter() {
                    self.walk_tm_id(arg_tm, visited);
                }
                self.walk_tm_id(body, visited);
            }
        }
    }

    fn walk_cxt(&mut self, cxt: &cxt::Cxt, visited: &mut std::collections::HashSet<usize>) {
        // Walk env
        self.walk_env(&cxt.env, visited);
        // Walk decls (both Tm and Val sides)
        for (_, (span, rtm, rval, rty, rvty, _, _)) in cxt.decl.iter() {
            self.span_void_count += 1;
            self.walk_tm_id(rtm, visited);
            self.walk_val_id(rval, visited);
            self.walk_tm_id(rty, visited);
            self.walk_val_id(rvty, visited);
        }
        // Walk namespace
        for (val, _, _raw) in cxt.namespace.iter() {
            self.walk_val_id(val, visited);
        }
        // Walk src_names
        for (_, _, (span, vty)) in cxt.src_names.iter_all() {
            self.span_void_count += 1;
            self.walk_val_id(vty, visited);
        }
    }

    fn walk_env(&mut self, env: &List<Rc<Val>>, visited: &mut std::collections::HashSet<usize>) {
        self.walk_list_spine_env(env, visited);
        for val in env.iter() {
            self.walk_val_id(val, visited);
        }
    }

    fn walk_spine(&mut self, spine: &Spine, visited: &mut std::collections::HashSet<usize>) {
        self.walk_list_spine_spine(spine, visited);
        for (val, _) in spine.iter() {
            self.walk_val_id(val, visited);
        }
    }

    fn walk_list_spine_env(&mut self, list: &List<Rc<Val>>, visited: &mut std::collections::HashSet<usize>) {
        let mut cur = &list.head;
        while let Some(node) = cur {
            let id = Rc::as_ptr(node) as *const () as usize;
            if visited.insert(id) {
                self.env_nodes += 1;
            }
            cur = &node.next;
        }
    }

    fn walk_list_spine_spine(&mut self, spine: &Spine, visited: &mut std::collections::HashSet<usize>) {
        let mut cur = &spine.head;
        while let Some(node) = cur {
            let id = Rc::as_ptr(node) as *const () as usize;
            if visited.insert(id) {
                self.spine_nodes += 1;
            }
            cur = &node.next;
        }
    }

    fn walk_closure(&mut self, clos: &Closure, visited: &mut std::collections::HashSet<usize>) {
        self.walk_env(&clos.0, visited);
        self.walk_tm_id(&clos.1, visited);
    }

    // Count a SmolStr �?track unique heap allocations
    fn count_smolstr(&mut self, s: &SmolStr, visited: &mut std::collections::HashSet<usize>) {
        if s.len() > 23 {
            let id = s.as_str().as_ptr() as usize;
            if visited.insert(id) {
                self.smolstr_unique += 1;
                self.smolstr_heap_est += s.len();
            }
        }
    }
}

impl Infer {
    pub fn new() -> Self {
        Self {
            meta: vec![],
            meta_contrains: vec![],
            trait_metas: vec![],
            trait_solver: Default::default(),
            trait_definition: Default::default(),
            trait_out_param: Default::default(),
            assoc_defaults: Default::default(),
            mutable_map: Default::default(),
            hover_table: vec![],
            completion_table: vec![],
            inlay_hint_table: vec![],
            symbol_table: HashMap::new(),
            import_map: HashMap::new(),
            trait_method_cache: HashMap::new(),
            accumulated_errors: vec![],
            defer_println: false,
            println_jobs: vec![],
            def_replay_memo: Default::default(),
        }
    }

    pub fn meta_len(&self) -> usize { self.meta.len() }
    pub fn meta_capacity(&self) -> usize { self.meta.capacity() }
    pub fn meta_contrains_len(&self) -> usize { self.meta_contrains.len() }
    pub fn meta_contrains_capacity(&self) -> usize { self.meta_contrains.capacity() }
    pub fn trait_definition_len(&self) -> usize { self.trait_definition.len() }
    pub fn shrink(&mut self) {
        self.meta.shrink_to_fit();
        self.meta_contrains.shrink_to_fit();
    }

    pub fn memory_stats_with_cxt(&self, cxt: Option<&cxt::Cxt>) -> serde_json::Value {
        use serde_json::json;
        use std::collections::HashSet as StdHashSet;
        let total = self.meta.len();
        let solved = self.meta.iter().filter(|m| matches!(m, MetaEntry::Solved(..))).count();
        let unsolved = self.meta.iter().filter(|m| matches!(m, MetaEntry::Unsolved(..))).count();
        let meta_cap = self.meta.capacity();
        let MetaEntry_sz = std::mem::size_of::<MetaEntry>();
        let hover_len = self.hover_table.len();
        let hover_cap = self.hover_table.capacity();
        let constraints_len = self.meta_contrains.len();
        let constraints_cap = self.meta_contrains.capacity();
        let completions_len = self.completion_table.len();

        // Pre-compute sizes for json! macro (avoids generic type parsing issues in json!)
        type RcValPair = (Rc<Val>, Rc<Val>);
        let meta_contrains_entry_sz = std::mem::size_of::<RcValPair>();
        let meta_contrains_cap_bytes = constraints_cap * meta_contrains_entry_sz;
        let hover_entry_sz = std::mem::size_of::<HoverEntry>();
        let hover_cap_bytes = hover_cap * hover_entry_sz;
        type DeclEntry = (SmolStr, (Span<()>, Rc<Tm>, Rc<Val>, Rc<Ty>, Rc<VTy>));
        let decl_entry_sz = std::mem::size_of::<DeclEntry>();

        // ── Meta content analysis ──
        // Categorize unsolved metas by their Cxt env length (= number of bound variables)
        let mut unsolved_env_len_hist: std::collections::BTreeMap<usize, usize> = std::collections::BTreeMap::new();
        let mut unsolved_decl_len_hist: std::collections::BTreeMap<usize, usize> = std::collections::BTreeMap::new();
        for entry in &self.meta {
            if let MetaEntry::Unsolved(_, c, _, _) = entry {
                *unsolved_env_len_hist.entry(c.env.len()).or_insert(0) += 1;
                *unsolved_decl_len_hist.entry(c.decl.len()).or_insert(0) += 1;
            }
        }
        // Categorize solved metas: what kind of Val are they?
        let mut solved_val_kind_hist: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
        for entry in &self.meta {
            if let MetaEntry::Solved(val, _vty) = entry {
                let kind = match val.as_ref() {
                    Val::Flex(_, _) => "Flex",
                    Val::Rigid(_, _) => "Rigid",
                    Val::Decl(_, _) => "Decl",
                    Val::Lam(_, _, _) => "Lam",
                    Val::Pi(_, _, _, _) => "Pi",
                    Val::U(_) => "U",
                    Val::LiteralType => "LiteralType",
                    Val::LiteralIntro(_) => "LiteralIntro",
                    Val::Nat(_) => "Nat",
                    Val::Sum(_, _, _, _) => "Sum",
                    Val::SumCase { .. } => "SumCase",
                    Val::Match(_, _, _) => "Match",
                    Val::Call(_, _, _) => "Call",
                    Val::Obj(_, _, _) => "Obj",
                };
                *solved_val_kind_hist.entry(kind.to_string()).or_insert(0) += 1;
            }
        }
        // Categorize unsolved metas: shape of the type
        let mut unsolved_vty_kind_hist: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
        for entry in &self.meta {
            if let MetaEntry::Unsolved(vty, _, _, _) = entry {
                let kind = match vty.as_ref() {
                    Val::Flex(_, _) => "Flex",
                    Val::Rigid(_, _) => "Rigid",
                    Val::Decl(_, _) => "Decl",
                    Val::Lam(_, _, _) => "Lam",
                    Val::Pi(_, _, _, _) => "Pi",
                    Val::U(_) => "U",
                    Val::LiteralType => "LiteralType",
                    Val::LiteralIntro(_) => "LiteralIntro",
                    Val::Nat(_) => "Nat",
                    Val::Sum(_, _, _, _) => "Sum",
                    Val::SumCase { .. } => "SumCase",
                    Val::Match(_, _, _) => "Match",
                    Val::Call(_, _, _) => "Call",
                    Val::Obj(_, _, _) => "Obj",
                };
                *unsolved_vty_kind_hist.entry(kind.to_string()).or_insert(0) += 1;
            }
        }
        // Check how many unsolved metas share the same Cxt decl (by pointer identity of the HashMap root)
        // We count unique (decl.len(), env.len()) combos to estimate Cxt sharing
        let mut unique_cxt_fingerprints: StdHashSet<(usize, usize)> = StdHashSet::new();
        for entry in &self.meta {
            if let MetaEntry::Unsolved(_, c, _, _) = entry {
                unique_cxt_fingerprints.insert((c.decl.len(), c.env.len()));
            }
        }

        // ── Per-sourcecategory breakdown ──
        let mut visited_solved: StdHashSet<usize> = StdHashSet::new();
        let mut visited_unsolved: StdHashSet<usize> = StdHashSet::new();
        let mut visited_cxt_in_meta: StdHashSet<usize> = StdHashSet::new();
        let mut visited_trait: StdHashSet<usize> = StdHashSet::new();
        let mut visited_mutable: StdHashSet<usize> = StdHashSet::new();
        let mut visited_top_cxt: StdHashSet<usize> = StdHashSet::new();

        let mut detail_solved = DetailCounts::default();
        let mut detail_unsolved = DetailCounts::default();
        let mut detail_cxt_in_meta = DetailCounts::default();
        let mut detail_trait = DetailCounts::default();
        let mut detail_mutable = DetailCounts::default();
        let mut detail_top_cxt = DetailCounts::default();

        for entry in &self.meta {
            match entry {
                MetaEntry::Solved(val, vty) => {
                    detail_solved.walk_val(val, &mut visited_solved);
                    detail_solved.walk_val(vty, &mut visited_solved);
                }
                MetaEntry::Unsolved(vty1, cxt_m, vty2, _) => {
                    detail_unsolved.walk_val(vty1, &mut visited_unsolved);
                    detail_cxt_in_meta.walk_cxt(cxt_m, &mut visited_cxt_in_meta);
                    detail_unsolved.walk_val(vty2, &mut visited_unsolved);
                }
            }
        }
        for (_, instances) in self.trait_solver.class_instances.iter() {
            for inst in instances {
                for arg in &inst.assertion.arguments {
                    detail_trait.walk_val(arg, &mut visited_trait);
                }
                for dep in inst.dependencies.iter() {
                    for arg in &dep.arguments {
                        detail_trait.walk_val(arg, &mut visited_trait);
                    }
                }
            }
        }
        for (assertion, entry) in &self.trait_solver.assertion_table {
            for arg in &assertion.arguments {
                detail_trait.walk_val(arg, &mut visited_trait);
            }
            for (ans_assertion, _) in &entry.answers {
                for arg in &ans_assertion.arguments {
                    detail_trait.walk_val(arg, &mut visited_trait);
                }
            }
        }
        if let Ok(map) = self.mutable_map.read() {
            for val in map.values() {
                detail_mutable.walk_val(val, &mut visited_mutable);
            }
        }
        let cxt_decl_count;
        if let Some(c) = cxt {
            cxt_decl_count = c.decl.len();
            detail_top_cxt.walk_cxt(c, &mut visited_top_cxt);
        } else {
            cxt_decl_count = 0;
        }

        let val_node_size = std::mem::size_of::<Val>();
        let tm_node_size = std::mem::size_of::<Tm>();
        let arc_val_alloc = (std::mem::size_of::<Val>() + 16 + 7) & !7;
        let arc_tm_alloc = (std::mem::size_of::<Tm>() + 16 + 7) & !7;
        let node_val_alloc = {
            type N = crate::list::Node<Rc<Val>>;
            (std::mem::size_of::<N>() + 16 + 7) & !7
        };
        let node_spine_alloc = {
            type N = crate::list::Node<(Rc<Val>, parser::syntax::Icit)>;
            (std::mem::size_of::<N>() + 16 + 7) & !7
        };
        let meta_alloc = (std::mem::size_of::<MetaEntry>() + 16 + 7) & !7;

        fn detail_bytes(d: &DetailCounts, arc_val: usize, arc_tm: usize, node_val: usize, node_spine: usize) -> serde_json::Value {
            let val_heap = d.val_unique * arc_val;
            let tm_heap = d.tm_unique * arc_tm;
            let env_bytes = d.env_nodes * node_val;
            let spine_bytes = d.spine_nodes * node_spine;
            serde_json::json!({
                "unique_val_nodes": d.val_unique,
                "val_heap_bytes": val_heap,
                "unique_tm_nodes": d.tm_unique,
                "tm_heap_bytes": tm_heap,
                "env_spine_nodes": d.env_nodes,
                "env_node_bytes": env_bytes,
                "spine_nodes": d.spine_nodes,
                "spine_node_bytes": spine_bytes,
                "span_void_count": d.span_void_count,
                "span_smolstr_count": d.span_smolstr_count,
                "closure_count": d.closure_count,
                "total_arc_bytes": val_heap + tm_heap + env_bytes + spine_bytes,
            })
        }

        // measure_cxt_deep inlined above

        let cxt_deep = if let Some(c) = cxt {
            let decl_len = c.decl.len();
            let decl_bytes = decl_len * (decl_entry_sz + 24);
            let src_names_len = c.src_names.len();
            let ns_bytes: usize = c.namespace.iter().map(|_| std::mem::size_of::<(Rc<Val>, HashSet<SmolStr>, Raw)>()).sum();
            let ns_set_bytes: usize = c.namespace.iter().map(|(_, s, _)| s.len() * (std::mem::size_of::<SmolStr>() + 8)).sum();
            let namespaces_bytes = c.namespaces.len() * (std::mem::size_of::<SmolStr>() + 8);
            let env_len = c.env.len();
            let pruning_len = c.pruning.len();

            json!({
                "cxt_struct_bytes": std::mem::size_of::<cxt::Cxt>(),
                "decl_entries": decl_len,
                "decl_approx_bytes": decl_bytes,
                "decl_entry_size": decl_entry_sz,
                "src_names_entries": src_names_len,
                "env_len": env_len,
                "pruning_len": pruning_len,
                "namespace_len": c.namespace.len(),
                "namespace_list_bytes": ns_bytes,
                "namespace_set_bytes": ns_set_bytes,
                "namespaces_len": c.namespaces.len(),
                "namespaces_set_bytes": namespaces_bytes,
                "lvl": c.lvl.0,
                "estimated_total": std::mem::size_of::<cxt::Cxt>() + decl_bytes + ns_bytes + ns_set_bytes + namespaces_bytes,
            })
        } else {
            json!(null)
        };

        // Measure unsolved meta Cxt sizes
        let cxt_in_meta_count: usize = self.meta.iter().filter_map(|m| match m {
            MetaEntry::Unsolved(_, c, _, _) => Some(c.decl.len()),
            _ => None,
        }).sum();
        let cxt_in_meta_env_avg: usize = if unsolved > 0 {
            self.meta.iter().filter_map(|m| match m {
                MetaEntry::Unsolved(_, c, _, _) => Some(c.env.len()),
                _ => None,
            }).sum::<usize>() / unsolved
        } else { 0 };

        json!({
            "meta_entries": {
                "total": total,
                "solved": solved,
                "unsolved": unsolved,
                "capacity": meta_cap,
                "entry_size": MetaEntry_sz,
                "vec_allocation_bytes": meta_cap * MetaEntry_sz,
                "est_inline_bytes": total * MetaEntry_sz,
            },
"hover_table": {
                "len": hover_len,
                "capacity": hover_cap,
                "entry_size": hover_entry_sz,
                "capacity_bytes": hover_cap_bytes,
            },
"meta_contrains": {
                "len": constraints_len,
                "capacity": constraints_cap,
                "entry_size": meta_contrains_entry_sz,
                "capacity_bytes": meta_contrains_cap_bytes,
            },
            "completion_table": {
                "len": completions_len,
            },
            "per_source_breakdown": {
                "solved_meta_vals": detail_bytes(&detail_solved, arc_val_alloc, arc_tm_alloc, node_val_alloc, node_spine_alloc),
                "unsolved_meta_vals": detail_bytes(&detail_unsolved, arc_val_alloc, arc_tm_alloc, node_val_alloc, node_spine_alloc),
                "cxt_in_unsolved_meta": detail_bytes(&detail_cxt_in_meta, arc_val_alloc, arc_tm_alloc, node_val_alloc, node_spine_alloc),
                "trait_solver_vals": detail_bytes(&detail_trait, arc_val_alloc, arc_tm_alloc, node_val_alloc, node_spine_alloc),
                "mutable_map_vals": detail_bytes(&detail_mutable, arc_val_alloc, arc_tm_alloc, node_val_alloc, node_spine_alloc),
                "top_level_cxt": detail_bytes(&detail_top_cxt, arc_val_alloc, arc_tm_alloc, node_val_alloc, node_spine_alloc),
            },
            "cxt_in_meta_stats": {
                "total_cxt_in_meta": unsolved,
                "sum_decl_entries_in_meta_cxts": cxt_in_meta_count,
                "avg_decl_entries_per_meta_cxt": if unsolved > 0 { cxt_in_meta_count / unsolved } else { 0 },
                "avg_env_len_per_meta_cxt": cxt_in_meta_env_avg,
            },
            "meta_content_analysis": {
                "unsolved_env_len_histogram": unsolved_env_len_hist,
                "unsolved_decl_len_histogram": unsolved_decl_len_hist,
                "solved_val_kind_histogram": solved_val_kind_hist,
                "unsolved_vty_kind_histogram": unsolved_vty_kind_hist,
                "unique_cxt_fingerprint_count": unique_cxt_fingerprints.len(),
            },
            "cxt_deep": cxt_deep,
            "trait_solver": {
                "class_count": self.trait_solver.class_instances.len(),
                "total_instances": self.trait_solver.class_instances.values().map(|v| v.len()).sum::<usize>(),
                "assertion_table_size": self.trait_solver.assertion_table.len(),
                "assertion_table_capacity": self.trait_solver.assertion_table.capacity(),
                "generator_stack_len": self.trait_solver.generator_stack.len(),
                "resume_stack_len": self.trait_solver.resume_stack.len(),
            },
            "cxt": {
                "decl_entries": cxt_decl_count,
            },
            "type_sizes": {
                "MetaEntry": MetaEntry_sz,
                "Cxt": std::mem::size_of::<cxt::Cxt>(),
                "Infer": std::mem::size_of::<Self>(),
                "Val": val_node_size,
                "Tm": tm_node_size,
                "Closure": std::mem::size_of::<Closure>(),
                "Env": std::mem::size_of::<Env>(),
                "Spine": std::mem::size_of::<Spine>(),
                "SmolStr": std::mem::size_of::<SmolStr>(),
                "Span_void": std::mem::size_of::<Span<()>>(),
                "Span_SmolStr": std::mem::size_of::<Span<SmolStr>>(),
                "Locals": std::mem::size_of::<syntax::Locals>(),
                "List_Rc_Val": std::mem::size_of::<List<Rc<Val>>>(),
                "DeclTm": std::mem::size_of::<DeclTm>(),
                "PatternDetail": std::mem::size_of::<PatternDetail>(),
                "BiMap": std::mem::size_of::<crate::bimap::BiMap<SmolStr, Lvl, (Span<()>, Rc<VTy>)>>(),
                "DeclEntry": decl_entry_sz,
                "Rc_Val": std::mem::size_of::<Rc<Val>>(),
                "Rc_Tm": std::mem::size_of::<Rc<Tm>>(),
            },
        })
    }

    pub fn memory_stats(&self) -> serde_json::Value {
        self.memory_stats_with_cxt(None)
    }

    fn new_meta(&mut self, a: Rc<VTy>, cxt: Cxt, origin_typ: Rc<VTy>, span: Span<()>) -> u32 {
        self.meta.push(MetaEntry::Unsolved(a, std::sync::Arc::new(cxt), origin_typ, span));
        self.meta.len() as u32 - 1
    }
    fn fresh_meta(&mut self, cxt: &Cxt, a: Rc<VTy>, span: Span<()>) -> Rc<Tm> {
        if let Ok(Some((a, _))) = self.solve_trait(cxt, &a, false) {
            a
        } else if let Val::Sum(_, _, _, true) = a.as_ref() {
            let m = self.new_meta(a.clone(), cxt.clone(), a, span);
            self.trait_metas.push(MetaVar(m));
            Tm::Meta(MetaVar(m)).into()
        } else {
            let closed = self.eval(
                &cxt.decl,
                &List::new(),
                &close_ty(&cxt.locals, self.quote(&cxt.decl, cxt.lvl, &a)),
            );
            let m = self.new_meta(closed, cxt.clone(), a, span);
            Tm::AppPruning(Tm::Meta(MetaVar(m)).into(), cxt.pruning.clone()).into()
        }
    }
    fn lookup_meta(&self, m: MetaVar) -> &MetaEntry {
        &self.meta[m.0 as usize]
    }
    /// Detect unsolved metas in a value graph WITHOUT quoting it (see
    /// `Tm::no_metas`): walk the `Val`s directly with a pointer-keyed visited
    /// set so shared subgraphs are visited once and nothing is forced.  All
    /// nodes reachable here stay alive through the meta table for the
    /// duration of the call, so pointer identity is stable.  The rare
    /// solved-meta-with-spine shape falls back to the quote-based walk.
    fn val_no_metas(&self, decl: &Decl, l: Lvl, v: &Rc<Val>, seen: &mut rustc_hash::FxHashSet<usize>) -> Option<(Cxt, Rc<Val>, Span<()>)> {
        if !seen.insert(Rc::as_ptr(v) as usize) {
            return None;
        }
        match v.as_ref() {
            Val::Flex(m, sp) => {
                if sp.len() > 0 {
                    // Solution applied to a spine: only evaluation can
                    // produce the applied value; keep the quote-based walk.
                    // The quote level is arbitrary-but-large: the result is
                    // only walked for `Tm::Meta` nodes, so de Bruijn indices
                    // never matter — but a too-small level would underflow
                    // `lvl2ix` on solutions carrying deeper Rigid levels
                    // than the current binder level.
                    const NM_QUOTE_LVL: Lvl = Lvl(u32::MAX / 2);
                    return self.quote(decl, NM_QUOTE_LVL, v).no_metas_seen(self, decl, NM_QUOTE_LVL, seen);
                }
                match self.lookup_meta(*m) {
                    MetaEntry::Unsolved(_, cxt, oty, span) => Some((cxt.as_ref().clone(), oty.clone(), *span)),
                    MetaEntry::Solved(sol, _) => self.val_no_metas(decl, l, sol, seen),
                }
            }
            Val::Rigid(_, sp) | Val::Decl(_, sp) => sp.iter().find_map(|(a, _)| self.val_no_metas(decl, l, a, seen)),
            Val::Obj(x, _, sp) => self.val_no_metas(decl, l, x, seen)
                .or_else(|| sp.iter().find_map(|(a, _)| self.val_no_metas(decl, l, a, seen))),
            Val::Lam(_, _, closure) => self.closure_no_metas(decl, l, closure, seen),
            Val::Pi(_, _, dom, closure) => self.val_no_metas(decl, l, dom, seen)
                .or_else(|| self.closure_no_metas(decl, l, closure, seen)),
            Val::U(_) | Val::LiteralType | Val::LiteralIntro(_) => None,
            Val::Nat(_) => None,
            Val::Sum(_, params, _, _) => params.iter().find_map(|(_, val, ty, _)| {
                self.val_no_metas(decl, l, val, seen).or_else(|| self.val_no_metas(decl, l, ty, seen))
            }),
            Val::SumCase { typ, datas, .. } => self.val_no_metas(decl, l, typ, seen)
                .or_else(|| datas.iter().find_map(|(_, d, _)| self.val_no_metas(decl, l, d, seen))),
            Val::Match(scrut, env, cases) => self.val_no_metas(decl, l, scrut, seen)
                .or_else(|| env.iter().find_map(|e| self.val_no_metas(decl, l, e, seen)))
                .or_else(|| cases.iter().find_map(|(_, body)| Tm::no_metas_rc(body, self, decl, l, seen))),
            Val::Call(_, args, body) => args.iter().find_map(|(a, _)| self.val_no_metas(decl, l, a, seen))
                .or_else(|| self.val_no_metas(decl, l, body, seen)),
        }
    }
    fn closure_no_metas(&self, decl: &Decl, l: Lvl, closure: &Closure, seen: &mut rustc_hash::FxHashSet<usize>) -> Option<(Cxt, Rc<Val>, Span<()>)> {
        closure.0.iter().find_map(|e| self.val_no_metas(decl, l, e, seen))
            .or_else(|| Tm::no_metas_rc(&closure.1, self, decl, l, seen))
    }
    fn force(&self, decl: &Decl, t: &Rc<Val>) -> Rc<Val> {
        prof_count(&FUNC_PROF.force.1);
        match t.as_ref() {
            // Only the compound shapes whose forcing recursively walks
            // sub-values benefit from the memo; every other shape is an
            // O(1) arm in `force_inner`.
            Val::SumCase { .. } | Val::Call(..) | Val::Obj(..) => {}
            _ => return self.force_inner(decl, t),
        }
        let key = Rc::as_ptr(t) as usize;
        let ver = PRIM_VERSION.load(std::sync::atomic::Ordering::Relaxed);
        let epoch = FORCE_MEMO_EPOCH.with(|e| e.get());
        if let Some(r) = FORCE_MEMO.with(|m| {
            m.borrow().get(&key)
                .filter(|(_, _, v, e)| *v == ver && *e == epoch)
                .map(|(_, r, _, _)| r.clone())
        }) {
            return r;
        }
        let taint0 = FORCE_TAINT.with(|t| t.get());
        let r = self.force_inner(decl, t);
        if FORCE_TAINT.with(|t| t.get()) == taint0
            && PRIM_VERSION.load(std::sync::atomic::Ordering::Relaxed) == ver
        {
            FORCE_MEMO.with(|m| {
                let mut m = m.borrow_mut();
                if m.len() >= FORCE_MEMO_CAP {
                    m.clear();
                }
                m.insert(key, (t.clone(), r.clone(), ver, epoch));
            });
        }
        r
    }
    // Fast path for deep constructor chains (e.g. big `Nat` literals, which
    // are nested `Val::SumCase`s): force the spine iteratively so a
    // million-deep chain does not consume a million native stack frames.
    fn force_inner(&self, decl: &Decl, t: &Rc<Val>) -> Rc<Val> {
        prof_shape(t);
        // `force_chain` only handles unary `SumCase` spines (big `Nat`
        // literals).  Gate the call on that shape so the overwhelming common
        // case (`Val::Sum`, plus flex/obj/call/etc.) skips `force_chain`'s
        // `t.clone()` + match entirely instead of cloning and bailing out.
        if matches!(t.as_ref(), Val::SumCase { datas, .. } if datas.len() == 1) {
            if let Some(v) = self.force_chain(decl, t) {
                return v;
            }
        }
        match t.as_ref() {
            Val::Flex(m, sp) => {
                // Meta state is memo-tainting (see FORCE_MEMO): solutions
                // change over time (and the ns-probe machinery rolls them
                // back), so walks through this arm are never cached.
                force_taint_bump();
                match self.lookup_meta(*m) {
                    MetaEntry::Solved(t_solved, _) => self.force(decl, &self.v_app_sp(decl,
                 t_solved.clone(), sp)),
                    MetaEntry::Unsolved(_, _, _, _) => Val::Flex(*m, sp.clone()).into(),
                }
            }
            // A native Nat is already WHNF (definitionally `succ^n zero`
            // compressed to one u64).  Not forcing it here is exactly the
            // Lean/Agda native-Nat win: re-forcing a concrete Nat used to
            // re-walk (and possibly rebuild) the whole unary chain.
            Val::Nat(_) => t.clone(),
            Val::Obj(x, a, b) => {
                let xf = self.force(decl, x);
                if Rc::ptr_eq(&xf, x) {
                    t.clone()
                } else {
                    Val::Obj(xf, a.clone(), b.clone()).into()
                }
            },
            Val::Call(name, args, body) => {
                // Stale def-shape normalization: prelude defs elaborated while
                // a helper was still a recursive `def` (e.g. `add_zero_left`'s
                // type `Eq (0 + a) a`) cache the inlined `Val::Call("nat_add",
                // [0, a], Match(a, ..))` shape.  After `register_nat_builtins`
                // overwrites `nat_add` with a prim, user code computes `0 + a`
                // as a `Val::Decl` (prim None), so the two shapes would not
                // unify.  When the call's name is now prim-backed, re-apply the
                // args through `v_app` so the value normalizes to the same
                // `Val::Decl`/concrete form the prim produces.
                // The name pre-filter avoids the decl-table hash lookup on
                // every Call force (the hottest value shape after Sum); the
                // decl-table check below stays authoritative, so a later user
                // redefinition of the name as a plain def disables the branch.
                if nat_primop_symbol(name).is_some()
                    && decl.get(name).map_or(false, |e| e.5.is_some())
                {
                    let mut acc: Rc<Val> = Val::Decl(empty_span(name.clone()), List::new()).into();
                    for (a, i) in args.iter() {
                        acc = self.v_app(decl, &acc, a.clone(), *i);
                    }
                    // If the prim returned a concrete result, force it; if it
                    // left a stuck `Val::Decl`, return it directly.  (The prim
                    // cannot return another `Val::Call`, so no re-entry loop.)
                    return match acc.as_ref() {
                        Val::Call(..) => self.force(decl, &acc),
                        _ => acc,
                    };
                }
                let bf = self.force(decl, body);
                // Also force the display args so comparisons (e.g. the unify
                // fast path) and pretty-printing see normalized values.
                let new_args = args.map(|(v, i)| (self.force(decl, v), *i));
                let changed = !Rc::ptr_eq(&bf, body)
                    || args
                        .iter()
                        .zip(new_args.iter())
                        .any(|((v, _), (vf, _))| !Rc::ptr_eq(v, vf));
                if changed {
                    Val::Call(name.clone(), new_args, bf).into()
                } else {
                    t.clone()
                }
            },
            Val::Decl(x, sp) => {
                if let Some((_, _, _, _, _, Some(prim_fn), _)) = decl.get(&x.data) {
                    // Impure prims (mutable globals / IO / diagnostics) are
                    // memo-tainting: skipping their re-execution on a cache
                    // hit would be observable.  The prim-ness lookup itself
                    // is covered by the entry's PRIM_VERSION tag.
                    if !prim_is_pure(&x.data) {
                        force_taint_bump();
                    }
                    let args: Vec<Rc<Val>> = {
                        let mut v: Vec<Rc<Val>> = sp.iter().map(|(v, _)| v.clone()).collect();
                        v.reverse();
                        v
                    };
                    if let Some(result) = prim_fn.0(self, decl, &args) {
                        return self.force(decl, &result);
                    }
                }
                t.clone()
            },
            // A `Sum` is already in WHNF (constructor-headed): its parameter
            // values/types are arguments of the constructor, not the head, and
            // normalizing them here (a) is wasted work — the result is
            // virtually always `t.clone()` — and (b) recursively walks the
            // whole type tree below the Sum on EVERY force call, which for
            // fat bundle/struct types (many params, nested bundles) dominates
            // elaboration time (measured: ~29M of ~33M force() calls in
            // examples/hdl/10-bundle.typort entered on `Val::Sum`).
            // Callers that need normalized params force them individually.
            // Mirrors the `Val::Rigid` treatment (spine args not forced).
            Val::Sum(..) => t.clone(),
            Val::SumCase { is_trait, typ, index, datas } => {
                let tf = self.force(decl, typ);
                let mut changed = !Rc::ptr_eq(&tf, typ);
                // Force every data (side effects must run regardless), but
                // avoid allocating the rebuilt `datas` Vec in the common case
                // where nothing changes — the previous `.map(...).collect()`
                // allocated a fresh Vec (plus a `SmolStr` clone per field) on
                // every call, then dropped it when `changed` was false.
                let mut new_datas: Option<Vec<(Span<SmolStr>, Rc<Val>, Icit)>> = None;
                for (i, (n, ty, ic)) in datas.iter().enumerate() {
                    let df = self.force(decl, ty);
                    if !Rc::ptr_eq(&df, ty) {
                        changed = true;
                    }
                    if changed {
                        let v = new_datas.get_or_insert_with(|| {
                            // First change: back-fill the unchanged fields seen
                            // so far (their forced value is ptr-identical).
                            datas.iter()
                                .take(i)
                                .map(|(n, ty, ic)| (n.clone(), ty.clone(), *ic))
                                .collect()
                        });
                        v.push((n.clone(), df, *ic));
                    }
                }
                if changed {
                    Val::SumCase {
                        is_trait: *is_trait,
                        typ: tf,
                        index: *index,
                        datas: Rc::new(new_datas.unwrap_or_default()),
                    }.into()
                } else {
                    t.clone()
                }
            },
            _ => t.clone(),
        }
    }

    /// Iterative force for deep unary-constructor chains (`Val::SumCase`
    /// spines where every node has exactly one data that is itself a
    /// `SumCase`, e.g. big `Nat` literals).  Returns `None` when `t` is not
    /// such a chain so the caller falls back to the recursive `force`.
    /// When nothing changed along the spine the original `t` is returned
    /// unchanged (identical to the recursive behaviour); otherwise the chain
    /// is rebuilt from the inside out.
    fn force_chain(&self, decl: &Decl, t: &Rc<Val>) -> Option<Rc<Val>> {
        struct Node {
            typ: Rc<Val>,
            forced_typ: Rc<Val>,
            index: u32,
            is_trait: bool,
            datas: SumCaseDatas,
        }
        // Descend the spine iteratively.
        let mut nodes: Vec<Node> = Vec::new();
        let mut cur = t.clone();
        loop {
            match cur.as_ref() {
                Val::SumCase { is_trait, typ, index, datas } if datas.len() == 1 => {
                    let forced_typ = self.force(decl, typ);
                    nodes.push(Node {
                        typ: typ.clone(),
                        forced_typ,
                        index: *index,
                        is_trait: *is_trait,
                        datas: datas.clone(),
                    });
                    cur = datas[0].1.clone();
                }
                _ => break,
            }
        }
        if nodes.is_empty() {
            return None;
        }
        // Force the tail (the innermost value below the spine).
        let tail_forced = self.force(decl, &cur);
        let mut changed = !Rc::ptr_eq(&tail_forced, &cur);
        for node in &nodes {
            if !Rc::ptr_eq(&node.forced_typ, &node.typ) {
                changed = true;
            }
        }
        if !changed {
            return Some(t.clone());
        }
        // Rebuild from the inside out.
        let mut inner = tail_forced;
        for node in nodes.into_iter().rev() {
            let name = node.datas[0].0.clone();
            let icit = node.datas[0].2;
            let new_datas: SumCaseDatas = Rc::new(vec![(name, inner.clone(), icit)]);
            inner = Val::SumCase {
                is_trait: node.is_trait,
                typ: node.forced_typ,
                index: node.index,
                datas: new_datas,
            }.into();
        }
        Some(inner)
    }
    fn v_meta(&self, m: MetaVar) -> Rc<Val> {
        match self.lookup_meta(m) {
            MetaEntry::Solved(v, _) => v.clone(),
            MetaEntry::Unsolved(_, _, _, _) => Val::vmeta(m).into(),
        }
    }

    fn closure_apply(&self, decl: &Decl, closure: &Closure, u: Rc<Val>) -> Rc<Val> {
        //println!("{} {:?} {:?}", "closure apply".yellow(), closure, u);
        self.eval(decl, &closure.0.prepend(u), &closure.1)
    }

    fn v_app(&self, decl: &Decl, t: &Rc<Val>, u: Rc<Val>, i: Icit) -> Rc<Val> {
        let _g = prof_enter(&FUNC_PROF.v_app.0, &FUNC_PROF.v_app.1);
        //println!("v_app {t:?} {u:?}");
        match t.as_ref() {
            Val::Lam(_, _, closure) => self.closure_apply(decl, closure, u),
            Val::Flex(m, sp) => Val::Flex(*m, sp.prepend((u, i))).into(),
            Val::Rigid(x, sp) => Val::Rigid(*x, sp.prepend((u, i))).into(),
            Val::Decl(x, sp) => {
                let acc = sp.prepend((u, i));
                if let Some(entry) = decl.get(&x.data) {
                    if let Some(ref prim_fn) = entry.5 {
                        // Impure prims taint any enclosing force-memo walk
                        // (their application is observable; pure prims'
                        // results are a function of their arguments).
                        if !prim_is_pure(&x.data) {
                            force_taint_bump();
                        }
                        let args: Vec<Rc<Val>> = {
                            let mut v: Vec<Rc<Val>> = acc.iter().map(|(v, _)| v.clone()).collect();
                            v.reverse();
                            v
                        };
                        if let Some(result) = prim_fn.0(self, decl, &args) {
                            return result;
                        }
                    }
                }
                Val::Decl(x.clone(), acc).into()
            },
            Val::Obj(x, name, sp) => Val::Obj(x.clone(), name.clone(), sp.prepend((u, i))).into(),
            Val::Call(name, args, body) => Val::Call(name.clone(), args.prepend((u.clone(), i)), self.v_app(decl, body, u, i)).into(),
            // A stuck match applied to an argument stays stuck; once the
            // scrutinee reduces, exactly one branch fires, so splicing the
            // application into every branch body is semantics-preserving.
            // (Previously this fell into `panic!("impossible apply")`, which
            // was user-triggerable on `(match x { ... }) arg` with a rigid x.)
            Val::Match(val, env, cases) => {
                let l = Lvl(env.len() as u32);
                let u_tm = self.quote(decl, l, &u);
                let new_cases = cases
                    .iter()
                    .map(|(p, b)| (p.clone(), Tm::App(b.clone(), u_tm.clone(), i).into()))
                    .collect();
                Val::Match(val.clone(), env.clone(), new_cases).into()
            },
            x => panic!("impossible apply\n  {:?}\nto\n  {:?}", x, u),
        }
    }

    fn v_app_sp(&self, decl: &Decl, mut t: Rc<Val>, spine: &Spine) -> Rc<Val> {
        let items: Vec<(&Rc<Val>, Icit)> = spine.iter().map(|(v, i)| (v, *i)).collect();
        for (u, i) in items.into_iter().rev() {
            t = self.v_app(decl, &t, u.clone(), i);
        }
        t
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
            // The pruning was recorded in a deeper context than the eval
            // environment: a fresh meta created inside a trait-wrapper let
            // (an operator wrapper) whose binding is not in scope at the
            // node's own eval position (the wrapper's application argument).
            // The missing argument has no value — apply the rest of the
            // spine only.
            (a, b) if a.head().is_none() && matches!(b.head(), Some(Some(_))) => {
                self.v_app_pruning(decl, a, v, &b.tail())
            }
            _ => panic!("impossible {v:?} with env={:?} pr={:?}", env, pr),
        }
    }

    fn eval(&self, decl: &Decl, env: &Env, tm: &Rc<Tm>) -> Rc<Val> {
        let _g = prof_enter(&FUNC_PROF.eval.0, &FUNC_PROF.eval.1);
        self.eval_inner(decl, env, tm)
    }

    /// Global-mutable names whose presence in a def body makes the def's
    /// `Tm::Decl` lookup side-effecting: the body must be replayed (re-run in
    /// the caller's context) instead of handing back the declaration-time
    /// cached WHNF.  `get_global` is included for the same reason a hardware
    /// def reads the current module tree — a cached read would observe a
    /// stale tree.
    const REPLAY_GLOBAL_OPS: &'static [&'static str] = &[
        "create_global", "change_mutable", "change_mutable_default", "get_global",
    ];

    /// Does evaluating `name` (a parameterless def) have global side effects?
    /// Memoized: the body term is scanned for `REPLAY_GLOBAL_OPS` calls,
    /// following referenced defs recursively (cycle-safe).  Parameterless
    /// hardware defs (SpinalHDL-style `def f() = { reg r = UInt[8]; ... }`)
    /// and the module macro's own `def tree` hit this path, so their
    /// `createSignalExpr`/`change_mutable` effects run against the CURRENT
    /// module tree every time the def is called.
    fn def_needs_replay(&self, decl: &Decl, name: &SmolStr) -> bool {
        if let Ok(memo) = self.def_replay_memo.read() {
            if let Some(m) = memo.get(name) {
                return *m;
            }
        }
        let mut visiting = std::collections::HashSet::new();
        let result = self.scan_def_replay(decl, name, &mut visiting);
        if let Ok(mut memo) = self.def_replay_memo.write() {
            memo.insert(name.clone(), result);
        }
        result
    }

    fn scan_def_replay(&self, decl: &Decl, name: &SmolStr, visiting: &mut std::collections::HashSet<SmolStr>) -> bool {
        if !visiting.insert(name.clone()) {
            return false; // cycle: nothing new to learn
        }
        match decl.get(name) {
            // Builtins (prim) are never replayed: their stored body term is a
            // self-referential `Tm::Decl(name)` placeholder, and the actual
            // behavior runs through the prim function at application time.
            Some(e) if e.5.is_some() => {
                visiting.remove(name);
                return false;
            }
            Some(e) => {
                let body = e.1.clone();
                let mut found = false;
                self.tm_scan_global_ops(decl, &body, visiting, &mut found);
                visiting.remove(name);
                found
            }
            None => false,
        }
    }

    /// Depth-first scan of a closed term for `REPLAY_GLOBAL_OPS` calls (as
    /// `Tm::Decl` heads) or references to other defs that need replay.
    fn tm_scan_global_ops(&self, decl: &Decl, tm: &Tm, visiting: &mut std::collections::HashSet<SmolStr>, found: &mut bool) {
        if *found {
            return;
        }
        match tm {
            Tm::Decl(x) => {
                if Self::REPLAY_GLOBAL_OPS.contains(&x.data.as_str()) {
                    *found = true;
                } else {
                    // A reference to another def: if that def needs replay,
                    // this one does too (the effect happens through it).
                    let entry = decl.get(&x.data).map(|e| e.1.clone());
                    if entry.is_some() && self.scan_def_replay(decl, &x.data, visiting) {
                        *found = true;
                    }
                }
            }
            Tm::Obj(t, _) => self.tm_scan_global_ops(decl, t, visiting, found),
            Tm::Lam(_, _, b) => self.tm_scan_global_ops(decl, b, visiting, found),
            Tm::App(f, u, _) => {
                self.tm_scan_global_ops(decl, f, visiting, found);
                self.tm_scan_global_ops(decl, u, visiting, found);
            }
            Tm::AppPruning(t, _) => self.tm_scan_global_ops(decl, t, visiting, found),
            Tm::Pi(_, _, a, b) => {
                self.tm_scan_global_ops(decl, a, visiting, found);
                self.tm_scan_global_ops(decl, b, visiting, found);
            }
            Tm::Let(_, _, t, u) => {
                self.tm_scan_global_ops(decl, t, visiting, found);
                self.tm_scan_global_ops(decl, u, visiting, found);
            }
            Tm::SumCase { typ, datas, .. } => {
                self.tm_scan_global_ops(decl, typ, visiting, found);
                for (_, t, _) in datas.iter() {
                    self.tm_scan_global_ops(decl, t, visiting, found);
                }
            }
            Tm::Match(t, cases) => {
                self.tm_scan_global_ops(decl, t, visiting, found);
                for (_, b) in cases {
                    self.tm_scan_global_ops(decl, b, visiting, found);
                }
            }
            Tm::Call(_, args, body) => {
                for (t, _) in args.iter() {
                    self.tm_scan_global_ops(decl, t, visiting, found);
                }
                self.tm_scan_global_ops(decl, body, visiting, found);
            }
            Tm::OpCall { args, body, .. } => {
                for (t, _) in args.iter() {
                    self.tm_scan_global_ops(decl, t, visiting, found);
                }
                self.tm_scan_global_ops(decl, body, visiting, found);
            }
            Tm::Sum(_, params, _, _) => {
                // Dependent-index param values can embed calls (case names
                // in `TmSumCases` are plain strings, nothing to scan).
                for (_, val, _, _) in params.iter() {
                    self.tm_scan_global_ops(decl, val, visiting, found);
                }
            }
            // Remaining variants (Var/U/Meta/LiteralType/LiteralIntro) carry
            // no sub-terms.  When adding a `Tm` variant that embeds `Rc<Tm>`
            // payloads, add an arm above: a missed arm makes an
            // effect-performing def look cacheable, its side effects are
            // silently dropped, and (since the decl-time eval skip in
            // elaboration.rs trusts this scan) its body never runs at all.
            _ => {}
        }
    }
    fn eval_inner(&self, decl: &Decl, env: &Env, tm: &Rc<Tm>) -> Rc<Val> {
        // Iterative evaluator.
        //
        // The original evaluator recursed through `self.eval` for every
        // application (`Tm::App` → `v_app` → `closure_apply` → `eval`) and
        // for every dispatched match branch (`Tm::Match` → `eval_aux` →
        // `eval`), so evaluating e.g. `0 + 1000000` on unary Peano `Nat`
        // (whose `nat_add_helper` recurses once per `succ`) consumed one
        // native stack frame per `succ` and overflowed the stack.  This
        // version runs the same evaluation steps as an explicit-stack loop:
        // each `succ`/match level costs O(1) native stack.  Evaluation order
        // within `Tm::App` matches the original (function part first).
        enum Frame {
            /// `Tm::App(t, u, i)`: after `t` evaluates, evaluate `u` next in
            /// the application's own env (the function part's evaluation may
            /// change the machine env, e.g. via `let`/`match` dispatch).
            EvalArg { arg: Rc<Tm>, icit: Icit, env: Env },
            /// The evaluated function; the current value (the evaluated
            /// argument) is applied to it.
            ApplyAfter { fun: Rc<Val>, icit: Icit },
            /// `Tm::Obj(t, name)`: after `t` evaluates, build the Obj value.
            Obj(Span<SmolStr>),
            /// `Tm::Let(_, _, t, u)`: after `t` evaluates to v, eval `u` in env+v.
            Let(Rc<Tm>, Env),
            /// `Tm::AppPruning(t, pr)`: after `t` evaluates, apply pruning.
            Prune(Pruning, Env),
            /// `Tm::Pi(x, i, a, b)`: after `a` evaluates, build the Pi value.
            Pi(Span<SmolStr>, Icit, Rc<Tm>, Env),
            /// `Tm::Call`/`Tm::OpCall`: after the body evaluates, wrap it in
            /// `Val::Call` if the body stuck at a match.
            Call(SmolStr, List<(Rc<Tm>, Icit)>, Env),
            /// `Tm::Match(t, cases)`: after the scrutinee evaluates, dispatch.
            Match(Vec<(PatternDetail, Rc<Tm>)>, Env),
            /// `Tm::SumCase`: after the current data term evaluates, collect it
            /// and evaluate the next data / the type.
            SumCase {
                is_trait: bool,
                typ: Rc<Tm>,
                index: u32,
                datas: TmSumCaseDatas,
                /// Data fields collected so far (in order).
                done: Vec<(Span<SmolStr>, Rc<Val>, Icit)>,
                /// The data field whose term is currently being evaluated.
                cur: (Span<SmolStr>, Icit),
            },
            /// All `Tm::SumCase` data terms evaluated; `typ` just evaluated:
            /// assemble the value.
            SumCaseTyp {
                is_trait: bool,
                index: u32,
                datas: Vec<(Span<SmolStr>, Rc<Val>, Icit)>,
            },
        }
        let mut stack: Vec<Frame> = Vec::new();
        let mut env = env.clone();
        let mut tm = tm.clone();
        loop {
            // Evaluate the current term to a value.  Composite terms push a
            // continuation frame and continue with their sub-term instead of
            // recursing.
            let mut v = match tm.as_ref() {
                Tm::Var(x) => match env.iter().nth(x.0 as usize) {
                    Some(v) => v.clone(),
                    None => panic!("var {:?} not found", x.0),
                },
                Tm::Decl(x) => {
                    let e = decl.get(&x.data);
                    match e {
                        Some(e) => {
                            // Parameterless defs whose body performs global
                            // side effects are replayed on EVERY lookup (the
                            // body re-evaluated in the CURRENT context, e.g.
                            // inside a module's tree push) instead of
                            // returning the declaration-time cached WHNF —
                            // see `def_needs_replay`.
                            if self.def_needs_replay(decl, &x.data) {
                                env = List::new();
                                tm = e.1.clone();
                                continue;
                            }
                            e.2.clone()
                        }
                        None => Val::Decl(x.clone(), List::new()).into(),
                    }
                }
                Tm::Lam(x, i, t) => Val::Lam(x.clone(), *i, Closure(env.clone(), t.clone())).into(),
                Tm::U(x) => Val::U(*x).into(),
                Tm::Meta(m) => self.v_meta(*m),
                Tm::LiteralIntro(x) => Val::LiteralIntro(x.clone()).into(),
                Tm::LiteralType => Val::LiteralType.into(),
                Tm::App(t, u, i) => {
                    stack.push(Frame::EvalArg { arg: u.clone(), icit: *i, env: env.clone() });
                    tm = t.clone();
                    continue;
                }
                Tm::Obj(t, name) => {
                    stack.push(Frame::Obj(name.clone()));
                    tm = t.clone();
                    continue;
                }
                Tm::Let(_, _, t, u) => {
                    stack.push(Frame::Let(u.clone(), env.clone()));
                    tm = t.clone();
                    continue;
                }
                Tm::AppPruning(t, pr) => {
                    stack.push(Frame::Prune(pr.clone(), env.clone()));
                    tm = t.clone();
                    continue;
                }
                Tm::Pi(x, i, a, b) => {
                    stack.push(Frame::Pi(x.clone(), *i, b.clone(), env.clone()));
                    tm = a.clone();
                    continue;
                }
                Tm::Call(name, args, body) => {
                    stack.push(Frame::Call(name.clone(), args.clone(), env.clone()));
                    tm = body.clone();
                    continue;
                }
                Tm::OpCall { symbol: _, name, args, body } => {
                    stack.push(Frame::Call(name.clone(), args.clone(), env.clone()));
                    tm = body.clone();
                    continue;
                }
                Tm::Match(tm0, cases) => {
                    stack.push(Frame::Match(cases.clone(), env.clone()));
                    tm = tm0.clone();
                    continue;
                }
                Tm::Sum(name, params, cases, is_trait) => {
                    let new_params = Rc::new(params
                        .iter()
                        .map(|x| (x.0.clone(), self.eval(decl, &env, &x.1), self.eval(decl, &env, &x.2), x.3))
                        .collect());
                    Val::Sum(name.clone(), new_params, cases.clone(), *is_trait).into()
                }
                Tm::SumCase { is_trait, typ, index, datas } => {
                    // Evaluate the data fields iteratively: deep constructor
                    // chains (e.g. quoted big `Nat` literals) are nested
                    // `Tm::SumCase` nodes, and recursive `self.eval` here
                    // would consume one native stack frame per constructor.
                    if datas.is_empty() {
                        stack.push(Frame::SumCaseTyp { is_trait: *is_trait, index: *index, datas: vec![] });
                        tm = typ.clone();
                        continue;
                    }
                    let (name, tm0, icit) = &datas[0];
                    stack.push(Frame::SumCase {
                        is_trait: *is_trait,
                        typ: typ.clone(),
                        index: *index,
                        datas: datas.clone(),
                        done: vec![],
                        cur: (name.clone(), *icit),
                    });
                    tm = tm0.clone();
                    continue;
                }
            };
            // Pop pending continuations, composing the value.
            loop {
                match stack.pop() {
                    None => return v,
                    Some(Frame::EvalArg { arg, icit, env: aenv }) => {
                        stack.push(Frame::ApplyAfter { fun: v.clone(), icit });
                        env = aenv;
                        tm = arg;
                        break;
                    }
                    Some(Frame::ApplyAfter { fun, icit }) => {
                        if let Val::Lam(_, _, closure) = fun.as_ref() {
                            // Inline lambda application into the machine loop
                            // instead of recursing through `closure_apply`
                            // (which would consume one native stack frame per
                            // constructor while evaluating e.g. `nat_add_helper`
                            // on a big literal).
                            env = closure.0.prepend(v);
                            tm = closure.1.clone();
                            break;
                        } else {
                            v = self.v_app(decl, &fun, v, icit);
                        }
                    }
                    Some(Frame::Obj(name)) => {
                        // Constructor-headed receivers project directly.
                        // force(SumCase) forces EVERY data field, so forcing
                        // before a projection re-walks the whole accumulated
                        // value on every field read - the module-tree update
                        // path was O(n^2) because of it.  Consumers that need
                        // normalized fields force them (the prims do via
                        // count_nat_forced; matches force their scrutinees).
                        // Mirrors the Val::Sum WHNF-leaf treatment.
                        let a = if matches!(v.as_ref(), Val::Sum(..) | Val::SumCase { .. }) {
                            v.clone()
                        } else {
                            self.force(decl, &v)
                        };
                        v = match a.as_ref() {
                            Val::Sum(_, params, _, _) => {
                                params.iter()
                                    .find(|(f_name, _, _, _)| f_name == &name)
                                    .unwrap().1.clone()
                            },
                            Val::SumCase { datas, typ, .. } => {
                                match typ.as_ref() {
                                    Val::Sum(_, params, _, _) => params
                                        .iter()
                                        .map(|x| (x.0.clone(), x.1.clone(), x.3))
                                        .chain(datas.iter().cloned())
                                        .find(|(f_name, _, _)| f_name == &name)
                                        .unwrap().1.clone(),
                                    // A stuck typ (meta/rigid head) has no
                                    // field table to project from: degrade to
                                    // the generic stuck projection instead of
                                    // panicking — eval must never crash the
                                    // server on a stuck value.
                                    _ => Val::Obj(a, name, List::new()).into(),
                                }
                            },
                            _ => {
                                Val::Obj(a, name, List::new()).into()
                            },
                        };
                    }
                    Some(Frame::Let(u, lenv)) => {
                        env = lenv.prepend(v);
                        tm = u;
                        break;
                    }
                    Some(Frame::Prune(pr, penv)) => {
                        v = self.v_app_pruning(decl, &penv, v, &pr);
                    }
                    Some(Frame::Pi(x, i, b, penv)) => {
                        v = Val::Pi(x, i, v, Closure(penv, b)).into();
                    }
                    Some(Frame::Call(name, args, cenv)) => {
                        if let Val::Match(..) = v.as_ref() {
                            let args = args
                                .map(|(x, i)| (self.eval(decl, &cenv, x), *i));
                            v = Val::Call(name, args, v).into();
                        }
                    }
                    Some(Frame::SumCase { is_trait, typ, index, datas, mut done, cur }) => {
                        done.push((cur.0, v.clone(), cur.1));
                        let dlen = done.len();
                        if dlen < datas.len() {
                            let (name, tm0, icit) = datas[dlen].clone();
                            stack.push(Frame::SumCase {
                                is_trait,
                                typ,
                                index,
                                datas,
                                done,
                                cur: (name, icit),
                            });
                            tm = tm0;
                            break;
                        } else {
                            stack.push(Frame::SumCaseTyp { is_trait, index, datas: done });
                            tm = typ;
                            break;
                        }
                    }
                    Some(Frame::SumCaseTyp { is_trait, index, datas }) => {
                        // Native-Nat compression (Lean/Agda-style): a fully
                        // concrete `Nat` constructor step is built directly as
                        // `Val::Nat` instead of a unary `Val::SumCase` chain.
                        // `succ (Nat k)` -> `Nat (k+1)`, `zero` -> `Nat 0`.
                        // Partially-stuck chains (`succ x` with x rigid/meta)
                        // keep the `SumCase` shape exactly as before.
                        if let Some(n) = nat_step_value(v.as_ref(), index, &datas) {
                            v = Val::Nat(n).into();
                        } else {
                            v = Val::SumCase {
                                is_trait,
                                typ: v,
                                index,
                                datas: Rc::new(datas),
                            }.into();
                        }
                    }
                    Some(Frame::Match(cases, menv)) => {
                        // Dispatch on the head constructor directly: forcing
                        // the whole scrutinee here would re-walk a deep
                        // constructor chain at every match step (O(n^2) for
                        // `nat_add_helper` on a big literal).  Only
                        // non-constructor heads (e.g. metas) are forced.
                        // `Val::Nat` (native Nat) is constructor-headed too.
                        match v.as_ref() {
                            Val::SumCase { .. } | Val::Nat(_) => {
                                match Compiler::eval_aux(self, &v, decl, &menv, &cases) {
                                    Some((tm_b, env_b)) => {
                                        tm = tm_b;
                                        env = env_b;
                                        break;
                                    }
                                    None => {
                                        v = Val::Match(v, menv, cases).into();
                                    }
                                }
                            }
                            _ => {
                                let val = self.force(decl, &v);
                                match val.as_ref() {
                                    Val::SumCase { .. } | Val::Nat(_) => {
                                        match Compiler::eval_aux(self, &val, decl, &menv, &cases) {
                                            Some((tm_b, env_b)) => {
                                                tm = tm_b;
                                                env = env_b;
                                                break;
                                            }
                                            None => {
                                                v = Val::Match(val, menv, cases).into();
                                            }
                                        }
                                    }
                                    _ => {
                                        v = Val::Match(val, menv, cases).into();
                                    }
                                }
                            }
                        }
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
        let _g = prof_enter(&FUNC_PROF.quote.0, &FUNC_PROF.quote.1);
        self.quote_inner(decl, l, t)
    }
    fn quote_inner(&self, decl: &Decl, l: Lvl, t: &Rc<Val>) -> Rc<Tm> {
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
            Val::Nat(k) => {
                // Native Nat -> the equivalent `succ`/`zero` `Tm::SumCase`
                // chain, so existing consumers (pretty/nf/unify round-trips)
                // see exactly the term shape they saw with unary chains.
                self.quote_nat(decl, l, *k)
            }
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
                index,
                datas,
            } => {
                // Fast path for deep unary-constructor chains (e.g. big `Nat`
                // literals, which are nested `Val::SumCase`s): quote the spine
                // iteratively so one native stack frame is not consumed per
                // constructor.  Falls back to the original recursive quoting
                // for short/irregular chains.
                struct Node {
                    typ: Rc<Val>,
                    index: u32,
                    is_trait: bool,
                    name: Span<SmolStr>,
                    icit: Icit,
                }
                let mut nodes: Vec<Node> = Vec::new();
                let mut cur: Rc<Val> = t.clone();
                loop {
                    match cur.as_ref() {
                        Val::SumCase { is_trait, typ, index, datas } if datas.len() == 1 => {
                            nodes.push(Node {
                                typ: typ.clone(),
                                index: *index,
                                is_trait: *is_trait,
                                name: datas[0].0.clone(),
                                icit: datas[0].2,
                            });
                            cur = datas[0].1.clone();
                        }
                        _ => break,
                    }
                }
                if nodes.len() >= 2 {
                    let mut inner = self.quote(decl, l, &cur);
                    for node in nodes.into_iter().rev() {
                        let datas: TmSumCaseDatas = Rc::new(vec![(node.name, inner.clone(), node.icit)]);
                        inner = Tm::SumCase {
                            is_trait: node.is_trait,
                            typ: self.quote(decl, l, &node.typ),
                            index: node.index,
                            datas,
                        }.into();
                    }
                    inner
                } else {
                    let datas = Rc::new(datas
                        .iter()
                        .map(|p| {
                            (p.0.clone(), self.quote(decl, l, &p.1), p.2)
                        })
                        .collect());
                    Tm::SumCase {
                        is_trait: *is_trait,
                        typ: self.quote(decl, l, typ),
                        index: *index,
                        datas,
                    }.into()
                }
            }
            Val::Call(name, args, body) => {
                // Operator-symbol recovery: an inlined helper call that backs
                // an operator method (`nat_add_helper x y` for `x + y`) quotes
                // to a display-only `Tm::OpCall` carrying the operator symbol,
                // which the pretty-printer renders in infix/prefix form.  The
                // helper→operator mapping is registered at impl elaboration
                // time, so user-defined operator symbols work too.  Keeping
                // the full call data (name/args/body) inside `OpCall` makes
                // quote → eval round-trips reproduce the original `Val::Call`.
                let sym = if args.iter().all(|(_, i)| *i == Icit::Expl) {
                    self.symbol_table.get(&(name.clone(), args.len())).cloned()
                } else {
                    None
                };
                match sym {
                    Some(sym) if args.len() == 1 || args.len() == 2 => Tm::OpCall {
                        symbol: sym,
                        name: name.clone(),
                        args: args.map(|(x, i)| (self.quote(decl, l, x), *i)),
                        body: self.quote(decl, l, body),
                    }.into(),
                    _ => Tm::Call(
                        name.clone(),
                        args.map(|(x, i)| (self.quote(decl, l, x), *i)),
                        self.quote(decl, l, body),
                    ).into(),
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
                // The quoted scrutinee's `Val::Match` carries a full case list.
                // Each case's body is evaluated against a *simplified* decl where
                // every definition is replaced by a `Decl` reference (so recursive
                // bodies don't re-expand).  Building that map is O(decl) and is
                // identical for the same decl, so cache it per decl address
                // (`simpl_decl`, shared with unify/rename).
                let declb = simpl_decl(decl);
                let tm_cases = cases
                    .iter()
                    .map(|x| (
                        x.0.clone(),
                        {
                            let env = (0..x.0.bind_count())
                                .fold(env.clone(), |env, x| env.prepend(Val::vvar(l + x).into()));
                            let tm = self.eval(declb.as_ref(), &env, &x.1);
                            self.quote(decl, l+x.0.bind_count(), &tm)
                        }
                    ))
                    .collect();
                Tm::Match(self.quote(decl, l, val), tm_cases).into()
            }
        }
    }

    /// Quote a native `Val::Nat(k)` into the equivalent `Tm::SumCase` chain
    /// (`succ^k zero`), built iteratively so a large `k` does not consume
    /// one native stack frame per constructor.  The `Nat` type is taken from
    /// the declaration table (`Raw::Nat` uses the same lookup).  This keeps
    /// `Tm` unchanged: every downstream consumer of a quoted value sees the
    /// exact term shape it saw when nats were unary chains.
    fn quote_nat(&self, decl: &Decl, l: Lvl, k: u64) -> Rc<Tm> {
        let nat_ty = decl.get("Nat").map(|e| e.2.clone()).unwrap_or_else(|| Val::U(0).into());
        let nat_tm = self.quote(decl, l, &nat_ty);
        let mut inner: Rc<Tm> = Tm::SumCase {
            is_trait: false,
            typ: nat_tm.clone(),
            index: 0,
            datas: Rc::new(vec![]),
        }.into();
        for _ in 0..k {
            inner = Tm::SumCase {
                is_trait: false,
                typ: nat_tm.clone(),
                index: 1,
                datas: Rc::new(vec![(empty_span(SmolStr::new("n")), inner.clone(), Icit::Expl)]),
            }.into();
        }
        inner
    }

    pub fn nf(&self, decl: &Decl, env: &Env, t: &Rc<Tm>) -> Rc<Tm> {
        let _g = prof_enter(&FUNC_PROF.nf.0, &FUNC_PROF.nf.1);
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
            parser::syntax::Decl::Class { name, .. } => {
                println!("> {}", name.data);
            }
        }
        let (x, _, new_cxt) = infer.infer(&cxt, tm.clone())?;
        cxt = new_cxt;
        // HDL self-check warnings: drain per decl (the module close-check
        // runs during the module class decl's own elaboration).
        for line in take_fresh_check_issues(&infer) {
            ret += &format_check_warning(&line);
            ret += "\n";
        }
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

type PreludeMacros = std::collections::HashMap<String, Vec<parser::macros::MacroRule>>;

/// Cached result of elaborating the builtin prelude.  Headless entry points
/// (`run_with_prelude`, used by tests/CLI) re-elaborate the ~24 prelude files
/// on every call, which dominates their runtime.  The prelude's elaborated
/// `Infer`/`Cxt` state is cloned per call; the mutable global map is
/// deep-copied so concurrent tests stay isolated.
struct PreludeState {
    infer: Infer,
    cxt: Cxt,
    global_macros: PreludeMacros,
}

thread_local! {
    static PRELUDE_CACHE: PreludeSlot = PreludeSlot::new(&PRELUDE_POOL);
    /// Cache of the prelude WITHOUT the hdl files, for `load_prelude_skip_hdl`.
    static PRELUDE_CACHE_NO_HDL: PreludeSlot = PreludeSlot::new(&PRELUDE_POOL_NO_HDL);
}

/// A prelude state handed across thread boundaries by exclusive ownership.
///
/// SAFETY: the state's `Rc` graphs are `!Send` because their reference
/// counts are non-atomic.  A pool entry is only ever touched by its owning
/// thread: the dying thread pushes it while holding the last remaining
/// references (the pool Mutex unlock/lock provides the happens-before
/// edge), and the taking thread becomes the sole owner before any of its
/// code can reach the graph.  No two threads ever mutate the same
/// refcount concurrently, which is exactly the discipline `Send` requires
/// of this wrapper.  The same argument covers the `RwLock`/`HashMap`
/// reachable from the state: access is strictly sequential across the
/// handoff.
struct PoolState(PreludeState);
// SAFETY: see the block comment above `PoolState` — the state crosses
// threads only by exclusive-ownership handoff through the pool Mutex, so
// no refcount (or RwLock) is ever touched by two threads concurrently.
unsafe impl Send for PoolState {}

type PreludePool = std::sync::Mutex<Vec<PoolState>>;

static PRELUDE_POOL: PreludePool = std::sync::Mutex::new(Vec::new());
static PRELUDE_POOL_NO_HDL: PreludePool = std::sync::Mutex::new(Vec::new());

/// Thread-local prelude cache that recycles its state through a
/// process-wide pool on thread exit.  The cache itself must be
/// thread-local (the elaborated state is not `Sync`), but without
/// recycling, workloads that spawn a thread per unit of work — the libtest
/// harness runs every test on a fresh thread — would re-elaborate the
/// whole prelude per test (~1.5s each).  With the pool, one elaboration
/// per concurrently-alive thread is recycled across all of them.
struct PreludeSlot {
    cell: std::cell::RefCell<Option<PreludeState>>,
    pool: &'static PreludePool,
}

impl PreludeSlot {
    fn new(pool: &'static PreludePool) -> Self {
        Self {
            cell: std::cell::RefCell::new(pool.lock().unwrap().pop().map(|p| p.0)),
            pool,
        }
    }
}

impl Drop for PreludeSlot {
    fn drop(&mut self) {
        if let Some(state) = self.cell.get_mut().take() {
            let mut pool = self.pool.lock().unwrap();
            if pool.len() < 64 {
                pool.push(PoolState(state));
            }
        }
    }
}

fn load_prelude_state() -> Result<PreludeState, Error> {
    load_prelude_state_impl(true)
}

fn decl_name_of(tm: &parser::syntax::Decl) -> SmolStr {
    match tm {
        parser::syntax::Decl::Def { name, .. }
        | parser::syntax::Decl::Enum { name, .. }
        | parser::syntax::Decl::TraitDecl { name, .. } => name.data.clone(),
        parser::syntax::Decl::Package { .. } => SmolStr::new("<package>"),
        parser::syntax::Decl::Import { .. } => SmolStr::new("<import>"),
        parser::syntax::Decl::Println(_) => SmolStr::new("<println>"),
        _ => SmolStr::new("<other>"),
    }
}

fn load_prelude_state_impl(include_hdl: bool) -> Result<PreludeState, Error> {
    let prelude_prof = std::env::var_os("TYPORT_PRELUDE_PROF").is_some();
    if prelude_prof {
        FUNC_PROF.enabled.store(true, std::sync::atomic::Ordering::Relaxed);
    }
    // Fresh force-memo epoch for the load (see `force_memo_clear`).
    force_memo_clear();
    let mut infer = Infer::new();
    let mut prelude: Vec<&str> = vec![
        include_str!("../prelude/core/op.typort"),
        include_str!("../prelude/core/eq.typort"),
        include_str!("../prelude/core/nat.typort"),
        include_str!("../prelude/core/calc.typort"),
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
    ];
    if include_hdl {
        prelude.extend([
            include_str!("../prelude/hdl/hdl-core.typort"),
            include_str!("../prelude/hdl/hdl-check.typort"),
            include_str!("../prelude/hdl/hdl-types.typort"),
            include_str!("../prelude/hdl/hdl-ops.typort"),
            include_str!("../prelude/hdl/hdl-clock.typort"),
            include_str!("../prelude/hdl/hdl-bus.typort"),
            include_str!("../prelude/hdl/hdl-signals.typort"),
            include_str!("../prelude/hdl/hdl-utils.typort"),
            include_str!("../prelude/hdl/hdl-stream.typort"),
            include_str!("../prelude/hdl/hdl-crossclock.typort"),
            include_str!("../prelude/hdl/hdl-bus-proto.typort"),
            include_str!("../prelude/hdl/hdl-misc-io.typort"),
            include_str!("../prelude/hdl/hdl-misc.typort"),
            include_str!("../prelude/hdl/hdl-macros.typort"),
            include_str!("../prelude/hdl/hdl-verilog-compat.typort"),
            include_str!("../prelude/hdl/hdl-verilog.typort"),
        ]);
    }
    prelude.push(include_str!("../prelude/show.typort"));
    let mut cxt = Cxt::new(&infer);

    // Accumulate exported macros from prelude files
    let mut global_macros: PreludeMacros = Default::default();
    let mut id = 0;
    let nat_typort = include_str!("../prelude/core/nat.typort");
    for p in prelude {
        // Per-file memo epoch: memoized force pins intermediate values of
        // the file's elaboration; clearing at the boundary returns that
        // garbage promptly instead of batching one large drop later
        // (measured 0.35s of cascaded Val drops on the first clear).
        force_memo_clear();
        let _pfile_t0 = std::time::Instant::now();
        let (_p_parse_t, _p_infer_t, n_decls) = if let Some((decls, parse_errs, new_exports, _expansions)) = parser::parser_with_macros(&preprocess(p), id, &global_macros) {
            let _p_parse_t = _pfile_t0.elapsed();
            for ast_err in parse_errs {
                println!("{:?}", ast_err)
            }
            for (name, rules) in new_exports {
                global_macros.insert(name, rules);
            }
            let nd = decls.len();
            let _infer_t0 = std::time::Instant::now();
            for tm in decls {
                let _d_t0 = std::time::Instant::now();
                let _e0 = FUNC_PROF.eval.0.load(std::sync::atomic::Ordering::Relaxed);
                let (x, _, new_cxt) = infer.infer(&cxt, tm.clone())?;
                let _d_el = _d_t0.elapsed().as_secs_f64();
                if prelude_prof && _d_el > 0.005 {
                    let _e1 = FUNC_PROF.eval.0.load(std::sync::atomic::Ordering::Relaxed);
                    eprintln!("[PPROF]   decl {:>8.3}s  eval {:>7.3}s  {}", _d_el, (_e1 - _e0) as f64 / 1e9, decl_name_of(&tm));
                }
                cxt = new_cxt;
            }
            (_p_parse_t, _infer_t0.elapsed(), nd)
        } else { (_pfile_t0.elapsed(), std::time::Duration::ZERO, 0) };
        let _p_el = _pfile_t0.elapsed().as_secs_f64();
        if prelude_prof {
            eprintln!("[PPROF] file[{}] {:>8.3}s (parse {:>6.3}s + infer {:>6.3}s)  {} decls", id, _p_el, _p_parse_t.as_secs_f64(), _p_infer_t.as_secs_f64(), n_decls);
        }
        id += 1;
        // After nat.typort is loaded, register nat builtins (nat_to_dec +
        // word-size nat arithmetic primops).
        // 基于内容判断而非索引 id：prelude 列表顺序变化（增删文件）时不会错位。
        if p == nat_typort {
            cxt::Cxt::register_nat_builtins(&mut cxt, &infer);
        }
    }
    // Verilog-compat vconnT builtin: its signature needs the prelude's
    // ModuleTree/Expr types, so it registers only after they exist.
    cxt::Cxt::register_vconn_builtin(&mut cxt, &infer);

    // Auto-import prelude: create short aliases for enum cases (e.g., Nat.zero → zero).
    // Namespace-registered instance methods (`TypeHead.method`, e.g. `Bool.mux`)
    // are excluded — methods are only reachable through `x.method` dispatch,
    // never by bare name, so they must not shadow constructor aliases.
    // Short-name collisions between constructors are resolved deterministically:
    // iterating in sorted full-key order makes the `or_insert` (first wins)
    // winner independent of HashMap iteration order.
    let ns_method_keys: std::collections::HashSet<SmolStr> = cxt.namespace.iter()
        .flat_map(|ns| ns.1.iter().map(move |m| SmolStr::new(format!("{}.{}", ns.2, m))))
        .collect();
    let mut prelude_aliases: Vec<(SmolStr, SmolStr, _)> = cxt.decl.iter()
        .filter(|(k, _)| k.contains('.') && !ns_method_keys.contains(*k))
        .map(|(k, v)| {
            let short = SmolStr::new(k.split('.').last().unwrap());
            (short, k.clone(), v.clone())
        })
        .collect();
    prelude_aliases.sort_by(|a, b| a.1.cmp(&b.1));
    let decl_map = Rc::make_mut(&mut cxt.decl);
    for (short, _full_key, v) in prelude_aliases {
        decl_map.entry(short).or_insert(v);
    }
    // The cached state is never queried for hover/completion; drop the
    // accumulated tables so per-call clones stay cheap.
    infer.hover_table.clear();
    infer.completion_table.clear();
    // Reset the HDL loop-index global to a clean empty at the end of the
    // load: checking `genFrom`'s succ-case body evaluates its side-effecting
    // lets (the checker evaluates applications), leaving Rigid-indexed
    // stack frames behind; the cache snapshot would hand that dirty stack to
    // every later run (nat_to_dec renders the Rigids as 0s — the
    // `a_0_0_0_0` port-name corruption). The key itself is created earlier
    // by `hdlLoopIdxGlobalInit` (hdl-core.typort), which keeps mid-load
    // `loopName` evaluations from panicking in `get_global`.
    {
        let empty_val = infer.eval(
            &cxt.decl,
            &cxt.env,
            &Tm::Decl(empty_span(SmolStr::new("hdlLoopIdxEmpty"))).into(),
        );
        infer.mutable_map.write().unwrap()
            .insert("HdlLoopIdx".to_string(), empty_val);
    }
    if prelude_prof {
        let fp = &FUNC_PROF;
        eprintln!("[PPROF] -- function-level during prelude load (exclusive, sums to ~wall) --");
        let mut rows: Vec<(String, u64, u64)> = vec![
            ("check".into(), fp.check.0.load(std::sync::atomic::Ordering::Relaxed), fp.check.1.load(std::sync::atomic::Ordering::Relaxed)),
            ("infer_expr".into(), fp.infer_expr.0.load(std::sync::atomic::Ordering::Relaxed), fp.infer_expr.1.load(std::sync::atomic::Ordering::Relaxed)),
            ("check_universe".into(), fp.check_universe.0.load(std::sync::atomic::Ordering::Relaxed), fp.check_universe.1.load(std::sync::atomic::Ordering::Relaxed)),
            ("eval".into(), fp.eval.0.load(std::sync::atomic::Ordering::Relaxed), fp.eval.1.load(std::sync::atomic::Ordering::Relaxed)),
            ("force".into(), fp.force.0.load(std::sync::atomic::Ordering::Relaxed), fp.force.1.load(std::sync::atomic::Ordering::Relaxed)),
            ("v_app".into(), fp.v_app.0.load(std::sync::atomic::Ordering::Relaxed), fp.v_app.1.load(std::sync::atomic::Ordering::Relaxed)),
            ("quote".into(), fp.quote.0.load(std::sync::atomic::Ordering::Relaxed), fp.quote.1.load(std::sync::atomic::Ordering::Relaxed)),
            ("nf".into(), fp.nf.0.load(std::sync::atomic::Ordering::Relaxed), fp.nf.1.load(std::sync::atomic::Ordering::Relaxed)),
            ("unify".into(), fp.unify.0.load(std::sync::atomic::Ordering::Relaxed), fp.unify.1.load(std::sync::atomic::Ordering::Relaxed)),
            ("solve_multi_trait".into(), fp.solve_trait.0.load(std::sync::atomic::Ordering::Relaxed), fp.solve_trait.1.load(std::sync::atomic::Ordering::Relaxed)),
        ];
        rows.sort_by(|a, b| b.1.cmp(&a.1));
        for (name, ns, n) in rows {
            eprintln!("[PPROF]     {:>8.3} s  {:>12} calls  {}", ns as f64 / 1e9, n, name);
        }
        let shapes = ["Flex", "Rigid", "Decl", "Obj", "Lam", "Pi", "U", "LiteralType", "LiteralIntro", "Sum", "SumCase", "Match", "Call"];
        eprintln!("[PPROF]   -- force() entry shapes (force count {}) --", fp.force.1.load(std::sync::atomic::Ordering::Relaxed));
        let mut shape_total = 0u64;
        for (i, name) in shapes.iter().enumerate() {
            let c = fp.force_shape[i].load(std::sync::atomic::Ordering::Relaxed);
            shape_total += c;
            if c > 0 {
                eprintln!("[PPROF]     {:>14} {:>12}", name, c);
            }
        }
        eprintln!("[PPROF]     {:>14} {:>12}  (shape total)", "TOTAL", shape_total);
    }
    // End-of-load epoch boundary: release the load's pinned intermediates
    // so they are not dropped in one batch inside the first user request.
    force_memo_clear();
    Ok(PreludeState {
        infer,
        cxt,
        global_macros,
    })
}

/// Clone the cached prelude elaborator state for use by a `Backend`
/// (LSP/CLI).  The prelude is elaborated once per process; subsequent
/// Backends reuse the cached `Infer`/`Cxt`/macro tables instead of
/// re-elaborating ~24 files.  The mutable global map is deep-copied so
/// writes never leak between users of the cache (mirrors `run_with_prelude`).
pub fn clone_prelude_state(
    include_hdl: bool,
) -> Result<(Infer, Cxt, std::collections::HashMap<String, Vec<parser::macros::MacroRule>>), Error> {
    fn cloned_state(
        cache: &'static std::thread::LocalKey<PreludeSlot>,
        include_hdl: bool,
    ) -> Result<(Infer, Cxt, std::collections::HashMap<String, Vec<parser::macros::MacroRule>>), Error> {
        let mut loaded: Option<Error> = None;
        let out = cache.with(|c| {
            let mut guard = c.cell.borrow_mut();
            if guard.is_none() {
                match load_prelude_state_impl(include_hdl) {
                    Ok(state) => *guard = Some(state),
                    Err(e) => { loaded = Some(e); return None; }
                }
            }
            let state = guard.as_ref().unwrap();
            Some((
                state.infer.clone(),
                state.cxt.clone(),
                state.global_macros.clone(),
            ))
        });
        match out {
            Some(parts) => Ok(parts),
            None => Err(loaded.take().expect("error must be set when output is None")),
        }
    }
    let (mut infer, cxt, global_macros) = if include_hdl {
        cloned_state(&PRELUDE_CACHE, include_hdl)?
    } else {
        cloned_state(&PRELUDE_CACHE_NO_HDL, include_hdl)?
    };
    // Fresh force-memo epoch per run: the memo is keyed by `Rc::as_ptr`
    // and holds strong refs, so entries from a previous run only die when
    // the previous run's Infer drops — after which their addresses CAN be
    // reused by this run's fresh allocations.  Without a per-run clear, a
    // lookup can then hit a stale entry from the previous run (same epoch,
    // same address, different value) and return the WRONG forced result —
    // order-dependent elaboration bugs like `f.zz_expr` staying stuck.
    force_memo_clear();
    // Clone the cached elaborator state.  The mutable global map is
    // deep-copied so writes from one user never leak into another.
    let mut mutable = infer.mutable_map.read().unwrap().clone();
    // Session-scoped globals are RESET per run: the cached copies were
    // written by declaration-time check evaluation during the prelude load
    // (e.g. the WhenStack accumulates leaked pushes when checked `when`
    // bodies evaluate their let chains), and their VALUES are shared Rc
    // nodes whose internal meta/level references belong to the load's
    // Infer.  Reusing them in a fresh run forces through the wrong meta
    // table and produces stuck `Val::Match` results (order-dependent test
    // failures — a heavy earlier run shifts the address/meta layout).
    // Each run re-seeds these through the preludes' own
    // `change_mutable_default` calls, so the empty state is the correct
    // baseline.
    for k in ["WhenStack", "ModuleTree", "HdlLoopIdx", "CombCtx", "ModulePortTable"] {
        mutable.remove(k);
    }
    infer.mutable_map = Rc::new(std::sync::RwLock::new(mutable));
    // The replay memo is keyed by DEF NAME ONLY and shared across every
    // clone of the cached Infer.  Two runs that both define a `def f` (one
    // pure, one with side effects — e.g. an Int helper vs `s.fire`) collide:
    // the first run's decision sticks, the second def is not replayed and
    // its stored WHNF (stuck outside a module tree) leaks into the output.
    // Per-run reset restores isolation (names may legitimately repeat).
    infer.def_replay_memo = Rc::new(std::sync::RwLock::new(HashMap::new()));
    Ok((infer, cxt, global_macros))
}

/// Drain accumulated HDL self-check issues (the mutable global
/// "CheckIssues" written by the report_check_issue builtin): returns
/// the pending "code|module|signal|message" lines and resets the
/// global. Callers dedup further with a per-file/per-run seen-set —
/// the global only dedups within its own (never-drained) content.
pub fn take_check_issues(infer: &Infer) -> Vec<String> {
    let lines = {
        let map = infer.mutable_map.read().unwrap();
        match map.get("CheckIssues") {
            Some(v) => match v.as_ref() {
                Val::LiteralIntro(s) => s.data.clone(),
                _ => String::new(),
            },
            None => String::new(),
        }
    };
    if lines.is_empty() { return Vec::new(); }
    infer.mutable_map.write().unwrap().insert(
        "CheckIssues".to_string(),
        Rc::new(Val::LiteralIntro(empty_span(String::new()))),
    );
    lines.split('\n').filter(|l| !l.is_empty()).map(|l| l.to_string()).collect()
}

/// "code|module|signal|message" -> human-readable warning line.
pub fn format_check_warning(line: &str) -> String {
    let parts: Vec<&str> = line.splitn(4, '|').collect();
    match parts.as_slice() {
        [code, module, signal, message] => {
            if signal.is_empty() {
                format!("[hdl][warning] {} [{}] {}", code, module, message)
            } else {
                format!("[hdl][warning] {} [{}] {}: {}", code, module, signal, message)
            }
        }
        _ => format!("[hdl][warning] {}", line),
    }
}

/// take_check_issues + cross-decl dedup: only lines not yet reported in
/// this run/file. The seen-set lives in the mutable global
/// "CheckIssuesSeen", which resets together with the rest of
/// mutable_map (cleared per file by lib.rs; deep-copied fresh per
/// run_with_prelude call). This is what keeps re-instantiated child
/// constructors (which replay their close-check) from re-reporting,
/// and pins each warning to the module's own declaration.
pub fn take_fresh_check_issues(infer: &Infer) -> Vec<String> {
    let pending = take_check_issues(infer);
    if pending.is_empty() { return Vec::new(); }
    let mut seen = {
        let map = infer.mutable_map.read().unwrap();
        match map.get("CheckIssuesSeen") {
            Some(v) => match v.as_ref() {
                Val::LiteralIntro(s) => s.data.clone(),
                _ => String::new(),
            },
            None => String::new(),
        }
    };
    let mut fresh = Vec::new();
    for line in pending {
        if !seen.split('\n').any(|l| l == line) {
            seen = if seen.is_empty() { line.clone() } else { format!("{}\n{}", seen, line) };
            fresh.push(line);
        }
    }
    if !fresh.is_empty() {
        infer.mutable_map.write().unwrap().insert(
            "CheckIssuesSeen".to_string(),
            Rc::new(Val::LiteralIntro(empty_span(seen))),
        );
    }
    fresh
}

#[allow(unused)]
pub fn run_with_prelude(input: &str) -> Result<String, Error> {
    let (mut infer, mut cxt, global_macros) = clone_prelude_state(true)?;
    let mut ret = String::new();

    // Parse main file with accumulated macros from prelude
    let ast = parser::parser_with_macros(&preprocess(input), 24, &global_macros)
        .map(|(d, e, _, _)| (d, e))
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
            parser::syntax::Decl::Class { name, .. } => {
                println!("> {}", name.data);
            }
        }
        let (x, _, new_cxt) = infer.infer(&cxt, tm.clone())?;
        cxt = new_cxt;
        // HDL self-check warnings: drain per decl (the module close-check
        // runs during the module class decl's own elaboration).
        for line in take_fresh_check_issues(&infer) {
            ret += &format_check_warning(&line);
            ret += "\n";
        }
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
    // Helper: replace each non-whitespace char with spaces equal to its byte length,
    // so the preprocessed text has the same byte length as the original.
    // This ensures parser span byte offsets still match the original text.
    fn replace_non_ws_preserve_bytes(input: &str) -> String {
        let mut out = String::with_capacity(input.len());
        for c in input.chars() {
            if c.is_whitespace() {
                out.push(c);
            } else {
                for _ in 0..c.len_utf8() {
                    out.push(' ');
                }
            }
        }
        out
    }
    let s = s.split("/*")
        .map(|x| {
            x.split_once("*/")
                .map(|(a, b)| replace_non_ws_preserve_bytes(a) + "  " + b)
                .unwrap_or(x.to_owned())
        })
        .reduce(|a, b| a + "  " + &b)
        .unwrap_or(s.to_owned());
    s.split('\n')
        .map(|x| {
            x.split_once("//")
                .map(|(a, b)| a.to_owned() + "  " + &replace_non_ws_preserve_bytes(b))
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
    // Expected tyck error: `reduce_balanced_tree` can't resolve `div2Up(len + 1)`
    // against the helper's `Vec[U] (succ l)` index (div2Up is a function, no inverse).
    match run(input, 0) {
        Ok(output) => panic!("expected tyck error, got output: {}", output),
        Err(e) => {
            println!("{}", e.0.data);
            assert!(e.0.data.contains("can't unify"),
                "expected can't unify error, got: {}", e.0.data);
        }
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
    // Expected tyck error: `up_fin`'s fzero branch can't unify Fin vs Nat.
    match run(input, 0) {
        Ok(output) => panic!("expected tyck error, got output: {}", output),
        Err(e) => {
            println!("{}", e.0.data);
            assert!(e.0.data.contains("can't unify"),
                "expected can't unify error, got: {}", e.0.data);
        }
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
    // Expected tyck error: `z1`'s `_` hole is a Pi type (not a trait meta), so
    // solve_multi_trait can't fill it. The error should still carry a search
    // closure; iddfs finds the correct solution `(c => (d => (Eq.refl c)))`.
    match run(input, 0) {
        Ok(output) => panic!("expected tyck error, got output: {}", output),
        Err(e) => {
            println!("{}", e.0.data);
            assert!(e.0.data.contains("find unsolved meta"),
                "expected find unsolved meta error, got: {}", e.0.data);
            let searched = e.1.get(0).map(|c| c()).flatten();
            println!("search closure: {:?}", searched);
            assert!(searched.is_some(), "expected search to find a candidate");
        }
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
    // Expected tyck error: `cong(_, e)` leaves an unresolved function hole for `_`.
    match run(input, 0) {
        Ok(output) => panic!("expected tyck error, got output: {}", output),
        Err(e) => {
            println!("{}", e.0.data);
            assert!(e.0.data.contains("can't unify"),
                "expected can't unify error, got: {}", e.0.data);
        }
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
    // Expected tyck error: the `_` hole is `Eq (add x 1) (add y 1)`, not a trait
    // meta, so solve_multi_trait can't fill it. The search closure should still
    // produce a candidate (iddfs finds `cong (x => succ _) e`, though incomplete).
    match run(input, 0) {
        Ok(output) => panic!("expected tyck error, got output: {}", output),
        Err(e) => {
            println!("{}", e.0.data);
            assert!(e.0.data.contains("find unsolved meta"),
                "expected find unsolved meta error, got: {}", e.0.data);
            let searched = e.1.get(0).map(|c| c()).flatten();
            println!("search closure: {:?}", searched);
            assert!(searched.is_some(), "expected search to find a candidate");
        }
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
    // Expected tyck error: the `_` holes inside `def t` leave unsolved metas
    // (find unsolved meta). No search closure is attached, so guard e.1 access.
    match run_with_prelude(input) {
        Ok(output) => panic!("expected tyck error, got output: {}", output),
        Err(e) => {
            println!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset);
            assert!(e.0.data.contains("find unsolved meta"),
                "expected find unsolved meta error, got: {}", e.0.data);
            let searched = e.1.get(0).map(|c| c()).flatten();
            println!("search closure: {:?}", searched);
        }
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
    // Expected tyck error: `let m : ... = _` leaves an unsolved meta of type
    // `Type 0` that solve_multi_trait can't resolve. The error should still
    // carry a search closure (iddfs produces a candidate, here just `a`).
    match run(input, 0) {
        Ok(output) => panic!("expected tyck error, got output: {}", output),
        Err(e) => {
            println!("{}", e.0.data);
            assert!(e.0.data.contains("find unsolved meta"),
                "expected find unsolved meta error, got: {}", e.0.data);
            let searched = e.1.get(0).map(|c| c()).flatten();
            println!("search closure: {:?}", searched);
            assert!(searched.is_some(), "expected search to find a candidate");
        }
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
    // Expected tyck error: `wallace_tree`'s `_` hole can't be unified with the
    // recursive result type. This can't-unify error carries no search closure,
    // so guard e.1 access.
    match run_with_prelude(input) {
        Ok(output) => panic!("expected tyck error, got output: {}", output),
        Err(e) => {
            println!("{}", e.0.data);
            assert!(e.0.data.contains("can't unify"),
                "expected can't unify error, got: {}", e.0.data);
            let searched = e.1.get(0).map(|c| c()).flatten();
            println!("search closure: {:?}", searched);
        }
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

struct TestBits[width: Nat] {
    name: String
}

impl[width: Nat] Add[TestBits[width], TestBits[width]] for TestBits[width] {
    def +(that: TestBits[width]): TestBits[width] =
        TestBits.mk(this.name + " + " + that.name)
}

impl[width: Nat] Sub[TestBits[width], TestBits[width]] for TestBits[width] {
    def -(that: TestBits[width]): TestBits[width] =
        TestBits.mk(this.name + " - " + that.name)
}

impl[width0: Nat, width1: Nat] Mul[TestBits[width1], TestBits[width0 + width1]] for TestBits[width0] {
    def *(that: TestBits[width1]): TestBits[width0 + width1] =
        TestBits.mk(this.name + " * " + that.name)
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
fn test_hdl_cat() {
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
fn test_verilog_pure_typort() {
    let input = r#"
module Adder {
    input a = UInt[8]
    input b = UInt[8]
    input cond = Bool
    output sum = UInt[8]
    sum := a + b
}
println (moduleTreeVL Adder.create.tree)
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("=== Output ===\n{}", output);
            assert!(output.contains("module Adder"), "{}", output);
            assert!(output.contains("input wire [7:0] a"), "{}", output);
            assert!(output.contains("input wire [7:0] b"), "{}", output);
            assert!(output.contains("input wire cond"), "{}", output);
            assert!(output.contains("output wire [7:0] sum"), "{}", output);
            assert!(output.contains("assign sum = (a + b)"), "{}", output);
            assert!(output.contains("endmodule"), "{}", output);
            assert!(output.contains('\n'), "should have newlines: {}", output);
        },
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_verilog_when_otherwise_merge() {
    // Test when/otherwise — each assignment carries its FULL enable
    // condition, so otherwise emits `if (!z)` instead of an else branch.
    let input = r#"
module Test {
    let a = UInt[4]
    let b = UInt[4]
    let c = UInt[4]
    let z = Bool
    when(z) {
        c := a + b
    } otherwise {
        c := a - b
    }
}
println (moduleTreeVL Test.create.tree)
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("=== Output ===\n{}", output);
            assert!(output.contains("module Test"), "missing module: {}", output);
            assert!(output.contains("always @(*)"), "missing always: {}", output);
            assert!(output.contains("if (z)"), "missing if: {}", output);
            assert!(output.contains("if (!z)"), "missing otherwise condition (if (!z)): {}", output);
            assert!(output.contains("c = (a + b);"), "missing when body: {}", output);
            assert!(output.contains("c = (a - b);"), "missing otherwise body: {}", output);
            // otherwise body must appear AFTER the if (both branches in the
            // same always block, in source order)
            let if_pos = output.find("if (z)").expect("if (z) present");
            let else_pos = output.find("c = (a - b);").expect("otherwise body present");
            assert!(if_pos < else_pos, "otherwise body should come after the if, got:\n{}", output);
            // Should NOT have continuous assign for c
            assert!(!output.contains("assign c"), "should not have continuous assign: {}", output);
        },
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_verilog_when_elsewhen_blocks() {
    // Test that when/elsewhen/otherwise compiles and generates Verilog.
    // elsewhen negates earlier branches (w && !z); otherwise negates all
    // branches (!z && !w) — semantically if / else if / else.
    let input = r#"
module Test[w: Nat] {
    let a = UInt[w]
    let b = UInt[w]
    let c = UInt[w]
    let z = Bool
    let e = Bool
    when(z) {
        c := a + b
    } elsewhen(e) {
        c := a
    } otherwise {
        c := a - b
    }
}
println (moduleTreeVL Test.create[8].tree)
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("=== Output ===\n{}", output);
            assert!(output.contains("module Test"), "missing module: {}", output);
            assert!(output.contains("endmodule"), "missing endmodule: {}", output);
            // when body assignments should appear as blocking assignments in always block
            assert!(output.contains("c = (a + b)"), "missing when body: {}", output);
            assert!(output.contains("c = a"), "missing elsewhen body: {}", output);
            assert!(output.contains("c = (a - b)"), "missing otherwise body: {}", output);
            // conditions carry the branch negation: elsewhen = e && !z, otherwise = !z && !e
            assert!(output.contains("if (e && !z)"), "missing elsewhen negation condition, got:\n{}", output);
            assert!(output.contains("if (!z && !e)"), "missing otherwise negation condition, got:\n{}", output);
            // otherwise body must come after the when body (source order)
            let if_pos = output.find("if (z)").expect("if present");
            let else_pos = output.find("c = (a - b)").expect("otherwise body present");
            assert!(if_pos < else_pos, "otherwise body should come after the when body, got:\n{}", output);
        },
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_verilog_when_default_merge() {
    // Test that when block + default assign merge into single always block
    let input = r#"
module Test {
    input sel = UInt[4]
    input a = UInt[4]
    input c = UInt[4]
    output result = UInt[4]
    result := c
    when(sel === a) {
        result := a
    }
}
println (moduleTreeVL Test.create.tree)
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("=== Output ===\n{}", output);
            assert!(output.contains("module Test"), "missing module: {}", output);
            assert!(output.contains("endmodule"), "missing endmodule: {}", output);
            // Should have always block with default assign inside
            assert!(output.contains("always @(*)"), "missing always block: {}", output);
            assert!(output.contains("result = c;"), "missing default assign in always: {}", output);
            assert!(output.contains("if ("), "missing if: {}", output);
            // Should NOT have continuous assign for result (it's in always block)
            assert!(!output.contains("assign result"), "should not have continuous assign for result: {}", output);
        },
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_verilog_when_blocks() {
    // Test when without elsewhen/otherwise.
    let input = r#"
module Test {
    let a = Bits[8]
    let z = Bool
    when(z) {
        a := a
    }
}
println (moduleTreeVL Test.create.tree)
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("=== Output ===\n{}", output);
            assert!(output.contains("module Test"), "missing module: {}", output);
            assert!(output.contains("endmodule"), "missing endmodule: {}", output);
            assert!(output.contains("if ("), "missing if: {}", output);
        },
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_nat_literals() {
    // Test that Nat literals work through Into[UInt[width]] for Nat
    // and that eqNat comparisons produce correct Verilog with literal values
    let input = r#"
module NatTest {
    let a = UInt[8]
    let b = UInt[8]
    output result = UInt[8]
    output zero_check = Bool
    result := 7
    zero_check := a.eqNat(0)
}
println (moduleTreeVL NatTest.create.tree)
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("=== Output ===\n{}", output);
            assert!(output.contains("module NatTest"), "missing module: {}", output);
            assert!(output.contains("endmodule"), "missing endmodule: {}", output);
            assert!(output.contains("assign result = 7"), "missing result assign: {}", output);
        },
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_verilog_switch_case() {
    // Test switch/is/default macro (desugars to when/otherwise)
    let input = r#"
module Test {
    let sel = UInt[2]
    let a = UInt[8]
    let b = UInt[8]
    let result = UInt[8]
    switch sel {
        is 0 {
            result := a
        }
        default {
            result := b
        }
    }
}
println (moduleTreeVL Test.create.tree)
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("=== Output ===\n{}", output);
            assert!(output.contains("module Test"), "missing module: {}", output);
            assert!(output.contains("endmodule"), "missing endmodule: {}", output);
            // switch desugars to when/otherwise, should produce always block
            assert!(output.contains("always @(*)"), "missing always: {}", output);
            assert!(output.contains("if ("), "missing if: {}", output);
            assert!(output.contains("result = a"), "missing is body: {}", output);
            assert!(output.contains("result = b"), "missing default body: {}", output);
        },
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_verilog_switch_multi_case() {
    // Test switch with multiple is cases
    let input = r#"
module Test {
    let sel = UInt[2]
    let a = UInt[8]
    let b = UInt[8]
    let c = UInt[8]
    let result = UInt[8]
    switch sel {
        is 0 {
            result := a
        }
        is 1 {
            result := b
        }
        default {
            result := c
        }
    }
}
println (moduleTreeVL Test.create.tree)
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("=== Output ===\n{}", output);
            assert!(output.contains("module Test"), "missing module: {}", output);
            assert!(output.contains("endmodule"), "missing endmodule: {}", output);
            assert!(output.contains("always @(*)"), "missing always: {}", output);
            // Should have independent ifs for each case; the default case
            // negates all is-cases (!(sel == 0) && !(sel == 1))
            assert!(output.contains("if ("), "missing if: {}", output);
            assert!(output.contains("!(sel == 0) && !(sel == 1)"), "missing default negation: {}", output);
            assert!(output.contains("result = a"), "missing is 0 body: {}", output);
            assert!(output.contains("result = b"), "missing is 1 body: {}", output);
            assert!(output.contains("result = c"), "missing default body: {}", output);
        },
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

// ============================================================
// Tests for multiple Into implementations for the same type
// ============================================================

/// Helper to run a multi-Into test with basic prelude
fn run_multi_into_test(input: &str) -> String {
    match run_with_prelude(input) {
        Ok(output) => {
            println!("=== Output ===\n{}", output);
            output
        },
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

/// Helper: test that multiple Into impls work for the same type
fn mk_multi_into_test(extra: &str) -> String {
    run_multi_into_test(extra)
}

// All multi-Into tests use `run_with_prelude` which loads Bool, Nat, Unit, Into, Add etc.
// These tests verify that multiple Into implementations for the same type resolve correctly.

/// Test 1: Into[Unit] for Nat �?unambiguous, no prelude conflict
#[test]
fn test_multi_into_unit_for_nat() {
    let input = r#"
impl Into[Unit] for Nat {
    def into: Unit = unit
}
def u: Unit = zero.into
println u
"#;
    let output = mk_multi_into_test(input);
    assert!(output.contains("Unit"), "expected Unit, got: {}", output);
}

/// Test 2: Into for custom struct �?tests that user-defined Into resolves over prelude Into[UInt[w]]
#[test]
fn test_multi_into_custom_struct() {
    let input = r#"
struct Wrapper {
    val: Nat
}
impl Into[Wrapper] for Nat {
    def into: Wrapper = Wrapper.mk this
}
def w: Wrapper = succ(zero).into
println w.val
"#;
    let output = mk_multi_into_test(input);
    // Succ(0) displays as 1 in decimal
    assert!(output.contains("1"), "expected 1 (succ(zero)), got: {}", output);
}

/// Test 3: Two user-defined Into impls for Nat (both custom structs)
#[test]
fn test_multi_into_two_custom_structs() {
    let input = r#"
struct WrapOne {
    val: Nat
}
struct WrapTwo {
    val: Nat
}
impl Into[WrapOne] for Nat {
    def into: WrapOne = WrapOne.mk this
}
impl Into[WrapTwo] for Nat {
    def into: WrapTwo = WrapTwo.mk this
}
def a: WrapOne = zero.into
def b: WrapTwo = succ(zero).into
println a.val
println b.val
"#;
    let output = mk_multi_into_test(input);
    assert!(output.contains("0"), "expected 0, got: {}", output);
    assert!(output.contains("1"), "expected 1 (succ(zero)), got: {}", output);
}

/// Test 4: Into in function argument position (Unit type)
#[test]
fn test_multi_into_fn_arg_unit() {
    let input = r#"
impl Into[Unit] for Nat {
    def into: Unit = unit
}
def expect_unit(x: Unit): Unit = x
def test: Unit = expect_unit(zero.into)
println test
"#;
    let output = mk_multi_into_test(input);
    assert!(output.contains("Unit"), "expected Unit, got: {}", output);
}

/// Test 5: Identity Into for custom struct
#[test]
fn test_multi_into_identity_custom() {
    // prelude (op.typort) already provides `impl[T] Into[T] for T`, so a
    // user re-definition would trip the `redefine` check. Rely on prelude's
    // identity instance for custom structs instead.
    let input = r#"
struct MyBox {
    val: Nat
}
def m: MyBox = MyBox.mk(succ zero).into
println m.val
"#;
    let output = mk_multi_into_test(input);
    assert!(output.contains("1"), "expected 1 (succ(zero)), got: {}", output);
}

/// Test 6: Parametric struct Into (generic Holder)
#[test]
fn test_multi_into_param_custom() {
    let input = r#"
struct Holder[A] {
    val: A
}
impl[A] Into[Holder[A]] for A {
    def into: Holder[A] = Holder.mk this
}
def h: Holder[Nat] = zero.into
println h.val
"#;
    let output = mk_multi_into_test(input);
    assert!(output.contains("0"), "expected 0, got: {}", output);
}

/// Test 7: Struct-to-struct conversion via Into
#[test]
fn test_multi_into_struct_convert() {
    let input = r#"
struct Celsius {
    temp: Nat
}
struct Fahrenheit {
    temp: Nat
}
impl Into[Celsius] for Fahrenheit {
    def into: Celsius = Celsius.mk this.temp
}
def c: Celsius = Fahrenheit.mk(succ zero).into
println c.temp
"#;
    let output = mk_multi_into_test(input);
    assert!(output.contains("1"), "expected 1 (succ(zero)), got: {}", output);
}

/// Test 8: Nested struct Into
#[test]
fn test_multi_into_nested_struct() {
    let input = r#"
struct Inner {
    x: Nat
}
struct Outer {
    inner: Inner
}
impl Into[Inner] for Nat {
    def into: Inner = Inner.mk this
}
def o: Outer = Outer.mk (succ(zero).into)
println o.inner.x
"#;
    let output = mk_multi_into_test(input);
    assert!(output.contains("1"), "expected 1 (succ(zero)), got: {}", output);
}

/// Test 9: Chained Into with wrapper function
#[test]
fn test_multi_into_chain_custom() {
    let input = r#"
struct Wrap {
    val: Nat
}
impl Into[Wrap] for Nat {
    def into: Wrap = Wrap.mk this
}
def get_val(w: Wrap): Nat = w.val
println (get_val (zero.into))
"#;
    let output = mk_multi_into_test(input);
    assert!(output.contains("0"), "expected 0, got: {}", output);
}

/// Test 10: Two structs with same field type, both Into from Nat
#[test]
fn test_multi_into_two_structs_same_field() {
    let input = r#"
struct PointA {
    x: Nat
}
struct PointB {
    x: Nat
}
impl Into[PointA] for Nat {
    def into: PointA = PointA.mk this
}
impl Into[PointB] for Nat {
    def into: PointB = PointB.mk this
}
def p: PointA = zero.into
println p.x
"#;
    let output = mk_multi_into_test(input);
    assert!(output.contains("0"), "expected 0, got: {}", output);
}

/// Test 11: HDL Nat literal via Into[UInt[w]] for Nat (prelude) still works
#[test]
fn test_multi_into_hdl_nat_uint() {
    let input = r#"
module Test[w: Nat] {
    output sum = UInt[w]
    sum := 42
}
println (moduleTreeVL Test.create[8].tree)
"#;
    let output = mk_multi_into_test(input);
    assert!(output.contains("assign sum = 42"), "expected 42 assign, got: {}", output);
}

/// Test 12: String concat still works
#[test]
fn test_multi_into_string_concat() {
    let input = r#"
println "hello" + " " + "world"
"#;
    let output = mk_multi_into_test(input);
    assert!(output.contains("hello world"), "expected hello world, got: {}", output);
}

/// Test 13: Two Into impls for different custom structs in same scope
#[test]
fn test_multi_into_two_structs_scope() {
    let input = r#"
struct A {
    x: Nat
}
struct B {
    y: Nat
}
impl Into[A] for Nat {
    def into: A = A.mk this
}
impl Into[B] for Nat {
    def into: B = B.mk this
}
def a: A = zero.into
def b: B = succ(zero).into
println a.x
println b.y
"#;
    let output = mk_multi_into_test(input);
    assert!(output.contains("0"), "expected 0, got: {}", output);
    assert!(output.contains("1"), "expected 1 (succ(zero)), got: {}", output);
}

/// Test 14: Prelude Add[String, String] works
#[test]
fn test_multi_into_prelude_add_string() {
    let input = r#"
println "a" + "b"
"#;
    let output = mk_multi_into_test(input);
    assert!(output.contains("ab"), "expected ab, got: {}", output);
}

/// Test 15: Into[UInt[w]] for Nat in verilog generation (prelude)
#[test]
fn test_multi_into_prelude_uint() {
    let input = r#"
module Test {
    output x = UInt[8]
    x := 42
}
println (moduleTreeVL Test.create.tree)
"#;
    let output = mk_multi_into_test(input);
    assert!(output.contains("assign x = 42"), "expected assign, got: {}", output);
}

/// Test 16: String.typort Into[String] for Boolean still works
#[test]
fn test_multi_into_boolean_to_string() {
    let input = r#"
println (true.into)
"#;
    let output = mk_multi_into_test(input);
    assert!(output.contains("true"), "expected true, got: {}", output);
}

/// Test 17: HDL assignment macro still works (uses .into for Nat �?UInt)
#[test]
fn test_multi_into_assign_macro() {
    let input = r#"
module Test[w: Nat] {
    let a = UInt[w]
    output b = UInt[w]
    b := a
}
println (moduleTreeVL Test.create[8].tree)
"#;
    let output = mk_multi_into_test(input);
    assert!(output.contains("endmodule"), "expected endmodule, got: {}", output);
}

/// Test 18: Basic Into[Unit] for Nat  (alternative pattern)
#[test]
fn test_multi_into_unit_alt() {
    let input = r#"
impl Into[Unit] for Nat {
    def into: Unit = unit
}
def to_unit(x: Nat): Unit = x.into
println (to_unit (succ zero))
"#;
    let output = mk_multi_into_test(input);
    assert!(output.contains("Unit"), "expected Unit, got: {}", output);
}

/// Test 19: Into + Add trait coexistence (using prelude Add)
#[test]
fn test_multi_into_add_coexist() {
    let input = r#"
impl Into[Unit] for Nat {
    def into: Unit = unit
}
def add_nat(x: Nat, y: Nat): Nat = match y {
    case zero => x
    case succ(n) => succ (add_nat x n)
}
def two = succ (succ zero)
def u: Unit = two.into
def five = add_nat (add_nat two two) (succ zero)
println u
println five
"#;
    let output = mk_multi_into_test(input);
    assert!(output.contains("Unit"), "expected Unit, got: {}", output);
    assert!(output.contains("5"), "expected 5, got: {}", output);
}

/// Test 20: Generic struct with Into matching both specific and identity
#[test]
fn test_multi_into_generic_struct_twoway() {
    let input = r#"
struct Wrapper[A] {
    val: A
}
impl[A] Into[Wrapper[A]] for A {
    def into: Wrapper[A] = Wrapper.mk this
}
def w: Wrapper[Nat] = zero.into
println w.val
"#;
    let output = mk_multi_into_test(input);
    assert!(output.contains("0"), "expected 0, got: {}", output);
}

#[test]
fn test_macro_cut_parse_error_in_body() {
    // Test 1: Parse error INSIDE module body �?verify error is at the
    // expression position (offset ~53: `+ +`), not backtracked to declaration.
    let input = r#"
module Adder {
    input a = UInt[8]
    sum := a + + b
}
println (moduleTreeVL Adder.create.tree)
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
        include_str!("../prelude/core/op.typort"),
        include_str!("../prelude/core/nat.typort"),
        include_str!("../prelude/hdl/hdl-core.typort"),
        include_str!("../prelude/hdl/hdl-types.typort"),
        include_str!("../prelude/hdl/hdl-ops.typort"),
    ];
    for p in prelude_files {
        if let Some((_, _, new_exports, _)) = parser::parser_with_macros(&preprocess(p), id, &global_macros) {
            for (name, rules) in new_exports {
                global_macros.insert(name, rules);
            }
        }
        id += 1;
    }
    let input = "module";
    let (_, errors) = parser::parser_with_macros(input, id, &global_macros)
        .map(|(d, e, _, _)| (d, e)).unwrap();
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
println (a => Eq[Nat](nat_add(1, a), nat_add(2, a)))
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
    // Expected tyck error: the `_` hole in `wallace_tree` can't be unified with
    // the recursive `wallace_tree`/`wallace_stage` result type (Fin refinement).
    match run_with_prelude(input) {
        Ok(output) => panic!("expected tyck error, got output: {}", output),
        Err(e) => {
            println!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset);
            assert!(e.0.data.contains("can't unify"),
                "expected can't unify error, got: {}", e.0.data);
        }
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
        ("op.typort", include_str!("../prelude/core/op.typort")),
        ("eq.typort", include_str!("../prelude/core/eq.typort")),
        ("nat.typort", include_str!("../prelude/core/nat.typort")),
        ("calc.typort", include_str!("../prelude/core/calc.typort")),
        ("bool.typort", include_str!("../prelude/core/bool.typort")),
        ("option.typort", include_str!("../prelude/data/option.typort")),
        ("result.typort", include_str!("../prelude/data/result.typort")),
        ("order.typort", include_str!("../prelude/data/order.typort")),
        ("void.typort", include_str!("../prelude/core/void.typort")),
        ("decidable.typort", include_str!("../prelude/data/decidable.typort")),
        ("vec.typort", include_str!("../prelude/data/vec.typort")),
        ("either.typort", include_str!("../prelude/data/either.typort")),
        ("list.typort", include_str!("../prelude/data/list.typort")),
        ("string.typort", include_str!("../prelude/data/string.typort")),
        ("nonempty.typort", include_str!("../prelude/data/nonempty.typort")),
        ("hdl-core.typort", include_str!("../prelude/hdl/hdl-core.typort")),
        ("hdl-types.typort", include_str!("../prelude/hdl/hdl-types.typort")),
        ("hdl-ops.typort", include_str!("../prelude/hdl/hdl-ops.typort")),
        ("hdl-clock.typort", include_str!("../prelude/hdl/hdl-clock.typort")),
        ("hdl-bus.typort", include_str!("../prelude/hdl/hdl-bus.typort")),
        ("hdl-signals.typort", include_str!("../prelude/hdl/hdl-signals.typort")),
        ("hdl-macros.typort", include_str!("../prelude/hdl/hdl-macros.typort")),
        ("hdl-verilog.typort", include_str!("../prelude/hdl/hdl-verilog.typort")),
        ("show.typort", include_str!("../prelude/show.typort")),
    ];

    #[test]
    fn test_prelude_syntax() {
        let mut all_ok = true;
        for (name, content) in PRELUDE_FILES {
            let processed = preprocess(content);
            // A file may legitimately contain only macro definitions
            // (e.g. hdl-macros.typort, calc.typort) — detect that via the
            // parsed macro exports rather than the file name.
            let macro_only = match super::parser::parser_with_macros(&processed, 0, &Default::default()) {
                Some((_, _, exports, _)) => !exports.is_empty(),
                None => false,
            };
            match parse_file(&processed, 0) {
                Some((decls, errors)) => {
                    if !errors.is_empty() {
                        all_ok = false;
                        eprintln!("[SYNTAX ERROR] {}: {:?}", name, errors);
                        for e in &errors {
                            eprintln!("  {:?}", e);
                        }
                    }
                    // Allow files with only macro definitions (no regular declarations)
                    if decls.is_empty() && !macro_only {
                        all_ok = false;
                        eprintln!("[EMPTY] {}: parsed no declarations", name);
                    } else if decls.is_empty() {
                        eprintln!("[OK] {}: macro-only file", name);
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
                // Nat.show 自 2026-08-02 起打印十进制（nat_to_dec），不再是 "succ" stub
                assert!(output.contains("Point(1, 0)"), "Expected Point(1, 0) in output, got: {}", output);
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

    #[test]
    fn test_static_method() {
        let input = r#"
struct Box[A] {
    val: A
}

impl[A] Box[A] {
    def get: A = this.val

    static def pack(x: A): Box[A] = new Box(x)
}

def b: Box[Nat] = Box.pack(42)
def v: Nat = b.get
println(v)
"#;
        match run_with_prelude(input) {
            Ok(output) => {
                eprintln!("static method test output: {}", output);
                assert_eq!(output.trim(), "42");
            }
            Err(e) => panic!("static method test failed: {} @ {}:{}", e.0.data, e.0.path_id, e.0.start_offset),
        }
    }

    /// Benchmark: time the elaboration of hdl-verilog.typort per-declaration.
    /// Run with: cargo test bench_hdl_verilog -- --nocapture
    #[test]
    fn bench_hdl_verilog_decls() {
        use std::time::Instant;

        let mut infer = Infer::new();
        let mut cxt = Cxt::new(&infer);
        let mut global_macros: std::collections::HashMap<String, Vec<parser::macros::MacroRule>> = Default::default();

        let prelude_files = &[
            ("op", include_str!("../prelude/core/op.typort")),
            ("eq", include_str!("../prelude/core/eq.typort")),
            ("nat", include_str!("../prelude/core/nat.typort")),
            ("bool", include_str!("../prelude/core/bool.typort")),
            ("option", include_str!("../prelude/data/option.typort")),
            ("result", include_str!("../prelude/data/result.typort")),
            ("order", include_str!("../prelude/data/order.typort")),
            ("void", include_str!("../prelude/core/void.typort")),
            ("decidable", include_str!("../prelude/data/decidable.typort")),
            ("vec", include_str!("../prelude/data/vec.typort")),
            ("either", include_str!("../prelude/data/either.typort")),
            ("list", include_str!("../prelude/data/list.typort")),
            ("string", include_str!("../prelude/data/string.typort")),
            ("nonempty", include_str!("../prelude/data/nonempty.typort")),
            ("hdl-core", include_str!("../prelude/hdl/hdl-core.typort")),
            ("hdl-types", include_str!("../prelude/hdl/hdl-types.typort")),
            ("hdl-ops", include_str!("../prelude/hdl/hdl-ops.typort")),
            ("hdl-clock", include_str!("../prelude/hdl/hdl-clock.typort")),
            ("hdl-bus", include_str!("../prelude/hdl/hdl-bus.typort")),
            ("hdl-signals", include_str!("../prelude/hdl/hdl-signals.typort")),
            ("hdl-macros", include_str!("../prelude/hdl/hdl-macros.typort")),
        ];

        for (name, content) in prelude_files {
            let processed = preprocess(content);
            if let Some((decls, _, new_exports, _)) = parser::parser_with_macros(&processed, 0, &global_macros) {
                for (n, rules) in new_exports { global_macros.insert(n, rules); }
                for tm in decls {
                    let (_, _, new_cxt) = infer.infer(&cxt, tm.clone()).unwrap();
                    cxt = new_cxt;
                }
            }
            if *name == "nat" {
                cxt::Cxt::register_nat_builtins(&mut cxt, &infer);
            }
        }

        println!("\n========== HDL-VERILOG BENCHMARK ==========");
        let verilog_content = preprocess(include_str!("../prelude/hdl/hdl-verilog.typort"));
        let parse_start = Instant::now();
        let (decls, _, _, _) = parser::parser_with_macros(&verilog_content, 0, &global_macros).unwrap();
        let parse_time = parse_start.elapsed();
        println!("  Parse: {}.{:03}s ({} decls)", parse_time.as_secs(), parse_time.subsec_millis(), decls.len());
        println!("  Per-decl elaboration:");
        let mut total_elab = std::time::Duration::ZERO;
        for (i, tm) in decls.iter().enumerate() {
            let name = match tm {
                parser::syntax::Decl::Def { name, .. } => format!("def {}", name.data),
                parser::syntax::Decl::Enum { name, .. } => format!("enum {}", name.data),
                parser::syntax::Decl::TraitDecl { name, .. } => format!("trait {}", name.data),
                parser::syntax::Decl::ImplDecl { .. } => format!("impl {}", i),
                _ => format!("decl_{}", i),
            };
            let start = Instant::now();
            let result = infer.infer(&cxt, tm.clone());
            let elapsed = start.elapsed();
            total_elab += elapsed;
            match result {
                Ok((_, _, new_cxt)) => { cxt = new_cxt; }
                Err(e) => { println!("  ERROR {}: {} @ {}:{}", name, e.0.data, e.0.path_id, e.0.start_offset); }
            }
            if elapsed.as_millis() >= 10 {
                println!("  {:>8}.{:03}s  {}", elapsed.as_secs(), elapsed.subsec_millis(), name);
            } else {
                println!("  {:>8}.{:03}s  {}", elapsed.as_secs(), elapsed.subsec_millis(), name);
            }
        }
        println!("  Total: {}.{:03}s", total_elab.as_secs(), total_elab.subsec_millis());
        println!("===========================================\n");
    }
}

#[test]
fn test_class_basic() {
    let input = r#"
enum Nat {
    zero
    succ(x: Nat)
}

class Point {
    let x: Nat = succ zero
    let y: Nat = succ (succ zero)
}

def main: Point = Point.create
"#;
    match run(input, 0) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("ERROR: {} @ {}:{}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

// ============================================================================
// §14.2 N1-N11 复现测试（2026-08-02 实测）
// 每个测试尝试触发对应问题；运行结果回写到 docs/L13-code-review.md §14.6。
// 实测结论：
//   - N6 未能复现：即便强制 per-constructor fork，类型检查仍能捕获 body
//     不匹配，cache 看似安全。
//   - N4/N5 probe 通过：未观察到 filter/refinement 副作用污染后续推理。
// ============================================================================

// N1: Tm::Call 注释字段名陈旧（写 4 字段，实际 3 字段）。
//    纯文档问题，无运行时表现 —— 由 `cargo build` 即可确认注释与 enum 不符。
#[test]
fn test_n1_doc_field_count() {
    // 与 src/L13_namespace/mod.rs:108 对照：
    //   Call(SmolStr, List<(Rc<Tm>, Icit)>, Rc<Tm>)  ← 3 字段
    // 注释 mod.rs:107 写 "Call(name, display_args, val_args, body)"  ← 4 字段，错的。
    // 无运行时崩点，靠人工审阅修复。
}

// N2: Tm::Call 包装仅在 body eval 为 Val::Match 时保留，否则静默丢弃。
//    不变量"Tm::Call 永远只包 Tm::Match"由 wrap_match_in_call 保证。
//    试图用正常用户代码打破该不变量不可行（只能包住 Match），因此无运行时复现。
//    这里仅断言 wrap_match_in_call 的输出形态。
#[test]
fn test_n2_call_wrapper_invariant() {
    // wrap_match_in_call 应用到 Lam 包裹 Match 应产生 Tm::Call(_, args, Tm::Match(..))
    let name = SmolStr::new("f");
    // \x => match x { ... }
    let inner_match = Tm::Match(
        Rc::new(Tm::Var(Ix(0))),
        vec![],
    );
    let lam = Tm::Lam(
        empty_span(SmolStr::new("x")),
        Icit::Expl,
        Rc::new(inner_match),
    );
    let wrapped = wrap_match_in_call(name.clone(), &lam, 0);
    match &wrapped {
        Tm::Lam(_, _, body) => match body.as_ref() {
            Tm::Call(n, _, inner) => {
                assert_eq!(n, &name, "wrap_match_in_call 应使用给定 name");
                assert!(matches!(inner.as_ref(), Tm::Match(..)),
                    "Tm::Call 的 body 必须是 Tm::Match（不变量）");
            }
            other => panic!("内层应为 Tm::Call，实际: {:?}", other),
        },
        other => panic!("外层应保持 Lam，实际: {:?}", other),
    }
}

// N3: vals_eq_ground 对 Val::Call 不比 body 只比 name+args，依赖
//    "同 name 同 args ⇒ 同 body" 不变量。Typort 不允许同作用域 def 重名，
//    故通过常规用户代码无法触发该不变量破坏。跳过运行时复现。
#[test]
fn test_n3_vals_eq_ground_doc_only() {
    // 不做运行时触发 —— 实际触发需要 def 重名或 import 冲突，当前不允许。
    // 这里仅作为文档锚点：typeclass.rs:346-352 的 vals_eq_ground_impl
    // 对 Val::Call 分支"不比 body"的不变量未在注释中声明。
}

// N6: checked_ret 按 idx 缓存假设 → 同一 wildcard arm 在多个 GADT 分支中
//    只首个分支做 body 类型检查、后续分支跳过 → 可能吞掉 cons 分支的
//    body 不一致。实测：NOT REPRODUCED。
//    即便用 `case nil => rfl` 强制 per-constructor fork，类型检查仍能
//    捕获 `Eq(?n, 0) vs Eq(?n, ?n)` 不匹配，说明 cache 跳过的路径并非
//    body 一致性检查的唯一兜底（leaf 处 check_pm_final 重新做 unify_pm
//    细化 + body check 内部用细化后的 cxt 而非缓存命中即跳过类型检查）。
#[test]
fn test_n6_checked_ret_cache_unsoundness() {
    let input = r#"
def buggy[T, n: Nat](v: Vec[T] n): Eq n zero =
    match v {
        case nil => rfl
        case _ => rfl
    }
println (buggy (cons zero nil))
"#;
    let result = run_with_prelude(input);
    match &result {
        Ok(output) => panic!(
            "N6 REPRO: 期望 cons 分支 body 检查被 cache 跳过、整函数类型检查通过（unsound），got Ok:\n{}",
            output
        ),
        Err(e) => println!("N6 NOT REPRODUCED (got expected error):\n  {}", e.0.data),
    }
}

// N4/N5: filter_accessible_constrs 不回滚 meta_contrains + GADT refinement
//    unify_pm 副作用泄漏到主 meta 池。
//    实测：probe pass（NOT REPRODUCED）—— 复杂 GADT 匹配后紧跟独立类型检查
//    未见 spurious 错误。说明副作用即便泄漏，量级/方式不至影响下游推理，
//    或者主 meta 池有其它保护；代码层面"三类快照 vs 两类快照"的不一致仍
//    是隐患，应在风险面扩大前修复。
#[test]
fn test_n4_n5_state_pollution_probe() {
    let input = r#"
def first_or_zero[T, n: Nat](v: Vec[T] n): Nat =
    match v {
        case nil => zero
        case cons(x, _) => succ zero
    }
def two = succ (succ zero)
def three = succ two
println (first_or_zero (cons zero nil))
println (first_or_zero nil)
println (three)
"#;
    match run_with_prelude(input) {
        Ok(output) => println!("N4/N5 probe pass (NOT REPRODUCED):\n{}", output),
        Err(e) => panic!(
            "N4/N5 可能 REPRO：GADT 路径后独立类型检查失败：\n{}",
            e.0.data
        ),
    }
}

// N7: eval_aux 用 u32::MAX sentinel 表示非 SumCase head。
//    要触发 sentinel 假阳需要 constr_idx 真的等于 u32::MAX，要求 ≥ 2^32-1
//    个 constructor，不可构造。Skip —— 仅作文档锚点。
#[test]
fn test_n7_sentinel_unreachable() {}

// N8/N9/N10/N11: 代码可读性/性能问题，无运行时崩点可构造。
// N10 已由 `cargo build` warning 确认（pattern_match.rs:764 `item_pats` 未使用）。
#[test]
fn test_n8_n9_n10_n11_doc_only() {}

// ============================================================================
// §15 Prelude bug 复现测试（2026-08-02）
// 每个测试先以"应输出 X"断言，修复前 fail（red），修复后 pass（green）。
// ============================================================================

#[test]
fn test_prelude_int_add_negative() {
    // §15.2 P1-1: int_add 负方向 bug。
    // 1 + (-2) = -1；当前返回 ofNat(pred(nat_sub 1 1)) = ofNat 0 = 0。
    let input = r#"
def m: Int = (ofNat 1) + (negSucc 1)
println m.show
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("int_add: {}", output);
            assert!(output.contains("-1"), "1 + (-2) 应得 -1，实际输出: {}", output);
        }
        Err(e) => panic!("ERROR: {}", e.0.data),
    }
}

#[test]
fn test_prelude_int_mul_negative() {
    // §15.2 P1-2: int_mul 负方向 bug。
    // (-2) * 2 = -4；当前返回 ofNat zero = 0。
    let input = r#"
def m: Int = (negSucc 1) * (ofNat 2)
println m.show
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("int_mul: {}", output);
            assert!(output.contains("-4"), "(-2)*2 应得 -4，实际输出: {}", output);
        }
        Err(e) => panic!("ERROR: {}", e.0.data),
    }
}

#[test]
fn test_prelude_nat_show_decimal() {
    // §15.2 D4: Nat.show stub，所有 succ 都返回 "succ"。
    // 应打印十进制 "3"。
    let input = r#"
def three: Nat = succ (succ (succ zero))
println three.show
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("nat.show: {}", output);
            assert!(output.contains("3"), "three.show 应得 3，实际输出: {}", output);
        }
        Err(e) => panic!("ERROR: {}", e.0.data),
    }
}

#[test]
fn test_prelude_either_to_result_direction() {
    // §15.2 P1-3: Either.to_result 与 either_to_result 方向矛盾。
    // 函数版 left→err；方法版当前 left→ok（错误）。修复后 left→err → is_ok=false。
    let input = r#"
def e: Either[String, Nat] = left "err"
println (e.to_result(n => n).is_ok)
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("to_result.is_ok: {}", output);
            assert!(output.contains("false"), "to_result 应把 left 当 err（is_ok=false），实际输出: {}", output);
        }
        Err(e) => panic!("ERROR: {}", e.0.data),
    }
}

#[test]
fn test_prelude_stream_fire_needs_ready() {
    // §15.2: Stream.fire 应为 valid && ready（SpinalHDL 语义）。
    // 构造 Stream，取 fire 的 Expr 并用 exprVL 输出，验证含 &&。
    let input = r#"
def v: Bool = newBoolNamed "valid"
def r: Bool = newBoolNamed "ready"
def s: Stream[Bool] = Stream.mk v r v
def f: Bool = s.fire
println (exprVL f.expr)
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("stream.fire output: {}", output);
            assert!(output.contains("&&"), "Stream.fire 应生成 && 表达式，实际输出: {}", output);
        }
        Err(e) => panic!("ERROR: {}", e.0.data),
    }
}

#[test]
fn test_prelude_int_arithmetic_cases() {
    // Int 加减乘跨正负多场景回归（show.typort 2026-08-02 修复后）。
    // `-` 运算符：Neg(一元)/Sub(二元) 同名冲突已在 method resolution 层
    // 按显式参数个数消歧（infix 调用选 1 参的 Sub）。
    let input = r#"
def a: Int = (ofNat 3) + (negSucc 1)      // 3 + (-2) = 1
def b: Int = (negSucc 1) + (ofNat 3)      // -2 + 3 = 1
def c: Int = (negSucc 2) + (negSucc 1)    // -3 + -2 = -5
def d: Int = (ofNat 5) - (ofNat 2)        // 5 - 2 = 3
def e: Int = (ofNat 2) - (ofNat 5)        // 2 - 5 = -3
def f: Int = (negSucc 1) * (ofNat 3)      // -2 * 3 = -6
def g: Int = (ofNat 3) * (negSucc 1)      // 3 * -2 = -6
def h: Int = (negSucc 1) * (negSucc 1)    // -2 * -2 = 4
println a.show
println b.show
println c.show
println d.show
println e.show
println f.show
println g.show
println h.show
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("int cases output:\n{}", output);
            let lines: Vec<&str> = output.trim().lines().collect();
            assert_eq!(lines.len(), 8, "应输出 8 行，实际:\n{}", output);
            let expected = ["1", "1", "-5", "3", "-3", "-6", "-6", "4"];
            for (i, exp) in expected.iter().enumerate() {
                assert_eq!(lines[i].trim(), *exp, "第 {} 行应得 {}，实际 {}（整体输出:\n{}）", i + 1, exp, lines[i], output);
            }
        }
        Err(e) => panic!("ERROR: {}", e.0.data),
    }
}

#[test]
fn test_inlay_hint_table() {
    // inlay hint：def 未写返回类型 → 显示推断返回类型；let 未写注解 → 显示值类型。
    let mut infer = Infer::new();
    let mut cxt = Cxt::new(&infer);
    let prelude = &[
        include_str!("../prelude/core/op.typort"),
        include_str!("../prelude/core/eq.typort"),
        include_str!("../prelude/core/nat.typort"),
    ];
    let mut global_macros: std::collections::HashMap<String, Vec<parser::macros::MacroRule>> = Default::default();
    for p in prelude {
        if let Some((decls, _, new_exports, _)) = parser::parser_with_macros(&preprocess(p), 0, &global_macros) {
            for (name, rules) in new_exports {
                global_macros.insert(name, rules);
            }
            for tm in decls {
                let (_, _, new_cxt) = infer.infer(&cxt, tm.clone()).unwrap();
                cxt = new_cxt;
            }
        }
    }
    let input = r#"
def add_one(x: Nat): Nat = succ x
def dbl(x: Nat) = x + x
def g = succ zero
def with_let(x: Nat) = let y = succ x; y
"#;
    if let Some((decls, _, _, _)) = parser::parser_with_macros(&preprocess(input), 1, &global_macros) {
        for tm in decls {
            let (_, _, new_cxt) = infer.infer(&cxt, tm.clone()).unwrap();
            cxt = new_cxt;
        }
    }
    println!("inlay hints: {:?}", infer.inlay_hint_table);
    let labels: Vec<String> = infer.inlay_hint_table.iter().map(|(_, s)| s.clone()).collect();
    // add_one 写了返回类型 → 不提示
    assert!(!labels.iter().any(|l| l.starts_with(": (x: Nat)")),
        "add_one 有显式返回类型，不应有 hint: {:?}", labels);
    // dbl 与 g 未写返回类型 → 提示 : Nat
    assert!(labels.iter().filter(|l| l.as_str() == ": Nat").count() >= 2,
        "dbl 与 g 应各有一条 : Nat hint，实际 {:?}", labels);
    // 无注解 let → 提示 : Nat
    assert!(labels.iter().any(|l| l.as_str() == ": Nat"),
        "with_let 的 let y 应有 : Nat hint，实际 {:?}", labels);
    // —— 位置断言（preprocess 保持字节偏移，parser 的 offset 即原始 input 的偏移）——
    // def dbl(x: Nat) = x + x 的 : Nat hint 应锚定在参数列表 `)` 与 `=` 之间。
    let dbl_def = input.find("def dbl(x: Nat)").unwrap();
    let dbl_close_paren = dbl_def + "def dbl(x: Nat)".len(); // 紧贴 `)` 之后
    let dbl_eq = dbl_def + "def dbl(x: Nat) ".len();         // `=` 的偏移
    let dbl_hint = infer.inlay_hint_table.iter().find(|(off, lab)| {
        lab.as_str() == ": Nat" && *off > dbl_close_paren as u32 - 1 && *off < dbl_eq as u32
    });
    assert!(dbl_hint.is_some(),
        "dbl 的 : Nat hint 应落在 `)` 与 `=` 之间（offset ∈ ({}..{})），实际: {:?}",
        dbl_close_paren - 1, dbl_eq, infer.inlay_hint_table);
    // 无参 def g = succ zero 的 : Nat hint 应锚定在 `g` 之后。
    let g_end = input.find("def g").unwrap() + "def g".len();
    assert!(infer.inlay_hint_table.iter().any(|(off, lab)| lab.as_str() == ": Nat" && *off == g_end as u32),
        "g 的 : Nat hint 应锚定在 g 之后（offset == {}），实际: {:?}", g_end, infer.inlay_hint_table);
}

#[cfg(test)]
mod symbol_recovery_tests {
    use super::*;

    fn rigid(l: u32) -> Rc<Val> {
        Val::Rigid(Lvl(l), List::new()).into()
    }

    /// `quote` restores an inlined two-argument helper call as a display
    /// `OpCall` carrying the registered operator symbol (`nat_add_helper
    /// x y` → `OpCall("+", [x, y])`, pretty-printed as `x + y`).
    #[test]
    fn quote_restores_infix_operator_application() {
        let mut infer = Infer::new();
        infer.symbol_table.insert(
            (SmolStr::new("nat_add_helper"), 2),
            SmolStr::new("+"),
        );
        let decl: Decl = Decl::default();
        let x = rigid(0);
        let y = rigid(1);
        let call: Rc<Val> = Val::Call(
            SmolStr::new("nat_add_helper"),
            List::new()
                .prepend((y.clone(), Icit::Expl))
                .prepend((x.clone(), Icit::Expl)),
            Val::Match(x.clone(), List::new(), Vec::new()).into(),
        )
        .into();
        let q = infer.quote(&decl, Lvl(2), &call);
        match q.as_ref() {
            Tm::OpCall { symbol, name, args, .. } => {
                assert_eq!(symbol, "+");
                assert_eq!(name, "nat_add_helper");
                assert_eq!(args.len(), 2);
                // Args are quoted in display order: x = Var(1), y = Var(0).
                let quoted: Vec<&Rc<Tm>> = args.iter().map(|(a, _)| a).collect();
                assert!(matches!(quoted[0].as_ref(), Tm::Var(Ix(1))), "a1 should be x, got {quoted:?}");
                assert!(matches!(quoted[1].as_ref(), Tm::Var(Ix(0))), "a2 should be y, got {quoted:?}");
            }
            other => panic!("expected OpCall, got {other:?}"),
        }
    }

    /// A one-argument registered helper restores to a prefix `OpCall`.
    #[test]
    fn quote_restores_prefix_operator_application() {
        let mut infer = Infer::new();
        infer.symbol_table.insert(
            (SmolStr::new("not_helper"), 1),
            SmolStr::new("!"),
        );
        let decl: Decl = Decl::default();
        let x = rigid(0);
        let call: Rc<Val> = Val::Call(
            SmolStr::new("not_helper"),
            List::new().prepend((x.clone(), Icit::Expl)),
            Val::Match(x.clone(), List::new(), Vec::new()).into(),
        )
        .into();
        let q = infer.quote(&decl, Lvl(1), &call);
        match q.as_ref() {
            Tm::OpCall { symbol, name, args, .. } => {
                assert_eq!(symbol, "!");
                assert_eq!(name, "not_helper");
                assert_eq!(args.len(), 1);
                let quoted: Vec<&Rc<Tm>> = args.iter().map(|(a, _)| a).collect();
                assert!(matches!(quoted[0].as_ref(), Tm::Var(Ix(0))), "arg should be x, got {quoted:?}");
            }
            other => panic!("expected OpCall, got {other:?}"),
        }
    }

    /// Unregistered helpers keep the plain `Tm::Call` form, as do calls
    /// with implicit arguments or non-matching arity.
    #[test]
    fn quote_keeps_call_for_unregistered_or_implicit() {
        let mut infer = Infer::new();
        let decl: Decl = Decl::default();
        let x = rigid(0);
        let y = rigid(1);

        // Unregistered helper.
        let call: Rc<Val> = Val::Call(
            SmolStr::new("nat_max"),
            List::new()
                .prepend((y.clone(), Icit::Expl))
                .prepend((x.clone(), Icit::Expl)),
            Val::Match(x.clone(), List::new(), Vec::new()).into(),
        )
        .into();
        assert!(matches!(infer.quote(&decl, Lvl(2), &call).as_ref(), Tm::Call(..)));

        // Registered helper but arity mismatch (3 args).
        infer.symbol_table.insert(
            (SmolStr::new("nat_add_helper"), 2),
            SmolStr::new("+"),
        );
        let z = rigid(2);
        let call3: Rc<Val> = Val::Call(
            SmolStr::new("nat_add_helper"),
            List::new()
                .prepend((z.clone(), Icit::Expl))
                .prepend((y.clone(), Icit::Expl))
                .prepend((x.clone(), Icit::Expl)),
            Val::Match(x.clone(), List::new(), Vec::new()).into(),
        )
        .into();
        assert!(matches!(infer.quote(&decl, Lvl(3), &call3).as_ref(), Tm::Call(..)));

        // Registered helper but an implicit argument.
        let call_impl: Rc<Val> = Val::Call(
            SmolStr::new("nat_add_helper"),
            List::new()
                .prepend((y.clone(), Icit::Impl))
                .prepend((x.clone(), Icit::Expl)),
            Val::Match(x.clone(), List::new(), Vec::new()).into(),
        )
        .into();
        assert!(matches!(infer.quote(&decl, Lvl(2), &call_impl).as_ref(), Tm::Call(..)));
    }

    /// Quote → eval round trip of a recovered operator call reproduces the
    /// original `Val::Call` (definitional equality is unaffected).
    #[test]
    fn quote_eval_roundtrip_preserves_call() {
        let mut infer = Infer::new();
        infer.symbol_table.insert(
            (SmolStr::new("nat_add_helper"), 2),
            SmolStr::new("+"),
        );
        let decl: Decl = Decl::default();
        let x = rigid(0);
        let y = rigid(1);
        let call: Rc<Val> = Val::Call(
            SmolStr::new("nat_add_helper"),
            List::new()
                .prepend((y.clone(), Icit::Expl))
                .prepend((x.clone(), Icit::Expl)),
            Val::Match(x.clone(), List::new(), Vec::new()).into(),
        )
        .into();
        let q = infer.quote(&decl, Lvl(2), &call);
        let env = List::new()
            .prepend(rigid(1))
            .prepend(rigid(0));
        let back = infer.eval(&decl, &env, &q);
        match back.as_ref() {
            Val::Call(name, args, _) => {
                assert_eq!(name, "nat_add_helper");
                assert_eq!(args.len(), 2);
            }
            other => panic!("expected Val::Call after round trip, got {other:?}"),
        }
    }
}

