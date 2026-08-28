use crate::bimap::BiMap;
use crate::parser_lib::ToSpan;

use super::{
    syntax::{Locals, Pruning},
    *,
};

/// `try_count_nat` that forces each spine step: prim arguments may carry
/// unnormalized values (e.g. widths embedded in Expr nodes projected without
/// projection-time forcing), and a plain SumCase walk would misread them as
/// 0.  Forcing per step keeps each step O(1) amortized under the current
/// force; widths are small so the total is bounded.
pub(super) fn count_nat_forced(infer: &Infer, decl: &Decl, val: &Rc<Val>) -> u64 {
    let mut count = 0u64;
    let mut current = infer.force(decl, val);
    loop {
        match current.as_ref() {
            // Native Nat: the whole concrete value in one u64 (Lean/Agda
            // native representation).  `succ (stuck)` chains still walk
            // below and keep the legacy behaviour (return 0 on a stuck
            // tail).  A mixed `succ^c (Nat k)` tail (only buildable via
            // nat_add's overflow fallback) totals c + k, so the walked
            // count must be added, not dropped.
            Val::Nat(k) => return count.checked_add(*k).unwrap_or(0),
            Val::SumCase { index: 0, .. } => return count,
            Val::SumCase { index: 1, datas, .. } => {
                match datas.first() {
                    Some((_, prev, _)) => {
                        count = match count.checked_add(1) {
                            Some(c) => c,
                            None => return 0,
                        };
                        current = infer.force(decl, prev);
                    }
                    None => return 0,
                }
            }
            _ => return 0,
        }
    }
}

/// Build the value of a `Nat` literal.  Native form: a concrete `succ^n zero`
/// is a single `Val::Nat(n)` (O(1)) instead of an n-deep unary chain.  The
/// `span`/`nat_type` arguments are kept for call-site compatibility; the
/// type is not needed because `quote` re-derives it from the declaration
/// table when expanding the value back to a term.
pub(super) fn build_nat(count: u64, _span: Span<()>, _nat_type: &Rc<Val>) -> Rc<Val> {
    Val::Nat(count).into()
}

pub(super) fn nat_to_dec(infer: &Infer, decl: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.is_empty() { return None; }
    let count = count_nat_forced(infer, decl, &args[0]);
    Some(Val::LiteralIntro(empty_span(count.to_string())).into())
}

/// Generate Verilog width range string: "[N-1:0] " for N>1, "" for N<=1
fn width_range(infer: &Infer, decl: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.is_empty() { return None; }
    let w = count_nat_forced(infer, decl, &args[0]);
    let result = if w <= 1 {
        String::new()
    } else {
        format!("[{}:0] ", w - 1)
    };
    Some(Val::LiteralIntro(empty_span(result)).into())
}

/// Is the Nat argument a fully evaluated (ground) number? True for native
/// `Val::Nat` and for `succ`-chains whose tail forces to ground; false for
/// anything stuck (dangling Rigid/Flex — elaboration-time variables that
/// will never resolve at runtime; see the typeclass instance Nat param bug,
/// docs/l13-typeclass-instance-nat-param-bug.md).
fn nat_is_ground(infer: &Infer, decl: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.is_empty() { return None; }
    let mut current = infer.force(decl, &args[0]);
    let ground = loop {
        match current.as_ref() {
            Val::Nat(_) => break true,
            Val::SumCase { index: 0, .. } => break true,   // zero
            Val::SumCase { index: 1, datas, .. } => {
                match datas.first() {
                    Some((_, prev, _)) => current = infer.force(decl, prev),
                    None => break false,
                }
            }
            _ => break false,
        }
    };
    let name = if ground { "true" } else { "false" };
    Some(decl.get(name).map(|x| x.2.clone()).unwrap_or(Val::Decl(empty_span(SmolStr::new(name)), List::new()).into()))
}

// === Nat arithmetic primops (Lean/Agda-style word-size primitives) ===
//
// The prelude defines `+ - * / %` on `Nat` by structural recursion, which is
// O(m) / O(n·m) in the value magnitude.  These primops sink the arithmetic
// into native u64 ops while *exactly* preserving the old definitions'
// reducibility (definitional equality), so the rfl/induction proofs in
// nat.typort keep checking.  See docs/nat-primops-plan.md for the rule tables.

/// Build a `succ inner` value of the native `Nat` sum type (mirrors the
/// `quote_nat` shape: `SumCase{ index:1, datas:[(n, inner)] }`).  Returns
/// `None` if the `Nat` type is not registered (shouldn't happen after the
/// prelude loads).
fn nat_succ_shape(decl: &Decl, inner: Rc<Val>) -> Option<Rc<Val>> {
    let typ = decl.get("Nat").map(|e| e.2.clone())?;
    Some(Val::SumCase {
        is_trait: false,
        typ,
        index: 1,
        datas: Rc::new(vec![(empty_span(SmolStr::new("n")), inner, Icit::Expl)]),
    }.into())
}

/// Build a stuck application `name args...` as `Val::Decl`, preserving the
/// spine prepend convention used by `v_app`/`force` in mod.rs: the most
/// recently applied argument sits at the list head, so for a call `f x y`
/// the spine is `[y, x]`.  Prepend the args in *forward* order so `force`'s
/// `collect().reverse()` recovers the natural order (a later `force`
/// re-invokes the prim, which is how the iterative "step one constructor
/// then leave the rest stuck" behaviour — e.g. `nat_sub` on two stuck
/// chains — is achieved).
fn stuck_decl(name: &str, args: &[Rc<Val>]) -> Rc<Val> {
    let mut sp = List::new();
    for a in args {
        sp = sp.prepend((a.clone(), Icit::Expl));
    }
    Val::Decl(empty_span(SmolStr::new(name)), sp).into()
}

/// Extract the native u64 of a `Nat` argument that is *fully concrete*:
/// `Val::Nat(k)` or a `zero` constructor (defensively: an uncompressed
/// `SumCase{ index:0 }` of the `Nat` type — after a `force` a concrete zero
/// is normally `Val::Nat(0)` already).  Any stuck value → `None`.
fn nat_concrete(infer: &Infer, decl: &Decl, v: &Rc<Val>) -> Option<u64> {
    let v = infer.force(decl, v);
    match v.as_ref() {
        Val::Nat(k) => Some(*k),
        Val::SumCase { typ, index: 0, datas, .. }
            if datas.is_empty() && is_nat_sum(&infer.force(decl, typ)) => Some(0),
        _ => None,
    }
}

/// The inner argument of a stuck (or merely forced) `succ d` chain of the
/// `Nat` type; anything else (incl. concrete `Val::Nat`) → `None`.  `v` must
/// already be forced (its `typ` field is then the forced `Nat` type).
fn nat_succ_inner(v: &Val) -> Option<&Rc<Val>> {
    match v {
        Val::SumCase { typ, index: 1, datas, .. }
            if datas.len() == 1 && is_nat_sum(typ) => Some(&datas[0].1),
        _ => None,
    }
}

/// `nat_add x y` — old `match y {0 => x; succ n => succ (add x n)}`:
/// reducibility is driven entirely by `y`.
fn nat_add(infer: &Infer, decl: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.len() < 2 { return None; }
    let x = args[0].clone();
    let y = infer.force(decl, &args[1]);
    // y ≡ 0 → x (unconditional: old `case zero => x` ignores x).  This is
    // what makes `a + 0 = a` / `add_zero_right` reduce by rfl.
    if nat_concrete(infer, decl, &y) == Some(0) {
        return Some(x);
    }
    // both concrete → native u64 fast path.
    if let (Some(a), Some(b)) = (nat_concrete(infer, decl, &x), nat_concrete(infer, decl, &y)) {
        return a.checked_add(b).map(|k| Val::Nat(k).into());
    }
    // y ≡ succ⟨d⟩ (stuck chain) → succ (nat_add x d); inner left to force.
    // This fires for e.g. `n + succ m` with rigid m, keeping
    // `add_succ_right` / `add_succ_left` / `add_comm` rfl-decomposable.
    if let Some(d) = nat_succ_inner(y.as_ref()) {
        let inner = stuck_decl("nat_add", &[x.clone(), d.clone()]);
        return nat_succ_shape(decl, inner);
    }
    // y ≡ Nat(k>0), x not concrete → unfold `succ^k x` (O(k)).  Preserves
    // walkability for `len + 1`-style width expressions (count_nat_forced).
    if let Val::Nat(k) = y.as_ref() {
        let mut inner = x;
        for _ in 0..*k {
            inner = nat_succ_shape(decl, inner)?;
        }
        return Some(inner);
    }
    // y fully stuck (rigid/meta) → old `match y` stuck.
    None
}

/// `nat_mul x y` — old `match y {0 => zero; succ n => add x (mul x n)}`.
/// Concrete pairs use the native u64 fast path; a stuck `succ` chain of `y`
/// unfolds one step (`x * succ d ⇒ x + (x * d)`) exactly like the old
/// recursion — the `double_mul`-style proofs in test_prove_term_pure rely on
/// this reducibility.
fn nat_mul(infer: &Infer, decl: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.len() < 2 { return None; }
    let x = args[0].clone();
    let y = infer.force(decl, &args[1]);
    // y ≡ 0 → 0 (unconditional: old `case zero => zero` ignores x).
    if nat_concrete(infer, decl, &y) == Some(0) {
        return Some(Val::Nat(0).into());
    }
    // both concrete → native u64 fast path.
    if let (Some(a), Some(b)) = (nat_concrete(infer, decl, &x), nat_concrete(infer, decl, &y)) {
        return a.checked_mul(b).map(|k| Val::Nat(k).into());
    }
    // y ≡ succ⟨d⟩ (stuck chain) → x + (x * d); inner left to force.
    if let Some(d) = nat_succ_inner(y.as_ref()) {
        let inner = stuck_decl("nat_mul", &[x.clone(), d.clone()]);
        return Some(stuck_decl("nat_add", &[x, inner]));
    }
    // y ≡ Nat(k > 0), x not concrete → unfold the k-fold add chain exactly
    // like the old recursion (`x * 0 = 0`, `x * k = x + (x * (k-1))`).
    // For k = 1 this is `x + 0`, which `nat_add` further reduces to `x`
    // (so `pow2(m) * 1 = pow2(m)` — relied on by double_step in
    // test_prove_term_pure).
    if let Val::Nat(k) = y.as_ref() {
        let mut acc: Rc<Val> = Val::Nat(0).into();
        for _ in 0..*k {
            acc = stuck_decl("nat_add", &[x.clone(), acc]);
        }
        return Some(acc);
    }
    // y fully stuck → old `match y` stuck.
    None
}

/// `nat_sub x y` — old `match x {0 => 0; succ k => match y {0 => succ k;
/// succ l => sub k l}}`.  Reducibility is driven by `x` first.
fn nat_sub(infer: &Infer, decl: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.len() < 2 { return None; }
    let x = infer.force(decl, &args[0]);
    let y = infer.force(decl, &args[1]);
    let xc = nat_concrete(infer, decl, &x);
    let yc = nat_concrete(infer, decl, &y);
    // x ≡ 0 → 0 regardless of y (old outer `match x` takes the zero branch
    // without inspecting y — `0 - m = 0` holds even for stuck m).
    if xc == Some(0) {
        return Some(Val::Nat(0).into());
    }
    // both concrete → truncated subtraction (n exhausts to 0).
    if let (Some(a), Some(b)) = (xc, yc) {
        return Some(Val::Nat(a.saturating_sub(b)).into());
    }
    // x ≡ succ⟨dx⟩: outer match fired.
    if let Some(dx) = nat_succ_inner(x.as_ref()) {
        return match yc {
            // y ≡ 0 → x (`succ k - 0 = succ k`).
            Some(0) => Some(x),
            // y concrete > 0 → step once: `nat_sub dx (y-1)`; force iterates.
            Some(b) => Some(stuck_decl("nat_sub", &[dx.clone(), Val::Nat(b - 1).into()])),
            // y ≡ succ⟨dy⟩ → step both: `nat_sub dx dy`; force iterates.
            _ => nat_succ_inner(y.as_ref())
                .map(|dy| stuck_decl("nat_sub", &[dx.clone(), dy.clone()])),
        };
    }
    // x rigid (incl. `x - 0`): old outer `match x` stuck — must NOT return x.
    None
}

/// `nat_div x y` / `nat_rem x y` — old definitions: `x=0 → 0`, else
/// `y=0 → x`, else structural recursion.  Only the fully-concrete fast path
/// is implemented; both return `x` when `y == 0` (covers `0/0=0` and
/// `x>0/0=x` uniformly) and the truncated `x/y` / `x%y` otherwise.
fn nat_div(infer: &Infer, decl: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.len() < 2 { return None; }
    let x = nat_concrete(infer, decl, &args[0]);
    let y = nat_concrete(infer, decl, &args[1]);
    match (x, y) {
        (Some(a), Some(0)) => Some(Val::Nat(a).into()),
        (Some(a), Some(b)) => Some(Val::Nat(a / b).into()),
        _ => None,
    }
}

fn nat_rem(infer: &Infer, decl: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.len() < 2 { return None; }
    let x = nat_concrete(infer, decl, &args[0]);
    let y = nat_concrete(infer, decl, &args[1]);
    match (x, y) {
        (Some(a), Some(0)) => Some(Val::Nat(a).into()),
        (Some(a), Some(b)) => Some(Val::Nat(a % b).into()),
        _ => None,
    }
}

/// Minimal context for hover display — only stores what pretty_tm/quote actually needs.
#[derive(Debug, Clone)]
pub struct HoverCxt {
    pub lvl: Lvl,
    pub locals: Locals,
    pub decl: Rc<Decl>,
}

impl HoverCxt {
    pub fn names(&self) -> List<SmolStr> {
        fn go(locals: &Locals) -> List<SmolStr> {
            match locals {
                Locals::Here => List::new(),
                Locals::Define(locals, name, _, _) => go(locals).prepend(name.data.clone()),
                Locals::Bind(locals, name, _) => go(locals).prepend(name.data.clone()),
            }
        }
        go(&self.locals)
    }
}

#[derive(Debug, Clone)]
pub struct Cxt {
    pub env: Env, // Used for evaluation
    pub lvl: Lvl, // Used for unification
    pub locals: Locals,
    pub pruning: Pruning,
    pub src_names: Rc<BiMap<SmolStr, Lvl, (Span<()>, Rc<VTy>)>>,
    pub decl: Rc<Decl>,
    pub namespace: List<(Rc<Val>, HashSet<SmolStr>, SmolStr)>,
    pub namespace_prefix: Option<SmolStr>,
    pub namespaces: Rc<HashSet<SmolStr>>,
    update_from: Option<usize>,
    /// The name of the current let-binding being elaborated.
    /// Used to synthesize implicit `BindingName` arguments.
    pub binding_name: Option<SmolStr>,
}

fn string_concat(_: &Infer, _: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.len() < 2 { return None; }
    match (args[0].as_ref(), args[1].as_ref()) {
        (Val::LiteralIntro(a), Val::LiteralIntro(b)) => {
            Some(Val::LiteralIntro(a.clone().map(|x| format!("{x}{}", b.data))).into())
        },
        _ => None,
    }
}

fn str_eq(_: &Infer, decl: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.len() < 2 { return None; }
    match (args[0].as_ref(), args[1].as_ref()) {
        (Val::LiteralIntro(a), Val::LiteralIntro(b)) => {
            let eq = a.data == b.data;
            let name = if eq { "true" } else { "false" };
            Some(decl.get(name).map(|x| x.2.clone()).unwrap_or(Val::Decl(empty_span(SmolStr::new(name)), List::new()).into()))
        },
        _ => None,
    }
}

/// Indent each line in a string by 2 spaces (for multi-line Verilog strings)
fn str_indent2(_: &Infer, _decl: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.is_empty() { return None; }
    match args[0].as_ref() {
        Val::LiteralIntro(s) => {
            let indented = s.data.replace('\n', "\n  ");
            Some(Val::LiteralIntro(empty_span(indented)).into())
        },
        _ => None,
    }
}

/// HDL self-check reporting (hdl-check.typort): append one
/// "code|module|signal|message" line to the mutable global
/// "CheckIssues", skipping lines already present (field re-evaluation
/// replays each module's close-check ~3x, and re-instantiating a child
/// module re-runs its constructor — line-level dedup keeps the report
/// idempotent). Drained per decl by lib.rs / run_with_prelude.
fn report_check_issue(infer: &Infer, _decl: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.len() < 4 { return None; }
    let get = |i: usize| match args[i].as_ref() {
        Val::LiteralIntro(s) => s.data.to_string(),
        _ => String::new(),
    };
    let (code, module, signal, message) = (get(0), get(1), get(2), get(3));
    if code.is_empty() || module.is_empty() { return Some(Val::U(0).into()); }
    let line = format!("{}|{}|{}|{}", code, module, signal, message);
    if let Ok(mut map) = infer.mutable_map.write() {
        let existing = match map.get("CheckIssues") {
            Some(v) => match v.as_ref() {
                Val::LiteralIntro(s) => s.data.clone(),
                _ => String::new(),
            },
            None => String::new(),
        };
        if !existing.split('\n').any(|l| l == line) {
            let next = if existing.is_empty() { line } else { format!("{}\n{}", existing, line) };
            map.insert("CheckIssues".to_string(), Rc::new(Val::LiteralIntro(empty_span(next))));
        }
    }
    Some(Val::U(0).into())
}

fn string_to_global_type(infer: &Infer, decl: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.is_empty() { return None; }
    match args[0].as_ref() {
        Val::LiteralIntro(a) => {
            Some(infer.eval(decl, &List::new(), &Tm::Decl(a.clone().map(|a| SmolStr::new(a))).into()))
        }
        _ => None,
    }
}

fn create_global(infer: &Infer, _decl: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.len() < 2 { return None; }
    match args[0].as_ref() {
        Val::LiteralIntro(a) => {
            if let Ok(mut x) = infer.mutable_map.write() {
                x.insert(a.data.clone(), args[1].clone());
            };
            Some(Val::U(0).into())
        }
        _ => None,
    }
}

fn change_mutable(infer: &Infer, decl: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.len() < 2 { return None; }
    match args[0].as_ref() {
        Val::LiteralIntro(a) => {
            if let Ok(mut x) = infer.mutable_map.write() {
                if let Some(x) = x.get_mut(&a.data) {
                    *x = infer.v_app(
                        decl,
                        &args[1],
                        x.clone(),
                        Icit::Expl
                    )
                }
            };
            Some(Val::U(0).into())
        }
        _ => None,
    }
}

fn get_global(infer: &Infer, _: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.is_empty() { return None; }
    match args[0].as_ref() {
        Val::LiteralIntro(a) => {
            Some(infer.mutable_map.write().unwrap().get(&a.data).unwrap().clone())
        }
        _ => None,
    }
}

/// Pure read of a mutable global with a fallback default — unlike
/// `change_mutable_default` it never WRITES the map, so calling it during
/// declaration-time check evaluation (L13's match/let check evaluates let
/// values for their types) cannot pollute design-level globals like
/// `ModuleTree`.  Missing key → `args[1]` (the default), same shape as
/// `change_mutable_default`'s `z` argument.
fn get_global_default(infer: &Infer, _: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.len() < 2 { return None; }
    match args[0].as_ref() {
        Val::LiteralIntro(a) => {
            let map = infer.mutable_map.read().unwrap();
            Some(map.get(&a.data).cloned().unwrap_or_else(|| args[1].clone()))
        }
        _ => None,
    }
}

/// Verilog-compat named-port connection (`child u1 (.a(x), .y(w))`): the
/// prelude's VExpr instance arm passes the child's OWN `tree` (fresh
/// values — the design-wide ModuleRegistry can hold stuck Match values
/// built through registerModuleTree's lambda, so it is not consulted), the
/// child-port Expr (`subSignal` constructor value) and the connected
/// signal's Expr. This builtin classifies the port direction by walking the
/// child tree (per-step force) and emits the assign through the prelude
/// helper `vconnEmit` (pickAssign-shaped) via v_app. All-typort versions of
/// this dispatch looped declaration-time elaboration; see
/// hdl-verilog-compat.typort.
fn vconn_builtin(infer: &Infer, decl: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    let noop = || Some(Rc::new(Val::U(0)));
    if args.len() < 3 { return None; }
    let child_tree = args[0].clone();
    let port = args[1].clone();
    let sig = args[2].clone();
    // The applied-ctor name of a SumCase value, resolved through its type's
    // constructor table (index-stable without hardcoding enum order).
    let ctor_name = |v: &Val| -> Option<String> {
        match v {
            Val::SumCase { typ, index, .. } => match typ.as_ref() {
                Val::Sum(_, _, cases, _) => cases.get(*index as usize).map(|n| n.data.to_string()),
                _ => None,
            },
            _ => None,
        }
    };
    if ctor_name(&port).as_deref() != Some("subSignal") { return noop(); }
    let pdata = match port.as_ref() { Val::SumCase { datas, .. } => datas, _ => return noop() };
    let lit_str = |v: &Rc<Val>| -> Option<String> {
        match v.as_ref() { Val::LiteralIntro(s) => Some(s.data.clone()), _ => None }
    };
    let pname = match pdata.get(1).and_then(|d| lit_str(&d.1)) { Some(s) => s, None => return noop() };
    let force = |v: &Rc<Val>| infer.force(decl, v);
    let field = |v: &Rc<Val>, name: &str| -> Option<Rc<Val>> {
        match v.as_ref() {
            Val::SumCase { datas, .. } => datas.iter().find(|d| d.0.data == name).map(|d| d.1.clone()),
            _ => None,
        }
    };
    let field_str = |v: &Rc<Val>, name: &str| -> Option<String> {
        field(v, name).and_then(|x| match x.as_ref() { Val::LiteralIntro(s) => Some(s.data.clone()), _ => None })
    };
    // child tree is a ModuleTree STRUCT — take `data`, then the head
    // ModuleDef's `expr` list, and scan the port declarations for `pname`.
    let data = match field(&force(&child_tree), "data") { Some(v) => force(&v), None => return noop() };
    let head_def = match field(&data, "x") { Some(v) => force(&v), None => return noop() };
    let mut is_input = false;
    let mut cur = match field(&head_def, "expr") { Some(v) => force(&v), None => return noop() };
    while let Some("cons") = ctor_name(&cur).as_deref() {
        let (x, xs) = match (field(&cur, "x"), field(&cur, "xs")) { (Some(x), Some(xs)) => (x, xs), _ => break };
        let xf = force(&x);
        let cn = ctor_name(&xf).unwrap_or_default();
        if matches!(cn.as_str(), "createIn" | "createInWidth" | "createSIntInWidth")
            && field_str(&xf, "name").as_deref() == Some(pname.as_str()) {
            is_input = true;
            break;
        }
        cur = force(&xs);
    }
    let bool_name = if is_input { "Boolean.true" } else { "Boolean.false" };
    let b = match decl.get(&SmolStr::new(bool_name)).map(|e| e.2.clone()) { Some(v) => v, None => return noop() };
    if let Some(emit) = decl.get(&SmolStr::new("vconnEmit")).map(|e| e.2.clone()) {
        let e = infer.v_app(decl, &emit, b, Icit::Expl);
        let e = infer.v_app(decl, &e, port, Icit::Expl);
        let _ = infer.v_app(decl, &e, sig, Icit::Expl);
    }
    noop()
}

fn change_mutable_default(infer: &Infer, decl: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.len() < 3 { return None; }
    match args[0].as_ref() {
        Val::LiteralIntro(a) => {
            if let Ok(mut x) = infer.mutable_map.write() {
                if let Some(x) = x.get_mut(&a.data) {
                    *x = infer.v_app(
                        decl,
                        &args[1],
                        x.clone(),
                        Icit::Expl
                    )
                } else {
                    x.insert(a.data.clone(), args[2].clone());
                }
            };
            Some(Val::U(0).into())
        }
        _ => None,
    }
}

fn file_read_all_text(_: &Infer, _: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.is_empty() { return None; }
    match args[0].as_ref() {
        Val::LiteralIntro(path) => {
            let content = std::fs::read_to_string(&path.data)
                .unwrap_or_else(|e| panic!("file_read_all_text: failed to read '{}': {}", path.data, e));
            Some(Val::LiteralIntro(path.clone().map(|_| content.clone())).into())
        },
        _ => None,
    }
}

fn file_write_all_text(_: &Infer, _: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.len() < 2 { return None; }
    match (args[0].as_ref(), args[1].as_ref()) {
        (Val::LiteralIntro(path), Val::LiteralIntro(content)) => {
            std::fs::write(&path.data, &content.data)
                .unwrap_or_else(|e| panic!("file_write_all_text: failed to write '{}': {}", path.data, e));
            Some(Val::U(0).into())
        },
        _ => None,
    }
}

fn file_append_all_text(_: &Infer, _: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.len() < 2 { return None; }
    match (args[0].as_ref(), args[1].as_ref()) {
        (Val::LiteralIntro(path), Val::LiteralIntro(content)) => {
            use std::io::Write;
            let mut file = std::fs::OpenOptions::new()
                .append(true)
                .create(true)
                .open(&path.data)
                .unwrap_or_else(|e| panic!("file_append_all_text: failed to open '{}': {}", path.data, e));
            write!(file, "{}", content.data)
                .unwrap_or_else(|e| panic!("file_append_all_text: failed to append to '{}': {}", path.data, e));
            Some(Val::U(0).into())
        },
        _ => None,
    }
}

fn file_exists(_: &Infer, _: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.is_empty() { return None; }
    match args[0].as_ref() {
        Val::LiteralIntro(path) => {
            let exists = std::path::Path::new(&path.data).exists();
            Some(Val::LiteralIntro(path.clone().map(|_| if exists { "true".to_string() } else { "false".to_string() })).into())
        },
        _ => None,
    }
}

fn file_delete(_: &Infer, _: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.is_empty() { return None; }
    match args[0].as_ref() {
        Val::LiteralIntro(path) => {
            std::fs::remove_file(&path.data)
                .unwrap_or_else(|e| panic!("file_delete: failed to delete '{}': {}", path.data, e));
            Some(Val::U(0).into())
        },
        _ => None,
    }
}

// === helpers for building Tm trees ===

pub(super) fn tm_lam(names: &[&str], inner: Rc<Tm>) -> Rc<Tm> {
    names.iter().rev().fold(inner, |acc, name|
        Tm::Lam(empty_span(SmolStr::new(*name)), Icit::Expl, acc).into())
}

pub(super) fn tm_pi(args: &[(&str, Rc<Tm>)], ret: Rc<Tm>) -> Rc<Tm> {
    args.iter().rev().fold(ret, |acc, (name, ty)|
        Tm::Pi(empty_span(SmolStr::new(*name)), Icit::Expl, ty.clone(), acc).into())
}

pub(super) fn tm_decl(name: &str) -> Rc<Tm> {
    Tm::Decl(empty_span(SmolStr::new(name))).into()
}

pub(super) fn tm_app(f: Rc<Tm>, arg: Rc<Tm>) -> Rc<Tm> {
    Tm::App(f, arg, Icit::Expl).into()
}

impl Cxt {
    pub fn new(infer: &Infer) -> Self {
        let mut cxt = Self::empty();

        cxt = cxt.decl(
            empty_span(SmolStr::new("String")),
            Tm::LiteralType.into(),
            Val::LiteralType.into(),
            Tm::U(0).into(),
            Val::U(0).into(),
            None,
            String::new(),
        ).unwrap();

        cxt = cxt.add_builtin(infer, "string_concat",
            tm_pi(&[("x", tm_decl("String")), ("y", tm_decl("String"))], tm_decl("String")),
            PrimFunc(Rc::new(string_concat)),
        ).unwrap();

        cxt = cxt.add_builtin(infer, "str_eq",
            tm_pi(&[("x", tm_decl("String")), ("y", tm_decl("String"))], tm_decl("Boolean")),
            PrimFunc(Rc::new(str_eq)),
        ).unwrap();

        cxt = cxt.add_builtin(infer, "str_indent2",
            tm_pi(&[("x", tm_decl("String"))], tm_decl("String")),
            PrimFunc(Rc::new(str_indent2)),
        ).unwrap();

        cxt = cxt.add_builtin(infer, "report_check_issue",
            tm_pi(&[
                ("code", tm_decl("String")),
                ("module", tm_decl("String")),
                ("signal", tm_decl("String")),
                ("message", tm_decl("String")),
            ], Tm::U(0).into()),
            PrimFunc(Rc::new(report_check_issue)),
        ).unwrap();

        cxt = cxt.add_builtin(infer, "string_to_global_type",
            tm_pi(&[("x", tm_decl("String"))], Tm::U(0).into()),
            PrimFunc(Rc::new(string_to_global_type)),
        ).unwrap();

        cxt = cxt.add_builtin(infer, "create_global",
            tm_pi(&[
                ("x", tm_decl("String")),
                ("y", tm_app(tm_decl("string_to_global_type"), Tm::Var(Ix(0)).into())),
            ], Tm::U(0).into()),
            PrimFunc(Rc::new(create_global)),
        ).unwrap();

        cxt = cxt.add_builtin(infer, "change_mutable",
            tm_pi(&[
                ("x", tm_decl("String")),
                ("f", tm_pi(&[
                    ("_", tm_app(tm_decl("string_to_global_type"), Tm::Var(Ix(0)).into())),
                ], tm_app(tm_decl("string_to_global_type"), Tm::Var(Ix(1)).into()))),
            ], Tm::U(0).into()),
            PrimFunc(Rc::new(change_mutable)),
        ).unwrap();

        cxt = cxt.add_builtin(infer, "get_global",
            tm_pi(&[("x", tm_decl("String"))],
                tm_app(tm_decl("string_to_global_type"), Tm::Var(Ix(0)).into())),
            PrimFunc(Rc::new(get_global)),
        ).unwrap();

        cxt = cxt.add_builtin(infer, "get_global_default",
            tm_pi(&[
                ("x", tm_decl("String")),
                ("z", tm_app(tm_decl("string_to_global_type"), Tm::Var(Ix(0)).into())),
            ], tm_app(tm_decl("string_to_global_type"), Tm::Var(Ix(1)).into())),
            PrimFunc(Rc::new(get_global_default)),
        ).unwrap();

        cxt = cxt.add_builtin(infer, "change_mutable_default",
            tm_pi(&[
                ("x", tm_decl("String")),
                ("f", tm_pi(&[
                    ("_", tm_app(tm_decl("string_to_global_type"), Tm::Var(Ix(0)).into())),
                ], tm_app(tm_decl("string_to_global_type"), Tm::Var(Ix(1)).into()))),
                ("z", tm_app(tm_decl("string_to_global_type"), Tm::Var(Ix(1)).into())),
            ], Tm::U(0).into()),
            PrimFunc(Rc::new(change_mutable_default)),
        ).unwrap();

        cxt = cxt.add_builtin(infer, "file_read_all_text",
            tm_pi(&[("path", tm_decl("String"))], tm_decl("String")),
            PrimFunc(Rc::new(file_read_all_text)),
        ).unwrap();

        cxt = cxt.add_builtin(infer, "file_write_all_text",
            tm_pi(&[("path", tm_decl("String")), ("content", tm_decl("String"))], Tm::U(0).into()),
            PrimFunc(Rc::new(file_write_all_text)),
        ).unwrap();

        cxt = cxt.add_builtin(infer, "file_append_all_text",
            tm_pi(&[("path", tm_decl("String")), ("content", tm_decl("String"))], Tm::U(0).into()),
            PrimFunc(Rc::new(file_append_all_text)),
        ).unwrap();

        cxt = cxt.add_builtin(infer, "file_exists",
            tm_pi(&[("path", tm_decl("String"))], tm_decl("String")),
            PrimFunc(Rc::new(file_exists)),
        ).unwrap();

        cxt = cxt.add_builtin(infer, "file_delete",
            tm_pi(&[("path", tm_decl("String"))], Tm::U(0).into()),
            PrimFunc(Rc::new(file_delete)),
        ).unwrap();

        cxt
    }

    pub fn add_builtin(self, infer: &Infer, name: &str, ty: Rc<Tm>, prim: PrimFunc) -> Result<Self, Error> {
        let va = infer.eval(&self.decl, &self.env, &ty);
        let name_span = empty_span(SmolStr::new(name));
        let val_tm = Tm::Decl(name_span.clone()).into();
        let vt = Val::Decl(name_span.clone(), List::new()).into();
        self.decl(name_span, val_tm, vt, ty, va, Some(prim), String::new())
    }

    /// Register nat builtins (nat_to_dec + word-size nat arithmetic primops).
    /// Must be called AFTER nat.typort is loaded.
    /// Verilog-compat named-port connection builtin. Registered AFTER the
    /// prelude loads (like register_nat_builtins): its signature mentions
    /// prelude types (ModuleTree / Expr) that do not exist at Cxt::new
    /// time — an eagerly-registered tm_decl("ModuleTree") stays a dangling
    /// neutral that loops later unifications.
    pub(crate) fn register_vconn_builtin(cxt: &mut Cxt, infer: &Infer) {
        let old = std::mem::replace(cxt, Self::empty());
        *cxt = old.add_builtin(infer, "vconnT",
            tm_pi(&[
                ("childTree", tm_decl("ModuleTree")),
                ("port", tm_decl("Expr")),
                ("sig", tm_decl("Expr")),
            ], Tm::U(0).into()),
            PrimFunc(Rc::new(vconn_builtin)),
        ).unwrap();
    }

    pub(crate) fn register_nat_builtins(cxt: &mut Cxt, infer: &Infer) {
        let f_nat_to_dec = PrimFunc(Rc::new(nat_to_dec));
        let old = std::mem::replace(cxt, Self::empty());
        *cxt = old.add_builtin(infer, "nat_to_dec",
            tm_pi(&[("n", tm_decl("Nat"))], tm_decl("String")),
            f_nat_to_dec,
        ).unwrap();

        let old2 = std::mem::replace(cxt, Self::empty());
        *cxt = old2.add_builtin(infer, "width_range",
            tm_pi(&[("w", tm_decl("Nat"))], tm_decl("String")),
            PrimFunc(Rc::new(width_range)),
        ).unwrap();

        // Is the Nat a ground (fully evaluated) number? Distinguishes widths
        // that reached the module tree as real numbers from widths frozen as
        // unevaluated elaboration-time variables (the typeclass instance Nat
        // param bug freezes class-parameterized widths as dangling Rigid
        // values — see docs/l13-typeclass-instance-nat-param-bug.md). The
        // HDL self-check uses it to report the silent 1-bit degradation.
        let old3 = std::mem::replace(cxt, Self::empty());
        *cxt = old3.add_builtin(infer, "nat_is_ground",
            tm_pi(&[("w", tm_decl("Nat"))], tm_decl("Boolean")),
            PrimFunc(Rc::new(nat_is_ground)),
        ).unwrap();

        // Nat arithmetic primops (replacing the structural recursion in
        // prelude/core/nat.typort).  nat_sub replaces the old `def nat_sub`;
        // the other four replace `nat_*_helper`.  nat_max / nat_min / pred
        // stay as recursive defs (cold, and nat_max/min have no operator
        // binding to restore).
        let nat_binop = tm_pi(&[("x", tm_decl("Nat")), ("y", tm_decl("Nat"))], tm_decl("Nat"));
        for (name, prim) in [
            ("nat_add", nat_add as fn(&Infer, &Decl, &[Rc<Val>]) -> Option<Rc<Val>>),
            ("nat_mul", nat_mul),
            ("nat_sub", nat_sub),
            ("nat_div", nat_div),
            ("nat_rem", nat_rem),
        ] {
            let old = std::mem::replace(cxt, Self::empty());
            *cxt = old.add_builtin(infer, name, nat_binop.clone(), PrimFunc(Rc::new(prim))).unwrap();
        }
    }

    pub fn empty() -> Self {
        Cxt {
            env: List::new(),
            lvl: Lvl(0),
            locals: Locals::Here,
            pruning: List::new(),
            src_names: Rc::new(BiMap::new()),
            decl: Rc::new(Decl::default()),
            namespace: List::new(),
            namespace_prefix: None,
            namespaces: Rc::new(HashSet::new()),
            update_from: None,
            binding_name: None,
        }
    }
    pub fn clone_without_src_names(&self) -> Self {
        Cxt {
            env: self.env.clone(),
            lvl: self.lvl,
            locals: self.locals.clone(),
            pruning: self.pruning.clone(),
            src_names: Rc::new(BiMap::new()),
            decl: self.decl.clone(),
            namespace: self.namespace.clone(),
            namespace_prefix: self.namespace_prefix.clone(),
            namespaces: self.namespaces.clone(),
            update_from: self.update_from,
            binding_name: self.binding_name.clone(),
        }
    }

    pub fn names(&self) -> List<SmolStr> {
        fn go(locals: &Locals) -> List<SmolStr> {
            match locals {
                Locals::Here => List::new(),
                Locals::Define(locals, name, _, _) => go(locals).prepend(name.data.clone()),
                Locals::Bind(locals, name, _) => go(locals).prepend(name.data.clone()),
            }
        }
        go(&self.locals)
    }

    pub fn bind(&self, x: Span<SmolStr>, a_quote: Rc<Tm>, a: Rc<Val>) -> Self {
        //println!("{} {x:?} {a:?} at {}", "bind".bright_purple(), self.lvl.0);
        let mut src_names = self.src_names.clone();
        Rc::make_mut(&mut src_names).insert(x.data.clone(), (self.lvl, (x.to_span(), a)));
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl).into()),
            lvl: self.lvl + 1,
            locals: Locals::Bind(Rc::new(self.locals.clone()), x, a_quote),
            pruning: self.pruning.prepend(Some(Icit::Expl)),
            src_names,
            decl: self.decl.clone(),
            namespace: self.namespace.clone(),
            namespace_prefix: self.namespace_prefix.clone(),
            namespaces: self.namespaces.clone(),
            update_from: self.update_from,
            binding_name: None,
        }
    }

    pub fn fake_bind(&self, x: Span<SmolStr>, a_quote: Rc<Tm>, a: Rc<Val>) -> Result<Self, Error> {
        //println!("{} {x:?} {a:?} at {}", "bind".bright_purple(), self.lvl.0);
        let mut decl = self.decl.clone();
        let decl_map = Rc::make_mut(&mut decl);
        let t = decl_map.insert(x.data.clone(), (x.to_span(), Tm::Decl(x.clone()).into(), Val::Decl(x.clone(), List::new()).into(), a_quote, a, None, String::new()));
        if t.is_some() {
            return Err(Error(x.to_span().map(|_| format!("redefine {}", x.data)), vec![]));
        }
        Ok(Cxt {
            env: self.env.clone(),
            lvl: self.lvl,
            locals: self.locals.clone(),
            pruning: self.pruning.clone(),
            src_names: self.src_names.clone(),
            decl,
            namespace: self.namespace.clone(),
            namespace_prefix: self.namespace_prefix.clone(),
            namespaces: self.namespaces.clone(),
            update_from: self.update_from,
            binding_name: self.binding_name.clone(),
        })
    }

    pub fn new_binder(&self, x: Span<SmolStr>, a_quote: Rc<Tm>) -> Self {
        //println!("{} {x:?} {a:?} at {}", "bind".bright_purple(), self.lvl.0);
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl).into()),
            lvl: self.lvl + 1,
            locals: Locals::Bind(Rc::new(self.locals.clone()), x, a_quote),
            pruning: self.pruning.prepend(Some(Icit::Expl)),
            src_names: self.src_names.clone(),
            decl: self.decl.clone(),
            namespace: self.namespace.clone(),
            namespace_prefix: self.namespace_prefix.clone(),
            namespaces: self.namespaces.clone(),
            update_from: self.update_from,
            binding_name: None,
        }
    }

    /// Bind a new local definition. The caller's `binding_name` is preserved:
    /// a let's continuation (or a trait-dispatch wrapper's rest) is still in
    /// the same binding context, so implicit `BindingName` parameters of
    /// factories elaborated there keep the caller's let-binding name (e.g.
    /// the receiver `AxiLite.create` inside an asMaster dispatch must produce
    /// `master_awaddr`-named wires, not bare `awaddr` ones that escape the
    /// port-shadowing in hdl-verilog.typort). Module/class body items set
    /// their own name explicitly via `with_binding_name` before checking.
    pub fn define(&self, x: Span<SmolStr>, t: Rc<Tm>, vt: Rc<Val>, a: Rc<Ty>, va: Rc<VTy>) -> Self {
        //println!("{} {}\n{t:?}\n{vt:?}\n{a:?}\n{va:?}", "define".bright_purple(), x.data);
        let mut src_names = self.src_names.clone();
        Rc::make_mut(&mut src_names).insert(x.data.clone(), (self.lvl, (x.to_span(), va)));
        Cxt {
            env: self.env.prepend(vt),
            lvl: self.lvl + 1,
            locals: Locals::Define(Rc::new(self.locals.clone()), x, a, t),
            pruning: self.pruning.prepend(None),
            src_names,
            decl: self.decl.clone(),
            namespace: self.namespace.clone(),
            namespace_prefix: self.namespace_prefix.clone(),
            namespaces: self.namespaces.clone(),
            update_from: self.update_from,
            binding_name: self.binding_name.clone(),
        }
    }

    /// `typ_pretty` is the def-site rendering of the declared type (computed
    /// with the elaboration context's own names).  Stored alongside the raw
    /// `Tm` because the raw term can embed `AppPruning(Meta, pr)` whose
    /// pruning is deeper than any display-side name list — hover must show
    /// the precomputed string instead of re-pretty-printing without context.
    pub fn decl(&self, x: Span<SmolStr>, t: Rc<Tm>, vt: Rc<Val>, a: Rc<Ty>, va: Rc<VTy>, prim: Option<PrimFunc>, typ_pretty: String) -> Result<Self, Error> {
        let mut decl = self.decl.clone();
        let decl_map = Rc::make_mut(&mut decl);
        // prim-ness transitions invalidate the force memo (see
        // `PRIM_VERSION`): registering a prim (`register_nat_builtins`,
        // startup builtins) or shadowing one with a plain def both change
        // what `force` computes for spines of that name.
        let had_prim = decl_map.get(&x.data).map_or(false, |e| e.5.is_some());
        let now_prim = prim.is_some();
        decl_map.insert(x.data.clone(), (x.to_span(), t, vt, a, va, prim, typ_pretty));
        if had_prim != now_prim {
            super::prim_version_bump();
        }
        Ok(Cxt {
            env: self.env.clone(),
            lvl: self.lvl,
            locals: self.locals.clone(),
            pruning: self.pruning.clone(),
            src_names: self.src_names.clone(),
            decl,
            namespace: self.namespace.clone(),
            namespace_prefix: self.namespace_prefix.clone(),
            namespaces: self.namespaces.clone(),
            update_from: self.update_from,
            binding_name: self.binding_name.clone(),
        })
    }

    /// freshVal 函数实现
    /// 参考 Haskell 代码: freshVal def from to = eval def to . quote def from (Lvl (length from))
    pub fn fresh_val(&self, infer: &Infer, from: &Env, to: &Env, val: &Rc<Val>) -> Rc<Val> {
        // quote def from (Lvl (length from))
        let quoted = infer.quote(&self.decl, Lvl(from.len() as u32), val);

        // eval def to
        infer.eval(&self.decl, to, &quoted)
    }

    pub fn update_cxt(&self, infer: &Infer, x: Lvl, v: Rc<Val>, update_prune: bool) -> Cxt {
        match v.as_ref() {
            Val::Flex(..) => self.clone(),
            _ => {
                let update_from = if let Some(u) = self.update_from {
                    if u < x.0 as usize {
                        u
                    } else {
                        x.0 as usize
                    }
                } else {
                    x.0 as usize
                };
                let x_prime = lvl2ix(self.lvl, x).0 as usize;
                /*println!(
                    " update {}: {} with {}",
                    x.0,
                    pretty_tm(0, self.names(), &infer.quote(self.lvl, self.env.iter().nth(x_prime).unwrap().clone())),
                    pretty_tm(0, self.names(), &infer.quote(self.lvl, v.clone()))
                );*/
                //let locals = self.locals.update_at(x_prime, infer.quote(&self.decl, self.lvl, &v));
                let env = self.env.change_n(x_prime, |_| v);
                let mut new_src_names = self.src_names.clone();
                let env_t = self.refresh(infer, &self.env, Rc::make_mut(&mut new_src_names), env, self.lvl.0 as usize - update_from);
                let locals = self.locals.clone().update_by_cxt(infer, &self.decl, self.lvl, &env_t);
        
                Cxt {
                    env: env_t,
                    lvl: self.lvl,
                    locals: if update_prune {locals} else {self.locals.clone()},//TODO: lookup env_t, if is not Val::vavar(lvl), set local to Define
                    //locals: self.locals.clone().update_by_cxt(infer, &self.decl, self.lvl, &self.env),
                    //locals,
                    pruning: if update_prune {self.pruning.change_n(x_prime, |_| None)} else {self.pruning.clone()},
                    src_names: new_src_names,
                    decl: self.decl.clone(),
                    namespace: self.namespace.clone(),
                    namespace_prefix: self.namespace_prefix.clone(),
                    namespaces: self.namespaces.clone(),
                    update_from: Some(update_from),
                    binding_name: self.binding_name.clone(),
                }
            }
        }
    }

    fn refresh(&self, infer: &Infer, env: &List<Rc<Val>>, src_names: &mut BiMap<SmolStr, Lvl, (Span<()>, Rc<Val>)>, env2: List<Rc<Val>>, walk: usize) -> List<Rc<Val>> {
        if env.is_empty() {
            List::new()
        } else {
            let env_t = if walk == 0 {env.tail()} else {self.refresh(infer, &env.tail(), src_names, env2.clone(), walk - 1)};
            let env_tt = env2.change_tail(env_t.clone());
            let ret = self.fresh_val(infer, &self.env, &env_tt, env.head().unwrap());
            /*let a = pretty_tm(0, self.names(), &infer.quote(self.lvl, env.head().unwrap().clone()));
            let b = pretty_tm(0, self.names(), &infer.quote(self.lvl, ret.clone()));
            if a != b {
                println!(
                    "refresh {}: {} with {}",
                    env.len(),
                    pretty_tm(0, self.names(), &infer.quote(self.lvl, env.head().unwrap().clone())),
                    pretty_tm(0, self.names(), &infer.quote(self.lvl, ret.clone()))
                );
            }*/
            
            let ret = env_t.prepend(ret);
            if let Some((_, x)) = src_names.get_by_key2_mut(&Lvl(env_t.len() as u32)) {
                *x = self.fresh_val(infer, &self.env, &env_tt, x);
            }
            ret
        }
    }
}

impl Cxt {
    /// Returns `true` if the environment has been refined via `update_cxt`
    /// since the last snapshot point.  Used to decide whether variable types
    /// need re-normalisation in the current environment.
    pub fn is_refined(&self) -> bool {
        self.update_from.is_some()
    }

    /// Create a copy of this context with the given binding name set.
    /// Used when elaborating the RHS of a `let` binding so that implicit
    /// `BindingName` parameters can be synthesized with the correct name.
    pub fn with_binding_name(&self, name: SmolStr) -> Self {
        Cxt {
            env: self.env.clone(),
            lvl: self.lvl,
            locals: self.locals.clone(),
            pruning: self.pruning.clone(),
            src_names: self.src_names.clone(),
            decl: self.decl.clone(),
            namespace: self.namespace.clone(),
            namespace_prefix: self.namespace_prefix.clone(),
            namespaces: self.namespaces.clone(),
            update_from: self.update_from,
            binding_name: Some(name),
        }
    }

    #[allow(unused)]
    pub fn print_env(&self, infer: &Infer) {
        self.env
            .iter()
            .zip(self.names().iter())
            .for_each(|(x, name)| {
                println!("{name}: {}", pretty_tm(0, self.names(), &infer.quote(&self.decl, self.lvl, x)))
            });
    }
}
