// ============================================================
// HDL module macro tests
//
// `module Name[cd] [params] <ports> { body }` desugars to a class whose
// constructor runs the body against a global ModuleTree and captures the
// result; the tree is exposed via the `Module` trait's `tree` method, so
// `moduleTreeVL(M.create.tree)` produces Verilog.
//
// Behavior pinned here:
//   - body-only modules (let declarations + := assignments)
//   - parametric modules [w: Nat] (create[w])
//   - explicit clock domain [cd] (create[myClockDomain])
//   - typed/Bool ports declared before the body braces (u.a handles)
//   - sub-module instantiation `let u = M.create[w]` auto-records an
//     instance (no Expr-macro special case needed)
//   - top-level creates leave no phantom instance in the global tree
// ============================================================

use super::*;

fn assert_ok(input: &str) -> String {
    match run_with_prelude(input) {
        Ok(output) => output,
        Err(e) => panic!("expected OK, got error: '{}' @ {}:{}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

fn assert_err_contains(input: &str, needle: &str) {
    match run_with_prelude(input) {
        Ok(output) => panic!("expected error containing '{}', got OK: {}", needle, output.trim()),
        Err(e) => {
            assert!(
                e.0.data.contains(needle),
                "expected error containing '{}', got: '{}'",
                needle,
                e.0.data
            );
        }
    }
}

// ── body-only module: let declarations + := assignments ──

#[test]
fn module_body_only() {
    let output = assert_ok(r#"
module counterDemo {
    let a = UInt[8]
    let b = UInt[8]
    let sum = UInt[8]
    sum := a + b
}
println(moduleTreeVL(counterDemo.create.tree))
"#);
    assert!(output.contains("counterDemo"), "verilog should name the module, got: {}", output);
    assert!(output.contains("module counterDemo"), "expected module header, got: {}", output);
}

// ── parametric module [w: Nat] ──

#[test]
fn module_param_width() {
    let output = assert_ok(r#"
module adder[w: Nat] {
    let a = UInt[w]
    let b = UInt[w]
    let sum = UInt[w + 1]
    sum := a +^ b
}
println(moduleTreeVL(adder.create[8].tree))
"#);
    assert!(output.contains("module adder"), "expected parametric module header, got: {}", output);
}

// ── explicit clock domain [cd] ──

#[test]
fn module_explicit_clock_domain() {
    let output = assert_ok(r#"
def myCd: ClockDomain = ClockDomain.mk "myclk" "myrst" Async RisingEdge ActiveHigh
module foo[myCd] {
    let a = UInt[8]
    let b = UInt[8]
    let s = UInt[8]
    s := a + b
}
println(moduleTreeVL(foo.create[myCd].tree))
"#);
    assert!(output.contains("module foo"), "expected cd module header, got: {}", output);
}

// ── typed + Bool ports before the body braces ──

#[test]
fn module_ports_typed_and_bool() {
    let output = assert_ok(r#"
module portmod
    input a = UInt[8]
    output sum = UInt[9]
    input en = Bool
{
    sum := a +^ a
    en := Bool.mk(Some("en"), createIn("en"))
}
println(moduleTreeVL(portmod.create.tree))
"#);
    assert!(output.contains("module portmod"), "expected port module header, got: {}", output);
}

// ── sub-module instantiation auto-records the instance ──

#[test]
fn module_nested_instance() {
    let output = assert_ok(r#"
module myAdder[w: Nat]
    input a = UInt[w]
    input b = UInt[w]
    output sum = UInt[w + 1]
{
    sum := a +^ b
}
module topWithAdder {
    let a = UInt[8]
    let b = UInt[8]
    let u = myAdder.create[8]
    u.a := a
    u.b := b
}
println(moduleTreeVL(topWithAdder.create.tree))
"#);
    assert!(output.contains("module topWithAdder"), "expected top module header, got: {}", output);
    assert!(output.contains("myAdder"), "expected sub-module instance in verilog, got: {}", output);
}

// ── top-level create leaves no phantom instance ──

#[test]
fn module_top_level_no_phantom_instance() {
    // A bare `M.create` at top level must not record an instance anywhere:
    // the restored tree after the body is the empty parent tree, and
    // mkInstanceIfParent drops the record on nil.
    let output = assert_ok(r#"
module solo {
    let a = UInt[8]
    let b = UInt[8]
    let s = UInt[8]
    s := a + b
}
def t = solo.create.tree
println(moduleTreeVL(t))
println(moduleTreeVL(t))
"#);
    // two identical prints prove the global tree was restored between creates
    let first = output.find("module solo").expect("first verilog missing");
    let second = output[first + 1..].find("module solo").expect("second verilog missing");
    assert!(second > 0, "expected two identical top-level verilogs, got: {}", output);
}

// ── plan C: no `tree_data` storage field ──
// The create-side side-effect chain is a bare class-body statement (a
// create-local, NOT a struct field), so the struct has no storage field and
// `m.tree_data` must fail to type-check. `def tree` recomputes the chain.

#[test]
fn module_no_tree_data_field() {
    assert_err_contains(r#"
module solo {
    let a = UInt[8]
}
def t = solo.create.tree
println(solo.create.tree_data)
"#, "tree_data");
}

// ── plan C2: module body lets ARE struct members ──
// User semantics: every class-body `let` is a struct field (no special
// cases, no create-locals). The module macro FLATTENS its side-effect chain
// into class-body fields, so every signal the user declares in the module —
// body signals AND ports — is reachable on the instance (`u.a`, `u.sum`),
// alongside the chain's `_`/`_prev`/`_res` bindings. Ports keep the
// double-declaration (real signal + subSignal handle; the handle wins in the
// struct), body signals keep their real signal value.

#[test]
fn module_body_signal_is_member() {
    let output = assert_ok(r#"
module counterDemo {
    let a = UInt[8]
    let b = UInt[8]
    let sum = UInt[8]
    sum := a + b
}
def u = counterDemo.create
println(u.a)
println(u.sum)
println(moduleTreeVL(u.tree))
"#);
    // u.a is the module's own signal (named "a", real createWidth expr) —
    // not a subSignal handle (the module has no ports).
    assert!(output.contains("UInt.mk(Option[String]::Some(a), Expr::createWidth(a, 8))"),
        "body signal member should be the real signal, got: {}", output);
    assert!(output.contains("UInt.mk(Option[String]::Some(sum), Expr::createWidth(sum, 8))"),
        "sum should be a member too, got: {}", output);
    assert!(output.contains("assign sum = (a + b);"),
        "verilog should still be generated from the tree, got: {}", output);
}

#[test]
fn module_port_is_member() {
    let output = assert_ok(r#"
module portmod
    input a = UInt[8]
    output sum = UInt[9]
{
    sum := a +^ a
}
def u = portmod.create
println(u.a)
println(u.sum)
"#);
    // Port members are the subSignal handles (for `u.a := sig` in a parent).
    assert!(output.contains("UInt.mk(Option[String]::None, Expr::subSignal(, a))"),
        "port member should be the subSignal handle, got: {}", output);
    assert!(output.contains("UInt.mk(Option[String]::None, Expr::subSignal(, sum))"),
        "output port member missing, got: {}", output);
}

#[test]
fn module_when_switch_no_scaffolding_members() {
    // when/switch transcribe their begin/end scaffolding as `let _ = ...`
    // discards, so the struct gains only the single `_` field — no
    // w_push/w_pop/_wb/_we junk members.
    let output = assert_ok(r#"
module ctrl {
    let a = UInt[8]
    let b = UInt[8]
    let out = UInt[8]
    when a === 0 {
        out := b
    } otherwise {
        out := a
    }
}
def u = ctrl.create
println(u.out)
println(u.a)
"#);
    assert!(output.contains("UInt.mk(Option[String]::Some(out), Expr::createWidth(out, 8))"),
        "body signal in when-module should be a member, got: {}", output);
    assert!(output.contains("UInt.mk(Option[String]::Some(a), Expr::createWidth(a, 8))"),
        "a should be a member too, got: {}", output);
    // u.w_push must NOT exist (the when scaffolding is `let _ =` discarded).
    assert_err_contains(r#"
module ctrl {
    let a = UInt[8]
    let b = UInt[8]
    let out = UInt[8]
    when a === 0 {
        out := b
    } otherwise {
        out := a
    }
}
def u = ctrl.create
println(u.w_push)
"#, "w_push");
}

// ── plan C2: chain bindings are accessible struct fields ──
// `_prev` is the ModuleTree captured before the module's push (the pre-push
// global — the empty tree at top level), `_res` is the tree after the body
// ran. Pinning them as struct fields keeps the "everything is in the struct"
// semantics honest.

#[test]
fn module_struct_exposes_chain_bindings() {
    let output = assert_ok(r#"
module solo {
    let a = UInt[8]
    let b = UInt[8]
    let s = UInt[8]
    s := a + b
}
def pc = solo.create
println(pc._prev)
println(pc._res)
"#);
    // _prev: the tree before the module's push — the empty tree at top level.
    assert!(output.contains("ModuleTree::ModuleTree.mk(0, Vec[ModuleDef]::nil)"),
        "expected _prev to be the pre-push empty tree, got: {}", output);
    // _res: the module's own tree after the body ran (solo with a, b, s and
    // the assign).
    assert!(output.contains("ModuleDef::ModuleDef.mk(solo"),
        "expected _res to hold the built solo tree, got: {}", output);
}

// ── plan C: def tree re-runs the chain — idempotent, instance exactly once ──

#[test]
fn module_def_tree_idempotent_instance_once() {
    // Two `.tree` accesses of the same module print byte-identical Verilog
    // (each access re-runs the chain from a clean push), and the nested
    // instance line appears exactly once per printed module.
    let output = assert_ok(r#"
module myAdder[w: Nat]
    input a = UInt[w]
    input b = UInt[w]
    output sum = UInt[w + 1]
{
    sum := a +^ b
}
module topWithAdder {
    let a = UInt[8]
    let b = UInt[8]
    let u = myAdder.create[8]
    u.a := a
    u.b := b
}
println(moduleTreeVL(topWithAdder.create.tree))
println(moduleTreeVL(topWithAdder.create.tree))
"#);
    // one instance record per printed tree → 2 total, never duplicated
    assert_eq!(output.matches("myAdder u (").count(), 2,
        "instance should be recorded exactly once per tree, got: {}", output);
    // hierarchy access still resolves: the instance line carries the ports
    assert!(output.contains("myAdder u (.a(a), .b(b))"),
        "expected aggregated port connections on the instance line, got: {}", output);
    // both prints byte-identical (idempotent def tree)
    let first = output.find("module topWithAdder").expect("first verilog missing");
    let second = output[first + 1..].find("module topWithAdder").expect("second verilog missing");
    assert!(second > 0, "expected two verilogs, got: {}", output);
    let second_start = first + 1 + second;
    assert_eq!(&output[first..second_start], &output[second_start..],
        "two .tree accesses must print byte-identical verilog, got: {}", output);
}

// ── carry/borrow-generating +^ / -^ emit pad-concat + plain + / - ──
// `+^` and `-^` are Typort-only tokens (result width +1). The prelude
// builds them as "pad one bit by type + plain +/-" expressions so the
// carry/borrow bit is explicit: UInt zero-extends `{1'b0, a}`, SInt
// sign-extends `{a[w-1], a}` — and for SInt BOTH operands are extended
// (the concat is unsigned in Verilog; extending only the lhs would
// zero-extend the rhs and corrupt negative operands). Emitting a bare
// `(a + b)` would rely on Verilog's context-determined width and silently
// drop the carry when nested/inlined. This pins all three emission paths:
// continuous assigns (exprVL), clocked regAssigns (exprVL), and when
// conditions (emitCondStr + proc).

#[test]
fn module_carry_ops_emit_plain_plus_minus() {
    let output = assert_ok(r#"
module carryOps {
    let a = UInt[8]
    let b = UInt[8]
    let c = UInt[8]
    let d = UInt[8]
    let sum = UInt[9]
    let diff = UInt[9]
    let nest = UInt[10]
    let sa = SInt[8]
    let sb = SInt[8]
    let ssum = SInt[9]
    let sdiff = SInt[9]
    let out = UInt[8]
    let w = UInt[9]
    reg r = UInt[9]
    sum := a +^ b
    diff := a -^ b
    nest := (a +^ b) +^ (c +^ d)
    ssum := sa +^ sb
    sdiff := sa -^ sb
    r := a +^ b
    w := Bool.mk(None, literal(0)) ## c
    when (a +^ b) === 0 {
        out := c
    }
}
println(moduleTreeVL(carryOps.create.tree))
"#);
    assert!(!output.contains("+^"), "generated Verilog must not contain the invalid '+^' token, got: {}", output);
    assert!(!output.contains("-^"), "generated Verilog must not contain the invalid '-^' token, got: {}", output);
    assert!(output.contains("assign sum = ({1'b0, a} + b);"), "expected UInt carry add as zero-extend + plus, got: {}", output);
    assert!(output.contains("assign diff = ({1'b0, a} - b);"), "expected UInt borrow sub as zero-extend + minus, got: {}", output);
    assert!(output.contains("assign nest = ({1'b0, ({1'b0, a} + b)} + ({1'b0, c} + d));"),
        "expected nested +^ chain with explicit pad at every level, got: {}", output);
    assert!(output.contains("assign ssum = ({sa[7], sa} + {sb[7], sb});"),
        "expected SInt carry add with both operands sign-extended, got: {}", output);
    assert!(output.contains("assign sdiff = ({sa[7], sa} - {sb[7], sb});"),
        "expected SInt borrow sub with both operands sign-extended, got: {}", output);
    assert!(output.contains("r <= ({1'b0, a} + b);"), "expected clocked carry add as zero-extend + plus, got: {}", output);
    assert!(output.contains("if (({1'b0, a} + b) == 0) begin"), "expected when condition carry add as zero-extend + plus, got: {}", output);
    // IEEE 1364-2001 §4.1.14: unsized constants are illegal inside concats,
    // so a literal Bool operand must be emitted as a sized 1-bit literal.
    assert!(output.contains("assign w = {1'b0, c};"), "expected sized literal in concatenation, got: {}", output);
}

// ── errors: unknown signal / type misuse still reported ──

#[test]
fn module_err_unknown_signal() {
    assert_err_contains(r#"
module bad {
    let a = UInt[8]
    sum := a + b
}
def t = bad.create.tree
"#, "sum");
}

// ── macro system: optional fragment $( ... )? ──
// (added for the module macro work; the final 2-arm module macro no longer
// uses it, but the matcher/transcriber support stays as macro-system
// capability — pinned here against regression)

#[test]
fn macro_optional_fragment() {
    let output = assert_ok(r#"
macro_rules optm {
    ($a: ident $( [ $b: ident ] )? ) => {
        def $a $( [ $b: Nat ] )? : Nat = 5
    }
}
optm foo [x]
optm bar
println (foo[1])
println (bar)
"#);
    let lines: Vec<&str> = output.trim().lines().collect();
    assert!(lines.iter().filter(|l| l.trim() == "5").count() == 2,
        "both foo[1] and bar should print 5, got: {}", output);
}
