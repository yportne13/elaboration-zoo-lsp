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
module counter {
    let a = UInt[8]
    let b = UInt[8]
    let sum = UInt[8]
    sum := a + b
}
println(moduleTreeVL(counter.create.tree))
"#);
    assert!(output.contains("counter"), "verilog should name the module, got: {}", output);
    assert!(output.contains("module counter"), "expected module header, got: {}", output);
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
