//! L07 <-> L13 cross-layer known-diff pins (2026-11-24, UPGRADE-L13-PLAN.md P5).
//!
//! `tests/audit_crosslayer_probe.rs` only writes TSV and never asserts, so it can
//! never go red. This file pins the CURRENT behaviour of both engines per program:
//! verdicts must agree (shared semantic core), rendering is deliberately different
//! (native Nat, namespace prefixes), and a couple of L13 relaxations are registered.

use elaboration_zoo_lsp::{L07_sum_type, L13_namespace};

fn l07(src: &str) -> Result<String, String> {
    L07_sum_type::run(src, 0).map_err(|e| e.0)
}
fn l13(src: &str) -> Result<String, String> {
    L13_namespace::run(src, 0).map_err(|e| e.0.data.to_string())
}

#[track_caller]
fn assert_same_verdict(name: &str, src: &str) {
    match (l07(src), l13(src)) {
        (Ok(_), Ok(_)) => {}
        (Err(_), Err(_)) => {}
        (a, b) => panic!(
            "[{name}] verdict diverged between L07 and L13: L07={:?} L13={:?}",
            a.is_ok(), b.is_ok()
        ),
    }
}

#[test]
fn core_programs_keep_the_same_verdict() {
    assert_same_verdict(
        "poly_id",
        "enum Bool {\n    true\n    false\n}\ndef id[A](x: A): A = x\nprintln (id true)\nprintln (id Bool)\n",
    );
    assert_same_verdict(
        "nat_add",
        "enum Nat {\n  zero\n  succ(x: Nat)\n}\ndef add(x: Nat, y: Nat): Nat = match x { case zero => y  case succ(n) => succ (add n y) }\nprintln (add (succ (succ zero)) (succ (succ zero)))\n",
    );
    assert_same_verdict(
        "ctor_eta",
        "enum Nat {\n  zero\n  succ(x: Nat)\n}\ndef f : Nat -> Nat = succ\nprintln f\n",
    );
    assert_same_verdict(
        "stuck_match",
        "enum Nat {\n  zero\n  succ(x: Nat)\n}\ndef g(n: Nat): Nat = match n { case zero => succ  case succ(k) => succ }\ndef h(n: Nat): Nat = g n\nprintln (h zero)\n",
    );
    assert_same_verdict(
        "illtyped_app",
        "enum Nat {\n  zero\n  succ(x: Nat)\n}\nprintln (succ zero zero)\n",
    );
    assert_same_verdict(
        "missing_case",
        "enum Nat {\n  zero\n  succ(x: Nat)\n}\ndef mono(n: Nat): Nat = match n { case zero => zero }\n",
    );
    // 注意：L07 的解析器不接受"单行 match 里通配臂后接第二臂"（会报
    // parse error: leftover token `def`）；L13 接受。为保证这里比的是**语义**
    // 而不是语法面，用多行写法（`.audit/raw-correctness/probe-programs.tsv` 原样）。
    assert_same_verdict(
        "unreachable_arm",
        "enum Nat {\n  zero\n  succ(x: Nat)\n}\n\ndef f(n: Nat): Nat =\n    match n {\n        case _ => zero\n        case succ(n) => n\n    }\n",
    );
}

/// Known diff #1: a `def` colliding with a constructor bare name.
/// L07 rejects it (`redefine succ`); L13 currently ACCEPTS it (registered).
#[test]
fn known_diff_redefine_ctor_name() {
    let src = "enum Nat {\n  zero\n  succ(x: Nat)\n}\ndef succ : Nat = zero\nprintln succ\n";
    assert!(l07(src).is_err(), "L07 is expected to reject the constructor-name collision");
    assert!(l13(src).is_ok(), "known diff: L13 currently accepts it (docs/l07-l13-known-diff.md)");
}

/// Known diff #2: rendering is deliberately different (native Nat vs succ chain).
#[test]
fn known_diff_nat_rendering() {
    let src = "enum Nat {\n  zero\n  succ(x: Nat)\n}\ndef two : Nat = succ (succ zero)\nprintln two\n";
    let a = l07(src).expect("L07 accepts the program");
    let b = l13(src).expect("L13 accepts the program");
    assert!(a.contains("succ"), "L07 still renders Nat as a succ chain, got: {a}");
    assert_ne!(a, b, "known diff: L07 and L13 render Nat differently");
}
