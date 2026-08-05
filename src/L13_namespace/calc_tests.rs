// ============================================================
// calc reasoning-chain tests
//
// `calc { a = b by p1 ... }` expands to a let chain of Eq-checked steps
// composed with trans. Positive cases mirror the hand-written chains in
// legacy_tests::test_prove_term_pure; negative cases pin the error shape
// (see docs/calc-reasoning-design.md §3.4).
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

// ── positive: two-step chain ──

#[test]
fn calc_two_step() {
    let output = assert_ok(r#"
def zero_add_comm_calc(n: Nat): Eq (0 + n) (n + 0) =
    calc {
        0 + n = n by add_zero_left n
        n = n + 0 by symm (add_zero_right n)
    }
def r = zero_add_comm_calc 5
println (match r { case refl(a) => a })
"#);
    assert!(output.trim() == "5", "expected 5, got: {}", output);
}

// ── positive: three-step chain (mid terms checked via trans unification) ──

#[test]
fn calc_three_step() {
    let output = assert_ok(r#"
def add_permute_calc(a: Nat, b: Nat, c: Nat): Eq ((a + b) + c) ((a + c) + b) =
    calc {
        (a + b) + c = a + (b + c) by add_assoc a b c
        a + (b + c) = a + (c + b) by cong (x => a + x) (add_comm b c)
        a + (c + b) = (a + c) + b by symm (add_assoc a c b)
    }
def r = add_permute_calc 1 2 3
println (match r { case refl(a) => a })
"#);
    assert!(output.trim() == "6", "expected 6, got: {}", output);
}

// ── positive: five-step chain mirroring hand-written double_distrib ──

#[test]
fn calc_five_step() {
    let output = assert_ok(r#"
def add_right_eq(a: Nat, b: Nat, c: Nat, h: Eq a b): Eq (a + c) (b + c) =
    match c { case zero =>
        trans(add_zero_right(a), trans(h, symm(add_zero_right(b))))
    case succ(k) => let ih = add_right_eq(a, b, k, h);
        trans(add_succ_right(a, k), trans(cong_succ(ih), symm(add_succ_right(b, k)))) }
def add_left_eq(a: Nat, b: Nat, c: Nat, h: Eq a b): Eq (c + a) (c + b) =
    trans(add_comm(c, a), trans(add_right_eq(a, b, c, h), symm(add_comm(c, b))))
def double_distrib_calc(x: Nat, y: Nat): Eq (double (x + y)) (double(x) + double(y)) =
    calc {
        double (x + y) = ((x + y) + x) + y by symm(add_assoc(x + y, x, y))
        ((x + y) + x) + y = (x + (y + x)) + y by add_right_eq((x + y) + x, x + (y + x), y, add_assoc(x, y, x))
        (x + (y + x)) + y = (x + (x + y)) + y by add_right_eq(x + (y + x), x + (x + y), y, add_left_eq(y + x, x + y, x, add_comm(y, x)))
        (x + (x + y)) + y = ((x + x) + y) + y by add_right_eq(x + (x + y), (x + x) + y, y, symm(add_assoc(x, x, y)))
        ((x + x) + y) + y = (x + x) + (y + y) by add_assoc(x + x, y, y)
    }
def r = double_distrib_calc 3 4
println (match r { case refl(a) => a })
"#);
    assert!(output.trim() == "14", "expected 14, got: {}", output);
}

// ── positive: single-line chain ──

#[test]
fn calc_single_line() {
    let output = assert_ok(r#"
def one_line(n: Nat): Eq (0 + n) (n + 0) = calc 0 + n = n by add_zero_left n = n + 0 by symm (add_zero_right n)
def r = one_line 7
println (match r { case refl(a) => a })
"#);
    assert!(output.trim() == "7", "expected 7, got: {}", output);
}

// ── positive: calc inside a let value ──

#[test]
fn calc_in_let() {
    let output = assert_ok(r#"
def via_let(n: Nat): Nat =
    let h : Eq (0 + n) (n + 0) = calc {
        0 + n = n by add_zero_left n
        n = n + 0 by symm (add_zero_right n)
    };
    n + 1
def r = via_let 3
println r
"#);
    assert!(output.trim() == "4", "expected 4, got: {}", output);
}

// ── positive: three-step chain with a `symm` proof in the middle step ──
// (mirrors the symm-in-the-middle shapes in adder_proof.typort)

#[test]
fn calc_three_step_symm_mid() {
    let output = assert_ok(r#"
def three_symm_mid(n: Nat): Eq ((n + 0) + 0) (0 + n) =
    calc {
        (n + 0) + 0 = n + 0 by add_zero_right(n + 0)
        n + 0 = n by symm(add_zero_right(n))
        n = 0 + n by symm(add_zero_left(n))
    }
def r = three_symm_mid 5
println (match r { case refl(a) => a })
"#);
    assert!(output.trim() == "5", "expected 5, got: {}", output);
}

// ── positive: chain result bound via `let ret: Eq(...) = calc {...}; ret` ──
// (the let-ret pattern used by every vec_adder_correct case body)

#[test]
fn calc_let_ret() {
    let output = assert_ok(r#"
def via_let_ret(n: Nat): Eq (0 + n) (n + 0) =
    let ret: Eq (0 + n) (n + 0) = calc {
        0 + n = n by add_zero_left n
        n = n + 0 by symm (add_zero_right n)
    };
    ret
def r = via_let_ret 5
println (match r { case refl(a) => a })
"#);
    assert!(output.trim() == "5", "expected 5, got: {}", output);
}

// ── positive: two-step chain whose last written term is closed only by a
// definitional reduction (n + 0 → n), like the double_mul / to_nat_snoc
// branches in adder_proof.typort ──

#[test]
fn calc_two_step_def_reduce() {
    let output = assert_ok(r#"
def two_step_def(n: Nat): Eq ((n + 0) + 0) (n + 0) =
    calc {
        (n + 0) + 0 = n + 0 by add_zero_right(n + 0)
        n + 0 = n by add_zero_right(n)
    }
def r = two_step_def 5
println (match r { case refl(a) => a })
"#);
    assert!(output.trim() == "5", "expected 5, got: {}", output);
}

// ── negative: chain broken (proofs don't connect — definitionally) ──
// NOTE: only the PROOFS' types are checked (each step's written terms are
// not separately verified — the let-chain check was dropped because hole
// annotations on GADT-indexed types hit a unifier limitation; see
// docs/calc-reasoning-design.md §8). A broken chain = adjacent proofs
// whose endpoints disagree definitionally.

#[test]
fn calc_err_broken_chain() {
    assert_err_contains(r#"
def neg_b: Eq (7 + 0) (0 + 7) =
    calc {
        7 + 0 = 7 by add_zero_right 7
        8 = 8 by add_zero_right 8
    }
"#, "can't unify");
}

// ── negative: Lean `:=` syntax is still not parseable (documented
// limitation) — `:=` lexes as an infix Op and is swallowed by the raw
// fragment, so the macro never matches and `calc` degrades to an identifier.

#[test]
fn calc_err_lean_syntax() {
    assert_err_contains(r#"
def neg_c: Eq (7 + 0) (0 + 7) = calc
    7 + 0 = 7 := add_zero_right 7
    7 = 0 + 7 := symm (add_zero_left 7)
"#, "calc");
}

// ── negative: a step missing its `by` proof does not match the macro
// (the matcher expects `by` after the right-hand term, so the rule fails
// and `calc` degrades to an ordinary identifier) ──

#[test]
fn calc_err_missing_by() {
    assert_err_contains(r#"
def neg_d: Eq (7 + 0) (0 + 7) =
    calc {
        7 + 0 = 7
        7 = 0 + 7
    }
"#, "calc");
}

// ── negative: `by` with no proof after it does not match the macro ──

#[test]
fn calc_err_by_no_proof() {
    assert_err_contains(r#"
def neg_e: Eq (7 + 0) (0 + 7) =
    calc {
        7 + 0 = 7 by
        7 = 0 + 7
    }
"#, "calc");
}

// ── negative: `by` before the `=` is not the calc step shape ──

#[test]
fn calc_err_by_wrong_position() {
    assert_err_contains(r#"
def neg_f: Eq (7 + 0) (0 + 7) =
    calc {
        7 + 0 by add_zero_right 7 = 7
        7 = 0 + 7
    }
"#, "calc");
}

// ── negative: the error for a broken step points AT the failing proof's
// source span (regression: expansion re-lexing used to leak expansion-relative
// offsets, so errors floated to unrelated source positions) ──

#[test]
fn calc_err_broken_chain_span() {
    let input = r#"
def broken(n: Nat): Eq (0 + n) (n + 0) =
    calc {
        0 + n = n by add_zero_left n
        n = n + 0 by symm (add_zero_right n)
        n + 0 = n by add_zero_left n
    }
"#;
    match run_with_prelude(input) {
        Ok(_) => panic!("expected error, got OK"),
        Err(e) => {
            let proof_off = input.rfind("add_zero_left n").expect("proof in input");
            let proof_end = proof_off + "add_zero_left n".len();
            assert!(
                e.0.start_offset as usize <= proof_end && e.0.end_offset as usize >= proof_off,
                "error span {}..{} should overlap the failing proof at {}..{}",
                e.0.start_offset, e.0.end_offset, proof_off, proof_end
            );
        }
    }
}

// ── positive: the theorem_proving example, including its appended `_calc`
// variants ──
// Each `_calc` variant re-proves the proposition of its original with a
// `calc { lhs = rhs by proof ... }` chain and prints exactly the same
// value as the original println (asserted by the exact output below).

#[test]
fn calc_example_theorem_proving() {
    let input = include_str!("../../examples/theorem_proving.typort");
    let output = assert_ok(input);
    let expected = "\
Eq[Nat]::refl(5)
Eq[Nat]::refl(3)
Eq[Nat]::refl(3)
Eq[Nat]::refl(4)
Eq[Nat]::refl(8)
Eq[Nat]::refl(7)
Eq[Nat]::refl(8)
Eq[Nat]::refl(12)
Eq[Nat]::refl(6)
Eq[Nat]::refl(6)
Eq[Boolean]::refl(Boolean::true)
Eq[Boolean]::refl(Boolean::false)
Eq[Nat]::refl(5)
Eq[Nat]::refl(5)
Eq[Nat]::refl(4)
Eq[Nat]::refl(7)
Eq[Nat]::refl(12)
Eq[Nat]::refl(6)
Eq[Nat]::refl(5)
Eq[Nat]::refl(5)
";
    assert!(
        output == expected,
        "expected the original output plus matching _calc lines, got ({} lines):\n{}",
        output.lines().count(),
        output
    );
}
