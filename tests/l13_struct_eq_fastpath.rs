//! L13 structural fast-path pins (2026-11-24).
//!
//! L13 never had L07/L12's `struct_eq` module, so `unify`'s `(Match, Match)` arm
//! could only re-evaluate branch bodies, burning the 64-comparison budget and
//! reporting `can't unify`. This round ports it back against L13's value
//! representation and tries it before the slow path. These pins lock it in.

use elaboration_zoo_lsp::L13_namespace::run_with_prelude as run;

/// 同一递归函数的卡住 match 在方程两侧各展开一份：没有结构快路径时，慢路径
/// 会把分支体再展开一层卡住 match、层级递增永不收敛，最终烧穿 64 次预算。
#[test]
fn stuck_match_self_comparison_resolves() {
    let src = concat!(
        "def twice(n: Nat): Nat =\n",
        "    match n {\n",
        "        case zero => zero\n",
        "        case succ(k) => succ (succ (twice k))\n",
        "    }\n",
        "def needsEq[T](p: Eq (twice zero) (twice zero)): Nat = zero\n",
        "println (needsEq (refl (twice zero)))\n");
    match run(src) {
        Ok(out) => assert!(!out.is_empty(), "expected output, got empty"),
        Err(e) => panic!("the structural fast path should accept this equation, got: {}", e.0.data),
    }
}

#[test]
fn structural_equality_accepts_equal_and_rejects_unequal() {
    let ok = concat!(
        "def a : Nat = succ zero\n",
        "def b : Nat = succ zero\n",
        "def needsEq(p: Eq a b): Nat = zero\n",
        "println (needsEq (refl a))\n");
    run(ok).expect("equal values must unify");

    let bad = concat!(
        "def a : Nat = succ zero\n",
        "def b : Nat = zero\n",
        "def needsEq(p: Eq a b): Nat = zero\n",
        "println (needsEq (refl a))\n");
    assert!(run(bad).is_err(), "unequal values must NOT unify through the fast path");
}
