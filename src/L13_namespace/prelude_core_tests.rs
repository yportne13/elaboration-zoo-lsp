// ============================================================
// prelude core tests (owner: prelude-core, task-1)
//
// 本模块钉住 src/prelude/core/** 的行为：新增函数/实例/引理的具体值探针。
// 写法参照同目录 prelude_stdlib_tests.rs：run_with_prelude + 逐行断言 println。
// 每个用例都必须能独立复现审计报告里声称的语义（含递归方向）。
// ============================================================

use super::*;

fn assert_output(input: &str, expected: &[&str]) {
    let output = match run_with_prelude(input) {
        Ok(output) => output,
        Err(e) => panic!(
            "expected OK, got error: '{}' @ {}:{}",
            e.0.data, e.0.path_id, e.0.start_offset
        ),
    };
    let lines: Vec<&str> = output
        .lines()
        .map(str::trim_end)
        .filter(|l| !l.is_empty())
        .collect();
    assert_eq!(lines, expected, "program output mismatch; raw: {:?}", output);
}

// ── eq：trans3 / cong3 / subst2 ──

#[test]
fn eq_trans3_cong3_subst2() {
    assert_output(
        r#"
def add3(x: Nat, y: Nat, z: Nat): Nat = x + y + z
def p1: Eq (add3 1 2 3) (add3 1 2 3) = cong3[Nat, Nat, Nat, Nat, 1, 1, 2, 2, 3, 3] add3 rfl rfl rfl
def q1: Nat = match p1 { case refl(a) => a }
println q1
def p2: Eq (1 + 2) (2 + 1) = trans3 (add_comm 1 2) (add_comm 2 1) (symm (add_comm 2 1))
def q2: Nat = match p2 { case refl(a) => a }
println q2
def eqfam(x: Nat, y: Nat): Type 0 = Eq x y
def p3: eqfam (1 + 2) (3 + 0) = subst2[Nat, Nat, eqfam, 1 + 2, 1 + 2, 3 + 0, 3 + 0] rfl rfl rfl
def q3: Nat = match p3 { case refl(a) => a }
println q3
"#,
        &["6", "3", "3"],
    );
}

// ── op：Product.bimap / compose3 ──

#[test]
fn op_bimap_compose3() {
    assert_output(
        r#"
def p0: Product[Nat, Nat] = new Product(3, 4)
def p1: Product[Nat, Boolean] = p0.bimap (x => x + 1) (y => y === 3)
println p1.fst
println (bool_to_nat p1.snd)
def p2: Product[Nat, Boolean] = p0.bimap (x => x + 1) (y => y === 4)
println (bool_to_nat p2.snd)
println (compose3 (x => x + 1) (x => x * 2) (x => x + 3) 1)
"#,
        &["4", "0", "1", "9"],
    );
}

// ── bool：证明层引理 + Compare[Boolean, Boolean] 实例 ──

#[test]
fn bool_proof_lemmas_and_ordering() {
    assert_output(
        r#"
def b1: Boolean = match not_not_neg true { case refl(a) => a }
def b2: Boolean = match not_not_neg false { case refl(a) => a }
def b3: Boolean = match eq_self_true true { case refl(a) => a }
def b4: Boolean = match nat_eq_refl 4 { case refl(a) => a }
def b5: Boolean = match nat_lte_refl 4 { case refl(a) => a }
def b6: Boolean = match nat_lt_irrefl 4 { case refl(a) => a }
def b7: Boolean = match nat_lte_succ 4 { case refl(a) => a }
def b8: Boolean = match nat_lt_succ 4 { case refl(a) => a }
println (bool_to_nat b1)
println (bool_to_nat b2)
println (bool_to_nat b3)
println (bool_to_nat b4)
println (bool_to_nat b5)
println (bool_to_nat b6)
println (bool_to_nat b7)
println (bool_to_nat b8)
println (bool_to_nat (nat_eq 3 3))
println (bool_to_nat (nat_lt 3 4))
println (bool_to_nat (nat_lte 4 3))
println (bool_to_nat (false < true))
println (bool_to_nat (true < false))
println (bool_to_nat (false <= false))
println (bool_to_nat (true >= true))
println (bool_to_nat (true > false))
"#,
        &[
            "1", "0", "1", "1", "1", "0", "1", "1", // proof lemmas
            "1", "1", "0", // nat predicates
            "1", "0", "1", "1", "1", // Boolean ordering
        ],
    );
}

// ── nat：1/succ 单位元、nat_pow 引理、max/min 幂等、factorial ──

#[test]
fn nat_one_pow_maxmin_factorial() {
    assert_output(
        r#"
def v_add_one_left: Nat = match add_one_left 4 { case refl(a) => a }
def v_mul_one_left: Nat = match mul_one_left 6 { case refl(a) => a }
def v_pow_one: Nat = match pow_one 9 { case refl(a) => a }
def v_pow_add: Nat = match pow_add 2 1 1 { case refl(a) => a }
def v_max: Nat = match max_self 6 { case refl(a) => a }
def v_min: Nat = match min_self 6 { case refl(a) => a }
def v_fact: Nat = match factorial_succ 4 { case refl(a) => a }
def v_fact0: Nat = match factorial_zero { case refl(a) => a }
def v_bymul: Nat = mul_by 3 5
println v_bymul
println (1 + 5)
println (7 + 1)
println (7 * 1)
println (1 * 7)
println (nat_pow 2 10)
println (nat_pow 2 (3 + 4))
println (nat_max 4 4)
println (nat_min 4 4)
println (nat_factorial 5)
println v_add_one_left
println v_mul_one_left
println v_pow_one
println v_pow_add
println v_max
println v_min
println v_fact
println v_fact0
"#,
        &[
            "15", "6", "8", "7", "7", "1024", "128", "4", "4", "120", "5", "6", "9", "4", "6", "6", "120", "1",
        ],
    );
}
