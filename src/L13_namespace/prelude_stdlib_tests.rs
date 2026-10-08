// ============================================================
// prelude stdlib tests
//
// prelude 以 include_str! 烧进二进制，编译期不会重跑 elaborate，这里把
// 2026-10 标准库补充轮（core eq/nat/bool 实例、data list/option/result/
// either/vec/order/nonempty、show 实例）的行为钉成断言：任一 prelude
// 回归（改名/语义反转/加载序破坏）都会在这里以测试失败暴露。
// 每个用例用 run_with_prelude 展开一段小程序，逐行断言 println 输出。
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

// ── list：fold / sort / show / split ──

#[test]
fn list_folds_sort_show() {
    assert_output(
        r#"
def xs: List[Nat] = lcons(1, lcons(2, lcons(3, lnil)))
println (xs.foldr (x => acc => x + acc) 0)
println (xs.foldl 0 (acc => x => acc + x))
println ((lcons(3, lcons(1, lcons(2, lnil)))).sort nat_compare).show
println (list_replicate 3 7).show
println (xs.take_while (x => x < 3)).show
println (xs.split_at 2).fst.show
println (xs.split_at 2).snd.show
"#,
        &["6", "6", "[1, 2, 3]", "[7, 7, 7]", "[1, 2]", "[1, 2]", "[3]"],
    );
}

// ── vec：append 方向（回归钉：曾因索引方向实现成 that ++ this）──

#[test]
fn vec_append_snoc_reverse_semantics() {
    assert_output(
        r#"
def v1: Vec[Nat] 2 = cons 1 (cons 2 nil)
def v2: Vec[Nat] 3 = cons 3 (cons 4 (cons 5 nil))
def v12: Vec[Nat] 5 = v1.append v2
println v12.len
println v12.to_list.show
println (v1.snoc 9).to_list.show
println v2.reverse.to_list.show
def w2: Vec[Nat] 2 = cons 10 (cons 20 nil)
println (v1.map2 w2 (x => y => x + y)).to_list.show
"#,
        &["5", "[1, 2, 3, 4, 5]", "[1, 2, 9]", "[5, 4, 3]", "[11, 22]"],
    );
}

// ── show 实例覆盖 ──

#[test]
fn show_instances() {
    assert_output(
        r#"
def b: Boolean = true
def o1: Option[Nat] = Some 5
def o2: Option[Nat] = None
def r1: Result[Nat, Boolean] = err false
def e1: Either[Nat, Boolean] = left 1
println b.show
println ((1 < 2) && (3 === 3) && !false).show
println (true =/= false).show
println (nat_compare 1 2).show
println (nat_compare 3 1).reverse.show
println o1.show
println o2.show
println (o1.and (Some 6)).show
println (o2.and (Some 6)).show
println ((Some (Some 3)).flatten).show
println r1.show
println e1.show
println ((e1.bimap (x => x * 10) (x => x)).show)
"#,
        &[
            "true",
            "true",
            "true",
            "lt",
            "lt",
            "some 5",
            "none",
            "some 6",
            "none",
            "some 3",
            "err false",
            "left 1",
            "left 10",
        ],
    );
}

// ── nat：nat_pow 与乘法引理（cong2 依赖链）──

#[test]
fn nat_pow_and_mul_lemmas() {
    assert_output(
        r#"
println (nat_pow 2 10)
println (nat_pow 3 0)
def c: Nat =
    match mul_comm 3 4 {
        case refl(a) => a
    }
println c
def d: Nat =
    match mul_assoc 2 3 4 {
        case refl(a) => a
    }
println d
def e: Nat =
    match mul_distrib_left 2 3 4 {
        case refl(a) => a
    }
println e
"#,
        &["1024", "1", "12", "24", "14"],
    );
}

// ══════════════════════════════════════════════════════════════
// 2026-10b 轮 · verifier 集成钉（跨文件组合面）
//
// owner 各自负责单文件测试；这里钉的是**组合面**：vec→list→show、
// option→either→result 转换格、nonempty→list→show，以及方向家族的
// 边界值（空表/单元素/重复元素/越界索引）。全部期望值都由 verifier 的
// 独立夹具（target/prelude_scratch/verify/**）实测取得，未复用 owner 测试。
// ══════════════════════════════════════════════════════════════

// ── vec 方向家族 + 边界（append/snoc/reverse/at/tail/fold 家族）──

#[test]
fn vec_direction_and_boundary_pins() {
    assert_output(
        r#"
def v0: Vec[Nat] 0 = nil
def v1: Vec[Nat] 1 = cons 7 nil
def v2: Vec[Nat] 2 = cons 1 (cons 2 nil)
def v3: Vec[Nat] 3 = cons 1 (cons 2 (cons 3 nil))
println (v1.append v2).to_list.show
println (v2.append v1).to_list.show
println (v0.append v3).to_list.show
println (v3.append v0).to_list.show
println (v3.snoc 9).to_list.show
println (v0.snoc 5).to_list.show
println v3.reverse.to_list.show
println v3.head
println v3.tail.to_list.show
println v3.at (2, 99)
println v3.at (5, 99)
println v0.at (0, 99)
println ((v3.map (x => x + 1)).to_list).show
println ((v3.zip v3).to_list.map (p => p.snd)).show
println (v3.foldl 0 (a => x => a * 10 + x))
println (v3.fold 0 (a => x => a * 10 + x))
"#,
        &[
            "[7, 1, 2]",
            "[1, 2, 7]",
            "[1, 2, 3]",
            "[1, 2, 3]",
            "[1, 2, 3, 9]",
            "[5]",
            "[3, 2, 1]",
            "1",
            "[2, 3]",
            "3",
            "99",
            "99",
            "[2, 3, 4]",
            "[1, 2, 3]",
            "123",
            "321",
        ],
    );
}

// ── list 方向 + 边界 + 本轮新增组合子（snoc/nth/find_index/intersperse/nub/partition/keys/values）──

#[test]
fn list_direction_and_new_combinator_pins() {
    assert_output(
        r#"
def xs: List[Nat] = lcons(1, lcons(2, lcons(3, lnil)))
def dup: List[Nat] = lcons(2, lcons(2, lcons(1, lnil)))
def pairs: List[Product[Nat, Nat]] = lcons(new Product(1, 10), lcons(new Product(2, 20), lnil))
println (xs.take 9).show
println (xs.drop 9).show
println (xs.split_at 0).snd.show
println (xs.split_at 9).fst.show
println (range 4).show
println (xs.snoc 4).show
println (xs.nth 2).show
println (xs.find_index (x => x === 3)).show
println (xs.intersperse 0).show
println ((lcons(3, lcons(1, lcons(2, lcons(1, lnil))))).nub nat_eq).show
println (dup.partition is_even).fst.show
println (dup.partition is_even).snd.show
println dup.sum
println (xs.zip_with (a => b => a + b) (lcons(9, lnil))).show
println pairs.keys.show
println pairs.values.show
println ((lcons(3, lcons(1, lcons(2, lnil)))).sort nat_compare).show
println ((lcons(1, lcons(2, lnil))).insert 3 nat_compare).show
println (list_replicate 3 7).show
println ((lcons(1, lcons(1, lnil))).nub nat_eq).show
"#,
        &[
            "[1, 2, 3]",
            "[]",
            "[1, 2, 3]",
            "[1, 2, 3]",
            "[0, 1, 2, 3]",
            "[1, 2, 3, 4]",
            "some 3",
            "some 2",
            "[1, 0, 2, 0, 3]",
            "[3, 2, 1]",
            "[2, 2]",
            "[1]",
            "5",
            "[10]",
            "[1, 2]",
            "[10, 20]",
            "[1, 2, 3]",
            "[1, 2, 3]",
            "[7, 7, 7]",
            "[1]",
        ],
    );
}

// ── 跨文件集成：vec→list→show、option→either→result 转换格、nonempty、Show 格式 ──

#[test]
fn cross_file_lattice_and_show_pins() {
    assert_output(
        r#"
def v1: Vec[Nat] 1 = cons 7 nil
def v2: Vec[Nat] 2 = cons 1 (cons 2 nil)
def v3: Vec[Nat] 3 = cons 1 (cons 2 (cons 3 nil))
println (v1.append v2).to_list.show
println ((v3.map2 v3 (x => y => new Product(x, y))).to_list.map (p => p.fst)).show
def o5: Option[Nat] = Some 5
def on: Option[Nat] = None
println o5.to_list.show
println on.to_list.show
def ob: Option[Boolean] = Some true
def obn: Option[Boolean] = None
println (option_to_either ob 7).show
println (option_to_either obn 7).show
println (option_to_result o5 false).show
println (option_to_result on false).show
def r7: Result[Nat, Boolean] = ok 7
def re: Result[Nat, Boolean] = err false
println (result_to_option r7).show
println (result_to_option re).show
def el9: Either[Nat, Boolean] = left 9
def er: Either[Nat, Boolean] = right true
println el9.left_to_option.show
println er.left_to_option.show
println (either_to_option er).show
println (el9.bimap (x => x * 10) (b => !b)).show
println (er.bimap (x => x * 10) (b => !b)).show
def q_e2r: Nat = (either_to_result el9).elim (b => bool_to_nat b) (n => n + 1)
println q_e2r
def ne: NonEmpty[Nat] = new NonEmpty(1, lcons(2, lcons(3, lnil)))
println ne.to_list.show
println ne.reverse.to_list.show
println (ne.foldl 0 (a => x => a * 10 + x))
println (new Product(true, false)).show
println (new Product(true, false)).swap.show
println (new Tuple2(3, 4)).show
def ol: Option[List[Nat]] = Some v3.to_list
println ol.show
println (lcons(v3.to_list, lcons(lcons(1, lnil), lnil))).show
def b1: Boolean = true
println b1.show
def s1: String = "hi"
println s1.show
println ((nat_compare 1 1).then_with (u => nat_compare 5 3)).show
"#,
        &[
            "[7, 1, 2]",
            "[1, 2, 3]",
            "[5]",
            "[]",
            "right true",
            "left 7",
            "ok 5",
            "err false",
            "some 7",
            "none",
            "some 9",
            "none",
            "some true",
            "left 90",
            "right false",
            "10",
            "[1, 2, 3]",
            "[3, 2, 1]",
            "123",
            "(true, false)",
            "(false, true)",
            "(3, 4)",
            "some [1, 2, 3]",
            "[[1, 2, 3], [1]]",
            "true",
            "hi",
            "gt",
        ],
    );
}

// ── 证明层引理 + 本轮新增算术引理：把证明的等式两端钉成具体值 ──

#[test]
fn proof_lemma_normalization_pins() {
    assert_output(
        r#"
def q_add_one_right: Nat = match add_one_right 5 { case refl(a) => a }
def q_add_one_left: Nat = match add_one_left 5 { case refl(a) => a }
def q_mul_one_right: Nat = match mul_one_right 5 { case refl(a) => a }
def q_mul_one_left: Nat = match mul_one_left 5 { case refl(a) => a }
def q_pow_zero: Nat = match pow_zero 7 { case refl(a) => a }
def q_pow_one: Nat = match pow_one 7 { case refl(a) => a }
def q_pow_succ: Nat = match pow_succ 2 3 { case refl(a) => a }
def q_pow_add: Nat = match pow_add 2 3 4 { case refl(a) => a }
def q_factorial: Nat = nat_factorial 5
def q_factorial_succ: Nat = match factorial_succ 3 { case refl(a) => a }
def q_not_not_neg: Boolean = match not_not_neg false { case refl(a) => a }
def q_nat_eq_refl: Boolean = match nat_eq_refl 3 { case refl(a) => a }
def q_nat_lt_irrefl: Boolean = match nat_lt_irrefl 4 { case refl(a) => a }
def q_cmp_bool_lt: Boolean = false < true
def q_cmp_bool_gte: Boolean = true >= true
def e33: Eq[Nat] 3 3 = rfl
def q_trans3: Nat = match trans3 e33 e33 e33 { case refl(a) => a }
def q_f3(a: Nat, b: Nat, c: Nat): Nat = a + b + c
def q_cong3: Nat = match cong3 q_f3 e33 e33 e33 { case refl(a) => a }
println q_add_one_right
println q_add_one_left
println q_mul_one_right
println q_mul_one_left
println q_pow_zero
println q_pow_one
println q_pow_succ
println q_pow_add
println q_factorial
println q_factorial_succ
println q_not_not_neg.show
println q_nat_eq_refl.show
println q_nat_lt_irrefl.show
println q_cmp_bool_lt.show
println q_cmp_bool_gte.show
println q_trans3
println q_cong3
"#,
        &[
            "6",
            "6",
            "5",
            "5",
            "1",
            "7",
            "16",
            "128",
            "120",
            "24",
            "false",
            "true",
            "false",
            "true",
            "true",
            "3",
            "9",
        ],
    );
}

#[test]
fn option_result_either_lattice() {
    assert_output(
        r#"
def o: Option[Nat] = Some 5
def oz: Option[Nat] = None
println o.to_list.show
// option_to_either 把 Option 值放右边：Some 5 → right 5，None → left if_none
println (option_to_either o true).elim (b => 0) (x => x + 1)
println (option_to_either oz true).elim (b => 0) (x => x + 1)
def e3: Either[Nat, Boolean] = left 1
println e3.left_to_option.show
def r: Result[Nat, Boolean] = ok 3
println (r.elim (x => x * 2) (b => 0))
println (r.map_or 0 (x => x + 1))
"#,
        &["[5]", "6", "0", "some 1", "6", "4"],
    );
}
