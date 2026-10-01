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

// ── option/result/either 转换格 ──

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
