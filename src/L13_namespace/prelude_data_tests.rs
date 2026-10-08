// ============================================================
// prelude data tests (owner: prelude-data, task-2)
//
// 本模块钉住 src/prelude/data/** 与 src/prelude/show.typort 的行为：
// 容器函数、转换格、Show 输出格式的具体值断言。
// 写法参照同目录 prelude_stdlib_tests.rs：run_with_prelude + 逐行断言 println。
// vec/list 的递归与索引方向必须有方向性钉（Vec.append 事故家族）。
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

// ── list：snoc 方向钉 + partition / nth / find_index / intersperse / nub / keys / values ──

#[test]
fn list_snoc_direction_and_new_combinators() {
    assert_output(
        r#"
def cs1(l: List[Nat]): Nat =
    let f: Nat -> Nat -> Nat = a => x => (a * 10) + x;
    l.foldl 0 f
def xs1: List[Nat] = lcons(1, lcons(2, lcons(3, lnil)))
def xs4: List[Nat] = lcons(1, lcons(2, lcons(3, lcons(4, lnil))))
def dup: List[Nat] = lcons(1, lcons(2, lcons(1, lcons(3, lcons(2, lnil)))))
def dup2: List[Nat] = lcons(3, lcons(1, lcons(2, lcons(1, lnil))))
def pe: Product[List[Nat], List[Nat]] = xs4.partition (x => is_even x)
def pe_f: List[Nat] = pe.fst
def pe_s: List[Nat] = pe.snd
def pr: List[Product[Nat, Boolean]] = lcons(new Product(1, true), lcons(new Product(2, false), lnil))
def uz: Product[List[Nat], List[Boolean]] = pr.unzip
def fi: Option[Nat] = xs4.find_index (x => nat_eq x 3)
def fn: Option[Nat] = xs4.find_index (x => nat_eq x 9)
// 方向钉：snoc 必须追加在末尾 -> [1, 2, 3, 9]（旧事故会得到 [9, 1, 2, 3]）
println (xs1.snoc 9).show
println (cs1 (xs1.snoc 9))
println (xs1.snoc 9).length
println (cs1 pe_f)
println (cs1 pe_s)
println (pe_f.length)
println (cs1 (xs1.intersperse 9))
// nub 语义钉 1：保留末次出现 -> [1, 3, 2] = 132（Haskell 式保留首个会得 [1, 2, 3] = 123）
println (cs1 (dup.nub nat_eq))
// nub 语义钉 2：[3,1,2,1] -> [3, 2, 1] = 321（保留首个会得 [3, 1, 2] = 312）
println (cs1 (dup2.nub nat_eq))
println ((xs4.nth 0).unwrap_or 99)
println ((xs4.nth 3).unwrap_or 99)
println ((xs4.nth 4).unwrap_or 99)
println (fi.unwrap_or 99)
println (fn.unwrap_or 99)
// keys/values 与 unzip 字段顺序一致：fst = keys = 12，snd = values，长度 2
println (cs1 pr.keys)
println (cs1 uz.fst)
println pr.values.length
println uz.snd.length
"#,
        &[
            "[1, 2, 3, 9]",
            "1239",
            "4",
            "24",
            "13",
            "2",
            "19293",
            "132",
            "321",
            "1",
            "4",
            "99",
            "2",
            "99",
            "12",
            "12",
            "2",
            "2",
        ],
    );
}

// ── vec：vec_replicate 索引方向 + vec_last_option + append/snoc 既有方向钉 ──

#[test]
fn vec_replicate_and_last_option() {
    assert_output(
        r#"
def vr: Vec[Nat] 3 = vec_replicate 3 7
def v0: Vec[Nat] 0 = nil
def v2: Vec[Nat] 2 = cons 1 (cons 2 nil)
def v3: Vec[Nat] 3 = vec_replicate 3 7
println vr.len
println vr.to_list.show
println (vec_last_option vr).show
println (vec_last_option v0).show
println (vec_last_option (vec_replicate 1 5)).show
// append 方向钉：[1, 2] ++ [7, 7, 7]（不是反过来）
println (v2.append v3).to_list.show
// snoc 方向钉：[1, 2].snoc 3 -> [1, 2, 3]
println (v2.snoc 3).to_list.show
"#,
        &[
            "3",
            "[7, 7, 7]",
            "some 7",
            "none",
            "some 5",
            "[1, 2, 7, 7, 7]",
            "[1, 2, 3]",
        ],
    );
}

// ── vec：foldl 必须是真左折、fold 是右折（verifier 复核出的方向缺陷回归钉）──

#[test]
fn vec_fold_direction() {
    assert_output(
        r#"
def f10: Nat -> Nat -> Nat = a => x => (a * 10) + x
def v3: Vec[Nat] 3 = cons 1 (cons 2 (cons 3 nil))
def v0: Vec[Nat] 0 = nil
// 左折从头部累积：((0*10+1)*10+2)*10+3 = 123（修复前误为 321）
println (v3.foldl 0 f10)
// 右折从尾部累积：((0*10+3)*10+2)*10+1 = 321
println (v3.fold 0 f10)
// reduce = fold 以 head 为初值，故同样从尾部累积：(1*10+3)*10+2 = 132
println (v3.reduce f10)
println (v0.foldl 5 f10)
println (v0.fold 5 f10)
"#,
        &["123", "321", "132", "5", "5"],
    );
}

// ── option / result / either：惰性默认值、ok_or、right_to_option ──

#[test]
fn option_result_either_new_combinators() {
    assert_output(
        r#"
def o1: Option[Nat] = Some 3
def o0: Option[Nat] = None
def r1: Result[Nat, Boolean] = err true
def r0: Result[Nat, Boolean] = ok 4
def e0: Either[Nat, Boolean] = left 5
def e1: Either[Nat, Boolean] = right true
println (o1.unwrap_or_else (u => 9))
println (o0.unwrap_or_else (u => 9))
println (o1.map_or_else (u => 8) (x => x + 1))
println (o0.map_or_else (u => 8) (x => x + 1))
println ((o1.ok_or false).elim (x => x) (b => 9))
println ((o0.ok_or false).elim (x => x) (b => 9))
println (r1.unwrap_or_else (b => 7))
println (r0.unwrap_or_else (b => 7))
println (r1.map_or_else (b => 7) (x => x * 2))
println (r0.map_or_else (b => 7) (x => x * 2))
println e1.right_to_option.show
println e0.right_to_option.is_none.show
println (either_right_to_option e0).show
"#,
        &[
            "3", "9", "4", "8", "3", "9", "7", "4", "7", "8", "some true", "true", "none",
        ],
    );
}

// ── order：ordering_min / ordering_max / Ordering.pick ──

#[test]
fn order_min_max_pick() {
    assert_output(
        r#"
println (ordering_min 3 2 nat_compare)
println (ordering_max 3 2 nat_compare)
println (ordering_min 2 2 nat_compare)
println (ordering_max 2 2 nat_compare)
println ((nat_compare 1 2).pick 10 20 30)
println ((nat_compare 2 2).pick 10 20 30)
println ((nat_compare 3 2).pick 10 20 30)
"#,
        &["2", "3", "2", "2", "10", "20", "30"],
    );
}

// ── decidable：get_or_else + dec_and（证明合取）──

#[test]
fn decidable_get_or_else_and_conjunction() {
    assert_output(
        r#"
def dn: Dec[Nat] = yes 5
def dn2: Dec[Nat] = yes 7
def dpp: Dec[Product[Nat, Nat]] = dec_and dn dn2
def pp: Product[Nat, Nat] = dpp.get_or_else (new Product(0, 0))
def dv: Dec[Void] = no (v => v)
println (dn.get_or_else 0)
println pp.fst
println pp.snd
println dv.is_no.show
println dv.to_option.is_none.show
println dn.is_yes.show
"#,
        &["5", "5", "7", "true", "true", "true"],
    );
}

// ── nonempty：foldr / find / nonempty_from_list ──

#[test]
fn nonempty_foldr_find_from_list() {
    assert_output(
        r#"
def ne: NonEmpty[Nat] = new NonEmpty(1, lcons(2, lcons(3, lnil)))
def el: List[Nat] = lnil
println (ne.foldr (x => acc => x + (acc * 10)) 0)
println (ne.foldl 0 (acc => x => (acc * 10) + x))
println (ne.find (x => nat_eq x 2)).show
println (ne.find (x => nat_eq x 9)).is_none.show
println (nonempty_from_list ne.to_list).is_some.show
println (nonempty_from_list el).is_none.show
"#,
        &["321", "123", "some 2", "true", "true", "true"],
    );
}

// ── show：本轮新增的 10 个具体实例头 ──

#[test]
fn show_new_instances() {
    assert_output(
        r#"
def p1: Product[String, String] = new Product("a", "b")
def t1: Tuple2[String, String] = new Tuple2("c", "d")
def en_s: Either[Nat, String] = right "hi"
def es_b: Either[String, Boolean] = left "bad"
def r_sb: Result[String, Boolean] = err false
def ll: List[List[Nat]] = lcons(lcons(1, lcons(2, lnil)), lcons(lnil, lnil))
def ol: Option[List[Nat]] = Some (lcons(3, lnil))
def on: Option[List[Nat]] = None
def lp: List[Product[Nat, Nat]] = lcons(new Product(1, 2), lcons(new Product(3, 4), lnil))
def ne: NonEmpty[Nat] = new NonEmpty(1, lcons(2, lnil))
def vn: Vec[Nat] 2 = cons 1 (cons 2 nil)
def pb: Product[Boolean, Nat] = new Product(true, 3)
def tn: Tuple2[Nat, Boolean] = new Tuple2(3, true)
println p1.show
println t1.show
println en_s.show
println es_b.show
println r_sb.show
println ll.show
println ol.show
println on.show
println lp.show
println ne.show
println vn.show
println pb.show
println tn.show
"#,
        &[
            "(a, b)",
            "(c, d)",
            "right hi",
            "left bad",
            "err false",
            "[[1, 2], []]",
            "some [3]",
            "none",
            "[(1, 2), (3, 4)]",
            "[1, 2]",
            "[1, 2]",
            "(true, 3)",
            "(3, true)",
        ],
    );
}
