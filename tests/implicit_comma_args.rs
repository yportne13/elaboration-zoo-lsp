//! 隐式实参逗号合写 `f[A, B]` 的跨章回归套件（2026-09-19）。
//!
//! 背景：`f[A, B]`（一个方括号内逗号分隔多个隐式实参）原本只有
//! L11/L12/L13 的 parser 支持；本轮把它回移植到 L06–L10（对齐 L11 的
//! `square_cut` + `many0_sep` 形态，`Raw::App` 展开与逐槽 `f[A][B]` 完全
//! 同构）。本套件对每个被移植章节钉三件事：
//!   1. 逐槽形态 `f[A][B]` 不回归（原本就支持的写法）；
//!   2. 逗号合写 `f[A, B]` 可解析且与逐槽形态逐字节等价；
//!   3. 参考版 ↔ 孪生版 parity（两实现共用 parser，回归即同坏）。
//! L02–L05 是 elab-zoo `{}` 方言（上游形态），不在本轮回移植范围。

#![allow(dead_code)]

#[path = "../src/list.rs"]
mod list;
#[path = "../src/bimap.rs"]
mod bimap;
#[path = "../src/parser_lib.rs"]
mod parser_lib;
#[path = "../src/parser_lib_resilient.rs"]
mod parser_lib_resilient;

#[path = "../src/L06_string/mod.rs"]
mod L06_string;
#[path = "../src/L07_sum_type/mod.rs"]
mod L07_sum_type;
#[path = "../src/L08_product_type/mod.rs"]
mod L08_product_type;
#[path = "../src/L09_mltt/mod.rs"]
mod L09_mltt;
#[path = "../src/L10_typeclass/mod.rs"]
mod L10_typeclass;
#[path = "../src/L11_macro/mod.rs"]
mod L11_macro;
#[path = "../src/L12_canonical/mod.rs"]
mod L12_canonical;

macro_rules! parity_case {
    ($test_name:ident, $m:ident, $src:expr) => {
        #[test]
        fn $test_name() {
            let src: &str = $src;
            let s1 = src.to_owned();
            let s2 = src.to_owned();
            // Error 可能携带非 Send 的重试闭包（L12 系）：子线程内先转 String
            let r1 = std::thread::Builder::new()
                .stack_size(64 * 1024 * 1024)
                .spawn(move || $m::run(&s1, 0).map_err(|e| format!("{e:?}")))
                .unwrap()
                .join()
                .unwrap();
            let r2 = std::thread::Builder::new()
                .stack_size(64 * 1024 * 1024)
                .spawn(move || $m::bump_spine_iter::run_fast(&s2, 0).map_err(|e| format!("{e:?}")))
                .unwrap()
                .join()
                .unwrap();
            match (r1, r2) {
                (Ok(a), Ok(b)) => assert_eq!(a, b, "parity mismatch\nsrc:\n{src}"),
                (Err(_), Err(_)) => {}
                (a, b) => panic!("verdict mismatch: ref={a:?} fast={b:?}\nsrc:\n{src}"),
            }
        }
    };
}

// --------------------------------------------------------------------------------
// L06_string：U 上的挑参函数（该章无 enum；逐槽 / 逗号 / 拖尾逗号 / 命名混排）
// --------------------------------------------------------------------------------

const L06_SRC: &str = r#"
def pick[A : U, B : U](x: A, y: B): A = x
def u1 : U = U
println (pick[U][U] u1 u1)
println (pick[U, U] u1 u1)
println (pick[U, U,] u1 u1)
println (pick[A = U, B = U] u1 u1)
"#;

parity_case!(l06_slot_and_comma_parity, L06_string, L06_SRC);

// --------------------------------------------------------------------------------
// L07_sum_type：逗号合写与逐槽形态的 elaboration 产物必须逐字节相等
// --------------------------------------------------------------------------------

const L07_HEAD: &str = r#"
enum Nat {
    zero
    succ(n: Nat)
}
def add(x: Nat, y: Nat): Nat =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }
def two = succ (succ zero)
def idnat(n: Nat): Nat = n
enum Id[A](x: A, y: A) {
    refl(a: A) -> Id a a
}
def cong_test[A : U, B : U](f: A -> B, a: A, b: A)(e: Id[A] a b): Id[B] (f a) (f b) =
    match e {
        case refl(x) => refl (f a)
    }
"#;

const L07_SLOT: &str = "println (cong_test[Nat][Nat] idnat two two (refl two))\n";
const L07_COMMA: &str = "println (cong_test[Nat, Nat] idnat two two (refl two))\n";

#[test]
fn l07_comma_equals_slot_output() {
    let out_slot = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| L07_sum_type::run(&format!("{L07_HEAD}{L07_SLOT}"), 0))
        .unwrap()
        .join()
        .unwrap()
        .expect("slot form must elaborate");
    let out_comma = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| L07_sum_type::run(&format!("{L07_HEAD}{L07_COMMA}"), 0))
        .unwrap()
        .join()
        .unwrap()
        .expect("comma form must elaborate");
    assert_eq!(out_slot, out_comma);
    assert!(
        out_slot.contains("Id::refl("),
        "unexpected display: {out_slot}"
    );
}

parity_case!(l07_comma_parity, L07_sum_type, &format!("{L07_HEAD}{L07_COMMA}"));

// --------------------------------------------------------------------------------
// L08_product_type：struct 与逗号合写共存
// --------------------------------------------------------------------------------

const L08_SRC: &str = r#"
enum Nat {
    zero
    succ(n: Nat)
}
def two = succ (succ zero)
struct Point[T] {
    x: T
    y: T
}
def pick[T : U, S : U](a: T, b: S): T = a
def px(p: Point[Nat]): Nat = p.x
def pt = new Point(two, zero)
println (px pt)
println (pick[Nat, Nat] two zero)
println (pick[Nat][Nat] two zero)
"#;

parity_case!(l08_slot_and_comma_parity, L08_product_type, L08_SRC);

// --------------------------------------------------------------------------------
// L09_mltt：Type N 时代的逗号合写
// --------------------------------------------------------------------------------

const L09_SRC: &str = r#"
enum Nat {
    zero
    succ(n: Nat)
}
def two = succ (succ zero)
def pick[A : Type 0, B : Type 0](x: A, y: B): A = x
println (pick[Nat, Nat] two (succ zero))
println (pick[Nat][Nat] two (succ zero))
"#;

parity_case!(l09_slot_and_comma_parity, L09_mltt, L09_SRC);

// --------------------------------------------------------------------------------
// L10_typeclass：trait/impl 与逗号合写共存
// --------------------------------------------------------------------------------

const L10_SRC: &str = r#"
enum Nat {
    zero
    succ(n: Nat)
}
def natadd(x: Nat, y: Nat): Nat =
    match x {
        case zero => y
        case succ(n) => succ (natadd n y)
    }
def two = succ (succ zero)
trait Semi[T] {
    def append(that: T): T
}
impl Semi[Nat] for Nat {
    def append(that: Nat): Nat = natadd this that
}
def twice[T][s: Semi[T]](x: T): T = x.append x
def pick[A : Type 0, B : Type 0](x: A, y: B): A = x
println (twice[Nat] two)
println (pick[Nat, Nat] two zero)
println (pick[Nat][Nat] two zero)
"#;

parity_case!(l10_slot_and_comma_parity, L10_typeclass, L10_SRC);

// --------------------------------------------------------------------------------
// L11_macro / L12_canonical：已有逗号支持的章不回归
// --------------------------------------------------------------------------------

const L11_SRC: &str = r#"
enum Nat {
    zero
    succ(n: Nat)
}
def two = succ (succ zero)
def pick[A : Type 0, B : Type 0](x: A, y: B): A = x
println (pick[Nat, Nat] two zero)
macro_rules make_bool {
    (yes) => {
        enum Yes { y }
    }
}
make_bool yes
def b = y
println b
"#;

parity_case!(l11_comma_no_regression, L11_macro, L11_SRC);

const L12_SRC: &str = r#"
enum Nat {
    zero
    succ(n: Nat)
}
def two = succ (succ zero)
def pick[A : Type 0, B : Type 0](x: A, y: B): A = x
println (pick[Nat, Nat] two zero)
"#;

parity_case!(l12_comma_no_regression, L12_canonical, L12_SRC);
