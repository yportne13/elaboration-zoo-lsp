//! L08_product_type 双 oracle 互检套件（参考版 `run` ↔ 性能版 `bump_spine_iter::
//! run_fast`）。`#[path]` 只编 list.rs / parser_lib.rs / L08_product_type/mod.rs
//! （不含 LSP / L02-L06 / L13），迭代快数倍（tests/l06_blackbox.rs 同款）。
//!
//! 判据：**Ok 输出逐字节一致 / Err 判定一致**。错误文案的 Debug-Span 偏移
//! 是文档化偏差（快版导出项的 span 全零），不比内容。
//!
//! 深递归（依赖匹配的精化合一链、深值 quote）远超测试线程默认 2MB 栈，
//! 两侧都在 256MB 栈线程里跑（L07 tests.rs 的 64MB 惯例再放宽——快版
//! quote 分支体重求值 + 参考版递归 quote 的深度都吃栈）。

#![feature(pattern)]

#[path = "../src/list.rs"]
mod list;

#[path = "../src/parser_lib.rs"]
mod parser_lib;

#[path = "../src/L08_product_type/mod.rs"]
mod L08_product_type;

use L08_product_type::bump_spine_iter as fast;
use L08_product_type::FILE_IO_LOCK;

/// 在大栈线程里跑参考版 `run`。
fn run_basic(src: &str) -> Result<String, L08_product_type::Error> {
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || L08_product_type::run(&input, 0))
        .unwrap()
        .join()
        .unwrap()
}

/// 在大栈线程里跑快版 `run_fast`。
fn run_fast(src: &str) -> Result<String, L08_product_type::Error> {
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || fast::run_fast(&input, 0))
        .unwrap()
        .join()
        .unwrap()
}

/// Err 文案归一化：剥掉 `@ 数字[,数字]` 形态的源码偏移（文档化偏差：
/// 参考版错误文案的 Debug-Span 携带源码偏移，快版全零），比对正文形态。
fn norm_err(e: &str) -> String {
    let b = e.as_bytes();
    let mut out = String::with_capacity(e.len());
    let mut i = 0usize;
    while i < b.len() {
        if b[i] == b'@' && i + 1 < b.len() && b[i + 1] == b' ' {
            let mut j = i + 2;
            let s0 = j;
            while j < b.len() && b[j].is_ascii_digit() {
                j += 1;
            }
            if j > s0 {
                if j < b.len() && b[j] == b',' {
                    let mut k = j + 1;
                    let s1 = k;
                    while k < b.len() && b[k].is_ascii_digit() {
                        k += 1;
                    }
                    if k > s1 {
                        j = k;
                    }
                }
                out.push_str("@_");
                i = j;
                continue;
            }
        }
        let ch = e[i..].chars().next().unwrap();
        out.push(ch);
        i += ch.len_utf8();
    }
    out
}

/// Oracle：参考版与性能版的 Ok 输出逐字节一致；Err 判定一致，且 span
/// 归一化后的错误正文形态一致。
fn assert_parity(src: &str) {
    let b = run_basic(src);
    let f = run_fast(src);
    match (&b, &f) {
        (Ok(b), Ok(f)) => assert_eq!(
            b, f,
            "Ok 输出双实现不一致，src:\n{src}\n--- basic ---\n{b}--- fast ---\n{f}"
        ),
        (Err(b), Err(f)) => assert_eq!(
            norm_err(&b.to_string()),
            norm_err(&f.to_string()),
            "Err 正文（span 归一化后）双实现不一致，src:\n{src}\n--- basic ---\n{b}\n--- fast ---\n{f}"
        ),
        _ => panic!(
            "判定不一致（basic={}，fast={}），src:\n{src}\nbasic-err={b:?}\nfast-err={f:?}",
            b.as_ref().map(|_| "Ok").unwrap_or("Err"),
            f.as_ref().map(|_| "Ok").unwrap_or("Err")
        ),
    }
}

// 基础与 builtin
// --------------------------------------------------------------------------------

#[test]
fn parity_demo_src() {
    // DEMO 全串：enum + 依赖 match + 字符串 builtin + 文件 IO + 可变全局
    // （两个实现先后跑，各自写删同一文件，幂等；文件 IO 经锁串行）
    let _guard = FILE_IO_LOCK.lock().unwrap();
    assert_parity(L08_product_type::DEMO_SRC);
}

#[test]
fn parity_u_enum_strings() {
    for src in [
        "println U\n",
        "println \"hello\"\n",
        "def s : String = \"abc\"\nprintln s\n",
        // builtin 组：拼接 / 判等 / 缩进 / 部分应用卡住 / 动态类型
        "def c : String = string_concat \"foo\" \"bar\"\nprintln c\n",
        "println (str_eq \"foo\" \"foo\")\nprintln (str_eq \"foo\" \"bar\")\n",
        "def f = s => string_concat s\nprintln f\n",
        "def st : U = string_to_global_type \"String\"\nprintln st\n",
        "def st : U = string_to_global_type \"Missing\"\nprintln st\n",
        "def ind = str_indent2 \"line1\nline2\"\nprintln ind\n",
        // 可变全局族
        "def store : U = create_global \"k\" \"v\"\ndef upd : U = change_mutable \"k\" (s => string_concat s \"!\")\ndef g1 : String = get_global \"k\"\nprintln g1\n",
        "def g3 : String = get_global_default \"nope\" \"fb\"\nprintln g3\n",
        "def v : String = get_global \"missing\"\nprintln v\n",
    ] {
        assert_parity(src);
    }
}

// tests.rs 的既有用例源码（enum / match / GADT / 等式推理 / 卡住 match 各形态）
// --------------------------------------------------------------------------------

#[test]
fn parity_tests_rs_basic() {
    // test_basic：ADT + 多态 + 高阶函数 + map/Option
    assert_parity(
        r#"
enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

def listid(x: List[Bool]): List[Bool] = x

def create0: List[Bool] = nil

def create1: List[Bool] = cons true nil

def create2: List[Bool] = cons true (cons false nil)

def two = succ (succ zero)

def not(x: Bool): Bool =
    match x {
        case true => false
        case false => true
    }

println (not true)

def add(x: Nat, y: Nat) =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def mul(x: Nat, y: Nat) =
    match x {
        case zero => zero
        case succ(n) => add y (mul n y)
    }

def four = add two two

println four

def is_zero(x: Nat): Bool =
    match x {
        case zero => true
        case succ(n) => false
    }

println (is_zero zero)

println (is_zero four)

enum Option[T] {
    Some(t: T)
    None
}

def map[R, X](x: Option[R], f: R -> X): Option[X] =
    match x {
        case None => None
        case Some(t) => Some (f t)
    }

def some_four = Some four

def is_false = map (some_four) (x => is_zero x)

println "Option(false) is"
println is_false

println (mul two four)
"#,
    );
}

#[test]
fn parity_tests_rs_index() {
    // test_index：索引族 Eq / Vec、构造子返回类型、投影
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Eq[A](x: A, y: A) {
    refl[a: A] -> Eq[A] a a
}

def two = succ (succ zero)

def three = succ (succ (succ zero))

def test: Eq two two = refl

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

def t = cons zero (cons two (cons three (cons two nil)))

println t.len

def head[T, L: Nat](x: Vec[T] (succ L)): T =
    match x {
        case cons(x, _) => x
    }

println (head (cons zero nil))

def length[T, l: Nat](x: (Vec[T] l)): Nat =
    match x {
        case nil => zero
        case cons(_, xs) => succ (xs.len)
    }
"#,
    );
}

#[test]
fn parity_tests_rs_dependent_match() {
    // test_dependent_match + test_dependent_match_nested_eval：索引精化
    // 传播到分支体与返回类型、嵌套 match 的 scrutinee 是计算出的值
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

def t[len: Nat](x: Vec[Nat] len, y: Vec[Nat] len): Vec[Nat] (succ len) =
    match x {
        case nil => cons zero nil
        case cons(x, xs) => match y {
            case cons(y, ys) => cons x (t xs ys)
        }
    }
"#,
    );
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

def t[len: Nat](x: Vec[Nat] len, y: Vec[Nat] len): Vec[Nat] (succ len) =
    match x {
        case nil => cons zero nil
        case cons(x, xs) => match y {
            case cons(y, ys) => match t xs ys {
                case cons(z, zs) => cons zero (cons zero zs)
            }
        }
    }
"#,
    );
}

#[test]
fn parity_tests_rs_eq_reasoning() {
    // test_eq_reasoning：cong / symm / trans / rfl
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Eq[A](x: A, y: A) {
    refl(a: A) -> Eq a a
}

def rfl[A][a: A]: Eq a a =
    refl a

def cong[A, B, f: A -> B, x: A, y: A](e: Eq x y): Eq (f x) (f y) =
    match e {
        case refl(a) => refl (f a)
    }

def symm[A, x, y: A](e: Eq[A] x y): Eq[A] y x =
    match e {
        case refl(a) => refl[A] a
    }

def trans[A, x, y, z: A](e1: Eq[A] x y, e2: Eq[A] y z): Eq[A] x z =
    match e1 {
        case refl(a) => e2
    }
"#,
    );
}

#[test]
fn parity_tests_rs_lambda_strings() {
    // test_lambda_calculus_and_strings：纯依赖 λ 演算 + 字符串内建 + enum
    assert_parity(
        r#"
def Eq[A : U](x: A, y: A): U = (P : A -> U) -> P x -> P y
def refl[A : U, x: A]: Eq[A] x x = _ => px => px

def the(A : U)(x: A): A = x

def m : U -> U -> U -> U = _
def test = a => b => c => the (Eq (m a b c) (m c b a)) refl

def pr1 = f => x => f x

def Nat : U =
    (N : U) -> (N -> N) -> N -> N
def mul : Nat -> Nat -> Nat =
    a => b => N => s => z => a _ (b _ s) z
def ten : Nat =
    N => s => z => s (s (s (s (s (s (s (s (s (s z)))))))))
def hundred = mul ten ten

println hundred

def mystr = "hello world"

def add_tail(x: String): String = string_concat x "!"

def mystr2 = add_tail mystr

println mystr2

enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

def two = succ (succ zero)

def add(x: Nat, y: Nat): Nat =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def four = add two two

println four
"#,
    );
}

#[test]
fn parity_tests_rs_generic_and_catch_all() {
    // test_generic_match + test_catch_all_mixed
    assert_parity(
        r#"
enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

def length(x: List[Bool]): Nat =
    match x {
        case nil => zero
        case cons(h, t) => succ (length t)
    }

println (length (cons true (cons false nil)))

def add(x: Nat, y: Nat) =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def sum(x: List[Nat]): Nat =
    match x {
        case nil => zero
        case cons(h, t) => add h (sum t)
    }

println (sum (cons (succ zero) (cons (succ (succ zero)) nil)))
"#,
    );
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Bool {
    true
    false
}

def is_zero(x: Nat): Bool =
    match x {
        case zero => true
        case other => false
    }

println (is_zero zero)
println (is_zero (succ zero))

def const_zero(x: Nat): Nat =
    match x {
        case n => zero
        case zero => zero
        case succ(k) => succ k
    }

println (const_zero (succ (succ zero)))
"#,
    );
}

#[test]
fn parity_tests_rs_gadt() {
    // test_gadt_accessible（Ok）+ test_projection_typing（Ok）
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

def only_nil(v: Vec[Nat] zero): Nat =
    match v {
        case nil => zero
    }
"#,
    );
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

def two = succ (succ zero)

def t = cons zero (cons two nil)

def n: Nat = t.len

def m: Nat = (cons two nil).len
"#,
    );
}

#[test]
fn parity_tests_rs_stuck_match() {
    // test_stuck_match_unify / _splice / _applied_with_outer_binder /
    // test_hole_in_branch：卡住 match 的合一、splice、外层 binder 实参
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Bool {
    true
    false
}

def V(n: Nat): U =
    match n {
        case zero => Bool
        case succ(m) => Bool
    }

def useV(n: Nat)(x: V n): V n = x

def intoV(n: Nat): V n =
    match n {
        case zero => true
        case succ(m) => false
    }

println (useV zero (intoV zero))
println (useV (succ zero) (intoV (succ zero)))
"#,
    );
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

def f(n: Nat): Nat -> Nat =
    match n {
        case zero => succ
        case succ(k) => succ
    }

println f
println (f zero)
println ((f zero) zero)
"#,
    );
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

def pick(n: Nat): Nat -> Nat =
    match n {
        case zero => k => k
        case succ(k) => k => succ k
    }

def test(m: Nat, j: Nat): Nat = (pick m) j

println test
"#,
    );
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Bool {
    true
    false
}

enum Eq[A](x: A, y: A) {
    refl[a: A] -> Eq[A] a a
}

def two = succ (succ zero)

def add(x: Nat, y: Nat) =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def mul(x: Nat, y: Nat) =
    match x {
        case zero => zero
        case succ(n) => add y (mul n y)
    }

def ck(x: Nat): Eq (add x x) (mul two x) =
    match x {
        case zero => refl[Nat][zero]
        case succ(xx) => _
    }

println "final"
"#,
    );
}

#[test]
fn parity_tests_rs_nested_patterns() {
    // test_nested_patterns + test_nested_pattern_outer_ref：嵌套模式 +
    // 深层绑定器的 de Bruijn 对齐
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

def add(x: Nat, y: Nat) =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def second_or_zero(x: List[Nat]): Nat =
    match x {
        case nil => zero
        case cons(h, nil) => zero
        case cons(h, cons(h2, t)) => h2
    }

println (second_or_zero (cons (succ zero) (cons (succ (succ zero)) nil)))
println (second_or_zero (cons (succ zero) nil))
println (second_or_zero nil)
"#,
    );
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

def add(x: Nat, y: Nat) =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def second_or(x: List[Nat], d: Nat): Nat =
    match x {
        case nil => d
        case cons(h, nil) => add h d
        case cons(h, cons(h2, t)) => add h2 d
    }

println (second_or nil (succ zero))
println (second_or (cons (succ (succ zero)) nil) (succ zero))
println (second_or (cons zero (cons (succ (succ (succ zero))) nil)) (succ zero))
"#,
    );
}

#[test]
fn parity_tests_rs_recursive_defs() {
    // test_recursive_defs：自递归 + 后定义引用先定义（decl 表自引用占位）
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Bool {
    true
    false
}

def even(x: Nat): Bool =
    match x {
        case zero => true
        case succ(n) => even n
    }

def odd(x: Nat): Bool =
    match x {
        case zero => false
        case succ(n) => even n
    }

println (even (succ (succ zero)))
println (odd (succ zero))
"#,
    );
}

#[test]
fn parity_tests_rs_eq_proofs() {
    // test_eq_add_zero_right / add_succ_right / add_comm / add_assoc /
    // mul_zero_right / mul_one_right / bits_adder：依赖递归函数的索引族
    // 等式推理（stuck match 与精化的组合推理全链路）
    let prefix = r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Eq[A](x: A, y: A) {
    refl(a: A) -> Eq a a
}

def rfl[A][a: A]: Eq a a =
    refl a

def cong[A, B, f: A -> B, x: A, y: A](e: Eq x y): Eq (f x) (f y) =
    match e {
        case refl(a) => refl (f a)
    }

def cong_succ[x: Nat, y: Nat](e: Eq x y): Eq (succ x) (succ y) =
    cong[Nat][Nat][succ][x][y] e

def add(x: Nat, y: Nat) =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def mul(x: Nat, y: Nat) =
    match x {
        case zero => zero
        case succ(n) => add y (mul n y)
    }
"#;
    assert_parity(&format!(
        r#"{prefix}
def add_zero_right(a: Nat): Eq (add a zero) a =
    match a {{
        case zero => refl zero
        case succ(t) => cong_succ (add_zero_right t)
    }}
"#
    ));
    assert_parity(&format!(
        r#"{prefix}
def add_succ_right(a: Nat, b: Nat): Eq (add a (succ b)) (succ (add a b)) =
    match a {{
        case zero => rfl[Nat][succ b]
        case succ(t) => cong_succ (add_succ_right t b)
    }}
"#
    ));
    // add_comm（含 symm/trans 与 b 侧卡住的搬运）
    assert_parity(&format!(
        r#"{prefix}
def symm[A, x, y: A](e: Eq[A] x y): Eq[A] y x =
    match e {{
        case refl(a) => refl[A] a
    }}

def trans[A, x, y, z: A](e1: Eq[A] x y, e2: Eq[A] y z): Eq[A] x z =
    match e1 {{
        case refl(a) => e2
    }}

def add_zero_right(a: Nat): Eq (add a zero) a =
    match a {{
        case zero => refl zero
        case succ(t) => cong_succ (add_zero_right t)
    }}

def add_succ_right(a: Nat, b: Nat): Eq (add a (succ b)) (succ (add a b)) =
    match a {{
        case zero => rfl[Nat][succ b]
        case succ(t) => cong_succ (add_succ_right t b)
    }}

def add_comm(a: Nat, b: Nat): Eq (add a b) (add b a) =
    match a {{
        case zero => trans (refl b) (symm (add_zero_right b))
        case succ(t) => trans (cong_succ (add_comm t b)) (symm (add_succ_right b t))
    }}
"#
    ));
    // add_assoc
    assert_parity(&format!(
        r#"{prefix}
def add_assoc(a: Nat, b: Nat, c: Nat): Eq (add (add a b) c) (add a (add b c)) =
    match a {{
        case zero => rfl
        case succ(t) => cong_succ (add_assoc t b c)
    }}
"#
    ));
    // mul_zero_right / mul_one_right（let 绑定的中间引理）
    assert_parity(&format!(
        r#"{prefix}
def trans[A, x, y, z: A](e1: Eq[A] x y, e2: Eq[A] y z): Eq[A] x z =
    match e1 {{
        case refl(a) => e2
    }}

def mul_zero_right(n: Nat): Eq[Nat] (mul n zero) zero =
    match n {{
        case zero => rfl
        case succ(k) => trans (refl (add zero (mul k zero))) (mul_zero_right k)
    }}
"#
    ));
    assert_parity(&format!(
        r#"{prefix}
def trans[A, x, y, z: A](e1: Eq[A] x y, e2: Eq[A] y z): Eq[A] x z =
    match e1 {{
        case refl(a) => e2
    }}

def add_zero_left(m: Nat): Eq[Nat] (add zero m) m =
    rfl

def mul_one_right(n: Nat): Eq[Nat] (mul n (succ zero)) n =
    match n {{
        case zero => rfl[Nat][zero]
        case succ(k) =>
            let ih = mul_one_right k;
            let lemma: Eq[Nat] (add (succ zero) k) (succ k) = cong_succ (add_zero_left k);
            trans (cong[Nat][Nat][add (succ zero)][mul k (succ zero)][k] ih) lemma
    }}
"#
    ));
    // bits_adder（L13 迁移：Vec[Bool] 递归全加器，嵌套模式 + 隐式槽）
    assert_parity(
        r#"
enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

enum Product[A, B] {
    product(a: A, b: B)
}

def half_adder(lhs: Bool, rhs: Bool): Product[Bool][Bool] =
    match lhs {
        case false => product false rhs
        case true => match rhs {
            case false => product false true
            case true => product true false
        }
    }

def full_adder(lhs: Bool, rhs: Bool, carrier: Bool): Product[Bool][Bool] =
    match lhs {
        case false => half_adder rhs carrier
        case true => match rhs {
            case false => half_adder true carrier
            case true => product true carrier
        }
    }

def bits_adder_carrier[len: Nat](lhs: Vec[Bool] len, rhs: Vec[Bool] len, carrier: Bool): Vec[Bool] (succ len) =
    match lhs {
        case nil => cons carrier nil
        case cons[_](n, taill) => match rhs {
            case cons[_](m, tailr) => match bits_adder_carrier taill tailr carrier {
                case cons[_](c, tail) => match full_adder n m c {
                    case product(a, b) => cons a (cons b tail)
                }
            }
        }
    }

def bits_adder[len: Nat](lhs: Vec[Bool] len, rhs: Vec[Bool] len): Vec[Bool] (succ len) =
    bits_adder_carrier lhs rhs false

println bits_adder (cons true nil) (cons false nil)
"#,
    );
}

// Err 判定 parity（名称不在 scope / icit 失配 / match 不完整 / 分支不可达 /
// can't unify）
// --------------------------------------------------------------------------------

#[test]
fn parity_error_cases() {
    for src in [
        // 名称不在 scope
        "println nope\n",
        // icit 失配
        "def g : U -> U -> U = x => y => x\nprintln (g U)\n",
        // 命名 λ 不可推断
        "def h = [B = x] y => y\nprintln h\n",
        // 字面量 vs U
        "def bad : U = \"not a type\"\nprintln bad\n",
        // match 不能被推断
        "enum Bool {\n    true\n    false\n}\ndef bad =\n    match true {\n        case true => false\n    }\n",
    ] {
        assert_parity(src);
    }
    // match 不完整：缺少构造子
    assert_parity(
        r#"
enum Bool {
    true
    false
}

def bad(x: Bool): Bool =
    match x {
        case true => false
    }
"#,
    );
    // 分支不可达：Vec[Nat] zero 上没有 cons
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

def bad(v: Vec[Nat] zero): Nat =
    match v {
        case cons(x, xs) => x
    }
"#,
    );
    // can't unify：Eq two three 不可证
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Eq[A](x: A, y: A) {
    refl[a: A] -> Eq[A] a a
}

def two = succ (succ zero)

def three = succ (succ (succ zero))

def bad: Eq two three = refl
"#,
    );
    // can't unify：卡住内建（string_concat 实参非字面量）不无条件判等
    assert_parity(
        r#"
enum Eq[A : U](x : A, y : A) {
    refl(x : A) -> Eq[A] x x
}

def bad(x: String, y: String, z: String): Eq[String] (string_concat x y) (string_concat x z) =
    refl [String] (string_concat x y)

println bad
"#,
    );
    // 已登记名不冒充 String（宽松臂把关）
    assert_parity(
        r#"
def bad : String = get_global "file_delete"
println bad
"#,
    );
}

// 深负载：church / strchain / globals / match 链 / 多 enum 依赖索引
// --------------------------------------------------------------------------------

fn parse_or_panic(src: &str) -> Vec<fast::SourceDecl> {
    match fast::parse(src, 0) {
        Ok(ast) => ast,
        Err(e) => panic!("parse failed: {e}\nsrc:\n{src}"),
    }
}

#[test]
fn deep_workloads_parity() {
    // church：2^(k+1) 翻倍链（nf 节点数 = 2n + 4）
    let src = fast::church_src(8);
    let ast = parse_or_panic(&src);
    let n = 1u64 << 9;
    let basic = {
        let ast = ast.clone();
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(move || L08_product_type::bench_check(&ast))
            .unwrap()
            .join()
            .unwrap()
    };
    let mut t = fast::Tycker::new();
    assert!(t.bench_check(&ast), "church 未通过（fast）");
    assert!(basic, "church 未通过（basic）");
    let basic_nf = {
        let ast = ast.clone();
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(move || L08_product_type::bench_check_nf(&ast))
            .unwrap()
            .join()
            .unwrap()
    };
    assert_eq!(t.bench_check_nf_memo(&ast), basic_nf, "church nf 节点数");
    assert_eq!(basic_nf, 2 * n + 4, "church nf 公式");
    // Ok 输出互检（含 println）
    assert_parity(&format!("{}println p_8\n", fast::church_src(8)));

    // strchain：builtin 触发链（nf 节点数 = 1）
    let src = fast::strchain_src(9);
    let ast = parse_or_panic(&src);
    assert!(t.bench_check(&ast), "strchain 未通过");
    assert_eq!(t.bench_check_nf_memo(&ast), 1, "strchain nf 节点数");
    let src_print = fast::strchain_src(5) + "println s0\n";
    assert_parity(&src_print);

    // globals：可变全局 + 重入 prim（nf 节点数 = 1）
    let src = fast::globals_src(9);
    let ast = parse_or_panic(&src);
    assert!(t.bench_check(&ast), "globals 未通过");
    assert_eq!(t.bench_check_nf_memo(&ast), 1, "globals nf 节点数");

    // match 链：自递归依赖 match（编译期特化 + 运行时首匹配）
    let src = fast::match_src(6);
    let ast = parse_or_panic(&src);
    assert!(t.bench_check(&ast), "match 链未通过");
    let basic_nf = {
        let ast = ast.clone();
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(move || L08_product_type::bench_check_nf(&ast))
            .unwrap()
            .join()
            .unwrap()
    };
    assert_eq!(t.bench_check_nf_memo(&ast), basic_nf, "match 链 nf 节点数");
    assert_parity(&src);
    // 卡住 match 的深 parity：递归函数值直接打印（分支体简化表 quote 的
    // 发散路径）
    assert_parity(
        &format!(
            "{}def g(m : Nat) : Nat = succ (f_6 m)\nprintln g\n",
            fast::match_src(6)
        ),
    );

    // enum 负载：多 enum + Vec 风格 GADT + 索引等式 + 投影 + 递归 length
    assert_parity(&fast::enum_src());
}

#[test]
fn parity_stuck_prim_and_match_mix() {
    // 卡住 match（实参非字面量的 builtin）+ 卡住投影 + pending 应用链
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

def f(n: Nat): String -> String =
    match n {
        case zero => s => string_concat s "!"
        case succ(k) => s => string_concat "!" s
    }

println (f zero "a")
println (f (succ zero) "a")
println (f zero)
println f
"#,
    );
    // 投影 + 卡住投影的 unify / quote
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

def two = succ (succ zero)

def t = cons two nil

def useLen[L: Nat](v: Vec[Nat] L): Nat = v.len

println (useLen t)
"#,
    );
}

#[test]
fn steady_state_reuse() {
    // 稳态复用：同一 Tycker 连续多轮（decl 表 / mutable_map / pm 事实表轮
    // 清空），输出与每轮新建的一致
    let _guard = FILE_IO_LOCK.lock().unwrap();
    let src = L08_product_type::DEMO_SRC;
    let steady_src = src.to_owned();
    let r1 = std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let mut steady = fast::Tycker::new();
            steady.run_input(&steady_src, 0).unwrap()
        })
        .unwrap()
        .join()
        .unwrap();
    let steady_src = src.to_owned();
    let r2 = std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let mut steady = fast::Tycker::new();
            steady.run_input(&steady_src, 0).unwrap();
            steady.run_input(&steady_src, 0).unwrap()
        })
        .unwrap()
        .join()
        .unwrap();
    let fresh = run_fast(src).unwrap();
    assert_eq!(r1, r2, "稳态两轮不一致");
    assert_eq!(r1, fresh, "稳态与一次性不一致");
}

// 产品类型（struct / new / 值级与类型级投影 / 依赖字段 / mk 限定名）
// --------------------------------------------------------------------------------

#[test]
fn parity_product_basic() {
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

def two = succ (succ zero)
def four = succ (succ two)

struct Point {
    x: Nat
    y: Nat
}

struct Unit {
}

def p = new Point(two, four)
println p.x
println p.y
println p

def p2 = Point.mk two four
println p2

def u = new Unit()
println u
"#,
    );
}

#[test]
fn parity_product_generic() {
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

def add(x: Nat, y: Nat): Nat =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def two = succ (succ zero)
def four = add two two

struct Point[T] {
    x: T
    y: T
}

def get_x[T](p: Point[T]) = p.x

def point_add(p1: Point[Nat], p2: Point[Nat]): Point[Nat] =
    new Point((add p1.x p2.x), (add p1.y p2.y))

def start_point = new Point(zero, four)
def end_point = new Point(four, two)

println (get_x start_point)
println (point_add start_point end_point)

def sy : Nat = end_point.y
println sy
"#,
    );
}

#[test]
fn parity_product_dependent() {
    assert_parity(
        r#"
def Eq[A : U](x: A, y: A): U = (P : A -> U) -> P x -> P y
def rfl[A : U, x: A]: Eq[A] x x = _ => px => px

enum Nat {
    zero
    succ(x: Nat)
}

def two = succ (succ zero)

struct Bits {
    name: String
    size: Nat
}

def get_name(x: Bits) = x.name
def sigA = new Bits("A", two)
println (get_name sigA)
println sigA

struct Exists[A: U, P: A -> U] {
    witness: A
    proof: (P witness)
}

def exists_two: Exists[Nat][x => Eq x two] =
    Exists.mk[Nat][x => Eq x two] two rfl

println exists_two
def w : Nat = exists_two.witness
println w
"#,
    );
}

#[test]
fn parity_product_dependent_check() {
    // 类型级 .mk 剥链的精确性在检查位：前字段 binder 以接收者卡住
    // 投影实例化（评审修复回归——修复前 `U` 占位令两版一致地假拒，
    // parity 绿≠正确，此用例锁判定结果）。
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

def Eq[A : U](x: A, y: A): U = (P : A -> U) -> P x -> P y
def rfl[A : U, x: A]: Eq[A] x x = _ => px => px
def two = succ (succ zero)

struct Exists[A: U, P: A -> U] {
    witness: A
    proof: (P witness)
}

def use_proof (e : Exists[Nat][x => Eq x two]) : Eq e.witness two = e.proof
def e2 : Exists[Nat][x => Eq x two] = Exists.mk[Nat][x => Eq x two] two rfl
def z : Eq e2.witness two = e2.proof
println z
println (use_proof e2)
"#,
    );
}

#[test]
fn parity_product_new_dot_chain() {
    // `new` 结果直接接 `.field` 后缀链（评审补齐的语法，两版共用解析器）
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}
def two = succ (succ zero)

struct Point {
    x: Nat
    y: Nat
}

struct Line {
    a: Point
    b: Point
}

def d1 = new Point(two, zero).x
def d2 = new Line(new Point(zero, zero), new Point(two, two)).b.x
println d1
println d2
"#,
    );
}

#[test]
fn parity_product_chains_and_partial() {
    // 左结合投影链（L08 语法扩展）：类型级逐段剥 .mk、值级逐段 project
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

struct Point {
    x: Nat
    y: Nat
}

struct Line {
    a: Point
    b: Point
}

def far(l: Line): Nat = l.a.x

def l = new Line((new Point(zero, succ zero)), (new Point(succ zero, zero)))
println (far l)
println l.b.x

def part = new Point(zero)
println (part (succ zero))
println Point.mk
"#,
    );
    // struct + match 变量臂（构造子名带点不可解构，绑定后走投影）
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

struct Point {
    x: Nat
    y: Nat
}

def f(p: Point): Nat =
    match p {
        case pt => pt.x
    }

println (f (new Point(zero, succ zero)))
"#,
    );
}

#[test]
fn parity_product_errors() {
    for src in [
        // 字段不存在（值级 receiver 是构造子值）
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\nstruct Point {\n    x: Nat\n}\n\ndef p = new Point(zero)\ndef bad = p.zzz\n",
        // 字段不存在（类型级——.mk 剥链也未命中）
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\nstruct Point {\n    x: Nat\n}\n\ndef bad(p: Point) = p.zzz\n",
        // 普通单 case enum 不享受 .mk 类型级剥链
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\nenum Wrap {\n    only(x: Nat)\n}\n\ndef bad(w: Wrap) = w.x\n",
        // new 的名字不存在
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\ndef bad = new Nope(zero)\n",
        // struct 字段类型错误
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\nenum Bool {\n    true\n    false\n}\n\nstruct Point {\n    x: Nat\n}\n\ndef bad = new Point(true)\n",
    ] {
        assert_parity(src);
    }
}

#[test]
fn parity_product_shadow_and_blank_lines() {
    // 投影接收者的局部遮蔽：`Foo.c2` 在 `Foo` 是局部 binder 时必须走投影
    //（旧实现先查 decl 表，静默解析成全局构造子——错误 Ok），同名但类型
    // 不可投影时两版一致报 has no field
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Foo {
    c1(x: Nat)
    c2
}

struct S {
    c2: Foo
}

def s : S = new S(c1 zero)
def pick(Foo: S) = Foo.c2
println (pick s)
"#,
    );
    assert_parity(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\nenum Foo {\n    c1(x: Nat)\n    c2\n}\n\ndef pick(Foo: Nat) = Foo.c2\n",
    );
    // struct 字段间连续空行 / 注释行（注释行剥成空白后仍是 EndLine）
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

struct P {
    x: Nat

    // 注释行 + 空行
    y: Nat
}

def p = new P(zero, (succ (succ zero)))
println p.y
"#,
    );
}

#[test]
fn parity_match_differential_pending() {
    // 两侧卡住 match 的 pending 实参数差分（(f x) 带 [y, z]、(g x) 带
    // [w]）：MatchStruct 屏障的 icit 推入必须按公共前缀截断，差分判定
    // 保留给弹出侧的 MatchPendingLen——修复前推入期 `pd2[i]` 越界 panic
    //（进程崩溃 vs 参考版干净的分支体 Err，违反 Err 判定一致合同）。
    // 同时覆盖屏障路径：scrutinee 比完 → cases 长度 → pattern → 分支体
    //（case a 的 m=>n=>m 与 m=>m 在 η 后链长失配）→ 干净 Err。
    assert_parity(
        r#"
enum Foo {
    a
    b
}

enum Nat {
    zero
    succ(x: Nat)
}

enum Eq[A](x: A, y: A) {
    refl[t: A] -> Eq[A] t t
}

def f(x: Foo): Nat -> Nat -> Nat =
    match x {
        case a => m => n => m
        case b => m => n => n
    }

def g(x: Foo): Nat -> Nat =
    match x {
        case a => m => m
        case b => m => m
    }

def bad(x: Foo, y: Nat, z: Nat, w: Nat): Eq (g x w) (f x y z) = refl
"#,
    );
}

#[test]
fn parity_product_name_identity_redef() {
    // 同名 struct 重定义 + 类型按名合一（Sum-Sum 臂只比名字与参数槽，
    // cases 不参与）的组合语义：后注册者覆盖 decl 表，早期 def 的登记
    // 类型仍是旧一代 `Val::Sum` 值，但与新一代同名 Sum 判等通过——旧
    // 函数会接受并产出新形状的值（`bad : Nat` 打印 `Bool::true`）。
    // 这是 L06+「后注册者覆盖同名裸名」decl 表设计 + 按名类型身份的
    // 组合结果（README §7 披露）：本用例锁定**两版一致地呈现**该语义，
    // 不是对其的背书。
    let src = r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Bool {
    true
    false
}

struct P {
    x: Nat
}

def get(p: P): Nat = p.x

struct P {
    x: Bool
}

def bad : Nat = get(new P(true))
println bad
"#;
    let b = run_basic(src);
    let f = run_fast(src);
    assert_eq!(
        b.as_deref().ok(),
        f.as_deref().ok(),
        "判定/输出不一致，src:\n{src}\nbasic={b:?}\nfast={f:?}"
    );
    assert_eq!(b.as_deref().ok(), Some("Bool::true\n"), "{src}");
}

#[test]
fn deep_workload_struct_parity() {
    // struct 负载（浅值投影 def 链 + 固定深度嵌套 Box 段）
    let src = fast::struct_src(8);
    let ast = parse_or_panic(&src);
    let mut t = fast::Tycker::new();
    assert!(t.bench_check(&ast), "struct 负载未通过（fast）");
    // 末值 = 构造子 zero：quote 出 SumCase + typ 的 Sum 两个节点
    assert_eq!(t.bench_check_nf_memo(&ast), 2, "struct nf 节点数");
    let basic = {
        let ast = ast.clone();
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(move || L08_product_type::bench_check(&ast))
            .unwrap()
            .join()
            .unwrap()
    };
    assert!(basic, "struct 负载未通过（basic）");
    let basic_nf = {
        let ast = ast.clone();
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(move || L08_product_type::bench_check_nf(&ast))
            .unwrap()
            .join()
            .unwrap()
    };
    assert_eq!(
        t.bench_check_nf_memo(&ast),
        basic_nf,
        "struct 负载 nf 节点数不一致"
    );
    assert_parity(&src);
}
