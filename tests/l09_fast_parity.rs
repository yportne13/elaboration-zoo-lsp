//! L09_mltt 双 oracle 互检套件（参考版 `run` ↔ 性能版 `bump_spine_iter::
//! run_fast`）。`#[path]` 只编 list.rs / bimap.rs / parser_lib.rs /
//! L09_mltt/mod.rs（不含 LSP / L02-L08 / L10-L13），迭代快数倍
//! （tests/l08_fast_parity.rs 同款）。
//!
//! 判据：**Ok 输出逐字节一致 / Err 判定一致**。错误文案两处已知偏差是
//! 文档化偏差，比对前归一化：参考版错误 Span 携带源码偏移（快版全零），
//! 且参考版消息内嵌的 Debug-Val/Tm 带真实偏移——统一剥掉
//! `start_offset/end_offset/path_id` 数字后比对正文。


#[path = "../src/list.rs"]
mod list;

#[path = "../src/bimap.rs"]
mod bimap;

#[path = "../src/parser_lib.rs"]
mod parser_lib;
#[path = "../src/parser_lib_resilient.rs"]
mod parser_lib_resilient;

#[path = "../src/L09_mltt/mod.rs"]
mod L09_mltt;

use L09_mltt::bump_spine_iter as fast;

/// 在大栈线程里跑参考版 `run`。
fn run_basic(src: &str) -> Result<String, L09_mltt::Error> {
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || L09_mltt::run(&input, 0))
        .unwrap()
        .join()
        .unwrap()
}

/// 在大栈线程里跑快版 `run_fast`。
fn run_fast(src: &str) -> Result<String, L09_mltt::Error> {
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || fast::run_fast(&input, 0))
        .unwrap()
        .join()
        .unwrap()
}

/// Err 文案归一化：剥掉 Debug-Span 的偏移数字（文档化偏差：参考版错误
/// 的 Debug-Span 携带源码偏移，快版导出项全零）。
fn norm_err(e: &str) -> String {
    let mut out = String::with_capacity(e.len());
    let b = e.as_bytes();
    let mut i = 0usize;
    while i < b.len() {
        // `@ N` / `@ N,M`（Span 自定义 Debug）
        if b[i] == b'@' && i + 1 < b.len() && b[i + 1] == b' ' {
            let mut j = i + 2;
            while j < b.len() && b[j].is_ascii_digit() {
                j += 1;
            }
            if j > i + 2 {
                if j < b.len() && b[j] == b',' {
                    let mut k = j + 1;
                    while k < b.len() && b[k].is_ascii_digit() {
                        k += 1;
                    }
                    if k > j + 1 {
                        j = k;
                    }
                }
                out.push_str("@ _");
                i = j;
                continue;
            }
        }
        // start_offset: N / end_offset: N / path_id: N（派生 Debug 形态）
        let rest = &e[i..];
        let mut matched = false;
        for key in ["start_offset: ", "end_offset: ", "path_id: "] {
            if rest.starts_with(key) {
                let mut j = i + key.len();
                while j < b.len() && b[j].is_ascii_digit() {
                    j += 1;
                }
                if j > i + key.len() {
                    out.push('_');
                    i = j;
                    matched = true;
                    break;
                }
            }
        }
        if matched {
            continue;
        }
        let ch = e[i..].chars().next().unwrap();
        out.push(ch);
        i += ch.len_utf8();
    }
    out
}

fn err_text(e: &L09_mltt::Error) -> String {
    norm_err(&e.0.data)
}

/// Oracle：参考版与性能版的 Ok 输出逐字节一致；Err 判定一致，且归一化
/// 后的错误正文一致。
fn assert_parity(src: &str) {
    let b = run_basic(src);
    let f = run_fast(src);
    match (&b, &f) {
        (Ok(b), Ok(f)) => assert_eq!(
            b, f,
            "Ok 输出双实现不一致，src:\n{src}\n--- basic ---\n{b}--- fast ---\n{f}"
        ),
        (Err(b), Err(f)) => assert_eq!(
            err_text(b),
            err_text(f),
            "Err 正文（span 归一化后）双实现不一致，src:\n{src}\n--- basic ---\n{}\n--- fast ---\n{}",
            b.0.data,
            f.0.data
        ),
        _ => panic!(
            "判定不一致（basic={}，fast={}），src:\n{src}\nbasic-err={:?}\nfast-err={:?}",
            b.as_ref().map(|_| "Ok").unwrap_or("Err"),
            f.as_ref().map(|_| "Ok").unwrap_or("Err"),
            b.as_ref().err().map(|e| &e.0.data),
            f.as_ref().err().map(|e| &e.0.data),
        ),
    }
}

// 基础：enum / match / 多态 / 高阶 / struct / new / 投影
// --------------------------------------------------------------------------------

#[test]
fn parity_tests_rs_basic() {
    // mod.rs test2 的主体（enum + 依赖 match + struct + 投影 + 等式推理）
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

def mul(x: Nat, y: Nat) = match x {
    case zero => zero
    case succ(n) => add y (mul n y)
}

def four = add two two

println four

struct Point[T] {
    x: T
    y: T
}

def get_x[T](p: Point[T]): T = p.x

def point_add(p1: Point[Nat], p2: Point[Nat]): Point[Nat] =
    new Point((add p1.x p2.x), (add p1.y p2.y))

def start_point = new Point(zero, four)

def end_point = new Point(four, two)

println (get_x start_point)

println (point_add start_point end_point)

def Eq[A](x: A, y: A) = (P : A -> Type 0) -> P x -> P y

def refl[A, x: A]: Eq[A] x x = _ => px => px

struct Bits {
    name: String
    size: Nat
}

def get_name(x: Bits) = x.name

def assign(a: Bits, b: Bits)(eq: Eq[Nat] a.size b.size): String = a.name

def sigA = new Bits("A", four)

def sigB = new Bits("B", four)

def sigC = new Bits("C", two)

def sigD = new Bits("D", two)

def ab = assign sigA sigB refl

def cd = assign sigC sigD refl
"#,
    );
}

#[test]
fn parity_universe_levels() {
    // mod.rs test2 的宇宙段：Type N 分层、高宇宙 enum、依赖类型参数
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

def test0: Type 1 = Type 0

def test1: Type 2 = Type 1 -> Type 0

enum HighLvl[A] {
    case1(a: A)
    case2(a: test1)
}

def test2: HighLvl[Nat] = case1 zero

def test3: Type 2 = HighLvl[Nat]

enum HighLvl2[A: Type 2] {
    case2_1(x: A)
    case2_2(x: Nat)
}

def test1_2: HighLvl2[HighLvl[Nat]] = case2_1 test2

def test1_3: Type 2 = HighLvl2[HighLvl[Nat]]

enum HighLvl3[A: Type 2] {
    case3_1
    case3_2(x: Nat)
}

def test2_2: HighLvl3[HighLvl[Nat]] = case3_1

def test2_3: Type 2 = HighLvl3[HighLvl[Nat]]

println test0
println test1
println test3
println test1_3
"#,
    );
    // struct 版高宇宙（.mk 剥链 + new）
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

def test1: Type 2 = Type 1 -> Type 0

def test2_t: Type 1 -> Type 0 = t => Nat

struct HighLvl[A] {
    case1: A
    case2: test1
}

def test2: HighLvl[Nat] = new HighLvl(zero, test2_t)

def test3: Type 2 = HighLvl[Nat]

struct HighLvl2[A: Type 2] {
    case2_1: A
    case2_2: Nat
}

def test1_2: HighLvl2[HighLvl[Nat]] = new HighLvl2(test2, zero)

def test1_3: Type 2 = HighLvl2[HighLvl[Nat]]

println test3
println test1_3
"#,
    );
}

#[test]
fn parity_lambda_calculus() {
    // mod.rs test 的 church 风格段：纯依赖 λ 演算 + 字符串内建
    assert_parity(
        r#"
def str_id(x: String, y: String): String = x

def str_id2: String = string_concat "hello " "world"

println str_id2

def Eq[A : Type 0](x: A, y: A): Type 0 = (P : A -> Type 0) -> P x -> P y

def refl[A : Type 0, x: A]: Eq[A] x x = _ => px => px

def the(A : Type 0)(x: A): A = x

def m : Type 0 -> Type 0 -> Type 0 -> Type 0 = _
def test = a => b => c => the (Eq (m a b c) (m c b a)) refl

def pr1 = f => x => f x

def Nat : Type 0 =
    (N : Type 0) -> (N -> N) -> N -> N
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

def stuck_concat = string_concat mystr

println stuck_concat
println (stuck_concat "!")
"#,
    );
}

// 索引族 / 依赖 match / 卡住 match / 等式推理
// --------------------------------------------------------------------------------

#[test]
fn parity_tests_rs_index() {
    // 索引族 Eq / Vec、构造子返回类型、投影
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
    // 索引精化传播到分支体与返回类型、嵌套 match
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
fn parity_eq_reasoning() {
    // cong / symm / trans / rfl
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

def two = succ (succ zero)

def ck: Eq two two = rfl
println ck
"#,
    );
}

#[test]
fn parity_stuck_match() {
    // 卡住 match 的合一 / splice / 外层 binder 实参
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

def V(n: Nat): Type 0 =
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
"#,
    );
    // 卡住 match 的递归链（match_src 的 check 期与 quote 期协同）。
    // 注：`println g`（打印引用自递归卡住 match 的函数值）会让参考版
    // v_app 触发 "impossible apply" panic（L09 语义下 succ 应用于卡住
    // match 值）——两版同崩，不进 parity 断言。
    assert_parity(&fast::match_src(6));
}

#[test]
fn parity_recursive_defs() {
    // 自递归 + 后定义引用先定义（fake_bind 占位 + global 表覆盖）
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

/// A6/§C 钉子：多层非线性 pruning 的掩码反转（参考版 `prune_ty` vs 快版
/// `prune_ty_bump`）。源取自 L06 `pruning_nonpalindrome_dependent_masks` 的
/// 非对称非线性形态（`m a a b c`），按 L09 的 `Type N` 层级适配：
/// `Eq` 是对 `A -> Type 0` 的 Leibniz 量化，故其**返回宇宙必须是 `Type 1`**
/// （`A : Type 0` ⇒ `A -> Type 0 : Type 1`）；直接照搬 `: Type 0` 会在
/// `Eq` 声明处就报 `find Type 0 / expected Type 1`，根本走不到 pruning。
///
/// `m a a b c` 的重复实参（η 展开后掩码内先序 `[Some,Some,Some,None,None]`）
/// 使参考版旧实现（不反转、按链头配最外层 Π）保留 A/B、剪掉 C/D，而 codomain
/// `D -> D` 引用被剪的 D → 参考版 Err，快版 Ok（修复前分叉）；修复后参考版
/// 与快版 `mask_inner_first.iter().rev()` 同口径，两版 Ok。
#[test]
fn parity_nonlinear_pruning_rev_mask() {
    let src = r#"
def Eq[A : Type 0](x : A, y : A) : Type 1 = (P : A -> Type 0) -> P x -> P y

def refl[A : Type 0, x : A] : Eq[A] x x = P => px => px

def m : (A : Type 0) -> (B : Type 0) -> (C : Type 0) -> (D : Type 0) -> D -> D = _

def test (a : Type 0)(b : Type 0)(c : Type 0) : Eq (m a a b c) (d => d) = refl
"#;
    assert!(
        run_basic(src).is_ok(),
        "多层非线性剪枝源应能过类型检查并解出 meta，basic={:?}",
        run_basic(src)
    );
    assert_parity(src);
}

/// A7 钉子：0 号全局（`global_idx=0` ⇒ 层级恰为哨兵 `1919810`）自引用。
/// 边界必须是 `>=`：用 `>` 会走 `l - x - 1` 下溢（debug panic / release
/// 大索引越界）；`println f` 经 pretty 的 `>=` 分支打印 `recursive_0`。
#[test]
fn parity_global_sentinel_self_ref() {
    let src = "def f : String = f\n\nprintln f\n";
    assert_eq!(run_basic(src).unwrap(), "recursive_0\n");
    assert_parity(src);
}

#[test]
fn parity_eq_proofs() {
    // 依赖递归函数的索引族等式推理（stuck match 与精化的组合推理全链路）
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
    assert_parity(&format!(
        r#"{prefix}
def add_assoc(a: Nat, b: Nat, c: Nat): Eq (add (add a b) c) (add a (add b c)) =
    match a {{
        case zero => rfl
        case succ(t) => cong_succ (add_assoc t b c)
    }}
"#
    ));
}

#[test]
fn parity_nested_patterns() {
    // 嵌套模式 + 深层绑定器的 de Bruijn 对齐
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
}

#[test]
fn parity_holes_and_let() {
    // 洞 / let / 隐式插入
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

def two = succ (succ zero)

def ck : Nat = _

def with_let : Nat = let x = two; succ x

println with_let
println (ck two)
"#,
    );
}

// Err 判定 parity
// --------------------------------------------------------------------------------

#[test]
fn parity_error_cases() {
    for src in [
        // 名称不在 scope（L09 消息前缀 "error "）
        "println nope\n",
        // icit 失配
        "def g : Nat -> Nat -> Nat = x => y => x\nprintln (g zero)\n",
        // 命名 λ 不可推断
        "def h = [B = zero] y => y\nprintln h\n",
        // 字面量 vs 宇宙（expected universe, got LiteralType）
        "def bad : Type 0 = \"not a type\"\nprintln bad\n",
        // match 不能被推断
        "enum Bool {\n    true\n    false\n}\ndef bad =\n    match true {\n        case true => false\n    }\n",
        // 字段不存在（值级 receiver 是构造子值）
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\nstruct Point {\n    x: Nat\n}\n\ndef p = new Point(zero)\ndef bad = p.zzz\n",
        // 字段不存在（类型级）
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\nstruct Point {\n    x: Nat\n}\n\ndef bad(p: Point) = p.zzz\n",
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
}

// 深负载：church / strchain / match 链 / 多 enum 依赖索引 / struct 链
// --------------------------------------------------------------------------------

fn parse_or_panic(src: &str) -> Vec<fast::SourceDecl> {
    match fast::parse(src, 0) {
        Ok(ast) => ast,
        Err(e) => panic!("parse failed: {e}\nsrc:\n{src}"),
    }
}

fn basic_bench(ast: &[fast::SourceDecl], f: fn(&[fast::SourceDecl]) -> u64) -> u64 {
    let ast = ast.to_vec();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || f(&ast))
        .unwrap()
        .join()
        .unwrap()
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
            .spawn(move || L09_mltt::bench_check(&ast))
            .unwrap()
            .join()
            .unwrap()
    };
    let mut t = fast::Tycker::new();
    assert!(t.bench_check(&ast), "church 未通过（fast）");
    assert!(basic, "church 未通过（basic）");
    let basic_nf = basic_bench(&ast, L09_mltt::bench_check_nf);
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

    // match 链：自递归依赖 match（编译期特化 + 运行时首匹配）
    let src = fast::match_src(6);
    let ast = parse_or_panic(&src);
    assert!(t.bench_check(&ast), "match 链未通过");
    let basic_nf = basic_bench(&ast, L09_mltt::bench_check_nf);
    assert_eq!(t.bench_check_nf_memo(&ast), basic_nf, "match 链 nf 节点数");
    assert!(basic_nf > 0, "match 链 basic nf");
    assert_parity(&src);

    // enum 负载：多 enum + Vec 风格 GADT + 索引等式 + 投影 + 递归 length
    assert_parity(&fast::enum_src());

    // struct 负载：浅值投影 def 链（末值 = zero：SumCase + typ 两个节点）
    let src = fast::struct_src(7);
    let ast = parse_or_panic(&src);
    assert!(t.bench_check(&ast), "struct 负载未通过（fast）");
    assert_eq!(t.bench_check_nf_memo(&ast), 2, "struct nf 节点数");
    let basic = {
        let ast = ast.clone();
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(move || L09_mltt::bench_check(&ast))
            .unwrap()
            .join()
            .unwrap()
    };
    assert!(basic, "struct 负载未通过（basic）");
    let basic_nf = basic_bench(&ast, L09_mltt::bench_check_nf);
    assert_eq!(t.bench_check_nf_memo(&ast), basic_nf, "struct nf 不一致");
    assert_parity(&src);
}

#[test]
fn steady_state_reuse() {
    // 稳态复用：同一 Tycker 连续多轮（metacontext / global 表 / 环境区域
    // 轮清空），输出与每轮新建的一致
    let src = fast::enum_src();
    let r1 = std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let mut steady = fast::Tycker::new();
            steady.run_input(&src, 0).unwrap()
        })
        .unwrap()
        .join()
        .unwrap();
    let src2 = fast::enum_src();
    let r2 = std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let mut steady = fast::Tycker::new();
            steady.run_input(&src2, 0).unwrap();
            let src3 = fast::enum_src();
            steady.run_input(&src3, 0).unwrap()
        })
        .unwrap()
        .join()
        .unwrap();
    let src4 = fast::enum_src();
    let fresh = run_fast(&src4).unwrap();
    assert_eq!(r1, r2, "稳态两轮不一致");
    assert_eq!(r1, fresh, "稳态与一次性不一致");
}


// —— L08→L09 继承连续性探针（A4 本轮补）——
// struct / new / 多段投影是 L08 的核心语言特性（脱糖为单构造子 enum）；
// L09 的 parser 保留了该子集，但此前没有 parity 用例钉住这条 L08 血统
// 契约。预期：两版 Ok 输出逐字节一致（构造子值 + 投影字段）；若某形态
// 被 L09 裁掉则两版同 Err（parity 判定仍须一致）。
#[test]
fn parity_struct_new_projection_l08_heritage() {
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

def headX(l: Line): Nat = l.a.x

println (headX (new Line(new Point(two, zero), new Point(zero, two))))

struct Dd[P: Nat -> Type 0] {
    w: Nat
    r: (P w)
}

def K(x: Nat): Type 0 = Nat

def dd = new Dd(two, two)

println dd.r
"#,
    );
}

// pretty 降级回归（本轮修复 accompany）：SumCase 头名 / 构造子值打印的
// 常规形态（quote 后的 nf 里 typ 恒为 Tm::Sum，走 sum_head_name 的 Sum
// 臂，输出与修复前逐字节一致）。钉住"降级只作用于不可达形态、不漂移
// 正常输出"。
#[test]
fn parity_ctor_value_print_shape() {
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

println (new Point(two, zero))
println two
"#,
    );
}

// —— A7 §2.6 转交：字面输出 golden（防共享 parser/pretty 漂移「两版同变」）——
// 预期值静态推导自 pretty_tm 各臂（pretty.rs）+ 已验证 parity 用例形态；
// 构造子值格式为 L09-L13 的 comma 血统（`Vec[Bool]::cons(1, …)`，锚点
// src/L13_namespace/legacy_tests.rs:604、src/L12_canonical/mod.rs:1479）；
// struct 值按本层实现显示为 `头名::Point.mk(...)`（分支名自带 .mk）。
// golden 只钉参考版 run 的 Ok 输出（双 oracle 一致性由上方 parity 套件
// 另行锁定）。

#[test]
fn golden_string_literals_and_concat() {
    let src = r#"
def mystr = "hello world"

def mystr2 = string_concat mystr "!"

println mystr
println mystr2
println (string_concat "hello " "world")
"#;
    assert_eq!(
        run_basic(src).unwrap(),
        "hello world\nhello world!\nhello world\n",
        "字符串字面量 / string_concat 全应用按裸内容打印（LiteralIntro 臂）"
    );
}

#[test]
fn golden_nat_and_bool_ctor_values() {
    let src = r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Bool {
    true
    false
}

def two = succ (succ zero)

def not(x: Bool): Bool =
    match x {
        case true => false
        case false => true
    }

println two
println zero
println (not true)
println (not false)
"#;
    assert_eq!(
        run_basic(src).unwrap(),
        "Nat::succ(Nat::succ(Nat::zero))\nNat::zero\nBool::false\nBool::true\n",
        "非泛型构造子值：头名::分支名(实参…，逗号连接)；two = succ(succ(zero)) 两层 succ"
    );
}

#[test]
fn golden_struct_mk_value_and_projection() {
    // struct 脱糖的分支名自带 `.mk`（parser/mod.rs），显示为
    // `头名::Point.mk(...)`；单级值级投影 p.x 化简到字段值（mod.rs eval
    // Tm::Obj 的 SumCase datas 按名查找，与 l10 parity_basics 的
    // `println p.x` 同形）。链式投影 l.a.x 的实际字节无法静态可靠推导
    // （终门禁实测与字段直取不符），不钉，见 a4-r2 Round 3 补救。
    let src = r#"
enum Nat {
    zero
    succ(x: Nat)
}

def two = succ (succ zero)

struct Point {
    x: Nat
    y: Nat
}

def p = new Point(two, zero)

println p
println p.x
"#;
    assert_eq!(
        run_basic(src).unwrap(),
        "Point::Point.mk(Nat::succ(Nat::succ(Nat::zero)), Nat::zero)\nNat::succ(Nat::succ(Nat::zero))\n",
        "struct 值 .mk 分支名 + 实参逗号连接（L09-L13 comma 血统）；值级投影化简到字段。手工展开：\
         two = succ(succ(zero))（两层 succ）；p = new Point(two, zero) 的 x 槽即 two 的值，\
         故 p 与 p.x 两行的 succ 链均为两层"
    );
}

#[test]
fn golden_universe_and_stuck_prim() {
    let src = r#"
def test0: Type 1 = Type 0

def test1: Type 2 = Type 1 -> Type 0

println test0
println test1

def mystr = "hello world"

def stuck_concat = string_concat mystr

println stuck_concat
println (stuck_concat "!")
"#;
    assert_eq!(
        run_basic(src).unwrap(),
        "Type 0\nType 1 → Type 0\ny => Prim Func\nhello world!\n",
        "宇宙字面 Type N、匿名 Π 的 → 箭头、string_concat 部分应用卡在 y 上的 Prim Func 形态"
    );
}

#[test]
fn golden_recursion_add_and_even() {
    let src = r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Bool {
    true
    false
}

def two = succ (succ zero)

def add(x: Nat, y: Nat) =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def four = add two two

def even(n: Nat): Bool =
    match n {
        case zero => true
        case succ(m) => match m {
            case zero => false
            case succ(k) => even k
        }
    }

println four
println (even four)
println (even (succ zero))
"#;
    // 期望值逐行手工展开（L09 不支持 def 前向引用——互递归 even/odd 在
    // even 体内引用 odd 会 Err "name not in scope"，故用单 def 自递归 +
    // 嵌套 match，只引用自身，fake_bind 自递归封口）：
    //   four = add two two = succ^4(zero)；
    //   even 4 = match 3 → succ → even 2 = match 1 → succ → even 0 = true；
    //   even 1 = succ(m=0) → match 0 → zero 臂 = false。
    assert_eq!(
        run_basic(src).unwrap(),
        "Nat::succ(Nat::succ(Nat::succ(Nat::succ(Nat::zero))))\nBool::true\nBool::false\n",
        "递归 def（自引用占位 Rigid 封口）归约到构造子链；嵌套 match 单 def 自递归 even"
    );
}

#[test]
fn golden_stuck_match_display() {
    // 卡住 match 是头等中性值；L09 时代的显示为 (unsolved match n)
    // （L08 的完整分支渲染未随 L08→L09 继承，刻意分歧已登记 a4-r2）。
    let src = r#"
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
"#;
    assert_eq!(
        run_basic(src).unwrap(),
        "n => (unsolved match n)\n",
        "卡住 match 的 λ 头 + (unsolved match 判别式) 形态"
    );
}

// 连续性审计 R2（2026-09）：L08 8988f7c「剥链精确化 + (Obj,Obj) 合同臂」回移探针
// --------------------------------------------------------------------------------

/// 依赖在前字段的在后字段（`proof : Eq witness two`）：剥链以接收者
/// **卡住投影**实例化显式字段 binder——旧 U(0) 占位使 `e.proof` 的类型
/// 成为 `Eq (U 0) two`，在检查位与 `Eq e.witness two` 合一失败（假拒）；
/// 精确化后参数槽是 stuck Obj 对，`(Obj,Obj)` 合同臂按接收者判等。
/// 断言两版 Ok + parity（修复前两版一致 Err，探针即失败）。
#[test]
fn parity_struct_dependent_field_projection() {
    let src = "enum Nat {\n    zero\n    succ(x: Nat)\n}\nenum Eq[A](x: A, y: A) {\n    refl(a: A) -> Eq a a\n}\ndef two = succ (succ zero)\nstruct Ex {\n    witness: Nat\n    proof: Eq witness two\n}\ndef p = Ex.mk two (refl two)\ndef get_proof(e: Ex): Eq e.witness two = e.proof\nprintln (get_proof p)\n";
    assert!(
        run_basic(src).is_ok(),
        "依赖字段投影在检查位假拒（剥链 U(0) 占位回退？），src:\n{src}"
    );
    assert_parity(src);
}

// 连续性审计 R3（2026-09）：enum/struct 声明处隐式无标注域钉 U(0) 的回移探针
// --------------------------------------------------------------------------------

/// L07/L08「黑盒三轮」修复的 L09 形态：多隐式无标注参数（`[A, B]`）时，
/// 第 2+ 个参数的域经 fresh_meta 的 AppPruning 成为部分应用 meta
/// （`?m A`），构造子上显式供给枚举隐式实参（`p1[Nat][Bool]`）需解
/// `?m A := U(0)`，L09 的 invert 对非变量 spine 实参（Nat 的值）直接
/// Err → 误报 can't unify。钉 U(0)（L09 全局默认层级）从声明处消除该
/// meta；struct 脱糖走同一 Decl::Enum 臂。显式标注（`[A : Type 0]`）
/// 与显式索引不动。
///
/// R3 门禁订正：原第 4 源 `enum Q[A : Type 0] { q[A](a: A) -> Q[A] a }`
/// 是**病态形态**——Q 无枚举级显式索引参数，返回类型 `Q[A] a` 把
/// `Q[A] : Type 0` 过度应用（App 臂对非 Π 函数类型造 `Π(?dom,?cod)`
/// 合一，`U(0) ≡ Π` 必败，enum 声明处即 Err）。R1 的 L08 探针同款源只
/// 做 parity 断言（两版一致 Err 也通过）故未被察觉；本套件的 is_ok
/// 断言揭示了它。已改写为 L07 `pack_annotated_params` 的合法索引族
/// 形态（枚举级显式索引 `(a : A)`、返回类型完全应用——L09 既有
/// `Vec[A](len: Nat)` 同构）。
#[test]
fn parity_enum_struct_impl_hole_pinned_u0() {
    for src in [
        // enum：多隐式无标注参数 + 显式实例化（修复的原始触发形态）
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\nenum Bool {\n    true\n    false\n}\nenum P1[A, B] {\n    p1[A, B](a: A, b: B) -> P1[A][B]\n}\nprintln (p1[Nat][Bool] zero true)\n",
        // enum：无标注隐式参数 + 注解处显式实例化 + 全显式构造子应用
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\nenum Bool {\n    true\n    false\n}\nenum P1[A, B] {\n    p1[A, B](a: A, b: B) -> P1[A][B]\n}\ndef s1: P1[Nat][Bool] = p1[Nat][Bool][Nat][Bool] zero true\nprintln s1\n",
        // struct：多类型参数 + 投影（脱糖路径同一臂）
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\nstruct Pair[A, B] {\n    fst: A\n    snd: B\n}\ndef p = new Pair(succ zero, zero)\nprintln p.fst\n",
        // 显式标注的隐式域与显式索引不动：annotated 索引族形态仍通过
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\nenum Q[A : Type 0](a: A) {\n    q[A](a: A) -> Q[A] a\n}\ndef t: Q[Nat] zero = q[Nat] zero\nprintln t\n",
    ] {
        // is_ok（参考版）+ 双版结果诊断输出 + parity
        let b = run_basic(src);
        let f = run_fast(src);
        assert!(
            b.is_ok(),
            "参考版 Err（隐式无标注域未钉 U(0)/钉后误拒/子用例病态？），src:\n{src}\nbasic={b:?}\nfast={f:?}"
        );
        assert_parity(src);
    }

}
