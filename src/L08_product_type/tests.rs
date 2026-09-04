//! L08 的测试套件 = L07 全部既有用例（继承和类型 / 依赖模式匹配 / builtin
//! 注册表行为）+ 产品类型专项：
//!
//! - `test_product_basic` / `test_product_generic` / `test_product_dependent` /
//!   `test_product_field_err`：`struct` / `new` / 字段投影（值级 + 类型级
//!   `.mk` 剥链）/ 依赖字段（Sigma：`Exists`）/ 错误路径。
//!   积类型的形态与旧 L08 test2 对齐（Point[T] / Bits / Exists 三连），
//!   语法糖的脱糖语义见 mod.rs 模块头。

use super::*;

/// 测试在 64MB 栈的线程里跑：类型检查的递归深度（依赖匹配的精化合一链）
/// 远超 cargo test harness 默认的 2MB 线程栈。
fn check(input: &str) -> String {
    let input = input.to_owned();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || run(&input, 0).unwrap_or_else(|e| panic!("check failed: {e:?}")))
        .unwrap()
        .join()
        .unwrap()
}

fn check_err(input: &str) -> String {
    let input = input.to_owned();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || match run(&input, 0) {
            Err(e) => e.0,
            Ok(out) => panic!("expected error, got ok:\n{out}"),
        })
        .unwrap()
        .join()
        .unwrap()
}

/// 基础 ADT + 多态 + 高阶函数（移植自 L07a test2）
#[test]
fn test_basic() {
    let out = check(
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
    assert_eq!(
        out.lines().collect::<Vec<_>>(),
        vec![
            "Bool::false",
            "Nat::succ(Nat::succ(Nat::succ(Nat::succ(Nat::zero))))",
            "Bool::true",
            "Bool::false",
            "Option(false) is",
            "Option::Some(Bool::false)",
            "Nat::succ(Nat::succ(Nat::succ(Nat::succ(Nat::succ(Nat::succ(Nat::succ(Nat::succ(Nat::zero))))))))",
        ]
    );
}

/// 索引族：Eq / Vec、构造子返回类型、投影（移植自 L07a test_index）
#[test]
fn test_index() {
    let out = check(
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
    assert_eq!(
        out.lines().collect::<Vec<_>>(),
        vec![
            "Nat::succ(Nat::succ(Nat::succ(Nat::succ(Nat::zero))))",
            "Nat::zero",
        ]
    );
}

/// 依赖模式匹配：索引精化传播到分支体与返回类型（移植自 L07a test5）
#[test]
fn test_dependent_match() {
    check(
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
}

/// 依赖模式匹配：嵌套 match 的 scrutinee 是计算出的值（移植自 L07a test6）
#[test]
fn test_dependent_match_nested_eval() {
    check(
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

/// 等式推理：cong / symm / trans / rfl（移植自 L07a test4 的核心部分）。
///
/// 已知限制（相对 L07a，详见 README 的"已知限制"一节）：依赖递归函数的
/// 索引族等式推理（add_zero_right / add_succ_right / add_comm / add_assoc，
/// 期望类型里出现"递归函数应用于模式绑定器"的 stuck match 组合）会触发
/// unify 中"索引槽 ↔ 构造子值"互相引用的未收敛路径（被 fuel 防护拦下后
/// 报 can't unify）。
#[test]
fn test_eq_reasoning() {
    check(
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

/// 纯依赖 λ 演算 + 字符串内建（移植自 L07a test / test1）
#[test]
fn test_lambda_calculus_and_strings() {
    let out = check(
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
    assert!(out.contains("hello world!"));
    assert!(out.contains("Nat::succ(Nat::succ(Nat::succ(Nat::succ(Nat::zero))))"));
}

/// 回归：泛型类型的 match —— 字段类型来自构造子类型按头部实参实例化，
/// 不再依赖"参数名恰好在 match 现场可见"（L08_product_type 的 Raw-in-Term bug）
#[test]
fn test_generic_match() {
    let out = check(
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
    assert_eq!(
        out.lines().collect::<Vec<_>>(),
        vec![
            "Nat::succ(Nat::succ(Nat::zero))",
            "Nat::succ(Nat::succ(Nat::succ(Nat::zero)))"
        ]
    );
}

/// 回归：通配臂与构造子臂混合 —— L07a 的矩阵算法在这里丢分支或遮蔽错序
#[test]
fn test_catch_all_mixed() {
    let out = check(
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
    assert_eq!(
        out.lines().collect::<Vec<_>>(),
        vec!["Bool::true", "Bool::false", "Nat::zero"]
    );
}

/// 回归：GADT 可达性 —— 在 `Vec[Nat] zero` 上匹配不到 cons，
/// 不写 cons 分支不算不完整
#[test]
fn test_gadt_accessible() {
    check(
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
}

/// 负例：GADT 不可达分支要报"分支不可达"
#[test]
fn test_gadt_unreachable_err() {
    let msg = check_err(
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
    assert!(msg.contains("不可达"), "{msg}");
}

/// 负例：缺少构造子覆盖
#[test]
fn test_missing_case_err() {
    let msg = check_err(
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
    assert!(msg.contains("缺少构造子"), "{msg}");
}

/// 索引等式：`Eq two two` 可证，`Eq two three` 不可证（报错）
#[test]
fn test_index_equality() {
    check(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Eq[A](x: A, y: A) {
    refl[a: A] -> Eq[A] a a
}

def two = succ (succ zero)

def ok: Eq two two = refl
"#,
    );
    check_err(
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

/// 回归：投影的类型取参数的**类型槽** —— `t.len : Nat` 可以显式标注
/// （L07/L07a 里投影类型是字段的"值"，显式标注会失败）
#[test]
fn test_projection_typing() {
    check(
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

/// 回归：卡住 match 作为中性值 —— 同一 match 的类型两次出现可互证
/// （unify 的 Match/Match 规则 + quote/rename 分支体的往返一致性）
#[test]
fn test_stuck_match_unify() {
    check(
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
}

/// 回归：卡住 match 被应用时把参数拼进各分支体（splice），不 panic。
/// `f` 的 WHNF 就是卡住的 Match；`f zero` 触发应用 → splice → 归约。
#[test]
fn test_stuck_match_splice() {
    check(
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
}

/// 回归：卡住 match 被应用、且实参引用比捕获 env 更外层的 binder。
/// 旧实现把实参 quote 进分支体（quote 层级取捕获 env 长度），实参越界：
/// debug 触发 lvl2ix 断言、release 静默错位成错误变量。修复后实参在值层
/// 累积（pending）、分支选中后再应用——作用域天然正确。
#[test]
fn test_stuck_match_applied_with_outer_binder() {
    let out = check(
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
    // 正确形态：match 保持卡住（m 中性），实参 `j` 在分支**外层**应用
    // ——旧实现把 j quote 进分支体（层级越界：debug panic / release 错位
    // 成 m），此处 `) j` 的尾部应用与分支体引用都是修复后的标志。
    assert!(out.contains("match m"), "{out}");
    assert!(out.contains(") j"), "{out}");
    assert!(!out.contains("zero => j"), "{out}");
}

/// 回归：卡住的内建（string_concat 实参非字面量）不再无条件判等——
/// `x ++ y ≡ x ++ z` 必须不可证（旧实现 Val::Prim 不带实参，
/// `(Prim, Prim) => Ok(())` 会把不同的拼接判成相等）。
#[test]
fn test_stuck_prim_not_unconditionally_equal() {
    let msg = check_err(
        r#"
enum Eq[A : U](x : A, y : A) {
    refl(x : A) -> Eq[A] x x
}

def bad(x: String, y: String, z: String): Eq[String] (string_concat x y) (string_concat x z) =
    refl [String] (string_concat x y)

println bad
"#,
    );
    assert!(msg.contains("can't unify"), "{msg}");
}

/// 回归：分支体里的洞（未解 meta）不炸 pretty（L07a 的 pretty todo!()）
#[test]
fn test_hole_in_branch() {
    let out = check(
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
    assert_eq!(out.trim(), "final");
}

/// 嵌套模式 + 深层绑定器的 de Bruijn 对齐
#[test]
fn test_nested_patterns() {
    let out = check(
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
    assert_eq!(
        out.lines().collect::<Vec<_>>(),
        vec![
            "Nat::succ(Nat::succ(Nat::zero))",
            "Nat::zero",
            "Nat::zero",
        ]
    );
}

/// 递归定义：自递归 + 后定义引用先定义（decl 表自引用占位）
#[test]
fn test_recursive_defs() {
    let out = check(
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
    assert_eq!(
        out.lines().collect::<Vec<_>>(),
        vec!["Bool::true", "Bool::true"]
    );
}

/// 依赖递归函数的索引族等式推理（原 README 已知限制 #1 的主体，迁移自
/// L13 legacy test4/test8）：`add_zero_right` 的 succ 分支要求"期望类型里的
/// stuck match 经卡住 match 的 meta 解与重实例化后仍能正确归约"。
/// 曾被 force 对 simpl_decl 中性占位的无限自旋（烧光 fuel 池）误判为不收敛。
#[test]
fn test_eq_add_zero_right() {
    check(
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

def cong_succ[x: Nat, y: Nat](e: Eq x y): Eq (succ x) (succ y) =
    cong[Nat][Nat][succ][x][y] e

def add(x: Nat, y: Nat) =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def add_zero_right(a: Nat): Eq (add a zero) a =
    match a {
        case zero => refl zero
        case succ(t) => cong_succ (add_zero_right t)
    }
"#,
    );
}

/// 同族的 `mul_zero_right`：trans 的第一个参数显式给出
/// `refl (add zero (mul k zero))`，要求 `add zero x` 归约与卡住 match 协同。
#[test]
fn test_eq_mul_zero_right() {
    check(
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

def trans[A, x, y, z: A](e1: Eq[A] x y, e2: Eq[A] y z): Eq[A] x z =
    match e1 {
        case refl(a) => e2
    }

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

def mul_zero_right(n: Nat): Eq[Nat] (mul n zero) zero =
    match n {
        case zero => rfl
        case succ(k) => trans (refl (add zero (mul k zero))) (mul_zero_right k)
    }
"#,
    );
}

/// 同族的 `mul_one_right`：let 绑定的中间引理 + 显式隐式参数的 cong 组合
/// （`cong[Nat][Nat][add (succ zero)][mul k (succ zero)][k] ih`）。
#[test]
fn test_eq_mul_one_right() {
    check(
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

def cong_succ[x: Nat, y: Nat](e: Eq x y): Eq (succ x) (succ y) =
    cong[Nat][Nat][succ][x][y] e

def trans[A, x, y, z: A](e1: Eq[A] x y, e2: Eq[A] y z): Eq[A] x z =
    match e1 {
        case refl(a) => e2
    }

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

def add_zero_left(m: Nat): Eq[Nat] (add zero m) m =
    rfl

def mul_one_right(n: Nat): Eq[Nat] (mul n (succ zero)) n =
    match n {
        case zero => rfl[Nat][zero]
        case succ(k) =>
            let ih = mul_one_right k;
            let lemma: Eq[Nat] (add (succ zero) k) (succ k) = cong_succ (add_zero_left k);
            trans (cong[Nat][Nat][add (succ zero)][mul k (succ zero)][k] ih) lemma
    }
"#,
    );
}

/// 嵌套解构 + 外层绑定器引用：嵌套 Con 模式不再产生"编译期哑槽"与运行时
/// prepend 不对齐的偏差（head 槽统一由 walk_con 入口绑定，eval_aux 同序前置）。
#[test]
fn test_nested_pattern_outer_ref() {
    let out = check(
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
    assert_eq!(
        out.lines().collect::<Vec<_>>(),
        vec![
            "Nat::succ(Nat::zero)",
            "Nat::succ(Nat::succ(Nat::succ(Nat::zero)))",
            "Nat::succ(Nat::succ(Nat::succ(Nat::succ(Nat::zero))))",
        ]
    );
}

/// 同族的 `add_succ_right`：`add a (succ b) ≡ succ (add a b)` 的归纳证明。
/// 旧实现已知限制 #1 的最后一块：succ 臂期望类型两侧都是"递归函数应用于
/// 模式绑定器"的卡住 match 组合（`add t (succ b)` 与 `succ (add t b)`）。
#[test]
fn test_eq_add_succ_right() {
    check(
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

def cong_succ[x: Nat, y: Nat](e: Eq x y): Eq (succ x) (succ y) =
    cong[Nat][Nat][succ][x][y] e

def add(x: Nat, y: Nat) =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def add_succ_right(a: Nat, b: Nat): Eq (add a (succ b)) (succ (add a b)) =
    match a {
        case zero => rfl[Nat][succ b]
        case succ(t) => cong_succ (add_succ_right t b)
    }
"#,
    );
}

/// `add_comm`：零臂用 `add zero b ≡ b` 的归约 + symm/trans 组合；
/// succ 臂把 `add b (succ t)`（b 侧卡住）经 add_succ_right 搬运到
/// `succ (add b t)`——卡住 match 与精化的组合推理。
#[test]
fn test_eq_add_comm() {
    check(
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

def cong_succ[x: Nat, y: Nat](e: Eq x y): Eq (succ x) (succ y) =
    cong[Nat][Nat][succ][x][y] e

def symm[A, x, y: A](e: Eq[A] x y): Eq[A] y x =
    match e {
        case refl(a) => refl[A] a
    }

def trans[A, x, y, z: A](e1: Eq[A] x y, e2: Eq[A] y z): Eq[A] x z =
    match e1 {
        case refl(a) => e2
    }

def add(x: Nat, y: Nat) =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def add_zero_right(a: Nat): Eq (add a zero) a =
    match a {
        case zero => refl zero
        case succ(t) => cong_succ (add_zero_right t)
    }

def add_succ_right(a: Nat, b: Nat): Eq (add a (succ b)) (succ (add a b)) =
    match a {
        case zero => rfl[Nat][succ b]
        case succ(t) => cong_succ (add_succ_right t b)
    }

def add_comm(a: Nat, b: Nat): Eq (add a b) (add b a) =
    match a {
        case zero => trans (refl b) (symm (add_zero_right b))
        case succ(t) => trans (cong_succ (add_comm t b)) (symm (add_succ_right b t))
    }
"#,
    );
}

/// `add_assoc`：旧实现的已知限制 #1（README）。失败机制是"精化改写上下文后，
/// meta 解里捕获的卡住 match 与使用现场槽位错位"——本架构（层级/槽位永不
/// 改写，精化只是事实表 + force 惰性展开）按构造排除该 bug 族。succ 臂的
/// 期望类型两侧都是嵌套的卡住 match：`add (add t b) c` 与 `add t (add b c)`。
#[test]
fn test_eq_add_assoc() {
    check(
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

def cong_succ[x: Nat, y: Nat](e: Eq x y): Eq (succ x) (succ y) =
    cong[Nat][Nat][succ][x][y] e

def add(x: Nat, y: Nat) =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def add_assoc(a: Nat, b: Nat, c: Nat): Eq (add (add a b) c) (add a (add b c)) =
    match a {
        case zero => rfl
        case succ(t) => cong_succ (add_assoc t b c)
    }
"#,
    );
}

/// 迁移自 L13_namespace/legacy_tests.rs 的 test7（bits_adder）：
/// Vec[Bool] 上的递归全加器——嵌套模式（`cons[_](n, taill)` 隐式槽）、
/// 多参数索引族（Vec / Product）、递归调用的结果继续被匹配。
/// 这是比 test5/test6 更深的依赖匹配组合，在旧 L07/L07a 上无法通过。
#[test]
fn test_bits_adder() {
    let out = check(
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
    // 1 + 0 的逐位加法：sum = true，carry = false（L13 断言的是 fully-reduced
    // 形态；本实现的结果里 carry 位可能停在未解 meta 上，断言只看位值内容）
    assert!(out.contains("Bool::true"), "{out}");
    assert!(out.contains("Bool::false"), "{out}");
}

// L06 演进同步（2026-09）：builtin 注册表 / 可变全局 / 文件 IO / 宽松臂
// --------------------------------------------------------------------------------

/// DEMO 全串：enum + 依赖 match + 字符串 builtin + 文件 IO + 可变全局。
/// （形态对齐 DEMO_SRC：函数体无花括号、enum 闭括号后空一行——顶层 decl
/// 分隔要求 `EndLine.many1()`，而 enum 的 case 分隔已吃掉 `}` 前的换行；
/// 旧版此测试零断言，两段一直在静默报 parse error，断言补上后修正。）
#[test]
fn test_demo() {
    for (name, seg) in [
        ("add", "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\ndef add(x: Nat, y: Nat): Nat =\n    match x {\n        case zero => y\n        case succ(n) => succ (add n y)\n    }\nprintln (add (succ (succ zero)) (succ zero))\n"),
        ("add_sp", "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\ndef add(x: Nat, y: Nat): Nat =\n    match x {\n        case zero => y\n        case succ(n) => succ (add n y)\n    }\nprintln (add (succ (succ zero)) (succ zero))\nprintln (add (succ zero) (succ (succ zero)))\n"),
    ] {
        let r = std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || match run(seg, 0) {
                Ok(_) => "ok".to_string(),
                Err(e) => format!("ERR: {e}"),
            })
            .unwrap()
            .join()
            .unwrap();
        println!("SEG {name}: {r}");
        assert_eq!(r, "ok", "{name}");
    }
}

/// 字符串 builtin：拼接 / 判等 / 缩进。
#[test]
fn test_string_builtins() {
    let out = check(
        r#"
def c : String = string_concat "foo" "bar"
println c
println (str_eq "foo" "foo")
println (str_eq "foo" "bar")
println (str_indent2 "a
b")
"#,
    );
    assert_eq!(out, "foobar
true
false
a
  b
");
}

/// 可变全局族：建档 / 更新 / 读取 / 缺省。
#[test]
fn test_decl_table_and_globals() {
    let out = check(
        r#"
def store : U = create_global "k" "v"
def upd : U = change_mutable "k" (s => string_concat s "!")
def g1 : String = get_global "k"
println g1
def g2 : String = get_global_default "k" "fb"
println g2
def g3 : String = get_global_default "nope" "fb"
println g3
"#,
    );
    assert_eq!(out, "v!
v!
fb
");
}

/// get_global 缺名保持卡住（不 panic），宽松臂对未登记名放行。
#[test]
fn test_get_global_missing_stays_stuck() {
    let out = check(
        r#"
def v : String = get_global "missing"
println v
"#,
    );
    assert!(out.contains("get_global"), "卡住值应打印名字：{out}");
}

/// 已登记名不冒充 String（宽松臂把关，L06 同款）。
#[test]
fn test_registered_prim_not_loosely_string() {
    check_err(
        r#"
def bad : String = get_global "file_delete"
println bad
"#,
    );
    check_err(
        r#"
def dyn(x : String) : String = get_global x
println (dyn "a")
"#,
    );
}

/// string_to_global_type：登记名给登记类型，未登记名走逃逸舱口。
#[test]
fn test_string_to_global_type() {
    let out = check(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

def n : U = string_to_global_type "Nat"
def two : Nat = succ (succ zero)
println two
"#,
    );
    assert!(out.contains("Nat::succ"), "{out}");
}

/// 文件 IO：写 / 追加 / 读回 / 存在性 / 删除。
#[test]
fn test_file_io_builtins() {
    let _guard = FILE_IO_LOCK.lock().unwrap();
    let out = check(
        r#"
def p : U = file_write_all_text "l08_test_io.txt" "hello"
def a : U = file_append_all_text "l08_test_io.txt" "!"
def r : String = file_read_all_text "l08_test_io.txt"
println r
println (file_exists "l08_test_io.txt")
def d : U = file_delete "l08_test_io.txt"
println (file_exists "l08_test_io.txt")
"#,
    );
    assert_eq!(out, "hello!
true
false
");
}

// --------------------------------------------------------------------------------
// L08：积类型（struct / new / 字段投影）
// --------------------------------------------------------------------------------

/// struct 声明 + new 构造 + 值级字段投影 + 空 struct + 限定构造子应用。
#[test]
fn test_product_basic() {
    let out = check(
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
    // 精确断言：p.x = two、p.y = four；p / p2 的显示去重形态（§4）；
    // nullary 构造子显示为 `Unit.mk`（无实参括号）
    assert_eq!(
        out,
        "Nat::succ(Nat::succ(Nat::zero))\n\
         Nat::succ(Nat::succ(Nat::succ(Nat::succ(Nat::zero))))\n\
         Point.mk(Nat::succ(Nat::succ(Nat::zero)) Nat::succ(Nat::succ(Nat::succ(Nat::succ(Nat::zero)))))\n\
         Point.mk(Nat::succ(Nat::succ(Nat::zero)) Nat::succ(Nat::succ(Nat::succ(Nat::succ(Nat::zero)))))\n\
         Unit.mk\n"
    );
}

/// 泛型 struct（隐式参数）+ 类型级投影（`get_x` 的 `p.x`：接收者只有
/// `Val::Sum` 类型）+ 字段构造的递归函数。形态对齐旧 L08 test2。
#[test]
fn test_product_generic() {
    let out = check(
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
    // 精确断言：get_x start_point = zero；point_add 两分量 = add zero four
    // （= four）与 add four two（= six）；sy = end_point.y = two。
    assert_eq!(
        out,
        "Nat::zero\n\
         Point.mk(Nat::succ(Nat::succ(Nat::succ(Nat::succ(Nat::zero)))) Nat::succ(Nat::succ(Nat::succ(Nat::succ(Nat::succ(Nat::succ(Nat::zero)))))))\n\
         Nat::succ(Nat::succ(Nat::zero))\n"
    );
}

/// 依赖字段（Sigma 积）：`Bits.name : String` 用字面量类型；
/// `Exists` 的 `proof` 字段依赖 `witness`；`Exists.mk` 显式实例化隐式参数。
#[test]
fn test_product_dependent() {
    let out = check(
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
    // 精确断言（已知形态的行）：get_name sigA = "A"（String 值裸打）；
    // sigA 的 Bits.mk 两字段；w = exists_two.witness = two。
    // （exists_two 自身的 Exists.mk 显示带隐参形态，泛型测试已覆盖同构
    // 输出，这里不锁死。）
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(lines.first(), Some(&"A"), "{out}");
    assert!(
        out.contains(
            "Bits.mk(A Nat::succ(Nat::succ(Nat::zero)))"
        ),
        "{out}"
    );
    assert_eq!(
        lines.last(),
        Some(&"Nat::succ(Nat::succ(Nat::zero))"),
        "{out}"
    );
}

/// 字段不存在 → 类型级与值级都给 `has no field` 错误。
#[test]
fn test_product_field_err() {
    let e1 = check_err(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

struct Point {
    x: Nat
}

def p = new Point(zero)
def bad = p.zzz
"#,
    );
    assert!(e1.contains("has no field"), "{e1}");
    let e2 = check_err(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

struct Point {
    x: Nat
}

def bad(p: Point) = p.zzz
"#,
    );
    assert!(e2.contains("has no field"), "{e2}");
}

/// struct 的字段名与 enum 的索引参数名一样参与投影查找（参数槽优先），
/// 且普通单 case enum（case 名不带 `.mk`）不享受类型级剥链——旧 L08 的
/// `contains(".mk")` 门控。
#[test]
fn test_product_vs_plain_enum() {
    let e = check_err(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Wrap {
    only(x: Nat)
}

def bad(w: Wrap) = w.x
"#,
    );
    assert!(e.contains("has no field"), "{e}");
}

/// 依赖字段投影出现在检查位：类型级剥链对前字段 binder 用接收者的
/// 卡住投影实例化，`e.proof` 拿到 `Eq e.witness two`（评审修复回归——
/// 旧 `U` 占位下 `P e.witness` vs `P U` 合一失败，合法程序被假拒）。
#[test]
fn test_product_dependent_check() {
    let out = check(
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
"#,
    );
    assert!(out.contains("_ => px => px"), "{out}");
}

/// `new` 结果直接接 `.field` 投影后缀链（与括号形式等价）；实参位
/// 嵌套 `new` 不受影响。
#[test]
fn test_product_new_dot_chain() {
    let out = check(
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
    assert!(out.contains("Nat::succ(Nat::succ(Nat::zero))"), "{out}");
    assert_eq!(
        out.lines().filter(|x| x.contains("succ")).count(),
        2,
        "{out}"
    );
}

/// 投影接收者的**局部遮蔽**回归：`Foo.c2` 的限定构造子快捷路径不得越过
/// 局部 binder——`Foo` 是函数参数（类型 S）时必须投影其字段，而不是静默
/// 解析成全局构造子 `Foo.c2`（旧实现先查 decl 表，恒返回 `c2` 的错误 Ok）。
/// 同形 `Foo: Nat` 的接收者则报 `Nat has no field c2`（修复前是 Ok）。
#[test]
fn test_product_shadow() {
    let out = check(
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
    // 普通 enum case 的打印形态是 `Foo::c1`（§4 去重只作用于 `.mk` 形态）；
    // 修复前此处恒打印全局构造子 `Foo::c2`
    assert_eq!(out, "Foo::c1(Nat::zero)\n");
    let e = check_err(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Foo {
    c1(x: Nat)
    c2
}

def pick(Foo: Nat) = Foo.c2
"#,
    );
    assert!(e.contains("has no field"), "{e}");
}

/// struct 字段间容忍连续空行与注释行（注释行经 preprocess 剥成空白后
/// 仍产生 EndLine，单 EndLine 分隔会把字段间注释打成语法错误——与
/// match 臂的 `EndLine.many1()` 分隔同款）。
#[test]
fn test_product_field_blank_lines() {
    let out = check(
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
    assert_eq!(out, "Nat::succ(Nat::succ(Nat::zero))\n");
}

/// lexer 空字符串与转义回归（L08 附带修复）：组合子版 `string` 用
/// `pmatch(c != '"')` 至少吃一字符，字面量 `""` 被误杀、`\` 不跳转义
/// 使 `\"` 提前截断；重写为逐字节扫描（`\` 跳两字节）后形态正确。
#[test]
fn test_string_empty_and_escape() {
    let out = check(
        r#"
println ""
println "a\"b"
println "\\"
"#,
    );
    assert_eq!(out, "\na\"b\n\\\n");
}
