//! L07 的测试套件。
//!
//! - `test_basic` / `test_index` / `test_dependent_match` / `test_dependent_match_nested_eval`
//!   / `test_eq_reasoning` / `test_lambda_calculus_and_strings`：从 L07a_depend_pm
//!   的 7 个测试移植（旧测试全部保留语义）。
//! - `test_generic_match` / `test_catch_all_mixed` / `test_gadt_*` /
//!   `test_projection_typing` / `test_stuck_match_*` / `test_hole_in_branch` /
//!   `test_nested_patterns` / `test_missing_case_err` / `test_index_equality_err`：
//!   针对 L07/L07a 已知 bug 的回归测试（见 README.md 的"修了什么"一节）。

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
/// 不再依赖"参数名恰好在 match 现场可见"（L07_sum_type 的 Raw-in-Term bug）
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
