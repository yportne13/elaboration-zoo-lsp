//! L07 的测试套件。
//!
//! - `test_basic` / `test_index` / `test_dependent_match` / `test_dependent_match_nested_eval`
//!   / `test_eq_reasoning` / `test_lambda_calculus_and_strings`：从 L07a_depend_pm
//!   移植（旧测试全部保留语义）。
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
/// 依赖递归扩展即本文件后半的 `test_eq_add_*` / `test_eq_reasoning_*`
/// 全家（README §6 的修复表）。
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

def NatC : U =
    (N : U) -> (N -> N) -> N -> N
def mul : NatC -> NatC -> NatC =
    a => b => N => s => z => a _ (b _ s) z
def ten : NatC =
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

"#,
    );
    assert_eq!(
        out.lines().collect::<Vec<_>>(),
        vec!["Bool::true", "Bool::false"]
    );
}

/// 负例（owner 2026-09-20 口径）：通配臂之后的臂运行时永不可达 → 报「分支不可达」。
/// 此前该形态是**静默跳过**（本测试的前身 `const_zero` 就钉着"接受"），
/// 口径改为报错后由本钉子接替。
#[test]
fn test_shadowed_arm_err() {
    let msg = check_err(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

def const_zero(x: Nat): Nat =
    match x {
        case n => zero
        case zero => zero
        case succ(k) => succ k
    }
"#,
    );
    assert!(msg.contains("分支不可达"), "{msg}");
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

/// DEMO 全串：enum + 依赖 match + 字符串 builtin + 文件 IO + 可变全局
/// （参考版整段跑通并断言 Ok；Ok 输出双实现对拍见
/// tests/l07_fast_parity.rs::parity_demo_src）。
#[test]
fn test_demo() {
    let _guard = FILE_IO_LOCK.lock().unwrap();
    let r = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || run(DEMO_SRC, 0).map(|_| ()))
        .unwrap()
        .join()
        .unwrap();
    assert!(r.is_ok(), "DEMO_SRC 应整段跑通：{:?}", r);
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
def p : U = file_write_all_text "l07_test_io.txt" "hello"
def a : U = file_append_all_text "l07_test_io.txt" "!"
def r : String = file_read_all_text "l07_test_io.txt"
println r
println (file_exists "l07_test_io.txt")
def d : U = file_delete "l07_test_io.txt"
println (file_exists "l07_test_io.txt")
"#,
    );
    assert_eq!(out, "hello!
true
false
");
}

// 显式替换重构（2026-09，dpm-nbe 对齐）的直接单测：Subst 链语义 /
// force_arg 多层解包 / struct_eq 的 VSub 分支。机制层回归——run 级行为
// 由上方用例与 l07_fast_parity 双 oracle 覆盖。

/// Subst 持久化链：沿链取最新（≙ 旧 pm_def 的 rev().find）、未命中回
/// vvar、compose 外层覆盖、extend 不影响既有链（臂边界 Rc 回滚的前提）。
#[test]
fn subst_chain_semantics() {
    let s0: std::rc::Rc<Subst> = std::rc::Rc::new(Subst::default());
    assert!(s0.is_empty());

    let s1 = Subst::extend(&s0, Lvl(5), Val::vvar(Lvl(1)));
    assert!(s1.has(Lvl(5)));
    assert!(struct_eq::val_eq(&s1.lookup(Lvl(5)), &Val::vvar(Lvl(1))));
    // 未命中 = 恒等延拓
    assert!(struct_eq::val_eq(&s1.lookup(Lvl(9)), &Val::vvar(Lvl(9))));

    // 同键再解：链头（最新）胜
    let s2 = Subst::extend(&s1, Lvl(5), Val::vvar(Lvl(2)));
    assert!(struct_eq::val_eq(&s2.lookup(Lvl(5)), &Val::vvar(Lvl(2))));
    // 旧链不受 extend 影响（Rc 共享）
    assert!(struct_eq::val_eq(&s1.lookup(Lvl(5)), &Val::vvar(Lvl(1))));

    // compose：外层（后应用）条目覆盖内层同键
    let outer = Subst::extend(&s0, Lvl(5), Val::vvar(Lvl(3)));
    let comp = Subst::compose(&outer, &s1);
    assert!(struct_eq::val_eq(&comp.lookup(Lvl(5)), &Val::vvar(Lvl(3))));
}

/// lookup 命中的包裹判据：解值引用已解层级 ⇒ 包 VSub(·, σ)（读点推开）；
/// 干净解值 ⇒ 原样返回（零分配零 fuel 的热路径）。
#[test]
fn subst_lookup_conditional_wrap() {
    let s0: std::rc::Rc<Subst> = std::rc::Rc::new(Subst::default());
    let s1 = Subst::extend(&s0, Lvl(3), Val::vvar(Lvl(30)));
    // 1 := Rigid(3)：解值引用已解层级 3 ⇒ 包裹
    let s2 = Subst::extend(&s1, Lvl(1), Val::vvar(Lvl(3)));
    match s2.lookup(Lvl(1)) {
        Val::VSub(v, sub) => {
            // 包裹携带的是整条 σ（后解的 3 := 30 借此对先解的 1 生效）
            assert!(std::rc::Rc::ptr_eq(&sub, &s2), "VSub must carry the full subst");
            assert!(struct_eq::val_eq(&v, &Val::vvar(Lvl(3))));
        }
        other => panic!("expected VSub, got {other:?}"),
    }
    // 1 := U：解值干净 ⇒ 原样
    let s3 = Subst::extend(&s1, Lvl(1), Val::U);
    assert!(matches!(s3.lookup(Lvl(1)), Val::U));
    // 1 := Rigid(7)：7 未解 ⇒ 原样（精化传播不需要 σ）
    let s4 = Subst::extend(&s1, Lvl(1), Val::vvar(Lvl(7)));
    assert!(struct_eq::val_eq(&s4.lookup(Lvl(1)), &Val::vvar(Lvl(7))));
    // 解值引用藏在**闭包 env 槽**里（mentions_level 区别于 val_mentions_lvl
    // 的分界情形）：λ 捕获 env 引用已解层级 3 ⇒ 也要包裹
    let lam = Val::Lam(
        empty_span("a".to_owned()),
        Icit::Expl,
        Closure(List::new().prepend(Val::vvar(Lvl(3))), Rc::new(Tm::Var(Ix(0)))),
    );
    let s5 = Subst::extend(&s1, Lvl(1), lam);
    assert!(matches!(s5.lookup(Lvl(1)), Val::VSub(..)));
}

/// force_arg 逐层解包：嵌套 match 的上下文被外层臂与内层臂各 subst_cxt
/// 一次，槽位带两层 VSub——invert/prune 需要看的是裸 rigid 槽位。
#[test]
fn force_arg_unwraps_nested_vsub() {
    let infer = Infer::new();
    let decl = cxt::Decls::new();
    let inner: std::rc::Rc<Subst> = std::rc::Rc::new(Subst::default());
    let outer = Subst::extend(&inner, Lvl(9), Val::U);
    // 两层包裹、内层是未解的裸 rigid 槽 ⇒ 解包到裸形态（pm_defs 不参与
    // invert 的旧行为等价）
    let slot = Val::VSub(Box::new(Val::vvar(Lvl(7))), outer.clone());
    let slot = Val::VSub(Box::new(slot), outer);
    match infer.force_arg(&decl, slot) {
        Val::Rigid(x, sp) => {
            assert!(sp.is_empty());
            assert_eq!(x, Lvl(7));
        }
        other => panic!("expected bare rigid slot, got {other:?}"),
    }
    // 内层是已解引用：invert 视角同样**不**推开 σ（旧"pm_defs 不参与
    // invert"等价——槽位是作用域事实，解的可见性属 force 全量视角）
    let mapped = Subst::extend(&inner, Lvl(7), Val::U);
    let slot2 = Val::VSub(Box::new(Val::vvar(Lvl(7))), mapped);
    match infer.force_arg(&decl, slot2) {
        Val::Rigid(x, sp) => {
            assert!(sp.is_empty());
            assert_eq!(x, Lvl(7));
        }
        other => panic!("expected bare rigid slot, got {other:?}"),
    }
    // 对照：全量 force 视角才推开为解值
    let slot3 = Val::VSub(Box::new(Val::vvar(Lvl(7))), Subst::extend(&inner, Lvl(7), Val::U));
    assert!(matches!(infer.force(&decl, slot3), Val::U));
}

/// struct_eq 的 VSub 分支：同一替换实例（同 Rc）且内层结构相等才短路；
/// 异实例一律 false 回落慢路径（正确性由 unify 的 force 承接）。
#[test]
fn struct_eq_vsub_pointer_identity() {
    let sub: std::rc::Rc<Subst> = std::rc::Rc::new(Subst::default());
    let a = Val::VSub(Box::new(Val::U), sub.clone());
    let b = Val::VSub(Box::new(Val::U), sub.clone());
    assert!(struct_eq::val_eq(&a, &b));
    let other = Subst::extend(&sub, Lvl(1), Val::U);
    let c = Val::VSub(Box::new(Val::U), other);
    assert!(!struct_eq::val_eq(&a, &c));
}

/// frcs 对"已解 rigid + 非空 spine"做解析应用（对齐 dpm-nbe 的 napp
/// 组合子；旧 pm_defs 版在带 spine 的 rigid 上卡住不展开）。函数类型的
/// 索引槽被特化解成 λ 后，类型位置的应用在 elaboration 期归约——本用例
/// 在新架构下通过，旧架构下 `Rigid(g,[zero])` 卡住会误报 can't unify。
/// 性能版移植必须复刻同一归约选择（l07_fast_parity 强制）。
#[test]
fn test_fn_typed_index_slot_applied_after_refine() {
    let out = check(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Foo(f: Nat -> Nat) {
    mk -> Foo (n => n)
}

def refl_e[A : U, x: A]: (P : A -> U) -> P x -> P x =
    P => px => px

def t(g: Nat -> Nat, w: Foo g): (P : Nat -> U) -> P (g zero) -> P zero =
    match w {
        case mk => refl_e
    }
"#,
    );
    assert!(out.is_empty(), "{out}");
}

/// 深嵌套模式的 fuel 预算边界回归：d=400 的逐层 cons 嵌套 + 通配兜底。
/// 显式替换初版把"每次 VSub 推开"都计 1 fuel，燃烧剖面劣化使默认 4096
/// 池在 d≈380 耗尽、被误报"分支不可达"（假 absurd）；燃烧点移到 lookup
/// 命中后剖面与旧 pm_defs 对齐（旧版 d=2000 仍在预算内）。d=400 为
/// 修复前的确定性失败点。512 MB 栈（走查递归深度 × walk_con 帧较大）。
#[test]
fn test_deep_pattern_fuel_budget_regression() {
    let depth = 400usize;
    let mut big = "nil".to_owned();
    for i in 0..depth {
        let elem = if i + 1 == depth { "succ zero" } else { "zero" };
        big = format!("cons ({elem}) ({big})");
    }
    let mut pat = "nil".to_owned();
    for i in (0..depth).rev() {
        pat = format!("cons(h{i}, {pat})");
    }
    let src = format!(
        "{NAT}{VEC}
def big = {big}

def f[n: Nat](v: Vec[Nat] n): Nat =
    match v {{
        case {pat} => h0
        case _ => zero
    }}

println (f big)
",
        NAT = r#"enum Nat {
    zero
    succ(x: Nat)
}

"#,
        VEC = r#"enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

"#,
    );
    let src = src.to_owned();
    let out = std::thread::Builder::new()
        .stack_size(512 * 1024 * 1024)
        .spawn(move || run(&src, 0).unwrap_or_else(|e| panic!("check failed: {e:?}")))
        .unwrap()
        .join()
        .unwrap();
    assert_eq!(out.lines().next(), Some("Nat::succ(Nat::zero)"));
}

/// README §7.6 回归钉（2026-09-18）：深值（succ^N 链）上的 occurs 守卫与
/// 结构相等全部迭代化——**默认测试栈**（约 2 MB，正是“常规栈 1–8 MB”的
/// 下界）下不再爆栈（旧递归版在 ~万级深度爆栈）。深链的 Rc/Drop 自身是
/// 深递归（测试基建的坑，非被测代码），故 ManuallyDrop 泄漏给进程。
#[test]
fn deep_value_iterative_under_default_stack() {
    const N_OCCURS: usize = 100_000;
    const N_EQ: usize = 4_000;

    fn nat_sum() -> Val {
        Val::Sum(
            empty_span("Nat".to_string()),
            vec![],
            vec![
                empty_span("zero".to_string()),
                empty_span("succ".to_string()),
            ],
        )
    }
    fn succ_of(typ: &std::rc::Rc<Val>, prev: Val) -> Val {
        Val::SumCase {
            typ: std::rc::Rc::clone(typ),
            case_name: empty_span("succ".to_string()),
            datas: vec![(empty_span("x".to_string()), std::rc::Rc::new(prev), Icit::Expl)],
        }
    }
    fn chain(nat: &std::rc::Rc<Val>, n: usize) -> Val {
        let mut v = Val::SumCase {
            typ: std::rc::Rc::clone(nat),
            case_name: empty_span("zero".to_string()),
            datas: vec![],
        };
        for _ in 0..n {
            v = succ_of(nat, v);
        }
        v
    }

    let nat = std::rc::Rc::new(nat_sum());
    // ① occurs 守卫：10 万层深链（无预算，纯遍历）
    let deep = std::mem::ManuallyDrop::new(chain(&nat, N_OCCURS));
    assert!(
        !val_mentions_lvl(&deep, Lvl(1)),
        "深链不含 Lvl(1)（且旧递归版此处爆栈）"
    );
    // 链中段嵌 Rigid(7)：命中为 true、别处为 false
    let mut with_rigid = Val::vvar(Lvl(7));
    for _ in 0..N_OCCURS / 2 {
        with_rigid = succ_of(&nat, with_rigid);
    }
    let with_rigid = std::mem::ManuallyDrop::new(with_rigid);
    assert!(val_mentions_lvl(&with_rigid, Lvl(7)));
    assert!(!val_mentions_lvl(&with_rigid, Lvl(1)));

    // ② 结构相等：预算内同构链判等；超预算（10 万层 > EQ_BUDGET 2 万）
    // 有界降级为 false——两者都不爆栈
    let a = std::mem::ManuallyDrop::new(chain(&nat, N_EQ));
    let b = std::mem::ManuallyDrop::new(chain(&nat, N_EQ));
    assert!(struct_eq::val_eq(&a, &b), "同构深链应判等（预算内）");
    let c = std::mem::ManuallyDrop::new(chain(&nat, N_OCCURS));
    assert!(
        !struct_eq::val_eq(&deep, &c),
        "超预算应有界降级（false），不爆栈"
    );
}

// --------------------------------------------------------------------------------
// 2026-09-18 评审回归钉（四角度评审 + 修复轮）：
// 嵌套覆盖检查 / stale-solvable 臂序污染 / 构造子良构性。

/// P0（嵌套覆盖缺失）：nil 臂 + cons(h, nil) 臂缺 cons(h, cons(..))——
/// 修复前静默接受、运行期在尾部为 cons 的值上卡住；修复后报模式位置缺失。
#[test]
fn test_nested_coverage_gap() {
    let msg = check_err(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

def f(x: List[Nat]): Nat =
    match x {
        case nil => zero
        case cons(h, nil) => h
    }
"#,
    );
    assert!(msg.contains("缺少构造子 cons"), "{msg}");
}

/// P0（嵌套覆盖缺失，三层）：深度 2 的嵌套位置缺 cons。
#[test]
fn test_nested_coverage_gap3() {
    let msg = check_err(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

def f(x: List[Nat]): Nat =
    match x {
        case nil => zero
        case cons(h, nil) => h
        case cons(h, cons(h2, nil)) => h2
    }
"#,
    );
    assert!(msg.contains("缺少构造子 cons"), "{msg}");
}

/// P1（stale-solvable 臂序污染）：big 臂（5 槽）在前时，其陈旧可解条目
/// 让后续 ident 荒谬臂的瞬态 η 被误判可解——修复前静默接受（臂序依赖），
/// 修复后两种臂序一致报"分支不可达"。
#[test]
fn test_stale_solvable_order_independent() {
    for arms in [
        "case big(a, b, c, d) => a\n        case ident => zero\n        case mk => succ zero",
        "case ident => zero\n        case big(a, b, c, d) => a\n        case mk => succ zero",
    ] {
        let src = format!(
            r#"
enum Nat {{
    zero
    succ(x: Nat)
}}

enum W(f: Nat -> Nat) {{
    big(a: Nat, b: Nat, c: Nat, d: Nat) -> W (n => succ zero)
    mk -> W (n => succ zero)
    ident -> W (n => n)
}}

def t(w: W (n => succ zero)): Nat =
    match w {{
        {arms}
    }}
"#
        );
        let msg = check_err(&src);
        assert!(msg.contains("分支不可达"), "{msg}");
    }
}

/// P1（构造子良构性）：ret 不是本 enum——c -> Nat 向构造子名字空间注入
/// phantom 值（对 Nat 的覆盖完备 match 在该值上卡死），修复后注册期拒绝。
#[test]
fn test_ctor_wf_external_ret() {
    let msg = check_err(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Foo {
    c -> Nat
}
"#,
    );
    assert!(msg.contains("不是 Foo"), "{msg}");
}

/// P1（构造子良构性）：参数位特化——隐式参数位是 Bool 而非参数变量，
/// 修复后拒绝（特化请走显式索引）。
#[test]
fn test_ctor_wf_param_specialized() {
    let msg = check_err(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Bool {
    true
    false
}

enum Foo[A] {
    c -> Foo[Bool]
}
"#,
    );
    assert!(msg.contains("参数变量"), "{msg}");
}
