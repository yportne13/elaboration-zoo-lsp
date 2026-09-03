//! L07_sum_type 黑盒测试套件。
//!
//! 被测对象：`src/L07_sum_type`（elaboration-zoo 07 的 Rust 移植：和类型 +
//! 依赖模式匹配，specialization by unification —— 特化合一 + 事实表惰性精化）。
//! 唯一黑盒入口：`elaboration_zoo_lsp::L07_sum_type::run(input: &str, path_id: u32)
//!   -> Result<String, Error>`。
//!
//! 黑盒契约（全部经独立探针实测确认，2026-08 版本）：
//!   - 输入是 typort 源码多语句文本；`println expr` 逐行打印求值结果；
//!   - 成功：`Ok(String)`，每行一个 pretty 值（构造子 `Enum::case(...)`、
//!     字符串原样、卡住 match 打印分支结构、meta 打印 `?m`）；
//!   - 类型/合一错误：`Err(Error)`，外部 crate 拿不到字段，断言用
//!     `format!("{:?}")`（形如 `Error("...")`）；
//!   - 语法错误：`Err(Error("parse error"))`（2026-09 起不再是 panic——
//!     解析失败的 panic 契约已改为可恢复错误）；
//!   - 测试都在 64MB 栈线程里跑（依赖匹配的精化合一递归深度远超默认 2MB）。
//!
//! 实测发现的实现特性（套件将其如实文档化）：
//!   1. 打印格式：SumCase 的隐式实参用 `[..]` 括号、显式实参空格分隔
//!      （`Vec::cons([Nat::zero] Nat::zero Vec::nil)`）；应用参数若本身是
//!      应用则打印成 `(f u)`；卡住 match 打印成 `binder => match ...`；
//!      构造子函数值 η 展开成 `x => Nat::succ(x)`。
//!   2. 投影只对 **Sum 参数**（索引）开放：`(cons two nil).len` 可用，
//!      `.x`/`.xs`（构造子数据字段）报 `Vec has no field x`；nullary
//!      构造子上任意投影报 `cannot project field ...`（README §2 的
//!      "先查索引再查字段"以实际行为为准）。
//!   3. 语法是行导向的：match 必须写在 `=` 之后的**下一行**（如所有
//!      `def f(x: T): U =` 换行 `match x { ... }`）；与 `=` 同行
//!      （`def mf = match ...`）、以及 `println (match zero {...})`
//!      内联的 match 都直接解析失败（Err("parse error")）；无期望类型的
//!      `def bad(x: Bool) =` 换行 `match ...` 反而被接受（不报错）。
//!   4. 未标注的 λ 实参应用给绑定器类型（Church 编码的 `Nat : U`）在
//!      prune_ty/prune_vflex 排序修复（2026-09）后可以正确通过——旧版
//!      误报 can't unify（多层 telescope 的剪枝掩码错位）。
//!   5. 期望类型里 match 之外创建的洞（`Eq _ _`）会被臂内约束解成含
//!      臂局部模式变量的值 → rename 作用域越界失败误报 can't unify
//!      （README「已知限制 #1」，两臂即使语义一致也报错）。
//!   6. 深度：64MB 栈下结构深度 ≤1000 的等式推理安然通过，~2000 深度
//!      即栈溢出（在解析/求值阶段，先于 4096 的 fuel 池）；运行时纯
//!      死循环（`f true` 自递归）同样表现为栈溢出而非 fuel 错误——
//!      fuel 耗尽的可黑盒触发路径未找到，深度防护以「可终止深项 +
//!      边界探针」形式覆盖。
//!   7. 预处理只用 `//` 与 `/* */`：字符串字面量里的 `//` 会被当注释
//!      剥离导致字符串截断（→ 未闭合 → 解析失败）；`/*` 会被改写为
//!      空白（`"a/*b"` 实际输出 `a  b`）。README 示例里的 `--` 注释
//!      不支持。
//!
//! 运行：`cargo test --test l07_blackbox`（探针测试需 `-- --ignored
//! --nocapture`）。

use elaboration_zoo_lsp::L07_sum_type::run;

// helpers
// --------------------------------------------------------------------------------

/// 在 64MB 栈线程里跑 `run`；期待成功，失败则 panic 并带出输出/错误。
fn check(src: &str) -> String {
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            run(&input, 0).unwrap_or_else(|e| panic!("expected ok, got Err: {e:?}\nsrc:\n{input}"))
        })
        .unwrap()
        .join()
        .unwrap()
}

/// 在 64MB 栈线程里跑 `run`；期待 Err，返回 `Debug` 文本（`Error("...")`）。
fn check_err(src: &str) -> String {
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || match run(&input, 0) {
            Err(e) => format!("{e:?}"),
            Ok(out) => panic!("expected Err, got Ok:\n{out}\nsrc:\n{input}"),
        })
        .unwrap()
        .join()
        .unwrap()
}

/// 在 64MB 栈线程里跑 `run`；返回 panic 消息（若有），Ok/Err 返回 None。
fn check_panic(src: &str) -> Option<String> {
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run(&input, 0)));
            match r {
                Ok(_) => None,
                Err(payload) => {
                    let msg = payload
                        .downcast_ref::<&str>()
                        .map(|s| s.to_string())
                        .or_else(|| payload.downcast_ref::<String>().cloned())
                        .unwrap_or_else(|| format!("{payload:?}"));
                    Some(msg)
                }
            }
        })
        .unwrap()
        .join()
        .unwrap()
}

/// 成功路径 + 逐行精确断言。
fn assert_lines(src: &str, expected: &[&str]) {
    let out = check(src);
    let got: Vec<&str> = out.lines().collect();
    assert_eq!(got, expected, "src:\n{src}\n--- actual ---\n{out}");
}

/// 错误路径 + 消息片段断言。
fn assert_err(src: &str, needle: &str) {
    let msg = check_err(src);
    assert!(msg.contains(needle), "err 缺 {needle:?}:\n{msg}\nsrc:\n{src}");
}

/// 语法错误 → Err(Error("parse error"))（2026-09 起解析失败不再 panic）。
fn assert_parse_err(src: &str) {
    let msg = check_err(src);
    assert!(
        msg.contains("parse error"),
        "expected parse error, got:\n{msg}\nsrc:\n{src}"
    );
}

/// 深度 n 的 `Nat::succ(...)` 嵌套输出文本。
fn nat_succs(n: usize) -> String {
    "Nat::succ(".repeat(n) + "Nat::zero" + &")".repeat(n)
}

/// 源码里构造深度 n 的 `succ (succ (... zero))` 项文本。
fn succ_chain(n: usize) -> String {
    "succ (".repeat(n) + "zero" + &")".repeat(n)
}

// 1. 成功路径
// --------------------------------------------------------------------------------

/// 构造子 / 字符串 / 和类型自身的打印格式（黑盒输出契约）。
///
/// 注意 `println nil`：nil 的隐式类型参数 [A] 未解，meta 按 spine 应用
/// 打印为绑定器形式 `[A] => List::nil`（同 `bb_stuck_match_splice` 里
/// 的 binder => 形式；无 meta 时才是裸 `List::nil`）。
#[test]
fn bb_output_formats() {
    assert_lines(
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

println true
println false
println zero
println (succ zero)
println (succ (succ zero))
println nil
println (cons true nil)
println (cons true (cons false nil))
println "hello world"
println Bool
"#,
        &[
            "Bool::true",
            "Bool::false",
            "Nat::zero",
            "Nat::succ(Nat::zero)",
            "Nat::succ(Nat::succ(Nat::zero))",
            "[A] => List::nil",
            "List::cons(Bool::true List::nil)",
            "List::cons(Bool::true List::cons(Bool::false List::nil))",
            "hello world",
            "Bool",
        ],
    );
}

/// 隐式类型参数 [A] 的实例化：map/not 组合，输出精确。
#[test]
fn bb_implicit_type_params() {
    assert_lines(
        r#"
enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

enum Option[T] {
    Some(t: T)
    None
}

def not(x: Bool): Bool =
    match x {
        case true => false
        case false => true
    }

def map[R, X](x: Option[R], f: R -> X): Option[X] =
    match x {
        case None => None
        case Some(t) => Some (f t)
    }

println (map (Some true) not)
println (map (Some (succ zero)) (x => x))
println (map (Some true) (x => x))
println (map None (x => x))
"#,
        &[
            "Option::Some(Bool::false)",
            "Option::Some(Nat::succ(Nat::zero))",
            "Option::Some(Bool::true)",
            "Option::None",
        ],
    );
}

/// 纯依赖 λ 演算（Church 编码）+ 字符串内建。
///
/// 注意：lambda 实参必须带 `: Nat` 标注——未标注的 λ 实参（推断类型带
/// meta）在 binder 类型是具体 Pi 的位置会报 can't unify（见
/// `bb_unannotated_lambda_arg_err`）。
#[test]
fn bb_church_and_strings() {
    assert_lines(
        r#"
def Eq[A : U](x: A, y: A): U = (P : A -> U) -> P x -> P y

def refl[A : U, x: A]: Eq[A] x x = _ => px => px

def the(A : U)(x: A): A = x

def m : U -> U -> U -> U = _

def test_free = a => b => c => the (Eq (m a b c) (m c b a)) refl

def Nat : U =
    (N : U) -> (N -> N) -> N -> N

def mul : Nat -> Nat -> Nat =
    a => b => N => s => z => a _ (b _ s) z

def two : Nat = N => s => z => s (s z)

def four = mul two two

println two
println four

def mystr = "hello world"

def add_tail(x: String): String = string_concat x "!"

println (add_tail mystr)
"#,
        &[
            "N => s => z => s (s z)",
            "N => s => z => s (s (s (s z)))",
            "hello world!",
        ],
    );
}

/// 索引族 + 构造子返回类型 + 索引投影。
#[test]
fn bb_indexed_family_projection() {
    assert_lines(
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

def head[T, L: Nat](x: Vec[T] (succ L)): T =
    match x {
        case cons(x, _) => x
    }

def length[T, l: Nat](x: Vec[T] l): Nat =
    match x {
        case nil => zero
        case cons(_, xs) => succ (xs.len)
    }

println t.len
println (cons two nil).len
println (head (cons zero nil))
println (head (cons (succ (succ zero)) nil))
println (length (cons zero (cons two nil)))
"#,
        &[
            "Nat::succ(Nat::succ(Nat::zero))",
            "Nat::succ(Nat::zero)",
            "Nat::zero",
            "Nat::succ(Nat::succ(Nat::zero))",
            "Nat::succ(Nat::succ(Nat::zero))",
        ],
    );
}

/// 依赖模式匹配的运行时行为：`t` 的具体调用输出。
/// 带隐式绑定器的构造子打印为 `ctor([隐式值] 显式值...)`。
#[test]
fn bb_dependent_match_runtime() {
    assert_lines(
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

def t[len: Nat](x: Vec[Nat] len, y: Vec[Nat] len): Vec[Nat] (succ len) =
    match x {
        case nil => cons zero nil
        case cons(x, xs) => match y {
            case cons(y, ys) => cons x (t xs ys)
        }
    }

def zero_one = t (cons zero nil) (cons two nil)

println zero_one
println (t nil nil)
"#,
        &[
            "Vec::cons([Nat::succ(Nat::zero)] Nat::zero Vec::cons([Nat::zero] Nat::zero Vec::nil))",
            "Vec::cons([Nat::zero] Nat::zero Vec::nil)",
        ],
    );
}

/// 卡住 match 是一等中性值：直接打印（binder => match 形式）、被应用
/// （splice）、归约；构造子函数值 η 展开成 λ 形式。
#[test]
fn bb_stuck_match_splice() {
    assert_lines(
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
        &[
            "n => match n { case zero => succ; case succ(k) => succ }",
            "x => Nat::succ(x)",
            "Nat::succ(Nat::zero)",
        ],
    );
}

/// 卡住 match 作为类型族 / 成员，两侧可互证。
#[test]
fn bb_stuck_match_typefamily() {
    assert_lines(
        r#"
enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
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
println (useV (succ (succ zero)) (intoV (succ (succ zero))))
"#,
        &["Bool::true", "Bool::false", "Bool::false"],
    );
}

/// 等式推理核心（cong / symm / trans）+ 具体证明的打印。
#[test]
fn bb_eq_reasoning_print() {
    assert_lines(
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

def symm[A, x, y: A](e: Eq[A] y x): Eq[A] x y =
    match e {
        case refl(a) => refl a
    }

def trans[A, x, y, z: A](e1: Eq[A] x y, e2: Eq[A] y z): Eq[A] x z =
    match e1 {
        case refl(a) => e2
    }

def two = succ (succ zero)

def three = succ (succ (succ zero))

def e1: Eq three three = cong[Nat][Nat][succ][two][two] (refl two)

def e2: Eq two two = symm[Nat][two][two] (refl two)

def e3: Eq two two = trans[Nat][two][two][two] (refl two) (refl two)

println e1
println e2
println e3
"#,
        &[
            "Eq::refl(Nat::succ(Nat::succ(Nat::succ(Nat::zero))))",
            "Eq::refl(Nat::succ(Nat::succ(Nat::zero)))",
            "Eq::refl(Nat::succ(Nat::succ(Nat::zero)))",
        ],
    );
}

/// 归纳证明：`add_comm`（等号两侧都是卡住 match 的依赖递归推理）。
#[test]
fn bb_inductive_add_comm() {
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

def symm[A, x, y: A](e: Eq[A] y x): Eq[A] x y =
    match e {
        case refl(a) => refl a
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

def two = succ (succ zero)

def prf: Eq (add two (succ zero)) (add (succ zero) two) = add_comm two (succ zero)

println "add_comm ok"
"#,
    );
}

/// 分支体里的洞（未解 meta）不炸 pretty + 顶层 `_` 洞打印。
#[test]
fn bb_hole_in_branch_and_top() {
    assert_lines(
        r#"
enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

def n: Nat = _

def f(b: Bool): Nat =
    match b {
        case true => zero
        case false => _
    }

println n
println (f true)
println "done"
"#,
        &["?0", "Nat::zero", "done"],
    );
}

/// 嵌套模式 + 深层绑定器 + 通配符子模式。
#[test]
fn bb_nested_patterns() {
    assert_lines(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

def second_or_zero(x: List[Nat]): Nat =
    match x {
        case nil => zero
        case cons(h, nil) => zero
        case cons(h, cons(h2, t)) => h2
    }

println (second_or_zero (cons (succ zero) (cons (succ (succ zero)) (cons (succ (succ (succ zero))) nil))))
println (second_or_zero (cons (succ zero) nil))
println (second_or_zero nil)
"#,
        &[
            "Nat::succ(Nat::succ(Nat::zero))",
            "Nat::zero",
            "Nat::zero",
        ],
    );
}

/// GADT 上的部分覆盖：只写可达构造子不报"不完整"；通配臂覆盖全部。
#[test]
fn bb_gadt_partial_coverage() {
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

def any(v: Vec[Nat] zero): Nat =
    match v {
        case _ => zero
    }
"#,
    );
}

/// 首匹配语义：通配臂之后的臂在运行时被跳过（编译期不报错）。
#[test]
fn bb_wildcard_first_match_wins() {
    assert_lines(
        r#"
enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

def pick(x: Nat): Nat =
    match x {
        case n => zero
        case zero => succ zero
        case succ(k) => succ k
    }

def is_zero(x: Nat): Bool =
    match x {
        case zero => true
        case other => false
    }

println (pick (succ (succ zero)))
println (pick zero)
println (is_zero zero)
println (is_zero (succ zero))
"#,
        &["Nat::zero", "Nat::zero", "Bool::true", "Bool::false"],
    );
}

/// 构造子可以作为函数值使用（`succ` 部分应用）。
#[test]
fn bb_constructor_as_function() {
    assert_lines(
        r#"
enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

def s: Nat -> Nat = succ

def two = succ (succ zero)

println (s zero)
println (s (s zero))
"#,
        &["Nat::succ(Nat::zero)", "Nat::succ(Nat::succ(Nat::zero))"],
    );
}

/// 自引用 def（指向自身的中性占位）：终止，打印名字本身。
#[test]
fn bb_self_referential_def() {
    assert_lines(
        r#"
enum Bool {
    true
    false
}

def g: Bool = g

println g
"#,
        &["g"],
    );
}

/// 深层项：1000 层嵌套 succ 的构造 / 打印 / 相等（逐字节精确）。
/// 深度边界实测：64MB 栈下 ~1500-2000 层即栈溢出（解析/求值阶段，
/// 先于 4096 的 fuel 池），见 `bb_probe_depth_sweep`。
#[test]
fn bb_deep_nat() {
    let src = format!(
        r#"
enum Nat {{
    zero
    succ(x: Nat)
}}

enum Eq[A](x: A, y: A) {{
    refl(a: A) -> Eq a a
}}

def big = {chain}

def ok: Eq big big = refl big

println big
"#,
        chain = succ_chain(1000)
    );
    let out = check(&src);
    assert_eq!(out.trim(), nat_succs(1000));
}

// 2. 错误路径
// --------------------------------------------------------------------------------

/// 覆盖缺失：缺构造子报"缺少构造子"。
#[test]
fn bb_err_missing_case() {
    assert_err(
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
        "缺少构造子",
    );
}

/// 不可达分支：索引族上不可能的模式报"不可达"。
#[test]
fn bb_err_unreachable_arm() {
    assert_err(
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
        "不可达",
    );
}

/// match 在 infer 位置被接受（不报错）——前提是能解析到该位置
/// （见 `bb_match_parse_positions`：println/无参 def 处直接解析 panic）。
#[test]
fn bb_match_infer_position_accepted() {
    check(
        r#"
enum Bool {
    true
    false
}

def bad(x: Bool) =
    match x {
        case true => false
        case false => true
    }
"#,
    );
}

/// 对非和类型（函数类型）做 match。
#[test]
fn bb_err_match_on_function() {
    assert_err(
        r#"
enum Bool {
    true
    false
}

def bad(f: Bool -> Bool): Bool =
    match f {
        case _ => true
    }
"#,
        "和类型",
    );
}

/// 模式元数错误：子模式多于构造子字段。
#[test]
fn bb_err_pattern_too_many() {
    assert_err(
        r#"
enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

def bad(x: Nat): Nat =
    match x {
        case succ(a, b) => a
    }
"#,
        "模式多了",
    );
}

/// 模式元数错误：子模式少于构造子字段。
#[test]
fn bb_err_pattern_missing_field() {
    assert_err(
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

def bad(x: List[Nat]): Nat =
    match x {
        case nil => zero
        case cons(h) => h
    }
"#,
        "缺少字段",
    );
}

/// 对 nullary 构造子给子模式。
#[test]
fn bb_err_pattern_on_nullary() {
    assert_err(
        r#"
enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

def bad(x: Nat): Nat =
    match x {
        case zero(k) => k
    }
"#,
        "模式多了",
    );
}

/// 未定义名字（前向引用同此：decl 按声明顺序处理）。
#[test]
fn bb_err_name_not_in_scope() {
    let msg = check_err(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

def bad(x: Nat): Nat = undefined_name x
"#,
    );
    assert!(
        msg.contains("undefined_name") || msg.contains("not in scope"),
        "unexpected err: {msg}"
    );
}

/// 索引等式负例：`Eq two three` 不可证。
#[test]
fn bb_err_index_mismatch() {
    assert_err(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Eq[A](x: A, y: A) {
    refl(a: A) -> Eq a a
}

def two = succ (succ zero)

def three = succ (succ (succ zero))

def bad: Eq two three = refl two
"#,
        "can't unify",
    );
}

/// 位置显式实参不能供给隐式绑定器（`rfl two`）——实测报 can't unify
/// （把 `two` 当第一个显式实参应用时类型合不上）。
#[test]
fn bb_err_positional_to_implicit_binder() {
    assert_err(
        r#"
enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

enum Eq[A](x: A, y: A) {
    refl(a: A) -> Eq a a
}

def rfl[A][a: A]: Eq a a =
    refl a

def two = succ (succ zero)

def bad: Eq two two = rfl two
"#,
        "can't unify",
    );
}

/// 未标注 λ 实参应用给具体类型绑定器（Church 编码）：prune_ty/prune_vflex
/// 排序修复（2026-09）前误报 can't unify（多层 telescope 的剪枝掩码错位）；
/// 修复后正确通过（与 L02-L05 的 church 样例同款）。
#[test]
fn bb_unannotated_lambda_arg_ok() {
    check(
        r#"
def Nat : U =
    (N : U) -> (N -> N) -> N -> N

def mul : Nat -> Nat -> Nat =
    a => b => N => s => z => a _ (b _ s) z

def two = N => s => z => s (s z)

def four = mul two two

println four
"#,
    );
}

/// 投影不存在的字段（Sum 参数之外的名字，含构造子数据字段）。
#[test]
fn bb_err_projection_no_field() {
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

def two = succ (succ zero)

def t = cons zero (cons two nil)

println t.nope
"#,
    );
    assert!(
        msg.contains("nope") && (msg.contains("field") || msg.contains("投影")),
        "unexpected err: {msg}"
    );
}

/// 投影构造子数据字段：`(cons two nil).x` 报 `Vec has no field x`
/// （实现只对 Sum 参数开放投影，与 README §2 "先查索引再查字段"的
/// 字面描述不一致，以实际行为为准）。
#[test]
fn bb_err_projection_data_field() {
    assert_err(
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

println (cons two nil).x
"#,
        "no field x",
    );
}

/// 对 nullary 构造子值投影（无参数可取）。
#[test]
fn bb_err_projection_on_nullary_ctor() {
    assert_err(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

println nil.len
"#,
        "cannot project",
    );
}

/// string_concat 的类型约束：非 String 实参。
#[test]
fn bb_err_string_concat_type() {
    assert_err(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

def bad = string_concat zero "!"
"#,
        "can't unify",
    );
}

/// 卡住 match 与任意值只能严格 eta 相等：`f x` 不能被证成 `x`。
#[test]
fn bb_err_strict_eta_only() {
    assert_err(
        r#"
enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

enum Eq[A](x: A, y: A) {
    refl(a: A) -> Eq a a
}

def rfl[A][a: A]: Eq a a =
    refl a

def f(n: Nat): Nat =
    match n {
        case zero => zero
        case succ(k) => k
    }

def bad(x: Nat): Eq (f x) x = rfl[Nat][x]
"#,
        "can't unify",
    );
}

/// README「已知限制 #1」：期望类型里的洞被臂内约束解成含臂局部模式
/// 变量的值 → rename 作用域越界失败，误报 can't unify（教学取舍）。
#[test]
fn bb_limitation1_outer_meta() {
    assert_err(
        r#"
enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

enum Eq[A](x: A, y: A) {
    refl(a: A) -> Eq a a
}

def bad(n: Nat): Eq _ _ =
    match n {
        case succ(k) => refl k
        case zero => refl zero
    }
"#,
        "can't unify",
    );
}

/// 已知限制 #1 的另一形态：两臂语义一致（都证 `Eq zero zero`）仍报错
/// ——洞的求解在臂 1 上下文里发生，臂 2 重锚后对不上。
#[test]
fn bb_limitation1_agreeing_arms() {
    assert_err(
        r#"
enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

enum Eq[A](x: A, y: A) {
    refl(a: A) -> Eq a a
}

def zero_zero(b: Bool): Eq _ _ =
    match b {
        case true => refl zero
        case false => refl zero
    }
"#,
        "can't unify",
    );
}

// 3. 语法与预处理怪癖（黑盒可观测行为，如实文档化）
// --------------------------------------------------------------------------------

/// match 的**行级**解析位置怪癖：语法是行导向的，match 必须写在
/// `=` 之后的下一行（`def bad(x: Bool) =` 换行 `match x { ... }`）；
/// 与 `=` 同行（`def mf = match ...`、`def ok(x: Nat): Nat = match ...`）
/// 以及 `println (match ...)` 中内联的 match 一律解析失败（Err）。
#[test]
fn bb_match_parse_positions() {
    let src = r#"
enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}
"#;
    assert_parse_err(&format!("{src}\nprintln (match zero {{ case zero => true case succ(k) => false }})\n"));
    assert_parse_err(&format!("{src}\ndef mf = match (succ zero) {{ case zero => true case succ(k) => false }}\n"));
    // 与 `=` 同行也不行（虽然带参数列表 + 返回类型）
    assert_parse_err(&format!("{src}\ndef bad(x: Bool): Bool = match x {{ case true => false case false => true }}\n"));
    // 正确形态：match 从 `=` 的下一行开始
    check(&format!(
        "{src}\ndef ok(x: Nat): Nat =\n    match x {{\n        case zero => zero\n        case succ(k) => k\n    }}\n"
    ));
}

/// `//` 行注释被剥离，不影响求值。
#[test]
fn bb_line_comments_ok() {
    assert_lines(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

def two = succ (succ zero) // trailing comment

println two
"#,
        &["Nat::succ(Nat::succ(Nat::zero))"],
    );
}

/// `/* */` 块注释被剥离（跨行）。
#[test]
fn bb_block_comments_ok() {
    assert_lines(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

/* a block
   comment */
def two = succ (succ zero)

println two
"#,
        &["Nat::succ(Nat::succ(Nat::zero))"],
    );
}

/// 预处理怪癖：字符串字面量里的 `//` 被当注释剥离 → 字符串截断 →
/// 未闭合 → 解析失败（Err("parse error")）。
#[test]
fn bb_string_double_slash_parse_err() {
    assert_parse_err("println \"a//b\"\n");
}

/// 预处理怪癖：字符串字面量里的 `/*` 被改写为空白（`"a/*b"` → `"a  b"`），
/// 程序能运行但输出被破坏（如实文档化）。
#[test]
fn bb_string_block_comment_mangled() {
    assert_lines(
        r#"
println "a/*b"
"#,
        &["a  b"],
    );
}

/// 顶层 `let` 不在 decl 语法里（Decl = Def/Println/Enum）→ 解析失败；
/// `let` 只在 match 分支体内合法（`case succ(k) => let y = k; succ y`）。
#[test]
fn bb_top_level_let_parse_err() {
    assert_parse_err(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\ndef two = succ (succ zero)\n\nlet x = two;\nprintln x\n",
    );
    assert_lines(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

def f(x: Nat): Nat =
    match x {
        case zero => zero
        case succ(k) =>
            let y = k;
            succ y
    }

println (f (succ (succ zero)))
"#,
        &["Nat::succ(Nat::succ(Nat::zero))"],
    );
}

// 4. 鲁棒性
// --------------------------------------------------------------------------------

/// 空输入 / 纯注释输入：parser 需要至少一个 decl → 解析失败。
#[test]
fn bb_empty_input_parse_err() {
    assert_parse_err("");
    assert_parse_err("   \n  \n");
    assert_parse_err("// only a comment\n");
}

/// 乱码输入：解析失败（Err("parse error")）。
#[test]
fn bb_garbage_parse_err() {
    assert_parse_err("def bad = @@@\n");
    assert_parse_err("enum { }\n");
}

/// 前向引用（引用后定义的 decl）：当前实现按声明顺序处理 → Err
/// `name not in scope`（panic 探针兜底两种可能）。
#[test]
fn bb_forward_reference() {
    let src = r#"
enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

def is_even(x: Nat): Bool =
    match x {
        case zero => true
        case succ(n) => is_odd n
    }

def is_odd(x: Nat): Bool =
    match x {
        case zero => false
        case succ(n) => is_even n
    }

println (is_even (succ (succ (succ zero))))
"#;
    match check_panic(src) {
        None => {
            let err = check_err(src);
            assert!(
                err.contains("is_odd") || err.contains("not in scope"),
                "unexpected err: {err}"
            );
        }
        Some(p) => panic!("unexpected panic: {p}\nsrc:\n{src}"),
    }
}

/// 确定性：同一程序跑两次，输出逐字节一致（含卡住 match 打印）。
#[test]
fn bb_determinism() {
    let src = r#"
enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

def f(n: Nat): Nat -> Nat =
    match n {
        case zero => succ
        case succ(k) => succ
    }

def V(n: Nat): U =
    match n {
        case zero => Bool
        case succ(m) => Bool
    }

println f
println (f (succ zero))
"#;
    let a = check(src);
    let b = check(src);
    assert_eq!(a, b, "non-deterministic output:\n{a}\n--- second ---\n{b}");
    assert!(a.contains("match n"), "out:\n{a}");
}

/// 中段错误截断语义：某 decl 报错时整个程序 Err（之前的 println 不产生
/// 输出，后续也不执行）。
#[test]
fn bb_error_truncates_program() {
    let msg = check_err(
        r#"
enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

enum Eq[A](x: A, y: A) {
    refl(a: A) -> Eq a a
}

def two = succ (succ zero)

def three = succ (succ (succ zero))

println two

def bad: Eq two three = refl two

println three
"#,
    );
    assert!(msg.contains("can't unify"), "err: {msg}");
}

/// 深度探针：可终止深结构的边界（fuel=4096 之前先栈溢出 ~1500-2000 层）。
/// 单独跑：`cargo test --test l07_blackbox bb_probe_depth_sweep -- --ignored
/// --nocapture`。注意：超过阈值的深度会让 64MB 线程栈溢出并终止整个
/// 测试进程，因此探针只扫安全区间（实测 2000 已溢出）。
#[test]
#[ignore]
fn bb_probe_depth_sweep() {
    fn probe(depth: usize) -> String {
        let src = format!(
            r#"
enum Nat {{
    zero
    succ(x: Nat)
}}

enum Eq[A](x: A, y: A) {{
    refl(a: A) -> Eq a a
}}

def big = {chain}

def ok: Eq big big = refl big
"#,
            chain = succ_chain(depth)
        );
        let input = src.to_owned();
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || match run(&input, 0) {
                Ok(out) => format!("depth {depth}: OK ({})", out.len()),
                Err(e) => format!("depth {depth}: ERR {e:?}"),
            })
            .unwrap()
            .join()
            .unwrap()
    }
    for depth in [100, 300, 600, 900, 1000] {
        eprintln!("{}", probe(depth));
    }
    eprintln!("measured elsewhere: depth 2000 overflows the 64MB stack (process abort); higher depths slow down super-linearly");
}