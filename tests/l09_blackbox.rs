//! L09_mltt 黑盒测试套件（参考版 `L09_mltt::run`）。
//!
//! 被测对象：src/L09_mltt（MLTT 切片：`Type N` 分层宇宙 + 和类型 / match，
//! 再定基层——def/enum 名字走大下标哨兵 global 表，无 decl 表；struct/new
//! 脱糖、显式替换精化、逐臂下钻匹配编译器）。
//! L09_mltt 在 lib.rs 中是私有模块，本套件用 `#[path]` 把层源码直接编入
//! 测试 crate（与 tests/l09_fast_parity.rs 同款），唯一黑盒入口是
//! `L09_mltt::run(input: &str, path_id: u32) -> Result<String, Error>`。
//!
//! 黑盒契约（全部经独立探针实测确认，2026-11；同族套件 l07/l08_blackbox 同风格）：
//!   - 输入是 typort 源码多语句文本；`println expr` 逐行把求值结果写进
//!     `Ok(String)`（每行一个 pretty 值）；
//!   - 成功：`Ok(String)`。显示形态为 L09–L13 的 **comma 血统**：
//!     构造子值 `头名::分支名(实参, …)`（L08 的空格连接是 L08 本地形态，
//!     不随 L08→L09 继承）；struct 脱糖分支名自带 `.mk`（`Point::Point.mk(...)`）；
//!     未解隐式参数打印成 binder 形式（`[A] => List::nil`；b0694c96 起隐含位
//!     用 parser 认的方括号，花括号只留给优先级分组）；卡住 match 是
//!     `n => (unsolved match n)`；越哨兵大下标 Var 显示 `recursive_N`；
//!   - 类型/合一错误：`Err(Error)`；`Error.0` 是带源码偏移的 `Span<String>`，
//!     Debug 形如 `Error("..." @ start,end)`；
//!   - **解析错误不返回 Err**（与 L08 的 `Err("parse error")` 契约不同）：
//!     L09 的 parser 返回 (已解析前缀, 错误表)，运行器把错误 `println!` 到
//!     进程 stdout 后继续检查已解析声明——因此坏 decl 前后的可解析声明都能
//!     产出输出，本套件只钉 `Ok` 输出与已解析面；
//!   - 覆盖性诊断（Warning）在本层被转成 `Err`：顶层缺构造子 = Debug 文本
//!     含 `Unmatched(Con("ctor" ...))`；嵌套缺口 = 含
//!     `match 不完整：模式位置 … 缺少构造子 …`；通配臂之后的臂 =
//!     含 `Unreachable(...)`；
//!   - 已知缺陷（本套件如实文档化，见 bb_struct_multi_projection_rejected）：
//!     L09 解析多段投影 `l.a.x` 但类型检查报 can’t unify（L08 血统的
//!     多段投影链在本层不成立；README 的"多段投影链"声称与实现不符）。
//!
//! 运行：`cargo test --test l09_blackbox`。

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

// helpers
// --------------------------------------------------------------------------------

/// 在 128MB 栈线程里跑参考版 `run`（深值/递归路径超出默认 2MB 栈）。
fn run_big(src: &str) -> Result<String, L09_mltt::Error> {
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(128 * 1024 * 1024)
        .spawn(move || L09_mltt::run(&input, 0))
        .unwrap()
        .join()
        .unwrap()
}

/// 期待成功，返回 Ok 输出。
fn check(src: &str) -> String {
    run_big(src).unwrap_or_else(|e| panic!("expected ok, got Err: {e:?}\nsrc:\n{src}"))
}

/// 期待失败，返回 `Debug` 文本（`Error("..." @ start,end)`）。
fn check_err(src: &str) -> String {
    match run_big(src) {
        Err(e) => format!("{e:?}"),
        Ok(out) => panic!("expected Err, got Ok:\n{out}\nsrc:\n{src}"),
    }
}

/// 成功路径 + 逐行精确断言。
fn assert_lines(src: &str, expected: &[&str]) {
    let out = check(src);
    let got: Vec<&str> = out.lines().collect();
    assert_eq!(got, expected, "src:\n{src}\n--- actual ---\n{out}");
}

/// 错误路径 + 消息片段断言（可多个 needle）。
fn assert_err(src: &str, needles: &[&str]) {
    let dbg = check_err(src);
    for needle in needles {
        assert!(dbg.contains(needle), "err 缺 {needle:?}:\n{dbg}\nsrc:\n{src}");
    }
}

/// 深度 n 的 `Nat::succ(...)` 嵌套输出文本。
fn nat_succs(n: usize) -> String {
    "Nat::succ(".repeat(n) + "Nat::zero" + &")".repeat(n)
}

// tests
// --------------------------------------------------------------------------------

/// 空输入 → 空输出（parser 无 decl、无错误）。
#[test]
fn bb_empty_input_ok() {
    assert_eq!(check(""), "");
}

/// 纯注释输入（行注释与块注释）→ 空输出。
#[test]
fn bb_comment_only_ok() {
    assert_eq!(check("// line comment only\n/* block\ncomment */\n"), "");
}

/// 块注释在行内被预处理抹掉，后继代码照常解析。
#[test]
fn bb_block_comment_inline() {
    assert_lines(
        "enum Bool {\n    true\n    false\n}\n\n/* 注释 */ println true\n",
        &["Bool::true"],
    );
}

/// 行尾 // 注释被预处理抹掉。
#[test]
fn bb_inline_line_comment() {
    assert_lines(
        "enum Bool {\n    true\n    false\n}\n\nprintln true // trailing comment\n",
        &["Bool::true"],
    );
}

/// 非泛型构造子值显示：头名::分支名(实参, …)，succ 嵌套。
#[test]
fn bb_nat_bool_ctor_display() {
    assert_lines(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\nenum Bool {\n    true\n    false\n}\n\ndef two = succ (succ zero)\n\ndef not(x: Bool): Bool =\n    match x {\n        case true => false\n        case false => true\n    }\n\nprintln two\nprintln zero\nprintln (not true)\nprintln (not false)\n",
        &[nat_succs(2).as_str(), "Nat::zero", "Bool::false", "Bool::true"],
    );
}

/// 字符串字面量按裸内容打印（LiteralIntro 臂）。
#[test]
fn bb_string_literal_display() {
    assert_lines(
        "def mystr = \"hello world\"\n\nprintln mystr\nprintln \"\"\n",
        &["hello world", ""],
    );
}

/// string_concat 全应用（两个字面量）直接拼接。
#[test]
fn bb_string_concat_applied() {
    assert_lines(
        "def mystr = \"hello world\"\n\ndef mystr2 = string_concat mystr \"!\"\n\nprintln mystr\nprintln mystr2\nprintln (string_concat \"hello \" \"world\")\n",
        &["hello world", "hello world!", "hello world"],
    );
}

/// string_concat 部分应用卡在 Prim Func（无 spine 裸 Prim）。
#[test]
fn bb_string_concat_partial_stuck() {
    assert_lines(
        "def mystr = \"hello world\"\n\ndef stuck_concat = string_concat mystr\n\nprintln stuck_concat\nprintln (stuck_concat \"!\")\n",
        &["string_concat hello world", "hello world!"],
    );
}

/// 泛型构造子值显示：List::cons(a, b) 逗号血统；Enum 名本身打印为类型名。
#[test]
fn bb_list_ctor_comma_display() {
    assert_lines(
        "enum Bool {\n    true\n    false\n}\n\nenum List[A] {\n    nil\n    cons(head: A, tail: List[A])\n}\n\nprintln nil\nprintln (cons true nil)\nprintln (cons true (cons false nil))\nprintln Bool\n",
        // 隐含 binder 用 parser 的 [] 语法（花括号只留给优先级分组）。
        &["[A] => List::nil", "List::cons(Bool::true, List::nil)", "List::cons(Bool::true, List::cons(Bool::false, List::nil))", "Bool"],
    );
}

/// 构造子作为函数值打印成 η 展开：x => Nat::succ(x)。
#[test]
fn bb_ctor_function_eta() {
    assert_lines(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\nprintln succ\n",
        &["x => Nat::succ(x)"],
    );
}

/// Unicode 字符串字面量原样输出。
#[test]
fn bb_unicode_string_literal() {
    assert_lines("println \"你好 世界\"\n", &["你好 世界"]);
}

/// 只有 def 没有 println → 空输出（ret 仅由 println 累积）。
#[test]
fn bb_only_defs_no_println() {
    assert_eq!(check("enum Nat {\n    zero\n    succ(x: Nat)\n}\n\ndef two = succ zero\n"), "");
}

/// let 绑定在 def 体内求值。
#[test]
fn bb_let_binding() {
    assert_lines(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\ndef two = succ (succ zero)\n\ndef with_let : Nat = let x = two; succ x\n\nprintln with_let\n",
        &[nat_succs(3).as_str()],
    );
}

/// let 作用域内再套两层 succ：four = succ(succ(two))。
#[test]
fn bb_let_shadowing() {
    assert_lines(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\ndef two = succ (succ zero)\n\ndef four = let x = two; succ (succ x)\n\nprintln four\n",
        &[nat_succs(4).as_str()],
    );
}

/// 自递归 def add：模式 match + succ 归约。
#[test]
fn bb_add_recursion() {
    assert_lines(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\ndef two = succ (succ zero)\n\ndef add(x: Nat, y: Nat) =\n    match x {\n        case zero => y\n        case succ(n) => succ (add n y)\n    }\n\ndef four = add two two\n\nprintln four\n",
        &[nat_succs(4).as_str()],
    );
}

/// 嵌套 match + 自递归 even：4 为 true。
#[test]
fn bb_even_nested_match() {
    assert_lines(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\nenum Bool {\n    true\n    false\n}\n\ndef four = succ (succ (succ (succ zero)))\n\ndef even(n: Nat): Bool =\n    match n {\n        case zero => true\n        case succ(m) => match m {\n            case zero => false\n            case succ(k) => even k\n        }\n    }\n\nprintln (even four)\n",
        &["Bool::true"],
    );
}

/// 三种嵌套模式的 list 匹配：cons(h,cons(h2,t)) / cons(h,nil) / nil。
#[test]
fn bb_second_or_zero_nested_patterns() {
    assert_lines(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\nenum List[A] {\n    nil\n    cons(head: A, tail: List[A])\n}\n\ndef second_or_zero(x: List[Nat]): Nat =\n    match x {\n        case nil => zero\n        case cons(h, nil) => zero\n        case cons(h, cons(h2, t)) => h2\n    }\n\nprintln (second_or_zero (cons (succ zero) (cons (succ (succ zero)) nil)))\nprintln (second_or_zero (cons (succ zero) nil))\nprintln (second_or_zero nil)\n",
        &[nat_succs(2).as_str(), "Nat::zero", "Nat::zero"],
    );
}

/// 0 号全局自引用（def f : String = f）显示为 recursive_0（哨兵边界修复的显示面）。
#[test]
fn bb_self_ref_recursive_0() {
    assert_lines("def f : String = f\n\nprintln f\n", &["recursive_0"]);
}

/// 前向引用（先声明后定义）报 name not in scope：L09 只有 fake_bind 自占位，没有后向查找。
#[test]
fn bb_forward_reference_rejected() {
    assert_err(
        "enum Vec[A](len: Nat) {\n    nil -> Vec[A] zero\n}\n",
        &["name not in scope: Nat"],
    );
}

/// 应用实参本身是应用/构造子时不额外加括号（pretty 恒等显示）。
#[test]
fn bb_app_argument_parens_display() {
    assert_lines(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\ndef two = succ (succ zero)\n\ndef id(x: Nat): Nat = x\n\nprintln (id two)\n",
        &[nat_succs(2).as_str()],
    );
}

/// 40 层 succ 链：深值 quote/pretty 路径（128MB 栈内）不崩。
#[test]
fn bb_deep_succ_40() {
    let src = format!(
        "enum Nat {{\n    zero\n    succ(x: Nat)\n}}\n\nprintln {}\n",
        "succ (".repeat(40) + "zero" + &")".repeat(40)
    );
    assert_lines(&src, &[nat_succs(40).as_str()]);
}

/// 索引参数投影 t.len 化简为构造子链（4）。
#[test]
fn bb_vec_len_projection() {
    assert_lines(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\nenum Vec[A](len: Nat) {\n    nil -> Vec[A] zero\n    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)\n}\n\ndef two = succ (succ zero)\n\ndef three = succ (succ (succ zero))\n\ndef t = cons zero (cons two (cons three (cons two nil)))\n\nprintln t.len\n",
        &[nat_succs(4).as_str()],
    );
}

/// GADT 索引：head 取 Vec[T] (succ L) 上的 cons 首元素。
#[test]
fn bb_vec_head_indexed_singleton() {
    assert_lines(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\nenum Vec[A](len: Nat) {\n    nil -> Vec[A] zero\n    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)\n}\n\ndef head[T, L: Nat](x: Vec[T] (succ L)): T =\n    match x {\n        case cons(x, _) => x\n    }\n\nprintln (head (cons zero nil))\n",
        &["Nat::zero"],
    );
}

/// GADT refl 值显示：Eq::refl(实参)。
#[test]
fn bb_gadt_refl_value_display() {
    assert_lines(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\nenum Eq[A](x: A, y: A) {\n    refl[a: A] -> Eq[A] a a\n}\n\ndef two = succ (succ zero)\n\ndef test: Eq two two = refl\n\nprintln test\n",
        &[format!("Eq::refl({})", nat_succs(2)).as_str()],
    );
}

/// GADT 索引不合：Eq two three = refl 报 cannot unify（期望类型带两个 succ 链）。
#[test]
fn bb_gadt_refl_bad() {
    assert_err(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\nenum Eq[A](x: A, y: A) {\n    refl[a: A] -> Eq[A] a a\n}\n\ndef two = succ (succ zero)\n\ndef three = succ (succ (succ zero))\n\ndef bad: Eq two three = refl\n",
        &["can't unify", "Eq[Nat", "expected:"],
    );
}

/// 等式证明项（rfl 包装）打印为 Eq::refl(Nat::succ(...))。
#[test]
fn bb_eq_proof_term_display() {
    assert_lines(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\nenum Eq[A](x: A, y: A) {\n    refl(a: A) -> Eq a a\n}\n\ndef rfl[A][a: A]: Eq a a =\n    refl a\n\ndef two = succ (succ zero)\n\ndef ck: Eq two two = rfl\n\nprintln ck\n",
        &[format!("Eq::refl({})", nat_succs(2)).as_str()],
    );
}

/// 依赖 match：索引精化传播到分支体与返回类型（无 println，只要求检查通过）。
#[test]
fn bb_dependent_match_ok() {
    let src = "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\nenum Vec[A](len: Nat) {\n    nil -> Vec[A] zero\n    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)\n}\n\ndef t[len: Nat](x: Vec[Nat] len, y: Vec[Nat] len): Vec[Nat] (succ len) =\n    match x {\n        case nil => cons zero nil\n        case cons(x, xs) => match y {\n            case cons(y, ys) => cons x (t xs ys)\n        }\n    }\n";
    assert!(run_big(src).is_ok(), "依赖 match 应通过: {:?}", run_big(src));
}

/// 隐式实参逗号合写 f[A, B] 等价于 f[A][B]（e2d04bb 回移植）。
#[test]
fn bb_implicit_comma_args_equiv() {
    assert_lines(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\nenum Bool {\n    true\n    false\n}\n\nenum P1[A, B] {\n    p1[A, B](a: A, b: B) -> P1[A][B]\n}\n\nprintln (p1[Nat, Bool] zero true)\n",
        &["P1::p1(Nat, Bool, Nat::zero, Bool::true)"],
    );
}

/// 多隐式无标注参数 P1[A, B] + 显式实例化：域洞钉 U(0) 后可通过。
#[test]
fn bb_implicit_hole_pinned_u0() {
    assert_lines(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\nenum Bool {\n    true\n    false\n}\n\nenum P1[A, B] {\n    p1[A, B](a: A, b: B) -> P1[A][B]\n}\n\nprintln (p1[Nat][Bool] zero true)\n",
        &["P1::p1(Nat, Bool, Nat::zero, Bool::true)"],
    );
}

/// 高宇宙 enum：Type 0/1 显示 + HighLvl[Nat] 属于 Type 2。
#[test]
fn bb_high_lvl_enum_universes() {
    assert_lines(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\ndef test0: Type 1 = Type 0\n\ndef test1: Type 2 = Type 1 -> Type 0\n\nenum HighLvl[A] {\n    case1(a: A)\n    case2(a: test1)\n}\n\ndef test2: HighLvl[Nat] = case1 zero\n\ndef test3: Type 2 = HighLvl[Nat]\n\nprintln test0\nprintln test1\nprintln test3\n",
        &["Type 0", "Type 1 → Type 0", "HighLvl[Nat]"],
    );
}

/// struct 脱糖：分支名自带 .mk（Point::Point.mk）；值级投影 p.x 化简到字段。
#[test]
fn bb_struct_mk_projection() {
    assert_lines(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\ndef two = succ (succ zero)\n\nstruct Point {\n    x: Nat\n    y: Nat\n}\n\ndef p = new Point(two, zero)\n\nprintln p\nprintln p.x\n",
        &[format!("Point::Point.mk({}, Nat::zero)", nat_succs(2)).as_str(), nat_succs(2).as_str()],
    );
}

/// struct 字段投影 + new 组合：point_add = (4, 6)。
#[test]
fn bb_struct_point_add() {
    assert_lines(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\ndef two = succ (succ zero)\n\ndef four = succ (succ (succ (succ zero)))\n\nstruct Point {\n    x: Nat\n    y: Nat\n}\n\ndef add(x: Nat, y: Nat) =\n    match x {\n        case zero => y\n        case succ(n) => succ (add n y)\n    }\n\ndef point_add(p1: Point, p2: Point): Point =\n    new Point((add p1.x p2.x), (add p1.y p2.y))\n\ndef start_point = new Point(zero, four)\n\ndef end_point = new Point(four, two)\n\nprintln (point_add start_point end_point)\n",
        &[format!("Point::Point.mk({}, {})", nat_succs(4), nat_succs(6)).as_str()],
    );
}

/// 依赖字段投影：proof : Eq witness two 的 e.proof 取回 refl。
#[test]
fn bb_struct_dependent_field_projection() {
    assert_lines(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\nenum Eq[A](x: A, y: A) {\n    refl(a: A) -> Eq a a\n}\ndef two = succ (succ zero)\nstruct Ex {\n    witness: Nat\n    proof: Eq witness two\n}\ndef p = Ex.mk two (refl two)\ndef get_proof(e: Ex): Eq e.witness two = e.proof\nprintln (get_proof p)\n",
        &[format!("Eq::refl({})", nat_succs(2)).as_str()],
    );
}

/// struct 版高宇宙类型：HighLvl[Nat] 可打印为类型项。
#[test]
fn bb_struct_high_universe() {
    assert_lines(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\ndef test1: Type 2 = Type 1 -> Type 0\n\ndef test2_t: Type 1 -> Type 0 = t => Nat\n\nstruct HighLvl[A] {\n    case1: A\n    case2: test1\n}\n\ndef test2: HighLvl[Nat] = new HighLvl(zero, test2_t)\n\ndef test3: Type 2 = HighLvl[Nat]\n\nprintln test3\n",
        &["HighLvl[Nat]"],
    );
}

/// 【已知缺陷·如实钉住】L09 解析多段投影 l.a.x，但类型检查报 cannot unify（L08 血统多段投影链在本层不成立；README 的"多段投影链"声称与实现不符）。若未来修复，本测试失败即提示更新。
#[test]
fn bb_struct_multi_projection_rejected() {
    assert_err(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\ndef two = succ (succ zero)\n\nstruct Point {\n    x: Nat\n    y: Nat\n}\n\nstruct Line {\n    a: Point\n    b: Point\n}\n\ndef headX(l: Line): Nat = l.a.x\n\nprintln (headX (new Line(new Point(two, zero), new Point(zero, two))))\n",
        &["can't unify"],
    );
}

/// Type N 字面显示：Type 0 / Type 1 → Type 0（匿名 Π 箭头）。
#[test]
fn bb_type_levels_display() {
    assert_lines(
        "def test0: Type 1 = Type 0\n\ndef test1: Type 2 = Type 1 -> Type 0\n\nprintln test0\nprintln test1\n",
        &["Type 0", "Type 1 → Type 0"],
    );
}

/// 高阶 λ 类型注释：Pi 塔的 universe 推断（Type 1 上的类型构造）。
#[test]
fn bb_universe_arrow_higher_order_ok() {
    let src = "def NatT : Type 1 = (N : Type 0) -> (N -> N) -> N -> N\n";
    let r = run_big(src);
    assert!(r.is_ok(), "高阶 λ 注释应通过: {r:?}");
}

/// 宇宙注解与字面量体不匹配：find Type 0 / expected String。
#[test]
fn bb_universe_body_literal_error() {
    assert_err(
        "def bad : Type 0 = \"not a type\"\nprintln bad\n",
        &["can't unify", "find: Type 0", "expected: String"],
    );
}

/// 类型层级失配：def bad : Nat = Type 0 → find Nat / expected Type 1。
#[test]
fn bb_universe_level_mismatch() {
    assert_err(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\ndef bad : Nat = Type 0\nprintln bad\n",
        &["can't unify", "find: Nat", "expected: Type 1"],
    );
}

/// 构造子返回类型不是本 enum：c -> Nat 被 check_ctor_wf 拒绝。
#[test]
fn bb_ctor_wf_external_ret() {
    assert_err(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\nenum Foo {\n    c -> Nat\n}\n",
        &["构造子 c 的返回类型是 Nat，不是 Foo"],
    );
}

/// 构造子返回类型参数被特化：c -> Foo[Bool] 拒绝（参数必须是参数变量）。
#[test]
fn bb_ctor_wf_param_specialized() {
    assert_err(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\nenum Bool {\n    true\n    false\n}\n\nenum Foo[A] {\n    c -> Foo[Bool]\n}\n",
        &["构造子 c 的返回类型参数必须是 Foo 的参数变量"],
    );
}

/// 构造子返回类型不是和类型：c -> Type 0 拒绝。
#[test]
fn bb_ctor_wf_not_sum() {
    assert_err(
        "enum Foo {\n    c -> Type 0\n}\n",
        &["构造子 c 的返回类型不是和类型"],
    );
}

/// 重绑定参数惯用法 pack[A, B](a, b) -> Pack[A][B] 放行。
#[test]
fn bb_ctor_wf_rebind_ok() {
    assert_lines(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\nenum Bool {\n    true\n    false\n}\n\nenum Pack[A, B] {\n    pack[A, B](a: A, b: B) -> Pack[A][B]\n}\n\ndef t = pack[Nat][Bool] zero true\n\nprintln t\n",
        &["Pack::pack(Nat, Bool, Nat::zero, Bool::true)"],
    );
}

/// 重定义报错（从 L07/L08 继承，L13 `fake_bind` 前传）：先前 def / enum /
/// 构造子裸名 / `Cxt::new` 内建已被占用 → `redefine {名}` 定向报错，
/// 不再静默覆盖。先类型后重定义（与 L07/L08/L13 同序）。
#[test]
fn bb_redefinition_rejected() {
    // 同名 def
    assert_err(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\ndef f: Nat = zero\ndef f: Nat = succ zero\n",
        &["redefine", "f"],
    );
    // def 撞 enum 名
    assert_err(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\ndef Nat: Type 1 = Type 0\n",
        &["redefine", "Nat"],
    );
    // def 撞构造子裸名
    assert_err(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\ndef zero: Nat = zero\n",
        &["redefine", "zero"],
    );
    // def 撞内建（Cxt::new 的 String）
    assert_err("def String: Type 1 = Type 0\n", &["redefine", "String"]);
    // enum 撞先前 def
    assert_err(
        "def Nat: Type 1 = Type 0\n\nenum Nat {\n    zero\n}\n",
        &["redefine", "Nat"],
    );
}

/// 顶层覆盖缺失：Bool 缺 false 臂 → Err 文本含 Unmatched(Con("false"...))。
#[test]
fn bb_coverage_missing_top() {
    assert_err(
        "enum Bool {\n    true\n    false\n}\n\ndef bad(x: Bool): Bool =\n    match x {\n        case true => false\n    }\n",
        &["Unmatched", "false"],
    );
}

/// 嵌套覆盖缺失：List 的 nil + cons(h,nil) 缺 cons(h,cons(...)) → IncompleteNested 文案。
#[test]
fn bb_coverage_nested_gap() {
    assert_err(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\nenum List[A] {\n    nil\n    cons(head: A, tail: List[A])\n}\n\ndef bad(x: List[Nat]): Nat =\n    match x {\n        case nil => zero\n        case cons(h, nil) => h\n    }\n",
        &["IncompleteNested", "match 不完整：模式位置 cons#2 缺少构造子 cons"],
    );
}

/// 补上嵌套臂后通过，且运行首匹配选 nil。
#[test]
fn bb_coverage_nested_complete_ok() {
    assert_lines(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\nenum List[A] {\n    nil\n    cons(head: A, tail: List[A])\n}\n\ndef ok(x: List[Nat]): Nat =\n    match x {\n        case nil => zero\n        case cons(h, nil) => h\n        case cons(h, cons(h2, t)) => h2\n    }\nprintln (ok nil)\n",
        &["Nat::zero"],
    );
}

/// 通配臂覆盖剩余构造子，不报 Unmatched。
#[test]
fn bb_coverage_wildcard_covers() {
    assert_lines(
        "enum Bool {\n    true\n    false\n}\n\ndef ok(x: Bool): Bool =\n    match x {\n        case true => false\n        case _ => true\n    }\nprintln (ok true)\n",
        &["Bool::false"],
    );
}

/// 通配臂之后的臂报 Unreachable（L09 只认通配臂之后的遮蔽）。
#[test]
fn bb_coverage_shadowed_after_catch_all() {
    assert_err(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\ndef const_zero(x: Nat): Nat =\n    match x {\n        case n => zero\n        case zero => zero\n        case succ(k) => succ k\n    }\n",
        &["Unreachable"],
    );
}

/// 索引族 Vec[Nat] zero 只写 cons 臂：实际报 Unmatched(nil)（该构造子可达而 cons 臂覆盖不到它；不是不可达臂告警）。
#[test]
fn bb_coverage_indexed_vec_nil_unmatched() {
    assert_err(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\nenum Vec[A](len: Nat) {\n    nil -> Vec[A] zero\n    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)\n}\n\ndef bad(v: Vec[Nat] zero): Nat =\n    match v {\n        case cons(x, xs) => x\n    }\n",
        &["Unmatched", "nil"],
    );
}

/// 未绑定名字：error name not in scope。
#[test]
fn bb_err_undefined_name() {
    assert_err("println nope\n", &["name not in scope: nope"]);
}

/// Err 携带源码偏移：Error.0 是 Span，start/end offset 指向 token（println nope → 8,12）。
#[test]
fn bb_err_carries_span() {
    let input = "println nope\n";
    let e = run_big(input).unwrap_err();
    assert_eq!(e.0.start_offset, 8, "start_offset: {:?}", e);
    assert_eq!(e.0.end_offset, 12, "end_offset: {:?}", e);
    let dbg = format!("{e:?}");
    assert!(dbg.contains("@ 8,12"), "Debug 应含 @ 8,12: {dbg}");
}

/// 命名 λ 不可推断：infer named lambda。
#[test]
fn bb_err_named_lambda() {
    assert_err("def h = [B = zero] y => y\nprintln h\n", &["infer named lambda"]);
}

/// 值级字段缺失（接收者类型未解）：has no object zzz。
#[test]
fn bb_err_field_missing_value() {
    assert_err(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\nstruct Point {\n    x: Nat\n}\n\ndef p = new Point(zero)\ndef bad = p.zzz\n",
        &["has no object", "zzz"],
    );
}

/// 类型级字段缺失：has no object zzz（Debug 内嵌 Sum 头）。
#[test]
fn bb_err_field_missing_type() {
    assert_err(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\nstruct Point {\n    x: Nat\n}\n\ndef bad(p: Point) = p.zzz\n",
        &["has no object", "zzz"],
    );
}

/// 【契约】解析错误不返回 Err：坏 decl 前后的可解析声明都被检查并输出（resilient 解析的前缀+后缀保留）。
#[test]
fn bb_parse_error_prefix_kept() {
    assert_lines(
        "enum Bool {\n    true\n    false\n}\nprintln true\n\ndef = 1\n\nprintln false\n",
        &["Bool::true", "Bool::false"],
    );
}

/// 【契约】只有坏 decl：run 仍 Ok，输出为空（错误走进程 stdout）。
#[test]
fn bb_parse_error_only_ok_empty() {
    assert_eq!(check("def bad(\n"), "");
}

/// 坏 token 在文件尾：已解析前缀的输出保留。
#[test]
fn bb_parse_error_trailing_ok() {
    assert_eq!(check("enum Bool {\n    true\n    false\n}\nprintln true\n@ # $\n"), "Bool::true\n");
}

/// README 的 -- 注释不支持，但当前 parser 容错为整行无 decl（Ok 空输出，不崩溃）。
#[test]
fn bb_dash_comment_tolerated() {
    assert_eq!(check("-- not a comment\n"), "");
}

/// 负向事实：L09 无 print builtin（唯一 builtin 是 string_concat）。
#[test]
fn bb_no_print_builtin() {
    assert_err("println (print \"x\")\n", &["name not in scope: print"]);
}

/// 负向事实：无 eq 内建，等式只能走 Eq/refl 编码。
#[test]
fn bb_no_equality_builtin() {
    assert_err(
        "enum Bool {\n    true\n    false\n}\nprintln (eq true true)\n",
        &["name not in scope: eq"],
    );
}

/// 负向事实：无文件 IO builtin。
#[test]
fn bb_no_io_builtin() {
    assert_err("println (read_file \"x\")\n", &["name not in scope: read_file"]);
}

/// 唯一 builtin string_concat：内建字符串类型 String 可作类型使用。
#[test]
fn bb_only_builtin_string_concat_display() {
    assert_lines(
        "def idS(x: String): String = x\nprintln (idS \"s\")\n",
        &["s"],
    );
}

/// 高阶函数组合：多态 compose 应用于 succ/succ → 两层 succ。
#[test]
fn bb_higher_order_compose() {
    assert_lines(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\ndef compose[A, B, C](f: B -> C, g: A -> B, x: A): C = f (g x)\n\nprintln (compose succ succ zero)\n",
        &[nat_succs(2).as_str()],
    );
}

/// Church 编码自然数（纯 λ 演算 + 高阶类型 NatC : Type 1）：Church 数应用回
/// enum Nat 的 toNat，four = addC twoC twoC → succ^4(zero)。
#[test]
fn bb_church_encoding_to_nat() {
    assert_lines(
        "def NatC : Type 1 = (N : Type 0) -> (N -> N) -> N -> N\n\ndef zeroC : NatC = N => s => z => z\n\ndef twoC : NatC = N => s => z => s (s z)\n\ndef addC : NatC -> NatC -> NatC =\n    a => b => N => s => z => a _ (b _ s) z\n\ndef fourC = addC twoC twoC\n\nenum Nat {\n    zero\n    succ(x: Nat)\n}\n\ndef toNat(n : NatC) : Nat = n Nat succ zero\n\nprintln (toNat fourC)\n",
        &[nat_succs(4).as_str()],
    );
}
