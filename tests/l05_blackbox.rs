//! L05_pruning 黑盒测试套件。
//!
//! 被测对象：`src/L05_pruning`（elaboration-zoo `05-pruning` 的 Rust 移植：
//! 双向 elaboration + holes + pattern unification + 隐式参数 + **meta 探测
//! （pruning）**），唯一黑盒入口是 `main_with(mode, src)`（mode ∈ {--help,
//! elab, nf, type}），经 `#[path]` 独立编译进本测试 crate。
//!
//! 双 oracle：
//!   1. 期望输出字符串 —— 由上游 05（Cxt/Evaluation/Unification/Elaboration/
//!      Pretty）逐函数语义推导 + 参考版实际输出核对（整串断言均已核对）；
//!   2. 参考版（`mod.rs`）↔ 性能版（`bump_spine_iter.rs`）**三模式**
//!      （nf/type/elab）逐字节互检。
//!
//! 与 L04 的语义差别（本套件专门覆盖）：
//!   - **typed metas**：elab 里每个 meta 打印类型 `let ?m : T = v;`（L04 无类型）；
//!     洞的类型是闭包迭代 Π（telescope）。
//!   - **AppPruning 掩码**：洞对 scope 的抽象是 `Option<Icit>` 掩码——绑定
//!     槽位应用（打印实参名，隐式裹 `{}`）、define 槽位跳过（不打印）；匿名
//!     binder `_` 打印 `@位序`。
//!   - **同头 flex-flex = intersect**：`?m sp =? ?m sp'` 取两 spine 的交并剪
//!     差异槽（L04 此处是逐实参 unify_sp）。
//!   - **非线性 spine**：`m a a =? rhs` 在 m 的类型不依赖 a 时可解（invert
//!     产掩码 + prune_ty 验证）。
//!   - **λ 包裹取自类型**：解的 λ 层名/icit 随 meta 类型 Π（`"_"` → `x{l}`）。

#![feature(pattern)]

#[path = "../src/list.rs"]
mod list;

#[path = "../src/parser_lib.rs"]
mod parser_lib;

#[path = "../src/L05_pruning/mod.rs"]
mod L05_pruning;

use L05_pruning::bump_spine_iter as fast;

// helpers
// --------------------------------------------------------------------------------

fn nf(src: &str) -> String {
    L05_pruning::main_with("nf", src)
}

fn ty(src: &str) -> String {
    L05_pruning::main_with("type", src)
}

fn elab(src: &str) -> String {
    L05_pruning::main_with("elab", src)
}

/// Oracle 2：参考版与性能版在全部三种模式下输出逐字节一致。
fn assert_parity(src: &str) {
    for mode in ["nf", "type", "elab"] {
        let b = L05_pruning::main_with(mode, src);
        let f = fast::main_with(mode, src);
        assert_eq!(
            b, f,
            "{mode} 模式双实现不一致，src:\n{src}\n--- basic ---\n{b}--- fast ---\n{f}"
        );
    }
}

/// 报错输出：以 `(stdin):{line}:{col}:` 开头且包含消息片段。
fn assert_error_at(src: &str, line: usize, col: usize, needle: &str) {
    let out = ty(src);
    assert!(
        out.starts_with(&format!("(stdin):{line}:{col}:\n")),
        "错误位置不符：期望 ({line}:{col})，实际：\n{out}"
    );
    assert!(out.contains(needle), "错误消息缺 {needle:?}：\n{out}");
    assert_parity(src);
}

const HELP: &str = "usage: elabzoo-pruning [--help|elab|nf|type]\n  --help : display this message\n  elab   : read & elaborate expression from stdin\n  nf     : read & typecheck expression from stdin, print its normal form and type\n  type   : read & typecheck expression from stdin, print its type\n";

// 模式与输出格式
// --------------------------------------------------------------------------------

#[test]
fn help_and_unknown_modes() {
    for mode in ["--help", "", "bogus", "foo", "ELAB", "-h"] {
        assert_eq!(L05_pruning::main_with(mode, ""), HELP, "mode {mode:?}");
        assert_eq!(fast::main_with(mode, ""), HELP, "fast mode {mode:?}");
    }
}

#[test]
fn type_and_nf_smoke() {
    assert_eq!(ty("U"), "U\n");
    assert_eq!(ty("_"), "?0\n");
    assert_eq!(nf("U"), "U\n  :\nU\n");
    // 洞的类型是闭包迭代 Π（telescope）——elab 打印带类型形态
    assert_eq!(
        elab("let f : (A : U)(x : A) -> U = _; f"),
        "let ?0 : (A : U)(x : A) → U = ?;\n\n\
         let f : (A : U)(x : A) → U\n  = ?0;\n\nf\n"
    );
    assert_parity("let f : (A : U)(x : A) -> U = _; f");
}

#[test]
fn parse_error_output_is_plain_line() {
    for src in ["", "   \n\t", "-- just a comment\n", "{- block -}", "\n\n", "{"] {
        assert_eq!(nf(src), "parse error\n", "src: {src:?}");
        assert_parity(src);
    }
}

// 基础（L04 同款基线：隐式插入/命名实参/icit）
// --------------------------------------------------------------------------------

#[test]
fn implicit_insertion_baseline() {
    assert_eq!(
        elab("let id : {A : U} -> A -> A = \\x. x;\nid U U\n"),
        "(stdin):2:1:\n  |\n2 | id U U\n  | ^\nCannot unify expected type\n\n  U\n\n\
         with inferred type\n\n  (x : ?1) → ?2 x\n"
    );
    // `id {U} U` 正常
    assert_eq!(nf("let id : {A : U} -> A -> A = \\x. x;\nid {U} U\n"), "U\n  :\nU\n");
    assert_parity("let id : {A : U} -> A -> A = \\x. x;\nid {U} U\n");
}

#[test]
fn error_messages_parity() {
    assert_error_at("id", 1, 1, "Name not in scope: id");
    assert_error_at(
        "let g : U -> U -> U = \\x y. x;\ng {U}",
        2,
        1,
        "Function icitness mismatch: expected implicit, got explicit.",
    );
    assert_error_at(
        "let const : {A B} -> A -> B -> A = \\x y. x;\nconst {C = U} U U\n",
        2,
        1,
        "No named implicit argument with name C",
    );
    assert_error_at(
        "\\{B = x} y. y",
        1,
        1,
        "Cannot infer type for lambda with named argument",
    );
}

// pruning：AppPruning 掩码显示
// --------------------------------------------------------------------------------

/// 洞的 scope 抽象掩码：绑定槽打印实参名、define 槽跳过。
#[test]
fn app_pruning_mask_skips_defines() {
    // `id2 = \x. id x`：插入的 A 由 `id` 的实参类型（x 的类型 meta）解出；
    // elab 里 `?0 A x` 只显示绑定槽（A、x），顶层 define（id）不入掩码。
    assert_eq!(
        elab(L05_pruning::EX0_SRC),
        "let ?0 : (A : U)(x : A) → U = λ A x. A;\n\n\
         let id : {A : U} → A → A\n  = λ {A} x. x;\n\n\
         let id2 : {A : U} → A → A\n  = λ {A} x. id {?0 A x} x;\n\nU\n"
    );
    assert_parity(L05_pruning::EX0_SRC);
}

/// 非线性可解（README 例 1）：`m a a =? λ x y. y`，m 的类型不依赖 a，
/// 重复变量整级剪除后求解；解 λ 包裹取自 m 的类型 telescope（名字随 Π）。
#[test]
fn nonlinear_solvable() {
    let src = "\
let Eq : {A : U} -> A -> A -> U = \\{A} x y. (P : A -> U) -> P x -> P y;
let refl : {A : U}{x : A} -> Eq {A} x x = \\ _ px. px;
let the : (A : U) -> A -> A = \\ _ x. x;
let m : (A : U)(B : U) -> U -> U -> U = _;
let test = \\ a b. the (Eq (m a a) (\\ x y. y)) refl;
U";
    assert_eq!(
        elab(src),
        "let ?0 : (A : U)(B : U) → U → U → U = λ A B x0 x1. x1;\n\
         let ?1 : U = (a : U)(b : ?3 a)(P : (U → U → U) → U) → P (λ x0 x1. x1) → P (λ x y. y);\n\
         let ?2 : U = U;\n\
         let ?3 : (a : U) → U = ?;\n\
         let ?4 : (a : U)(b : ?3 a) → U = λ a b. U → U → U;\n\
         let ?5 : (a : U)(b : ?3 a) → U = λ a b. U → U → U;\n\
         let ?6 : (a : U)(b : ?3 a) → U → U → U = λ a b x0 x1. x1;\n\
         let ?7 : U → U → U = λ x0 x1. x1;\n\n\
         let Eq : {A : U} → A → A → U\n  = λ {A} x y. (P : A → U) → P x → P y;\n\n\
         let refl : {A : U}{x : A} → Eq {A} x x\n  = λ {A} {x} _ px. px;\n\n\
         let the : (A : U) → A → A\n  = λ _ x. x;\n\n\
         let m : (A : U)(B : U) → U → U → U\n  = ?0;\n\n\
         let test : ?1\n  = λ a b. the (Eq {?4 a b} (m a a) (λ x y. y)) (refl {?5 a b} {?6 a b});\n\nU\n"
    );
    assert_eq!(ty(src), "U\n");
    assert_parity(src);
}

/// 非线性不可解（README 例 2）：m 的类型依赖非线性实参，剪不动 → Cannot unify。
#[test]
fn nonlinear_unsolvable() {
    let src = "\
let Eq : {A : U} -> A -> A -> U = \\{A} x y. (P : A -> U) -> P x -> P y;
let refl : {A : U}{x : A} -> Eq {A} x x = \\ _ px. px;
let the : (A : U) -> A -> A = \\ _ x. x;
let m : (A : U)(B : U) -> A -> B -> B = _;
let test = \\ a b. the (Eq (m a a) (\\ x y. y)) refl;
U";
    let out = ty(src);
    assert!(out.contains("Cannot unify expected type"), "{out}");
    assert!(out.contains("(P : (a → a → a) → U) → P (?0 a a) → P (λ x y. y)"), "{out}");
    assert_error_at(src, 5, 47, "Cannot unify expected type");
}

/// 交集剪枝（README 例 3）：`m a b c =? m c b a`——首尾实参不等被剪，
/// 只留中间的 b；m 解为 `λ x0 x1 x2. ?8 x1`。
#[test]
fn intersection_pruning() {
    let src = "\
let Eq : {A : U} -> A -> A -> U = \\{A} x y. (P : A -> U) -> P x -> P y;
let refl : {A : U}{x : A} -> Eq {A} x x = \\ _ px. px;
let the : (A : U) -> A -> A = \\ _ x. x;
let m : U -> U -> U -> U = _;
let test = \\ a b c. the (Eq (m a b c) (m c b a)) refl;
U";
    let out = elab(src);
    assert!(out.contains("let ?0 : U → U → U → U = λ x0 x1 x2. ?8 x1;\n"), "{out}");
    assert!(out.contains("let ?8 : (b : U) → U = ?;\n"), "{out}");
    // 剪枝产物：?1 的类型只剩 P (…b…)（a、c 被剪）
    assert!(
        out.contains("(P : U → U) → P (?8 b) → P (?8 b)"),
        "{out}"
    );
    assert_eq!(ty(src), "U\n");
    assert_parity(src);
}

/// pr1/pr2/pr3（README 例 4：需要剪枝的推断）——三例的推断类型全展开。
#[test]
fn pr1_pr2_pr3_inference() {
    assert_eq!(
        ty("let pr1 = \\ f x. f x;\npr1\n"),
        "(f : (x : ?5) → ?6 x)(x : ?5) → ?6 x\n"
    );
    assert_parity("let pr1 = \\ f x. f x;\npr1\n");
    // pr2：f 的类型经剪枝成多态函数，逐 meta 打印类型
    let out = elab("let pr2 = \\ f x y. f x y;\npr2\n");
    assert!(
        out.contains("let ?0 : U = (f : (x : ?6)(x' : ?10 x) → ?11 x x')(x : ?6)(y : ?10 x) → ?11 x y;\n"),
        "{out}"
    );
    assert_parity("let pr2 = \\ f x y. f x y;\npr2\n");
    // pr3：`λ f. f U`——f 的类型 meta 被剪 f 自身（?5 不含 f）
    assert_eq!(
        elab("let pr3 = \\ f. f U;\nU\n"),
        "let ?0 : U = (f : (x : U) → ?5 x) → ?5 U;\n\
         let ?1 : U = (x : U) → ?5 x;\n\
         let ?2 : (f : (x : U) → ?5 x) → U = λ f. U;\n\
         let ?3 : (f : (x : U) → ?5 x)(x : U) → U = λ f x. ?5 x;\n\
         let ?4 : U = U;\n\
         let ?5 : (x : U) → U = ?;\n\n\
         let pr3 : ?0\n  = λ f. f U;\n\nU\n"
    );
    assert_parity("let pr3 = \\ f. f U;\npr3\n");
}

// 上游示例套件与压力
// --------------------------------------------------------------------------------

#[test]
fn ex1_zoo_suite() {
    // 上游 05 Main.hs ex1 全套（nonlin 可解 + 交集剪枝 + pr1/pr2/pr3），
    // 顶层 U：type 模式打印 U。
    let out = ty(L05_pruning::EX1_SRC);
    assert_eq!(out, "U\n", "{out}");
    assert_parity(L05_pruning::EX1_SRC);
}

/// prune 负载 k=2（8 层非线性求解 + telescope 闭型），三模式与参考版一致；
/// 尾项 `t0` 的类型即首个非线性方程解出的 Π（验证多层求解稳定）。
#[test]
fn prune_workload_parity_small() {
    let src = fast::prune_src(2);
    assert_parity(&src);
    assert_eq!(
        ty(&src),
        "(a : U)(b : ?3 a)(P : (U → U → U) → U) → P (λ x0 x1. x1) → P (λ x y. y)\n"
    );
}

/// 深度压力：solve 负载在深栈线程里跑通（参考版 rename 沿 church 链递归）。
#[test]
fn deep_solve_under_big_stack() {
    let src = fast::solve_src(11);
    with_big_stack(move || {
        let s = src;
        assert_eq!(L05_pruning::main_with("type", &s), fast::main_with("type", &s));
    });
}

fn with_big_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(512 * 1024 * 1024)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

// 注：消融开关（L05_NO_CONV_MEMO / L05_NO_NAME_MAP）的「只影响性能、不影响
// 输出」契约由性能版内嵌互检测试覆盖；env 经 LazyLock 每进程只读一次。
