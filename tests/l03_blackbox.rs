//! L03_holes 黑盒测试套件。
//!
//! 被测对象：`src/L03_holes`（elaboration-zoo `03-holes` 的 Rust 移植：双向
//! elaboration + holes + pattern unification），唯一黑盒入口是
//! `main_with(mode, src)`（mode ∈ {--help, elab, nf, type}），经 `#[path]`
//! 独立编译进本测试 crate（`lib.rs` 里的私有 `mod`，集成测试无法直接引用；
//! 同 `tests/l02_blackbox.rs` 的做法）。
//!
//! 双 oracle：
//!   1. 期望输出字符串 —— 由 main.hs 语义 + 源码逐行推导，凡是整串断言处
//!      均已与实际输出核对（探针实测确认的字节），并与 L02 套件交叉印证；
//!   2. 参考版（`mod.rs`）↔ 性能版（`bump_spine_iter.rs`）**三模式**
//!      （nf/type/elab）逐字节互检 —— 两实现被承诺输出一致，任何一侧的
//!      回归都会在此暴露。
//!
//! 与 L02 的语义差别（本套件专门覆盖）：
//!   - `_` 在项位置是 hole（产生 meta），不再是尾随垃圾：`U _` 报
//!     Cannot unify（合成 Pi 与 U 无法合一），而 `U 1`、`U;` 仍是垃圾；
//!   - 顶层 λ 可推断（对定义域挂洞）：`\x. x` 的类型是 `(x : ?0) → ?0`；
//!   - let 体 λ 合法（L02 拒绝）：`let x : U = U; \A. A`。
//!   - 未解 meta 在 binder 下引读**不再 panic**（readme「已知限制」已过时），
//!     一律以 spine 应用形态显示：`λ x. ?2 x`、`(A : U) → ?0 A`。
//!   - 错误消息措辞：`Name not in scope: x` / `Cannot unify expected type…`
//!     （L02 是 `variable out of scope` / `type mismatch`）；错误列号按字节。
//!   - 消融环境变量 `L03_NO_CONV_MEMO` / `L03_NO_NAME_MAP` 只影响性能，
//!     逐字节输出不变（A/B 实验开关的非性能契约）。

#![feature(pattern)]

#[path = "../src/list.rs"]
mod list;

#[path = "../src/parser_lib.rs"]
mod parser_lib;

#[path = "../src/L02_tyck/mod.rs"]
mod L02_tyck;

#[path = "../src/L03_holes/mod.rs"]
mod L03_holes;

use L03_holes::bump_spine_iter as fast;

// helpers
// --------------------------------------------------------------------------------

fn nf(src: &str) -> String {
    L03_holes::main_with("nf", src)
}

fn ty(src: &str) -> String {
    L03_holes::main_with("type", src)
}

fn elab(src: &str) -> String {
    L03_holes::main_with("elab", src)
}

fn fast_nf(src: &str) -> String {
    fast::main_with("nf", src)
}

/// Oracle 2：参考版与性能版在全部三种模式下输出逐字节一致。
fn assert_parity(src: &str) {
    for mode in ["nf", "type", "elab"] {
        let b = L03_holes::main_with(mode, src);
        let f = fast::main_with(mode, src);
        assert_eq!(
            b, f,
            "{mode} 模式双实现不一致，src:\n{src}\n--- basic ---\n{b}--- fast ---\n{f}"
        );
    }
}

/// nf 模式输出 = `{nf}\n  :\n{type}\n`：断言 nf 输出以 type 模式输出结尾。
fn assert_nf_embeds_type(src: &str) {
    let t = ty(src);
    assert!(
        nf(src).ends_with(&format!("  :\n{t}")),
        "nf 输出未以 type 模式输出结尾：\nsrc:\n{src}\ntype:\n{t}\nnf:\n{}",
        nf(src),
    );
}

/// 报错输出：以 `(stdin):{line}:{col}:` 开头且包含消息片段。
fn assert_error_at(src: &str, line: usize, col: usize, needle: &str) {
    let out = nf(src);
    assert!(
        out.starts_with(&format!("(stdin):{line}:{col}:\n")),
        "错误位置不符：期望 ({line}:{col})，实际：\n{out}"
    );
    assert!(out.contains(needle), "错误消息缺 {needle:?}：\n{out}");
    assert_parity(src);
}

/// 在指定栈大小的线程里跑（深度负载：参考版 eval/quote/pretty 全是递归）。
fn with_big_stack(f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(512 * 1024 * 1024)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap();
}

/// church n 的 nf 文本（`λ N s z. s (s (… z))`，无尾换行）。
fn church_tm(n: usize) -> String {
    fn f(k: usize) -> String {
        match k {
            0 => "z".to_string(),
            1 => "s z".to_string(),
            k => format!("s ({})", f(k - 1)),
        }
    }
    format!("λ N s z. {}", f(n))
}

/// church n 的 nf 文本（带尾换行，与 `mod.rs::church_nf` 同形）。
fn church_nf_expect(n: usize) -> String {
    format!("{}\n", church_tm(n))
}

/// Nat 的类型文本（`(N : U) → (N → N) → N → N`）。
fn nat_type() -> &'static str {
    "(N : U) → (N → N) → N → N"
}

/// Eq 型负载（conv/solve 系）的期望 nf：`λ P px. px`，
/// 类型 `(P : (Nat) → U) → P (church n) → P (church n)`。
fn eq_battery_expect(n: usize) -> String {
    format!(
        "λ P px. px\n  :\n(P : ({nat}) → U) → P ({ch}) → P ({ch})\n",
        nat = nat_type(),
        ch = church_tm(n),
    )
}

const HELP: &str = "usage: elabzoo-holes [--help|elab|nf|type]\n  --help : display this message\n  elab   : read & elaborate expression from stdin\n  nf     : read & typecheck expression from stdin, print its normal form and type\n  type   : read & typecheck expression from stdin, print its type\n";

// 模式与输出格式
// --------------------------------------------------------------------------------

#[test]
fn help_and_unknown_modes() {
    for mode in ["--help", "", "bogus", "foo", "ELAB", "-h"] {
        assert_eq!(L03_holes::main_with(mode, ""), HELP, "mode {mode:?}");
        assert_eq!(fast::main_with(mode, ""), HELP, "fast mode {mode:?}");
    }
}

#[test]
fn type_mode_prints_type_only() {
    assert_eq!(ty("U"), "U\n");
    assert_eq!(ty("(A : U) -> A -> A"), "U\n");
    // 顶层洞：类型本身是 ?0
    assert_eq!(ty("_"), "?0\n");
    // 顶层 λ：定义域挂洞（L03 新行为，L02 在此报错）
    assert_eq!(ty("\\x. x"), "(x : ?0) → ?0\n");
}

#[test]
fn nf_mode_prints_normal_form_and_type() {
    assert_eq!(nf("U"), "U\n  :\nU\n");
    assert_eq!(nf("(A : U) -> A -> A"), "(A : U) → A → A\n  :\nU\n");
    // 顶层洞：项 meta ?1 与类型 meta ?0 均未解
    assert_eq!(nf("_"), "?1\n  :\n?0\n");
}

#[test]
fn nf_output_embeds_type_mode_output() {
    for src in [
        "U",
        "(A : U) -> A -> A",
        "_",
        "\\x. x",
        "let id : (A : U) -> A -> A = \\A x. x;\nid _ _",
        "let f : U -> U = \\x. _; f U",
        L03_holes::EX1_SRC,
        L03_holes::EX2_SRC,
        "let Nat : U = (N : U) -> (N -> N) -> N -> N;\nlet two : Nat = \\N s z. s (s z);\ntwo",
        "let g : (w : U) -> _ = \\w. _;\ng U",
    ] {
        assert_nf_embeds_type(src);
    }
}

#[test]
fn elab_mode_prints_metacontext_then_term() {
    // 无洞程序：metacontext 空（一个空行），随后是展开的核心项。
    assert_eq!(elab("U"), "\nU\n");
    // 顶层洞：两个未解 meta，末尾再一个换行。
    assert_eq!(elab("_"), "let ?0 = ?;\nlet ?1 = ?;\n\n?1\n");
    // 已解 meta：`let ?m = <nf>;`，项里引用
    assert_eq!(elab("let x : U = _; x"), "let ?0 = ?;\n\nlet x : U\n  = ?0;\n\nx\n");
}

#[test]
fn parse_error_output_is_plain_line() {
    for src in ["", "   \n\t", "-- just a comment\n", "{- block -}", "\n\n"] {
        assert_eq!(nf(src), "parse error\n", "src: {src:?}");
        assert_eq!(ty(src), "parse error\n", "src: {src:?}");
        assert_eq!(elab(src), "parse error\n", "src: {src:?}");
        assert_parity(src);
    }
}

// 词法与解析
// --------------------------------------------------------------------------------

#[test]
fn lambda_prefixes_are_equivalent() {
    let src = "let id : (A : U) -> A -> A = \\A x. x;\nid";
    let src2 = "let id : (A : U) -> A -> A = λA x. x;\nid";
    assert_eq!(nf(src), nf(src2));
    assert_eq!(nf(src), "λ A x. x\n  :\n(A : U) → A → A\n");
}

#[test]
fn unicode_lambda_top_level_is_well_typed() {
    // L03 对顶层 λ 挂洞推断（L02 报 Can't infer）；`λx` 无需空格。
    assert_eq!(nf("λx. x"), "λ x. x\n  :\n(x : ?0) → ?0\n");
    assert_eq!(nf("λx y. x"), "λ x y. x\n  :\n(x : ?0)(y : ?1 x) → ?0\n");
}

#[test]
fn multi_binder_lam_desugars_to_nested() {
    let a = "let id : (A : U) -> A -> A = \\A x. x;\nid";
    let b = "let id : (A : U) -> A -> A = \\A. \\x. x;\nid";
    assert_eq!(nf(a), nf(b));
}

#[test]
fn pi_multi_binder_parens() {
    assert_eq!(
        nf("(A B : U) -> A -> B -> A"),
        "(A : U)(B : U) → A → B → A\n  :\nU\n"
    );
    assert_eq!(ty("(A B : U) -> A -> B -> A"), "U\n");
}

#[test]
fn unannotated_arrow_is_underscore_pi() {
    // `A -> B` ≡ `(_ : A) -> B`；`_` 在 binder 位置只是名字，不建 meta。
    assert_eq!(nf("U -> U"), "U → U\n  :\nU\n");
    assert_eq!(nf("(_ : U) -> U"), "U → U\n  :\nU\n");
}

#[test]
fn line_comment_between_tokens() {
    assert_eq!(nf("U -- trailing comment\n"), "U\n  :\nU\n");
    assert_eq!(nf("-- leading\nU"), "U\n  :\nU\n");
}

#[test]
fn block_comment_handling() {
    assert_eq!(nf("{- c -} U"), "U\n  :\nU\n");
    // mid 注释把 `U {- c -} U` 连成应用 → Cannot unify（合成 Pi vs U）
    assert_eq!(
        nf("U {- c -} U"),
        "(stdin):1:1:\n  |\n1 | U {- c -} U\n  | ^\nCannot unify expected type\n\n  (x : ?0) → ?1 x\n\nwith inferred type\n\n  U\n"
    );
}

#[test]
fn unclosed_block_comment_swallows_rest_of_input() {
    assert_eq!(nf("{- oops"), "parse error\n");
    assert_eq!(nf("U {- oops"), "U\n  :\nU\n");
}

#[test]
fn underscore_binder_position_is_not_a_hole() {
    assert_eq!(
        nf("let f : U -> U -> U = \\x _. x;\nf"),
        "λ x _. x\n  :\nU → U → U\n"
    );
    assert_eq!(ty("let f : U -> U -> U = \\x _. x;\nf"), "U → U → U\n");
    assert_eq!(nf("let _ : U = U; U"), "U\n  :\nU\n");
}

#[test]
fn underscore_in_term_position_is_a_hole() {
    // 与 L02 的关键区别：`U _` 是应用 U 到 hole → Cannot unify（合成 Pi），
    // 不再被当作尾随垃圾。
    assert_error_at("U _", 1, 1, "Cannot unify expected type");
}

#[test]
fn trailing_junk_tokens_are_silently_ignored() {
    for junk in ["U 1", "U;", "U 1 2", "U +", "U → U", "U (", "U {- c -}"] {
        assert_eq!(nf(junk), "U\n  :\nU\n", "junk: {junk:?}");
        assert_eq!(ty(junk), "U\n", "junk: {junk:?}");
    }
}

#[test]
fn parse_error_battery() {
    for src in [
        "(",
        ")",
        "\\x.",
        "\\1. x",
        "let x : U = U;",
        "let x : U = ; x",
        "let x : U = U;; x",
        "let x : U = U x",
        "(U : U) -> U",
        "let U : U = U; U",
        "\\U. U",
        "[",
        "(x : U -> ",
        "let x : U = ",
        "let x : ",
        "let",
    ] {
        assert_eq!(nf(src), "parse error\n", "src: {src:?}");
        assert_eq!(ty(src), "parse error\n", "src: {src:?}");
        assert_eq!(elab(src), "parse error\n", "src: {src:?}");
    }
}

#[test]
fn parens_nest() {
    assert_eq!(nf("((((U))))"), "U\n  :\nU\n");
}

#[test]
fn let_sets_do_not_need_spaces() {
    assert_eq!(nf("let x : U = U;let y : U = x;y"), "U\n  :\nU\n");
    // elab 下 let 链格式化输出
    assert_eq!(
        elab("let x : U = U;let y : U = x;y"),
        "\nlet x : U\n  = U;\n\nlet y : U\n  = x;\n\ny\n"
    );
}

// 洞的基础行为（L03 核心）
// --------------------------------------------------------------------------------

#[test]
fn hole_in_type_annotation_gets_solved() {
    // `let x : _ = U; x`：注解里的洞与 U 合一 → ?0 := U
    assert_eq!(nf("let x : _ = U; x"), "U\n  :\nU\n");
    assert_eq!(
        elab("let x : _ = U; x"),
        "let ?0 = U;\n\nlet x : ?0\n  = U;\n\nx\n"
    );
}

#[test]
fn hole_type_solved_to_nat() {
    let src = "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
               let two : Nat = \\N s z. s (s z);\n\
               let x : _ = two; x";
    assert_eq!(
        nf(src),
        "λ N s z. s (s z)\n  :\n(N : U) → (N → N) → N → N\n"
    );
    assert_eq!(
        elab(src),
        "let ?0 = (N : U) → (N → N) → N → N;\n\n\
         let Nat : U\n  = (N : U) → (N → N) → N → N;\n\n\
         let two : Nat\n  = λ N s z. s (s z);\n\n\
         let x : ?0\n  = two;\n\nx\n"
    );
}

#[test]
fn hole_as_function_argument_unsolved() {
    // `id _ _`：两个实参洞都未解 → nf 里直接显示 meta
    let src = "let id : (A : U) -> A -> A = \\A x. x;\nid _ _";
    assert_eq!(nf(src), "?1\n  :\n?0\n");
    assert_eq!(elab(src), "let ?0 = ?;\nlet ?1 = ?;\n\nlet id : (A : U) → A → A\n  = λ A x. x;\n\nid ?0 ?1\n");
    // `id _`：类型洞未解，cod 出现两次 → ?0 → ?0
    let src1 = "let id : (A : U) -> A -> A = \\A x. x;\nid _";
    assert_eq!(nf(src1), "λ x. x\n  :\n?0 → ?0\n");
}

#[test]
fn hole_in_let_type_annotation() {
    let src = "let id : (A : U) -> A -> A = \\A x. x;\nlet y : _ = id; y";
    assert_eq!(nf(src), "λ A x. x\n  :\n(A : U) → A → A\n");
    // 洞解为 id 的完整类型
    assert_eq!(
        elab(src),
        "let ?0 = (A : U) → A → A;\n\n\
         let id : (A : U) → A → A\n  = λ A x. x;\n\n\
         let y : ?0\n  = id;\n\ny\n"
    );
}

#[test]
fn hole_in_type_argument() {
    // `nil _`：List 的类型实参挂洞，与 nil 的注解合一
    let src = "let List : U -> U = \\A. (L : _) -> (A -> L -> L) -> L -> L;\n\
               let nil : (A : _) -> List A = \\A L c n. n;\n\
               nil _";
    assert_eq!(
        nf(src),
        "λ L c n. n\n  :\n(L : U) → (?2 → L → L) → L → L\n"
    );
    assert_eq!(
        elab(src),
        "let ?0 = λ x1. U;\nlet ?1 = U;\nlet ?2 = ?;\n\n\
         let List : U → U\n  = λ A. (L : ?0 A) → (A → L → L) → L → L;\n\n\
         let nil : (A : ?1) → List A\n  = λ A L c n. n;\n\n\
         nil ?2\n"
    );
}

#[test]
fn hole_with_dependent_type() {
    let src = "let f : (A : U) -> (x : A) -> A = \\A x. x;\nlet y : _ = f U; y";
    assert_eq!(nf(src), "λ x. x\n  :\n(x : U) → U\n");
    assert_eq!(
        elab(src),
        "let ?0 = (x : U) → U;\n\n\
         let f : (A : U)(x : A) → A\n  = λ A x. x;\n\n\
         let y : ?0\n  = f U;\n\ny\n"
    );
    let src2 = "let f : (A : U) -> (x : A) -> A = \\A x. x;\nlet y : _ = f U U; y";
    assert_eq!(nf(src2), "U\n  :\nU\n");
    assert!(elab(src2).starts_with("let ?0 = U;\n\n"));
}

#[test]
fn top_level_lambda_infers_meta_type() {
    assert_eq!(nf("\\x. x"), "λ x. x\n  :\n(x : ?0) → ?0\n");
    assert_eq!(nf("\\x y z. z"), "λ x y z. z\n  :\n(x : ?0)(y : ?1 x)(z : ?2 x y) → ?2 x y\n");
    // 多 binder 的 cod meta 依次 spine 应用
    assert_eq!(nf("\\x y. x"), "λ x y. x\n  :\n(x : ?0)(y : ?1 x) → ?0\n");
}

#[test]
fn unsolved_hole_under_binder_quotes_with_spine() {
    // readme「已知限制」已过时：未解洞在 binder 下不再 panic，
    // 引读为 meta + spine 应用形态。
    assert_eq!(nf("\\x. _"), "λ x. ?2 x\n  :\n(x : ?0) → ?1 x\n");
    // check 走廊（有注解）下 spine 只挂 binder 变量
    assert_eq!(
        nf("let f : U -> U = \\x. _; f"),
        "λ x. ?0 x\n  :\nU → U\n"
    );
    // 应用后 spine 挂上实参
    assert_eq!(nf("let f : U -> U = \\x. _; f U"), "?0 U\n  :\nU\n");
    // Pi 余定义域挂洞
    assert_eq!(nf("(A : U) -> _"), "(A : U) → ?0 A\n  :\nU\n");
    // 洞作整个值
    assert_eq!(nf("let x : U -> U = _; x"), "?0\n  :\nU → U\n");
}

#[test]
fn hole_applied_to_bound_var_elaborates_spine() {
    // `f _`（f 的函数类型下）：洞 meta 挂上 binder 实参
    let src = "let bad : (U -> U) -> U = \\f. f _; bad (\\x. x)";
    assert_eq!(nf(src), "?0 (λ x. x)\n  :\nU\n");
    assert_eq!(
        elab(src),
        "let ?0 = ?;\n\nlet bad : (U → U) → U\n  = λ f. f (?0 f);\n\nbad (λ x. x)\n"
    );
}

#[test]
fn hole_let_value_unsolved() {
    let src = "let x : U = _; x";
    assert_eq!(nf(src), "?0\n  :\nU\n");
    assert_eq!(elab(src), "let ?0 = ?;\n\nlet x : U\n  = ?0;\n\nx\n");
}

#[test]
fn hole_in_annotation_with_body() {
    // `_ -> _` 洞只做 dom/cod 类型；洞值在 lambda 体
    let src = "let f : _ -> _ = \\x. _; f";
    assert_eq!(nf(src), "λ x. ?2 x\n  :\n?0 → ?1 _\n");
    // `_ -> U`：dom 是洞
    assert_eq!(nf("_ -> U"), "?0 → U\n  :\nU\n");
    // `U -> _`：cod 洞挂匿名 binder
    assert_eq!(nf("U -> _"), "U → ?0 _\n  :\nU\n");
    // 洞在 arrow 里的类型与 U 无法合一
    assert_error_at("let x : _ -> _ = U; x", 1, 18, "?0 → ?1 _");
}

// 求解：pattern unification
// --------------------------------------------------------------------------------

#[test]
fn ex0_elab_solves_id2_hole() {
    // 上游注释示例：`id _ x` 的洞解为 `λ x1 x2. x1`（即 `?0 A x ≡ x` 的
    // 反解），elab 输出的 metacontext 与展开项都是金样。
    assert_eq!(
        L03_holes::ex0(),
        "let ?0 = λ x1 x2. x1;\n\n\
         let id : (A : U) → A → A\n  = λ A x. x;\n\n\
         let id2 : (A : U) → A → A\n  = λ A x. id (?0 A x) x;\n\n\
         U\n"
    );
}

#[test]
fn ex1_nf_solves_type_hole() {
    // `id _ two`：类型洞解为 Nat，项归约为 two 本身。
    assert_eq!(
        L03_holes::ex1(),
        "λ N s z. s (s z)\n  :\n(N : U) → (N → N) → N → N\n"
    );
}

#[test]
fn ex2_nf_solves_holes_in_cod() {
    // church 编码全用 `_` 注类型洞：eqTest 的 nf 里 P hundred 出现两次
    // （hundred = mul ten ten = church 100 的完整展开）。
    let ch = church_tm(100);
    let expect = format!(
        "λ P px. px\n  :\n(P : ({nat}) → U) → P ({ch}) → P ({ch})\n",
        nat = nat_type(),
        ch = ch,
    );
    assert_eq!(L03_holes::ex2(), expect);
}

#[test]
fn solve_refl_holes() {
    // `Eq _ p1 p1 = refl _ _`：三个洞（类型 ×2 + 值）全解；
    // 解的 nf 用 metacontext 打印（fresh 名字 x1 x2 x3）。
    let src = "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
               let zero : Nat = \\N s z. z;\n\
               let add : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z);\n\
               let Eq : (A : U) -> A -> A -> U = \\A x y. (P : A -> U) -> P x -> P y;\n\
               let refl : (A : U) -> (x : A) -> Eq A x x = \\A x P px. px;\n\
               let p0 : Nat = \\N s z. s (s z);\n\
               let p1 : Nat = add p0 p0;\n\
               let eqTest : Eq _ p1 p1 = refl _ _;\n\
               eqTest";
    assert_eq!(nf(src), eq_battery_expect(4));
    assert_eq!(ty(src), format!(
        "(P : ({nat}) → U) → P {ch0} → P {ch0}\n",
        nat = nat_type(),
        ch0 = format!("({})", church_tm(4)),
    ));
    // elab：?0/?1 解为 Nat 类型，?2 解为 church 4（fresh 名）
    assert_eq!(
        elab(src),
        "let ?0 = (N : U) → (N → N) → N → N;\n\
         let ?1 = (N : U) → (N → N) → N → N;\n\
         let ?2 = λ x1 x2 x3. x2 (x2 (x2 (x2 x3)));\n\n\
         let Nat : U\n  = (N : U) → (N → N) → N → N;\n\n\
         let zero : Nat\n  = λ N s z. z;\n\n\
         let add : Nat → Nat → Nat\n  = λ a b N s z. a N s (b N s z);\n\n\
         let Eq : (A : U) → A → A → U\n  = λ A x y. (P : A → U) → P x → P y;\n\n\
         let refl : (A : U)(x : A) → Eq A x x\n  = λ A x P px. px;\n\n\
         let p0 : Nat\n  = λ N s z. s (s z);\n\n\
         let p1 : Nat\n  = add p0 p0;\n\n\
         let eqTest : Eq ?0 p1 p1\n  = refl ?1 ?2;\n\n\
         eqTest\n"
    );
}

#[test]
fn flex_flex_same_sign_regression() {
    // 同号 flex-flex 回归（commit e541de0）：`g w` 在 cod 位置被两处独立
    // 求值，同一未解 meta 以两个同实参 spine 在 check fallthrough 的 unify
    // 相遇——必须逐实参比较，不能误入 solve（occurs check 对同号必败）。
    let src = "let g : (w : U) -> _ = \\w. _;\n\
               let f : (w : U) -> U -> g w = \\w x. _;\n\
               let test : (w : U) -> U -> g w = \\w x. f w x;\n\
               test";
    assert_eq!(nf(src), "λ w x. ?2 w x\n  :\n(w : U) → U → ?1 w\n");
    assert_eq!(
        elab(src),
        "let ?0 = λ x1. U;\nlet ?1 = ?;\nlet ?2 = ?;\n\n\
         let g : (w : U) → ?0 w\n  = λ w. ?1 w;\n\n\
         let f : (w : U) → U → g w\n  = λ w x. ?2 w x;\n\n\
         let test : (w : U) → U → g w\n  = λ w x. f w x;\n\n\
         test\n"
    );
}

#[test]
fn non_pattern_spine_leaves_meta_unsolved() {
    // `f (f U)`：f 的类型洞挂上非变量 spine —— 非模式方程，解不了但
    // 不报错（读作「悬念」）：nf 里 meta 以 spine 形态原样展开.
    let src = "let f : (A : U) -> A = \\A. _;\nf (f U)";
    assert_eq!(nf(src), "?0 (?0 U)\n  :\n?0 U\n");
    assert_eq!(elab(src), "let ?0 = ?;\n\nlet f : (A : U) → A\n  = λ A. ?0 A;\n\nf (f U)\n");
}

#[test]
fn occurs_check_scoped_loop_keeps_meta() {
    // `z = \A. f A` 与 f 的洞类型互相引用：解不闭合（自由变量在解里），
    // 保持未解而不报错。
    let src = "let f : (A : U) -> A = \\A. _;\n\
               let z : (A : U) -> A = \\A. f A;\nz";
    assert_eq!(nf(src), "λ A. ?0 A\n  :\n(A : U) → A\n");
    assert_eq!(
        elab(src),
        "let ?0 = ?;\n\n\
         let f : (A : U) → A\n  = λ A. ?0 A;\n\n\
         let z : (A : U) → A\n  = λ A. f A;\n\nz\n"
    );
}

#[test]
fn hole_in_cod_unifies_with_use() {
    // `h U (g U)`：余定义域洞（g 的 cod）与实参类型对不上 → Cannot unify，
    // 期望侧显示 spine 形态 `?1 U`。
    let src = "let g : (w : U) -> _ = \\w. _;\n\
               let h : (w : U) -> g w -> U = \\w x. U;\n\
               h U (g U)";
    assert_error_at(src, 3, 6, "Cannot unify expected type");
    let out = nf(src);
    assert!(out.contains("  ?1 U\n\nwith inferred type\n\n  U\n"), "{out}");
}

#[test]
fn self_application_fails_synthesized_pi() {
    // `\x. x x`：对洞类型应用 → 合成 Pi 与洞类型合一失败。
    let src = "\\x. x x";
    assert_eq!(
        nf(src),
        "(stdin):1:5:\n  |\n1 | \\x. x x\n  |     ^\nCannot unify expected type\n\n  (x' : ?1 x) → ?2 x x'\n\nwith inferred type\n\n  ?0\n"
    );
    assert_parity(src);
}

#[test]
fn hole_in_function_position_synthesizes_pi() {
    // `\f. f _`：洞作函数（头），f 的类型为洞 → 合成 Pi 失败。
    let src = "\\f. f _";
    assert_eq!(
        nf(src),
        "(stdin):1:5:\n  |\n1 | \\f. f _\n  |     ^\nCannot unify expected type\n\n  (x : ?1 f) → ?2 f x\n\nwith inferred type\n\n  ?0\n"
    );
    assert_parity(src);
}

#[test]
fn lambda_under_pi_body_hole_ok() {
    // `\g. g _` 在 (U -> U) -> U 下：洞挂 binder 实参，整体良构。
    let src = "let f : ((U -> U) -> U) -> U = \\g. g _; f (\\x. U)";
    assert_eq!(nf(src), "U\n  :\nU\n");
    assert_eq!(
        elab(src),
        "let ?0 = ?;\n\nlet f : ((U → U) → U) → U\n  = λ g. g (?0 g);\n\nf (λ x. U)\n"
    );
}

// 错误报告
// --------------------------------------------------------------------------------

#[test]
fn name_not_in_scope() {
    assert_eq!(
        nf("id"),
        "(stdin):1:1:\n  |\n1 | id\n  | ^\nName not in scope: id\n"
    );
    let out = nf("let x : U = U;\nlet y : U = z;\ny");
    assert!(out.starts_with("(stdin):2:13:\n"), "{out}");
    assert!(out.contains("Name not in scope: z"), "{out}");
}

#[test]
fn name_not_in_scope_in_pi_cod() {
    assert_eq!(
        nf("(A : U) -> x"),
        "(stdin):1:12:\n  |\n1 | (A : U) -> x\n  |            ^\nName not in scope: x\n"
    );
}

#[test]
fn cannot_unify_broken_composition() {
    // `id id` 在 U 目标下：期望 U，推断多态 Pi。
    let src = "let id : (A : U) -> A -> A\n  = \\A x. x;\nlet bar : U = id id;\nbar";
    assert_eq!(
        nf(src),
        "(stdin):3:18:\n  |\n3 | let bar : U = id id;\n  |                  ^\nCannot unify expected type\n\n  U\n\nwith inferred type\n\n  (A : U) → A → A\n"
    );
}

#[test]
fn cannot_unify_with_unicode_before_caret() {
    // caret 列按字节算：`λ` 占 2 字节，caret 视觉右移 1 列（套件文档怪癖）。
    let src = "let id : (A : U) -> A -> A = λA x. x; id id";
    assert_eq!(
        nf(src),
        "(stdin):1:43:\n  |\n1 | let id : (A : U) -> A -> A = λA x. x; id id\n  |                                           ^\nCannot unify expected type\n\n  U\n\nwith inferred type\n\n  (A : U) → A → A\n"
    );
}

#[test]
fn cannot_unify_argument_domain() {
    let src = "let f : U -> U = \\A. A;\nf f";
    assert_eq!(
        nf(src),
        "(stdin):2:3:\n  |\n2 | f f\n  |   ^\nCannot unify expected type\n\n  U\n\nwith inferred type\n\n  U → U\n"
    );
}

#[test]
fn cannot_unify_let_value() {
    let src = "let f : U -> U = U; f";
    assert_eq!(
        nf(src),
        "(stdin):1:18:\n  |\n1 | let f : U -> U = U; f\n  |                  ^\nCannot unify expected type\n\n  U → U\n\nwith inferred type\n\n  U\n"
    );
}

#[test]
fn cannot_unify_lambda_against_non_pi() {
    // λ 的目标类型不是 Pi → 合成 Pi 无法与 U 合一（L02 此处报 Can't infer）。
    let src = "let bad : U = \\x. x; bad";
    assert_eq!(
        nf(src),
        "(stdin):1:15:\n  |\n1 | let bad : U = \\x. x; bad\n  |               ^\nCannot unify expected type\n\n  U\n\nwith inferred type\n\n  (x : ?0) → ?0\n"
    );
    assert_parity(src);
}

#[test]
fn cannot_unify_under_lambda_body() {
    // 错在 λ 体里的 `x x`（L03 强调：洞插入不会让自应用通过）。
    let src = "let f : U -> U = \\x. x x; f";
    assert_eq!(
        nf(src),
        "(stdin):1:22:\n  |\n1 | let f : U -> U = \\x. x x; f\n  |                      ^\nCannot unify expected type\n\n  (x' : ?0 x) → ?1 x x'\n\nwith inferred type\n\n  U\n"
    );
    assert_parity(src);
}

#[test]
fn cannot_unify_synthesized_pi_against_U() {
    // `U U` / `U _`：头推断为 U（非 Pi）→ 合成 Pi 与 U 合一失败。
    let expect = "(stdin):1:1:\n  |\n1 | {src}\n  | ^\nCannot unify expected type\n\n  (x : ?0) → ?1 x\n\nwith inferred type\n\n  U\n";
    for src in ["U U", "U _"] {
        let golden = expect.replace("{src}", src);
        assert_eq!(nf(src), golden, "src: {src}");
    }
}

#[test]
fn cannot_unify_equal_argument() {
    // `Eq U U (U -> U)` 下 refl：两个被比较项不相等。
    let src = "let Eq : (A : U) -> A -> A -> U = \\A x y. (P : A -> U) -> P x -> P y;\n\
               let eqT : Eq U U (U -> U) = \\P px. px;\neqT";
    assert_eq!(
        nf(src),
        "(stdin):2:36:\n  |\n2 | let eqT : Eq U U (U -> U) = \\P px. px;\n  |                                    ^\nCannot unify expected type\n\n  P (U → U)\n\nwith inferred type\n\n  P U\n"
    );
}

#[test]
fn error_position_multiline() {
    let src = "let id : (A : U) -> A -> A\n  = \\A x. x;\nid id";
    let out = nf(src);
    assert!(out.starts_with("(stdin):3:4:\n"), "{out}");
    assert!(out.contains("3 | id id\n  |    ^"), "{out}");
    assert_parity(src);
}

#[test]
fn name_not_in_scope_in_application() {
    // `_ y`：洞是合法头，y 未定义 → 名字错误（caret 在 y）。
    let src = "\\x. _ y";
    assert_eq!(
        nf(src),
        "(stdin):1:7:\n  |\n1 | \\x. _ y\n  |       ^\nName not in scope: y\n"
    );
    assert_parity(src);
}

// 良构程序（精确定值）
// --------------------------------------------------------------------------------

#[test]
fn id_const_application() {
    assert_eq!(
        nf("let id : (A : U) -> A -> A\n      = \\A x. x;\nlet const : (A B : U) -> A -> B -> A\n      = \\A B x y. x;\nid ((A B : U) -> A -> B -> A) const"),
        "λ A B x y. x\n  :\n(A : U)(B : U) → A → B → A\n"
    );
}

#[test]
fn type_application_polymorphism() {
    let src = "let id : (A : U) -> A -> A = \\A x. x;\nid ((A : U) -> A -> A) (\\A x. x)";
    assert_eq!(nf(src), "λ A x. x\n  :\n(A : U) → A → A\n");
}

#[test]
fn eta_wrapped_definition_normalizes() {
    let src = "let id : (A : U) -> A -> A = \\A x. x;\n\
               let g : (A : U) -> A -> A = \\A. id A;\ng";
    assert_eq!(nf(src), "λ A x. x\n  :\n(A : U) → A → A\n");
}

#[test]
fn dependent_substitution() {
    let src = "let f : (A : U) -> (x : A) -> A = \\A x. x;\nf";
    assert_eq!(nf(src), "λ A x. x\n  :\n(A : U)(x : A) → A\n");
    assert_eq!(
        nf("let f : (A : U) -> (x : A) -> A = \\A x. x;\nf (U -> U) (\\A. A)"),
        "λ A. A\n  :\nU → U\n"
    );
}

#[test]
fn church_numerals_raw() {
    let nat = "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
               let zero : Nat = \\N s z. z;\n\
               let one : Nat = \\N s z. s z;\n\
               let two : Nat = \\N s z. s (s z);\ntwo";
    assert_eq!(
        nf(nat),
        "λ N s z. s (s z)\n  :\n(N : U) → (N → N) → N → N\n"
    );
    // raw add：`add (\N s z. s z) (\N s z. s (s z))` = church 3
    let add = "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
               let add : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z);\n\
               add (\\N s z. s z) (\\N s z. s (s z))";
    assert_eq!(nf(add), "λ N s z. s (s (s z))\n  :\n(N : U) → (N → N) → N → N\n");
}

#[test]
fn composition_application() {
    let src = "let comp : (U -> U) -> (U -> U) -> U -> U = \\f g x. f (g x);\n\
               comp (\\x. x) (\\x. x) U";
    assert_eq!(nf(src), "U\n  :\nU\n");
}

#[test]
fn lambda_shadowing_fresh_names() {
    assert_eq!(nf("let f : U -> U -> U = \\x x. x;\nf"), "λ x x'. x'\n  :\nU → U → U\n");
    assert_eq!(nf("(x : U) -> (x : U) -> x"), "(x : U)(x' : U) → x'\n  :\nU\n");
}

#[test]
fn let_shadowing_refers_to_outer_in_value() {
    assert_eq!(nf("let x : U = U;\nlet x : U = x;\nx"), "U\n  :\nU\n");
    // elab 里第二个 x 换名 x'，值仍是外层 x
    assert_eq!(
        elab("let x : U = U;\nlet x : U = x;\nx"),
        "\nlet x : U\n  = U;\n\nlet x' : U\n  = x;\n\nx'\n"
    );
}

#[test]
fn lambda_in_let_body_now_legal() {
    // L02 拒绝（infer λ 报错），L03 挂洞接受——行为差异的锚点。
    let src = "let x : U = U; \\A. A";
    assert_eq!(nf(src), "λ A. A\n  :\n(A : ?0) → ?0\n");
    assert_eq!(
        elab(src),
        "let ?0 = ?;\n\nlet x : U\n  = U;\n\nλ A. A\n"
    );
}

#[test]
fn nf_no_let_apparatus() {
    assert_eq!(nf("let x : U = U;\nlet y : U -> U = \\A. x;\ny"), "λ A. U\n  :\nU → U\n");
}

// 双实现互检（回归 oracle）
// --------------------------------------------------------------------------------

#[test]
fn parity_well_typed_with_holes_battery() {
    for src in [
        "U",
        "(A : U) -> A -> A",
        "_",
        "\\x. x",
        "\\x y z. z",
        "let x : U = _; x",
        "let x : _ = U; x",
        "let id : (A : U) -> A -> A = \\A x. x;\nid _ _",
        "let id : (A : U) -> A -> A = \\A x. x;\nid _",
        "let f : U -> U = \\x. _; f U",
        "(A : U) -> _",
        "U -> _",
        "_ -> U",
        "let g : (w : U) -> _ = \\w. _;\ng U",
        "let x : _ -> U = \\y. y; x U",
        L03_holes::EX0_SRC,
        L03_holes::EX1_SRC,
        L03_holes::EX2_SRC,
        "let List : U -> U = \\A. (L : _) -> (A -> L -> L) -> L -> L;\n\
         let nil : (A : _) -> List A = \\A L c n. n;\nnil _",
        "let g : (w : U) -> _ = \\w. _;\n\
         let f : (w : U) -> U -> g w = \\w x. _;\n\
         let test : (w : U) -> U -> g w = \\w x. f w x;\ntest",
        "let f : (A : U) -> A = \\A. _;\nf (f U)",
        "let f : (A : U) -> A = \\A. _;\nlet z : (A : U) -> A = \\A. f A;\nz",
        "let f : ((U -> U) -> U) -> U = \\g. g _; f (\\x. U)",
        "let bad : (U -> U) -> U = \\f. f _; bad (\\x. x)",
        "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
         let two : Nat = \\N s z. s (s z);\nlet x : _ = two; x",
        "let f : (A : U) -> (x : A) -> A = \\A x. x;\nlet y : _ = f U; y",
        "let f : (A : U) -> (x : A) -> A = \\A x. x;\nlet y : _ = f U U; y",
        "let f : _ -> _ = \\x. _; f",
        "let x : U = U; _ x",
        "let x : U = U; \\A. A",
        "let ev : (A : U) -> A -> A = \\A x. _; ev U",
        "let x : U -> U = _; x",
        "let Nat : U = (N : U) -> (N -> N) -> N -> N;\nlet x : Nat = _; x",
        "let f : U -> U -> U = \\x _. x;\nf",
        "let id : (A : U) -> A -> A = \\A x. x;\nlet g : (A : U) -> A -> A = \\A. id A;\ng",
        "let comp : (U -> U) -> (U -> U) -> U -> U = \\f g x. f (g x);\n\
         comp (\\x. x) (\\x. x) U",
        "let f : (A : U) -> (x : A) -> A = \\A x. x;\nf (U -> U) (\\A. A)",
        "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
         let add : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z);\n\
         add (\\N s z. s z) (\\N s z. s (s z))",
        "let f : U -> U -> U = \\x x. x;\nf",
        "(x : U) -> (x : U) -> x",
        "let x : U = U;\nlet x : U = x;\nx",
        "let id : (A : U) -> A -> A\n  = \\A x. x;\nlet id2 : (A : U) -> A -> A = \\A x. id _ x;\nU",
        "((((U))))",
        "{- c -} let x : U = _; -- mid\nx",
    ] {
        assert_parity(src);
    }
}

#[test]
fn parity_error_battery() {
    for src in [
        "U U",
        "U _",
        "U {- c -} U",
        "\\x. x x",
        "\\f. f _",
        "let x : _ -> _ = U; x",
        "let f : U -> U = U; f",
        "let f : U -> U = \\A. A;\nf f",
        "let bad : U = \\x. x; bad",
        "let f : U -> U = \\x. x x; f",
        "let x : U = U; let y : U = z; y",
        "id",
        "(A : U) -> x",
        "\\x. _ y",
        "let id : (A : U) -> A -> A = \\A x. x;\nid (U -> U) id",
        "let g : (w : U) -> _ = \\w. _;\n\
         let h : (w : U) -> g w -> U = \\w x. U;\nh U (g U)",
        "let id : (A : U) -> A -> A = λA x. x; id id",
        "let Eq : (A : U) -> A -> A -> U = \\A x y. (P : A -> U) -> P x -> P y;\n\
         let eqT : Eq U U (U -> U) = \\P px. px;\neqT",
        "let id : (A : U) -> A -> A\n  = \\A x. x;\nlet bar : U = id id;\nbar",
    ] {
        assert_parity(src);
    }
}

#[test]
fn parity_parse_error_battery() {
    for src in [
        "",
        "   ",
        "(",
        "\\x.",
        "\\1. x",
        "let x : U = U;",
        "let x : U = U;; x",
        "(U : U) -> U",
        "let U : U = U; U",
        "{- oops",
        "let x : U = ; x",
        "(x : U -> ",
        "let x : U = ",
        "let x : ",
        "let",
    ] {
        assert_parity(src);
    }
}

#[test]
fn parity_unicode_and_comments() {
    for src in [
        "let id : (A : U) -> A -> A = λA x. x;\nid",
        "λx. x",
        "λx y. x",
        "{- 中文注释 -} let x : U = _; -- 行注释\nx",
        "U → U",
        "{- c -} U",
        "U {- oops",
        "(_ : U) -> U",
        "\\x _. x",
    ] {
        assert_parity(src);
    }
}

// 消融环境变量
// --------------------------------------------------------------------------------

#[test]
fn ablation_env_vars_leave_output_unchanged() {
    // A/B 消融开关只影响性能，不得改变逐字节输出（两种实现都是）。
    // 用 Mutex 把自己串行化（进程级 env；并行测试只读 env 不写）。
    static ENV_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
    let _g = ENV_LOCK.lock().unwrap();
    let mut battery: Vec<String> = [
        "U",
        "_",
        "\\x. x",
        "let id : (A : U) -> A -> A = \\A x. x;\nid _ _",
        "let f : U -> U = \\x. _; f U",
        L03_holes::EX0_SRC,
        L03_holes::EX1_SRC,
        "let f : U -> U = \\A. A;\nf f",
        "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
         let chain0 : Nat = \\N s z. s z;\nchain0",
    ]
    .iter()
    .map(|s| s.to_string())
    .collect();
    battery.push(L03_holes::bump_spine_iter::solve_src(4));
    battery.push(L03_holes::bump_spine_iter::conv_dup_src(4));
    for var in ["L03_NO_CONV_MEMO", "L03_NO_NAME_MAP"] {
        unsafe { std::env::set_var(var, "1") };
        for src in &battery {
            assert_parity(src);
        }
        unsafe { std::env::remove_var(var) };
    }
}

// 压力与深度
// --------------------------------------------------------------------------------

#[test]
fn deep_church_8192_full_output() {
    // church 2^13：全量 nf 输出逐字节断言（两个实现）。
    with_big_stack(|| {
        let src = L03_holes::bump_spine_iter::church_src(12);
        let expected = format!("{}  :\n{}\n", church_nf_expect(8192), nat_type());
        let basic = nf(&src);
        let fast_out = fast_nf(&src);
        assert_eq!(basic, expected);
        assert_eq!(fast_out, expected);
        assert_eq!(basic, fast_out);
    });
}

#[test]
fn deep_solve_2048_full_output() {
    // `Eq _ p_k p_k = refl _ _`：求解 + rename 沿 church 2048 的整条
    // neutral 链（k=10 → 2^11）。参考版这里是递归 rename 的压力点。
    with_big_stack(|| {
        let src = L03_holes::bump_spine_iter::solve_src(10);
        let expected_nf = eq_battery_expect(2048);
        let basic = nf(&src);
        assert_eq!(basic, expected_nf);
        assert_eq!(basic, fast_nf(&src));
        assert_eq!(ty(&src), fast::main_with("type", &src));
        // elab：开头的解块（?0/?1 = Nat 类型，?2 = church 2048 fresh 名）
        let e = elab(&src);
        assert_eq!(fast::main_with("elab", &src), e);
        assert!(e.starts_with(
            "let ?0 = (N : U) → (N → N) → N → N;\n\
             let ?1 = (N : U) → (N → N) → N → N;\n"
        ), "{e}");
    });
}

#[test]
fn deep_conv_2048_full_output() {
    // `Eq Nat (add p_k zero) p_k = refl Nat p_k`：转换检查强制两侧完整
    // 展开后结构比较；输出与 solve 同形（无洞参与）。
    with_big_stack(|| {
        let src = L03_holes::bump_spine_iter::conv_src(10);
        let expected_nf = eq_battery_expect(2048);
        let basic = nf(&src);
        assert_eq!(basic, expected_nf);
        assert_eq!(basic, fast_nf(&src));
        assert_eq!(ty(&src), fast::main_with("type", &src));
    });
}

#[test]
fn deep_conv_dup_2048_full_output() {
    // `Rel` 余定义域重复谓词：`(add p_k zero, add p_k zero)` 这对比较出现
    // 3 次（记忆化命中负载）；nf = `λ P p1 p2. p1`，类型三份 church。
    with_big_stack(|| {
        let src = L03_holes::bump_spine_iter::conv_dup_src(10);
        let ch = church_tm(2048);
        let expected_nf = format!(
            "λ P p1 p2. p1\n  :\n(P : ({nat}) → U) → P ({ch}) → P ({ch}) → P ({ch})\n",
            nat = nat_type(),
            ch = ch,
        );
        let basic = nf(&src);
        assert_eq!(basic, expected_nf);
        assert_eq!(basic, fast_nf(&src));
        assert_eq!(ty(&src), fast::main_with("type", &src));
    });
}

#[test]
fn deep_dup_16384_full_output() {
    // `D p_k`（D = \x f. f x x）：quote 对同一闭包强制 2 次（无记忆化时）。
    with_big_stack(|| {
        let src = L03_holes::bump_spine_iter::dup_src(13);
        let ch = church_tm(16384);
        let expected_nf = format!(
            "λ f. f ({ch}) ({ch})\n  :\n(({nat}) → ({nat}) → {nat}) → {nat}\n",
            nat = nat_type(),
            ch = ch,
        );
        let basic = nf(&src);
        assert_eq!(basic, expected_nf);
        assert_eq!(basic, fast_nf(&src));
        assert_eq!(ty(&src), fast::main_with("type", &src));
    });
}

#[test]
fn deep_dup_deep_2048_quad_copy() {
    // `D1 (D0 p_k)` 两层复制：C 被强制 4 次。类型文本验证小 k 金样，
    // 深 k 用前缀 + 后缀 + 互检。
    with_big_stack(|| {
        let src = L03_holes::bump_spine_iter::dup_deep_src(10);
        let ch = church_tm(2048);
        let basic = nf(&src);
        let prefix = format!("λ f. f (λ f'. f' ({ch}) ({ch})) (λ f'. f' ({ch}) ({ch}))\n  :\n");
        assert!(basic.starts_with(&prefix), "{basic}");
        assert!(basic.ends_with(&format!("→ {nat}\n", nat = nat_type())), "{basic}");
        assert_eq!(basic, fast_nf(&src));
        assert_eq!(ty(&src), fast::main_with("type", &src));
    });
}

#[test]
fn deep_chain_4096_elab_parity() {
    // 名字解析链负载：4096 条顶层 let；elab 展开整个链（参考版 O(n²)
    // 找名，名字 map 下 O(n)）。nf 只是 church 2。
    with_big_stack(|| {
        let src = L03_holes::bump_spine_iter::chain_src(11);
        assert_eq!(nf(&src), church_nf_expect(2) + "  :\n" + nat_type() + "\n");
        let e = elab(&src);
        let f = fast::main_with("elab", &src);
        assert_eq!(e, f);
        assert!(e.starts_with("\nlet Nat : U\n  = (N : U) → (N → N) → N → N;\n\n"), "{e}");
        assert!(e.contains("let p4095 : Nat\n  = add p4094 p0;"), "{e}");
        assert!(e.ends_with("p0\n"), "{e}");
        assert_eq!(ty(&src), fast::main_with("type", &src));
    });
}

#[test]
fn deep_parens_300_do_not_break() {
    let deep_parens = format!("{}{}", "(".repeat(300), "U".to_string() + &")".repeat(300));
    assert_eq!(nf(&deep_parens), "U\n  :\nU\n");
    assert_parity(&deep_parens);
}

// 跨层交叉一致性（L02 ↔ L03）
// --------------------------------------------------------------------------------

#[test]
fn cross_l02_well_typed_battery() {
    // L02 能通过的良构程序（无洞出现时），L03 的 nf/type 必须逐字节相同；
    // 注意 L03 会额外接受 L02 拒绝的程序（洞插入），此处只比较共同成功面。
    for src in [
        "U",
        "(A : U) -> A -> A",
        "let id : (A : U) -> A -> A = \\A x. x;\nid ((A B : U) -> A -> B -> A) (\\A B x y. x)",
        "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
         let add : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z);\n\
         add (\\N s z. s z) (\\N s z. s (s z))",
        "let x : U = U;\nlet y : U -> U -> U = \\a b. a;\ny U U",
        "let f : (A : U) -> (x : A) -> A = \\A x. x;\nf (U -> U) (\\A. A)",
        "let f : (A : U) -> A -> A = \\A x. x;\nlet g : (A : U) -> A -> A = \\A. f A;\ng",
        "let comp : (U -> U) -> (U -> U) -> U -> U = \\f g x. f (g x);\n\
         comp (\\x. x) (\\x. x) U",
        "let f : U -> U -> U = \\x x. x;\nf",
        "(x : U) -> (x : U) -> x",
        "let x : U = U;\nlet x : U = x;\nx",
        "let f : ((U -> U) -> U) -> U = \\g. U;\nf",
        "(_ : U) -> (x : U) -> U",
        "{- c -} let x : U = U; -- mid\nx",
    ] {
        let b = L02_tyck::main_with("nf", src);
        let l3 = nf(src);
        assert_eq!(b, l3, "L02/L03 nf 分歧，src:\n{src}");
        let b = L02_tyck::main_with("type", src);
        let l3 = ty(src);
        assert_eq!(b, l3, "L02/L03 type 分歧，src:\n{src}");
        // 顺带把性能版也一起核了
        assert_eq!(b, fast::main_with("type", src));
    }
}

#[test]
fn cross_l02_vs_l03_hole_divergence() {
    // L03 相对 L02 的三个新行为（洞插入）：
    //   1. `U _` 不再是尾随垃圾（合成 Pi vs U 报错，而非输出 U）
    assert_ne!(nf("U _"), nf("U"));
    assert!(nf("U _").contains("?1 x"), "{}", nf("U _"));
    assert_eq!(L02_tyck::main_with("nf", "U _"), "U\n  :\nU\n");
    //   2. 顶层 λ 可推断（L02 报 Can't infer）
    assert!(nf("\\x. x").contains("?0"),
            "L03 顶层 λ 应挂洞推断：{}", nf("\\x. x"));
    assert!(L02_tyck::main_with("nf", "\\x. x").contains("Can't infer"));
    //   3. let 体 λ 合法（L02 拒绝）
    assert!(nf("let x : U = U; \\A. A").contains("?0"));
    assert!(L02_tyck::main_with("nf", "let x : U = U; \\A. A").contains("Can't infer"));
}