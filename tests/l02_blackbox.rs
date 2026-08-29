//! L02_tyck 黑盒测试套件。
//!
//! 被测对象：`src/L02_tyck`（elaboration-zoo `typecheck-closures-debruijn` 的
//! Rust 移植），唯一黑盒入口是 `main_with(mode, src)`（mode ∈ {nf, type,
//! --help}），经 `#[path]` 独立编译进本测试 crate（同 `tests/l03_review_probe.rs`
//! 的做法；L02 是 `lib.rs` 里的私有 `mod`，集成测试无法直接引用）。
//!
//! 双 oracle：
//!   1. 期望输出字符串 —— 由 main.hs 语义 + 源码逐行推导，凡是整串断言处
//!      均已与实际输出核对（实测确认的字节）；未经实测的点用 contains 断言。
//!   2. 参考版（`mod.rs`）↔ 性能版（`bump_spine_iter.rs`）逐字节互检 ——
//!      两实现被承诺输出一致，任何一侧的回归都会在此暴露。
//!
//! 套件记录的三个「已知怪癖」（来自解析器/报错器的忠实移植，非 bug）：
//!   - 尾随垃圾 token 被静默忽略：`U 1`、`U;`、`U → U` 都按 `U` 处理；
//!   - `_` 在项位置不是 hole（区别于 L03），同样被当作尾随垃圾丢弃；
//!   - 错误列号按**字节**计算（`offset - line_start + 1`），多字节字符
//!     （如 `λ`）出现在 caret 之前时，caret 视觉上会右移每个字符的字节差。

#![feature(pattern)]

#[path = "../src/list.rs"]
mod list;

#[path = "../src/parser_lib.rs"]
mod parser_lib;

#[path = "../src/L02_tyck/mod.rs"]
mod L02_tyck;

#[path = "../src/L03_holes/mod.rs"]
mod L03_holes;

use L02_tyck::bump_spine_iter as fast;
use L03_holes::bump_spine_iter as fast3;

// helpers
// --------------------------------------------------------------------------------

fn nf(src: &str) -> String {
    L02_tyck::main_with("nf", src)
}

fn ty(src: &str) -> String {
    L02_tyck::main_with("type", src)
}

fn fast_nf(src: &str) -> String {
    fast::main_with("nf", src)
}

fn fast_ty(src: &str) -> String {
    fast::main_with("type", src)
}

/// Oracle 2：参考版与性能版在 nf/type 两种模式下输出逐字节一致。
fn assert_parity(src: &str) {
    let b = nf(src);
    let f = fast_nf(src);
    assert_eq!(b, f, "nf 模式双实现不一致，src:\n{src}\n--- basic ---\n{b}--- fast ---\n{f}");
    let b = ty(src);
    let f = fast_ty(src);
    assert_eq!(b, f, "type 模式双实现不一致，src:\n{src}\n--- basic ---\n{b}--- fast ---\n{f}");
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

/// EX2 式 church 编码的源码（n 个 s 的 numeral）。
fn church_src(n: usize) -> String {
    let mut s = String::from("let Nat : U = (N : U) -> (N -> N) -> N -> N;\n");
    s.push_str(&format!("let n : Nat = \\N s z. "));
    for _ in 0..n {
        s.push_str("s (");
    }
    s.push('z');
    for _ in 0..n {
        s.push(')');
    }
    s.push_str(";\nn");
    s
}

/// 期望的 church n 的 nf 文本（`λ N s z. s (s (… z))`）。
fn church_nf_expect(n: usize) -> String {
    fn f(k: usize) -> String {
        match k {
            0 => "z".to_string(),
            1 => "s z".to_string(),
            k => format!("s ({})", f(k - 1)),
        }
    }
    format!("λ N s z. {}\n", f(n))
}

const HELP: &str = "usage: elabzoo-typecheck-closures-debruijn [--help|nf|type]\n  --help : display this message\n  nf     : read & typecheck expression from stdin, print its normal form and type\n  type   : read & typecheck expression from stdin, print its type\n";

// 模式与输出格式
// --------------------------------------------------------------------------------

#[test]
fn type_mode_prints_type_only() {
    assert_eq!(ty("U"), "U\n");
    assert_eq!(ty("(A : U) -> A -> A"), "U\n");
}

#[test]
fn nf_mode_prints_normal_form_and_type() {
    assert_eq!(nf("U"), "U\n  :\nU\n");
    assert_eq!(
        nf("(A : U) -> A -> A"),
        "(A : U) → A → A\n  :\nU\n"
    );
}

#[test]
fn nf_output_embeds_type_mode_output() {
    // nf 格式 = `{nf}\n  :\n{type}\n`，type 模式独立跑出的类型必须与之一致。
    for src in [
        "U",
        "(A : U) -> A -> A",
        "let id : (A : U) -> A -> A = \\A x. x;\nid",
        "let id : (A : U) -> A -> A = \\A x. x;\nid ((A : U) -> A -> A) (\\A x. x)",
        "let Nat : U = (N : U) -> (N -> N) -> N -> N;\nlet one : Nat = \\N s z. s z;\none",
        "let f : (A : U) -> (x : A) -> A = \\A x. x;\nf U",
    ] {
        assert_nf_embeds_type(src);
    }
}

#[test]
fn help_and_unknown_modes() {
    for mode in ["--help", "", "bogus", "foo", "ELAB"] {
        assert_eq!(L02_tyck::main_with(mode, ""), HELP, "mode {mode:?}");
        assert_eq!(fast::main_with(mode, ""), HELP, "fast mode {mode:?}");
    }
}

#[test]
fn parse_error_output_is_plain_line() {
    for src in ["", "   \n\t", "-- just a comment\n", "{- block -}"] {
        assert_eq!(nf(src), "parse error\n", "src: {src:?}");
        assert_eq!(ty(src), "parse error\n", "src: {src:?}");
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
fn unicode_lambda_lexes_without_space() {
    // `λx` 会被 lexer 拆成 Lambda + Ident（λ 后无需空格）。
    // 顶层 λ 无法推断类型，报错应在 λ 处而不是 parse error。
    assert_error_at(r"\x. x", 1, 1, "Can't infer type for lambda expression");
    assert_error_at("λx. x", 1, 1, "Can't infer type for lambda expression");
    assert_error_at("λx y. x", 1, 1, "Can't infer type for lambda expression");
}

#[test]
fn multi_binder_lam_desugars_to_nested() {
    let a = "let id : (A : U) -> A -> A = \\A x. x;\nid";
    let b = "let id : (A : U) -> A -> A = \\A. \\x. x;\nid";
    assert_eq!(nf(a), nf(b));
}

#[test]
fn pi_multi_binder_parens() {
    // `(A B : U) -> …` 一个括号里多个 binder。
    assert_eq!(
        nf("(A B : U) -> A -> B -> A"),
        "(A : U)(B : U) → A → B → A\n  :\nU\n"
    );
    assert_eq!(ty("(A B : U) -> A -> B -> A"), "U\n");
}

#[test]
fn unannotated_arrow_is_underscore_pi() {
    // `A -> B` ≡ `(_ : A) -> B`，打印成无 binder 形式。
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
    // mid 注释把 `U {- c -} U` 连成应用 → Expected a function type
    assert_eq!(
        nf("U {- c -} U"),
        "(stdin):1:1:\n  |\n1 | U {- c -} U\n  | ^\nExpected a function type, instead inferred:\n\n  U\n\n"
    );
}

#[test]
fn unclosed_block_comment_swallows_rest_of_input() {
    // 注释未闭合时吞到 EOF：`{- oops` 之后没有项 → parse error；
    // 但 `U {- oops` 的 U 是完整项，输出照常。
    assert_eq!(nf("{- oops"), "parse error\n");
    assert_eq!(nf("U {- oops"), "U\n  :\nU\n");
}

#[test]
fn underscore_only_binder_positions() {
    // 三个 binder 位置都合法（`_` 和普通标识符一样是多 binder 语法里的一个名字）。
    assert_eq!(nf("let f : U -> U -> U = \\_ x. x;\nf"), "λ _ x. x\n  :\nU → U → U\n");
    assert_eq!(nf("let _ : U = U; U"), "U\n  :\nU\n");
    assert_eq!(nf("(_ : U) -> U"), "U → U\n  :\nU\n");
}

#[test]
fn underscore_in_term_position_is_inert_junk() {
    // L02 没有 hole：`_` 在项位置解析失败后作为尾随垃圾被丢弃（L03 会建 meta）。
    assert_eq!(nf("U _"), "U\n  :\nU\n");
    assert_eq!(ty("U _"), "U\n");
}

#[test]
fn trailing_junk_tokens_are_silently_ignored() {
    // 解析器只取第一个完整项，剩余 token 被忽略（与 main.hs 的 pRaw 一致）。
    // 注意 `U x` 不在其中：两个相邻标识符是合法应用，不是尾随垃圾。
    for junk in ["U 1", "U;", "U 1 2", "U +", "U _", "U → U"] {
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
        "let",
    ] {
        assert_eq!(nf(src), "parse error\n", "src: {src:?}");
        assert_eq!(ty(src), "parse error\n", "src: {src:?}");
    }
}

#[test]
fn parens_nest() {
    assert_eq!(nf("((((U))))"), "U\n  :\nU\n");
}

#[test]
fn let_sets_do_not_need_spaces() {
    assert_eq!(
        nf("let x : U = U;let y : U = x;y"),
        "U\n  :\nU\n"
    );
}

// 良构程序（精确定值）
// --------------------------------------------------------------------------------

#[test]
fn id_const_application() {
    // elaboration-zoo 上游 ex1 的形态：id 应用于类型再应用于 const。
    assert_eq!(
        nf("let id : (A : U) -> A -> A\n      = \\A x. x;\nlet const : (A B : U) -> A -> B -> A\n      = \\A B x y. x;\nid ((A B : U) -> A -> B -> A) const"),
        "λ A B x y. x\n  :\n(A : U)(B : U) → A → B → A\n"
    );
}

#[test]
fn pi_polymorphism_requires_instantiation() {
    // id 的类型是多态 Pi；直接用 `id (U -> U) id` 不合法（cod 是中性 A，
    // 无法与 U 转换），必须先应用到类型上。
    let src = "let id : (A : U) -> A -> A = \\A x. x;\nid (U -> U) id";
    assert_eq!(
        nf(src),
        "(stdin):2:13:\n  |\n2 | id (U -> U) id\n  |             ^\ntype mismatch\n\nexpected type:\n\n  U → U\n\ninferred type:\n\n  (A : U) → A → A\n\n"
    );
    // 应用到类型上之后即可：
    assert_eq!(
        nf("let id : (A : U) -> A -> A = \\A x. x;\nid ((A : U) -> A -> A) id"),
        "λ A x. x\n  :\n(A : U) → A → A\n"
    );
}

#[test]
fn dependent_substitution() {
    let src = "let f : (A : U) -> (x : A) -> A = \\A x. x;\nf";
    // f 的类型：cod 是依赖的 (x : A) -> A
    assert_eq!(nf(src), "λ A x. x\n  :\n(A : U)(x : A) → A\n");
    // f U : (x : U) -> U —— 第一个实参替换进 cod；nf 为 λ x. x
    assert_eq!(
        nf("let f : (A : U) -> (x : A) -> A = \\A x. x;\nf U"),
        "λ x. x\n  :\n(x : U) → U\n"
    );
    assert_eq!(ty("let f : (A : U) -> (x : A) -> A = \\A x. x;\nf U"), "(x : U) → U\n");
    // f U U : U，U 代入后 cod 变 U
    assert_eq!(nf("let f : (A : U) -> (x : A) -> A = \\A x. x;\nf U U"), "U\n  :\nU\n");
    // f (U -> U) (\\A. A) —— 实参是函数类型与函数值
    assert_eq!(
        nf("let f : (A : U) -> (x : A) -> A = \\A x. x;\nf (U -> U) (\\A. A)"),
        "λ A. A\n  :\nU → U\n"
    );
}

#[test]
fn church_numerals() {
    let nat = "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n";
    assert_eq!(
        nf(&format!("{nat}let zero : Nat = \\N s z. z;\nzero")),
        "λ N s z. z\n  :\n(N : U) → (N → N) → N → N\n"
    );
    assert_eq!(
        nf(&format!("{nat}let one : Nat = \\N s z. s z;\none")),
        "λ N s z. s z\n  :\n(N : U) → (N → N) → N → N\n"
    );
    assert_eq!(
        nf(&format!("{nat}let two : Nat = \\N s z. s (s z);\ntwo")),
        "λ N s z. s (s z)\n  :\n(N : U) → (N → N) → N → N\n"
    );
}

#[test]
fn church_arithmetic_5_plus_5() {
    let src = "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
               let five : Nat = \\N s z. s (s (s (s (s z))));\n\
               let add : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z);\n\
               add five five";
    assert_eq!(
        nf(src),
        "λ N s z. s (s (s (s (s (s (s (s (s (s z)))))))))\n  :\n(N : U) → (N → N) → N → N\n"
    );
}

#[test]
fn church_arithmetic_2_times_3() {
    let src = "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
               let two : Nat = \\N s z. s (s z);\n\
               let three : Nat = \\N s z. s (s (s z));\n\
               let mul : Nat -> Nat -> Nat = \\a b N s z. a N (b N s) z;\n\
               mul two three";
    assert_eq!(
        nf(src),
        "λ N s z. s (s (s (s (s (s z)))))\n  :\n(N : U) → (N → N) → N → N\n"
    );
}

#[test]
fn church_thousand_ex2() {
    // 上游 ex2：千位 church 数（参考版中等深度的完整展开）。
    with_big_stack(|| {
        let out = nf(L02_tyck::EX2_SRC);
        assert_eq!(
            out,
            format!("{}  :\n(N : U) → (N → N) → N → N\n", L02_tyck::church_nf(1000))
        );
        assert_eq!(out, fast_nf(L02_tyck::EX2_SRC));
    });
}

#[test]
fn eta_wrapped_definition_normalizes() {
    // `\A. id A` 通过 conv（eta 形态）通过检查，nf 里 β 展开成 `λ A x. x`。
    let src = "let id : (A : U) -> A -> A = \\A x. x;\n\
               let g : (A : U) -> A -> A = \\A. id A;\ng";
    assert_eq!(nf(src), "λ A x. x\n  :\n(A : U) → A → A\n");
}

#[test]
fn alpha_renamed_instances_are_convertible() {
    let src = "let id1 : (A : U) -> A -> A = \\A x. x;\n\
               let id2 : (B : U) -> B -> B = \\B y. y;\n\
               let f : ((A : U) -> A -> A) -> U = \\g. U;\n\
               f id2";
    assert_eq!(nf(src), "U\n  :\nU\n");
}

#[test]
fn lambda_shadowing_fresh_names() {
    assert_eq!(nf("let f : U -> U -> U = \\x x. x;\nf"), "λ x x'. x'\n  :\nU → U → U\n");
    assert_eq!(
        nf("let f : U -> U -> U -> U = \\x x x. x;\nf"),
        "λ x x' x''. x''\n  :\nU → U → U → U\n"
    );
}

#[test]
fn pi_shadowing_fresh_names() {
    assert_eq!(nf("(x : U) -> (x : U) -> x"), "(x : U)(x' : U) → x'\n  :\nU\n");
}

#[test]
fn let_shadowing_refers_to_outer_in_value() {
    // 第二个 let 的 value 里的 x 是外层的 x（binder 在 value 之后才生效）。
    assert_eq!(nf("let x : U = U;\nlet x : U = x;\nx"), "U\n  :\nU\n");
}

#[test]
fn checkable_lambda_with_function_arrow() {
    // `\g. g` 的目标类型是 (U -> U) -> U -> U：body g 是函数类型，
    // conv 两边的 cod 都是字面 U → U，可转换（不同于多态 id 情形）。
    let src = "let f : (U -> U) -> U -> U = \\g. g;\nf";
    assert_eq!(nf(src), "λ g. g\n  :\n(U → U) → U → U\n");
}

#[test]
fn nf_does_not_eta_reduce() {
    // nf 是 β-正规形，不做 η 收缩：`λ g x. g x` 保持展开形态。
    let src = "let f : (U -> U) -> U -> U = \\g x. g x;\nf";
    assert_eq!(nf(src), "λ g x. g x\n  :\n(U → U) → U → U\n");
    // 但应用会 β：f (id) U → U
    let app = "let f : (U -> U) -> U -> U = \\g x. g x;\nf (\\x. x) U";
    assert_eq!(nf(app), "U\n  :\nU\n");
}

#[test]
fn nested_pi_precedence_parens() {
    let src = "let f : ((U -> U) -> U) -> U = \\g. U;\nf";
    assert_eq!(nf(src), "λ g. U\n  :\n((U → U) → U) → U\n");
    assert_eq!(ty(src), "((U → U) → U) → U\n");
}

#[test]
fn multiline_let_value() {
    let src = "let f : U -> U =\n  \\A. A;\nf U";
    assert_eq!(nf(src), "U\n  :\nU\n");
}

#[test]
fn composition_uses_function_arguments() {
    let src = "let comp : (U -> U) -> (U -> U) -> U -> U = \\f g x. f (g x);\n\
               comp (\\x. x) (\\x. x) U";
    assert_eq!(nf(src), "U\n  :\nU\n");
}

#[test]
fn let_value_reuses_earlier_let() {
    let src = "let id : (A : U) -> A -> A = \\A x. x;\n\
               let id2 : (A : U) -> A -> A = id ((A : U) -> A -> A) (\\A x. x);\nid2";
    assert_eq!(nf(src), "λ A x. x\n  :\n(A : U) → A → A\n");
}

// 类型错误（精确定值）
// --------------------------------------------------------------------------------

#[test]
fn ex0_self_application_error() {
    // 与模块内测试同款：`id id` 在 U 目标下类型不匹配，caret 在第二个 id。
    with_big_stack(|| {
        assert_eq!(
            L02_tyck::ex0(),
            r#"(stdin):4:18:
  |
4 | let bar : U = id id;     -- we cannot apply any function to itself (already true in simple TT)
  |                  ^
type mismatch

expected type:

  U

inferred type:

  (A : U) → A → A

"#
        );
        assert_eq!(L02_tyck::ex0(), fast_nf(L02_tyck::EX0_SRC));
    });
}

#[test]
fn expected_function_type_UU() {
    assert_eq!(
        nf("U U"),
        "(stdin):1:1:\n  |\n1 | U U\n  | ^\nExpected a function type, instead inferred:\n\n  U\n\n"
    );
}

#[test]
fn expected_function_type_after_block_comment() {
    // 注释把两个 U 连成应用；caret 在头部 U。
    assert_eq!(
        nf("U {- c -} U"),
        "(stdin):1:1:\n  |\n1 | U {- c -} U\n  | ^\nExpected a function type, instead inferred:\n\n  U\n\n"
    );
}

#[test]
fn type_mismatch_let_value() {
    let src = "let f : U -> U = U; f";
    assert_eq!(
        nf(src),
        "(stdin):1:18:\n  |\n1 | let f : U -> U = U; f\n  |                  ^\ntype mismatch\n\nexpected type:\n\n  U → U\n\ninferred type:\n\n  U\n\n"
    );
}

#[test]
fn type_mismatch_argument_domain() {
    let src = "let f : U -> U = \\A. A;\nf f";
    assert_eq!(
        nf(src),
        "(stdin):2:3:\n  |\n2 | f f\n  |   ^\ntype mismatch\n\nexpected type:\n\n  U\n\ninferred type:\n\n  U → U\n\n"
    );
}

#[test]
fn type_mismatch_lambda_body() {
    let src = "let f : (U -> U) -> U -> U = \\g. U; f";
    assert_eq!(
        nf(src),
        "(stdin):1:34:\n  |\n1 | let f : (U -> U) -> U -> U = \\g. U; f\n  |                                  ^\ntype mismatch\n\nexpected type:\n\n  U → U\n\ninferred type:\n\n  U\n\n"
    );
}

#[test]
fn type_mismatch_church_term() {
    let src = "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
               let one : Nat = \\N s z. s s;\none";
    assert_eq!(
        nf(src),
        "(stdin):2:27:\n  |\n2 | let one : Nat = \\N s z. s s;\n  |                           ^\ntype mismatch\n\nexpected type:\n\n  N\n\ninferred type:\n\n  N → N\n\n"
    );
}

#[test]
fn lambda_cant_infer_top_level() {
    assert_error_at(r"\x. x", 1, 1, "Can't infer type for lambda expression");
    assert_error_at("λx. x", 1, 1, "Can't infer type for lambda expression");
}

#[test]
fn lambda_in_function_position() {
    assert_error_at(r"(\x. x) U", 1, 2, "Can't infer type for lambda expression");
}

#[test]
fn lambda_against_non_pi_expectation() {
    // λ 的目标类型不是 Pi → 无法检查（不是类型不匹配，而是不能推断）。
    assert_error_at("let bad : U = λx. x; bad", 1, 15, "Can't infer type for lambda expression");
}

#[test]
fn variable_out_of_scope() {
    assert_eq!(
        nf("id"),
        "(stdin):1:1:\n  |\n1 | id\n  | ^\nvariable out of scope: id\n"
    );
    let out = nf("let x : U = U;\nlet y : U = z;\ny");
    assert!(out.starts_with("(stdin):2:"), "{out}");
    assert!(out.contains("variable out of scope: z"), "{out}");
}

#[test]
fn variable_out_of_scope_in_pi_cod() {
    assert_eq!(
        nf("(A : U) -> x"),
        "(stdin):1:12:\n  |\n1 | (A : U) -> x\n  |            ^\nvariable out of scope: x\n"
    );
}

#[test]
fn let_body_lambda_rejected() {
    // let 的 body 走 infer 走廊，λ 无法推断（区别于 L03 的 hole 插入）。
    assert_error_at("let x : U = U; \\A. A", 1, 16, "Can't infer type for lambda expression");
}

#[test]
fn eta_lam_against_neutral_cod_rejected() {
    // `\A x y. x y` 的第三层 body 目标类型是中性 A（变量类型），
    // 不是 Pi → λ 无法检查。eta 展开的 λ 在 L02 里不能直接通过检查。
    let src = "let id : (A : U) -> A -> A = \\A x. x;\n\
               let e : (A : U) -> A -> A = \\A x y. x y;\ne";
    assert_error_at(src, 2, 29, "Can't infer type for lambda expression");
}

#[test]
fn error_position_with_unicode_lambda_before_caret() {
    // caret 列按字节算：`λ` 占 2 字节，使 caret 视觉右移 1 列（套件文档中的怪癖 3）。
    let src = "let id : (A : U) -> A -> A = λA x. x; id id";
    let out = nf(src);
    assert_eq!(
        out,
        "(stdin):1:43:\n  |\n1 | let id : (A : U) -> A -> A = λA x. x; id id\n  |                                           ^\ntype mismatch\n\nexpected type:\n\n  U\n\ninferred type:\n\n  (A : U) → A → A\n\n"
    );
    assert_parity(src);
}

// 求值与规范化语义
// --------------------------------------------------------------------------------

#[test]
fn nf_eliminates_let_apparatus() {
    // eval 消费掉 let：nf 输出里没有 let 痕迹。
    assert_eq!(nf("let x : U = U; x"), "U\n  :\nU\n");
    assert_eq!(nf("let f : U -> U = \\A. A; f"), "λ A. A\n  :\nU → U\n");
    assert_eq!(
        nf("let x : U = U;\nlet y : U -> U = \\A. x;\ny"),
        "λ A. U\n  :\nU → U\n"
    );
}

#[test]
fn nf_beta_reduces_type_application() {
    // f (U -> U)：类型作为值参加 β 归约，nf 是 `U → U`。
    let src = "let f : U -> U = \\A. A;\nf (U -> U)";
    assert_eq!(nf(src), "U → U\n  :\nU\n");
}

#[test]
fn nf_under_bindings_reduces() {
    // `comp (\x. x)` 先在 NF 里把 g 实例化掉。
    let src = "let comp : (U -> U) -> (U -> U) -> U -> U = \\f g x. f (g x);\ncomp (\\x. x)";
    assert_eq!(nf(src), "λ g x. g x\n  :\n(U → U) → U → U\n");
}

// 双实现互检（回归 oracle）
// --------------------------------------------------------------------------------

#[test]
fn parity_well_typed_battery() {
    for src in [
        "U",
        "(A : U) -> A -> A",
        "(A B : U) -> A -> B -> A",
        "let id : (A : U) -> A -> A = \\A x. x;\nid",
        "let id : (A : U) -> A -> A = \\A x. x;\nid ((A : U) -> A -> A) (\\A x. x)",
        "let id : (A : U) -> A -> A = \\A x. x;\nid ((A B : U) -> A -> B -> A) (\\A B x y. x)",
        "let f : (A : U) -> (x : A) -> A = \\A x. x;\nf U U",
        "let f : (A : U) -> (x : A) -> A = \\A x. x;\nf (U -> U) (\\A. A)",
        "let comp : (U -> U) -> (U -> U) -> U -> U = \\f g x. f (g x);\ncomp (\\x. x) (\\x. x) U",
        "let f : (U -> U) -> U -> U = \\g x. g x;\nf (\\x. x) U",
        "let Nat : U = (N : U) -> (N -> N) -> N -> N;\nlet two : Nat = \\N s z. s (s z);\ntwo",
        L02_tyck::EX1_SRC,
        "let id : (A : U) -> A -> A = \\A x. x;\nlet g : (A : U) -> A -> A = \\A. id A;\ng",
        "let x : U = U;\nlet y : U -> U -> U = \\a b. a;\ny U U",
        "((((U))))",
        "let f : ((U -> U) -> U) -> U = \\g. U;\nf",
        "(_ : U) -> (x : U) -> U",
        "{- c -} let x : U = U; -- mid\nx",
    ] {
        assert_parity(src);
    }
}

#[test]
fn parity_error_battery() {
    for src in [
        "U U",
        "U {- c -} U",
        r"\x. x",
        r"(\x. x) U",
        "let f : U -> U = U; f",
        "let f : U -> U = \\A. A;\nf f",
        "let f : (U -> U) -> U -> U = \\g. U; f",
        "let x : U = U; \\A. A",
        "(A : U) -> x",
        "id",
        "let id : (A : U) -> A -> A = \\A x. x;\nid (U -> U) id",
        "let bad : U = λx. x; bad",
        "let id : (A : U) -> A -> A = \\A x. x;\nlet e : (A : U) -> A -> A = \\A x y. x y;\ne",
        "let Nat : U = (N : U) -> (N -> N) -> N -> N;\nlet one : Nat = \\N s z. s s;\none",
        L02_tyck::EX0_SRC,
        "let x : U = U;\nlet y : U = z;\ny",
        "let f : U -> U = \\A. A;\nlet x : U = f f;\nx",
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
    ] {
        assert_parity(src);
    }
}

#[test]
fn parity_unicode_and_comments() {
    for src in [
        "let id : (A : U) -> A -> A = λA x. x;\nid",
        "λx. x",
        "let bad : U = λx. x; bad",
        "let id : (A : U) -> A -> A = λA x. x; id id",
        "{- 中文注释 -} let x : U = U; -- 行注释\nx",
        "U → U",
    ] {
        assert_parity(src);
    }
}

// 压力与深度
// --------------------------------------------------------------------------------

#[test]
fn deep_church_1024_full_output_parity() {
    with_big_stack(|| {
        let src = church_src(1024);
        let expected = format!("{}  :\n(N : U) → (N → N) → N → N\n", church_nf_expect(1024));
        assert_eq!(nf(&src), expected);
        assert_eq!(fast_nf(&src), expected);
    });
}

#[test]
fn deep_church_4096_reference_full_output() {
    // 参考版 infer 对「字面深右嵌套应用链」是 O(n²)（每层对剩余子链重新
    // eval——上游 Main.hs 同款），4096 是整串断言下可行的深度上限。
    // 512MB 栈：eval/quote/pretty 三段递归各 4096 层。
    with_big_stack(|| {
        let src = church_src(4096);
        let expected = format!("{}  :\n(N : U) → (N → N) → N → N\n", church_nf_expect(4096));
        assert_eq!(nf(&src), expected);
        assert_eq!(fast_nf(&src), expected);
    });
}

#[test]
fn deep_church_65536_doubling_chain_both_impls() {
    // 模块 bench 同款负载：`add p_k p_k` 倍增链（值经闭包共享，infer 线性）。
    // 两个实现都要在 65536 层上输出逐字节一致的全量 nf。
    with_big_stack(|| {
        let src = L02_tyck::bump_spine_iter::church_src(15); // church 2^16 = 65536
        let expected = format!("{}  :\n(N : U) → (N → N) → N → N\n", church_nf_expect(65536));
        let basic = nf(&src);
        let fast_out = fast_nf(&src);
        assert_eq!(basic, expected);
        assert_eq!(fast_out, expected);
        assert_eq!(basic, fast_out);
    });
}

#[test]
fn deep_parens_and_apps_do_not_break() {
    let deep_parens = format!("{}{}", "(".repeat(500), format!("{}", "U".to_string() + &")".repeat(500)));
    assert_eq!(nf(&deep_parens), "U\n  :\nU\n");
    // 500 连乘的应用链（U 是函数？不是 —— 检查期望的报错而非炸栈）
    let deep_apps = format!("{} {}", "U ".repeat(200), "U");
    assert_error_at(&deep_apps, 1, 1, "Expected a function type");
}

// 跨层交叉一致性（对 L03）
// --------------------------------------------------------------------------------

#[test]
fn cross_l03_well_typed_battery() {
    // L02 能通过的良构程序，L03（无 hole 出现时）输出必须逐字节相同。
    // 注意 L03 会额外接受 L02 拒绝的程序（hole 插入），此处只比较共同成功面。
    for src in [
        "U",
        "(A : U) -> A -> A",
        "let id : (A : U) -> A -> A = \\A x. x;\nid ((A B : U) -> A -> B -> A) (\\A B x y. x)",
        "let Nat : U = (N : U) -> (N -> N) -> N -> N;\nlet add : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z);\nadd (\\N s z. s z) (\\N s z. s (s z))",
        "let x : U = U;\nlet y : U -> U -> U = \\a b. a;\ny U U",
        "let f : (A : U) -> (x : A) -> A = \\A x. x;\nf (U -> U) (\\A. A)",
    ] {
        let b = nf(src);
        let l3 = L03_holes::main_with("nf", src);
        assert_eq!(b, l3, "L02/L03 nf 分歧，src:\n{src}");
        let b = ty(src);
        let l3 = L03_holes::main_with("type", src);
        assert_eq!(b, l3, "L02/L03 type 分歧，src:\n{src}");
        // 顺带把性能版也一起核了
        assert_eq!(b, fast3::main_with("type", src));
    }
}