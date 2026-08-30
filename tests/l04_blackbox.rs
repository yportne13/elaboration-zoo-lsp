//! L04_implicit 黑盒测试套件。
//!
//! 被测对象：`src/L04_implicit`（elaboration-zoo `04-implicit-args` 的 Rust
//! 移植：双向 elaboration + holes + pattern unification + **隐式参数**），
//! 唯一黑盒入口是 `main_with(mode, src)`（mode ∈ {--help, elab, nf, type}），
//! 经 `#[path]` 独立编译进本测试 crate。
//!
//! 双 oracle：
//!   1. 期望输出字符串 —— 由上游 Main.hs 语义 + 源码逐行推导（整串断言处
//!      均已与实际输出核对）；
//!   2. 参考版（`mod.rs`）↔ 性能版（`bump_spine_iter.rs`）**三模式**
//!      （nf/type/elab）逐字节互检。
//!
//! 与 L03 的语义差别（本套件专门覆盖）：
//!   - `Icit` 穿线：`{x : A} → B`、`λ {x}. t`、`f {a}` 的显示；
//!   - 隐式插入：显式应用前自动补 `?m` 实参，隐式 λ 检查时跳过插入；
//!   - 命名隐式：`t {x = u}` 实参与 `\{x = y}` lambda 按 Pi binder 名定位
//!     （`No named implicit argument with name …` 报错）；命名 λ 不可推断；
//!   - `{u}` 位置隐式实参应用到显式 Pi → `Function icitness mismatch`；
//!   - inserted binder 对源码名字不可见（插入的隐式 binder 不遮蔽同名 def）；
//!   - 消融环境变量 `L04_NO_CONV_MEMO` / `L04_NO_NAME_MAP` 只影响性能，
//!     逐字节输出不变。

#![feature(pattern)]

#[path = "../src/list.rs"]
mod list;

#[path = "../src/parser_lib.rs"]
mod parser_lib;

#[path = "../src/L04_implicit/mod.rs"]
mod L04_implicit;

use L04_implicit::bump_spine_iter as fast;

// helpers
// --------------------------------------------------------------------------------

fn nf(src: &str) -> String {
    L04_implicit::main_with("nf", src)
}

fn ty(src: &str) -> String {
    L04_implicit::main_with("type", src)
}

fn elab(src: &str) -> String {
    L04_implicit::main_with("elab", src)
}

/// Oracle 2：参考版与性能版在全部三种模式下输出逐字节一致。
fn assert_parity(src: &str) {
    for mode in ["nf", "type", "elab"] {
        let b = L04_implicit::main_with(mode, src);
        let f = fast::main_with(mode, src);
        assert_eq!(
            b, f,
            "{mode} 模式双实现不一致，src:\n{src}\n--- basic ---\n{b}--- fast ---\n{f}"
        );
    }
}

/// nf 模式输出以 type 模式输出结尾。
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
    let out = ty(src);
    assert!(
        out.starts_with(&format!("(stdin):{line}:{col}:\n")),
        "错误位置不符：期望 ({line}:{col})，实际：\n{out}"
    );
    assert!(out.contains(needle), "错误消息缺 {needle:?}：\n{out}");
    assert_parity(src);
}

const HELP: &str = "usage: elabzoo-implicit-args [--help|elab|nf|type]\n  --help : display this message\n  elab   : read & elaborate expression from stdin\n  nf     : read & typecheck expression from stdin, print its normal form and type\n  type   : read & typecheck expression from stdin, print its type\n";

// 模式与输出格式
// --------------------------------------------------------------------------------

#[test]
fn help_and_unknown_modes() {
    for mode in ["--help", "", "bogus", "foo", "ELAB", "-h"] {
        assert_eq!(L04_implicit::main_with(mode, ""), HELP, "mode {mode:?}");
        assert_eq!(fast::main_with(mode, ""), HELP, "fast mode {mode:?}");
    }
}

#[test]
fn type_mode_prints_type_only() {
    assert_eq!(ty("U"), "U\n");
    assert_eq!(ty("(A : U) -> A -> A"), "U\n");
    assert_eq!(ty("_"), "?0\n");
    assert_eq!(ty("\\x. x"), "(x : ?0) → ?0\n");
    // 隐式 Pi 显示：`{x : A} → …`；无注解的 binder 域是洞
    assert_eq!(ty("{A : U} -> A -> A"), "U\n");
    assert_eq!(
        ty("let f : {A : U}{B : U} -> U = U;\nf"),
        "{A : U}{B : U} → U\n"
    );
    assert_eq!(
        ty("let f : {A B} -> U = U;\nf"),
        "{A : ?0}{B : ?1 A} → U\n"
    );
}

#[test]
fn nf_mode_prints_normal_form_and_type() {
    assert_eq!(nf("U"), "U\n  :\nU\n");
    assert_eq!(nf("(A : U) -> A -> A"), "(A : U) → A → A\n  :\nU\n");
    assert_eq!(nf("_"), "?1\n  :\n?0\n");
    // 隐式 λ 形态：`λ {x}. t`；顶层推断——λx 的域 meta 在 binder A 之
    // 下（InsertedMeta 的 bds 带 A），显示 `?1 A`
    assert_eq!(nf("\\{A} x. x"), "λ {A} x. x\n  :\n{A : ?0}(x : ?1 A) → ?1 A\n");
}

#[test]
fn nf_output_embeds_type_mode_output() {
    for src in [
        "U",
        "\\x. x",
        "\\{A} x. x",
        "_",
        "let id : {A : U} -> A -> A = \\x. x;\nid U\n",
        "let const : {A B} -> A -> B -> A = \\x y. x;\nconst {B = U} U\n",
        L04_implicit::EX0_SRC,
        L04_implicit::EX1_SRC,
    ] {
        assert_nf_embeds_type(src);
        assert_parity(src);
    }
}

#[test]
fn elab_mode_prints_metacontext_then_term() {
    assert_eq!(elab("U"), "\nU\n");
    assert_eq!(elab("_"), "let ?0 = ?;\nlet ?1 = ?;\n\n?1\n");
    // 隐式插入的洞：解是 λ 包裹（spine 逆应用序），项里显示 `{?0 A x}`
    assert_eq!(
        elab("let id : {A : U} -> A -> A = \\x. x;\nlet id2 : {A : U} -> A -> A = \\x. id x;\nU\n"),
        "let ?0 = λ x1 x2. x1;\n\nlet id : {A : U} → A → A\n  = λ {A} x. x;\n\n\
         let id2 : {A : U} → A → A\n  = λ {A} x. id {?0 A x} x;\n\nU\n"
    );
}

#[test]
fn parse_error_output_is_plain_line() {
    for src in ["", "   \n\t", "-- just a comment\n", "{- block -}", "\n\n", "{"] {
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
    let src = "let id : {A : U} -> A -> A = \\x. x;\nid";
    let src2 = "let id : {A : U} -> A -> A = λx. x;\nid";
    assert_eq!(nf(src), nf(src2));
}

#[test]
fn line_and_block_comments() {
    assert_eq!(nf("U -- trailing comment\n"), "U\n  :\nU\n");
    assert_eq!(nf("{- c -} U"), "U\n  :\nU\n");
}

#[test]
fn multi_binder_implicit_pi_and_lam() {
    // `{A B}` 双 binder 展开为嵌套；λ 同理
    assert_eq!(
        nf("let f : {A B : U} -> A -> B -> A = \\x y. x;\nf"),
        "λ {A} {B} x y. x\n  :\n{A : U}{B : U} → A → B → A\n"
    );
}

// 隐式插入
// --------------------------------------------------------------------------------

#[test]
fn implicit_insertion_on_explicit_application() {
    // `id U`：隐式 A 插入后解为 U，整个项 : U
    assert_eq!(
        nf("let id : {A : U} -> A -> A = \\x. x;\nid U\n"),
        "U\n  :\nU\n"
    );
    // 位置隐式实参：`id {U}` 不给显式实参，类型停在 U → U
    assert_eq!(
        ty("let id : {A : U} -> A -> A = \\x. x;\nid {U}\n"),
        "U → U\n"
    );
    // const 双隐式：命名实参 `{B = U}` 按名定位，其余插入
    assert_eq!(
        ty("let const : {A B} -> A -> B -> A = \\x y. x;\nconst {B = U} U U\n"),
        "U\n"
    );
}

#[test]
fn implicit_lambda_skips_insertion() {
    // `\{A} x. x` 已显式拿住隐式 binder：检查到 `{A} -> A -> A` 不补
    // meta（无插入元）；域洞被 cod `A -> A` 的 `: U` 检查合法解为 U
    assert_eq!(
        nf("let insert : {A} -> A -> A = \\{A} x. x;\ninsert\n"),
        "λ {A} x. x\n  :\n{A : U} → A → A\n"
    );
    // 非隐式 λ 检查到隐式 Pi：插入 binder（λ 的 binder 与 Pi 名不同侧）——
    // 参考版/性能版同输出；`λx. x` 对 `{A} -> A -> A` 补 A
    assert_eq!(
        nf("let f : {A : U} -> A -> A = \\x. x;\nf\n"),
        "λ {A} x. x\n  :\n{A : U} → A → A\n"
    );
}

#[test]
fn inserted_binder_invisible_to_source_names() {
    // 插入的隐式 binder A 不遮蔽同名 def：`\x. A` 的 A 解析到外层 def
    // （类型 Nat 而非插入 binder 的 U）——解析错会 Cannot unify U vs Nat
    let src = "\
let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
let two : Nat = \\N s z. s (s z);\n\
let A : Nat = two;\n\
let f : {A : U} -> Nat -> Nat = \\x. A;\n\
f\n";
    assert_eq!(
        nf(src),
        "λ {A} x N s z. s (s z)\n  :\n\
         {A : U} → ((N : U) → (N → N) → N → N) → (N : U) → (N → N) → N → N\n"
    );
    // 源码写出的隐式 λ binder 可见且免插：`\{A} x. x` 的 A 是本层 binder，
    // 检查对 `{A} -> A -> A` 直接匹配（不补 inserted binder）
    assert_eq!(
        nf("let f : {A : U} -> A -> A = \\{A} x. x;\nf\n"),
        "λ {A} x. x\n  :\n{A : U} → A → A\n"
    );
}

// 命名隐式实参与命名 λ
// --------------------------------------------------------------------------------

#[test]
fn named_lambda_matches_by_pi_name() {
    // `\{B = B}`：引用名 B 与 Pi binder B 匹配——{A B C} 三个隐式全由
    // 插 binder 路径补上，named binder 按名定位（本地名 B 绑定）
    assert_eq!(
        elab("let namedLam : {A B C} -> A -> B -> C -> A = \\{B = B} a b c. a;\nnamedLam\n"),
        "let ?0 = U;\nlet ?1 = λ x1. U;\nlet ?2 = λ x1 x2. U;\n\n\
         let namedLam : {A : ?0}{B : ?1 A}{C : ?2 A B} → A → B → C → A\n\
         \x20 = λ {A} {B} {C} a b c. a;\n\nnamedLam\n"
    );
}

#[test]
fn no_named_implicit_argument_error() {
    assert_error_at(
        "let const : {A B} -> A -> B -> A = \\x y. x;\nconst {C = U} U\n",
        2,
        1,
        "No named implicit argument with name C",
    );
}

#[test]
fn named_lambda_cannot_be_inferred() {
    assert_error_at(
        "\\{B = x} y. y",
        1,
        1,
        "Cannot infer type for lambda with named argument",
    );
}

#[test]
fn icit_mismatch_error() {
    // `{u}` 隐式实参应用到显式 Pi 头
    assert_error_at(
        "let g : U -> U -> U = \\x y. x;\ng {U}\n",
        2,
        1,
        "Function icitness mismatch: expected implicit, got explicit.",
    );
    // 反方向（显式实参 vs 隐式 Pi）在 check 侧被插 binder 捕获，不走失配：
    // insert 吞掉 {A} 后头类型是 U，显式实参 U 触发合成 Pi 的 Cannot unify
    // （位置 = spine 起点）
    assert_eq!(
        ty("let f : {A : U} -> U = U;\nf U U\n"),
        "(stdin):2:1:\n  |\n2 | f U U\n  | ^\nCannot unify expected type\n\n  U\n\n\
         with inferred type\n\n  (x : ?1) → ?2 x\n"
    );
}

// 错误消息与位置
// --------------------------------------------------------------------------------

#[test]
fn name_not_in_scope() {
    assert_error_at("id", 1, 1, "Name not in scope: id");
}

#[test]
fn cannot_unify_with_implicit_metas() {
    // `id id`：第一个 id 类型显式 Pi，第二个 id 检查到其域洞（λ 头）
    // ——期望 U，推断出函数类型
    let src = "let id : {A : U} -> A -> A\n  = \\x. x;\nlet bar : U = id id;\nbar\n";
    let out = nf(src);
    assert!(out.contains("Cannot unify expected type"), "{out}");
    assert_parity(src);
}

// 上游示例套件与压力
// --------------------------------------------------------------------------------

#[test]
fn ex1_zoo_suite() {
    // EX1（上游 readme 示例套件）type 模式：church 100 全展开的 Eq 类型
    let out = ty(L04_implicit::EX1_SRC);
    assert!(
        out.starts_with("(P : ((N : U) → (N → N) → N → N) → U) → P (λ N s z. s ("),
        "前置不符：\n{out}"
    );
    // nf = refl 的展开
    assert!(nf(L04_implicit::EX1_SRC).starts_with("λ _ px. px\n"), "nf 不符");
    assert_parity(L04_implicit::EX1_SRC);
}

/// 深度压力：church 模式在默认栈线程上跑通（同 L03 套件口径：
/// with_big_stack 供参考版递归路径使用）。
#[test]
fn deep_church_under_big_stack() {
    use L04_implicit::bump_spine_iter::solve_src;
    let src = solve_src(11);
    with_big_stack(move || {
        assert_eq!(ty(&src), fast::main_with("type", &src));
    });
}

/// 在指定栈大小的线程里跑（深度负载：参考版 eval/quote/pretty 全递归）。
fn with_big_stack(f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(512 * 1024 * 1024)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap();
}

// 注：消融开关（L04_NO_CONV_MEMO / L04_NO_NAME_MAP）的「只影响性能、
// 不影响输出」契约由性能版内嵌互检测试覆盖（开关下输出与参考版仍逐字节
// 一致）；env 经 LazyLock 每进程只读一次，跨进程断言交由 measure 脚本。