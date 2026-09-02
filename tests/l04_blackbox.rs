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

// 求解与 pattern unification（补充黑盒）
// --------------------------------------------------------------------------------
//
// 与 L03 共享 unify/solve 骨架，但插入机制制造出 L04 特有的方程形态：
//   - check 侧 binder icit 失配（隐式 λ ↔ 显式 Π）在 unify 层报 Π/Π 失配
//     （与 App 侧 `{u}` 实参的 Function icitness mismatch 是两条路径）；
//   - 插入的隐式 meta 由**显式实参的类型**求解（`const U U` 双 meta 全解、
//     `id Nat two` 的 A 被解成 U 而非 Nat）；
//   - 部分插入：多隐式只喂一实参，余 meta 悬挂（`?3 → U`）；
//   - 同号 flex-flex（cod 双求值）逐实参比较，不误入 solve；
//   - 中性头套中性实参（`B (?m …)`）走通（L04 移除 unify 长度 fail-fast
//     的回归，readme 明示与 L03 的语义差别）。

#[test]
fn check_side_pi_icit_mismatch() {
    // `\{A} x. x` 的 binder 是隐式，目标 Π 是显式 → binder 匹配失败，走
    // infer 路径，Π/Π icit 失配在 unify 报 Cannot unify，两侧类型都显示。
    let src = "let f : (A : U) -> A -> A = \\{A} x. x;\nf U\n";
    let out = ty(src);
    assert!(
        out.contains("Cannot unify expected type\n\n  (A : U) → A → A\n\nwith inferred type\n\n  {A : ?0}(x : ?1 A) → ?1 A"),
        "{out}"
    );
    assert_error_at(src, 1, 29, "Cannot unify expected type");
}

#[test]
fn named_lambda_wrong_name_falls_back_to_infer() {
    // `\{B = x}` 引用名 B 与 Pi binder A 不匹配 → 落到 check 尾案 infer，
    // 命名 λ 不可推断。
    assert_error_at(
        "let f : {A : U} -> A -> A = \\{B = x} x. x;\nf\n",
        1,
        29,
        "Cannot infer type for lambda with named argument",
    );
}

#[test]
fn implicit_metas_solved_by_explicit_arg_types() {
    // `const U U`：两个插入的隐式 meta 都由显式实参的类型求解
    // （`?2 = U`、`?3 = U`），nf 折叠为 U。
    let src = "let const : {A B} -> A -> B -> A = \\a b. a;\nconst U U\n";
    assert_eq!(nf(src), "U\n  :\nU\n");
    assert_eq!(
        elab(src),
        "let ?0 = U;\nlet ?1 = λ x1. U;\nlet ?2 = U;\nlet ?3 = U;\n\n\
         let const : {A : ?0}{B : ?1 A} → A → B → A\n\
         \x20 = λ {A} {B} a b. a;\n\nconst {?2} {?3} U U\n"
    );
    assert_parity(src);
}

#[test]
fn partial_insertion_leaves_meta_unsolved() {
    // `f U`：f 有两个隐式 {A B}，只喂一个显式实参 → A 由实参类型求解，
    // B 悬挂（`?3 = ?`），类型停在 `?3 → U`。
    let src = "let f : {A B} -> A -> B -> A = \\a b. a;\nf U\n";
    assert_eq!(nf(src), "λ b. U\n  :\n?3 → U\n");
    assert_eq!(
        elab(src),
        "let ?0 = U;\nlet ?1 = λ x1. U;\nlet ?2 = U;\nlet ?3 = ?;\n\n\
         let f : {A : ?0}{B : ?1 A} → A → B → A\n\
         \x20 = λ {A} {B} a b. a;\n\nf {?2} {?3} U\n"
    );
    assert_parity(src);
}

#[test]
fn flex_flex_same_sign_implicit_regression() {
    // 同号 flex-flex 的隐式版（L03 e541de0 回归移植）：`g {w}` 在 cod 位置
    // 被两处独立求值，同一未解 meta 以两个同实参 spine 相遇——必须逐实参
    // 比较，不能误入 solve（occurs check 对同号必败）。
    let src = "\
let g : {w : U} -> _ = \\{w}. _;\n\
let f : {w : U} -> U -> g {w} = \\{w} x. _;\n\
let test : {w : U} -> U -> g {w} = \\{w} x. f {w} x;\n\
test\n";
    assert_eq!(nf(src), "λ {w} x. ?2 w x\n  :\n{w : U} → U → ?1 w\n");
    assert_eq!(
        elab(src),
        "let ?0 = λ x1. U;\nlet ?1 = ?;\nlet ?2 = ?;\n\n\
         let g : {w : U} → ?0 w\n  = λ {w}. ?1 w;\n\n\
         let f : {w : U} → U → g {w}\n  = λ {w} x. ?2 w x;\n\n\
         let test : {w : U} → U → g {w}\n  = λ {w} x. f {w} x;\n\n\
         test\n"
    );
}

#[test]
fn hole_in_implicit_lambda_body_unsolved() {
    // `\{A}. _` 体内洞的 meta 挂 binder 实参，`f {U}` 位置实参喂 A 后
    // 洞仍不闭合：nf 以 spine 形态 `?0 U` 展开。
    let src = "let f : {A : U} -> A = \\{A}. _;\nf {U}\n";
    assert_eq!(nf(src), "?0 U\n  :\nU\n");
    assert_eq!(
        elab(src),
        "let ?0 = ?;\n\n\
         let f : {A : U} → A\n  = λ {A}. ?0 A;\n\nf {U}\n"
    );
    assert_parity(src);
}

#[test]
fn neutral_eta_through_implicit_pi() {
    // 中性 `id` 检查到隐式 Π：check 先插入隐式 binder（`λ {A}.`），体内
    // 再为中性 id 插入 meta 并沿 Π/Π η 解出 `?0 := λ x1. x1`。
    let src = "let id : {A : U} -> A -> A = \\x. x;\n\
               let f : {A : U} -> A -> A = id;\nf\n";
    assert_eq!(nf(src), "λ {A} x. x\n  :\n{A : U} → A → A\n");
    assert_eq!(
        elab(src),
        "let ?0 = λ x1. x1;\n\n\
         let id : {A : U} → A → A\n  = λ {A} x. x;\n\n\
         let f : {A : U} → A → A\n  = λ {A}. id {?0 A};\n\nf\n"
    );
    assert_parity(src);
}

#[test]
fn def_unfolds_through_explicit_implicit_arg() {
    // `\{A} x. id {A} x`：显式隐式实参 + 应用，nf 折叠 id 的展开为恒等。
    let src = "let id : {A : U} -> A -> A = \\x. x;\n\\{A} x. id {A} x\n";
    assert_eq!(nf(src), "λ {A} x. x\n  :\n{A : U}(x : A) → A\n");
    assert_eq!(
        elab(src),
        "let ?0 = U;\nlet ?1 = λ x1. x1;\n\n\
         let id : {A : U} → A → A\n  = λ {A} x. x;\n\nλ {A} x. id {A} x\n"
    );
    assert_parity(src);
}

#[test]
fn explicit_binder_eta_fails_for_implicit_id() {
    // `\A x. id A x` 对隐式 id 不可作 η：`id A` 的插入 meta 解成 A 的类型
    // 洞（`?0`），不再是 Π，应用 x 触发合成 Π 失败。反例说明隐式 id 的
    // η 形式必须是 `\{A} x. id {A} x`。
    let src = "let id : {A : U} -> A -> A = \\x. x;\n\\A x. id A x\n";
    let out = ty(src);
    assert!(
        out.contains("Cannot unify expected type\n\n  ?0\n\nwith inferred type\n\n  (x' : ?3 A x) → ?4 A x x'"),
        "{out}"
    );
    assert_error_at(src, 2, 7, "Cannot unify expected type");
}

#[test]
fn implicit_solved_to_function_type_from_lambda_arg() {
    // `id (\x. x)`：插入的 A 由实参 lambda 的推断类型求解为函数类型。
    let src = "let id : {A : U} -> A -> A = \\x. x;\nid (\\x. x)\n";
    assert_eq!(nf(src), "λ x. x\n  :\n(x : ?1) → ?1\n");
    assert_eq!(
        elab(src),
        "let ?0 = (x : ?1) → ?1;\nlet ?1 = ?;\n\n\
         let id : {A : U} → A → A\n  = λ {A} x. x;\n\nid {?0} (λ x. x)\n"
    );
    assert_parity(src);
}

#[test]
fn let_with_hole_annotation_and_shadowing() {
    // `let x : _ = U;`：注解洞与省略注解等价，类型 meta 由定义求解。
    for src in ["let x : _ = U;\nx\n", "let x = U;\nx\n"] {
        assert_eq!(nf(src), "U\n  :\nU\n");
        assert_eq!(elab(src), "let ?0 = U;\n\nlet x : ?0\n  = U;\n\nx\n");
        assert_parity(src);
    }
    // 同名遮蔽：pretty 层给后一个定义改名（x'），引用指向内层。
    let src = "let x : U = U;\nlet x : U = x;\nx\n";
    assert_eq!(nf(src), "U\n  :\nU\n");
    assert_eq!(
        elab(src),
        "\nlet x : U\n  = U;\n\nlet x' : U\n  = x;\n\nx'\n"
    );
    assert_parity(src);
}

#[test]
fn named_lambda_middle_binder_matches() {
    // `\{C = c}`：前两个隐式 A、B 由插入 binder 补上，命名 binder 按 Pi
    // 名 C 定位（本地名 c 绑定），尾实参 c' 是 C 的值。
    let src = "let f : {A B C} -> A -> B -> C -> A = \\{C = c} a b c. a;\nf\n";
    assert_eq!(
        nf(src),
        "λ {A} {B} {c} a b c'. a\n  :\n{A : U}{B : U}{C : U} → A → B → C → A\n"
    );
    assert_eq!(
        elab(src),
        "let ?0 = U;\nlet ?1 = λ x1. U;\nlet ?2 = λ x1 x2. U;\n\n\
         let f : {A : ?0}{B : ?1 A}{C : ?2 A B} → A → B → C → A\n\
         \x20 = λ {A} {B} {c} a b c'. a;\n\nf\n"
    );
    assert_parity(src);
}

#[test]
fn named_arg_requires_implicit_prefix() {
    // 命名实参要求头部是隐式 Π；对显式 Π 头直接报错。
    assert_error_at(
        "let f : (A : U) -> U -> U = \\A x. x;\nf {A = U} U\n",
        2,
        1,
        "No named implicit argument with name A",
    );
}

#[test]
fn named_args_processed_in_order() {
    // `f {C = U} {A = U}`：先按 C 定位（补 A、B 两个 meta），C 消化后类型
    // 已是显式 Π，再找 A 失败。
    assert_error_at(
        "let f : {A B C : U} -> A -> B -> C -> A = \\a b c. a;\nf {C = U} {A = U} U\n",
        2,
        1,
        "No named implicit argument with name A",
    );
    // 单个命名实参按名定位、其余插入：`const {B = U} U` 停在 `U → U`；
    // elab 里命名实参的名被定位消费，项里显示为位置 `{U}`。
    let src = "let const : {A B} -> A -> B -> A = \\a b. a;\nconst {B = U} U\n";
    assert_eq!(nf(src), "λ b. U\n  :\nU → U\n");
    assert_eq!(
        elab(src),
        "let ?0 = U;\nlet ?1 = λ x1. U;\nlet ?2 = U;\n\n\
         let const : {A : ?0}{B : ?1 A} → A → B → A\n\
         \x20 = λ {A} {B} a b. a;\n\nconst {?2} {U} U\n"
    );
    assert_parity(src);
}

#[test]
fn comp_neutral_head_applied_to_neutral_arg() {
    // L04 移除 L03 的 unify 长度 fail-fast 的回归（readme）：隐式插入大量
    // 制造 `B (?m …)` 形态（中性头应用到中性实参），必须逐实参比较。
    let src = "\
let comp : {A}{B : A -> U}{C : {a} -> B a -> U}\n\
  (f : {a}(b : B a) -> C b)\n\
  (g : (a : A) -> B a)\n\
  (a : A)\n\
  -> C (g a)\n\
  = \\f g a. f (g a);\n\
comp\n";
    assert_eq!(
        nf(src),
        "λ {A} {B} {C} f g a. f {a} (g a)\n  :\n\
         {A : U}{B : A → U}{C : {a : A} → B a → U}(f : {a : A}(b : B a) → C {a} b)(g : (a : A) → B a)(a : A) → C {a} (g a)\n"
    );
    let out = elab(src);
    assert!(out.contains("let ?5 = λ x1 x2 x3 x4 x5 x6. x6;\n"), "{out}");
    assert!(out.contains("f {?5 A B C f g a} (g a);\n"), "{out}");
    assert_parity(src);
}

#[test]
fn scoped_loop_keeps_meta_unsolved() {
    // `z = \{A}. f {A}` 与 f 的洞类型互相引用：解不闭合，保持未解而不报错。
    let src = "\
let f : {A : U} -> A = \\{A}. _;\n\
let z : {A : U} -> A = \\{A}. f {A};\n\
z\n";
    assert_eq!(nf(src), "λ {A}. ?0 A\n  :\n{A : U} → A\n");
    assert_eq!(
        elab(src),
        "let ?0 = ?;\n\n\
         let f : {A : U} → A\n  = λ {A}. ?0 A;\n\n\
         let z : {A : U} → A\n  = λ {A}. f {A};\n\nz\n"
    );
    assert_parity(src);
}

#[test]
fn implicit_meta_solved_by_argument_type_not_value() {
    // `id Nat two`：插入的 A 由显式实参 **Nat 的类型** U 求解（而非值
    // Nat），于是 `id Nat : U`，再应用 two 时合成 Π 失败。要传 Nat 必须
    // 显式写 `{Nat}`。
    let src = "\
let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
let two : Nat = \\N s z. s (s z);\n\
let id : {A : U} -> A -> A = \\x. x;\n\
id Nat two\n";
    let out = ty(src);
    assert!(
        out.contains("Cannot unify expected type\n\n  U\n\nwith inferred type\n\n  (x : ?1) → ?2 x"),
        "{out}"
    );
    assert_error_at(src, 4, 1, "Cannot unify expected type");

    let ok = "\
let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
let two : Nat = \\N s z. s (s z);\n\
let id : {A : U} -> A -> A = \\x. x;\n\
id {Nat} two\n";
    assert_eq!(nf(ok), "λ N s z. s (s z)\n  :\n(N : U) → (N → N) → N → N\n");
    assert_eq!(
        elab(ok),
        "\nlet Nat : U\n  = (N : U) → (N → N) → N → N;\n\n\
         let two : Nat\n  = λ N s z. s (s z);\n\n\
         let id : {A : U} → A → A\n  = λ {A} x. x;\n\n\
         id {Nat} two\n"
    );
    assert_parity(ok);
}

#[test]
fn implicit_self_application_synthesizes_pi() {
    // `\{A} x. x x`：x 的类型洞应用 → 合成 Π 与洞类型合一失败，期望侧
    // 显示 spine `?1 A`。
    let src = "\\{A} x. x x\n";
    let out = ty(src);
    assert!(
        out.contains("Cannot unify expected type\n\n  ?1 A\n\nwith inferred type\n\n  (x' : ?2 A x) → ?3 A x x'"),
        "{out}"
    );
    assert_error_at(src, 1, 9, "Cannot unify expected type");
}

#[test]
fn non_pattern_implicit_spine_leaves_meta_unsolved() {
    // `f (f {U})`：外层插入 meta 的 spine 含非变量实参（`?0 U`），非模式
    // 方程解不了但不报错，nf 以 spine 形态展开。
    let src = "let f : {A : U} -> A = \\{A}. _;\nf (f {U})\n";
    assert_eq!(nf(src), "?0 ((x : U) → ?3 x) (?0 U)\n  :\n?3 (?0 U)\n");
    assert_eq!(
        elab(src),
        "let ?0 = ?;\nlet ?1 = (x : U) → ?3 x;\nlet ?2 = U;\nlet ?3 = ?;\n\n\
         let f : {A : U} → A\n  = λ {A}. ?0 A;\n\nf {?1} (f {U})\n"
    );
    assert_parity(src);
}

#[test]
fn explicit_app_after_insertion_synthesizes_pi() {
    // `f U`（f : {A : U} → A）：插入 A 后余类型是 meta（非 Π），显式实参
    // 触发合成 Π——nf 里 `f {?1} U` 的 ?1 解为 (x : U) → ?3 x。
    let src = "let f : {A : U} -> A = \\{A}. _;\nf U\n";
    assert_eq!(nf(src), "?0 ((x : U) → ?3 x) U\n  :\n?3 U\n");
    assert_eq!(
        elab(src),
        "let ?0 = ?;\nlet ?1 = (x : U) → ?3 x;\nlet ?2 = U;\nlet ?3 = ?;\n\n\
         let f : {A : U} → A\n  = λ {A}. ?0 A;\n\nf {?1} U\n"
    );
    assert_parity(src);
}

#[test]
fn explicit_implicit_arg_needs_no_insertion_meta() {
    // `id {U} U`：位置隐式实参直接给值，不产生插入 meta（elab 空 meta）。
    let src = "let id : {A : U} -> A -> A = \\x. x;\nid {U} U\n";
    assert_eq!(nf(src), "U\n  :\nU\n");
    assert_eq!(
        elab(src),
        "\nlet id : {A : U} → A → A\n  = λ {A} x. x;\n\nid {U} U\n"
    );
    assert_parity(src);
}

#[test]
fn codomain_does_not_use_implicit_binder() {
    // `{A : U} -> U`：A 不出现在余域；顶层 infer 不插入，nf 折叠为
    // `λ {A}. U`（let-def 展开），elab 无 meta。
    let src = "let f : {A : U} -> U = U;\nf\n";
    assert_eq!(nf(src), "λ {A}. U\n  :\n{A : U} → U\n");
    assert_eq!(elab(src), "\nlet f : {A : U} → U\n  = λ {A}. U;\n\nf\n");
    assert_parity(src);
}

#[test]
fn binder_mismatch_error_parity_complex() {
    // 两则 λ binder 与 Π 结构错位导致的错误，双实现逐字节一致：
    //   - `\A g. g A` 的显式 A 与隐式 Π binder 错位：整体被插 binder 包裹，
    //     体内 g 应用 A 时合成 Π 失败，spine 呈 `?0 A A`；
    //   - 显式 Π 后跟隐式 {B}：λ 的 b 与隐式 B 错位 → 插 binder，
    //     `\a x. U` 的 x 撞到 cod 的 U。
    assert_error_at(
        "let f : {A : U} -> (A -> U) -> U = \\A g. g A;\nf {A = Nat} (\\n. n)\n",
        1,
        42,
        "Cannot unify expected type",
    );
    assert_error_at(
        "let f : (A : U) -> {B : A -> U} -> (a : A) -> B a -> U = \\A b a x. U;\nf U {B = \\x. x} U U\n",
        1,
        58,
        "Cannot unify expected type",
    );
}

#[test]
fn implicit_chain_workload_parity_and_elab() {
    use L04_implicit::bump_spine_iter::implicit_src;
    // k=1（2^(1+1)=4 层，p1..p3 链 + 尾项 p0）：逐层一次插入 + 一次
    // `? := church` 求解；elab 金样。
    let src = implicit_src(1);
    let out = elab(&src);
    assert!(out.contains("let ?0 = (N : U) → (N → N) → N → N;\n"), "{out}");
    assert!(out.contains("let ?2 = (N : U) → (N → N) → N → N;\n"), "{out}");
    assert!(out.contains("let p3 : Nat\n  = id {?2} p2;\n"), "{out}");
    assert!(out.ends_with("p0\n"), "{out}");
    // k=2、k=3：三模式与参考版逐字节一致，nf 折叠为 p0 的展开。
    for k in [2u32, 3] {
        let src = implicit_src(k);
        assert_parity(&src);
        assert_eq!(
            nf(&src),
            "λ N s z. s (s z)\n  :\n(N : U) → (N → N) → N → N\n"
        );
    }
}

// 「连续链长度 fail-fast」回归（L04 本就无此守卫）：钉住 η 吸收与 meta 实参
// 短侧两类误杀形态，防止将来从 L03 重新移植冠军配方时把守卫带回来。
const ETA_ABSORB_CONV_SRC: &str = "\
let big : (P : (U -> U) -> U) -> (h : U -> U -> U) -> (y : U)
       -> (v : P (h y)) -> (f : P (\\x. h y x) -> U) -> U
      = \\P h y v f. f v;
big
";

const META_SHORTER_SIDE_SRC: &str = "\
let big : (P : (U -> U) -> U) -> (h : U -> U -> U) -> (y : U)
       -> (v : P (h y)) -> (f : P _ -> U) -> U
      = \\P h y v f. f v;
big
";

#[test]
fn unify_eta_absorption_and_meta_shorter_side() {
    for src in [ETA_ABSORB_CONV_SRC, META_SHORTER_SIDE_SRC] {
        let out = ty(src);
        assert!(!out.contains("Cannot unify"), "{out}");
        assert_parity(src);
    }
}

// 注：消融开关（L04_NO_CONV_MEMO / L04_NO_NAME_MAP）的「只影响性能、
// 不影响输出」契约由性能版内嵌互检测试覆盖（开关下输出与参考版仍逐字节
// 一致）；env 经 LazyLock 每进程只读一次，跨进程断言交由 measure 脚本。