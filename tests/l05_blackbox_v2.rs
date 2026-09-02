//! L05_pruning 黑盒测试套件 · 第二卷（v2）。
//!
//! 与 `tests/l05_blackbox.rs`（第一卷）互补：第一卷钉住上游 ex1 全家桶、
//! 非线性可解/不可解、交集剪枝基线、pr1/pr2/pr3 等主干场景；本卷面向
//! **边缘与分支**：
//!   - 词法/语法怪癖（`--` 吞 `-->`、块注释不嵌套/未闭合、尾随垃圾被忽略、
//!     `_x` = 洞+变量、Unicode λ、CJK 标识符、数字/`€` token）；
//!   - AppPruning 掩码显示全谱（匿名 binder `@i`、源隐式 binder 在掩码里
//!     按上游 `Cxt.bind` 恒为 `Some(Expl)` 的怪癖、define 层塌缩）；
//!   - unify 各分派支：intersect 取交保留公共槽/等长全保/非变量回落
//!     unify_sp、flex_flex 异头等长与不等长、η×剪枝、rename 的
//!     prune_vflex 越界变量剪枝；
//!   - 隐式插入的命名路径（按名定位、乱序、重名的失败文案）；
//!   - 错误渲染的字节级布局（两位行号对齐、Tab/CJK 的字节列、CRLF）；
//!   - typed-meta telescope 与 meta 编号的可复现性；
//!   - 负载生成器（含 prune/solve/church）的小 k 全模式互检与大 k 深栈互检。
//!
//! 双 oracle 与第一卷相同：
//!   1. golden 输出串（参考版语义推导 + 实测核对，全部逐字节断言或由
//!      `render_err` 按 `display_error` 的构造规则重建）；
//!   2. 参考版（`mod.rs`）↔ 性能版（`bump_spine_iter.rs`）**三模式**
//!      （nf/type/elab）逐字节互检。
//!
//! 已核对的「按实现如此、与上游 megaparsec 有差」的怪癖，均在对应测试的
//! 文档注释里标明（解析器不强制 EOF：首项完整后尾随 token——包括无法识别
//! 的字节——被丢弃）。

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

/// 按 `display_error`（megaparsec 风格）的构造规则重建期望错误块。
fn render_err(line: usize, col: usize, src_line: &str, msg: &str) -> String {
    let lnum = line.to_string();
    let lpad = " ".repeat(lnum.len());
    format!(
        "(stdin):{line}:{col}:\n{lpad} |\n{lnum} | {src_line}\n{lpad} | {}^\n{msg}\n",
        " ".repeat(col - 1)
    )
}

/// 报错输出 = 重建的完整错误块（位置、pad 宽、caret 列逐字节）+ 双实现互检。
fn assert_err_block(src: &str, line: usize, col: usize, src_line: &str, msg: &str) {
    assert_eq!(ty(src), render_err(line, col, src_line, msg));
    assert_parity(src);
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

fn with_big_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(512 * 1024 * 1024)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

const HELP: &str = "usage: elabzoo-pruning [--help|elab|nf|type]\n  --help : display this message\n  elab   : read & elaborate expression from stdin\n  nf     : read & typecheck expression from stdin, print its normal form and type\n  type   : read & typecheck expression from stdin, print its type\n";

/// `Eq / refl / the` 三件套前奏（上游 05 触发 unification 的标准模式）。
const PRELUDE: &str = r#"let Eq : {A : U} -> A -> A -> U = \{A} x y. (P : A -> U) -> P x -> P y;
let refl : {A : U}{x : A} -> Eq {A} x x = \ _ px. px;
let the : (A : U) -> A -> A = \ _ x. x;
"#;

fn zoo(body: &str) -> String {
    format!("{PRELUDE}{body}\nU\n")
}

// --------------------------------------------------------------------------------
// zoo 用例的 body 与 golden
// --------------------------------------------------------------------------------

/// intersect 取交：`m {a} b =? m {a} c`——公共槽 `a` 保留、差异槽剪除。
const BODY_INTERSECT_KEEP: &str = r#"let m : {A : U} -> U -> U = _;
let test = \ a b c. the (Eq (m {a} b) (m {a} c)) refl;"#;
const GOLD_INTERSECT_KEEP: &str = r#"let ?0 : (A : U) → U → U = λ A x1. ?8 A;
let ?1 : U = (a : U)(b : U)(c : U)(P : U → U) → P (?8 a) → P (?8 a);
let ?2 : U = U;
let ?3 : (a : U) → U = λ a. U;
let ?4 : (a : U)(b : U) → U = λ a b. U;
let ?5 : (a : U)(b : U)(c : U) → U = λ a b c. U;
let ?6 : (a : U)(b : U)(c : U) → U = λ a b c. U;
let ?7 : (a : U)(b : U)(c : U) → U = λ a b c. ?8 a;
let ?8 : (A : U) → U = ?;

let Eq : {A : U} → A → A → U
  = λ {A} x y. (P : A → U) → P x → P y;

let refl : {A : U}{x : A} → Eq {A} x x
  = λ {A} {x} _ px. px;

let the : (A : U) → A → A
  = λ _ x. x;

let m : {A : U} → U → U
  = λ {A}. ?0 A;

let test : ?1
  = λ a b c. the (Eq {?5 a b c} (m {a} b) (m {a} c)) (refl {?6 a b c} {?7 a b c});

U
"#;

/// 同头 flex 等长同 spine：`m a b =? m a b`——注意经 refl 插入链后实走
/// **flex_flex**（?x 的 telescope spine vs ?0 的 spine，长度相等、解长者
/// 即 ?0），m 的顶层 meta 被解为转发 λ，`?6`（refl 的 x）保持未解。
const BODY_INTERSECT_EQUAL: &str = r#"let m : U -> U -> U = _;
let test = \ a b. the (Eq (m a b) (m a b)) refl;"#;
const GOLD_INTERSECT_EQUAL: &str = r#"let ?0 : U → U → U = λ x0 x1. ?6 x0 x1;
let ?1 : U = (a : U)(b : U)(P : U → U) → P (?6 a b) → P (?6 a b);
let ?2 : U = U;
let ?3 : (a : U) → U = λ a. U;
let ?4 : (a : U)(b : U) → U = λ a b. U;
let ?5 : (a : U)(b : U) → U = λ a b. U;
let ?6 : (a : U)(b : U) → U = ?;

let Eq : {A : U} → A → A → U
  = λ {A} x y. (P : A → U) → P x → P y;

let refl : {A : U}{x : A} → Eq {A} x x
  = λ {A} {x} _ px. px;

let the : (A : U) → A → A
  = λ _ x. x;

let m : U → U → U
  = ?0;

let test : ?1
  = λ a b. the (Eq {?4 a b} (m a b) (m a b)) (refl {?5 a b} {?6 a b});

U
"#;

/// 非变量实参回落 unify_sp：`m a b =? m (f a) b`——intersect_go 遇 Flex
/// 实参返回 None，逐实参比较反而把 `f` 解成 `λ x0. x0`。
const BODY_FALLBACK_NONVAR: &str = r#"let f : U -> U = _;
let m : U -> U -> U = _;
let test = \ a b. the (Eq (m a b) (m (f a) b)) refl;"#;
const GOLD_FALLBACK_NONVAR: &str = r#"let ?0 : U → U = λ x0. x0;
let ?1 : U → U → U = λ x0 x1. ?7 x0 x1;
let ?2 : U = (a : U)(b : U)(P : U → U) → P (?7 a b) → P (?7 a b);
let ?3 : U = U;
let ?4 : (a : U) → U = λ a. U;
let ?5 : (a : U)(b : U) → U = λ a b. U;
let ?6 : (a : U)(b : U) → U = λ a b. U;
let ?7 : (a : U)(b : U) → U = ?;

let Eq : {A : U} → A → A → U
  = λ {A} x y. (P : A → U) → P x → P y;

let refl : {A : U}{x : A} → Eq {A} x x
  = λ {A} {x} _ px. px;

let the : (A : U) → A → A
  = λ _ x. x;

let f : U → U
  = ?0;

let m : U → U → U
  = ?1;

let test : ?2
  = λ a b. the (Eq {?5 a b} (m a b) (m (f a) b)) (refl {?6 a b} {?7 a b});

U
"#;

/// 异头 flex-flex 等长：`m a =? n a b`——较长侧 `n`（spine 2）被解为
/// `λ x0 x1. ?0 x0`（丢弃 b），较短侧 `m` 保持未解。
const BODY_FLEXFLEX: &str = r#"let m : U -> U = _;
let n : U -> U -> U = _;
let test = \ a b. the (Eq (m a) (n a b)) refl;"#;
const GOLD_FLEXFLEX: &str = r#"let ?0 : U → U = ?;
let ?1 : U → U → U = λ x0 x1. ?0 x0;
let ?2 : U = (a : U)(b : U)(P : U → U) → P (?0 a) → P (?0 a);
let ?3 : U = U;
let ?4 : (a : U) → U = λ a. U;
let ?5 : (a : U)(b : U) → U = λ a b. U;
let ?6 : (a : U)(b : U) → U = λ a b. U;
let ?7 : (a : U)(b : U) → U = λ a b. ?0 a;

let Eq : {A : U} → A → A → U
  = λ {A} x y. (P : A → U) → P x → P y;

let refl : {A : U}{x : A} → Eq {A} x x
  = λ {A} {x} _ px. px;

let the : (A : U) → A → A
  = λ _ x. x;

let m : U → U
  = ?0;

let n : U → U → U
  = ?1;

let test : ?2
  = λ a b. the (Eq {?5 a b} (m a) (n a b)) (refl {?6 a b} {?7 a b});

U
"#;

/// η + intersect：`m a =? \z. m a b`——Lam 侧 η 展开出 `?0 [a, z]`，与
/// `?0 [a, b]` 同头 intersect 剪掉尾槽；`m` 的解 `λ x0 x1. ?7 x0` 丢弃
/// 第二实参，`?7` 成为只依赖 a 的共享 meta。
const BODY_ETA_INTERSECT: &str = r#"let m : U -> U -> U = _;
let test = \ a b. the (Eq (m a) (\ z. m a b)) refl;"#;
const GOLD_ETA_INTERSECT: &str = r#"let ?0 : U → U → U = λ x0 x1. ?7 x0;
let ?1 : U = (a : U)(b : U)(P : (U → U) → U) → P (λ x1. ?7 a) → P (λ z. ?7 a);
let ?2 : U = U;
let ?3 : (a : U) → U = λ a. U;
let ?4 : (a : U)(b : U) → U = λ a b. U → U;
let ?5 : (a : U)(b : U) → U = λ a b. U → U;
let ?6 : (a : U)(b : U) → U → U = λ a b x1. ?7 a;
let ?7 : U → U = ?;

let Eq : {A : U} → A → A → U
  = λ {A} x y. (P : A → U) → P x → P y;

let refl : {A : U}{x : A} → Eq {A} x x
  = λ {A} {x} _ px. px;

let the : (A : U) → A → A
  = λ _ x. x;

let m : U → U → U
  = ?0;

let test : ?1
  = λ a b. the (Eq {?4 a b} (m a) (λ z. m a b)) (refl {?5 a b} {?6 a b});

U
"#;

/// prune_vflex（rename 的 flex 分支）：解 `?0 [x, w]` 时 rhs 含
/// `n y w`——`y` 越出 partial renaming 的定义域，rename 对 `n` 的 spine
/// 剪掉 `y` 槽造新 meta `?8`，`m`、`n` 双双转发到 `?8`。
const BODY_VFLEX_ESCAPE: &str = r#"let m : (x : U) -> U -> U = _;
let n : (y : U)(z : U) -> U = _;
let test = \ x y. the (Eq (m x) (\ w. n y w)) refl;"#;
const GOLD_VFLEX_ESCAPE: &str = r#"let ?0 : (x : U) → U → U = λ x x1. ?8 x1;
let ?1 : (y : U)(z : U) → U = λ y z. ?8 z;
let ?2 : U = (x : U)(y : U)(P : (U → U) → U) → P (λ x1. ?8 x1) → P (λ w. ?8 w);
let ?3 : U = U;
let ?4 : (x : U) → U = λ x. U;
let ?5 : (x : U)(y : U) → U = λ x y. U → U;
let ?6 : (x : U)(y : U) → U = λ x y. U → U;
let ?7 : (x : U)(y : U) → U → U = λ x y x1. ?8 x1;
let ?8 : U → U = ?;

let Eq : {A : U} → A → A → U
  = λ {A} x y. (P : A → U) → P x → P y;

let refl : {A : U}{x : A} → Eq {A} x x
  = λ {A} {x} _ px. px;

let the : (A : U) → A → A
  = λ _ x. x;

let m : (x : U) → U → U
  = ?0;

let n : (y : U)(z : U) → U
  = ?1;

let test : ?2
  = λ x y. the (Eq {?5 x y} (m x) (λ w. n y w)) (refl {?6 x y} {?7 x y});

U
"#;

/// η 正向（L04 无此支：λ 与中性合一）：`(\x. f x) ≡ f`。
const BODY_ETA_POS: &str = r#"let ete : (f : U -> U) -> Eq {U -> U} (\ x. f x) f = \ f. refl;"#;
const GOLD_ETA_POS: &str = r#"let ?0 : (f : U → U) → U = λ f. U → U;
let ?1 : (f : U → U) → U → U = λ f x1. f x1;

let Eq : {A : U} → A → A → U
  = λ {A} x y. (P : A → U) → P x → P y;

let refl : {A : U}{x : A} → Eq {A} x x
  = λ {A} {x} _ px. px;

let the : (A : U) → A → A
  = λ _ x. x;

let ete : (f : U → U) → Eq {U → U} (λ x. f x) f
  = λ f. refl {?0 f} {?1 f};

U
"#;

// 模式与输出骨架
// --------------------------------------------------------------------------------

/// 非 nf/type/elab 模式（含 `--help`）无条件回 HELP，与源码内容无关。
#[test]
fn help_wins_regardless_of_source() {
    for mode in ["--help", "", "nf2", "Type", "NF", "elab ", "-h"] {
        assert_eq!(L05_pruning::main_with(mode, "let {{{ U"), HELP, "mode {mode:?}");
        assert_eq!(fast::main_with(mode, "let {{{ U"), HELP, "fast mode {mode:?}");
    }
}

// 解析器：错误语料与怪癖
// --------------------------------------------------------------------------------

#[test]
fn parse_error_corpus() {
    for src in [
        "",
        "   \n\t",
        "-- just a comment\n",
        "{- block -}",
        "let",
        "let x",
        "let x =",
        "let x = U",
        "let x = U;", // 缺体
        "\\x",
        "\\x.",
        "\\x y", // 缺点
        "(U",
        "{U}",
        "1", // 数字 token 不在文法
        "let x = 1; x",
        ";",
        "{",
        "{x :} -> U", // 冒号后缺类型
        "let _ : = U; _",
        "let x : ; x",
        "-> U",
        "{- {- -} -} U", // 块注释不嵌套：第一个 -} 提前闭合，残 `-}` 无法起手
        "let x = U {- no end\nx", // 未闭合块注释吞掉其余，let 缺分号
    ] {
        assert_eq!(ty(src), "parse error\n", "src: {src:?}");
        assert_parity(src);
    }
}

/// **本层已知怪癖（与上游 megaparsec 的 `eof` 行为有差）**：解析器只取首
/// 个完整表达式，之后的尾随 token——包括 `)`、`{`、`->`、`;`、`+`、甚至
/// 非法字节 `€`——一律被忽略；`--` 先于 `->` 匹配，`U --> U` 里 `-->` 起
/// 行注释。
#[test]
fn trailing_junk_is_ignored() {
    for src in ["U)", "U ) )", "U {", "U ->", "U;", "U + U", "U --> U", "U €", "U {- {- x -} -}"] {
        assert_eq!(ty(src), "U\n", "src: {src:?}");
        assert_parity(src);
    }
}

/// `_` 永远先切成 Hole token（先于 ident）：`_x` = 洞应用于变量 x。
#[test]
fn underscore_prefix_lexes_as_hole_app() {
    assert_eq!(
        ty("_x"),
        render_err(1, 2, "_x", "Name not in scope: x")
    );
    assert_parity("_x");
}

/// Unicode：`λ` 与 `\` 等价；CJK 可作标识符；非 ASCII 非空白字节成 ErrToken
/// （仅在尾随位置被忽略）。
#[test]
fn unicode_sources() {
    assert_eq!(ty("λx. x"), "(x : ?0) → ?0\n");
    assert_parity("λx. x");
    assert_eq!(ty("let 错 = U;\n错"), "U\n");
    assert_parity("let 错 = U;\n错");
    // `λ` 后紧跟 binder（无空格）也成立：ident 贪婪吞 `λx` 后被重新切分
    assert_eq!(ty("\\{x} y. y"), "{x : ?0}(y : ?1 x) → ?1 x\n");
    assert_parity("\\{x} y. y");
}

// 基础推断与 nf
// --------------------------------------------------------------------------------

#[test]
fn basic_type_goldens() {
    // 重复 binder 名在 pretty 里按 fresh 规则加 `'`
    assert_eq!(ty("let f = \\x. \\x. x;\nf\n"), "(x : ?1)(x' : ?2 x) → ?2 x\n");
    assert_parity("let f = \\x. \\x. x;\nf\n");
    // Pi binder 多名共享一个省略的类型注解：各自成洞，A 的洞被 A 的用法解掉
    assert_eq!(ty("let f : {A B} (x : A) -> U = _;\nf\n"), "{A : U}{B : ?1 A}(x : A) → U\n");
    assert_parity("let f : {A B} (x : A) -> U = _;\nf\n");
    // 匿名隐式 binder：不走箭头简写（简写只认 `"_"` + 显式），打印 `{_ : U}`
    assert_eq!(ty("let g : {_ : U} -> U = _;\ng\n"), "{_ : U} → U\n");
    assert_parity("let g : {_ : U} -> U = _;\ng\n");
    // the 的类型参数位置放洞：由实参解出
    assert_eq!(ty("let the : (A : U) -> A -> A = \\_ x. x;\nlet m : U = _;\nthe _ U"), "U\n");
    assert_parity("let the : (A : U) -> A -> A = \\_ x. x;\nlet m : U = _;\nthe _ U");
    // let 注解可省成洞，被值解出
    assert_eq!(ty("let x : _ = U;\nx"), "U\n");
    assert_parity("let x : _ = U;\nx");
    // 洞做函数头（infer Hole 支：类型 meta 套类型 meta）
    assert_eq!(ty("(_ U)"), "?3 U\n");
    assert_parity("(_ U)");
}

#[test]
fn basic_nf_goldens() {
    // β + δ（define 透明展开）
    assert_eq!(nf("let id : U -> U = \\x. x;\nid (id U)"), "U\n  :\nU\n");
    assert_parity("let id : U -> U = \\x. x;\nid (id U)");
    // 未解 meta 的中性应用停在 nf
    assert_eq!(nf("let m : U -> U = _;\nm U"), "?0 U\n  :\nU\n");
    assert_parity("let m : U -> U = _;\nm U");
}

#[test]
fn scope_and_application_errors() {
    // 注解/值都在 define 入范围**之前**检查：自引用不可见
    assert_err_block(
        "let x : x = U;\nx\n",
        1,
        9,
        "let x : x = U;",
        "Name not in scope: x",
    );
    assert_err_block("let x = x;\nU\n", 1, 9, "let x = x;", "Name not in scope: x");
    // λ 体内位置：错误定位到体内项
    assert_error_at(
        "let f : U -> U = \\x. zzz;\nf\n",
        1,
        22,
        "Name not in scope: zzz",
    );
    // 头不是 Π：infer App 合成 Π（域 + 余域挂洞）再与之合一，`U U` 即在此失败
    assert_eq!(
        ty("U U"),
        render_err(
            1,
            1,
            "U U",
            "Cannot unify expected type\n\n  U\n\nwith inferred type\n\n  (x : ?0) → ?1 x"
        )
    );
    // 隐式 Pi 头被显式应用穷尽后仍非 Π：Cannot unify 在实参位置
    assert_error_at(
        "let f : U -> U = \\x. x; f f",
        1,
        27,
        "Cannot unify expected type",
    );
    // let 体内多项尾随（`id id2`）：定位到体内变量
    assert_error_at(
        "let id : {A : U} -> A -> A = \\x. x; id id2",
        1,
        40,
        "Name not in scope: id2",
    );
}

// typed metas 的 elab 显示
// --------------------------------------------------------------------------------

#[test]
fn typed_meta_display_basics() {
    // 顶层两洞：编号 0/1 递增、未解 = `?`，telescope 无 define 时就是类型本身
    assert_eq!(
        elab("let a : U = _;\nlet b : U = _;\nU\n"),
        "let ?0 : U = ?;\nlet ?1 : U = ?;\n\n\
         let a : U\n  = ?0;\n\nlet b : U\n  = ?1;\n\nU\n"
    );
    assert_parity("let a : U = _;\nlet b : U = _;\nU\n");
    // define 不入洞的 telescope（eval 塌缩 Let 层），但占掩码槽（显示时跳过）
    assert_eq!(
        elab("let a : U = U;\nlet b : U = _;\nlet f : (x : U) -> U = \\ x. _;\nU"),
        "let ?0 : U = ?;\nlet ?1 : (x : U) → U = ?;\n\n\
         let a : U\n  = U;\n\nlet b : U\n  = ?0;\n\n\
         let f : (x : U) → U\n  = λ x. ?1 x;\n\nU\n"
    );
    assert_parity("let a : U = U;\nlet b : U = _;\nlet f : (x : U) -> U = \\ x. _;\nU");
    // define 值为洞时（a = _），后续洞的 telescope 同样只剩绑定层
    assert_eq!(
        elab("let a : U = _;\nlet f : (x : U) -> U = \\ x. _;\nU\n"),
        "let ?0 : U = ?;\nlet ?1 : (x : U) → U = ?;\n\n\
         let a : U\n  = ?0;\n\nlet f : (x : U) → U\n  = λ x. ?1 x;\n\nU\n"
    );
    assert_parity("let a : U = _;\nlet f : (x : U) -> U = \\ x. _;\nU\n");
    // `_` 作 let binder：源码名不可见，但类型注解的洞照建
    assert_eq!(
        elab("let _ = U;\nlet y : U = _;\ny\n"),
        "let ?0 : U = U;\nlet ?1 : U = ?;\n\n\
         let _ : ?0\n  = U;\n\nlet y : U\n  = ?1;\n\ny\n"
    );
    assert_parity("let _ = U;\nlet y : U = _;\ny\n");
    // 位置显式实参对隐式 Π 头：insert_t 建的 meta 带类型显示、并被解为 U
    assert_eq!(
        elab("let id : {A : U} -> A -> A = \\x. x;\nlet g : U = id U;\ng\n"),
        "let ?0 : U = U;\n\n\
         let id : {A : U} → A → A\n  = λ {A} x. x;\n\n\
         let g : U\n  = id {?0} U;\n\ng\n"
    );
    assert_parity("let id : {A : U} -> A -> A = \\x. x;\nlet g : U = id U;\ng\n");
}

/// AppPruning 掩码显示：匿名 binder 打 `@位序`；而**源隐式 binder 经
/// `Cxt.bind` 入掩码时 icit 恒为 `Some(Expl)`（上游 Cxt.hs 同款）**——所以
/// `\{A} x. _` 的洞应用打印 `?0 A x` 而非 `?0 {A} x`。
#[test]
fn app_pruning_mask_display() {
    assert_eq!(
        elab("let f : (x : U) -> U = \\_. _;\nU\n"),
        "let ?0 : U → U = ?;\n\n\
         let f : (x : U) → U\n  = λ _. ?0 @0;\n\nU\n"
    );
    assert_parity("let f : (x : U) -> U = \\_. _;\nU\n");
    assert_eq!(
        elab("let f : {A : U}(x : A) -> U = \\{A} x. _;\nU\n"),
        "let ?0 : (A : U)(x : A) → U = ?;\n\n\
         let f : {A : U}(x : A) → U\n  = λ {A} x. ?0 A x;\n\nU\n"
    );
    assert_parity("let f : {A : U}(x : A) -> U = \\{A} x. _;\nU\n");
}

/// 命名隐式 binder `\{B = bb}`：体内本地名是 `bb`，按名定位用 `B`；注解里
/// 省略类型的三个隐式 Pi binder 各成一个洞（telescope `{A : ?0}{B : ?1 A}
/// {C : ?2 A B}`），随后在类型检查中逐级解出。
#[test]
fn named_implicit_lambda() {
    assert_eq!(
        elab("let namedLam : {A B C} -> A -> B -> C -> A = \\{B = bb} a b c. a;\nU\n"),
        "let ?0 : U = U;\nlet ?1 : (A : U) → U = λ A. U;\n\
         let ?2 : (A : U)(B : U) → U = λ A B. U;\n\n\
         let namedLam : {A : ?0}{B : ?1 A}{C : ?2 A B} → A → B → C → A\n\
         \x20 = λ {A} {bb} {C} a b c. a;\n\nU\n"
    );
    assert_parity("let namedLam : {A B C} -> A -> B -> C -> A = \\{B = bb} a b c. a;\nU\n");
}

/// 命名实参按 Pi binder 名定位：一旦越过匹配点继续找同名 binder——隐式前缀
/// 耗尽即 `No named implicit argument`（首个实参 `{C = U}` 消耗掉 A、B 的
/// 插入后，剩余类型已非 Π，后两个命名实参都报缺名）。
#[test]
fn named_implicit_insertion_errors() {
    assert_error_at(
        "let f : {A B C : U} -> U = _;\nf {C = U} {B = U} {A = U}\n",
        2,
        1,
        "No named implicit argument with name B",
    );
    assert_error_at(
        "let f : {A B C : U} -> U = _;\nf {A = U} {A = U}\n",
        2,
        1,
        "No named implicit argument with name A",
    );
}

// unification / pruning 分支
// --------------------------------------------------------------------------------

/// intersect 取交：公共槽 `A` 保留进新 meta 的 telescope，差异槽剪除。
#[test]
fn intersect_prunes_differing_slots() {
    let src = zoo(BODY_INTERSECT_KEEP);
    assert_eq!(elab(&src), GOLD_INTERSECT_KEEP);
    assert_eq!(ty(&src), "U\n");
    assert_parity(&src);
}

#[test]
fn equal_spine_goes_through_flex_flex() {
    let src = zoo(BODY_INTERSECT_EQUAL);
    assert_eq!(elab(&src), GOLD_INTERSECT_EQUAL);
    assert_parity(&src);
}

#[test]
fn intersect_falls_back_to_unify_sp_on_nonvariable() {
    let src = zoo(BODY_FALLBACK_NONVAR);
    assert_eq!(elab(&src), GOLD_FALLBACK_NONVAR);
    assert_parity(&src);
}

#[test]
fn flex_flex_solves_longer_spine() {
    let src = zoo(BODY_FLEXFLEX);
    assert_eq!(elab(&src), GOLD_FLEXFLEX);
    assert_parity(&src);
}

#[test]
fn eta_expansion_then_intersect_pruning() {
    let src = zoo(BODY_ETA_INTERSECT);
    assert_eq!(elab(&src), GOLD_ETA_INTERSECT);
    assert_parity(&src);
}

/// prune_vflex：解 `m` 的方程时 rhs 的 `n y w` 含越界变量 `y`，rename 现场
/// 把 `n` 的 spine 剪成 renaming（`y` 槽剪除、造 `?8`），`m`/`n` 同时转发。
#[test]
fn prune_vflex_prunes_escaping_variable() {
    let src = zoo(BODY_VFLEX_ESCAPE);
    assert_eq!(elab(&src), GOLD_VFLEX_ESCAPE);
    assert_parity(&src);
}

/// η 正向：`\x. f x ≡ f`（f 为 Π 绑定的刚性变量）可判等；解记录显示
/// refl 的 x meta 被 η 规整为 `λ f x1. f x1`。
#[test]
fn eta_unification_positive() {
    let src = zoo(BODY_ETA_POS);
    assert_eq!(ty(&src), "U\n");
    assert_eq!(elab(&src), GOLD_ETA_POS);
    assert_parity(&src);
}

/// η 负向：η 展开后刚性头不同（f vs g；f x vs f (f x)）→ Cannot unify。
#[test]
fn eta_unification_negative() {
    let body1 = r#"let neq : (f : U -> U) -> (g : U -> U) -> Eq {U -> U} (\ x. f x) (\ y. g y) = \ f g. refl;"#;
    let src1 = zoo(body1);
    assert_error_at(&src1, 4, 86, "Cannot unify expected type");
    assert!(
        ty(&src1).contains("P (λ x2. f x2) → P (λ x2. f x2)"),
        "推断侧应显出两侧各自 η 展开后的形态：\n{}",
        ty(&src1)
    );

    let body2 = r#"let neq : (f : U -> U) -> Eq {U -> U} (\ x. f x) (\ x. f (f x)) = \ f. refl;"#;
    let src2 = zoo(body2);
    assert_error_at(&src2, 4, 72, "Cannot unify expected type");
}

/// 非线性依赖前缀 `m a a`（m : (A : U)(x : A) -> U）：第二个 `a` 要先过
/// `A := a` 的类型检查——在**插入 Π 的实参位**就报 `a` vs `U`，根本走不到
/// solve（对照第一卷 nonlinear_unsolvable：那里失败在 prune_ty）。
#[test]
fn nonlinear_dependent_spine_fails_at_argument() {
    let body = r#"let m : (A : U)(x : A) -> U = _;
let test = \ a. the (Eq (m a a) (\ x. U)) refl;"#;
    let src = zoo(body);
    assert_error_at(&src, 5, 30, "Cannot unify expected type");
    assert!(ty(&src).contains("  a\n\nwith inferred type\n\n  U"), "{}", ty(&src));
}

/// 异头 flex-flex `?m ≡ ?n ?m`：先解 `?n := λ x0. ?0`（rhs 是空 spine 的
/// flex，合法 renaming），随后 refl 两侧 `?0` 与 `?1 ?0` 无法合一——
/// occurs 性质的失败落在 Eq 的第二个实参位。
#[test]
fn flex_flex_self_reference_fails_on_refl_side() {
    let body = r#"let m : U = _;
let n : U -> U = _;
let z = the (Eq m (n m)) refl;"#;
    let src = zoo(body);
    assert_error_at(&src, 6, 26, "Cannot unify expected type");
    assert!(
        ty(&src).contains("(P : U → U) → P ?5 → P (?1 ?5)"),
        "期望类型应含自引用应用：\n{}",
        ty(&src)
    );
}

// 错误渲染的字节级布局
// --------------------------------------------------------------------------------

/// 两位行号：pad 宽度随行号位数增长（`   |` 对齐 `10 |`）。
#[test]
fn error_layout_two_digit_line() {
    let src = (0..9)
        .map(|i| format!("let a{} : U = U;\n", i + 1))
        .collect::<String>()
        + "id\n";
    assert_eq!(
        ty(&src),
        render_err(10, 1, "id", "Name not in scope: id")
    );
    assert_parity(&src);
}

/// 列按**字节**计（`line_col`）：CJK/Tab 前缀使 caret 与视觉列错位。
#[test]
fn error_layout_byte_columns() {
    // 「let ok = U; 」= 12 字节，`中` 起始字节列 = 13
    assert_eq!(
        ty("let ok = U; 中 ok\n"),
        render_err(1, 13, "let ok = U; 中 ok", "Name not in scope: 中")
    );
    assert_parity("let ok = U; 中 ok\n");
    // Tab 占 1 字节列
    assert_eq!(
        ty("\tid\n"),
        render_err(1, 2, "\tid", "Name not in scope: id")
    );
    assert_parity("\tid\n");
}

/// CRLF 源：`\n` 计数行、`\r` 从展示行尾裁掉，列不受影响。
#[test]
fn error_layout_crlf() {
    assert_eq!(ty("let x : U = U;\r\nx\r\n"), "U\n");
    assert_parity("let x : U = U;\r\nx\r\n");
    assert_eq!(
        ty("let x : U = U;\r\nid x\r\n"),
        render_err(2, 1, "id x", "Name not in scope: id")
    );
    assert_parity("let x : U = U;\r\nid x\r\n");
}

// 可复现性
// --------------------------------------------------------------------------------

/// meta 编号按调用重置（Infer 每次新建）、输出确定；跨调用互不串号。
#[test]
fn meta_numbering_is_deterministic() {
    let src = zoo(BODY_INTERSECT_KEEP);
    let first = elab(&src);
    assert_eq!(first, elab(&src));
    assert_eq!(first, elab(&src));
    // 新调用从 ?0 起编号（两次相同输入输出一致）
    assert_eq!(ty("_"), "?0\n");
    assert_eq!(ty("_"), "?0\n");
    // 已定义变量的类型打印的是标注类型（U），不是其洞解 ?0
    assert_eq!(ty("let f : U = _;\nf\n"), "U\n");
    assert_eq!(ty(&src), "U\n");
}

// 负载生成器：小 k 全模式互检 + 大 k 深栈互检
// --------------------------------------------------------------------------------

#[test]
fn workload_parity_small() {
    for k in 1..=4 {
        assert_parity(&fast::church_src(k));
        assert_parity(&fast::implicit_src(k));
        assert_parity(&fast::chain_src(k));
        assert_parity(&fast::conv_src(k));
        assert_parity(&fast::conv_dup_src(k));
        assert_parity(&fast::dup_src(k));
        assert_parity(&fast::dup_deep_src(k));
    }
    for k in 1..=3 {
        assert_parity(&fast::solve_src(k));
        assert_parity(&fast::prune_src(k));
    }
}

/// prune 负载 k=5（每层 2 binder + 非线性求解）：参考版走 512MB 栈线程。
#[test]
fn prune_workload_deep_type_parity_big_stack() {
    let src = fast::prune_src(5);
    let b = {
        let s = src.clone();
        with_big_stack(move || L05_pruning::main_with("type", &s))
    };
    let f = fast::main_with("type", &src);
    assert_eq!(b, f);
}

/// solve/church 深负载：两版**都**放 512MB 栈线程跑 type 模式互检——参考版
/// rename 沿 church 展开链递归（主因）；而 solve k=14 展开 2^15 个节点，
/// 性能版的 quote/求值链在 libtest 默认 2MB 线程栈上也会溢出（实测），故
/// 两者一并挪进大栈线程。
#[test]
fn deep_solve_church_parity_big_stack() {
    for (name, src) in [("solve", fast::solve_src(14)), ("church", fast::church_src(14))] {
        let (b, f) = with_big_stack(move || {
            let b = L05_pruning::main_with("type", &src);
            let f = fast::main_with("type", &src);
            (b, f)
        });
        assert_eq!(b, f, "{name} 深负载双实现不一致");
    }
}

/// 300 层 define 链（每层引用前一定义）+ 末尾洞：define 不进 telescope，
/// 大栈下双实现一致。
#[test]
fn long_define_chain_parity_big_stack() {
    let mut src = String::from("let x0 : U = U;\n");
    for i in 1..300 {
        src.push_str(&format!("let x{i} : U = x{};\n", i - 1));
    }
    src.push_str("let h : U = _;\nh\n");
    let b = {
        let s = src.clone();
        with_big_stack(move || L05_pruning::main_with("type", &s))
    };
    let f = fast::main_with("type", &src);
    assert_eq!(b, f);
    assert_eq!(f, "U\n");
    // elab 里末尾洞的 meta：telescope 只剩自身类型（define 层全部塌缩）
    let e = fast::main_with("elab", &src);
    assert!(e.starts_with("let ?0 : U = ?;\n"), "{e}");
}

/// 多层 λ 下的洞：telescope 逐级命名、双实现互检（覆盖 close_ty 的
/// Bind 链形态与 lams 的匿名命名 `x{l}`）。
#[test]
fn nested_lam_hole_telescope() {
    let src = "let f = \\a b c d e. _;\nf\n";
    assert_parity(src);
    let out = ty(src);
    assert!(out.starts_with("(a : ?"), "{out}");
    // 五层 binder 的名字在类型里逐级出现
    for v in ["a", "b", "c", "d", "e"] {
        let needle = format!("({v} : ");
        assert!(out.contains(&needle), "缺 binder {v}: {out}");
    }
}

