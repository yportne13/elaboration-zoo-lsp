//! L02_tyck 黑盒攻击套件 v2（第二轮系统化攻击）。
//!
//! 风格、helper 与双 oracle（期望输出 + 参考版↔孪生版逐字节 parity）向
//! `tests/l02_blackbox.rs`（v1）看齐；v1 已钉死的「已知怪癖」此处不重复
//! 上报（尾随垃圾 token 静默忽略、`_` 非 hole、错误列号按字节），只在
//! 必要处继续沿这些语义钉住回归。
//!
//! 本轮攻击面：
//!   1. nf/type 正常路径边界——空输入/注释-only、深嵌套 λ/Π、超长 spine、
//!      深 de Bruijn、unicode/超长标识符；
//!   2. 错误路径——类型不匹配（含 Π 期望、binder 下自由变量的打印）、
//!      应用非函数、未绑定变量、解析残缺/括号不平衡——不得 panic、不得
//!      挂死、错误位置按字节列号合理；
//!   3. parity 扫描——同一批用例参考版↔孪生版 nf/type 双模式互检；
//!   4. 语义角落——η 吸收（双向/两层）、闭包捕获与 quote、let 推断与
//!      类型位置的 let。
//!
//! 可能挂死/深递归的用例在带截止时间的大栈子线程里跑
//! （`with_big_stack_deadline`），保证套件本身不会卡死。

#[path = "../src/list.rs"]
mod list;

#[path = "../src/parser_lib.rs"]
mod parser_lib;
#[path = "../src/parser_lib_resilient.rs"]
mod parser_lib_resilient;

#[path = "../src/L02_tyck/mod.rs"]
mod L02_tyck;

#[path = "../src/L03_holes/mod.rs"]
mod L03_holes;

use L02_tyck::bump_spine_iter as fast;

// helpers（与 v1 同款）
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

/// 报错输出：以 `(stdin):{line}:{col}:` 开头且包含消息片段（col 按字节）。
fn assert_error_at(src: &str, line: usize, col: usize, needle: &str) {
    let out = nf(src);
    assert!(
        out.starts_with(&format!("(stdin):{line}:{col}:\n")),
        "错误位置不符：期望 ({line}:{col})，实际：\n{out}"
    );
    assert!(out.contains(needle), "错误消息缺 {needle:?}：\n{out}");
    assert_parity(src);
}

/// 按字节偏移算 (line, col)：测试里用源码定位 token，避免手数列号
/// （列号语义 = `offset - line_start + 1`，按字节，与被测实现一致）。
fn line_col_of(src: &str, byte_offset: usize) -> (usize, usize) {
    let mut line = 1;
    let mut line_start = 0;
    for (i, b) in src.bytes().enumerate() {
        if i >= byte_offset {
            break;
        }
        if b == b'\n' {
            line += 1;
            line_start = i + 1;
        }
    }
    (line, byte_offset - line_start + 1)
}

/// 报错位置由源码里 needle 首次出现处推出（等价于手写行列，但可读）。
fn assert_error_at_needle(src: &str, needle: &str, msg_needle: &str) {
    let off = src.find(needle).expect("src 里找不到定位 needle");
    let (line, col) = line_col_of(src, off);
    assert_error_at(src, line, col, msg_needle);
}

// helpers v2：带截止时间的大栈线程（挂死表征用，不让套件卡死）
// --------------------------------------------------------------------------------

/// 512MB 栈 + 截止时间。超时或子线程 panic 都以可读消息失败（超时线程
/// 泄漏由进程退出兜底——join 无法带超时，只能轮询完成标志）。
fn with_big_stack_deadline(secs: u64, name: &str, f: impl FnOnce() + Send + 'static) {
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::{Arc, Mutex};
    let done = Arc::new(AtomicBool::new(false));
    let payload: Arc<Mutex<Option<Box<dyn std::any::Any + Send>>>> = Arc::new(Mutex::new(None));
    let (d2, p2) = (done.clone(), payload.clone());
    std::thread::Builder::new()
        .stack_size(512 * 1024 * 1024)
        .spawn(move || {
            let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
            if let Err(e) = r {
                *p2.lock().unwrap() = Some(e);
            }
            d2.store(true, Ordering::SeqCst);
        })
        .unwrap();
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(secs);
    while !done.load(Ordering::SeqCst) {
        if std::time::Instant::now() >= deadline {
            panic!("用例 {name} 超过 {secs}s 未完成：疑似挂死（或栈深超限）");
        }
        std::thread::sleep(std::time::Duration::from_millis(25));
    }
    if let Some(e) = payload.lock().unwrap().take() {
        std::panic::resume_unwind(e);
    }
}

/// EX2 式 church 编码 numeral 的源码（n 个 s 的字面右嵌套链）。
fn numeral_src(n: usize) -> String {
    let mut s = String::from("let Nat : U = (N : U) -> (N -> N) -> N -> N;\n");
    s.push_str("let n : Nat = \\N s z. ");
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
fn numeral_nf(n: usize) -> String {
    fn f(k: usize) -> String {
        match k {
            0 => "z".to_string(),
            1 => "s z".to_string(),
            k => format!("s ({})", f(k - 1)),
        }
    }
    format!("λ N s z. {}\n", f(n))
}

/// `\x1 x2 … xn. body` 多 binder λ（1 起始编号，打印同名）。
fn multi_lam(n: usize, body: &str) -> String {
    let binders: Vec<String> = (1..=n).map(|i| format!("x{i}")).collect();
    format!("\\{}. {}", binders.join(" "), body)
}

/// `U -> U -> … -> U`：n 个箭头、n+1 个 U（源码形态）。
fn arrow_chain_src(n: usize) -> String {
    vec!["U"; n + 1].join(" -> ")
}

/// 同上的 pretty 形态。
fn arrow_chain_pretty(n: usize) -> String {
    vec!["U"; n + 1].join(" → ")
}

/// `(a1 : U) -> … -> (an : U) -> U` 命名 Π 链（源码形态）。
fn named_pi_chain_src(n: usize) -> String {
    let doms: Vec<String> = (1..=n).map(|i| format!("(a{i} : U)")).collect();
    format!("{} -> U", doms.join(" -> "))
}

/// 命名 Π 链的 pretty 期望：`(a1 : U)(a2 : U)…(an : U) → U`。
fn named_pi_chain_pretty(n: usize) -> String {
    let binds: Vec<String> = (1..=n).map(|i| format!("(a{i} : U)")).collect();
    format!("{} → U", binds.join(""))
}

/// n 层 `let x_i : U = x_{i-1};` 链（x0 = U），返回完整源码。
fn let_chain_src(n: usize, body: &str) -> String {
    let mut s = String::from("let x0 : U = U;\n");
    for i in 1..=n {
        s.push_str(&format!("let x{i} : U = x{};\n", i - 1));
    }
    s.push_str(body);
    s
}

// 输入与词法边界
// --------------------------------------------------------------------------------

#[test]
fn v2_comment_only_and_whitespace_inputs() {
    for src in [
        "-- 只有一行注释\n",
        "{- 只有一段注释 -}",
        "{-a-} {-b-} {-c-}",
        "\n\n\n",
        "  \t  \n  ",
        "-- a\n-- b\n-- c\n",
    ] {
        assert_eq!(nf(src), "parse error\n", "src: {src:?}");
        assert_eq!(ty(src), "parse error\n", "src: {src:?}");
        assert_parity(src);
    }
}

#[test]
fn v2_single_junk_char_inputs() {
    // 无任何完整项 → parse error（垃圾 token 语义见 v1：只取第一个完整项）。
    for src in ["}", "$", ".", ",", "\"", "'", "|", "~", "^", "!", "*/", "@", "#"] {
        assert_eq!(nf(src), "parse error\n", "src: {src:?}");
        assert_parity(src);
    }
    // 完整项后跟垃圾 → 项照常输出（v1 已钉的尾随垃圾语义，这里补字符面）。
    for junk in ["U }", "U $ . ,", "U \"str\"", "U | ~ ^"] {
        assert_eq!(nf(junk), "U\n  :\nU\n", "junk: {junk:?}");
        assert_parity(junk);
    }
}

#[test]
fn v2_unicode_whitespace_is_trivia() {
    // 全角空格 U+3000 走 char::is_whitespace 的 trivia 通道（不是
    // ErrToken），词法上与 ASCII 空白等价。
    let src = "\u{3000}U\u{3000}";
    assert_eq!(nf(src), "U\n  :\nU\n");
    let src2 = "let x\u{3000}: U = U; x";
    assert_eq!(nf(src2), "U\n  :\nU\n");
    assert_parity(src);
    assert_parity(src2);
}

#[test]
fn v2_nul_is_inert_junk() {
    // NUL 不是空白也不是任何 token 字符 → ErrToken 垃圾：
    // 项前有垃圾 → 无法解析；项后 → 静默忽略（怪癖家族，钉住防回归）。
    assert_eq!(nf("\0"), "parse error\n");
    assert_eq!(nf("U \0"), "U\n  :\nU\n");
    assert_parity("\0");
    assert_parity("U \0");
}

#[test]
fn v2_unicode_identifiers_end_to_end() {
    // 中文/希腊/全角标识符走 is_alphabetic 路径，nf/type 全程可用。
    assert_eq!(nf("let 类型 : U = U; 类型"), "U\n  :\nU\n");
    // αβγ 的值是函数 U → U，但它的类型是 U（值与类型两个平面）。
    assert_eq!(ty("let αβγ : U = U -> U; αβγ"), "U\n");
    assert_eq!(nf("let αβγ : U = U -> U; αβγ"), "U → U\n  :\nU\n");
    assert_eq!(nf("let Ｕｎｉ : U = U; Ｕｎｉ"), "U\n  :\nU\n");
    assert_parity("let 类型 : U = U; 类型");
    assert_parity("let αβγ : U = U -> U; αβγ");
    assert_parity("let id : (A : U) -> A -> A = λA ξ. ξ;\nid");
}

#[test]
fn v2_unicode_ident_out_of_scope_message_and_byte_col() {
    // 未绑定 unicode 名：消息带原名；列号按字节（中在 UTF-8 占 3 字节，
    // caret 列 = 字节偏移 + 1——文档化怪癖，用字节偏移自算列号钉住）。
    let src = "let x : U = U;\nlet y : U = 中; y";
    let off = src.find("中").unwrap();
    let (line, col) = line_col_of(src, off);
    let out = nf(src);
    assert!(
        out.starts_with(&format!("(stdin):{line}:{col}:\n")),
        "错误位置不符：期望 ({line}:{col})，实际：\n{out}"
    );
    assert!(out.contains("variable out of scope: 中"), "{out}");
    assert_parity(src);
}

#[test]
fn v2_unicode_lambda_binder_scopes_correctly() {
    // `λ甲. 甲`：λ 后无空格拆 token，unicode binder 名全程一致。
    let src = "let 类型 : U -> U = λ甲. 甲; 类型 U";
    assert_eq!(nf(src), "U\n  :\nU\n");
    assert_parity(src);
}

#[test]
fn v2_long_identifier_500_chars() {
    // 超过 SmolStr 23 字节内联阈值的超长名字：解析、查找、pretty 全程一致。
    let long = format!("v{}", "0123456789".repeat(49)); // 491 字符
    let src = format!("let {long} : U = U; {long}");
    assert_eq!(nf(&src), "U\n  :\nU\n");
    let src2 = format!("let {long} : U -> U = \\x. x; {long}");
    assert_eq!(nf(&src2), "λ x. x\n  :\nU → U\n");
    // 未绑定的超长名：错误消息原样带回。
    let src3 = format!("let f : U = U; {long}");
    let out = nf(&src3);
    assert!(out.contains(&format!("variable out of scope: {long}")), "{out}");
    assert_parity(&src);
    assert_parity(&src2);
    assert_parity(&src3);
}

#[test]
fn v2_crlf_line_endings_display_and_positions() {
    // CRLF：\r 是空白；报错行内容去掉行尾 \r（display_error 的 trim），
    // 列号不受影响（按字节、\r 不入列）。
    let src = "let x : U = U;\r\nlet y : U = zz;\r\ny";
    let off = src.find("zz").unwrap();
    let (line, col) = line_col_of(src, off);
    assert_eq!((line, col), (2, 13));
    let out = nf(src);
    assert!(out.starts_with("(stdin):2:13:\n"), "{out}");
    assert!(out.contains("2 | let y : U = zz"), "{out}");
    assert!(!out.contains('\r'), "输出里不应残留 \\r：\n{out:?}");
    assert_parity(src);
}

#[test]
fn v2_error_on_last_line_without_trailing_newline() {
    // 文件不以换行结尾：报错行的源码摘录仍完整显示（无尾随换行）。
    let src = "let x : U = U;\nlet y : U = zz; y";
    let out = nf(src);
    assert!(out.starts_with("(stdin):2:13:\n"), "{out}");
    assert!(out.contains("2 | let y : U = zz; y"), "{out}");
    assert!(out.contains("variable out of scope: zz"), "{out}");
    assert_parity(src);
}

#[test]
fn v2_error_on_third_line_multiline_program() {
    let src = "let id : (A : U) -> A -> A = \\A x. x;\nlet c : U = U;\nlet bad : U = id c;\nbad";
    let off = src.find("id c").unwrap();
    let (line, col) = line_col_of(src, off);
    assert_eq!(line, 3);
    let out = nf(src);
    assert!(
        out.starts_with(&format!("(stdin):3:{col}:\n")),
        "错误位置不符：期望 (3:{col})，实际：\n{out}"
    );
    // id c : U → U（A := U 的实例化 Π 值）对 U 期望 → mismatch（在 id c 处）。
    assert!(
        out.contains("type mismatch") && out.contains("inferred type:\n\n  U → U"),
        "{out}"
    );
    assert_parity(src);
}

#[test]
fn v2_underscore_prefixed_name_lexes_as_two_binders() {
    // 怪癖家族（与 v1 `_` 系列同源）：lexer 把 `_` 切成独立 Underscore
    // token，`_ab` = `_` + `ab` 两个 binder——不是名为 "_ab" 的一个名字。
    // 钉住该行为防回归（与 v1 已钉的 `_` binder 语义自洽，不按 bug 改）。
    let src = "let f : U -> U -> U = \\_ab. ab; f";
    assert_eq!(nf(src), "λ _ ab. ab\n  :\nU → U → U\n");
    assert_parity(src);
}

// nf/type 正常路径边界
// --------------------------------------------------------------------------------

#[test]
fn v2_deep_lambda_100_binders_outermost_body() {
    // 100 个 binder、body 取最外层（de Bruijn Ix = 99）：任何环境/索引
    // 错位都会打错名字。中深度，默认测试线程栈即可。
    let src = format!(
        "let f : {} = {}; f",
        arrow_chain_src(100),
        multi_lam(100, "x1")
    );
    let binders: Vec<String> = (1..=100).map(|i| format!("x{i}")).collect();
    let expected = format!("λ {}. x1\n  :\n{}\n", binders.join(" "), arrow_chain_pretty(100));
    assert_eq!(nf(&src), expected);
    assert_nf_embeds_type(&src);
    assert_parity(&src);
}

#[test]
fn v2_deep_lambda_100_binders_innermost_body() {
    let src = format!(
        "let f : {} = {}; f",
        arrow_chain_src(100),
        multi_lam(100, "x100")
    );
    let binders: Vec<String> = (1..=100).map(|i| format!("x{i}")).collect();
    let expected = format!("λ {}. x100\n  :\n{}\n", binders.join(" "), arrow_chain_pretty(100));
    assert_eq!(nf(&src), expected);
    assert_parity(&src);
}

#[test]
fn v2_deep_pi_chain_300_named_binders() {
    // 300 层命名 Π + body 指向第 150 个 binder：深 de Bruijn 双向
    // （infer 递归 300 层、env nth 150 步、pretty 连链 300 段）。
    let src = format!(
        "let f : {} = {}; f",
        named_pi_chain_src(300),
        multi_lam(300, "x150")
    );
    let binders: Vec<String> = (1..=300).map(|i| format!("x{i}")).collect();
    with_big_stack_deadline(120, "deep_pi_300", move || {
        assert_eq!(ty(&src), format!("{}\n", named_pi_chain_pretty(300)));
        // nf：λ x1 … x300. x150 —— body 打印走 λ 自带的 binder 名表
        // （第 150 个 binder 的名字是 x150，不是类型侧的 a150）。
        let out = nf(&src);
        assert_eq!(
            out,
            format!("λ {}. x150\n  :\n{}\n", binders.join(" "), named_pi_chain_pretty(300))
        );
        assert_parity(&src);
    });
}

#[test]
fn v2_long_spine_300_args_partial_application() {
    // 301 元函数吃 300 个实参：超长 spine + 依赖替换，剩 `λ x301. U`。
    let src = format!(
        "let f : {} = {}; f {}",
        arrow_chain_src(301),
        multi_lam(301, "x1"),
        vec!["U"; 300].join(" ")
    );
    assert_eq!(nf(&src), "λ x301. U\n  :\nU → U\n");
    assert_parity(&src);
}

#[test]
fn v2_let_chain_300_deep_name_lookup_hits_outermost() {
    // 300 层 let，body 引最外层名字：名字查找走满链、env nth 走满深。
    let s = let_chain_src(300, "x0");
    assert_eq!(nf(&s), "U\n  :\nU\n");
    assert_parity(&s);
}

#[test]
fn v2_moderate_parens_300_no_big_stack() {
    let deep = format!("{}U{}", "(".repeat(300), ")".repeat(300));
    assert_eq!(nf(&deep), "U\n  :\nU\n");
    assert_parity(&deep);
}

#[test]
fn v2_numeral_600_via_doubling() {
    // 自倍增：n=300 字面量经 d 翻倍成 600——闭包共享环境下的 quote。
    let src = format!(
        "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
         let n : Nat = \\N s z. {};\n\
         let d : Nat -> Nat = \\m N s z. m N s (m N s z);\n\
         d n",
        format!("{}z{}", "s (".repeat(300), ")".repeat(300))
    );
    with_big_stack_deadline(240, "numeral_600", move || {
        let out = nf(&src);
        assert_eq!(out, format!("{}  :\n(N : U) → (N → N) → N → N\n", numeral_nf(600)));
        assert_eq!(out, fast_nf(&src));
    });
}

#[test]
fn v2_numeral_1024_literal_chain_parity() {
    // 字面 1024 深右嵌套链：参考版 infer 对该形态 O(n²)（readme 已知限制），
    // 大栈 + 截止时间跑通即可，形状断言不整串（v1 已有整串 1024/4096）。
    let src = numeral_src(1024);
    with_big_stack_deadline(240, "numeral_1024", move || {
        let out = nf(&src);
        assert!(out.starts_with("λ N s z. s (s (s ("), "out prefix: {out}");
        assert!(
            out.ends_with("  :\n(N : U) → (N → N) → N → N\n"),
            "out suffix: {out}"
        );
        assert_eq!(out, fast_nf(&src));
    });
}

// 错误路径（位置/消息/不 panic）
// --------------------------------------------------------------------------------

#[test]
fn v2_mismatch_lambda_against_U() {
    // λ 对 U 期望：走 infer 走廊报 Can't infer，位置在 λ 的反斜杠。
    assert_error_at_needle("let f : U = \\x. x; f", "\\", "Can't infer type for lambda expression");
}

#[test]
fn v2_app_non_function_after_let() {
    assert_error_at_needle(
        "let x : U = U; x x",
        "x x",
        "Expected a function type, instead inferred:\n\n  U\n",
    );
}

#[test]
fn v2_out_of_scope_in_lam_body() {
    assert_error_at_needle("let f : U -> U = \\x. zz; f", "zz", "variable out of scope: zz");
}

#[test]
fn v2_out_of_scope_in_let_type() {
    assert_error_at_needle("let x : zz = U; x", "zz", "variable out of scope: zz");
}

#[test]
fn v2_out_of_scope_deep_in_pi_cod() {
    assert_error_at_needle("(A : U) -> (B : U) -> qq", "qq", "variable out of scope: qq");
}

#[test]
fn v2_expected_function_in_long_spine_arg() {
    // `g x U`：内层 g x : U，再吃 U → Expected a function type，
    // caret 在整个 App 产生式的首 token（g）。
    assert_error_at_needle(
        "let f : (U -> U) -> U -> U = \\g x. g x U; f",
        "g x U",
        "Expected a function type",
    );
}

#[test]
fn v2_mismatch_expected_pi_inferred_U() {
    // λ body 的 x : U 对期望 U → U：mismatch（非 Can't infer），
    // 位置在 body 的 x（带自己的 SrcPos）。期望类型的 Π binder 名与
    // λ binder 名撞车 → pretty fresh 出 `x'`（报错打印路径的改名行为）。
    let src = "let f : U -> (x : U) -> U = \\x. x; f";
    let off = src.find("\\x. x").unwrap() + 4; // body x 的字节位置
    let (line, col) = line_col_of(src, off);
    let out = nf(src);
    assert!(
        out.starts_with(&format!("(stdin):{line}:{col}:\n")),
        "错误位置不符：期望 ({line}:{col})，实际：\n{out}"
    );
    assert!(
        out.contains("type mismatch")
            && out.contains("expected type:\n\n  (x' : U) → U")
            && out.contains("inferred type:\n\n  U\n"),
        "{out}"
    );
    assert_parity(src);
}

#[test]
fn v2_mismatch_under_binders_prints_free_var_name() {
    // binder 下自由变量的期望类型打印：A 是外层 binder（VVar(0)），
    // quote(2) 后落在 ns[1] = "A"——报错路径 quote 的 level/名字表必须一致。
    let src = "let f : (A : U) -> (x : A) -> A = \\A x. U; f";
    let off = src.find("U; f").unwrap();
    let (line, col) = line_col_of(src, off);
    let out = nf(src);
    assert!(
        out.starts_with(&format!("(stdin):1:{col}:\n")),
        "错误位置不符：期望 (1:{col})，实际：\n{out}"
    );
    assert!(
        out.contains("expected type:\n\n  A\n") && out.contains("inferred type:\n\n  U\n"),
        "{out}"
    );
    assert_parity(src);
}

#[test]
fn v2_mismatch_expected_var_prints_raw_indexed_name() {
    // 期望类型是 binder 变量本身时：Var 打印直接按下标取名字表
    // （Main.hs 同款：Var 臂不走 fresh——与 Π binder 名打印的 fresh 是
    // 两条路径）。cod `x` 指外层 binder → quote(2) → Ix(1) → ns[1] = "x"。
    let src = "let f : (x : U) -> (y : U) -> x = \\x x. U; f";
    let out = nf(src);
    assert!(
        out.contains("expected type:\n\n  x\n") && out.contains("inferred type:\n\n  U\n"),
        "{out}"
    );
    assert_parity(src);
}

#[test]
fn v2_truncated_inputs_parse_error_battery() {
    for src in [
        "let x : U", "let x : U =", "let x : U = U", "let x", "\\", "\\x", "\\x .", "(U",
        "let x : U = U;", "let x : U = U; ", "λ", "λx", "λx.", "let", ";", "=", "->", ":",
        "(let x : U = U;", "let f : U -> = \\x. x; f",
    ] {
        assert_eq!(nf(src), "parse error\n", "src: {src:?}");
        assert_eq!(ty(src), "parse error\n", "src: {src:?}");
        assert_parity(src);
    }
    // 「截断在悬垂箭头/垃圾处」不是截断：箭头解析整体回溯，U 已是完整项，
    // 余下 token 全是尾随垃圾（v1 已钉的静默忽略语义）。
    for src in ["U (", "U ->", "U -> -> U"] {
        assert_eq!(nf(src), "U\n  :\nU\n", "src: {src:?}");
        assert_parity(src);
    }
    // `\x. U ->`：λ 语法完整（body U，箭头回溯成垃圾）→ 顶层 λ 走 infer
    // 走廊报 Can't infer，而非 parse error。
    assert_error_at("\\x. U ->", 1, 1, "Can't infer type for lambda expression");
}

#[test]
fn v2_unbalanced_parens_battery() {
    for (src, expect) in [
        ("((U)", "parse error\n"), // 外层 `(` 到 EOF 处缺 `)`
        ("(U))", "U\n  :\nU\n"),   // 多余 `)` 是尾随垃圾（v1 怪癖）
        ("()", "parse error\n"),
        ("())", "parse error\n"),
        ("(", "parse error\n"),
        (")", "parse error\n"),
        ("((((( U )))))", "U\n  :\nU\n"),
        (
            "(U)(U)",
            "(stdin):1:1:\n  |\n1 | (U)(U)\n  | ^\nExpected a function type, instead inferred:\n\n  U\n\n",
        ),
    ] {
        assert_eq!(nf(src), expect, "src: {src:?}");
        assert_parity(src);
    }
}

#[test]
fn v2_empty_lambda_body_and_missing_dot() {
    for src in ["\\x.", "\\x x", ". x", "\\ . x", "\\1. x", "λ.", "λ x x"] {
        assert_eq!(nf(src), "parse error\n", "src: {src:?}");
        assert_parity(src);
    }
}

#[test]
fn v2_lambda_arg_check_error_position() {
    // 实参位置放 λ：check 退 infer 报 Can't infer，位置在 λ 起（括号不算）。
    assert_error_at_needle(
        "let f : U -> U = \\x. x; f (\\y. y)",
        "\\y. y",
        "Can't infer type for lambda expression",
    );
}

#[test]
fn v2_error_path_with_wide_chars_does_not_panic() {
    // caret 前有多个多字节字符：输出仍良构（位置按字节——文档化怪癖），
    // 且实现不 panic。
    let src = "let 类型 : U -> U = λ甲. 甲; let g : U = 类型 类型; g";
    let out = nf(src);
    assert!(out.contains("type mismatch"), "{out}");
    assert_parity(src);
}

// parity 扫描（nf/type 双模式互检）
// --------------------------------------------------------------------------------

#[test]
fn v2_parity_scan_battery() {
    let mut cases: Vec<String> = vec![
        "U".into(),
        "(A : U) -> A -> A".into(),
        "(A B C : U) -> C -> B -> A".into(),
        "(_ : U) -> (x : U) -> (_ : U) -> x".into(),
        "let f : U -> U -> U -> U = \\a b c. a; f".into(),
        "let k : U -> U -> U = \\a b. a; let s : U -> U -> U = \\b c. k c b; s".into(),
        "let f : U -> U = \\x. x; let g : U -> U -> U = f; g".into(),
        "let T : U = U -> U; let f : T = \\x. x; f".into(),
        "let f : let T : U = U; T = \\x. x; f".into(), // T 的值是 U → f : U → λ 报 Can't infer
        "let f : (let T : U = U; T) -> U -> U = \\x y. x; f".into(),
        "let f : (U -> U) -> U = \\g. g U; f (\\x. x)".into(),
        "let x : U = U; let f : U -> U = \\x. x; f x".into(),
        "let a : U = U; let b : U = a; let c : U = b; c".into(),
        "let f : (A : U) -> (x : A) -> A = \\A x. x; let g : (A : U) -> (y : A) -> A = f; g".into(),
        "let Nat : U = (N : U) -> (N -> N) -> N -> N; let z0 : Nat = \\N s z. z; let z1 : Nat = \\N. z0 N; z1".into(),
        "let id : (A : U) -> A -> A = \\A x. x; id ((A : U) -> A -> A) id".into(),
        "let f : U -> U = \\x. x; f (let y : U = U; y)".into(),
        "let 类型 : U = U -> U; let f : 类型 = \\x. x; f U".into(),
        "let 类型 : U -> U = λ甲. 甲; let g : U -> U = 类型 类型; g".into(),
        "let f : ((U -> U) -> U) -> (U -> U) -> U = \\g x. g (g x); f".into(),
        "λ 甲乙. 甲".into(), // 顶层 λ：Can't infer 报错路径
        "let f : U = \\x. x; f".into(),
        "let x : U = U; x x".into(),
        "U U U".into(),
        "let f : U -> U = U; f".into(),
        "(x : U) -> qq".into(),
        "let f : U -> (x : U) -> U = \\x. x; f".into(),
        "let f : (A : U) -> (x : A) -> A = \\A x. U; f".into(),
        "let f : (x : U) -> (x : U) -> x = \\x y. U; f".into(),
        "let x : U = U;\r\nlet y : U = zz;\r\ny".into(),
        "let x : U = U;\nlet y : U = qq".into(),
        "let 类型 : U -> U = λ甲. 甲; let g : U = 类型 类型; g".into(),
        "(U)(U)".into(),
        "U ))".into(),
        "U {- c -} U U".into(),
        "let f : U -> U -> U = \\_ab. ab; f".into(),
        // let 在各语法槽位
        "let f : (let T : U = U; T) -> U = \\x. x; f U".into(),
        "let g : U -> U = let h : U -> U = \\z. z; h; g".into(),
        "(let x : U = U; x)".into(),
        // 混合注释/unicode/未闭合块注释
        "{- 中文 -} let x : U = U; -- 行注释\nx {- 尾注释".into(),
        "let λ λ : U = U; λ".into(), // λ 开头 binder → Lambda token → parse error
        "\\λ. x".into(),              // binder 位是 Lambda token → parse error
    ];
    // 数值族：i 与 40-i 的 church numeral 相加（eval/quote/conv 的扫描面）
    for i in 0..40usize {
        let mut s = String::from("let Nat : U = (N : U) -> (N -> N) -> N -> N;\n");
        s.push_str(&format!(
            "let a : Nat = \\N s z. {};\n",
            format!("{}z{}", "s (".repeat(i), ")".repeat(i))
        ));
        s.push_str(&format!(
            "let b : Nat = \\N s z. {};\n",
            format!("{}z{}", "s (".repeat(40 - i), ")".repeat(40 - i))
        ));
        s.push_str("let add : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z);\nadd a b");
        cases.push(s);
    }
    for src in &cases {
        assert_parity(src);
    }
}

#[test]
fn v2_parity_nf_embeds_type_battery() {
    for src in [
        "let f : U -> U -> U -> U = \\a b c. b; f U",
        "let f : (A : U) -> (x : A) -> A = \\A x. x; f (U -> U) (\\A. A)",
        "let Nat : U = (N : U) -> (N -> N) -> N -> N; let two : Nat = \\N s z. s (s z); let add : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z); add two two",
        "let f : let T : U = U -> U; T = \\x. x; f U",
        "let T : U = U -> U; let f : T = \\x. x; f",
    ] {
        assert_nf_embeds_type(src);
    }
}

// 语义角落：η、闭包捕获与 quote、let 推断
// --------------------------------------------------------------------------------

/// η 吸收·闭包在左：`P (\x. h y x)`（len 1 链，base 是闭包）与 `P (h y)`
/// （len 2 链）βη 等价。v1 的 `conv_eta_absorption_accepted_by_both` 只钉了
/// 闭包在右侧的方向，这里补对侧。
const ETA_ABSORB_CLOSURE_LEFT: &str = "\
let big : (P : (U -> U) -> U) -> (h : U -> U -> U) -> (y : U)
       -> (v : P (\\x. h y x)) -> (f : P (h y) -> U) -> U
      = \\P h y v f. f v;
big
";

#[test]
fn v2_conv_eta_absorption_closure_on_left() {
    let b = ty(ETA_ABSORB_CLOSURE_LEFT);
    assert!(
        b.starts_with("(P : (U → U) → U)(h : U → U → U)(y : U)(v : P (λ x. h y x))(f : P (h y) → U)"),
        "良型 η 等价程序不应被拒：\n{b}"
    );
    assert_parity(ETA_ABSORB_CLOSURE_LEFT);
}

/// η 吸收·两层：`P (h a b)`（len 2、cod 还有两个箭头）与
/// `P (\x1 x2. h a b x1 x2)`——η 对多参 λ 逐层应用，两次吸收后链同形。
const ETA_ABSORB_TWO_LEVEL: &str = "\
let big : (h : U -> U -> U -> U -> U) -> (a : U) -> (b : U) -> (P : (U -> U -> U) -> U)
       -> (v : P (h a b)) -> (f : P (\\x1 x2. h a b x1 x2) -> U) -> U
      = \\h a b P v f. f v;
big
";

#[test]
fn v2_conv_eta_absorption_two_levels() {
    let out = ty(ETA_ABSORB_TWO_LEVEL);
    assert!(!out.contains("mismatch") && !out.contains("Can't infer"), "{out}");
    assert_parity(ETA_ABSORB_TWO_LEVEL);
}

#[test]
fn v2_nf_does_not_eta_collapse_partially_applied() {
    // nf 不做 η 收缩：`\g. \x. g x` 保持展开形态（v1 钉过两参形态，
    // 这里钉嵌套书写形态）。
    let src = "let f : (U -> U) -> U -> U = \\g. \\x. g x; f";
    assert_eq!(nf(src), "λ g x. g x\n  :\n(U → U) → U → U\n");
    assert_parity(src);
}

#[test]
fn v2_closure_capture_and_quote_battery() {
    // 捕获 let 值（quote 时值已代入）：
    assert_eq!(
        nf("let c : U = U; let f : U -> U -> U = \\x y. c; f U U"),
        "U\n  :\nU\n"
    );
    // 部分应用：闭包捕获第一实参，quote 出 `λ y. U`。
    assert_eq!(nf("let f : U -> U -> U = \\x y. x; f U"), "λ y. U\n  :\nU → U\n");
    // 交错捕获多个 let：f 返回捕获的 y（不施加）→ `λ z. b`，quote 强制
    // 捕获的 b → `λ z t. U`（闭包捕获 + 多层 quote 的正确性）。
    let src = "let a : U = U; let b : U -> U = \\t. a; let f : U -> (U -> U) -> U -> U -> U = \\x y z. y; f a b";
    assert_eq!(nf(src), "λ z t. U\n  :\nU → U → U\n");
    assert_parity("let f : U -> U -> U = \\x y. x; f U");
    assert_parity(src);
}

#[test]
fn v2_let_in_type_position_elaborates_away() {
    // 类型位置的 let：annotation `let T : U = U -> U; T` check against U
    // 通过，eval 消费 let 后 f : U -> U；打印里没有 let 痕迹。
    let src = "let f : let T : U = U -> U; T = \\x. x; f";
    assert_eq!(nf(src), "λ x. x\n  :\nU → U\n");
    assert_eq!(ty(src), "U → U\n");
    assert_parity(src);
}

#[test]
fn v2_let_value_as_function_in_arg_position() {
    let src = "let g : U -> U = let h : U -> U = \\z. z; h; g";
    assert_eq!(nf(src), "λ z. z\n  :\nU → U\n");
    let src2 = "(let x : U = U; x)";
    assert_eq!(nf(src2), "U\n  :\nU\n");
    assert_parity(src);
    assert_parity(src2);
}

#[test]
fn v2_pi_binder_names_ignored_in_conv() {
    // conv 忽略 Π binder 名：f 的类型换名后 g 的注解仍通过；
    // nf 保留值侧（f 的 λ）名字，类型打印用注解侧名字。
    let src = "let f : (A : U) -> (x : A) -> A = \\A x. x; let g : (B : U) -> (y : B) -> B = f; g";
    assert_eq!(nf(src), "λ A x. x\n  :\n(B : U)(y : B) → B\n");
    assert_parity(src);
}

#[test]
fn v2_church_zero_eta_form_passes_conv() {
    let src = "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
               let z0 : Nat = \\N s z. z;\n\
               let z1 : Nat = \\N. z0 N;\nz1";
    assert_eq!(nf(src), "λ N s z. z\n  :\n(N : U) → (N → N) → N → N\n");
    assert_parity(src);
}

#[test]
fn v2_deep_mixed_nesting_battery() {
    // λ 里套 let 套应用（中深度，默认测试线程栈即可）：
    let mut s = String::from("let f : U -> U -> U = \\a b. a;\n");
    for i in 0..60 {
        s.push_str(&format!("let g{i} : U -> U = \\x. f x x;\n"));
    }
    s.push_str("g59 U");
    assert_eq!(nf(&s), "U\n  :\nU\n");
    assert_parity(&s);
}

// 压力与挂死表征（大栈 + 截止时间）
// --------------------------------------------------------------------------------

#[test]
fn v2_deep_parens_2000_big_stack() {
    let deep = format!("{}U{}", "(".repeat(2000), ")".repeat(2000));
    with_big_stack_deadline(120, "deep_parens_2000", move || {
        assert_eq!(nf(&deep), "U\n  :\nU\n");
        assert_parity(&deep);
    });
}

#[test]
fn v2_spine_1000_args_big_stack() {
    // 1001 元函数吃 1000 个实参：超长 spine + 逐实参 conv + 深替换。
    let src = format!(
        "let f : {} = {}; f {}",
        arrow_chain_src(1001),
        multi_lam(1001, "x1"),
        vec!["U"; 1000].join(" ")
    );
    with_big_stack_deadline(240, "spine_1000", move || {
        let out = nf(&src);
        assert_eq!(out, "λ x1001. U\n  :\nU → U\n");
        assert_eq!(out, fast_nf(&src));
    });
}

#[test]
fn v2_neutral_error_chain_400_args_no_hang() {
    // 400 个 U 连吃：第一个 U U 就报错，不因链长挂死/炸栈。
    let deep = format!("{} U", "U ".repeat(400));
    with_big_stack_deadline(60, "neutral_error_400", move || {
        let out = nf(&deep);
        assert!(out.starts_with("(stdin):1:1:\n"), "out: {out}");
        assert!(out.contains("Expected a function type"), "out: {out}");
        assert_eq!(out, fast_nf(&deep));
    });
}

#[test]
fn v2_let_chain_1500_big_stack() {
    // 1500 层 let：infer/eval/env 全链，名字查找命中最内层。
    let s = let_chain_src(1500, "x1500");
    with_big_stack_deadline(120, "let_chain_1500", move || {
        assert_eq!(nf(&s), "U\n  :\nU\n");
        assert_parity(&s);
    });
}

#[test]
fn v2_help_and_mode_edge_strings() {
    // 模式串精确匹配：大小写/尾随空白都不是 nf/type → HELP。
    for mode in ["nf ", " nf", "NF", "Type", "type\n", "--help "] {
        assert_eq!(L02_tyck::main_with(mode, "U"), L02_tyck::main_with("--help", ""));
        assert_eq!(fast::main_with(mode, "U"), L02_tyck::main_with("--help", ""));
    }
}

// 差分模糊：参考版↔孪生版逐字节 parity 的系统化扫描
// --------------------------------------------------------------------------------

/// splitmix64：固定种子的确定性伪随机（不引外部依赖，跑量可复现）。
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// 生成一个表面语法项。names 是当前作用域的名字栈（生成 λ/let/Pi 时
/// 压栈、离开作用域时弹栈，保证 Var 引用词法上在作用域内——类型上则
/// 有意不作保证，让错误路径一起进 parity 扫描）。
fn fuzz_term(rng: &mut Rng, depth: u32, names: &mut Vec<String>) -> String {
    let choice = if depth == 0 { rng.below(2) } else { rng.below(9) };
    match choice {
        0 => "U".to_string(),
        // Var：从作用域池取（池含 unicode 名；空作用域退化为 U）
        1 => {
            if names.is_empty() {
                "U".to_string()
            } else {
                let i = rng.below(names.len() as u64) as usize;
                names[i].clone()
            }
        }
        // 多 binder λ（1..3 个，名字可能重名/与外层重名——打印 fresh 路径）
        2 => {
            let n = 1 + rng.below(3) as usize;
            let mut binders = Vec::new();
            for _ in 0..n {
                let nm = ["v", "类型", "αx", "_x"][rng.below(4) as usize].to_string()
                    + &rng.below(3).to_string();
                binders.push(nm.clone());
                names.push(nm);
            }
            let body = fuzz_term(rng, depth - 1, names);
            for _ in 0..n {
                names.pop();
            }
            format!("\\{}. {}", binders.join(" "), body)
        }
        // 应用（括号包死，避免与 λ/let 的黏连歧义）
        3 => {
            let f = fuzz_term(rng, depth - 1, names);
            let a = fuzz_term(rng, depth - 1, names);
            format!("({}) ({})", f, a)
        }
        // 命名 Pi（binder 名随机，可能 `_`）
        4 => {
            let nm = ["b", "β", "_", "名"][rng.below(4) as usize].to_string()
                + &rng.below(3).to_string();
            names.push(nm.clone());
            let body = fuzz_term(rng, depth - 1, names);
            names.pop();
            format!("({} : U) -> ({})", nm, body)
        }
        // 无名箭头
        5 => {
            let d = fuzz_term(rng, depth - 1, names);
            let c = fuzz_term(rng, depth - 1, names);
            format!("({}) -> ({})", d, c)
        }
        // let（注解恒 U，值/体随机——值类型不对时走报错 parity）
        6 => {
            let nm = ["w", "物", "ζ"][rng.below(3) as usize].to_string()
                + &rng.below(3).to_string();
            let val = fuzz_term(rng, depth - 1, names);
            names.push(nm.clone());
            let body = fuzz_term(rng, depth - 1, names);
            names.pop();
            format!("(let {nm} : U = ({}); {})", val, body)
        }
        // 括号
        7 => format!("({})", fuzz_term(rng, depth - 1, names)),
        // 注释穿插
        _ => format!("{{- c{} -}} {}", rng.below(100), fuzz_term(rng, depth - 1, names)),
    }
}

#[test]
fn v2_fuzz_parity_battery() {
    // 1200 个固定种子生成的程序：nf/type 双模式参考版↔孪生版逐字节一致。
    // 生成面覆盖 λ/应用/Pi/箭头/let/括号/注释/unicode/重名 binder，
    // 良构与错误路径混跑（parity 是唯一的 oracle，错误输出同样互检）。
    for seed in 0..1200u64 {
        let depth = if seed % 3 == 0 { 7 } else { 5 };
        let mut rng = Rng(seed.wrapping_mul(0x1234_5678_9ABC_DEF1));
        let mut names = Vec::new();
        let src = fuzz_term(&mut rng, depth, &mut names);
        let b = nf(&src);
        let f = fast_nf(&src);
        assert_eq!(b, f, "fuzz(seed={seed}) nf 模式不一致，src:\n{src}\n--- basic ---\n{b}--- fast ---\n{f}");
        let b = ty(&src);
        let f = fast_ty(&src);
        assert_eq!(b, f, "fuzz(seed={seed}) type 模式不一致，src:\n{src}\n--- basic ---\n{b}--- fast ---\n{f}");
    }
}

/// 良构 church 程序组合器：随机 add/mul 组合 + 倍增链（eval/quote/conv
/// 在「通过检查」的深路径上的扫描；输出必然成功，可加 nf⊃type oracle）。
/// 返回 (源码, 数值)，数值用于把归约规模钉在安全线内——参考版 quote 是
/// 递归实现（readme「已知限制」），默认测试线程上链长 >1000 会炸栈
/// （进程级 STATUS_STACK_OVERFLOW，panic 钩子都拦不住），必须靠生成器
/// 侧限值而不是事后护栏。
fn fuzz_welltyped_program(rng: &mut Rng) -> (String, u64) {
    let mut s = String::from(
        "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
         let add : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z);\n\
         let mul : Nat -> Nat -> Nat = \\a b N s z. a N (b N s) z;\n",
    );
    // 0..4 号字面量 numeral
    for i in 0..5usize {
        s.push_str(&format!(
            "let c{i} : Nat = \\N s z. {};\n",
            format!("{}z{}", "s (".repeat(i), ")".repeat(i))
        ));
    }
    // 倍增链 d1..d3：`let d{k} : Nat = add d{k-1} d{k-1};`
    s.push_str("let d0 : Nat = c4;\n");
    for k in 1..=3usize {
        s.push_str(&format!("let d{k} : Nat = add d{} d{};\n", k - 1, k - 1));
    }
    // 随机组合表达式（操作数池：c0..c4 / d1..d3，带数值）
    let operand = |rng: &mut Rng| -> (String, u64) {
        let pool = [("c0", 0u64), ("c1", 1), ("c2", 2), ("c3", 3), ("c4", 4), ("d1", 8), ("d2", 16), ("d3", 32)];
        let (n, v) = pool[rng.below(pool.len() as u64) as usize];
        (n.to_string(), v)
    };
    let (mut expr, mut val) = operand(rng);
    for _ in 0..(1 + rng.below(4)) {
        let (o2, v2) = operand(rng);
        // 括号必须显式：源码应用是左折叠，不加括号会变成 op 吃一串实参。
        // mul 超限（>900）就退化为 add，把 quote/pretty 深度留在安全线内。
        if rng.below(2) == 0 || val * v2 > 900 {
            expr = format!("add ({}) ({})", expr, o2);
            val += v2;
        } else {
            expr = format!("mul ({}) ({})", expr, o2);
            val *= v2;
        }
    }
    (s + &expr, val)
}

#[test]
fn v2_fuzz_welltyped_numeric_battery() {
    // 60 个随机良构 church 程序：nf = type 模式的嵌入关系 + 双实现
    // 逐字节 parity（归约规模限值 ≤900，默认测试线程栈可跑）。
    for seed in 0..60u64 {
        let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 0xDEAD_BEEF);
        let (src, val) = fuzz_welltyped_program(&mut rng);
        assert!(val <= 900, "seed {seed} 生成的 numeral 超限：{val}");
        assert_nf_embeds_type(&src);
        assert_parity(&src);
    }
}

#[test]
fn v2_cross_l03_welltyped_numeric_battery() {
    // 跨章 oracle：无 hole 的良构程序里 L03（独立演进的一章）输出必须与
    // L02 逐字节一致。只比成功输出——L03 的报错文案（unify 风格）与 L02
    // 本就不同；只覆盖「无 `_` 出现」的生成面（L03 在项位置把 `_` 变成
    // hole，语义面不同）。
    for seed in 0..20u64 {
        let mut rng = Rng(seed.wrapping_mul(0x0DDB_1A5E_5EED) ^ 0x1234_9876);
        let (src, _val) = fuzz_welltyped_program(&mut rng);
        if src.contains('_') {
            continue;
        }
        let b = nf(&src);
        if b.starts_with("(stdin)") {
            continue; // 生成器漏出的错误程序：报错文案跨章本就不同，跳过
        }
        assert_eq!(b, L03_holes::main_with("nf", &src), "L02/L03 nf 分歧，src:\n{src}");
        assert_eq!(ty(&src), L03_holes::main_with("type", &src), "L02/L03 type 分歧，src:\n{src}");
    }
}

// 更多语义角落（第二轮补充）
// --------------------------------------------------------------------------------

#[test]
fn v2_ident_containing_lambda_char_in_middle() {
    // λ 只在 ident **首位**被切开成 Lambda token；中/尾部的 λ 是普通字母
    // 字符，可以进名字。λ 起首的串（如 `λxλ`）必然是 λ 前缀 + 其余 token，
    // 不能作名字——`let λxλ : U = …` 是 parse error（钉住该词法行为）。
    let src = "let aλ : U = U; aλ";
    assert_eq!(nf(src), "U\n  :\nU\n");
    let src2 = "let xλy : U = U; xλy";
    assert_eq!(nf(src2), "U\n  :\nU\n");
    assert_eq!(nf("let λxλ : U = U; λxλ"), "parse error\n");
    assert_parity(src);
    assert_parity(src2);
    assert_parity("let λxλ : U = U; λxλ");
}

#[test]
fn v2_conv_ignores_pi_binder_names_named_vs_named() {
    // 同一 Π 类型换 binder 名后 conv 仍通过（z ↔ y）。
    let src = "let f : (z : U) -> z -> z = \\z z2. z2; let g : (y : U) -> y -> y = f; g";
    assert_eq!(nf(src), "λ z z2. z2\n  :\n(y : U) → y → y\n");
    assert_parity(src);
}

#[test]
fn v2_unicode_binder_prime_in_nf_print() {
    // 重名 unicode binder 的 prime 是 ASCII 撇号：类型'。
    let src = "(类型 : U) -> (类型 : U) -> 类型";
    assert_eq!(nf(src), "(类型 : U)(类型' : U) → 类型'\n  :\nU\n");
    assert_parity(src);
}

#[test]
fn v2_dependent_pi_id_type_nf() {
    // 依赖 Π（第二 binder 的定义域是 a）：`(a : U) -> (b : a) -> a`，
    // nf 保留依赖打印；应用后依赖替换成 `U → U → U → U`。
    let src = "let id2 : (a : U) -> (b : a) -> a = \\a b. b; id2";
    assert_eq!(nf(src), "λ a b. b\n  :\n(a : U)(b : a) → a\n");
    assert_parity(src);
    let applied = "let id2 : (a : U) -> (b : a) -> a = \\a b. b; id2 (U -> U) (\\x. x)";
    assert_eq!(nf(applied), "λ x. x\n  :\nU → U\n");
    assert_parity(applied);
}
