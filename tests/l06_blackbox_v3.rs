//! L06_string 黑盒测试套件 · 第三卷（v3）——新一轮攻击面。
//!
//! v1（基础形态 / prim / decl 表 / 重定义）/ v2（剪枝 / 跨轮隔离 / 词法
//! 角落）之外的黑盒攻击面，双 oracle 同前（期望输出 + 参考版↔孪生版
//! Ok 逐字节、Err 判定一致；失败信息带出源码）：
//!
//! - **字符串字面量边界**：全转义表（`\n` `\t` `\r` `\0` 未知转义原样）、
//!   多字节/emoji、2 万字符超长串、源码内原生换行/CRLF/制表、块注释标记
//!   出现在字面量里、注释内出现引号、行注释无换行收尾；
//! - **builtin prim 元数边界**：实参不足卡住（不 panic）、实参为洞（未解
//!   meta）卡住、嵌套 prim 链（str_eq 喂 string_concat、indent 叠加）、
//!   卡住 prim 的 pretty 括号形态、命名实参 / icit 失配的定向报错；
//! - **可变全局**：同名 global 与 def 冲突（已登记名按登记类型把关的
//!   推论面）、global 存自身卡住头、prim/部分应用当 `change_mutable` 的
//!   函数实参、闭包捕获时机（应用时读最新值）、空名/含空格键、
//!   `get_global_default` 纯读（不建档）、未解 meta 存进 global；
//! - **decl 表 / string_to_global_type**：builtin 名（含自身）、def 的
//!   函数值、动态（变量）名、String 型 def 名的"动态类型 = 登记值"边角；
//! - **错误路径与解析残缺**：空文件/纯空白/纯注释/残缺 decl 一律 Err 不
//!   panic，残余 token 的偏移定位精确到字节；
//! - **跨轮隔离新角度**：稳态复用时同名 def 重定义不报错（decl 表随轮
//!   清空）；`path_id` 变化不影响 Ok 输出。
//!
//! 挂死防护口径：本套件所有用例都**有界**（会发散的自应用递归是栈溢出
//! 而非死循环——子线程超时拦不住进程 abort，v1 已钉其 elaborate 判定并
//! 明确不引读输出，这里不再重复触发）；深递归用例（深层括号、30 连 λ）
//! 在 256MB 栈线程里跑。命令行统一 `timeout 600 cargo test …` 兜底。

#[path = "../src/list.rs"]
mod list;

#[path = "../src/parser_lib.rs"]
mod parser_lib;
#[path = "../src/parser_lib_resilient.rs"]
mod parser_lib_resilient;

#[path = "../src/L06_string/mod.rs"]
mod L06_string;

use L06_string::bump_spine_iter as fast;

/// 文件 IO builtin 用固定文件名——本 crate 里所有做文件副作用的用例
/// 统一经模块内的这把锁串行（Windows 并行线程的句柄竞争会让删除报
/// os error 5）。
use L06_string::FILE_IO_LOCK;

fn run_basic(src: &str) -> Result<String, L06_string::Error> {
    L06_string::run(src, 0)
}

fn run_basic_at(src: &str, path_id: u32) -> Result<String, L06_string::Error> {
    L06_string::run(src, path_id)
}

fn run_fast(src: &str) -> Result<String, L06_string::Error> {
    fast::run_fast(src, 0)
}

/// Oracle 2：参考版与性能版的 Ok 输出逐字节一致；Err 判定一致。
fn assert_parity(src: &str) {
    let b = run_basic(src);
    let f = run_fast(src);
    match (&b, &f) {
        (Ok(b), Ok(f)) => assert_eq!(
            b, f,
            "Ok 输出双实现不一致，src:\n{src}\n--- basic ---\n{b}--- fast ---\n{f}"
        ),
        (Err(_), Err(_)) => {}
        _ => panic!(
            "判定不一致（basic={}，fast={}），src:\n{src}",
            b.map(|_| "Ok").unwrap_or("Err"),
            f.map(|_| "Ok").unwrap_or("Err")
        ),
    }
}

/// 双实现都 Ok 且输出恰为 expect（带源码的失败信息）。
fn assert_out(src: &str, expect: &str) {
    assert_parity(src);
    let out = run_basic(src).unwrap_or_else(|e| panic!("应 Ok：{src}\nerr: {e:?}"));
    assert_eq!(out, expect, "输出不符，src:\n{src}");
}

/// 双实现都 Err 且消息含 needle（Error 字段私有，经 Display/Debug 读内容；
/// 含 span 偏移的消息只做 needle 断言——快版 span 全零是文档化偏差）。
fn assert_error_parity(src: &str, needle: &str) {
    let b = run_basic(src);
    let f = run_fast(src);
    assert!(b.is_err(), "basic 应报错：{src}");
    assert!(f.is_err(), "fast 应报错：{src}");
    assert!(
        format!("{:?}", b.unwrap_err()).contains(needle),
        "basic 消息缺 {needle:?}：{src}"
    );
    assert!(
        format!("{:?}", f.unwrap_err()).contains(needle),
        "fast 消息缺 {needle:?}：{src}"
    );
}

/// 深递归用例的 256MB 栈线程（v1 同款口径）。
fn with_big_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

// 字符串字面量边界
// --------------------------------------------------------------------------------

/// 全转义表：`\n` `\t` `\r` `\0` 各打印真实控制字符（Rust 源里 `\\n` 是
/// ty 源的转义序列两字符）。
#[test]
fn escape_table_control_chars() {
    // \n → 换行
    assert_out("println \"a\\nb\"\n", "a\nb\n");
    // \t → 制表
    assert_out("println \"a\\tb\"\n", "a\tb\n");
    // \r → 回车
    assert_out("println \"a\\rb\"\n", "a\rb\n");
    // \0 → NUL
    assert_out("println \"a\\0b\"\n", "a\u{0}b\n");
}

/// 未知转义原样保留（`\` + 字符两字符原文）；`\\` 与未知转义相邻不串扰。
#[test]
fn unknown_escape_kept_verbatim() {
    assert_out("println \"a\\qb\"\n", "a\\qb\n");
    assert_out("println \"\\\\x\\y\"\n", "\\x\\y\n");
}

/// 多字节/emoji 内容：打印、拼接、str_eq 的字节级 parity（快版 string_concat
/// 是裸 memcpy + from_utf8_unchecked，多字节拼接不得产生坏 UTF-8）。
#[test]
fn unicode_multibyte_content() {
    assert_out("println \"你好，世界！🎉 αβγ\"\n", "你好，世界！🎉 αβγ\n");
    assert_out(
        "println (string_concat \"你\" \"好\")\n",
        "你好\n",
    );
    assert_out("println (str_eq \"你\" \"好\")\n", "false\n");
    assert_out("println (str_eq \"🎉α\" \"🎉α\")\n", "true\n");
    // 转义与多字节相邻（`\` 跳 2 字节的配对不得咬到多字节序列）
    assert_out("println \"a\\n你好\"\n", "a\n你好\n");
}

/// 超长串（2 万字符）：字面量引读、str_eq 逐字节相等/不等、两半拼接复原。
#[test]
fn very_long_literal() {
    let half1 = "ab".repeat(5000); // 10_000 chars
    let half2 = "cd".repeat(5000);
    let long = format!("{half1}{half2}");
    let src = format!(
        "def a : String = \"{long}\"\n\
         println a\n\
         def b : String = \"{long}\"\n\
         println (str_eq a b)\n\
         def c : String = string_concat a \"{half2}\"\n\
         println (str_eq a c)\n\
         println (string_concat \"{half1}\" \"{half2}\")\n"
    );
    let out = run_basic(&src).unwrap();
    assert_eq!(&out[..long.len()], &long[..], "长串引读必须逐字节一致");
    let rest = &out[long.len() + 1..];
    assert_eq!(rest, "true\nfalse\n{long}\n".replace("{long}", &long), "后三行不符");
    assert_parity(&src);
}

/// 源码内原生换行/制表进字面量（lexer 不拒多行 token）；CRLF 行尾的 decl 流。
#[test]
fn raw_newline_tab_and_crlf() {
    // 字面量跨行：源码里就是真实换行
    assert_out("println \"l1\nl2\"\n", "l1\nl2\n");
    // 源码内原生制表符
    assert_out("println \"a\tb\"\n", "a\tb\n");
    // CRLF 行尾
    assert_out("def s : String = \"a\"\r\nprintln s\r\n", "a\n");
    // `\r\n` 在字面量内部原样保留（缩进只看 `\n`，`\r` 挂在行尾）
    assert_out("println (str_indent2 \"a\r\nb\")\n", "a\r\n  b\n");
}

/// 注释与字面量的互不干扰（v1 钉过 `//`/`/*` 在字面量内；这里攻击反向）：
/// 注释内出现引号不得开启字符串、行注释无换行收尾、空块注释。
#[test]
fn comments_containing_quotes_and_tail_cases() {
    // 行注释里有未闭合引号——不得把后续源码吞成字符串
    assert_out("def s = \"x\" // \"unclosed quote in comment\nprintln s\n", "x\n");
    // 块注释里有未闭合引号同理
    assert_out("/* \"unterminated */\nprintln \"y\"\n", "y\n");
    // 行注释在文件末尾无换行（注释吞到 EOF，println 在注释前）
    assert_out("println \"z\" // tail", "z\n");
    // 空块注释紧跟字面量
    assert_out("def s = \"w\"/**/\nprintln s\n", "w\n");
    // `*/` 出现在字面量里（无配对 `/*`）原样保留
    assert_out("println \"a*/b\"\n", "a*/b\n");
}

/// 文档化怪癖钉住：未闭合块注释静默吞掉余下全部 decl（readme「已知限制」
/// 明示的历史行为，无告警）——run 以 Ok("") 结束而非报错。
#[test]
fn unterminated_block_comment_swallows_rest() {
    assert_out("def s = \"a\" /* oops\nprintln s\n", "");
}

// 错误路径与解析残缺
// --------------------------------------------------------------------------------

/// 残缺输入一律解析 Err（不 panic、不静默空转）。
#[test]
fn truncated_inputs_all_parse_error() {
    for src in [
        "",                                  // 空文件
        "   \n\t  ",                         // 纯空白
        "// only comment\n",                 // 纯行注释
        "/* only block */",                  // 纯块注释
        "println\n",                         // println 缺体
        "def println : U = U\n",             // 关键字当 def 名
        "def def = U\n",                     // 关键字当 def 名（第二 token）
        "println 42\n",                      // 数字不是 atom
        "def a : String = \"unclosed\n",     // 未闭合字符串（lex 失败）
        "println (string_concat \"a\" \"b\"\n", // 括号不闭
    ] {
        let b = run_basic(src);
        let f = run_fast(src);
        assert!(b.is_err(), "basic 应报错：{src:?}");
        assert!(f.is_err(), "fast 应报错：{src:?}");
        assert!(
            format!("{:?}", b.unwrap_err()).contains("parse error"),
            "缺 parse error：{src:?}"
        );
    }
}

/// 残余 token 的偏移定位精确到字节（共用 parser，两版消息全文一致）。
/// 注意 op 的 pmatch 是贪心连续段：`???`/`%%` 各是**一个** Op token
///（不在 OP 表内 → kind=Op，内容保留整段）。
#[test]
fn leftover_token_offset_exact() {
    // "def a : U = U" 13 字节 + `\n` → `???` 起于 14，止于 17
    let src = "def a : U = U\n???\n";
    assert_eq!(src.find("???").unwrap(), 14);
    let b = run_basic(src).unwrap_err().to_string();
    let f = run_fast(src).unwrap_err().to_string();
    assert!(b.contains("leftover token `???` @ 14,17"), "basic: {b}");
    assert_eq!(b, f, "解析错误消息两版应全文一致：{src}");
    // 字符串后的垃圾 op：`%%` 起于 12（println+空格+"x"+空格）
    let src2 = "println \"x\" %%\n";
    let b2 = run_basic(src2).unwrap_err().to_string();
    let f2 = run_fast(src2).unwrap_err().to_string();
    assert!(b2.contains("leftover token `%%` @ 12,14"), "basic: {b2}");
    assert_eq!(b2, f2);
    // 单字符残余（`;`）的定位（v2 已钉消息，这里钉偏移）
    let src3 = "def a : U = U\n;\n";
    let b3 = run_basic(src3).unwrap_err().to_string();
    assert!(b3.contains("leftover token `;` @ 14,15"), "basic: {b3}");
}

/// 深层括号（300 层）解析与求值不爆栈、输出不变（大栈线程）。
#[test]
fn deep_parenthesized_expr() {
    let depth = 300;
    let src = format!(
        "println {}U{}\n",
        "(".repeat(depth),
        ")".repeat(depth)
    );
    let src2 = src.clone();
    let out = with_big_stack(move || run_basic(&src2).unwrap());
    assert_eq!(out, "U\n");
    with_big_stack(move || {
        assert_parity(&src);
    });
}

/// 30 连 λ 链的 pretty 逐字节（binder 名去重不触发——名字全异）。
#[test]
fn deep_lambda_chain_exact() {
    let binders: Vec<String> = (0..30).map(|i| format!("b{i}")).collect();
    let lam = binders.iter().map(|b| format!("{b} => ")).collect::<String>();
    let src = format!("def deep = {lam}b0\nprintln deep\n");
    let expect = format!(
        "{}b0\n",
        binders.iter().map(|b| format!("{b}=> ")).collect::<String>()
    );
    assert_out(&src, &expect);
}

// builtin prim 元数边界与嵌套链
// --------------------------------------------------------------------------------

/// 元数不足卡住（不 panic）：3 参的 report 只喂 2 参、1 参的 indent 空头、
/// 部分应用经 println 直接引读。
#[test]
fn prim_arity_short_stays_stuck() {
    assert_out("println (string_concat \"a\")\n", "string_concat a\n");
    assert_out("println (report_check_issue \"A\" \"m\")\n", "report_check_issue A m\n");
    assert_out("println (report_check_issue \"A\" \"m\" \"s\")\n", "report_check_issue A m s\n");
    assert_out("println str_indent2\n", "str_indent2\n");
    assert_out("println file_exists\n", "file_exists\n");
}

/// 实参为洞（未解 meta）卡住 + meta 编号连续性：洞进 prim 实参位不被求解、
/// 按创建顺序 ?0 ?1 打出。
#[test]
fn prim_hole_args_stuck_and_meta_numbering() {
    assert_out("println (str_indent2 _)\n", "str_indent2 ?0\n");
    assert_out("println (get_global _)\n", "get_global ?0\n");
    assert_out("println (string_concat _ _)\n", "string_concat ?0 ?1\n");
    // 编号跨 def 延续：?0 被第一个 def 捕获，后续洞是 ?1
    assert_out(
        "def s : String = string_concat \"a\" _\nprintln s\nprintln (string_concat \"b\" _)\n",
        "string_concat a ?0\nstring_concat b ?1\n",
    );
}

/// 嵌套 prim 链化简：str_eq 产出字面量喂 string_concat、indent 叠加、
/// concat 产出喂 indent（内层先触发，外层拿到的是字面量）。
#[test]
fn prim_nested_chains() {
    assert_out("println (string_concat (str_eq \"x\" \"y\") \"!\")\n", "false!\n");
    assert_out("println (string_concat (str_eq \"\" \"\") \"z\")\n", "truez\n");
    assert_out("def d = str_indent2 (str_indent2 \"a\nb\")\nprintln d\n", "a\n    b\n");
    assert_out("println (str_indent2 (string_concat \"x\n\" \"y\"))\n", "x\n  y\n");
    // 三层链：eq → concat → concat
    assert_out(
        "println (string_concat (string_concat (str_eq \"x\" \"y\") \"!\") \"?\")\n",
        "false!?\n",
    );
}

/// 卡住 prim 的 pretty 形态：实参位的应用要裹花括号（与 church 输出同款
/// 约定），字面量实参打印原文。
#[test]
fn stuck_prim_pretty_shapes() {
    // get_global "zz" 卡住 → 实参位整体是应用 → {…}
    assert_out(
        "println (string_concat \"P\" (get_global \"zz\"))\n",
        "string_concat P {get_global zz}\n",
    );
    // 两层卡住实参
    assert_out(
        "println (string_concat (get_global \"z1\") (get_global \"z2\"))\n",
        "string_concat {get_global z1} {get_global z2}\n",
    );
}

/// 命名实参喂 prim：insert_until_name 找不到隐式 Π 位 → 定向报错。
#[test]
fn prim_named_arg_is_error() {
    assert_error_parity(
        "println (string_concat [y = \"b\"] \"a\")\n",
        "no named implicit arg",
    );
}

/// 隐式实参喂 Expl-only prim：icit mismatch 定向报错。
#[test]
fn prim_implicit_arg_is_icit_mismatch() {
    assert_error_parity("println (str_eq [U] \"a\" \"b\")\n", "icit mismatch");
}

/// 非字面量实参（类型 U 的名字）喂 prim → 类型层先报 can't unify。
#[test]
fn prim_nonliteral_typed_arg_is_error() {
    assert_error_parity("def n : U = U\nprintln (string_concat \"a\" n)\n", "can't unify");
}

/// report_check_issue 的元数/跳过/去重/顺序：module 位是洞（非字面量）
/// → 整条跳过且不建档；行级去重按整行相等；追加保序。
#[test]
fn report_check_issue_variants() {
    assert_out(
        concat!(
            "def i1 : U = report_check_issue \"A\" \"m\" \"s1\" \"msg1\"\n",
            "def i2 : U = report_check_issue \"A\" \"m\" \"s2\" \"msg2\"\n",
            "def i3 : U = report_check_issue \"A\" \"m\" \"s1\" \"msg1\"\n",
            "def issues : String = get_global \"CheckIssues\"\n",
            "println issues\n",
        ),
        "A|m|s1|msg1\nA|m|s2|msg2\n",
    );
    // 非 module（洞）→ 跳过：CheckIssues 未建档 → get_global 卡住
    assert_out(
        "def i0 : U = report_check_issue \"E9\" _ \"sig\" \"msg\"\nprintln (get_global \"CheckIssues\")\n",
        "get_global CheckIssues\n",
    );
    // 3 参不足卡住（不触发、不 panic）
    assert_out("println (report_check_issue \"A\" \"m\" \"s\")\n", "report_check_issue A m s\n");
}

// string_to_global_type / decl 表边角
// --------------------------------------------------------------------------------

/// st2g 取 builtin 名：值 = 注册的卡住头（打印名字本身）；st2g 自身亦可。
#[test]
fn st2g_of_builtin_names() {
    assert_out(
        concat!(
            "def t1 : U = string_to_global_type \"str_indent2\"\nprintln t1\n",
            "def t2 : U = string_to_global_type \"string_to_global_type\"\nprintln t2\n",
            "def t3 : U = string_to_global_type \"String\"\nprintln t3\n",
        ),
        "str_indent2\nstring_to_global_type\nString\n",
    );
}

/// st2g 取 def 的函数值：登记值整体（λ 打印原文形态）。
#[test]
fn st2g_of_def_function_value() {
    assert_out(
        "def f : U -> U = x => x\ndef t : U = string_to_global_type \"f\"\nprintln t\n",
        "x=> x\n",
    );
}

/// st2g 的动态（变量）名：应用时触发，卡住/命中都按当时 decl 表。
#[test]
fn st2g_dynamic_variable_name() {
    assert_out(
        concat!(
            "def dyn(x : String) : U = string_to_global_type x\n",
            "println (dyn \"String\")\n",
            "println (dyn \"get_global\")\n",
            "println (dyn \"Nope\")\n",
        ),
        "String\nget_global\nNope\n",
    );
}

/// st2g 取的是登记**值**（类型即值）：String 型 def 名的"动态类型"是
/// 字面量值本身 → 与 String 注解不可合一（unify 无 LiteralIntro 臂的
/// 推论面）；bare println（无注解）则 eval 走 map miss → 卡住的 prim 头。
#[test]
fn get_global_of_string_typed_def_name() {
    assert_out(
        "def s : String = \"a\"\nprintln (get_global \"s\")\n",
        "get_global s\n",
    );
    assert_error_parity(
        "def s : String = \"a\"\ndef g : String = get_global \"s\"\nprintln g\n",
        "can't unify",
    );
}

// 可变全局
// --------------------------------------------------------------------------------

/// 交错序列：create → 读 → change → 读 → change_default（已有则 f）→
/// change_default（缺失则建档为 default，f 不施加）。
#[test]
fn global_interleave_sequence() {
    assert_out(
        concat!(
            "def g0 : U = create_global \"k\" \"1\"\n",
            "println (get_global \"k\")\n",
            "def u1 : U = change_mutable \"k\" (s => string_concat s \"2\")\n",
            "println (get_global \"k\")\n",
            "def u2 : U = change_mutable_default \"k\" (s => string_concat s \"3\") \"x\"\n",
            "println (get_global \"k\")\n",
            "def u3 : U = change_mutable_default \"n2\" (s => string_concat s \"!\") \"fresh\"\n",
            "println (get_global \"n2\")\n",
        ),
        "1\n12\n123\nfresh\n",
    );
}

/// 同轮重复 create 覆盖；get_global_default 纯读不建档（miss 后再 get 仍卡住）。
#[test]
fn global_overwrite_and_default_readonly() {
    assert_out(
        concat!(
            "def a : U = create_global \"k\" \"1\"\n",
            "def b : U = create_global \"k\" \"2\"\n",
            "println (get_global \"k\")\n",
        ),
        "2\n",
    );
    assert_out(
        concat!(
            "def d1 : String = get_global_default \"fk\" \"d\"\n",
            "println d1\n",
            "println (get_global \"fk\")\n",
        ),
        "d\nget_global fk\n",
    );
}

/// global 存自身卡住头：create 时 map 还空 → get_global 卡在自己的
/// prim 头（`get_global k`）入表；之后 change_mutable 的 f 拿到的是
/// 卡住值 → 整体保持卡住（非字面量不触发）。
#[test]
fn global_self_stuck_storage() {
    assert_out(
        concat!(
            "def g : U = create_global \"k\" (get_global \"k\")\n",
            "println (get_global \"k\")\n",
            "def u : U = change_mutable \"k\" (s => string_concat s \"!\")\n",
            "println (get_global \"k\")\n",
        ),
        "get_global k\nstring_concat {get_global k} !\n",
    );
    // 有值（即便卡住）时 default 被忽略
    assert_out(
        concat!(
            "def g2 : U = create_global \"k2\" (get_global \"k2\")\n",
            "def d : String = get_global_default \"k2\" \"fb\"\nprintln d\n",
        ),
        "get_global k2\n",
    );
}

/// prim / 部分应用当 `change_mutable` 的函数实参（f 的类型与卡住 decl 的
/// 宽松臂互锁）：bare `str_indent2`（元数 1 立即触发）、`string_concat "P"`
/// （部分应用补触发）、bare `string_concat`（余域不是 String → 定向 Err）。
#[test]
fn global_prim_as_change_function() {
    assert_out(
        concat!(
            "def g0 : U = create_global \"k\" \"a\nb\"\n",
            "def u1 : U = change_mutable \"k\" str_indent2\n",
            "def v1 : String = get_global \"k\"\nprintln v1\n",
            "def g2 : U = create_global \"k2\" \"v\"\n",
            "def u2 : U = change_mutable \"k2\" (string_concat \"P\")\n",
            "def v2 : String = get_global \"k2\"\nprintln v2\n",
        ),
        "a\n  b\nPv\n",
    );
    // bare string_concat 的余域是 Pi 而非卡住 decl → can't unify
    assert_error_parity(
        "def g : U = create_global \"k\" \"v\"\ndef u : U = change_mutable \"k\" string_concat\n",
        "can't unify",
    );
}

/// 闭包捕获时机：λ 体里的 get_global 在**应用时**求值——定义在前、
/// change 在后、应用最后 → 读到的是改后值。
#[test]
fn global_closure_capture_timing() {
    assert_out(
        concat!(
            "def g0 : U = create_global \"k\" \"v1\"\n",
            "def f : String -> String = x => string_concat x (get_global \"k\")\n",
            "def u1 : U = change_mutable \"k\" (s => string_concat s \"!\")\n",
            "println (f \"cur=\")\n",
        ),
        "cur=v1!\n",
    );
}

/// 同名 global 与 def 冲突（readme「已登记名按登记类型把关」的推论面）：
/// `create_global "k" "v"` 的第二实参类型 st2g"k" 查表得已登记的 U →
/// 与 String 定向 can't unify（写都写不进去）；bare `get_global "k"` 无
/// 注解不受影响——map miss 卡住头照打。
#[test]
fn global_name_clash_with_def() {
    assert_error_parity(
        "def k : U = U\ndef g0 : U = create_global \"k\" \"v\"\n",
        "can't unify",
    );
    // bare println（无注解）：map miss → 卡住的 get_global prim 头
    assert_out("def k : U = U\nprintln (get_global \"k\")\n", "get_global k\n");
}

/// 空名/含空格键：map 键就是字面量内容，无转义无修剪。
#[test]
fn global_empty_and_space_keys() {
    assert_out(
        concat!(
            "def a : U = create_global \"\" \"empty\"\n",
            "def b : U = create_global \"a b\" \"spaced\"\n",
            "println (get_global \"\")\n",
            "println (get_global \"a b\")\n",
        ),
        "empty\nspaced\n",
    );
}

/// 未解 meta 存进 global：create 的实参位是洞 → 值是 Flex；get 回读打印 ?0。
#[test]
fn global_stores_unsolved_meta() {
    assert_out(
        concat!(
            "def g : U = create_global \"k\" _\n",
            "def v : String = get_global \"k\"\nprintln v\n",
        ),
        "?0\n",
    );
}

/// 洞当 global 键名：st2g 对非字面量卡住 → 实参类型是卡住的
/// `string_to_global_type ?0` 头（已登记名）→ 与 String 不再宽松 → Err。
#[test]
fn global_hole_name_is_error() {
    assert_error_parity("def g : U = create_global _ \"v\"\n", "can't unify");
}

// decl / println / let / β 杂项
// --------------------------------------------------------------------------------

/// println 多行输出顺序（定义与字面量交错）。
#[test]
fn println_multi_line_order() {
    assert_out(
        concat!(
            "println \"one\"\n",
            "def a : String = \"two\"\n",
            "println a\n",
            "println \"three\"\nprintln (string_concat \"four\" \"five\")\n",
        ),
        "one\ntwo\nthree\nfourfive\n",
    );
}

/// β-redex 里触发 prim：λ 体在应用时求值，实参先于外层应用求值。
#[test]
fn beta_redex_with_prim() {
    assert_out("println ((x => string_concat x \"!\") \"a\")\n", "a!\n");
    assert_out("println ((x => x) \"raw\")\n", "raw\n");
}

/// let 无注解（洞注解可解）+ let 内触发 prim。
#[test]
fn let_without_annotation_with_prim() {
    assert_out(
        "def s = let t = \"a\"; string_concat t \"b\"\nprintln s\n",
        "ab\n",
    );
    assert_out(
        "def s : String = let t : String = \"L\"; string_concat t \"R\"\nprintln s\n",
        "LR\n",
    );
}

/// def 无返回类型注解（洞类型可解）+ 值引读。
#[test]
fn def_without_ret_annotation() {
    assert_out(
        "def f (x : U) = x\nprintln (f U)\nprintln f\n",
        "U\nx=> x\n",
    );
}

/// binder 名遮蔽 builtin（String）后再用 builtin 不受影响。
#[test]
fn binder_shadows_builtin_name() {
    assert_out(
        "def g (String : U) : U = String\nprintln (g U)\nprintln \"after\"\n",
        "U\nafter\n",
    );
}

/// Π 类型的 pretty：匿名域的箭头形态（金样）。
#[test]
fn pi_type_pretty() {
    assert_out("def T : U = U -> U\nprintln T\n", "U → U\n");
}

/// 递归 def 的新角度：**值级**自引用冻结在 def 时刻——体的求值发生在
/// 占位替换之前，`string_concat h "!"` 里的 h 命中占位（卡住 Decl 头）
/// 且 prim 对非字面量不触发 → 登记值整体卡住，println 引读安全（不发散；
/// 对照：λ 体里的自**应用**会在引读时经终值 β 展开，即 v1 记录的发散形
/// 态，不可 println——本套件不触发）。
#[test]
fn recursive_def_value_level_stuck() {
    assert_out(
        "def h : String = string_concat h \"!\"\nprintln h\n",
        "string_concat h !\n",
    );
}

/// def 先用后定义 → 定向 name not in scope（run 在首错即停）。
#[test]
fn use_before_def_is_scope_error() {
    assert_error_parity("println later\ndef later : U = U\n", "name not in scope");
}

// 文件 IO 组合（锁内）
// --------------------------------------------------------------------------------

/// 文件组与 string 组的组合嵌套：写空内容、多字节内容、覆盖写、
/// exists("") → false；内容经 string_concat 拼装。
#[test]
fn file_io_combinations() {
    let _guard = FILE_IO_LOCK.lock().unwrap();
    let p = "l06_blackbox_v3_tmp.txt";
    let src = format!(
        concat!(
            "def w0 : U = file_write_all_text \"{p}\" \"\"\n",
            "def r0 : String = file_read_all_text \"{p}\"\nprintln r0\n",
            "def w1 : U = file_write_all_text \"{p}\" (string_concat \"你好\" \"世界\")\n",
            "def r1 : String = file_read_all_text \"{p}\"\nprintln r1\n",
            "def w2 : U = file_write_all_text \"{p}\" \"second\"\n",
            "def r2 : String = file_read_all_text \"{p}\"\nprintln r2\n",
            "println (file_exists \"\")\n",
            "println (str_eq r2 \"second\")\n",
        ),
        p = p
    );
    assert_parity(&src);
    assert_eq!(
        run_basic(&src).unwrap(),
        "\n你好世界\nsecond\nfalse\ntrue\n"
    );
    let _ = std::fs::remove_file(p);
}

// 跨轮隔离新角度 / path_id
// --------------------------------------------------------------------------------

/// 稳态复用的新角度：decl 表随轮清空 → 上轮 def 同名重定义**不再报
/// redefine**；mutable_map 不跨轮（default 兜底）；meta 编号复位。
#[test]
fn steady_state_redef_allowed_next_round() {
    let mut t = fast::Tycker::new();
    t.run_input("def n : U = U\ndef g : U = create_global \"k\" \"v\"", 0)
        .unwrap();
    assert_eq!(
        t.run_input("def n : U = U\nprintln n\n", 0).unwrap(),
        "U\n",
        "上轮 def 名本轮重定义不得报 redefine"
    );
    assert_eq!(
        t.run_input(
            "def g2 : String = get_global_default \"k\" \"fb\"\nprintln g2\n",
            0
        )
        .unwrap(),
        "fb\n",
        "mutable_map 应随轮清空"
    );
    assert_eq!(
        t.run_input("def s : String = _\nprintln s\n", 0).unwrap(),
        "?0\n",
        "meta 编号应随轮复位"
    );
}

/// path_id 变化不影响 Ok 输出（Err 判定也不受影响）。
#[test]
fn path_id_variations() {
    let src = "def s : String = string_concat \"a\" \"b\"\nprintln s\n";
    for pid in [0u32, 7, 42] {
        assert_eq!(
            run_basic_at(src, pid).unwrap(),
            "ab\n",
            "path_id={pid} 的 Ok 输出应一致"
        );
    }
    let f = fast::run_fast(src, 9).unwrap();
    assert_eq!(f, "ab\n");
    // Err 判定与 path_id 无关
    assert!(run_basic_at("println nope\n", 3).is_err());
    assert!(fast::run_fast("println nope\n", 3).is_err());
}

/// 同一批混合用例的整体 parity 扫描（Ok 逐字节 / Err 判定）。
#[test]
fn mixed_batch_parity_scan() {
    let cases: Vec<String> = vec![
        "println \"\\n\\t\\r\\0\\q\"\n".to_string(),
        "println (string_concat (str_indent2 \"a\nb\") \"!\")\n".to_string(),
        "def p = string_concat \"x\"\nprintln (p \"y\")\n".to_string(),
        "def p = string_concat \"x\"\nprintln p\n".to_string(),
        "def g : U = create_global \"k\" (get_global \"m\")\nprintln (get_global \"k\")\n"
            .to_string(),
        "println (string_concat (get_global \"z\") (str_eq \"\" \"\"))\n".to_string(),
        "def d (x : String) : String = string_concat x (get_global \"kk\")\nprintln (d \"v\")\n"
            .to_string(),
        "def t : U = string_to_global_type \"file_exists\"\nprintln t\n".to_string(),
        "println ((y => str_indent2 y) \"a\nb\")\n".to_string(),
        "def m : U -> U -> U = _\nprintln (m U)\n".to_string(),
        "def e = str_eq \"a\" \"b\"\nprintln (string_concat e e)\n".to_string(),
        "def f : String -> String -> String = string_concat\nprintln f\n".to_string(),
    ];
    for src in &cases {
        assert_parity(src);
    }
}

// 第二轮攻击：st2g 把 def 的函数值当"动态类型"的族（Bug-1 回归）
// --------------------------------------------------------------------------------

/// 【Bug-1 回归】st2g 把 def 的登记值（可以是 λ）当"动态类型"返回后，λ 值
/// 会以类型身份流入 unify：`get_global "f"` 的类型就是 f 的 λ 值，与
/// String 注解（LiteralType）比较时 η 臂曾对**不可应用值**做 v_app——
/// 参考版命中 impossible panic、快版压栈后 Err，判定发散。修复后两版
/// 一致 Err（λ 与非函数值的比较直接失败）。
#[test]
fn bug1_eta_on_inapplicable_literal() {
    assert_error_parity(
        "def f : U -> U = x => x\ndef g : String = get_global \"f\"\nprintln g\n",
        "can't unify",
    );
}

/// 【Bug-1 回归】同族变体：η 的另一侧——λ 值（作为注解实参求出）在
/// `(_, Lam)` 臂吃 **Π 值**的应用，参考版同样 impossible panic。
#[test]
fn bug1_eta_on_inapplicable_pi() {
    assert_error_parity(
        "def f : U -> U = x => x\ndef g : string_to_global_type \"f\" = \"s\"\nprintln g\n",
        "can't unify",
    );
    // change_mutable 的 f 实参位注解是 Π 值（dom_f），get_global "f" 的
    // 类型是 λ 值 → (Π, λ) 比较，同一守卫拦下
    assert_error_parity(
        "def f : U -> U = x => x\ndef g : U = create_global \"k\" \"v\"\ndef u : U = change_mutable \"k\" (get_global \"f\")\n",
        "can't unify",
    );
}

/// 【Bug-1 回归】get_global_default 同族（Lit vs λ 值）。
#[test]
fn bug1_eta_on_inapplicable_default() {
    assert_error_parity(
        "def f : U -> U = x => x\ndef g : String = get_global_default \"f\" \"z\"\n",
        "can't unify",
    );
}

/// st2g 对**函数 def** 名的取值在无注解路径照常（println 引读 λ 值，无
/// unify 参与）；st2g 结果（U 型）喂 string_concat 在类型层先报错。
#[test]
fn st2g_lambda_value_without_unify_is_ok() {
    assert_out(
        "def f : U -> U = x => x\ndef t : U = string_to_global_type \"f\"\nprintln t\n",
        "x=> x\n",
    );
    assert_error_parity(
        "println (string_concat (string_to_global_type \"nope\") \"!\")\n",
        "can't unify",
    );
}

/// change_mutable 的 f 实参位允许绑定变量（Rigid 值 η/β 均安全——守卫
/// 不影响中性值路径）。
#[test]
fn change_mutable_with_bound_function_var() {
    assert_out(
        concat!(
            "def g0 : U = create_global \"k\" \"v\"\n",
            "def run (g : String -> String) : U = change_mutable \"k\" g\n",
            "def u : U = run (s => string_concat s \"!\")\n",
            "println (get_global \"k\")\n",
        ),
        "v!\n",
    );
}

// 第二轮攻击：冻结时机 / 打印形态 / 杂项
// --------------------------------------------------------------------------------

/// def 的值在登记时刻**冻结**：r 先于 create 登记——r 的值是登记时 map
/// miss 的卡住 prim 头，后续 create 不回填（打印经 r 引读仍卡住）。
#[test]
fn def_value_freeze_order() {
    assert_out(
        concat!(
            "def r : String = get_global \"late\"\n",
            "def c : U = create_global \"late\" \"v\"\n",
            "println r\n",
            "println (get_global \"late\")\n",
        ),
        "get_global late\nv\n",
    );
}

/// 洞的 pruning 形态经 λ 引读：体是 `AppPruning ?m [x]`，eval 时掩码应用
/// → `?0 x`；应用后实参代入 → `?0 q`。
#[test]
fn flex_in_lambda_print() {
    assert_out("def f (x : String) : String = _\nprintln f\n", "x=> ?0 x\n");
    assert_out(
        "def f (x : String) : String = _\nprintln (f \"q\")\n",
        "?0 q\n",
    );
}

/// `_` 命名 binder 的打印：Var 位退化为 `@序号`（pretty 的 go_ix 约定）。
#[test]
fn underscore_binder_print() {
    assert_out("def f (_ : String) : String = _\nprintln f\n", "_=> ?0 @0\n");
}

/// 重复 binder 名的 fresh 去重（`a'` 后缀）。
#[test]
fn fresh_name_dedup() {
    assert_out("def d = a => a => a\nprintln d\n", "a=> a'=> a'\n");
}

/// str_eq 的 `'static` 真假字面量存进 global，再被部分应用 prim 改写
///（跨分配层的内容流转：'static → bump 拷贝）。
#[test]
fn static_bool_into_global_chain() {
    assert_out(
        concat!(
            "def b : U = create_global \"k\" (str_eq \"a\" \"a\")\n",
            "def u : U = change_mutable \"k\" (string_concat \"P\")\n",
            "println (get_global \"k\")\n",
        ),
        "Ptrue\n",
    );
}

/// def 别名 prim（0 参头登记为值），后续经别名补触发。
#[test]
fn def_alias_prim_zero_arg_refires() {
    assert_out(
        concat!(
            "def sc : String -> String -> String = string_concat\n",
            "println (sc \"a\" \"b\")\n",
        ),
        "ab\n",
    );
}

/// 隐式实例化与字面量：`f "s"` 的隐式 A 解为 LiteralType。
#[test]
fn implicit_instantiation_with_string() {
    assert_out(
        "def f [A : U] (x : A) : A = x\nprintln (f \"s\")\n",
        "s\n",
    );
}

/// 注解位全是洞：?0 ?1 编号与打印。
#[test]
fn hole_annotations_numbering() {
    assert_out("def f : _ -> _ = x => x\nprintln f\n", "x=> x\n");
}

/// global 不能存类型/函数值（第二实参类型 st2g"k" 是卡住 decl，与 U/
/// Π 无宽松臂）——只有 String 值与同名卡住 decl 可入表。
#[test]
fn global_cannot_store_types_or_functions() {
    assert_error_parity("def g : U = create_global \"k\" U\n", "can't unify");
    assert_error_parity(
        "def f : U -> U = x => x\ndef g : U = create_global \"k\" f\n",
        "can't unify",
    );
}

/// get_global_default 的 default 位是卡住 prim 头：miss 时原样返回。
/// （default 位的类型是 st2g"m"——卡住 decl 与卡住 decl 的宽松臂只认
/// 同名/字面量，异名 prim 头在类型层先报错；同名 `get_global "m"` 可过。）
#[test]
fn default_value_is_stuck_prim() {
    assert_out(
        "println (get_global_default \"m\" (get_global \"m\"))\n",
        "get_global m\n",
    );
    assert_error_parity(
        "println (get_global_default \"m\" (get_global \"zz\"))\n",
        "can't unify",
    );
}

/// 100 对 create/get 的顺序烟雾（输出顺序 = decl 序）。
#[test]
fn many_globals_smoke() {
    let mut src = String::new();
    let mut expect = String::new();
    for i in 0..100 {
        src.push_str(&format!("def c{i} : U = create_global \"k{i}\" \"v{i}\"\n"));
        src.push_str(&format!("println (get_global \"k{i}\")\n"));
        expect.push_str(&format!("v{i}\n"));
    }
    assert_out(&src, &expect);
}

/// 洞对上 λ 值类型：fresh meta 的类型是 λ 值（不求解、仅打印 ?0）。
#[test]
fn hole_against_lambda_typed_annotation() {
    assert_out(
        "def f : U -> U = x => x\ndef g : string_to_global_type \"f\" = _\nprintln g\n",
        "?0\n",
    );
}

/// LiteralIntro 值当 Π 定义域（st2g 取 String 型 def 的登记值）：λ 本体
/// 可定义可打印（体不触域）；但字面量实参落进 (LiteralType, LiteralIntro)
/// 的无臂比较 → Err（(Lit,·) 家族的推论面）。
#[test]
fn literal_intro_as_pi_domain() {
    assert_out(
        concat!(
            "def s : String = \"a\"\n",
            "def h : string_to_global_type \"s\" -> U = x => U\n",
            "println h\n",
        ),
        "x=> U\n",
    );
    assert_error_parity(
        "def s : String = \"a\"\ndef h : string_to_global_type \"s\" -> U = x => U\nprintln (h \"a\")\n",
        "can't unify",
    );
}

/// 多字节未知名报错路径（ident 词法的 unicode 分支 + Debug 文案）。
#[test]
fn multibyte_unknown_ident_error() {
    assert_error_parity("println 你好\n", "name not in scope");
}

// 陈旧函数部分红ex 回归（L05 fix 65269fb / L07 fix c3af684 的 L06 回灌）
// --------------------------------------------------------------------------------
//
// meta 先被应用进某条 spine 值、随后才被解成多 λ（flex_flex 转发解）时，
// 快版 quote 的链分解（ChainRun bail 的 `prev: Some(prev)` + `Q(fi)`、二叉
// fallback 的 `Q(stack[h].f)`）把该 spine 的「函数部分」单独 force 后引读
// ——它停在**部分应用的闭包**上，重拼 App 即产出 β-红ex 项（修复前快版
// 实测输出混入 `App(Lam("b" …), Var)` = `(b' => ?5 a b') b`；最小复现见
// redex_regression_eq_swapped_args，trace 实测命中 ChainRun bail 位点）；
// 参考版整值 force 经 vAppSp 一路 β，永不产出红ex。修复：两处分解位点在
// 函数部分 force 为闭包（tag 1）时改走 β 语义——按本槽实参求闭包体
// （env_ext + eval_iter）再引应用结果，ChainRun 恢复点以 prev:None 直接
// 取该结果为已累计项（不再拼接）；中性路径（变量/未解 meta）保持原速路。
//
// 判据口径：L06 的 can't unify 文案把项渲染成 Debug 形式且带 Span（快版
// span 全零是文档化偏差，见 assert_error_parity 注），全文比对前先剥掉
// ` @ 行,列` 注记——红ex 的 Lam 节点与 span 无关，剥后两版 Err 文案照旧
// 逐字节可比（本节 oracle 相对 assert_parity 加严：后者对 Err 只比判定，
// 修复前双版同为 Err，抓不住快版文案里混入的红ex）。

/// Church 编码前奏（Eq / refl / the；触发 unification 的标准模式）。
const CHURCH: &str = "def Eq[A : U](x: A, y: A): U = (P : A -> U) -> P x -> P y
def refl[A : U, x: A]: Eq[A] x x = _ => px => px
def the(A : U)(x: A): A = x
";

/// 剥掉 Debug 文案里的 Span 注记（` @ 行,列`）：快版 span 全零是文档化
/// 偏差，剥掉后两版 Err 文案可全文逐字节比对。
fn strip_spans(s: &str) -> String {
    let b = s.as_bytes();
    let mut out: Vec<u8> = Vec::with_capacity(b.len());
    let mut i = 0;
    while i < b.len() {
        if b[i..].starts_with(b" @ ") {
            let mut j = i + 3;
            while j < b.len() && b[j].is_ascii_digit() {
                j += 1;
            }
            if j > i + 3 && j < b.len() && b[j] == b',' {
                let mut k = j + 1;
                while k < b.len() && b[k].is_ascii_digit() {
                    k += 1;
                }
                if k > j + 1 {
                    i = k;
                    continue;
                }
            }
        }
        out.push(b[i]);
        i += 1;
    }
    String::from_utf8_lossy(&out).into_owned()
}

/// 归一化文本：Ok 原样、Err 剥 Span（Err 文案全文比对形态）。
fn normalized_text(r: &Result<String, L06_string::Error>) -> String {
    match r {
        Ok(s) => s.clone(),
        Err(e) => strip_spans(&format!("{e:?}")),
    }
}

/// 全文 parity（加严版）：Ok 原样、Err 剥 Span 后逐字节比对（assert_parity
/// 对 Err 只比判定，抓不住文案分歧）。返回双版归一化文本供钉子续断言。
fn assert_full_text_parity(src: &str) -> (String, String) {
    let b = run_basic(src);
    let f = run_fast(src);
    let (bt, ft) = (normalized_text(&b), normalized_text(&f));
    assert_eq!(
        bt, ft,
        "全文（Err 剥 Span 后）双实现不一致，src:\n{src}\n--- basic ---\n{bt}--- fast ---\n{ft}"
    );
    (bt, ft)
}

/// 看门狗 + 全文 parity（家族批量扫描用；超时/恐慌让测试失败，套件不挂死）。
fn assert_terminates_full_text_parity(src: &str, secs: u64) {
    let input = src.to_owned();
    let (tx, rx) = std::sync::mpsc::channel::<()>();
    let handle = std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            assert_full_text_parity(&input);
            let _ = tx.send(());
        })
        .expect("看门狗线程创建失败");
    if rx
        .recv_timeout(std::time::Duration::from_secs(secs))
        .is_err()
    {
        panic!("输入在 {secs}s 内未终止（疑似挂死/发散）：\n{src}");
    }
    handle.join().unwrap();
}

/// 最小复现（L05/L07 同款输入的 L06 语法移植）：`m1 : [A : U] -> U -> U`
/// 的两个部分应用做 Church-Eq。解 `m1` 的隐式槽时 `?0` 的 spine 里挂了
/// `?5 a b`；随后 `?5` 被 flex_flex 解成**双 λ 转发解**，而引用它的 spine
/// 值（建链早于求解）仍是陈旧位模式。修复前快版报错混入红ex
/// `App(Lam("b" …), Var)`；修复后两版都给干净形态 `?5 a b`。
#[test]
fn redex_regression_eq_swapped_args() {
    let src = format!(
        "{CHURCH}def m1[A : U] : U -> U = _\ndef t = a => b => the (Eq (m1 b) (m1 a)) refl\n"
    );
    let (bt, ft) = assert_full_text_parity(&src);
    // 无红ex 形态（Lam 节点 = `(b' => ?5 a b') b` 的重拼残留）
    assert!(!ft.contains("Lam("), "快版文案混入 β-红ex：{ft}");
    // 干净形态 ?5 a b 钉死（参考版即此形态）
    assert!(
        bt.contains("App(App(Meta(MetaVar(5)), Var(Ix(2)), Expl), Var(Ix(1)), Expl)"),
        "参考版文案缺干净形态 ?5 a b：{bt}"
    );
}

/// 同族镜像：实参顺序互换（`m1 a` vs `m1 b`），失败方向镜像。
#[test]
fn redex_regression_eq_args_order_mirror() {
    let src = format!(
        "{CHURCH}def m1[A : U] : U -> U = _\ndef t = a => b => the (Eq (m1 a) (m1 b)) refl\n"
    );
    let (bt, ft) = assert_full_text_parity(&src);
    assert!(!ft.contains("Lam("), "快版文案混入 β-红ex：{ft}");
    assert!(
        bt.contains("App(App(Meta(MetaVar(5)), Var(Ix(3)), Expl), Var(Ix(2)), Expl)"),
        "参考版文案缺干净形态 ?5 b a：{bt}"
    );
}

/// 同族：`m1` 多一个显式域（P 的定义域带箭头），转发解照旧、红ex 照旧。
#[test]
fn redex_regression_extra_domain() {
    let src = format!(
        "{CHURCH}def m1[A : U] : U -> U -> U = _\ndef t = a => b => the (Eq (m1 b) (m1 a)) refl\n"
    );
    let (bt, ft) = assert_full_text_parity(&src);
    assert!(!ft.contains("Lam("), "快版文案混入 β-红ex：{ft}");
    assert!(
        bt.contains("App(App(Meta(MetaVar(5)), Var(Ix(2)), Expl), Var(Ix(1)), Expl)"),
        "参考版文案缺干净形态 ?5 a b：{bt}"
    );
}

/// 家族批量全文 parity（L05/L07 同款形状网格：6 体 × 3 声明），带看门狗。
/// 覆盖转发解（红ex 位点）、可解 η-intersect、icit 失配、双版本 Ok 等形态。
#[test]
fn redex_family_full_parity_scan() {
    let bodies = [
        "def t = a => b => the (Eq (m1 b) (m1 a)) refl",
        "def t = a => b => the (Eq (m1 a) (m1 b)) refl",
        "def t = a => b => the (Eq (m1 [a] b) (m1 a)) refl",
        "def t = a => b => the (Eq (m1 a b) (m1 b a)) refl",
        "def t = a => b => the (Eq (z => m1 a z) (m1 b)) refl",
        "def t = a => b => the (Eq (m1 [a] [b]) ([z] => m1 [a] [b] [z])) refl",
    ];
    let decls = [
        "def m1[A : U] : U -> U = _",
        "def m1 : U -> U -> U = _",
        "def m1[A : U] : U -> U -> U = _",
    ];
    for d in decls {
        for b in bodies {
            assert_terminates_full_text_parity(&format!("{CHURCH}{d}\n{b}\n"), 60);
        }
    }
}

/// 可解例（Ok 路径对照）：η 展开后经 intersect 剪掉差异槽，方程可解、
/// 程序成功——修复不得影响中性路径的正常引读。
#[test]
fn redex_family_solvable_ok() {
    let src = format!(
        "{CHURCH}def m1 : U -> U -> U = _\ndef t = a => b => the (Eq (m1 a) (z => m1 b z)) refl\nprintln U\n"
    );
    assert_out(&src, "U\n");
    assert_full_text_parity(&src);
}
