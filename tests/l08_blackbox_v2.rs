//! L08_product_type 黑盒测试套件 v2（第二轮独立攻击面）。
//!
//! 与 `tests/l08_blackbox.rs`（47 例，已覆盖核心输出格式、依赖匹配正误路径、
//! 解析位置怪癖、深度边界）互补，本套件聚焦其未触及的角落：
//!   - builtin 注册表全量扫描（string prim / 可变全局族 / 文件 IO 族 /
//!     string_to_global_type 逃逸舱口），含失败 panic 契约；
//!   - enum 冷僻特性：空 enum、显式参数 enum、跨 enum 重名构造子、
//!     隐式子模式 `cons[_]`、命名隐式实参 `[A = Nat]`、限定名引用；
//!   - 类型层 match（`T true ≡ String` 的往返）；
//!   - preprocess 怪癖（臂间注释行、内联枚举单行、未闭合块注释、`--`）；
//!   - run 层契约：Display / std::error::Error、path_id 不变性、并发 run、
//!     跨 run 可变全局隔离、同名 def 重定义、多 println 顺序累积。
//!
//! 唯一黑盒入口：`elaboration_zoo_lsp::L08_product_type::run(input, path_id)
//!   -> Result<String, Error>`；成功输出逐行断言，错误用 `Error` 的
//!   Debug/Display 文本断言，panic 契约用 catch_unwind 断言消息。
//! 全部在 ≥64MB 栈线程内执行。文件 IO 用例持 `FILE_IO_LOCK`。
//!
//! 缺陷与修复状态（2026-09 黑盒二轮）：
//!   F1 [已修] 嵌套 prim / change_mutable 更新链不化简——force 的
//!     Val::Prim 分支现先逐个 force spine 实参再做字面量检查（参考版 +
//!     孪生版同步，与 Val::Obj 先 force 头部的纪律对齐）；本套件按修复
//!     后语义断言（`abc` / `false`，而非卡住渲染）。
//!   F2 [澄清] 跨 enum 重名构造子裸名按「最后注册」解析；限定引用是
//!     **点号**语法 `ColA.red`（注册键 `Enum.case` + Obj 投影特判），
//!     打印才渲染 `::`；`ColA::red` 形式无语法入口（leftover `::`）。
//!   F3 [表征固化] 未解洞编号从 `?1` 起；带剪枝掩码渲染 `?n @k`。
//!   F4 [已修] match 臂分隔符放宽为 `EndLine+`：臂间注释行/空行合法。
//!   F5 [设计限制，见 README] enum 显式参数是**索引**（由构造子返回类型
//!     的特化方程精化），不自动前置为构造子参；需要它作字段 binder 时
//!     由构造子自己再量化（`box1(T : U)(x : T)`）。
//!   F6 [表征固化] 在 U 上应用不 panic，报 can't unify（文档化
//!     「impossible apply」panic 路径实际难以黑盒触达）。
//!
//! 运行：`cargo test --test l08_blackbox_v2`；
//! 格式探针：`cargo test --test l08_blackbox_v2 v2_probe -- --ignored --nocapture`。

use elaboration_zoo_lsp::L08_product_type::{run, FILE_IO_LOCK};

// helpers
// --------------------------------------------------------------------------------

/// 在 64MB 栈线程里跑 `run`；期待成功，失败则 panic 并带出错误与源码。
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

/// 在 64MB 栈线程里跑 `run`；期待 Err，返回 Debug 文本（`Error("...")`）。
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
        .unwrap_or_else(|_| panic!("worker aborted (stack overflow?) for src:\n{src}"))
}

/// 在指定栈大小线程里跑 `run`；返回 Ok/Err/panic 三态文本（探针用）。
fn probe_run(src: &str) -> String {
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run(&input, 0))) {
                Ok(Ok(out)) => format!("OK\n{out}"),
                Ok(Err(e)) => format!("ERR {e:?}"),
                Err(p) => {
                    let m = p
                        .downcast_ref::<&str>()
                        .map(|s| s.to_string())
                        .or_else(|| p.downcast_ref::<String>().cloned())
                        .unwrap_or_else(|| format!("{p:?}"));
                    format!("PANIC {m}")
                }
            }
        })
        .unwrap()
        .join()
        .unwrap_or_else(|_| "STACK-OVERFLOW/ABORT".to_owned())
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

/// 语法错误 → Err(Error("parse error"))（不带定位信息）。
fn assert_parse_err(src: &str) {
    let msg = check_err(src);
    assert_eq!(msg, "Error(\"parse error\")", "src:\n{src}");
}

// 共享前言
// --------------------------------------------------------------------------------

const NAT: &str = r#"
enum Nat {
    zero
    succ(x: Nat)
}
"#;

const VEC: &str = r#"
enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}
"#;

const BOOL: &str = r#"
enum Bool {
    true
    false
}
"#;

const ADD: &str = r#"
def add(x: Nat, y: Nat): Nat =
match x {
case zero => y
case succ(n) => succ (add n y)
}
"#;

// --------------------------------------------------------------------------------
// A. string prim 族
// --------------------------------------------------------------------------------

#[test]
fn v2_str_prim_flat_literals() {
    // 双字面量直接触发；str_eq 输出也是字符串字面量 "true"/"false"。
    assert_lines(
        r#"
println (string_concat "ab" "cd")
println (str_eq "foo" "foo")
println (str_eq "foo" "bar")
println (string_concat "" "x")
println (string_concat "x" "")
println (str_eq "" "")
"#,
        &["abcd", "true", "false", "x", "x", "true"],
    );
}

#[test]
fn v2_str_prim_via_decl_indirection() {
    // 实参是经 force 展开成字面量的全局 def：可以触发（DEMO 同款路径）。
    assert_lines(
        r#"
def a = "f"
def b = "oo"
def cc : String = string_concat a b
println cc
println (str_eq cc "foo")
println (str_eq cc "bar")
"#,
        &["foo", "true", "false"],
    );
}

#[test]
fn v2_nested_prim_reduces() {
    // F1 回归：实参是嵌套 prim 应用时，读点 force 先归约实参再检查字面量，
    // prim 链恢复可组合性（修复前卡在 `string_concat ab c` / `str_eq foo foo`）。
    assert_lines(
        r#"
def n1 : String = string_concat (string_concat "a" "b") "c"
def n2 : String = str_eq "foo" (string_concat "f" "oo")
def n3 : String = str_eq "abc" n1
println n1
println n2
println n3
"#,
        &["abc", "true", "true"],
    );
}

#[test]
fn v2_str_prim_eta_and_stuck_print() {
    // 部分应用打印成 η 展开的 λ；含变量实参的 prim 卡住、渲染无引号。
    assert_lines(
        r#"
println string_concat
def h : String -> String = s => string_concat "a" s
println h
"#,
        &["x => y => string_concat x y", "s => string_concat a s"],
    );
}

#[test]
fn v2_str_indent_and_multiline_output() {
    // \n 真换行；println 输出跨行。str_indent2 只缩进第 2 行起（首行不缩）。
    assert_lines(
        "\nprintln (str_indent2 \"a\\nb\\nc\")\nprintln \"l1\\nl2\"\nprintln \"tab\\there\"\n",
        &["a", "  b", "  c", "l1", "l2", "tab\there"],
    );
}

#[test]
fn v2_string_escape_set() {
    // 已知转义还原；未知转义原样保留 `\c`（词法文档行为）。
    assert_lines(
        "\nprintln \"\\a\\q\\z\"\nprintln \"back\\\\slash\"\nprintln \"q\\\"r\"\n",
        &["\\a\\q\\z", "back\\slash", "q\"r"],
    );
}

// --------------------------------------------------------------------------------
// B. 可变全局族
// --------------------------------------------------------------------------------

#[test]
fn v2_globals_lifecycle() {
    assert_lines(
        r#"
def d0 : String = get_global_default "k" "init"
println d0
def c1 : U = create_global "k" "v1"
println (get_global "k")
def u1 : U = change_mutable "k" (s => string_concat s "!")
println (get_global "k")
def u2 : U = change_mutable "k" (s => s)
println (get_global "k")
def u3 : U = change_mutable_default "fresh" (s => s) "seed"
println (get_global "fresh")
println (get_global_default "k" "fallback")
"#,
        &["init", "v1", "v1!", "v1!", "seed", "v1!"],
    );
}

#[test]
fn v2_named_update_fn_composes() {
    // 单步更新走具名函数同样正确化简（F1 只在**链式**二次更新暴露：
    // 第一次存的未 force Prim 值成为第二次的实参）。
    assert_lines(
        r#"
def bang (s : String) : String = string_concat s "!"
def c : U = create_global "k" "hi"
def u : U = change_mutable "k" bang
println (get_global "k")
"#,
        &["hi!"],
    );
}

#[test]
fn v2_mutable_update_chain_reduces() {
    // F1 回归（同根因）：连续 change_mutable 存的未 force `f old`，读点
    // 现在整链化简（修复前输出 `string_concat ab c`）。
    assert_lines(
        r#"
def c : U = create_global "k" "a"
def u1 : U = change_mutable "k" (s => string_concat s "b")
def u2 : U = change_mutable "k" (s => string_concat s "c")
println (get_global "k")
def c2 : U = create_global "m" "a"
def u3 : U = change_mutable "m" (s => string_concat "z" s)
println (get_global "m")
"#,
        &["abc", "za"],
    );
}

#[test]
fn v2_get_global_absent_stuck_not_panic() {
    // 缺名 get_global 不 panic、不报错：保持卡住 prim（渲染 `get_global <名>`），
    // 且能通过 String 类型检查（st2g 未登记名 → Decl 逃逸舱口 + 宽松合一）。
    assert_lines(
        r#"
def gg : String = get_global "nope_missing"
println gg
"#,
        &["get_global nope_missing"],
    );
}

#[test]
fn v2_change_mutable_absent_silent_noop() {
    assert_lines(
        r#"
def u1 : U = change_mutable "ghost" (x => x)
println (get_global_default "ghost" "still-absent")
"#,
        &["still-absent"],
    );
}

#[test]
fn v2_report_check_issue_dedup_and_skip() {
    // 重复行去重；code 或 module 为空静默跳过（返回 U 不写入）。
    assert_lines(
        r#"
def a1 : U = report_check_issue "E1" "m" "s" "msg1"
def a2 : U = report_check_issue "E1" "m" "s" "msg1"
def a3 : U = report_check_issue "E2" "m" "s" "msg2"
def b1 : U = report_check_issue "" "m" "s" "no-code"
def b2 : U = report_check_issue "c" "" "s" "no-module"
def g : String = get_global "CheckIssues"
println g
"#,
        &["E1|m|s|msg1", "E2|m|s|msg2"],
    );
}

#[test]
fn v2_mutable_state_isolated_across_runs() {
    // 每次 run 全新 mutable_map：第一个 run 写入的 key 对第二个 run 不可见。
    let writer = r#"
def c : U = create_global "l07v2_key" "payload"
def r : U = report_check_issue "X" "y" "z" "w"
"#;
    let reader = r#"
println (get_global_default "l07v2_key" "clean")
println (get_global_default "CheckIssues" "clean")
"#;
    check(writer);
    assert_lines(reader, &["clean", "clean"]);
}

// --------------------------------------------------------------------------------
// C. 文件 IO 族（panic 契约 + 正常往返）
// --------------------------------------------------------------------------------

#[test]
fn v2_file_write_read_exists_delete_roundtrip() {
    let _io = FILE_IO_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let out = check(
        r#"
println (file_exists "l07_v2_bb_rt.txt")
def w : U = file_write_all_text "l07_v2_bb_rt.txt" "hello"
println (file_exists "l07_v2_bb_rt.txt")
println (file_read_all_text "l07_v2_bb_rt.txt")
def a : U = file_append_all_text "l07_v2_bb_rt.txt" "!!"
println (file_read_all_text "l07_v2_bb_rt.txt")
def d : U = file_delete "l07_v2_bb_rt.txt"
println (file_exists "l07_v2_bb_rt.txt")
"#,
    );
    let _ = std::fs::remove_file("l07_v2_bb_rt.txt");
    let got: Vec<&str> = out.lines().collect();
    assert_eq!(
        got,
        &["false", "true", "hello", "hello!!", "false"],
        "out:\n{out}"
    );
}

#[test]
fn v2_file_append_creates_new() {
    let _io = FILE_IO_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let src = r#"
def a : U = file_append_all_text "l07_v2_bb_new.txt" "x"
println (file_read_all_text "l07_v2_bb_new.txt")
def d : U = file_delete "l07_v2_bb_new.txt"
"#;
    let out = check(src);
    let _ = std::fs::remove_file("l07_v2_bb_new.txt");
    assert_eq!(out, "x\n");
}

#[test]
fn v2_file_read_missing_panics() {
    let _io = FILE_IO_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let msg = check_panic(r#"
def r : String = file_read_all_text "l07_v2_bb_no_such.txt"
"#)
    .expect("file_read_all_text on missing path must panic");
    assert!(msg.contains("file_read_all_text: failed to read"), "panic msg: {msg}");
    assert!(msg.contains("l07_v2_bb_no_such.txt"), "panic msg: {msg}");
}

#[test]
fn v2_file_delete_missing_panics() {
    let _io = FILE_IO_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let msg = check_panic(r#"
def d : U = file_delete "l07_v2_bb_no_such_zzz.txt"
"#)
    .expect("file_delete on missing path must panic");
    assert!(msg.contains("file_delete: failed to delete"), "panic msg: {msg}");
}

#[test]
fn v2_file_write_bad_path_panics() {
    let _io = FILE_IO_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let msg = check_panic(r#"
def w : U = file_write_all_text "l07_v2_bb_no_dir/sub.txt" "x"
"#)
    .expect("file_write_all_text into missing dir must panic");
    assert!(msg.contains("file_write_all_text: failed to write"), "panic msg: {msg}");
}

#[test]
fn v2_file_side_effects_fire_at_def_registration() {
    // 副作用在顶层 def 登记（force 到 WHNF）时按声明序触发：println 里不出现
    // U 结果行；写→读必须分在两个 def 才看到文件内容。
    let _io = FILE_IO_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let src = r#"
def w : U = file_write_all_text "l07_v2_bb_order.txt" "1st"
def r : String = file_read_all_text "l07_v2_bb_order.txt"
println r
"#;
    let out = check(src);
    let _ = std::fs::remove_file("l07_v2_bb_order.txt");
    assert_eq!(out, "1st\n");
}

// --------------------------------------------------------------------------------
// D. string_to_global_type 与逃逸舱口
// --------------------------------------------------------------------------------

#[test]
fn v2_st2g_registered_names() {
    // 已登记名给登记**类型**：def 给 Π 链、类型/字面量类型给 U。
    assert_lines(
        &format!(
            "{NAT}\ndef myf : Nat -> Nat = x => x\ndef t1 = string_to_global_type \"myf\"\ndef t2 = string_to_global_type \"Nat\"\ndef t3 = string_to_global_type \"String\"\nprintln t1\nprintln t2\nprintln t3\n"
        ),
        &["Nat → Nat", "U", "U"],
    );
}

#[test]
fn v2_st2g_unregistered_escapes_as_name() {
    // 未登记名 → 以该名逃出的卡住 Decl（动态类型舱口）；打印就是名字本身。
    assert_lines(
        r#"
def t = string_to_global_type "bogus_name"
println t
"#,
        &["bogus_name"],
    );
}

#[test]
fn v2_st2g_type_hatch_passes_check() {
    // 舱口值参与类型位置：`get_global "bogus2"` 的类型是逃逸 Decl，
    // check 字面量实参时靠宽松臂放行（不报 can't unify）。
    assert_lines(
        r#"
def c : U = create_global "bogus2" "hi"
def g : String = get_global "bogus2"
println g
"#,
        &["hi"],
    );
}

// --------------------------------------------------------------------------------
// E. enum 冷僻特性
// --------------------------------------------------------------------------------

#[test]
fn v2_enum_empty_rejected() {
    // 构造子列表 many1：空 enum 解析失败（Void 无法声明）。
    assert_parse_err("\nenum Void {\n}\n");
}

#[test]
fn v2_enum_inline_rejected() {
    // 构造子必须换行分隔：单行 `{ red green }` 解析失败。
    assert_parse_err("\nenum ColA { red green }\n");
}

#[test]
fn v2_dup_ctor_last_wins_with_dotted_disambiguation() {
    // 跨 enum 重名构造子：裸名静默取最后注册者；限定引用用**点号**
    // `ColA.red`（Obj 投影特判 + `Enum.case` 注册键），可稳定消歧。
    assert_lines(
        r#"
enum ColA {
red
green
}

enum ColB {
red
blue
}

def x : ColA = ColA.red
def y : ColB = ColB.red
println red
println x
println y
"#,
        &["ColB::red", "ColA::red", "ColB::red"],
    );
}

#[test]
fn v2_print_only_double_colon_unparsable() {
    // 打印用 `::`（如 ColA::red），但引用语法只有点号：`::` 是独立
    // token、无语法入口——读写格式不对称，值得留意。
    assert_err("\nenum ColA {\nred\n}\ndef x : ColA = ColA::red\n", "leftover token");
}

#[test]
fn v2_enum_explicit_param_requires_requantify() {
    // 构造子字段/返回类型引用的显式参数，必须由构造子自己再量化（表征 F5：
    // `enum Box1(T : U) { box1(x : T) ... }` 直接报 name not in scope: T）。
    assert_lines(
        &format!(
            "{NAT}\nenum Box1(T : U) {{\nbox1(T : U)(x : T) -> Box1 T\n}}\ndef b = box1 Nat zero\nprintln b\n"
        ),
        &["Box1::box1(Nat Nat::zero)"],
    );
    assert_err(
        &format!(
            "{NAT}\nenum Box1(T : U) {{\nbox1(x : T) -> Box1 T\n}}\ndef b = box1[Nat] zero\n"
        ),
        "name not in scope: T",
    );
}

#[test]
fn v2_named_implicit_instance() {
    // 命名隐式实参 `[A = Nat]` 与位置隐式 `[Nat]` 等义；裸 `nil` η 成 `[A] => ...`。
    assert_lines(
        &format!("{NAT}{VEC}\nprintln nil\nprintln nil[Nat]\nprintln nil[A = Nat]\n"),
        &["[A] => Vec::nil", "Vec::nil", "Vec::nil"],
    );
}

#[test]
fn v2_print_type_values() {
    // 类型作为一等值打印：Sum 名与字面量类型名原样。
    assert_lines(
        &format!("{NAT}\nprintln Nat\nprintln String\nprintln U\n"),
        &["Nat", "String", "U"],
    );
}

// --------------------------------------------------------------------------------
// F. match / 依赖精化 / 洞
// --------------------------------------------------------------------------------

#[test]
fn v2_typelevel_match_roundtrip() {
    // 类型层 match：`T true ≡ String`、`T false ≡ Nat`，可作期望类型往返。
    assert_lines(
        &format!(
            "{NAT}{BOOL}\ndef T(b : Bool) : U =\nmatch b {{\ncase true => String\ncase false => Nat\n}}\ndef the(A : U)(x : A) : A = x\nprintln (the (T true) \"abc\")\ndef u2 : T false = succ zero\nprintln u2\n"
        ),
        &["abc", "Nat::succ(Nat::zero)"],
    );
}

#[test]
fn v2_coverage_error_lists_all_missing() {
    // 零臂 match：全部构造子一次报全，多错误以 \n 连接。
    assert_err(
        &format!("{NAT}{BOOL}\ndef f(x : Bool) : Nat =\nmatch x {{\n}}\n"),
        r"缺少构造子 true\nmatch 不完整：缺少构造子 false",
    );
}

#[test]
fn v2_gadt_impossible_arm_rejected() {
    // Vec[Nat] zero 上写 cons 臂：特化方程 zero ≡ succ l 结构冲突 →
    // 「分支不可达」拒绝（报错含 Rust Debug 形式的模式——诊断渲染待打磨）。
    let msg = check_err(
        &format!("{NAT}{VEC}\ndef f(v : Vec[Nat] zero) : Nat =\nmatch v {{\ncase nil => zero\ncase cons(_, _) => zero\n}}\n"),
    );
    assert!(msg.contains("分支不可达"), "err: {msg}");
    assert!(msg.contains("cons"), "err: {msg}");
}

#[test]
fn v2_implicit_subpattern_pruning() {
    // 隐式子模式 `cons[_]`：显式给出隐式参数槽的通配。
    assert_lines(
        &format!(
            "{NAT}{VEC}\ndef hd2[A, n : Nat](v : Vec[A] (succ n)) : A =\nmatch v {{\ncase cons[_](x, _) => x\n}}\nprintln (hd2 (cons[Nat][zero] zero nil))\n"
        ),
        &["Nat::zero"],
    );
}

#[test]
fn v2_stuck_match_rendering() {
    // 卡住 match 是头等中性值：λ 头 + 分支体各自 nf 后按 `; ` 串起。
    assert_lines(
        &format!("{NAT}\ndef f(x: Nat): Nat =\nmatch x {{\ncase zero => succ zero\ncase succ(n) => n\n}}\nprintln f\n"),
        &["x => match x { case zero => succ zero; case succ(n) => n }"],
    );
}

#[test]
fn v2_match_scrutinee_expression() {
    // scrutinee 是复合表达式：运行时具体值走实臂；函数值打印时保持卡住。
    let src = format!("{NAT}{ADD}\ndef f(x: Nat, y: Nat): Nat =\nmatch add x y {{\ncase zero => succ zero\ncase succ(k) => k\n}}\nprintln (f zero zero)\nprintln (f (succ zero) zero)\n");
    let out = check(&src);
    let mut it = out.lines();
    assert_eq!(it.next(), Some("Nat::succ(Nat::zero)"));
    assert_eq!(it.next(), Some("Nat::zero"));
}

#[test]
fn v2_projection_on_variable_and_call() {
    // `v.len` 在体内卡住（渲染 `v.len`），应用到具体 vec 后化简为索引值。
    assert_lines(
        &format!("{NAT}{VEC}\ndef pl[A, n : Nat](v : Vec[A] n) : Nat = v.len\nprintln pl\nprintln (pl[Nat] nil)\nprintln (pl[Nat] (cons zero nil))\n"),
        &[
            "[A] => [n] => v => v.len",
            "Nat::zero",
            "Nat::succ(Nat::zero)",
        ],
    );
}

#[test]
fn v2_hole_numbering_and_paren_mask() {
    // 表征（F3）：顶层洞从 ?1 起；带剪枝掩码的洞打印 `?n @k`；
    // 递归 def 的分支体里递归调用以**原名**打印（quote 防重展开）。
    let out = check(&format!("{NAT}{ADD}\nprintln _\n"));
    assert_eq!(out.lines().next(), Some("?1"));
    let out2 = check(&format!("{NAT}{ADD}\ndef m1 = _ => _\nprintln m1\n"));
    let l = out2.lines().nth(0).unwrap();
    assert!(l.starts_with("_ => ?") && l.ends_with(" @0"), "hole-with-mask render: {l}");
    let out3 = check(&format!("{NAT}{ADD}\nprintln (add _ zero)\n"));
    let l3 = out3.lines().next().unwrap();
    assert!(
        l3.starts_with("match ?") && l3.contains("case succ(n) => succ (add n Nat::zero)"),
        "stuck meta scrutinee: {l3}"
    );
}

#[test]
fn v2_tree_nested_pattern_and_recursion() {
    // 树上的嵌套构造子模式（非索引族）+ 自递归 size。
    assert_lines(
        &format!(
            "{NAT}{ADD}\nenum Tree {{\nleaf\nnode(l: Tree, r: Tree)\n}}\ndef size(t : Tree) : Nat =\nmatch t {{\ncase leaf => succ zero\ncase node(l, r) => add (size l) (size r)\n}}\nprintln (size (node (node leaf leaf) leaf))\nprintln (size leaf)\n"
        ),
        &["Nat::succ(Nat::succ(Nat::succ(Nat::zero)))", "Nat::succ(Nat::zero)"],
    );
}

// --------------------------------------------------------------------------------
// G. 解析 / 预处理怪癖
// --------------------------------------------------------------------------------

#[test]
fn v2_blank_and_comment_lines_between_arms_ok() {
    // F4 回归：臂间注释行（剥成空行后连续两个 EndLine）与显式空行、
    // 行尾同行注释一律合法。修复前臂间注释行导致整个 def 残余 token。
    assert_lines(
        &format!("{NAT}\ndef f(x : Nat) : Nat =\nmatch x {{\ncase zero => succ zero // tail\n\n// cmt between arms\n\ncase succ(n) => n\n}}\nprintln (f zero)\nprintln (f (succ (succ zero)))\n"),
        &["Nat::succ(Nat::zero)", "Nat::succ(Nat::zero)"],
    );
}

#[test]
fn v2_dashdash_is_not_comment() {
    // `--` 是独立 token（非注释），报错带定位。
    let msg = check_err(&format!("{NAT}\n-- old comment\nprintln zero\n"));
    assert!(msg.contains("parse error"), "err: {msg}");
    assert!(msg.contains("`--`"), "err should locate the token: {msg}");
}

#[test]
fn v2_block_comment_variants() {
    // 跨行块注释在 decl 之间安全；项内 `succ /*c*/ zero` 安全；未闭合剥到 EOF。
    assert_lines(
        &format!("{NAT}\n/* block\n   spanning */\nprintln zero\n"),
        &["Nat::zero"],
    );
    assert_lines(
        &format!("{NAT}\nprintln (succ /* mid */ zero)\n"),
        &["Nat::succ(Nat::zero)"],
    );
    assert_lines(
        "\nprintln \"a\"\n/* unterminated".to_owned().as_str(),
        &["a"],
    );
}

#[test]
fn v2_let_in_term_forms() {
    // let 可省略类型标注（默认洞）；仅项内合法。
    assert_lines(
        &format!(
            "{NAT}\ndef x : Nat = let y : Nat = succ zero; succ y\ndef z : Nat = let w = succ (succ zero); w\nprintln x\nprintln z\n"
        ),
        &[
            "Nat::succ(Nat::succ(Nat::zero))",
            "Nat::succ(Nat::succ(Nat::zero))",
        ],
    );
}

// --------------------------------------------------------------------------------
// H. run 层契约 / 类型系统边界
// --------------------------------------------------------------------------------

#[test]
fn v2_no_println_returns_empty() {
    assert_eq!(check(&format!("{NAT}\ndef a = zero\n")), "");
}

#[test]
fn v2_multi_println_accumulates_in_order() {
    assert_lines(
        &format!("{NAT}\nprintln zero\ndef d = succ zero\nprintln d\nprintln \"mid\"\nprintln (succ d)\n"),
        &["Nat::zero", "Nat::succ(Nat::zero)", "mid", "Nat::succ(Nat::succ(Nat::zero))"],
    );
}

#[test]
fn v2_error_truncates_whole_program() {
    // 中途出错：已积累的 println 输出一并作废（不产出部分结果）。
    assert_err(
        &format!("{NAT}\nprintln zero\ndef bad : Nat = \"str\"\nprintln bad\n"),
        "can't unify",
    );
}

#[test]
fn v2_type_mismatch_literal_vs_sum() {
    assert_err(&format!("{NAT}\ndef bad : Nat = \"x\"\n"), "can't unify");
}

#[test]
fn v2_find_f6_apply_u_is_unify_error() {
    // 表征（F6）：`U zero` 不 panic「impossible apply」，而是合一失败 Err。
    assert_err(&format!("{NAT}\ndef bad : U = U zero\n"), "can't unify");
}

#[test]
fn v2_same_name_def_last_wins() {
    assert_lines(
        &format!("{NAT}\ndef a : Nat = zero\ndef a : Nat = succ zero\nprintln a\n"),
        &["Nat::succ(Nat::zero)"],
    );
}

#[test]
fn v2_path_id_invariance() {
    let src = format!("{NAT}{VEC}\nprintln (cons[Nat][zero] zero nil)\n");
    let a = {
        let s = src.clone();
        std::thread::spawn(move || run(&s, 0)).join().unwrap().unwrap()
    };
    let b = {
        let s = src.clone();
        std::thread::spawn(move || run(&s, 42)).join().unwrap().unwrap()
    };
    assert_eq!(a, b);
}

#[test]
fn v2_concurrent_runs_independent() {
    // run 内部状态（Infer/mutable_map/fuel）不跨调用共享：并发双跑结果一致。
    let src = format!(
        "{NAT}\ndef c : U = create_global \"shared_key\" \"mine\"\nprintln (get_global \"shared_key\")\n"
    );
    let mut handles = Vec::new();
    for _ in 0..2 {
        let s = src.clone();
        handles.push(
            std::thread::Builder::new()
                .stack_size(64 * 1024 * 1024)
                .spawn(move || run(&s, 0))
                .unwrap(),
        );
    }
    for h in handles {
        assert_eq!(h.join().unwrap().unwrap(), "mine\n");
    }
}

#[test]
fn v2_error_display_and_std_error_trait() {
    // Error 对外不可解构，但 Display 给内部消息、且实现 std::error::Error。
    let e = run(&format!("{NAT}\ndef bad : Nat = succ \"x\"\n"), 0).unwrap_err();
    let disp = format!("{e}");
    assert!(disp.contains("can't unify"), "Display: {disp}");
    let dynref: &dyn std::error::Error = &e;
    assert_eq!(dynref.to_string(), disp);
}

// --------------------------------------------------------------------------------
// I. 格式探针（保留：行为变更时重跑对账）
// --------------------------------------------------------------------------------

#[test]
#[ignore]
fn v2_probe_formats() {
    let _io = FILE_IO_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let probes: Vec<(&str, String)> = vec![
        (
            "meta_print",
            format!("{NAT}{ADD}\nprintln _\ndef m1 = _ => _\nprintln m1\nprintln (add _ zero)\n"),
        ),
        (
            "st2g_print",
            format!("{NAT}\ndef f : Nat -> Nat = x => x\nprintln (string_to_global_type \"f\")\nprintln (string_to_global_type \"Nat\")\n"),
        ),
        (
            "prim_eta",
            "\nprintln string_concat\nprintln str_eq\nprintln get_global\n".to_owned(),
        ),
        (
            "dup_ctor",
            "\nenum ColA {\nred\ngreen\n}\n\nenum ColB {\nred\nblue\n}\n\nprintln red\n".to_owned(),
        ),
        (
            "qual_dotted",
            "
enum ColA {
red
green
}

enum ColB {
red
blue
}

def x : ColA = ColA.red
def y : ColB = ColB.red
println x
println y
".to_owned(),
        ),
        (
            "match_scrut_expr",
            format!("{NAT}{ADD}\ndef f(x: Nat, y: Nat): Nat =\nmatch add x y {{\ncase zero => succ zero\ncase succ(k) => k\n}}\nprintln f\n"),
        ),
    ];
    for (name, src) in probes {
        println!("=====PROBE {name}=====");
        println!("{}", probe_run(&src));
    }
}

#[test]
#[ignore]
fn v2_probe_change_mutable() {
    let probes: Vec<(&str, String)> = vec![
        (
            "identity_update",
            "\ndef c : U = create_global \"k\" \"v1\"\ndef u : U = change_mutable \"k\" (s => s)\nprintln (get_global \"k\")\n".to_owned(),
        ),
        (
            "named_fn_update",
            "\ndef bang (s : String) : String = string_concat s \"!\"\ndef c : U = create_global \"k\" \"hi\"\ndef u : U = change_mutable \"k\" bang\nprintln (get_global \"k\")\n".to_owned(),
        ),
        (
            "demo_greeting",
            "\ndef store1 : U = create_global \"greeting\" \"hi\"\ndef upd1 : U = change_mutable \"greeting\" (s => string_concat s \"!\")\ndef g1 : String = get_global \"greeting\"\nprintln g1\n".to_owned(),
        ),
        (
            "double_update",
            "\ndef c : U = create_global \"k\" \"a\"\ndef u1 : U = change_mutable \"k\" (s => string_concat s \"b\")\ndef u2 : U = change_mutable \"k\" (s => string_concat s \"c\")\nprintln (get_global \"k\")\n".to_owned(),
        ),
        (
            "get_after_stuck_update",
            "\ndef c : U = create_global \"k\" \"a\"\ndef u : U = change_mutable \"k\" (s => string_concat s \"b\")\nprintln u\n".to_owned(),
        ),
        (
            "chained_lit_arg",
            "\ndef c : U = create_global \"k\" \"a\"\ndef u : U = change_mutable \"k\" (s => string_concat \"z\" s)\nprintln (get_global \"k\")\n".to_owned(),
        ),
    ];
    for (name, src) in probes {
        println!("=====PROBE-CM {name}=====");
        println!("{}", probe_run(&src));
    }
}
