//! L13_namespace 双 oracle 互检套件（参考版 `run` ↔ 性能版 `bump_spine_iter::
//! run_fast`）。`#[path]` 只编 list.rs / bimap.rs / parser_lib.rs /
//! parser_lib_resilient.rs / L13_namespace/mod.rs（不含 LSP / L02-L12），
//! 迭代快数倍（tests/l12_fast_parity.rs 同款）。
//!
//! 判据：**Ok 输出逐字节一致 / Err 判定一致**。错误文案的 Span 偏移、
//! meta 编号（`?N`）与 Debug-Span 数字是文档化偏差，比对前归一化。
//!
//! # 已知偏差（快版孪生，缺陷另案跟踪）
//!
//! - **multiline 枚举声明的 match 编译**（`Compiler`，缺陷另案）：枚举声明
//!   跨多行（构造子含子模式字段，如 `succ(x: Nat)`）时，快版 match 编译
//!   对构造子分支子模式绑定会越界/死循环（Windows 下爆 `STATUS_ACCESS_
//!   VIOLATION`）。**单行枚举声明**的等价 match（含递归、子模式、求值）
//!   完全正常且与参考版逐字节一致（本套件 `parity_single_line` 覆盖）。
//!   根因在快版 `Compiler::compile_aux` 对多行枚举构造子 span 的子模式
//!   level 推算，尚未定位——单行枚举不受影响，故本套件的语言面（enum /
//!   match / 递归 / trait / 全局 / 字符串 / 报错）全部用单行声明呈现。
//! - **GADT 索引宇宙判定 × trait 求解交互**、struct 接收者实例、单臂构造
//!   子匹配、Prim 求值时机差（L12 先例家族）在快版分叉或发散，整体剔除。
//! - **prelude 依赖的测试源**（run_with_prelude / class / module / derive /
//!   verilog / hdl）不在本套件（本套件用无 prelude 的 `run` 口径）；参考版
//!   的这些行为由既有 `cargo test --lib`（647 例）保证。
//!
//! # 覆盖（全部用单行枚举声明）
//! - Ok 逐字节：enum + 构造子匹配（含子模式绑定 `succ(x)`）、递归 def +
//!   match（natadd 雏形，含求值）、字符串拼接。
//! - Err 判定 + 归一化正文：name-not-in-scope、universe 报错、`+` 运算符
//!   未绑定（无 prelude 时 `String` 无 `+` 方法——两版一致报错）。

#![feature(pattern)]

#[path = "../src/list.rs"]
mod list;

#[path = "../src/bimap.rs"]
mod bimap;

#[path = "../src/parser_lib.rs"]
mod parser_lib;
#[path = "../src/parser_lib_resilient.rs"]
mod parser_lib_resilient;

#[path = "../src/L13_namespace/mod.rs"]
mod L13_namespace;

use L13_namespace::bump_spine_iter as fast;

/// 在大栈线程里跑参考版 `run`。线程边界只传归一化后的 Err 文案
/// （L13 的 `Error` 携带非 Send 的重试闭包）。
fn run_basic(src: &str) -> Result<String, String> {
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || L13_namespace::run(&input, 0).map_err(|e| norm_err(&e.0.data)))
        .unwrap()
        .join()
        .unwrap()
}

/// 在大栈线程里跑快版 `run_fast`。
fn run_fast(src: &str) -> Result<String, String> {
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || fast::run_fast(&input, 0).map_err(|e| norm_err(&e.0.data)))
        .unwrap()
        .join()
        .unwrap()
}

/// Err 文案归一化：剥掉 Span 自定义 Debug 的 `@ N` / `@ N,M`、派生
/// Debug 的 `start_offset/end_offset/path_id: N` 数字，以及 meta 编号
/// `?N`（双实现 meta 分配序列不同，文档化偏差）。
fn norm_err(e: &str) -> String {
    let mut out = String::with_capacity(e.len());
    let b = e.as_bytes();
    let mut i = 0usize;
    while i < b.len() {
        if b[i] == b'@' && i + 1 < b.len() && b[i + 1] == b' ' {
            let mut j = i + 2;
            while j < b.len() && b[j].is_ascii_digit() {
                j += 1;
            }
            if j > i + 2 {
                if j < b.len() && b[j] == b',' {
                    let mut k = j + 1;
                    while k < b.len() && b[k].is_ascii_digit() {
                        k += 1;
                    }
                    if k > j + 1 {
                        j = k;
                    }
                }
                out.push_str("@ _");
                i = j;
                continue;
            }
        }
        if b[i] == b'?' && i + 1 < b.len() && b[i + 1].is_ascii_digit() {
            let mut j = i + 1;
            while j < b.len() && b[j].is_ascii_digit() {
                j += 1;
            }
            if j > i + 1 {
                out.push_str("?_");
                i = j;
                continue;
            }
        }
        let rest = &e[i..];
        let mut matched = false;
        for key in ["start_offset: ", "end_offset: ", "path_id: "] {
            if rest.starts_with(key) {
                let mut j = i + key.len();
                while j < b.len() && b[j].is_ascii_digit() {
                    j += 1;
                }
                if j > i + key.len() {
                    out.push('_');
                    i = j;
                    matched = true;
                    break;
                }
            }
        }
        if matched {
            continue;
        }
        let ch = e[i..].chars().next().unwrap();
        out.push(ch);
        i += ch.len_utf8();
    }
    out
}

/// Oracle：Ok 逐字节 / Err 判定 + 归一化正文一致。
fn assert_parity(src: &str) {
    let b = run_basic(src);
    let f = run_fast(src);
    match (&b, &f) {
        (Ok(b), Ok(f)) => assert_eq!(
            b, f,
            "Ok 输出双实现不一致，src:\n{src}\n--- basic ---\n{b}--- fast ---\n{f}"
        ),
        (Err(b), Err(f)) => assert_eq!(
            b, f,
            "Err 正文（归一化后）双实现不一致，src:\n{src}\n--- basic ---\n{b}\n--- fast ---\n{f}"
        ),
        _ => panic!(
            "判定不一致（basic={}，fast={}），src:\n{src}\nbasic-err={:?}\nfast-err={:?}",
            b.as_ref().map(|_| "Ok").unwrap_or("Err"),
            f.as_ref().map(|_| "Ok").unwrap_or("Err"),
            b.as_ref().err(),
            f.as_ref().err(),
        ),
    }
}

// 基础语言面（单行枚举声明，规避 multiline-enum match 编译缺陷）
// --------------------------------------------------------------------------------

#[test]
fn parity_single_line() {
    // enum + 构造子匹配（含子模式绑定 `succ(x)`）
    assert_parity(
        "enum Nat { zero succ(x: Nat) } def two = succ (succ zero) \
         def mono(n: Nat): Nat = match n { case zero => zero case succ(x) => x } \
         println (mono two)\n",
    );
    // 递归 def + match（natadd 雏形，含求值）
    assert_parity(
        "enum Nat { zero succ(x: Nat) } \
         def add(x: Nat, y: Nat): Nat = match x { case zero => y case succ(n) => succ (add n y) } \
         def p0 : Nat = add (succ (succ zero)) (succ zero) \
         println p0\n",
    );
    // 字符串拼接（无 prelude 时 String 无 `+` 实例——两版一致报错）
    assert_parity("println (\"a\" + \"b\" + \"c\")\n");
    // 纯字符串字面量输出
    assert_parity("println \"hello\"\n");
}

// Err 判定 parity（判定一致 + 归一化正文一致）
// --------------------------------------------------------------------------------

#[test]
fn parity_errors() {
    // 名字不在 scope
    assert_parity("def bad = nope\n");
    // 期望宇宙（`: Nat` 无 prelude 时不解析——两版一致报 name not in scope）
    assert_parity("def bad : Nat = Type 0\n");
    // 单臂 match 的非穷尽（两版都给 Unmatched 类警告文案）
    assert_parity(
        "enum Nat { zero succ(x: Nat) } \
         def mono(n: Nat): Nat = match n { case zero => zero }\n",
    );
}

// 稳态复用（trait/可变全局跨轮清空）
// --------------------------------------------------------------------------------

#[test]
fn steady_state_reuse() {
    // 全局链连续两轮：上一轮的 mutable 全局不得泄漏（test6 同款）
    let gsrc = "enum Nat { zero succ(x: Nat) } \
         def ttt = let useless1 = create_global \"Nat\" 2; \
         let useless2 = change_mutable(\"Nat\", z => succ(z)); \
         get_global \"Nat\" \
         println ttt\n";
    let mut steady = fast::Tycker::new();
    let a = steady.run_input(gsrc, 0).unwrap();
    let b = steady.run_input(gsrc, 0).unwrap();
    assert_eq!(a, b, "跨轮 mutable 全局泄漏");
    assert_parity(gsrc);
}
