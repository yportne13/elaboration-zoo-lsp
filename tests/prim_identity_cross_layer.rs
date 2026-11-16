//! 跨层 prim 语义钉子（2026-11-16，配合 L09–L12 prim 模型改造）。
//!
//! 每个层（参考版 run）都必须满足：
//!   1) 字面量自反：Eq[String] "ab" "ab" = refl                -> Ok
//!   2) 字面量负例：Eq[String] "ab" "cd" = refl                -> Err
//!   3) 卡住 prim 正控：Eq[String] (p x) (p x) = refl（p=string_concat x "a"）-> Ok
//!   4) 卡住 prim 负例：Eq[String] (p x) (q y) = refl             -> Err
//!   5) 部分应用/零应用 builtin 不 panic                          -> Ok
//!
//! L09/L10/L11 在 src/lib.rs 是私有模块，按 tests/gadt_refine_cross_layer_tests.rs
//! 同款用 `#[path]` 编入；L07/L08/L12/L13 走库入口。

#![allow(non_snake_case)]

#[path = "../src/list.rs"]
mod list;
#[path = "../src/bimap.rs"]
mod bimap;
#[path = "../src/parser_lib.rs"]
mod parser_lib;
#[path = "../src/parser_lib_resilient.rs"]
mod parser_lib_resilient;
#[path = "../src/L09_mltt/mod.rs"]
mod L09_mltt;
#[path = "../src/L10_typeclass/mod.rs"]
mod L10_typeclass;
#[path = "../src/L11_macro/mod.rs"]
mod L11_macro;

use elaboration_zoo_lsp::{L07_sum_type, L08_product_type, L12_canonical, L13_namespace};
use std::panic::{catch_unwind, AssertUnwindSafe};

const LIT_OK: &str = r#"
enum Eq[A](x: A, y: A) {
    refl[a: A] -> Eq[A] a a
}

def ok: Eq[String] "ab" "ab" = refl
"#;

const LIT_BAD: &str = r#"
enum Eq[A](x: A, y: A) {
    refl[a: A] -> Eq[A] a a
}

def bad: Eq[String] "ab" "cd" = refl
"#;

const PRIM_CTRL: &str = r#"
enum Eq[A](x: A, y: A) {
    refl[a: A] -> Eq[A] a a
}

def p(x: String): String = string_concat x "a"

def good(x: String): Eq[String] (p x) (p x) = refl
"#;

const PRIM_BAD: &str = r#"
enum Eq[A](x: A, y: A) {
    refl[a: A] -> Eq[A] a a
}

def p(x: String): String = string_concat x "a"

def q(y: String): String = string_concat y "b"

def bad(x: String, y: String): Eq[String] (p x) (q y) = refl
"#;

const PARTIAL: &str = r#"
def f = string_concat "a"
println f
def g = string_concat
println g
"#;

fn is_ok<T: std::fmt::Debug, E: std::fmt::Debug>(f: impl FnOnce() -> Result<T, E>) -> bool {
    matches!(catch_unwind(AssertUnwindSafe(f)), Ok(Ok(_)))
}

fn is_err<T: std::fmt::Debug, E: std::fmt::Debug>(f: impl FnOnce() -> Result<T, E>) -> bool {
    matches!(catch_unwind(AssertUnwindSafe(f)), Ok(Err(_)))
}

macro_rules! check_layer {
    ($layer:literal, $run:path) => {{
        assert!(is_ok(|| $run(LIT_OK, 0)), "{}: literal reflexivity must be Ok", $layer);
        assert!(is_err(|| $run(LIT_BAD, 0)), "{}: distinct literals must be Err", $layer);
        assert!(is_ok(|| $run(PRIM_CTRL, 0)), "{}: stuck prim self-equality must be Ok", $layer);
        assert!(is_err(|| $run(PRIM_BAD, 0)), "{}: distinct stuck prims must be Err", $layer);
        assert!(is_ok(|| $run(PARTIAL, 0)), "{}: partial/zero builtin application must be Ok (no panic)", $layer);
    }};
}

#[test]
fn l07_l13_prim_semantics() {
    check_layer!("L07", L07_sum_type::run);
    check_layer!("L08", L08_product_type::run);
    check_layer!("L09", L09_mltt::run);
    check_layer!("L10", L10_typeclass::run);
    check_layer!("L11", L11_macro::run);
    check_layer!("L12", L12_canonical::run);
    check_layer!("L13", L13_namespace::run);
}
