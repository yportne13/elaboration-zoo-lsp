// ============================================================
// Prim safety regressions（prim 面源码可达路径不 panic）
//
// 修复回归钉（review-l07l12 FIXES D3 P1-4 同族口径，参考版 cxt.rs 与
// 孪生 bump_spine_iter/prim.rs 同步修改）：文件族 IO 内建失败 →
// 卡住降级（None），与"实参非字面量"同口径（L07/L08 的
// v2_file_*_stuck_not_panic 契约）。
// typeclass 求解器 effort 上限的回归钉在 class_tests.rs（就近 Synth 用例）。
// ============================================================

use super::*;

fn run_ok(input: &str) -> String {
    match run_with_prelude(input) {
        Ok(output) => output,
        Err(e) => panic!("expected OK, got error: '{}' @ {}", e.0.data, e.0.start_offset),
    }
}

// ── 文件族 IO：失败卡住降级，不 panic ──

#[test]
fn file_read_missing_println_stays_stuck_not_panic() {
    // println 路径（修复前在 prim 内 panic）：卡住值原样渲染（含 prim 名
    // 与路径实参），后续声明继续求值，进程不崩。
    let out = run_ok(r#"
println (file_read_all_text "l13_prim_safety_missing_file.typort")
println "survived"
"#);
    assert!(out.contains("file_read_all_text"), "stuck prim call must render, got: {}", out);
    assert!(out.contains("survived"), "elaboration must continue after stuck IO, got: {}", out);
}

#[test]
fn file_write_bad_path_is_stuck_not_panic() {
    let out = run_ok(r#"
def w : Type 0 = file_write_all_text "l13_prim_safety_no_such_dir/x.txt" "hi"
println "survived"
"#);
    assert!(out.contains("survived"), "got: {}", out);
}

#[test]
fn file_append_bad_path_is_stuck_not_panic() {
    let out = run_ok(r#"
def a : Type 0 = file_append_all_text "l13_prim_safety_no_such_dir/x.txt" "hi"
println "survived"
"#);
    assert!(out.contains("survived"), "got: {}", out);
}

#[test]
fn file_delete_missing_is_stuck_not_panic() {
    let out = run_ok(r#"
def d : Type 0 = file_delete "l13_prim_safety_missing_file.typort"
println "survived"
"#);
    assert!(out.contains("survived"), "got: {}", out);
}

#[test]
fn file_roundtrip_still_works() {
    // 正常路径行为不变：写 → 读回 → 删 → exists 翻转。
    let out = run_ok(r#"
def w : Type 0 = file_write_all_text "l13_prim_safety_rt.txt" "hello"
def r : String = file_read_all_text "l13_prim_safety_rt.txt"
println r
def d : Type 0 = file_delete "l13_prim_safety_rt.txt"
println (file_exists "l13_prim_safety_rt.txt")
"#);
    assert!(out.contains("hello"), "roundtrip readback, got: {}", out);
    assert!(out.contains("false"), "file deleted, got: {}", out);
}
