// ============================================================
// prelude HDL A tests (owner: hdl-a, task-3)
//
// 本模块钉住 hdl-core / hdl-check / hdl-check-graph / hdl-types / hdl-ops
// 的修补与关键约定；文档承诺的行为也在这里落成断言。
// 写法参照 hdl_check_graph_tests.rs 与 prelude_stdlib_tests.rs。
//
// 覆盖的修补（task-3 一致性审计）：
//   1. HDL034 的检测范围：只报「同选择器异值 eq 项」形态，裸信号 p && !p
//      形态**故意不报**（与 WHENSTACK 重放残留叶层面不可区分）。
//      依据：docs/hdl-selfcheck-phase234-design.md §11.5 / §11.12、
//      docs/hdl-selfcheck-design.md:109；
//      源码：hdl-check-graph.typort 的 ruleDeadCond 与它上方被修正的段注释
//      （旧注释错误地宣称 "contains p and !p"）。
//   2. 入口反转：模块宏的 _res 走 checkModuleTreeAll（hdl-check-graph），
//      它在同一轮里先跑 runChecks（阶段 1：HDL001-004/010-013/020-025），
//      再跑阶段 2-4 图规则（HDL032-042）。hdl-check.typort 的
//      checkModuleTree 已无调用者，只作为回滚路径保留。
//      依据：hdl-check.typort 文件头（本轮修正）；hdl-macros.typort 的四处
//      _res 调用点。
// ============================================================

use super::*;

fn assert_ok(input: &str) -> String {
    match run_with_prelude(input) {
        Ok(output) => output,
        Err(e) => panic!(
            "expected OK, got error: '{}' @ {}:{}",
            e.0.data, e.0.path_id, e.0.start_offset
        ),
    }
}

// ── HDL034 范围（正例）：同选择器异值 eq 项必报 ──

#[test]
fn hdl034_eq_term_form_reported() {
    let output = assert_ok(
        r#"
module eqTermDead {
    input sel = UInt[2]
    input a = UInt[4]
    output q = UInt[4]
    let s = UInt[4]
    when (sel == 0) && (sel == 1) {
        s := a
    }
    q := s
}
println(moduleTreeVL(eqTermDead.create.tree))
"#,
    );
    assert!(
        output.contains("HDL034"),
        "同一驱动条件把 sel 约束成两个不同常量属于恒假，必须报 HDL034，got:\n{}",
        output
    );
    assert!(
        output.contains("driver condition is always false"),
        "HDL034 报文固定为 'driver condition is always false'（不带裸叶形态的括注），got:\n{}",
        output
    );
}

// ── HDL034 范围（负例 / 回归钉）：裸信号 p && !p 故意不报 ──

#[test]
fn hdl034_bare_leaf_form_silent() {
    let output = assert_ok(
        r#"
module bareLeafDead {
    input sel = UInt[2]
    input a = UInt[4]
    output q = UInt[4]
    let s = UInt[4]
    let c = (sel == 0)
    when c && !c {
        s := a
    }
    q := s
}
println(moduleTreeVL(bareLeafDead.create.tree))
"#,
    );
    assert!(
        !output.contains("HDL034"),
        "裸信号 p && !p 形态在叶层面与 WHENSTACK 重放残留（!en && en）不可区分，\
         为避免 latchOk/loopExempt 类模块的必然误报，HDL034 故意不报它\
         （phase234 §11.5）；若此断言失败，说明检测范围被悄悄放宽，got:\n{}",
        output
    );
    // 同一个残缺覆盖仍然要被 HDL032 抓住——静默不等于「无条件豁免」。
    assert!(
        output.contains("HDL032"),
        "裸叶恒假驱动仍是「无默认的分支覆盖」，HDL032 必须照报，got:\n{}",
        output
    );
}

// ── 入口反转：阶段 1 与阶段 2-4 规则在同一轮里都跑 ──
//
// 一个模块同时含：阶段 1 的 HDL003（output 从未被驱动）与阶段 2-4 的
// HDL032（推断 latch）。两者同时出现即证明 live entry 是
// checkModuleTreeAll（它先调 runChecks 再跑图规则），而不是只跑阶段 1 的
// hdl-check.typort::checkModuleTree。

#[test]
fn check_entry_runs_phase1_and_graph_rules_in_one_pass() {
    let output = assert_ok(
        r#"
module liveEntry {
    input sel = UInt[2]
    input a = UInt[4]
    output q = UInt[4]
    output r = UInt[4]
    when (sel == 0) {
        r := a
    }
}
println(moduleTreeVL(liveEntry.create.tree))
"#,
    );
    assert!(
        output.contains("HDL003"),
        "阶段 1 的 HDL003（undriven output）必须跑，got:\n{}",
        output
    );
    assert!(
        output.contains("HDL032"),
        "阶段 2-4 的 HDL032（inferred latch）必须在同一轮里跑，got:\n{}",
        output
    );
}