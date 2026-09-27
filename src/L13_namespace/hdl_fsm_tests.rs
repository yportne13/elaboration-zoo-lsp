// ============================================================
// HDL FSM DSL tests (docs/hdl-stream-fsm-design.md §7, phase 1)
//
// Pins the phase-1 FSM surface (hdl-fsm.typort):
//   - fsmNew expansion: stateReg(init 0) + stateNext wire + default-first
//     regAssign (§7.3 expected Verilog, adapted for the when(1)-wrapped
//     default — see the doc deviation notes on HDL011/D5)
//   - whenIsActive / goto / onEntry / onExit / whenIsNext / isActive /
//     isState落树形状 (macro brace form + method lambda form)
//   - HDL060-064 trigger and non-trigger cases (§7.4 / §11.6)
//   - multiple FSMs per module (§7.5)
//   - out-of-module FsmCtx use degrades without panic
// ============================================================

use super::*;

fn assert_ok(input: &str) -> String {
    match run_with_prelude(input) {
        Ok(output) => output,
        Err(e) => panic!("expected OK, got error: '{}' @ {}:{}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

// ── §7.2/§7.3/§11.6 acceptance: the fsmDemo shape (macro brace form) ──
// sDone gets noExitCheck() so the demo is check-clean (its missing goto is
// exercised as the HDL062 trigger below).

#[test]
fn fsm_acceptance_demo_verilog() {
    let output = assert_ok(r#"
module fsmDemo {
    input start = Bool
    input finish = Bool
    output done = Bool
    output st = UInt[2]
    output isRun = Bool
    let ctrl = fsmNew[2](4)
    let sIdle = ctrl.state(0)
    let sRun = ctrl.state(1)
    let sDone = ctrl.state(2)
    sDone.noExitCheck()
    whenIsActive(sIdle) {
        when start { sRun.goto() }
    }
    whenIsActive(sRun) {
        when finish { sDone.goto() } otherwise { sIdle.goto() }
    }
    whenIsActive(sDone) {
        done := true
    }
    onEntry(sDone) { done := true }
    onExit(sIdle) { done := false }
    st := ctrl.stateReg
    isRun := sRun.isActive
}
println(moduleTreeVL(fsmDemo.create.tree))
"#);
    // state register + next wire, both 2-bit regs (stateNext is when-driven)
    assert!(output.contains("reg [1:0] ctrl_stateReg;"), "stateReg decl, got:\n{}", output);
    assert!(output.contains("reg [1:0] ctrl_stateNext;"), "stateNext decl, got:\n{}", output);
    // clocked chain + async reset to state 0 (entry state = reset state)
    assert!(
        output.contains("always @(posedge clk or posedge reset) begin"),
        "clocked always header, got:\n{}", output
    );
    assert!(output.contains("if (reset) begin"), "reset branch, got:\n{}", output);
    assert!(output.contains("ctrl_stateReg <= 0;"), "reset init to entry state, got:\n{}", output);
    assert!(
        output.contains("ctrl_stateReg <= ctrl_stateNext;"),
        "clock edge regAssign, got:\n{}", output
    );
    // merged combinational always with the default FIRST (insertion order).
    // Documented fallback shape (docs/hdl-stream-fsm-design.md §7.3): phase 1
    // cannot take the HDL011/D5 refinement route (hdl-check is outside the
    // phase-1 ownership), so fsmNew wraps the default in when(1) — codegen
    // emits `if (1) begin <default> end`, and the HDL011 rule counts it as a
    // conditional drive. The default must still precede every goto if.
    assert!(output.contains("always @(*) begin"), "comb always, got:\n{}", output);
    let always = output.find("always @(*) begin").expect("comb always missing");
    assert!(
        output.contains("if (1) begin\n      ctrl_stateNext = ctrl_stateReg;\n    end"),
        "when(1)-wrapped default (documented fallback), got:\n{}", output
    );
    let default_line = output[always..].find("ctrl_stateNext = ctrl_stateReg;").expect("default drive missing") + always;
    let first_goto = output[always..].find("ctrl_stateNext = 2'd1;").expect("first goto missing") + always;
    assert!(default_line > always && default_line < first_goto, "default must precede the goto ifs, got:\n{}", output);
    // transfers: guards conjoined with the state compare, sized goto literals.
    // Condition composition order is the engine's (WhenStack folds the inner
    // user condition outermost: `<user cond> && (<state cmp>)`) — see the
    // design doc's §7.7 deviation note (measured 2026-09-27).
    assert!(
        output.contains("if (start && (ctrl_stateReg == 0)) begin"),
        "sIdle + start guard, got:\n{}", output
    );
    assert!(output.contains("ctrl_stateNext = 2'd1;"), "goto 1 sized literal, got:\n{}", output);
    assert!(
        output.contains("if (finish && (ctrl_stateReg == 1)) begin"),
        "sRun + finish guard, got:\n{}", output
    );
    assert!(output.contains("ctrl_stateNext = 2'd2;"), "goto 2 sized literal, got:\n{}", output);
    assert!(
        output.contains("if (!finish && (ctrl_stateReg == 1)) begin"),
        "otherwise-branch guard, got:\n{}", output
    );
    assert!(output.contains("ctrl_stateNext = 2'd0;"), "goto 0 sized literal, got:\n{}", output);
    // sDone body + onEntry/onExit hooks
    assert!(output.contains("if (ctrl_stateReg == 2) begin"), "sDone body guard, got:\n{}", output);
    assert!(output.contains("done = 1;"), "done set, got:\n{}", output);
    assert!(
        output.contains("if ((ctrl_stateNext == 2) && (ctrl_stateReg != 2)) begin"),
        "onEntry guard, got:\n{}", output
    );
    assert!(
        output.contains("if ((ctrl_stateNext != 0) && (ctrl_stateReg == 0)) begin"),
        "onExit guard, got:\n{}", output
    );
    assert!(output.contains("done = 0;"), "onExit clears done, got:\n{}", output);
    // combinational queries
    assert!(output.contains("assign st = ctrl_stateReg;"), "stateReg passthrough, got:\n{}", output);
    assert!(output.contains("assign isRun = (ctrl_stateReg == 1);"), "isActive query, got:\n{}", output);
    // §11.6 regression: FSM modules must NOT raise HDL011 (D5 not needed with
    // the when(1)-wrapped default) and the clean demo raises no FSM checks
    // (HDL063 is reserved: entry is always state 0 in phase 1).
    assert!(!output.contains("HDL011"), "no HDL011 on FSM modules, got:\n{}", output);
    assert!(!output.contains("HDL06"), "clean FSM must not warn HDL060-064, got:\n{}", output);
}

// ── method + lambda form: same conditions, same tree shape ──
// ENGINE DEVIATION (2026-09-27, measured): the BARE apply-block lambda form
//   sB.whenIsActive { u => ... }
// fails inside the class body with `find unsolved meta with type `Type 0``
// (the for-hdl-blocker family, docs/for-hdl-blocker.md). Watchdog-isolated
// variants, all failing the same way: bare block, `let _ = <bare block>`,
// block with a let-chain body, block with a simple body, block with an
// explicitly typed `(u: Unit)` parameter. Working equivalents: the paren
// lambda `sB.whenIsActive(u => ...)` and the PARENTHESIZED block lambda
// `sB.whenIsActive({ u => ... })` — both really defer (body runs inside the
// when context). The bare form is pinned by the #[ignore]d test below with
// the minimal repro; it is an engine-side apply-block/lambda defect, not
// reachable from hdl-fsm.typort.

#[test]
fn fsm_method_lambda_form() {
    let output = assert_ok(r#"
module fsmMethodForm {
    input go = Bool
    output st = UInt[2]
    let ctrl = fsmNew[2](2)
    let sA = ctrl.state(0)
    let sB = ctrl.state(1)
    sA.whenIsActive(u => when go { sB.goto() })
    sB.whenIsActive({ u => when go { sA.goto() } })
    st := ctrl.stateReg
}
println(moduleTreeVL(fsmMethodForm.create.tree))
"#);
    assert!(
        output.contains("if (go && (ctrl_stateReg == 0)) begin"),
        "paren-lambda whenIsActive guard, got:\n{}", output
    );
    assert!(
        output.contains("if (go && (ctrl_stateReg == 1)) begin"),
        "block-lambda whenIsActive guard, got:\n{}", output
    );
    assert!(output.contains("ctrl_stateNext = 2'd1;"), "goto 1, got:\n{}", output);
    assert!(output.contains("ctrl_stateNext = 2'd0;"), "goto 0, got:\n{}", output);
    assert!(!output.contains("HDL06"), "0->1->0 ring is check-clean, got:\n{}", output);
}

// ── engine limitation pin: bare apply-block lambda method call ──
// Ignored because the ENGINE cannot elaborate the shape inside a module
// class body (see the deviation note above fsm_method_lambda_form). Minimal
// repro (fails with `find unsolved meta with type `Type 0``):
//
//   module m { let ctrl = fsmNew[1](2); let s0 = ctrl.state(0)
//              let s1 = ctrl.state(1)
//              s0.whenIsActive { u => when go { s1.goto() } } }
//
// All of these fail identically (watchdog-measured):
//   s0.whenIsActive { u => ... }            (bare block)
//   let _ = s0.whenIsActive { u => ... }    (let-bound bare block)
//   s0.whenIsActive { u => s1.goto() }      (trivial lambda body)
//   s0.whenIsActive { (u: Unit) => ... }    (typed parameter)
// while `s0.whenIsActive(u => ...)` and `s0.whenIsActive({ u => ... })`
// work. The defect lives in the parser/elaborator's apply-block handling
// (same family as docs/for-hdl-blocker.md's recovery-Hole meta leak), not
// in hdl-fsm.typort. Un-ignore when the engine handles it.
#[test]
#[ignore = "engine: bare apply-block lambda argument -> find unsolved meta (docs/for-hdl-blocker.md family)"]
fn fsm_method_bare_apply_block_engine_bug() {
    let output = assert_ok(r#"
module fsmBareBlock {
    input go = Bool
    output st = UInt[1]
    let ctrl = fsmNew[1](2)
    let sA = ctrl.state(0)
    let sB = ctrl.state(1)
    sA.whenIsActive { u => when go { sB.goto() } }
    sB.noExitCheck()
    st := ctrl.stateReg
}
println(moduleTreeVL(fsmBareBlock.create.tree))
"#);
    assert!(output.contains("ctrl_stateNext = 1'd1;"), "bare-block lambda transfer, got:\n{}", output);
}

// ── whenIsNext / isState: next-state view + Nat comparison query ──

#[test]
fn fsm_when_is_next_and_is_state() {
    let output = assert_ok(r#"
module fsmNextView {
    input go = Bool
    output led = Bool
    output busy = Bool
    let ctrl = fsmNew[1](2)
    let sIdle = ctrl.state(0)
    let sRun = ctrl.state(1)
    whenIsActive(sIdle) {
        when go { sRun.goto() }
    }
    sRun.noExitCheck()
    whenIsNext(sIdle) { led := true }
    busy := ctrl.isState(1)
}
println(moduleTreeVL(fsmNextView.create.tree))
"#);
    assert!(
        output.contains("if (ctrl_stateNext == 0) begin"),
        "whenIsNext guard on stateNext, got:\n{}", output
    );
    assert!(output.contains("led = 1;"), "whenIsNext body, got:\n{}", output);
    assert!(output.contains("assign busy = (ctrl_stateReg == 1);"), "isState query, got:\n{}", output);
    assert!(!output.contains("HDL06"), "clean FSM must not warn, got:\n{}", output);
}

// ── §7.5: two FSMs in one module, independent names and records ──

#[test]
fn fsm_two_per_module() {
    let output = assert_ok(r#"
module fsmTwo {
    input a = Bool
    input b = Bool
    output sa = UInt[1]
    output sb = UInt[1]
    let ctrlA = fsmNew[1](2)
    let ctrlB = fsmNew[1](2)
    let aIdle = ctrlA.state(0)
    let aRun = ctrlA.state(1)
    let bIdle = ctrlB.state(0)
    let bRun = ctrlB.state(1)
    whenIsActive(aIdle) {
        when a { aRun.goto() }
    }
    whenIsActive(aRun) {
        when a { aIdle.goto() }
    }
    whenIsActive(bIdle) {
        when b { bRun.goto() }
    }
    whenIsActive(bRun) {
        when b { bIdle.goto() }
    }
    sa := ctrlA.stateReg
    sb := ctrlB.stateReg
}
println(moduleTreeVL(fsmTwo.create.tree))
"#);
    assert!(output.contains("ctrlA_stateReg"), "FSM A registers, got:\n{}", output);
    assert!(output.contains("ctrlB_stateReg"), "FSM B registers, got:\n{}", output);
    // fsmNew[1] = 1-bit encoding (w is the explicit encoding width)
    assert!(output.contains("ctrlA_stateNext = 1'd1;"), "FSM A transfer, got:\n{}", output);
    assert!(output.contains("ctrlB_stateNext = 1'd1;"), "FSM B transfer, got:\n{}", output);
    assert!(!output.contains("HDL06"), "two clean FSMs must not warn, got:\n{}", output);
}

// ── HDL060: goto target >= stateCount ──

#[test]
fn hdl060_goto_out_of_range() {
    let output = assert_ok(r#"
module fsmHdl060 {
    input fire = Bool
    let ctrl = fsmNew[2](4)
    let sIdle = ctrl.state(0)
    let sBad = ctrl.state(4)
    whenIsActive(sIdle) {
        when fire { sBad.goto() }
    }
}
println(moduleTreeVL(fsmHdl060.create.tree))
"#);
    assert!(output.contains("HDL060"), "out-of-range goto must warn, got:\n{}", output);
    assert!(
        output.contains("goto target 4 out of range (stateCount = 4)"),
        "HDL060 must name target and stateCount, got:\n{}", output
    );
    assert!(output.contains("fsmHdl060"), "HDL060 must carry the module name, got:\n{}", output);
}

// ── HDL060 non-trigger: target == stateCount - 1 is the last legal state ──

#[test]
fn hdl060_boundary_target_ok() {
    let output = assert_ok(r#"
module fsmHdl060ok {
    input fire = Bool
    let ctrl = fsmNew[2](2)
    let sIdle = ctrl.state(0)
    let sEnd = ctrl.state(1)
    whenIsActive(sIdle) {
        when fire { sEnd.goto() }
    }
    sEnd.noExitCheck()
}
println(moduleTreeVL(fsmHdl060ok.create.tree))
"#);
    assert!(!output.contains("HDL060"), "target 1 < 2 is legal, got:\n{}", output);
    assert!(!output.contains("HDL06"), "no FSM warnings expected, got:\n{}", output);
}

// ── HDL061: declared states no goto targets (state 0 reachable by reset) ──

#[test]
fn hdl061_unreachable_states() {
    let output = assert_ok(r#"
module fsmHdl061 {
    input go = Bool
    let ctrl = fsmNew[2](4)
    let sIdle = ctrl.state(0)
    let sRun = ctrl.state(1)
    let sWait = ctrl.state(2)
    let sErr = ctrl.state(3)
    whenIsActive(sIdle) {
        when go { sRun.goto() }
    }
    whenIsActive(sRun) {
        when go { sIdle.goto() }
    }
    whenIsActive(sWait) {
        sWait.noExitCheck()
    }
}
println(moduleTreeVL(fsmHdl061.create.tree))
"#);
    assert!(output.contains("HDL061"), "unreachable states must warn, got:\n{}", output);
    assert!(
        output.contains("state 2 is unreachable"),
        "state 2 must be named, got:\n{}", output
    );
    assert!(
        output.contains("state 3 is unreachable"),
        "state 3 must be named, got:\n{}", output
    );
    assert_eq!(
        output.matches("HDL061").count(),
        2,
        "exactly states 2 and 3 are unreachable, got:\n{}", output
    );
    // sWait's empty-of-goto body is exempted (noExitCheck) — no HDL062 here.
    assert!(!output.contains("HDL062"), "exempted state must not warn HDL062, got:\n{}", output);
}

// ── HDL061 non-trigger: every declared state gets a goto target ──
// (covered by fsm_acceptance_demo_verilog's clean assertion)

// ── HDL062: state body without any goto (may get stuck) + the cure ──

#[test]
fn hdl062_state_without_exit() {
    let output = assert_ok(r#"
module fsmHdl062 {
    input fire = Bool
    let ctrl = fsmNew[1](2)
    let sIdle = ctrl.state(0)
    let sEnd = ctrl.state(1)
    whenIsActive(sIdle) {
        when fire { sEnd.goto() }
    }
    whenIsActive(sEnd) { }
}
println(moduleTreeVL(fsmHdl062.create.tree))
"#);
    assert!(output.contains("HDL062"), "exit-less active state must warn, got:\n{}", output);
    assert!(
        output.contains("state 1 has no outgoing goto"),
        "HDL062 must name the state, got:\n{}", output
    );
    assert!(output.contains("fsmHdl062"), "HDL062 must carry the module name, got:\n{}", output);
    assert!(!output.contains("HDL061"), "both states are targeted, got:\n{}", output);
}

#[test]
fn hdl062_no_exit_check_cures() {
    let output = assert_ok(r#"
module fsmHdl062ok {
    input fire = Bool
    let ctrl = fsmNew[1](2)
    let sIdle = ctrl.state(0)
    let sEnd = ctrl.state(1)
    whenIsActive(sIdle) {
        when fire { sEnd.goto() }
    }
    whenIsActive(sEnd) { }
    sEnd.noExitCheck()
}
println(moduleTreeVL(fsmHdl062ok.create.tree))
"#);
    // noExitCheck() written AFTER the state body must still exempt it
    // (HDL062 is decided at drain time, not at pop time).
    assert!(!output.contains("HDL062"), "noExitCheck must cure HDL062, got:\n{}", output);
    assert!(!output.contains("HDL06"), "no FSM warnings expected, got:\n{}", output);
}

// ── HDL063 is reserved (phase-1 entry state is always 0) ──
// A normal FSM never reports it; pinned by the clean assertions in
// fsm_acceptance_demo_verilog / fsm_method_lambda_form (no "HDL06" at all).

// ── HDL064: goto outside any whenIsActive context ──

#[test]
fn hdl064_bare_goto_outside_context() {
    let output = assert_ok(r#"
module fsmHdl064 {
    input go = Bool
    let ctrl = fsmNew[2](2)
    let sIdle = ctrl.state(0)
    let sRun = ctrl.state(1)
    whenIsActive(sIdle) {
        when go { sRun.goto() }
    }
    when go { ctrl.goto(0) }
}
println(moduleTreeVL(fsmHdl064.create.tree))
"#);
    assert!(output.contains("HDL064"), "context-less goto must warn, got:\n{}", output);
    assert!(
        output.contains("goto outside any whenIsActive state context"),
        "HDL064 message, got:\n{}", output
    );
    assert!(output.contains("fsmHdl064"), "HDL064 must carry the module name, got:\n{}", output);
    // the transition itself still lands in the tree under the user's when
    assert!(
        output.contains("if (go) begin") && output.contains("ctrl_stateNext = 2'd0;"),
        "bare goto still emits under the enclosing when, got:\n{}", output
    );
    // inside whenIsActive the same goto does NOT warn (non-trigger)
    assert!(!output.contains("HDL060"), "target 0 is in range, got:\n{}", output);
}

// ── HDL064 ordering coverage (fixed 2026-09-27 review): a bare goto BEFORE
// the first whenIsActive or BETWEEN two whenIsActive blocks used to be a
// blind spot — fsmCtxPush cleared the flag evidence, so only a bare goto
// AFTER the LAST whenIsActive was reported. The fix adds an accumulating
// oocTargets channel: a bare goto never records an edge, so at drain its
// target stays uncovered and reports, while an in-context goto's
// check-pass pre-eval artifact is always covered by the edge the same goto
// records in the real pass (hdl-fsm.typort, fsmGotoLog CHECK-PASS note).
// The probe targets state 2, which no in-context goto targets.

#[test]
fn hdl064_bare_goto_before_first_when_is_active() {
    let output = assert_ok(r#"
module fsmHdl064First {
    input go = Bool
    let ctrl = fsmNew[2](3)
    let sIdle = ctrl.state(0)
    let sRun = ctrl.state(1)
    let sErr = ctrl.state(2)
    when go { ctrl.goto(2) }
    whenIsActive(sIdle) {
        when go { sRun.goto() }
    }
    whenIsActive(sRun) {
        when go { sIdle.goto() }
    }
}
println(moduleTreeVL(fsmHdl064First.create.tree))
"#);
    assert!(
        output.contains("HDL064"),
        "bare goto before the first whenIsActive must warn, got:\n{}", output
    );
    assert!(
        output.contains("goto outside any whenIsActive state context"),
        "HDL064 message, got:\n{}", output
    );
    assert!(output.contains("fsmHdl064First"), "HDL064 must carry the module name, got:\n{}", output);
}

#[test]
fn hdl064_bare_goto_between_when_is_active() {
    let output = assert_ok(r#"
module fsmHdl064Mid {
    input go = Bool
    let ctrl = fsmNew[2](3)
    let sIdle = ctrl.state(0)
    let sRun = ctrl.state(1)
    let sErr = ctrl.state(2)
    whenIsActive(sIdle) {
        when go { sRun.goto() }
    }
    when go { ctrl.goto(2) }
    whenIsActive(sRun) {
        when go { sIdle.goto() }
    }
}
println(moduleTreeVL(fsmHdl064Mid.create.tree))
"#);
    assert!(
        output.contains("HDL064"),
        "bare goto between two whenIsActive blocks must warn, got:\n{}", output
    );
    assert!(
        output.contains("goto outside any whenIsActive state context"),
        "HDL064 message, got:\n{}", output
    );
}

// ── HDL064 residual blind spot, PINNED as expected behavior: a bare goto
// whose target is ALSO goto-targeted in-context by the same Fsm stays
// silent before/between whenIsActive blocks — its record mutations are
// identical to the engine's check-pass pre-eval artifact of the in-context
// goto, so the drain's edge-coverage check suppresses it. Documented in
// hdl-fsm.typort (fsmGotoLog CHECK-PASS note) and the design doc §7.7;
// mitigation: put bare gotos at the end of the module body (the flag
// channel then reports regardless of target, as
// hdl064_bare_goto_outside_context pins). If this test ever fails, the
// engine gained a way to distinguish the two — widen the rule.

#[test]
fn hdl064_blind_spot_covered_target_bare_goto_stays_silent() {
    let output = assert_ok(r#"
module fsmHdl064Covered {
    input go = Bool
    let ctrl = fsmNew[2](2)
    let sIdle = ctrl.state(0)
    let sRun = ctrl.state(1)
    when go { ctrl.goto(1) }
    whenIsActive(sIdle) {
        when go { sRun.goto() }
    }
    whenIsActive(sRun) {
        when go { sIdle.goto() }
    }
}
println(moduleTreeVL(fsmHdl064Covered.create.tree))
"#);
    assert!(
        !output.contains("HDL064"),
        "covered-target bare goto before whenIsActive is the documented blind spot, got:\n{}", output
    );
    // the in-context edges themselves are clean
    assert!(!output.contains("HDL061"), "both states are targeted, got:\n{}", output);
}

// ── HDL064 boundary case: a FULLY bare goto at module top level is an
// unconditional comb drive on stateNext — it co-fires HDL011 (uncond + cond
// mix). This pins the documented boundary of the design's D5 fallback: the
// when(1) wrapper keeps the DEFAULT drive off HDL011, but a user-emitted
// unconditional goto is a genuine uncond drive (and HDL064 flags it as a
// user error anyway).

#[test]
fn hdl064_fully_bare_goto_boundary() {
    let output = assert_ok(r#"
module fsmHdl064bare {
    input go = Bool
    let ctrl = fsmNew[2](2)
    let sIdle = ctrl.state(0)
    let sRun = ctrl.state(1)
    whenIsActive(sIdle) {
        when go { sRun.goto() }
    }
    let _bare = ctrl.goto(1)
}
println(moduleTreeVL(fsmHdl064bare.create.tree))
"#);
    assert!(output.contains("HDL064"), "bare goto must warn HDL064, got:\n{}", output);
    assert!(
        output.contains("HDL011"),
        "unconditional goto is an uncond comb drive (documented boundary), got:\n{}", output
    );
}

// ── out-of-module FsmCtx use: no panic, reports degrade silently ──
// The def body is evaluated at declaration-check time OUTSIDE any module:
// the ModuleTree global is absent (tree writes no-op) and the HDL064 report
// carries an empty module name (report_check_issue drops it).

#[test]
fn fsm_out_of_module_fallback_no_panic() {
    let output = assert_ok(r#"
def fsmOutsideProbe(): Unit =
    let sm = fsmNew[2](4);
    let s1 = sm.state(1);
    let _g = s1.goto();
    unit
println("fsm-fallback-ok")
"#);
    assert!(output.contains("fsm-fallback-ok"), "no panic outside a module, got:\n{}", output);
    assert!(!output.contains("HDL06"), "empty module name must not report, got:\n{}", output);
}
