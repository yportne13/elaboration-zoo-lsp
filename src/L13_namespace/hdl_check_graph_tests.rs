// ============================================================
// HDL self-check graph tests — phases 2-4 (HDL030-039)
//
// Pins docs/hdl-selfcheck-phase234-design.md §9 acceptance cases:
//   §9.1/§9.2 comb loops (HDL030/031, mutual-exclusion exemption)
//   §9.3   latch / coverage / bit ranges / dead + shadowed conditions
//   §9.4   CDC (domain propagation, 2FF chains, multi-bit)
// plus non-trigger twins for every rule.
//
// Warnings drain into run_with_prelude's output string (same channel as
// the phase-1 tests in legacy_tests.rs) — assertions are contains-style.
// ============================================================

use super::*;

fn assert_ok(input: &str) -> String {
    match run_with_prelude(input) {
        Ok(output) => output,
        Err(e) => panic!("expected OK, got error: '{}' @ {}:{}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

// ── §9.1: true combinational loop ──

#[test]
fn hdl030_comb_loop() {
    let output = assert_ok(r#"
module combLoop {
    input en = Bool
    output ao = Bool
    output bo = Bool
    let a = Bool
    let b = Bool
    a := b && en
    b := !a
    ao := a
    bo := b
}
println(moduleTreeVL(combLoop.create.tree))
"#);
    assert!(output.contains("HDL030"), "comb loop must warn HDL030, got:\n{}", output);
    assert!(
        output.contains("combinational loop: a -> b -> a"),
        "loop path a -> b -> a expected, got:\n{}", output
    );
    assert!(!output.contains("HDL031"), "in-module loop must not be HDL031, got:\n{}", output);
}

// ── §9.1: single-node self loop ──

#[test]
fn hdl030_self_loop() {
    let output = assert_ok(r#"
module selfLoop {
    input d = UInt[8]
    output q = UInt[8]
    let t = UInt[8]
    t := t + 1
    q := t
}
println(moduleTreeVL(selfLoop.create.tree))
"#);
    assert!(output.contains("HDL030"), "self loop must warn HDL030, got:\n{}", output);
    assert!(
        output.contains("combinational loop: t -> t"),
        "self loop path expected, got:\n{}", output
    );
}

// ── §9.2: mutually exclusive conditions exempt the ring ──
// a <- b (sel) and b <- a (!sel): the ring's edge conditions are
// syntactically contradictory -> no HDL030. Also T2-complete -> no HDL032.

#[test]
fn hdl030_loop_exempt_by_mutex() {
    let output = assert_ok(r#"
module loopExempt {
    input sel = Bool
    input x = UInt[8]
    input y = UInt[8]
    output ao = UInt[8]
    output bo = UInt[8]
    let a = UInt[8]
    let b = UInt[8]
    when sel {
        a := b
    } otherwise {
        a := x
    }
    when sel {
        b := y
    } otherwise {
        b := a
    }
    ao := a
    bo := b
}
println(moduleTreeVL(loopExempt.create.tree))
"#);
    assert!(!output.contains("HDL030"), "mutex ring must be exempt, got:\n{}", output);
    assert!(!output.contains("HDL032"), "T2-complete drivers must not warn HDL032, got:\n{}", output);
    assert!(!output.contains("[hdl][warning]"), "zero warnings expected, got:\n{}", output);
}

// ── §9.2 (review probe 2 shape, per-cycle exemption pin): a TRUE feedback
// ring and a mux hold ring share one SCC. The hold edge x -> x (under !c) is
// mutually exclusive with the read edge x -> y (under c), but those two
// edges never belong to one simple cycle — the old SCC-level shortcut
// exempted the whole SCC on that pair and went silent on the real ring.
// The per-cycle judgment must report x -> y -> x (and the hold self-ring
// x -> x stays a reportable self-loop too).
#[test]
fn hdl030_true_ring_survives_hold_ring_mutex() {
    let output = assert_ok(r#"
module holdMix {
    input c = Bool
    input en = Bool
    output xo = Bool
    output yo = Bool
    let x = Bool
    let y = Bool
    when c {
        x := y
    } otherwise {
        x := x
    }
    y := x && en
    xo := x
    yo := y
}
println(moduleTreeVL(holdMix.create.tree))
"#);
    assert!(output.contains("HDL030"), "true ring must warn HDL030, got:\n{}", output);
    assert!(
        output.contains("combinational loop: x -> y -> x"),
        "true ring x -> y -> x expected, got:\n{}", output
    );
    assert!(
        output.contains("combinational loop: x -> x"),
        "hold self-ring x -> x is separately reportable, got:\n{}", output
    );
}

// ── §9.2: mux feedback hold form — the when branch feeds the signal back to
// itself, the otherwise branch feeds fresh data. The hold edge is a real
// combinational self-loop (HDL030 y -> y): "keep current value" without a
// register is hardware, not an exemption.
#[test]
fn hdl030_mux_hold_self_loop() {
    let output = assert_ok(r#"
module muxHold {
    input sel = Bool
    input d = UInt[8]
    output qo = UInt[8]
    let y = UInt[8]
    when sel {
        y := y
    } otherwise {
        y := d
    }
    qo := y
}
println(moduleTreeVL(muxHold.create.tree))
"#);
    assert!(output.contains("HDL030"), "mux hold feedback must warn HDL030, got:\n{}", output);
    assert!(
        output.contains("combinational loop: y -> y"),
        "hold self-loop y -> y expected, got:\n{}", output
    );
}

// ── §9.2: cross-hierarchy loop through a combinational child passthrough ──
// NOTE (engine fact, deviation from the design's §9.2 snippet): the child's
// ports MUST be declared in the module HEADER (before `{`). Ports declared
// inside the body are module-internal signals with no subSignal handle
// (hdl-macros.typort module-macro docs) — `u.port := x` on them does not
// form a connection, so no cross-layer edge can exist for that shape.

#[test]
fn hdl031_cross_hierarchy_loop() {
    let output = assert_ok(r#"
module passthru
    input pin = Bool
    output pout = Bool
{
    pout := !pin
}
module crossLoop {
    input en = Bool
    let x = Bool
    let y = Bool
    let u = passthru.create
    u.pin := x
    y := u.pout
    x := y && en
}
println(moduleTreeVL(crossLoop.create.tree))
"#);
    assert!(output.contains("HDL031"), "cross-hierarchy loop must warn HDL031, got:\n{}", output);
    assert!(
        output.contains("combinational loop through instance 'u'"),
        "instance attribution expected, got:\n{}", output
    );
}

// ── non-trigger: cross-hierarchy loop is exempt when two ring edges carry
// mutually exclusive conditions (§3.3 exemption: the ring is syntactically
// unsatisfiable). The mutex must sit on two DIFFERENT edges of the ring —
// a self-contradictory single-edge condition is HDL034 territory, not a
// loop exemption (documented in the phase234 design deviations).

#[test]
fn hdl031_cross_loop_exempt_by_mutex() {
    let output = assert_ok(r#"
module passthruM
    input pin = Bool
    output pout = Bool
{
    pout := !pin
}
module crossLoopM {
    input sel = Bool
    let x = Bool
    let y = Bool
    let u = passthruM.create
    when sel {
        u.pin := x
    }
    y := u.pout
    when !sel {
        x := y
    }
}
println(moduleTreeVL(crossLoopM.create.tree))
"#);
    assert!(!output.contains("HDL031"), "mutex cross loop must be exempt, got:\n{}", output);
    assert!(!output.contains("HDL030"), "no in-module loop here, got:\n{}", output);
}

// ── §9.3: inferred latch — conditional comb drivers without a default ──

#[test]
fn hdl032_inferred_latch() {
    let output = assert_ok(r#"
module latchDemo {
    input en = Bool
    input d = UInt[8]
    output q = UInt[8]
    let l = UInt[8]
    when en {
        l := d
    }
    q := l
}
println(moduleTreeVL(latchDemo.create.tree))
"#);
    assert!(output.contains("HDL032"), "incomplete conditional drivers must warn HDL032, got:\n{}", output);
    assert!(
        output.contains("inferred latch"),
        "latch message expected, got:\n{}", output
    );
}

// ── §9.3 non-trigger: same shape + otherwise → T2-complete, zero warnings ──

#[test]
fn hdl032_latch_cured_by_otherwise() {
    let output = assert_ok(r#"
module latchOk {
    input en = Bool
    input d = UInt[8]
    input d2 = UInt[8]
    output q = UInt[8]
    let l = UInt[8]
    when en {
        l := d
    } otherwise {
        l := d2
    }
    q := l
}
println(moduleTreeVL(latchOk.create.tree))
"#);
    assert!(!output.contains("HDL032"), "T2-complete drivers must not warn, got:\n{}", output);
    assert!(!output.contains("[hdl][warning]"), "zero warnings expected, got:\n{}", output);
}

// ── §9.3: T3 coverage — switch + default over one selector ──

#[test]
fn hdl032_switch_default_t3_complete() {
    let output = assert_ok(r#"
module switchCov {
    input sel = UInt[2]
    input a = UInt[4]
    input b = UInt[4]
    input c = UInt[4]
    output q = UInt[4]
    let s = UInt[4]
    switch sel {
        is 0 { s := a }
        is 1 { s := b }
        default { s := c }
    }
    q := s
}
println(moduleTreeVL(switchCov.create.tree))
"#);
    assert!(!output.contains("HDL032"), "switch+default is T3-complete, got:\n{}", output);
    assert!(!output.contains("[hdl][warning]"), "zero warnings expected, got:\n{}", output);
}

// ── §9.3: bit-range partial drives with disjoint ranges — no HDL033, and
// the phase-1 HDL010 multi-driver false positive is suppressed ──

#[test]
fn hdl033_slice_ok_suppresses_hdl010() {
    let output = assert_ok(r#"
module sliceOK {
    input a = UInt[4]
    input b = UInt[4]
    output q = UInt[8]
    let t = UInt[8]
    t.slice[3, 0] := a
    t.slice[7, 4] := b
    q := t
}
println(moduleTreeVL(sliceOK.create.tree))
"#);
    assert!(!output.contains("HDL033"), "disjoint ranges must not warn HDL033, got:\n{}", output);
    assert!(!output.contains("HDL010"), "rangeSafe must suppress HDL010, got:\n{}", output);
    assert!(!output.contains("[hdl][warning]"), "zero warnings expected, got:\n{}", output);
}

// ── §9.3: overlapping bit ranges on two drivers ──

#[test]
fn hdl033_slice_overlap() {
    let output = assert_ok(r#"
module sliceOverlap {
    input a = UInt[6]
    input b = UInt[4]
    output q = UInt[8]
    let t = UInt[8]
    t.slice[5, 0] := a
    t.slice[7, 4] := b
    q := t
}
println(moduleTreeVL(sliceOverlap.create.tree))
"#);
    assert!(output.contains("HDL033"), "overlapping ranges must warn HDL033, got:\n{}", output);
    assert!(
        output.contains("overlapping bit ranges [7:4] and [5:0] on multiple drivers"),
        "canonical range pair expected, got:\n{}", output
    );
}

// ── §9.3: always-false driver condition (dead driver); HDL032 co-fires
// because the dead driver does not constitute coverage. NOTE (deviation):
// the dead condition is expressed over one SELECTOR with two values — the
// bare-signal form `when c && !c` is indistinguishable from the
// WhenStack-residue pollution of replay rounds (engine finding) and is
// therefore not reported; see the phase234 design deviations list. ──

#[test]
fn hdl034_dead_condition() {
    let output = assert_ok(r#"
module deadCond {
    input sel = UInt[2]
    input a = UInt[4]
    output q = UInt[4]
    let s = UInt[4]
    when (sel == 0) && (sel == 1) {
        s := a
    }
    q := s
}
println(moduleTreeVL(deadCond.create.tree))
"#);
    assert!(output.contains("HDL034"), "self-contradictory condition must warn HDL034, got:\n{}", output);
    assert!(
        output.contains("driver condition is always false"),
        "dead condition message expected, got:\n{}", output
    );
    assert!(output.contains("HDL032"), "dead driver does not constitute coverage (HDL032 co-fires), got:\n{}", output);
}

// ── §9.3 non-trigger twin for hdl034_dead_condition: a single eq leaf over
// one selector (when + otherwise) is a LIVE condition — T2-complete, no
// dead-condition warning, zero warnings overall.

#[test]
fn hdl034_live_eq_condition_silent() {
    let output = assert_ok(r#"
module deadOk {
    input sel = UInt[2]
    input a = UInt[4]
    input b = UInt[4]
    output q = UInt[4]
    let s = UInt[4]
    when (sel == 0) {
        s := a
    } otherwise {
        s := b
    }
    q := s
}
println(moduleTreeVL(deadOk.create.tree))
"#);
    assert!(!output.contains("HDL034"), "single eq-leaf condition is live, got:\n{}", output);
    assert!(!output.contains("HDL032"), "when/otherwise is T2-complete, got:\n{}", output);
    assert!(!output.contains("[hdl][warning]"), "zero warnings expected, got:\n{}", output);
}

// ── §9.3: same-condition driver shadowed by a later one ──

#[test]
fn hdl035_shadowed_condition() {
    let output = assert_ok(r#"
module shadowCond {
    input en = Bool
    input a = UInt[4]
    input b = UInt[4]
    output q = UInt[4]
    let s = UInt[4]
    when en {
        s := a
    }
    when en {
        s := b
    }
    q := s
}
println(moduleTreeVL(shadowCond.create.tree))
"#);
    assert!(output.contains("HDL035"), "same-condition double drive must warn HDL035, got:\n{}", output);
    assert!(
        output.contains("conditional driver shadowed by a later driver with the same condition"),
        "shadow message expected, got:\n{}", output
    );
}

// ── §9.3 non-trigger: different conditions on the same signal don't shadow ──

#[test]
fn hdl035_different_conditions_ok() {
    let output = assert_ok(r#"
module shadowOk {
    input e1 = Bool
    input e2 = Bool
    input a = UInt[4]
    input b = UInt[4]
    output q = UInt[4]
    let s = UInt[4]
    when e1 {
        s := a
    }
    when e2 {
        s := b
    }
    q := s
}
println(moduleTreeVL(shadowOk.create.tree))
"#);
    assert!(!output.contains("HDL035"), "different conditions must not shadow, got:\n{}", output);
}

// ── §9.4 CDC: single-bit 2FF chain (manual bufferCC equivalent, built with
// the low-level regAssignCd API) — recognized synchronizer, zero warnings ──
// Naming-trap homage (design §5.3): `_sync2` is the FIRST stage, `_sync1`
// the second — the walk is purely structural, names are decoration.

#[test]
fn cdc_good_2ff_chain_silent() {
    let output = assert_ok(r#"
def cdA: ClockDomain = ClockDomain.mk "clkA" "rstA" Async RisingEdge ActiveHigh
def cdB: ClockDomain = ClockDomain.mk "clkB" "rstB" Async RisingEdge ActiveHigh
module cdcGood[cdA] {
    output q = UInt[1]
    let src = newUIntRegInitCdNamed("src", 1, 0, cdA)
    let _ = createSignalExpr("", regAssignCd(src.zz_expr, literal(0), cdA))
    let r1 = newUIntRegCdNamed("flag_sync2", 1, cdB)
    let _ = createSignalExpr("", regAssignCd(r1.zz_expr, src.zz_expr, cdB))
    let r2 = newUIntRegCdNamed("flag_sync1", 1, cdB)
    let _ = createSignalExpr("", regAssignCd(r2.zz_expr, r1.zz_expr, cdB))
    q := r2
}
println(moduleTreeVL(cdcGood.create[cdA].tree))
"#);
    assert!(!output.contains("HDL037"), "2FF chain must exempt HDL037, got:\n{}", output);
    assert!(!output.contains("HDL038"), "1-bit chain must not warn HDL038, got:\n{}", output);
    assert!(!output.contains("HDL039"), "no mid-stage read here, got:\n{}", output);
    assert!(!output.contains("HDL036"), "no domain mixing here, got:\n{}", output);
    assert!(!output.contains("[hdl][warning]"), "zero warnings expected, got:\n{}", output);
}

// ── §9.4 CDC: chain length 1 → HDL037 with the chain-length note ──

#[test]
fn cdc_bad_single_stage() {
    let output = assert_ok(r#"
def cdA: ClockDomain = ClockDomain.mk "clkA" "rstA" Async RisingEdge ActiveHigh
def cdB: ClockDomain = ClockDomain.mk "clkB" "rstB" Async RisingEdge ActiveHigh
module cdcBad[cdA] {
    output q = UInt[8]
    let src = newUIntRegInitCdNamed("src", 8, 0, cdA)
    let _ = createSignalExpr("", regAssignCd(src.zz_expr, literal(0), cdA))
    let hop = newUIntRegCdNamed("hop", 8, cdB)
    let _ = createSignalExpr("", regAssignCd(hop.zz_expr, src.zz_expr, cdB))
    q := hop
}
println(moduleTreeVL(cdcBad.create[cdA].tree))
"#);
    assert!(output.contains("HDL037"), "chain-length-1 sampling must warn HDL037, got:\n{}", output);
    assert!(
        output.contains("register 'hop' (clkB) samples registered 'src' (clkA) without a synchronizer chain (chain length 1)"),
        "exact HDL037 message expected, got:\n{}", output
    );
}

// ── §9.4 CDC: identified 2FF chain with a multi-bit head → HDL038 ──

#[test]
fn cdc_wide_multibit_chain() {
    let output = assert_ok(r#"
def cdA: ClockDomain = ClockDomain.mk "clkA" "rstA" Async RisingEdge ActiveHigh
def cdB: ClockDomain = ClockDomain.mk "clkB" "rstB" Async RisingEdge ActiveHigh
module cdcWide[cdA] {
    output q = UInt[8]
    let src = newUIntRegInitCdNamed("src", 8, 0, cdA)
    let _ = createSignalExpr("", regAssignCd(src.zz_expr, literal(0), cdA))
    let r1 = newUIntRegCdNamed("w_sync2", 8, cdB)
    let _ = createSignalExpr("", regAssignCd(r1.zz_expr, src.zz_expr, cdB))
    let r2 = newUIntRegCdNamed("w_sync1", 8, cdB)
    let _ = createSignalExpr("", regAssignCd(r2.zz_expr, r1.zz_expr, cdB))
    q := r2
}
println(moduleTreeVL(cdcWide.create[cdA].tree))
"#);
    assert!(output.contains("HDL038"), "multi-bit 2FF chain must warn HDL038, got:\n{}", output);
    assert!(
        output.contains("multi-bit (8) signal crossed to clkB through a 2-FF synchronizer — Gray coding required"),
        "HDL038 message expected, got:\n{}", output
    );
    assert!(!output.contains("HDL037"), "identified chain must not warn HDL037, got:\n{}", output);
}

// ── §9.4 CDC: toggle-sync XOR edge detection is the exempt mid-stage read ──

#[test]
fn cdc_xor_edge_detect_exempt() {
    let output = assert_ok(r#"
def cdA: ClockDomain = ClockDomain.mk "clkA" "rstA" Async RisingEdge ActiveHigh
def cdB: ClockDomain = ClockDomain.mk "clkB" "rstB" Async RisingEdge ActiveHigh
module xorExempt[cdA] {
    input pulse = Bool
    output pulseOut = Bool
    let toggle = newBoolRegCdNamed("toggle", cdA)
    let sync1 = newBoolRegCdNamed("sync1", cdB)
    let sync2 = newBoolRegCdNamed("sync2", cdB)
    when pulse {
        let _ = createSignalExpr("", regAssignCd(toggle.zz_expr, unary("!", toggle.zz_expr), cdA))
    }
    let _ = createSignalExpr("", regAssignCd(sync1.zz_expr, toggle.zz_expr, cdB))
    let _ = createSignalExpr("", regAssignCd(sync2.zz_expr, sync1.zz_expr, cdB))
    pulseOut := Bool.mk(None, binary(sync1.zz_expr, "^", sync2.zz_expr))
}
println(moduleTreeVL(xorExempt.create[cdA].tree))
"#);
    assert!(!output.contains("HDL039"), "XOR edge detect must be exempt, got:\n{}", output);
    assert!(!output.contains("HDL037"), "identified chain must not warn HDL037, got:\n{}", output);
    assert!(!output.contains("[hdl][warning]"), "zero warnings expected, got:\n{}", output);
}

// ── §9.4 CDC: the XOR edge-detect exemption is operand-order insensitive —
// sync2 ^ sync1 is the same symmetric form as sync1 ^ sync2 (exprKey renders
// binary operand order, the matcher accepts both orders).

#[test]
fn cdc_xor_edge_detect_operand_order_exempt() {
    let output = assert_ok(r#"
def cdA: ClockDomain = ClockDomain.mk "clkA" "rstA" Async RisingEdge ActiveHigh
def cdB: ClockDomain = ClockDomain.mk "clkB" "rstB" Async RisingEdge ActiveHigh
module xorExemptFlip[cdA] {
    input pulse = Bool
    output pulseOut = Bool
    let toggle = newBoolRegCdNamed("toggle", cdA)
    let sync1 = newBoolRegCdNamed("sync1", cdB)
    let sync2 = newBoolRegCdNamed("sync2", cdB)
    when pulse {
        let _ = createSignalExpr("", regAssignCd(toggle.zz_expr, unary("!", toggle.zz_expr), cdA))
    }
    let _ = createSignalExpr("", regAssignCd(sync1.zz_expr, toggle.zz_expr, cdB))
    let _ = createSignalExpr("", regAssignCd(sync2.zz_expr, sync1.zz_expr, cdB))
    pulseOut := Bool.mk(None, binary(sync2.zz_expr, "^", sync1.zz_expr))
}
println(moduleTreeVL(xorExemptFlip.create[cdA].tree))
"#);
    assert!(!output.contains("HDL039"), "flipped-operand XOR edge detect must be exempt, got:\n{}", output);
    assert!(!output.contains("HDL037"), "identified chain must not warn HDL037, got:\n{}", output);
    assert!(!output.contains("[hdl][warning]"), "zero warnings expected, got:\n{}", output);
}

// ── §9.4 CDC: port sources are domain-neutral — an input feeding a foreign-
// domain register does NOT report (design §5.1 anchor 4, conservative) ──

#[test]
fn cdc_port_source_neutral_silent() {
    let output = assert_ok(r#"
def cdA: ClockDomain = ClockDomain.mk "clkA" "rstA" Async RisingEdge ActiveHigh
def cdB: ClockDomain = ClockDomain.mk "clkB" "rstB" Async RisingEdge ActiveHigh
module portNeutral[cdA] {
    input din = UInt[8]
    output q = UInt[8]
    let r = newUIntRegCdNamed("r", 8, cdB)
    let _ = createSignalExpr("", regAssignCd(r.zz_expr, din.zz_expr, cdB))
    q := r
}
println(moduleTreeVL(portNeutral.create[cdA].tree))
"#);
    assert!(!output.contains("HDL037"), "port source is domain-neutral (no report), got:\n{}", output);
    assert!(!output.contains("[hdl][warning]"), "zero warnings expected, got:\n{}", output);
}

// ── HDL036: a combinational signal fed from two different clock domains ──

#[test]
fn hdl036_domain_mix() {
    let output = assert_ok(r#"
def cdA: ClockDomain = ClockDomain.mk "clkA" "rstA" Async RisingEdge ActiveHigh
def cdB: ClockDomain = ClockDomain.mk "clkB" "rstB" Async RisingEdge ActiveHigh
module domMix[cdA] {
    output q = UInt[8]
    let ra = newUIntRegCdNamed("ra", 8, cdA)
    let rb = newUIntRegCdNamed("rb", 8, cdB)
    let _ = createSignalExpr("", regAssignCd(ra.zz_expr, literal(0), cdA))
    let _ = createSignalExpr("", regAssignCd(rb.zz_expr, literal(0), cdB))
    q := ra + rb
}
println(moduleTreeVL(domMix.create[cdA].tree))
"#);
    assert!(output.contains("HDL036"), "mixed-domain comb signal must warn HDL036, got:\n{}", output);
    assert!(
        output.contains("combinational signal mixes domains clkA/clkB"),
        "HDL036 message expected, got:\n{}", output
    );
}

// ── HDL039: a mid-stage chain read by a plain comb consumer (no XOR) ──

#[test]
fn hdl039_mid_stage_read() {
    let output = assert_ok(r#"
def cdA: ClockDomain = ClockDomain.mk "clkA" "rstA" Async RisingEdge ActiveHigh
def cdB: ClockDomain = ClockDomain.mk "clkB" "rstB" Async RisingEdge ActiveHigh
module midRead[cdA] {
    output q = UInt[1]
    let src = newUIntRegInitCdNamed("src", 1, 0, cdA)
    let _ = createSignalExpr("", regAssignCd(src.zz_expr, literal(0), cdA))
    let r1 = newUIntRegCdNamed("s1", 1, cdB)
    let _ = createSignalExpr("", regAssignCd(r1.zz_expr, src.zz_expr, cdB))
    let r2 = newUIntRegCdNamed("s2", 1, cdB)
    let _ = createSignalExpr("", regAssignCd(r2.zz_expr, r1.zz_expr, cdB))
    q := r1
}
println(moduleTreeVL(midRead.create[cdA].tree))
"#);
    assert!(output.contains("HDL039"), "mid-stage consumer must warn HDL039, got:\n{}", output);
    assert!(
        output.contains("synchronizer mid-stage read: consumer bypasses the chain head"),
        "HDL039 message expected, got:\n{}", output
    );
    assert!(!output.contains("HDL037"), "identified chain must not warn HDL037, got:\n{}", output);
}

// ── examples/hdl/21-crossclock: the library sync chains are recognized —
// HDL038 x2 (binary FIFO pointers through 2FF chains), nothing else ──

#[test]
fn examples_21_crossclock_expected_warnings() {
    let output = assert_ok(include_str!("../../examples/hdl/21-crossclock.typort"));
    assert_eq!(
        output.matches("HDL038").count(),
        2,
        "exactly the two binary FIFO pointer chains warn HDL038, got:\n{}", output
    );
    assert!(
        output.contains("multi-bit (3) signal crossed to clkB") && output.contains("multi-bit (3) signal crossed to clkA"),
        "wrPtrSync1 (to clkB) and rdPtrSync1 (to clkA) chains expected, got:\n{}", output
    );
    assert!(!output.contains("HDL036"), "no mixed-domain comb signal in 21-crossclock, got:\n{}", output);
    assert!(!output.contains("HDL037"), "all crossings are synchronized chains, got:\n{}", output);
    assert!(!output.contains("HDL039"), "XOR edge reads are exempt, got:\n{}", output);
}

// ── HDL041: constant bit-select/part-select index out of the declared
// width — silent x read/write in Verilog (review 2026-09-29 P2-7) ──

#[test]
fn hdl041_slice_index_out_of_range() {
    let output = assert_ok(r#"
module sliceOob {
    input a = UInt[8]
    output y = UInt[3]
    y := a.slice[9, 7]
}
println(moduleTreeVL(sliceOob.create.tree))
"#);
    assert!(output.contains("HDL041"), "out-of-range part select must warn HDL041, got:\n{}", output);
    assert!(
        output.contains("constant bit range [9:7] out of declared width 8"),
        "HDL041 message expected, got:\n{}", output
    );
}

#[test]
fn hdl041_bitsel_index_out_of_range() {
    let output = assert_ok(r#"
module bitselOob {
    input a = UInt[8]
    output z = Bool
    z := a[8]
}
println(moduleTreeVL(bitselOob.create.tree))
"#);
    assert!(output.contains("HDL041"), "out-of-range bit select must warn HDL041, got:\n{}", output);
    assert!(
        output.contains("constant bit index 8 out of declared width 8"),
        "HDL041 message expected, got:\n{}", output
    );
}

// In-range constant selects stay silent (both read and drive sides).

#[test]
fn hdl041_in_range_selects_silent() {
    let output = assert_ok(r#"
module sliceOk {
    input a = UInt[8]
    input b = UInt[3]
    output y = UInt[3]
    output z = Bool
    let t = UInt[8]
    t.slice[2, 0] := b
    t[7] := a[7]
    y := a.slice[4, 2]
    z := t[3]
}
println(moduleTreeVL(sliceOk.create.tree))
"#);
    assert!(!output.contains("HDL041"), "in-range selects must not warn HDL041, got:\n{}", output);
    assert!(!output.contains("[hdl][warning]"), "zero warnings expected, got:\n{}", output);
}

// subSignal bases (child-port selects) stay out of scope: the port width is
// declared in the CHILD module, not in this module's GDecl table.

#[test]
fn hdl041_subsignal_base_silent() {
    let output = assert_ok(r#"
module srcMod
    output o = UInt[8]
{
    o := 1
}
module dynIdx {
    input x = UInt[8]
    output z = Bool
    let u = srcMod.create
    z := u.o[9]
    x := u.o
}
println(moduleTreeVL(dynIdx.create.tree))
"#);
    assert!(!output.contains("HDL041"), "subSignal bases are out of scope, got:\n{}", output);
}

// ── HDL042: same-name second module registration with a different
// parameterization — designVL emits one def per name, so the second
// parameterization's instances silently connect to the wrong port widths
// (review 2026-09-29 P3-10, spec §8.1 known limitation) ──

#[test]
fn hdl042_second_parameterization_warns() {
    let output = assert_ok(r#"
module myAdder[w: Nat]
    input a = UInt[w]
    input b = UInt[w]
    output sum = UInt[w]
    input en = Bool
{
    sum := en.mux(a + b, a)
}
module top8 {
    input a = UInt[8]
    input b = UInt[8]
    input en = Bool
    output sum = UInt[8]
    let u = myAdder.create[8]
    u.a := a
    u.b := b
    u.en := en
    sum := u.sum
}
module top16 {
    input a = UInt[16]
    input b = UInt[16]
    input en = Bool
    output sum = UInt[16]
    let u = myAdder.create[16]
    u.a := a
    u.b := b
    u.en := en
    sum := u.sum
}
println(moduleTreeVL(top8.create.tree))
println(moduleTreeVL(top16.create.tree))
"#);
    assert!(output.contains("HDL042"), "myAdder[16] after myAdder[8] must warn HDL042, got:\n{}", output);
    assert!(
        output.contains("second registration under the same module name"),
        "HDL042 message expected, got:\n{}", output
    );
}

// Non-trigger twin: the same parameterization instantiated twice (and a
// plain module afterwards) is the ordinary case — every replay round of one
// parameterization matches the recorded signature and stays silent.

#[test]
fn hdl042_same_parameterization_and_replays_silent() {
    let output = assert_ok(r#"
module myAdder[w: Nat]
    input a = UInt[w]
    input b = UInt[w]
    output sum = UInt[w]
    input en = Bool
{
    sum := en.mux(a + b, a)
}
module topA {
    input a = UInt[8]
    input b = UInt[8]
    input en = Bool
    output sum = UInt[8]
    let u1 = myAdder.create[8]
    let u2 = myAdder.create[8]
    u1.a := a
    u1.b := b
    u1.en := en
    sum := u1.sum
}
module topB {
    input x = UInt[16]
    output y = UInt[16]
    y := x
}
println(moduleTreeVL(topA.create.tree))
println(moduleTreeVL(topB.create.tree))
"#);
    assert!(!output.contains("HDL042"), "same parameterization must not warn HDL042, got:\n{}", output);
}
