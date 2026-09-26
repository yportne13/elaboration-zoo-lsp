// ============================================================
// HDL enum tests (the SpinalEnum counterpart, docs/hdl-enum-design.md)
//
// `#[derive(HdlEnum)] enum FsmState { IDLE RUN DONE }` generates EnumLit
// element defs (FsmState.IDLE …), FsmState.count, and the craft/craftAs/reg/
// regInit factories. Craft signals degrade to createWidth/createRegWidth
// nodes, so the Verilog below is plain bit-vector Verilog.
//
// Behavior pinned here (design doc §9 acceptance cases):
//   - derive products resolve: FsmState.IDLE / FsmState.count / FsmState.craft
//   - craft + ===/=/= generate the encoded comparison strings
//   - regInit reset block + exhaustive switch (FSM shape)
//   - exhaustive switch without default: no HDL040
//   - missing is-case: HDL040 WARNING naming the missing element
//   - cross-enum / cross-width mixing: type errors
//   - oneHot width = element count
//   - L07 pure match patterns on a derived enum keep working
// ============================================================

use super::*;

fn assert_ok(input: &str) -> String {
    match run_with_prelude(input) {
        Ok(output) => output,
        Err(e) => panic!("expected OK, got error: '{}' @ {}:{}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

fn assert_err_contains(input: &str, needle: &str) {
    match run_with_prelude(input) {
        Ok(output) => panic!("expected error containing '{}', got OK: {}", needle, output.trim()),
        Err(e) => {
            assert!(
                e.0.data.contains(needle),
                "expected error containing '{}', got: '{}'",
                needle,
                e.0.data
            );
        }
    }
}

const ENUM_DECLS: &str = r#"
#[derive(HdlEnum)]
enum FsmState {
    IDLE
    RUN
    DONE
}

#[derive(HdlEnum)]
enum Cmd {
    NOP
    READ
    WRITE
}
"#;

// ── §9.1: declare, compare, combinational assignment ──

#[test]
fn hdl_enum_craft_compare_asuint() {
    let output = assert_ok(&format!(
        r#"{}
module enumBasics {{
    input hit = Bool
    output isRun = Bool
    output code = UInt[2]
    let cur = FsmState.craft
    when hit {{
        cur := FsmState.RUN
    }} otherwise {{
        cur := FsmState.IDLE
    }}
    isRun := cur === FsmState.RUN
    code := cur.asUInt
}}
println(moduleTreeVL(enumBasics.create.tree))
"#,
        ENUM_DECLS
    ));
    // cur is when-driven, so it becomes a reg with an always @(*) block;
    // RUN encodes to 1, IDLE to 0 (binary).
    assert!(output.contains("reg [1:0] cur;"), "expected 2-bit reg cur, got: {}", output);
    assert!(output.contains("cur = 1;"), "expected `cur = 1;` (RUN), got: {}", output);
    assert!(output.contains("cur = 0;"), "expected `cur = 0;` (IDLE), got: {}", output);
    assert!(output.contains("assign isRun = (cur == 1);"), "expected encoded compare, got: {}", output);
    assert!(output.contains("assign code = cur;"), "expected asUInt passthrough, got: {}", output);
}

// ── §9.2: mux over craft signals ──

#[test]
fn hdl_enum_mux() {
    let output = assert_ok(&format!(
        r#"{}
module enumMux {{
    input sel = Bool
    output q = UInt[2]
    let a = FsmState.craft
    let b = FsmState.craft
    let out = FsmState.craft
    a := FsmState.RUN
    b := FsmState.IDLE
    out := sel.mux(a, b)
    q := out.asUInt
}}
println(moduleTreeVL(enumMux.create.tree))
"#,
        ENUM_DECLS
    ));
    assert!(output.contains("wire [1:0] a;"), "expected 2-bit wires, got: {}", output);
    assert!(output.contains("assign a = 1;"), "expected `assign a = 1;`, got: {}", output);
    assert!(output.contains("assign b = 0;"), "expected `assign b = 0;`, got: {}", output);
    assert!(output.contains("assign out = (sel ? a : b);"), "expected mux of craft signals, got: {}", output);
    assert!(output.contains("assign q = out;"), "expected `assign q = out;`, got: {}", output);
}

// ── §9.2: FSM — regInit reset block + exhaustive switch without default ──

#[test]
fn hdl_enum_reg_init_fsm_switch() {
    let output = assert_ok(&format!(
        r#"{}
module fsm {{
    input start = Bool
    input doneIn = Bool
    output busy = Bool
    output outState = UInt[2]
    let st = FsmState.regInit(FsmState.IDLE)
    switch st {{
        is FsmState.IDLE {{ when start  {{ st := FsmState.RUN  }} }}
        is FsmState.RUN  {{ when doneIn {{ st := FsmState.DONE }} }}
        is FsmState.DONE {{ st := FsmState.IDLE }}
    }}
    busy := st === FsmState.RUN
    outState := st.asUInt
}}
println(moduleTreeVL(fsm.create.tree))
"#,
        ENUM_DECLS
    ));
    assert!(output.contains("reg [1:0] st;"), "expected 2-bit reg st, got: {}", output);
    // async reset to IDLE = 0
    assert!(output.contains("st <= 0;"), "expected reset assignment `st <= 0;`, got: {}", output);
    // nested when conditions conjoin with the state compare (each level
    // accumulates the negation of the earlier branch conditions)
    assert!(output.contains("if (start && (st == 0))"), "expected IDLE+start guard, got: {}", output);
    assert!(output.contains("if (doneIn && ((st == 1) && !(st == 0)))"), "expected RUN+done guard, got: {}", output);
    assert!(output.contains("if ((st == 2) && (!(st == 0) && !(st == 1)))"), "expected DONE guard, got: {}", output);
    assert!(output.contains("st <= 1;"), "expected `st <= 1;` (RUN), got: {}", output);
    assert!(output.contains("st <= 2;"), "expected `st <= 2;` (DONE), got: {}", output);
    assert!(output.contains("assign busy = (st == 1);"), "expected busy compare, got: {}", output);
    // exhaustive (all three is-cases) — no HDL040
    assert!(!output.contains("HDL040"), "exhaustive switch must not warn HDL040, got: {}", output);
}

// ── §9.3: oneHot encoding — width = element count, values are powers of 2 ──

#[test]
fn hdl_enum_onehot_width_and_values() {
    let output = assert_ok(&format!(
        r#"{}
module cmdEnc {{
    input fire = Bool
    output cmdOut = UInt[3]
    let c = Cmd.craftAs[encOneHot]
    when fire {{
        c := Cmd.READ
    }} otherwise {{
        c := Cmd.NOP
    }}
    cmdOut := c.asUInt
}}
println(moduleTreeVL(cmdEnc.create.tree))
"#,
        ENUM_DECLS
    ));
    // 3 elements → 3-bit oneHot
    assert!(output.contains("reg [2:0] c;"), "expected 3-bit oneHot reg c, got: {}", output);
    // READ is position 1 → 2^1 = 2; NOP is position 0 → 2^0 = 1
    assert!(output.contains("c = 2;"), "expected oneHot READ = 2, got: {}", output);
    assert!(output.contains("c = 1;"), "expected oneHot NOP = 1, got: {}", output);
    assert!(output.contains("assign cmdOut = c;"), "expected cmdOut passthrough, got: {}", output);
}

// ── §9.4: exhaustive switch without default — no HDL040 ──

#[test]
fn hdl_enum_switch_exhaustive_no_warning() {
    let output = assert_ok(&format!(
        r#"{}
module fsmDecode {{
    input adv = Bool
    let st = FsmState.regInit(FsmState.IDLE)
    when adv {{ st := FsmState.DONE }}
    let last = FsmState.craft
    switch st {{
        is FsmState.IDLE {{ last := FsmState.RUN  }}
        is FsmState.RUN  {{ last := FsmState.DONE }}
        is FsmState.DONE {{ last := FsmState.IDLE }}
    }}
}}
println(moduleTreeVL(fsmDecode.create.tree))
"#,
        ENUM_DECLS
    ));
    // when-driven craft signal → combinational reg
    assert!(output.contains("reg [1:0] last;"), "expected 2-bit reg last, got: {}", output);
    assert!(!output.contains("HDL040"), "exhaustive switch must not warn, got: {}", output);
}

// ── §9.4: missing is-case → HDL040 WARNING naming the missing element ──

#[test]
fn hdl_enum_switch_missing_case_reports_hdl040() {
    // The no-default switch desugars to a plain when chain; the HDL040
    // exhaustiveness check is the direct switchFinalEnum call (one line per
    // check, cases built from the derive-generated element table).
    let output = assert_ok(&format!(
        r#"{}
module fsmMissing {{
    input adv = Bool
    let st = FsmState.regInit(FsmState.IDLE)
    when adv {{ st := FsmState.DONE }}
    let last = FsmState.craft
    switch st {{
        is FsmState.IDLE {{ last := FsmState.RUN }}
    }}
    let _ = switchFinalEnum(st,
        scCons (shEnum ("FsmState", "IDLE", FsmState.hdlEnumElems)) scEmpty, false)
}}
println(moduleTreeVL(fsmMissing.create.tree))
"#,
        ENUM_DECLS
    ));
    assert!(
        output.contains("HDL040"),
        "non-exhaustive switch must report HDL040, got: {}",
        output
    );
    assert!(
        output.contains("missing: DONE, RUN"),
        "HDL040 must name the missing elements, got: {}",
        output
    );
    assert!(
        output.contains("fsmMissing"),
        "HDL040 must carry the module name, got: {}",
        output
    );
}

// ── examples/hdl/08-control-flow 抽查:with-default switch（is 0 / is 1 /
//    default）的展开与改动前逐 token 一致,既有用法零回归 ──

#[test]
fn hdl_enum_examples_08_switch_regression() {
    let output = assert_ok(
        r#"
module switchExample {
    input sel = UInt[4]
    input a = UInt[4]
    input b = UInt[4]
    input c = UInt[4]
    output result = UInt[4]
    switch sel {
        is 0 { result := a }
        is 1 { result := b }
        default { result := c }
    }
}
println(moduleTreeVL(switchExample.create.tree))
"#,
    );
    // when-driven output ports render as `output reg` with an always @(*)
    // block of independent ifs (one per case, negation-accumulated guards).
    assert!(output.contains("output reg [3:0] result"), "expected output reg result, got: {}", output);
    assert!(output.contains("if (sel == 0)"), "expected `if (sel == 0)` guard, got: {}", output);
    assert!(output.contains("(sel == 1) && !(sel == 0)"), "expected negation-accumulated guard, got: {}", output);
    assert!(output.contains("result = a;"), "expected `result = a;`, got: {}", output);
    assert!(output.contains("result = c;"), "expected `result = c;`, got: {}", output);
    assert!(!output.contains("HDL0"), "no HDL warnings expected, got: {}", output);
}

// ── default branch suppresses the check even when is-cases are partial ──

#[test]
fn hdl_enum_switch_with_default_no_warning() {
    let output = assert_ok(&format!(
        r#"{}
module fsmDefaulted {{
    input adv = Bool
    let st = FsmState.regInit(FsmState.IDLE)
    when adv {{ st := FsmState.DONE }}
    let last = FsmState.craft
    switch st {{
        is FsmState.IDLE {{ last := FsmState.RUN }}
        default {{ last := FsmState.IDLE }}
    }}
}}
println(moduleTreeVL(fsmDefaulted.create.tree))
"#,
        ENUM_DECLS
    ));
    assert!(!output.contains("HDL040"), "default must suppress HDL040, got: {}", output);
}

// ── behavior relaxation: no-default switch over UInt now elaborates ──
// Previously a macro match failure; the SwitchFinal fallback makes it a
// plain when chain with no check (design doc §4.7 / §10.4).

#[test]
fn hdl_enum_switch_uint_no_default_now_allowed() {
    let output = assert_ok(
        r#"
module uintSwitch {
    input sel = UInt[4]
    input a = UInt[4]
    output result = UInt[4]
    switch sel {
        is 0 { result := a }
    }
}
println(moduleTreeVL(uintSwitch.create.tree))
"#,
    );
    assert!(output.contains("module uintSwitch"), "expected module output, got: {}", output);
    assert!(!output.contains("HDL040"), "UInt selectors are not checked, got: {}", output);
}

// ── negative: cross-enum comparison is a type error ──

#[test]
fn hdl_enum_cross_enum_compare_rejected() {
    assert_err_contains(
        &format!(
            r#"{}
module crossCmp {{
    input fire = Bool
    output bad = Bool
    let st = FsmState.craft
    when fire {{ st := FsmState.IDLE }}
    bad := st === Cmd.NOP
}}
println(moduleTreeVL(crossCmp.create.tree))
"#,
            ENUM_DECLS
        ),
        "find unsolved meta",
    );
}

// ── negative: cross-enum assignment is a type error (Into phantom E) ──

#[test]
fn hdl_enum_cross_enum_assign_rejected() {
    assert_err_contains(
        &format!(
            r#"{}
module crossAssign {{
    input fire = Bool
    let x = FsmState.craft
    when fire {{ x := Cmd.NOP }}
}}
println(moduleTreeVL(crossAssign.create.tree))
"#,
            ENUM_DECLS
        ),
        "no `Into[EnumCraft",
    );
}

// ── negative: oneHot vs binary craft of the SAME enum — width 3 ≠ 2 ──

#[test]
fn hdl_enum_cross_encoding_compare_rejected() {
    assert_err_contains(
        &format!(
            r#"{}
module crossEnc {{
    input fire = Bool
    output bad = Bool
    let c = Cmd.craftAs[encOneHot]
    let d = Cmd.craft
    when fire {{
        c := Cmd.READ
        d := Cmd.NOP
    }}
    bad := c === d
}}
println(moduleTreeVL(crossEnc.create.tree))
"#,
            ENUM_DECLS
        ),
        "find unsolved meta",
    );
}

// ── negative: derive rejects constructors with payloads ──

#[test]
fn hdl_enum_derive_payload_rejected() {
    assert_err_contains(
        r#"
#[derive(HdlEnum)]
enum Bad {
    A
    B(n: Nat)
}

module usesBad {
    input fire = Bool
    let x = Bad.craft
    when fire { x := Bad.A }
}
println(moduleTreeVL(usesBad.create.tree))
"#,
        "HdlEnum_error_constructors_must_have_no_payload",
    );
}

// ── regInit to a non-zero element encodes its ordinal ──

#[test]
fn hdl_enum_reg_init_nonzero_element() {
    let output = assert_ok(&format!(
        r#"{}
module fsmStart {{
    input tick = Bool
    output busy = Bool
    let st = FsmState.regInit(FsmState.RUN)
    when tick {{ st := FsmState.DONE }}
    busy := st =/= FsmState.IDLE
}}
println(moduleTreeVL(fsmStart.create.tree))
"#,
        ENUM_DECLS
    ));
    assert!(output.contains("st <= 1;"), "expected reset to RUN=1, got: {}", output);
    assert!(output.contains("assign busy = (st != 0);"), "expected =/= compare, got: {}", output);
}

// ── RegNext on a craft signal ──

#[test]
fn hdl_enum_reg_next() {
    let output = assert_ok(&format!(
        r#"{}
module enumDelay {{
    input tick = Bool
    let st = FsmState.regInit(FsmState.IDLE)
    when tick {{ st := FsmState.RUN }}
    let n = regNext(st)
}}
println(moduleTreeVL(enumDelay.create.tree))
"#,
        ENUM_DECLS
    ));
    assert!(output.contains("reg [1:0] n;"), "expected 2-bit delay reg n, got: {}", output);
    assert!(output.contains("n <= st;"), "expected `n <= st;`, got: {}", output);
}

// ── derive products are first-class decls: FsmState.IDLE / FsmState.count ──

#[test]
fn hdl_enum_derived_decls_resolve() {
    let output = assert_ok(&format!(
        r#"{}
def cnt: Nat = FsmState.count
def ord: Nat = FsmState.hdlEnumOrdinal(FsmState.RUN)
println(nat_to_dec(cnt))
println(nat_to_dec(ord))
"#,
        ENUM_DECLS
    ));
    assert!(output.contains("3"), "FsmState.count should be 3, got: {}", output);
    assert!(output.contains("1"), "ordinal(RUN) should be 1, got: {}", output);
}

// ── the L07 side survives: pure match over the derived enum's cases ──

#[test]
fn hdl_enum_l07_pure_match_still_works() {
    let output = assert_ok(&format!(
        r#"{}
def decode(s: FsmState): Nat = match s {{
    case IDLE => 0
    case RUN => 1
    case DONE => 2
}}
def enc2: Nat = encValueOf(encOneHot, 2)
println(nat_to_dec(enc2))
"#,
        ENUM_DECLS
    ));
    // The pure decoder still elaborates (patterns resolve against the Sum);
    // encoding arithmetic is exercised independently of the derive.
    assert!(output.contains("4"), "encValueOf(encOneHot, 2) should be 4, got: {}", output);
}
