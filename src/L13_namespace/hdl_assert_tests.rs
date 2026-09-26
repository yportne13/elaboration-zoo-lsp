// ============================================================
// HDL simulation-assert tests (docs/hdl-blackbox-sim-design.md §3, P1)
//
// `assert(cond, "msg")` and its severity / clock-domain variants desugar to
// assertExpr / assertExprCd statement nodes (createSignalExpr default arm →
// when context folded in). The Verilog generator emits them as
// translate_off-wrapped `always @(posedge clk)` blocks with
// `TYPORT_ASSERT_<SEV>` marker lines.
//
// Behavior pinned here (L2 shape; the sim-level close-up lives in
// tests/sim_tests.rs):
//   - top-level assert   → unconditional clocked assertion
//   - when-wrapped assert→ nested if (condition folded)
//   - assertCd           → extra-domain block + synthesized `input wire clk2`
//   - manifest           → extra-domain clk port mirrored into the module JSON
//                          (moduleJsonFull, P2-1)
//   - assertCd-only      → zero-port module header: the extra-cd port is the
//                          ONLY port source, emitted without a leading comma
//                          (P3-4)
//   - severity variants  → INFO / WARNING / ERROR / FATAL(+ $finish)
//   - pure-comb module   → assert alone still synthesizes the clk port
//   - self-check         → assert cond counts as a read, never a drive
// ============================================================

use super::*;

fn assert_ok(input: &str) -> String {
    match run_with_prelude(input) {
        Ok(output) => output,
        Err(e) => panic!("expected OK, got error: '{}' @ {}:{}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

// ── top-level assert: unconditional clocked assertion (design doc §7.1) ──

#[test]
fn assert_top_level_counter() {
    let output = assert_ok(r#"
module aCounter {
    input en = Bool
    output reg count = UInt[8] init 0
    when en {
        count := count + 1
    }
    assert(count < 100, "count overflow")
    when (count >= 50) {
        assert(count < 100, "half-way guard")
    }
}
println(moduleTreeVL(aCounter.create.tree))
"#);
    // clk port synthesized (clocked block exists), reset from the reg init
    assert!(output.contains("input wire en,"), "en port first, got: {}", output);
    assert!(output.contains("input wire clk,"), "clk port synthesized, got: {}", output);
    assert!(output.contains("input wire reset"), "reset port from init, got: {}", output);
    // the translate_off-wrapped assertion block, placed after the clocked block
    assert!(output.contains("// synthesis translate_off"), "translate_off wrapper, got: {}", output);
    assert!(output.contains("// synthesis translate_on"), "translate_on wrapper, got: {}", output);
    assert!(output.contains("always @(posedge clk) begin"), "assert always block, got: {}", output);
    assert!(
        output.contains("$display(\"TYPORT_ASSERT_ERROR %0t %m: count overflow\", $time);"),
        "top-level assert marker, got: {}", output
    );
    assert!(output.contains("if (!(count < 100)) begin"), "negated condition, got: {}", output);
    // when-wrapped assert folds into a nested if with one extra indent level
    assert!(
        output.contains("    if (count >= 50) begin\n      if (!(count < 100)) begin\n        $display(\"TYPORT_ASSERT_ERROR %0t %m: half-way guard\", $time);\n      end\n    end"),
        "when-wrapped assert nests, got: {}", output
    );
    // the assert block must not leak into the clocked or combinational blocks
    assert!(!output.contains("always @(*)"), "assert must not enter a comb block, got: {}", output);
    // clocked regAssign stays in its own (reset-gated) block, asserts never reset
    assert!(output.contains("count <= 0;"), "reset init, got: {}", output);
    assert!(output.contains("count <= (count + 1);"), "clocked count, got: {}", output);
}

// ── severity variants: INFO / WARNING / FATAL ──

#[test]
fn assert_severity_tags() {
    let output = assert_ok(r#"
module aSevs {
    input a = Bool
    assertInfo(a, "a is high")
    assertWarning(!a, "a is low")
    assert(a, "default is error")
    assertFatal(a, "fatal stop")
}
println(moduleTreeVL(aSevs.create.tree))
"#);
    assert!(output.contains("TYPORT_ASSERT_INFO %0t %m: a is high"), "INFO tag, got: {}", output);
    assert!(output.contains("TYPORT_ASSERT_WARNING %0t %m: a is low"), "WARNING tag, got: {}", output);
    assert!(output.contains("TYPORT_ASSERT_ERROR %0t %m: default is error"), "ERROR default, got: {}", output);
    assert!(output.contains("$display(\"TYPORT_ASSERT_ERROR %0t %m: fatal stop\", $time);"), "FATAL display, got: {}", output);
    assert!(output.contains("$finish;"), "FATAL finish, got: {}", output);
    // a pure-assert module: no clocked block, but the clk port is still synthesized
    assert!(output.contains("input wire clk"), "clk synthesized for assert-only module, got: {}", output);
    assert!(!output.contains("posedge clk or"), "no reset edge without init regs, got: {}", output);
    // exactly one always block section: only the assert block
    let always_count = output.matches("always @(").count();
    assert_eq!(always_count, 1, "exactly the assert always block, got: {}", output);
}

// ── assertCd: extra clock domain (design doc §7.3) ──

#[test]
fn assert_cd_extra_domain() {
    // NOTE: the cd is built INLINE in the module body, and the emission goes
    // through moduleTreeVL. Sourcing the cd from a top-level def / module
    // parameter, or emitting through designVL (its global ops trigger a def
    // replay whose Val→Tm quote of the replayed tree panics on the 4-arg
    // assertExprCd), trips the pre-existing lvl2ix dangling-level limitation
    // of the test engine — the CLI engine emits all these shapes fine. See
    // the deviation note in the example file.
    let output = assert_ok(r#"
module aCounterCd {
    input en = Bool
    output reg count = UInt[8] init 0
    when en { count := count + 1 }
    assertCd(count < 100, "cd2 overflow", ClockDomain.mk "clk2" "reset2" Async RisingEdge ActiveHigh)
}
println(moduleTreeVL(aCounterCd.create.tree))
"#);
    // the extra-domain clock port reaches the port table via the merged
    // collectClockCds walker
    assert!(output.contains("input wire clk2"), "extra-cd clk port, got: {}", output);
    // the cd2 assertion lives in its own translate_off block on posedge clk2
    assert!(
        output.contains("always @(posedge clk2) begin"),
        "extra-cd assert block, got: {}", output
    );
    assert!(
        output.contains("$display(\"TYPORT_ASSERT_ERROR %0t %m: cd2 overflow\", $time);"),
        "cd2 marker, got: {}", output
    );
    // the main clocked block (before the translate_off wrapper) must NOT
    // carry the cd2 assert
    let main_block = output.split("// synthesis translate_off").next().unwrap_or("");
    assert!(!main_block.contains("cd2 overflow"), "cd2 assert must not leak into the main block, got: {}", output);
}

// ── assert inside when on a combinational module: no reg, no reset ──

#[test]
fn assert_pure_combinational_module() {
    let output = assert_ok(r#"
module aComb {
    input a = Bool
    output y = Bool
    y := a
    assert(a, "a asserted")
}
println(moduleTreeVL(aComb.create.tree))
"#);
    assert!(output.contains("assign y = a;"), "comb drive intact, got: {}", output);
    assert!(output.contains("input wire clk"), "clk synthesized though module is combinational, got: {}", output);
    assert!(output.contains("always @(posedge clk) begin"), "assert block, got: {}", output);
    assert!(output.contains("TYPORT_ASSERT_ERROR %0t %m: a asserted"), "marker, got: {}", output);
}

// ── self-check: assert cond is a read, not a drive ──

#[test]
fn assert_cond_counts_as_read() {
    // `only` is read ONLY by the assert — without the scanStmt arm this
    // would be a false-positive HDL002 (declared but never read).
    let output = assert_ok(r#"
module aOnlyRead {
    input a = Bool
    output y = Bool
    let only = Bool
    only := a
    y := a
    assert(only, "only is high")
}
println(moduleTreeVL(aOnlyRead.create.tree))
"#);
    assert!(!output.contains("HDL002"), "assert-only read must not be flagged dead, got: {}", output);
    assert!(output.contains("assign only = a;"), "drive intact, got: {}", output);
}

#[test]
fn assert_is_not_a_drive() {
    // The assert never drives: `sig` is driven exactly once (uncond comb), so
    // HDL010 (multiple unconditional assignments) must stay silent, and an
    // undriven assert condition still reports HDL001.
    let output = assert_ok(r#"
module aNotDrive {
    input a = Bool
    output y = Bool
    let sig = Bool
    y := a
    let undriven = Bool
    assert(undriven, "undriven cond")
}
println(moduleTreeVL(aNotDrive.create.tree))
"#);
    assert!(output.contains("HDL001"), "undriven assert cond is still a dangling read, got: {}", output);
    let output2 = assert_ok(r#"
module aNotDrive2 {
    input a = Bool
    output y = Bool
    let sig = Bool
    sig := a
    y := sig
    assert(sig, "sig high")
}
println(moduleTreeVL(aNotDrive2.create.tree))
"#);
    assert!(!output2.contains("HDL010"), "assert must not count as a second driver, got: {}", output2);
    assert!(!output2.contains("HDL011"), "no mixed-driver false positive, got: {}", output2);
}

// ── manifest mirrors the extra-domain clock ports (assert P2-1) ──
//
// The design manifest (designManifestVL → moduleJsonFull) must list every
// port the emitted Verilog declares — including the extra-domain clk that
// collectClockCds/extraCdPortsVL synthesize into the module header. Before
// this was mirrored, the Verilog had `input wire clk2` while the manifest
// had no clk2 port, so the sim harness (built from the manifest) could not
// connect or drive the extra domain and the assertCd path was unsimulatable.
//
// NOTE: exercised through moduleJsonFull(headModuleDef(tree.data)) — the
// same renderer designManifestVL dispatches to, minus its ModuleRegistry
// global ops. run_with_prelude panics inside those global ops (the known
// def-replay lvl2ix quote limitation, see example 26's NOTE); the CLI emit
// engine has no such limit and the real designManifestVL path is covered
// end-to-end by tests/sim_tests.rs (every SimConfig::compile builds the
// manifest through it).

#[test]
fn assert_cd_manifest_mirrors_extra_domain_ports() {
    let output = assert_ok(r#"
module aCounterCdM {
    input en = Bool
    output reg count = UInt[8] init 0
    when en { count := count + 1 }
    assertCd(count < 100, "cd2 overflow", ClockDomain.mk "clk2" "reset2" Async RisingEdge ActiveHigh)
}
println(moduleTreeVL(aCounterCdM.create.tree))
println(moduleJsonFull(headModuleDef(aCounterCdM.create.tree.data)))
"#);
    // the emitted Verilog declares the extra-domain clock port …
    assert!(output.contains("input wire clk2"), "extra-cd clk port in Verilog, got: {}", output);
    // … and the manifest mirrors it: an input entry for clk2 (P2-1 fix)
    assert!(
        output.contains("{\"name\": \"clk2\", \"dir\": \"input\", \"width\": 1, \"signed\": false, \"reg\": false}"),
        "manifest must list the extra-cd clk2 port, got: {}", output
    );
    // the main-domain synthesized ports are still listed
    assert!(
        output.contains("{\"name\": \"clk\", \"dir\": \"input\", \"width\": 1, \"signed\": false, \"reg\": false}"),
        "manifest still lists the synthesized main clk port, got: {}", output
    );
    assert!(
        output.contains("{\"name\": \"reset\", \"dir\": \"input\", \"width\": 1, \"signed\": false, \"reg\": false}"),
        "manifest still lists the synthesized main reset port, got: {}", output
    );
    // reset2 is NOT mirrored: that cd has no init regs, and extraCdPortsVL
    // emits a reset port only then — the manifest stays in lockstep
    assert!(!output.contains("\"name\": \"reset2\""),
        "no reset2 port without init regs on the extra cd, got: {}", output);
    // declared ports are untouched
    assert!(output.contains("{\"name\": \"count\", \"dir\": \"output\", \"width\": 8"),
        "declared output port intact, got: {}", output);
    assert!(output.contains("{\"name\": \"en\", \"dir\": \"input\", \"width\": 1"),
        "declared input port intact, got: {}", output);
}

// ── assertCd-only module with NO declared ports (assert P3-4) ──
//
// Here the extra-cd ports are the module's ONLY port source: moduleDefVL
// hits its has_no_port_content + has_extra_ports header branch, where
// extraCdPortsVL must emit the first port WITHOUT a leading comma. Pins the
// header shape (`module X (\n  input wire clk2\n);`) and the manifest's
// port list, which must be exactly that one port (no main-domain clk: the
// module has no main-cd assert and no clocked content).

#[test]
fn assert_cd_only_module_zero_port_header() {
    let output = assert_ok(r#"
module aBareCd {
    assertCd(Bool.mk(None, literal(1)), "never fires", ClockDomain.mk "clk2" "reset2" Async RisingEdge ActiveHigh)
}
println(moduleTreeVL(aBareCd.create.tree))
println(moduleJsonFull(headModuleDef(aBareCd.create.tree.data)))
"#);
    // the header opens the port list directly with the extra-cd clk — no
    // leading comma, no `module X ()` empty-header fallback
    assert!(
        output.contains("module aBareCd (\n  input wire clk2\n);"),
        "zero-port module header must start with the extra-cd clk port (no leading comma), got: {}",
        output
    );
    assert!(output.contains("always @(posedge clk2) begin"), "extra-cd assert block, got: {}", output);
    // the manifest lists exactly the one synthesized port
    assert!(
        output.contains("\"ports\": [{\"name\": \"clk2\", \"dir\": \"input\", \"width\": 1, \"signed\": false, \"reg\": false}]"),
        "manifest port list must be exactly the extra-cd clk, got: {}", output
    );
    assert!(!output.contains("\"name\": \"clk\""), "no main-domain clk port for an assertCd-only module, got: {}", output);
}
