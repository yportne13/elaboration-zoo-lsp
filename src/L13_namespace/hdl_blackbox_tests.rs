// ============================================================
// HDL BlackBox tests (docs/hdl-blackbox-sim-design.md §4, P2)
//
// The `blackbox` macro (hdl-macros.typort) expands to the module macro's
// plain-arm sandwich (same port factories / ModuleRegistry / self-check
// registration) plus two blackbox-only effects:
//   - `generic K = v` lines land in the "BlackBoxCtx" global, and the
//     (name -> generics) pair is registered in "BlackBoxRegistry" before
//     checkModuleTree runs (DEVIATION from §4.2: a parallel registry global
//     instead of a ModuleDef.bb field — see hdl-core.typort).
//   - hdl-verilog emits the `ifndef-guarded empty stub for the def carrying
//     the blackbox SELF marker and injects `#(.K(v))` at instantiation sites
//     (the parameter strings are rendered at CREATE time by hdl-macros and
//     transported as the dedicated bbMarkerExpr(isInst, params) Expr variant —
//     the emission chain is PURE: any reachable global op trips the
//     pre-existing lvl2ix drain bug,
//     docs/l13-typeclass-instance-nat-param-bug.md).
//
// Behavior pinned here (L1 self-check + L2 shape; the sim-level close-up with
// a hand-written behavior model lives in tests/sim_tests.rs, per design §5.1):
//   - blackbox declaration  -> `ifndef TYPORT_BB_<Name>` + `#(parameter ...)
//     stub + declared port directions/widths, no synthesized clk/reset
//   - instantiation         -> zero new Expr variants; `#(.WIDTH(8), ...)`
//     injected from the marker the declaration left in the parent def
//   - self-check            -> port table covers the blackbox (HDL020/021/022
//     fire as usual) while the body rules are gated (no HDL003 for the
//     undriven blackbox output)
//   - mixed hierarchy       -> blackbox instances and plain module instances
//     coexist in one design
//   - manifest              -> the blackbox module JSON carries exactly its
//     declared ports (no synthesized clock ports), instances carry no
//     parameter values (sim tools don't need them, design §4.3)
// ============================================================

use super::*;

fn assert_ok(input: &str) -> String {
    match run_with_prelude(input) {
        Ok(output) => output,
        Err(e) => panic!("expected OK, got error: '{}' @ {}:{}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

// The SyncRam declaration from design §7.2, reused by several tests below.
// Port groups follow the macro's contiguous-run pattern (generics, Bool,
// typed, Bool) — see the blackbox macro arms in hdl-macros.typort.
const SYNC_RAM_DECL: &str = r#"
blackbox SyncRam[depth: Nat, w: Nat]
    generic WIDTH = w
    generic DEPTH = depth
    input  clk  = Bool
    input  we   = Bool
    input  addr = UInt[log2Up depth]
    input  din  = UInt[w]
    output dout = UInt[w]
{
}
"#;

// ── declaration: guarded empty stub with parameters and port directions ──

#[test]
fn blackbox_decl_emits_guarded_stub() {
    let output = assert_ok(&format!(
        r#"{}
println(moduleTreeVL(SyncRam.create[64, 8].tree))
"#,
        SYNC_RAM_DECL
    ));
    // `ifndef guard pair (a hand-written behavior model defining
    // TYPORT_BB_SyncRam replaces the stub without duplicate-module errors)
    assert!(output.contains("`ifndef TYPORT_BB_SyncRam"), "ifndef guard, got: {}", output);
    assert!(output.contains("`endif"), "endif guard, got: {}", output);
    // parameterized header
    assert!(
        output.contains("module SyncRam #(parameter WIDTH = 8, parameter DEPTH = 64) ("),
        "parameterized stub header, got: {}", output
    );
    // port directions and widths (Bool ports 1-bit, param-driven widths)
    assert!(output.contains("input wire clk"), "clk port, got: {}", output);
    assert!(output.contains("input wire we"), "we port, got: {}", output);
    assert!(output.contains("input wire [5:0] addr"), "addr width log2Up(64)=6, got: {}", output);
    assert!(output.contains("input wire [7:0] din"), "din width, got: {}", output);
    assert!(output.contains("output wire [7:0] dout"), "dout width, got: {}", output);
    // empty body: no storage/logic sections leak into the stub
    assert!(output.contains("endmodule"), "endmodule, got: {}", output);
    assert!(!output.contains("always"), "no always block in a stub, got: {}", output);
    assert!(!output.contains("assign"), "no assigns in a stub, got: {}", output);
    // no synthesized clk/reset ports (design §4.3): the port list holds
    // exactly the five declared ports
    assert!(!output.contains("input wire reset"), "no synthesized reset, got: {}", output);
    let clk_count = output.matches("input wire clk").count();
    assert_eq!(clk_count, 1, "exactly the declared clk, got: {}", output);
}

// ── port group order: typed ports may precede the Bool ports ──

#[test]
fn blackbox_typed_ports_before_bool_ports() {
    let output = assert_ok(r#"
blackbox TypedFirst[w: Nat]
    generic W = w
    input data = UInt[w]
    output q = UInt[w]
    input clk = Bool
{
}
println(moduleTreeVL(TypedFirst.create[8].tree))
"#);
    assert!(
        output.contains("module TypedFirst #(parameter W = 8) ("),
        "header, got: {}", output
    );
    assert!(output.contains("input wire [7:0] data"), "typed port, got: {}", output);
    assert!(output.contains("input wire clk"), "Bool port after typed ports, got: {}", output);
}

// ── generic-less blackbox: bare module header, bare instantiation ──

#[test]
fn blackbox_genericless_has_no_parameter_syntax() {
    let output = assert_ok(r#"
blackbox ToyLock
    input clk = Bool
    input key = UInt[8]
{
}
println(moduleTreeVL(ToyLock.create.tree))
"#);
    assert!(output.contains("module ToyLock ("), "bare header without #(...), got: {}", output);
    assert!(!output.contains("parameter"), "no parameter keyword, got: {}", output);
}

// ── instantiation: parameter injection rendered at create time ──

#[test]
fn blackbox_instance_injects_params() {
    // NOTE: concrete (literal-generic) blackbox + non-parameterized parent.
    // A PARAMETERIZED def inside a designVL closure trips a PRE-EXISTING
    // engine bug (lvl2ix at the println nf - reproduced at HEAD with a plain
    // parametric module, no blackbox involved; same limitation the P1 assert
    // batch worked around in examples/hdl/26-assert.typort). The
    // declaration-level tests pin the parameterized shape via moduleTreeVL,
    // which is unaffected; examples/hdl/27-blackbox.typort is the
    // moduleTreeVL end-to-end (see its NOTE).
    let output = assert_ok(r#"
blackbox SyncRamC
    generic WIDTH = 8
    generic DEPTH = 64
    input  clk  = Bool
    input  we   = Bool
    input  addr = UInt[6]
    input  din  = UInt[8]
    output dout = UInt[8]
{
}
module ramWrap {
    input clk = Bool
    input we = Bool
    input addr = UInt[6]
    input din = UInt[8]
    output dout = UInt[8]
    let ram = SyncRamC.create
    ram.clk := clk
    ram.we := we
    ram.addr := addr
    ram.din := din
    dout := ram.dout
}
println(moduleTreeVL(ramWrap.create.tree))
"#);
    // instantiation site: the name carries the #(...) parameters from the
    // declared generic statements, then the instance name and the usual
    // .port(sig) connections
    assert!(
        output.contains("SyncRamC #(.WIDTH(8), .DEPTH(64)) ram (.clk(clk), .we(we), .addr(addr), .din(din), .dout(dout));"),
        "parameterized instance line, got: {}", output
    );
    // the parent module itself is emitted as a plain module (the blackbox stub
    // is its own def, emitted by the declaration-level path above and by
    // designVL in examples/hdl/27-blackbox.typort)
    assert!(output.contains("module ramWrap ("), "plain parent header, got: {}", output);
}

// ── generic-less instantiation stays bare ──

#[test]
fn blackbox_genericless_instance_has_no_params() {
    let output = assert_ok(r#"
blackbox ToyLock
    input clk = Bool
    input key = UInt[8]
{
}
module lockUser {
    input clk = Bool
    let u = ToyLock.create
    u.clk := clk
}
println(moduleTreeVL(lockUser.create.tree))
"#);
    assert!(
        output.contains("ToyLock u (.clk(clk));"),
        "bare instance line without #(...), got: {}", output
    );
}

// ── self-check: the blackbox body rules are gated (no HDL003) ──

#[test]
fn blackbox_output_ports_not_flagged_undriven() {
    // The blackbox has an output port and no body: without the §4.4 gating
    // every create would report HDL003 for dout.
    let output = assert_ok(&format!(
        r#"{}
let t = SyncRam.create[64, 8]
println("created")
"#,
        SYNC_RAM_DECL
    ));
    assert!(!output.contains("HDL003"), "blackbox output must not be flagged undriven, got: {}", output);
    assert!(!output.contains("HDL001"), "no dangling-read false positive, got: {}", output);
    assert!(!output.contains("HDL002"), "no unused-decl false positive, got: {}", output);
}

#[test]
fn plain_module_still_reports_hdl003() {
    // Control for the gating above: a regular module with an undriven output
    // must keep reporting HDL003 while the blackbox's own undriven output
    // (dout) stays silent (the gate keys on the blackbox SELF marker —
    // chkBbDefIsBlackBox over the def's bbMarkerExpr(isInst=false, ...) node —
    // not on the mere absence of drives, and never on the registry name).
    // No create call: the module class declaration's own check round is what
    // reports (same shape as the existing legacy_tests::test_hdl_check_out_undriven case).
    let output = assert_ok(r#"
blackbox BbControl
    input  clk  = Bool
    output dout = UInt[8]
{
}
module noDrive[w: Nat]
    output z = UInt[w]
{
    let a = UInt[w]
    a := 1
}
"#);
    assert!(
        output.contains("HDL003 [noDrive] z"),
        "plain module undriven output still reported, got: {}", output
    );
    assert!(
        !output.contains("HDL003 [BbControl]"),
        "blackbox output stays gated, got: {}", output
    );
}

// ── P1 aliasing regression (R2 review): user constant-Bool asserts are NOT ──
// ── blackbox parameter markers                                             ──
//
// The marker channel originally piggybacked on
// assertExpr(literal(zero|succ(zero)), <params>, AssertError) — byte-identical
// to a user constant Bool assertion (Boolean.into → Bool.mk(None,
// literal(bool_to_nat ...))). Repro #1: `assert(false.into, msg)` made
// bbIsBlackBox replace the whole module body with a malformed stub. Repro #2:
// `assert(true.into, "sanity")` right before a sub-module create made
// collectInstHelp consume the assert as the INSTANCE parameter marker,
// polluting the instance name (`<module><msg> u (...)`) and swallowing the
// assertion. The dedicated bbMarkerExpr variant ends the aliasing; these two
// tests pin the reviewer's exact repro shapes as negative cases.

#[test]
fn plain_module_bool_literal_assert_is_not_a_blackbox() {
    // Repro #1 (SELF-marker alias): the module must keep its normal body and
    // its user assert — no guarded stub, no msg hijacked as a parameter string.
    let output = assert_ok(r#"
module plainMarker {
    input a = Bool
    output y = Bool
    y := a
    assert(false.into, "parameter X = 1")
}
println(moduleTreeVL(plainMarker.create.tree))
"#);
    assert!(!output.contains("`ifndef"), "no blackbox stub guard, got: {}", output);
    assert!(output.contains("module plainMarker ("), "plain module header, got: {}", output);
    assert!(output.contains("assign y = a;"), "module body emitted, got: {}", output);
    // the user assert survives verbatim in the translate-off block
    assert!(
        output.contains("$display(\"TYPORT_ASSERT_ERROR %0t %m: parameter X = 1\", $time);"),
        "user assert emitted, got: {}", output
    );
    assert!(!output.contains("#(parameter"), "no stub #(...) header, got: {}", output);
    assert!(!output.contains("endmodule\n`endif"), "no stub guard pair, got: {}", output);
}

#[test]
fn plain_module_bool_literal_assert_does_not_pollute_instance() {
    // Repro #2 (INSTANCE-marker alias): the assert sits right before the
    // create, i.e. immediately AFTER the instance node in walk order (prepend
    // order) — exactly where the blackbox INSTANCE marker is picked up. The
    // instance line must stay clean and the assert must still be emitted.
    // (The child declares its ports in the HEADER — in-body ports are
    // module-internal signals with no connectable u.x handle, design §4.5-6.)
    let output = assert_ok(r#"
module inv
    input a = Bool
    output y = Bool
{
    y := !a
}
module markerUser {
    input a = Bool
    output y = Bool
    assert(true.into, "sanity")
    let u = inv.create
    u.a := a
    y := u.y
}
println(moduleTreeVL(markerUser.create.tree))
"#);
    // instance line unpolluted (the old shape was `invsanity u (.a(a), .y(y));`)
    assert!(output.contains("inv u (.a(a), .y(y));"), "clean instance line, got: {}", output);
    assert!(!output.contains("invsanity"), "instance name not polluted by the msg, got: {}", output);
    // the user assert still lands in the translate-off block (not consumed as
    // an instance parameter marker)
    assert!(
        output.contains("TYPORT_ASSERT_ERROR %0t %m: sanity"),
        "user assert still emitted, got: {}", output
    );
}

// ── self-check: port table covers blackbox instances (HDL020/021/022) ──

#[test]
fn blackbox_unconnected_port_reports_hdl022() {
    // design §7.2: commenting out `ram.din := din` must report HDL022 —
    // ruleInstPorts consults the port table the blackbox registered.
    let output = assert_ok(&format!(
        r#"{}
module ramWrapMissing[w: Nat] {{
    input clk = Bool
    input we = Bool
    input addr = UInt[log2Up w]
    input din = UInt[w]
    output dout = UInt[w]
    let ram = SyncRam.create[w, w]
    ram.clk := clk
    ram.we := we
    ram.addr := addr
    dout := ram.dout
}}
println("checked")
"#,
        SYNC_RAM_DECL
    ));
    assert!(output.contains("HDL022"), "unconnected blackbox port reported, got: {}", output);
    assert!(output.contains("ram.din"), "names the unconnected port, got: {}", output);
}

#[test]
fn blackbox_direction_rules_still_fire() {
    // HDL020: parent drives a child OUTPUT port (dout) — the connection is
    // legal tyck-wise (subSignal handle) but flagged by the direction table.
    let output = assert_ok(&format!(
        r#"{}
module drivesBbOut {{
    input clk = Bool
    output x = UInt[8]
    let ram = SyncRam.create[64, 8]
    ram.dout := x
}}
println("checked")
"#,
        SYNC_RAM_DECL
    ));
    assert!(output.contains("HDL020"), "driving a blackbox output flagged, got: {}", output);
    // HDL021: parent reads a child INPUT port.
    let output2 = assert_ok(&format!(
        r#"{}
module readsBbIn {{
    input clk = Bool
    input we = Bool
    input addr = UInt[6]
    let y = UInt[6]
    let ram = SyncRam.create[64, 8]
    y := ram.addr
}}
println("checked")
"#,
        SYNC_RAM_DECL
    ));
    assert!(output2.contains("HDL021"), "reading a blackbox input flagged, got: {}", output2);
}

// ── mixed hierarchy: plain modules and blackboxes coexist ──

#[test]
fn blackbox_mixed_hierarchy_with_plain_module() {
    // Concrete blackbox (see blackbox_instance_injects_params: a parameterized
    // def inside a designVL closure trips a PRE-EXISTING engine lvl2ix).
    // NOTE: the plain child `inverter` declares its ports in the HEADER — an
    // in-body `input x = Bool` is a module-internal signal with no connectable
    // `u.x` handle (documented on the module macro), so the parent could not
    // connect to it. The blackbox macro has no in-body arm: its ports are
    // always header-declared and therefore always connectable.
    let output = assert_ok(r#"
blackbox SyncRamC
    generic WIDTH = 8
    generic DEPTH = 64
    input  clk  = Bool
    input  we   = Bool
    input  addr = UInt[6]
    input  din  = UInt[8]
    output dout = UInt[8]
{
}
module inverter
    input a = Bool
    output y = Bool
{
    y := !a
}
module mixedTop {
    input clk = Bool
    input a = Bool
    input we = Bool
    input addr = UInt[6]
    input din = UInt[8]
    output dout = UInt[8]
    output inv = Bool
    let uInv = inverter.create
    uInv.a := a
    inv := uInv.y
    let uRam = SyncRamC.create
    uRam.clk := clk
    uRam.we := we
    uRam.addr := addr
    uRam.din := din
    dout := uRam.dout
}
println(moduleTreeVL(mixedTop.create.tree))
println(moduleTreeVL(inverter.create.tree))
println(moduleTreeVL(SyncRamC.create.tree))
"#);
    // plain module instance: no parameters, connections from the handles
    assert!(output.contains("inverter uInv (.a(a), .y(inv));"), "plain instance, got: {}", output);
    // blackbox instance: parameters injected
    assert!(
        output.contains("SyncRamC #(.WIDTH(8), .DEPTH(64)) uRam (.clk(clk), .we(we), .addr(addr), .din(din), .dout(dout));"),
        "blackbox instance, got: {}", output
    );
    // the plain child's body is emitted, the blackbox def stays a guarded stub
    assert!(output.contains("assign y = !a;"), "plain child body, got: {}", output);
    assert!(output.contains("`ifndef TYPORT_BB_SyncRamC"), "blackbox stub in the same design, got: {}", output);
}

// ── manifest: declared ports only; instances carry no parameter values ──

#[test]
fn blackbox_manifest_lists_declared_ports() {
    // Exercised through moduleJsonFull(headModuleDef(...)) — the renderer
    // designManifestVL dispatches to (same pattern as the assert tests; the
    // end-to-end manifest path is covered by tests/sim_tests.rs).
    let output = assert_ok(&format!(
        r#"{}
println(moduleTreeVL(SyncRam.create[64, 8].tree))
println(moduleJsonFull(headModuleDef(SyncRam.create[64, 8].tree.data)))
"#,
        SYNC_RAM_DECL
    ));
    // every declared port is listed with its direction/width…
    assert!(
        output.contains("{\"name\": \"clk\", \"dir\": \"input\", \"width\": 1"),
        "manifest clk port, got: {}", output
    );
    assert!(
        output.contains("{\"name\": \"addr\", \"dir\": \"input\", \"width\": 6"),
        "manifest addr port (log2Up 64), got: {}", output
    );
    assert!(
        output.contains("{\"name\": \"dout\", \"dir\": \"output\", \"width\": 8"),
        "manifest dout port, got: {}", output
    );
    // …and nothing is synthesized: a blackbox stub has no clock/reset ports
    assert!(
        output.contains("\"ports\": [{\"name\": \"dout\", \"dir\": \"output\", \"width\": 8, \"signed\": false, \"reg\": false}, {\"name\": \"din\", \"dir\": \"input\", \"width\": 8, \"signed\": false, \"reg\": false}, {\"name\": \"addr\", \"dir\": \"input\", \"width\": 6, \"signed\": false, \"reg\": false}, {\"name\": \"we\", \"dir\": \"input\", \"width\": 1, \"signed\": false, \"reg\": false}, {\"name\": \"clk\", \"dir\": \"input\", \"width\": 1, \"signed\": false, \"reg\": false}]"),
        "manifest port list is exactly the declared five, got: {}", output
    );
}

#[test]
fn blackbox_instance_manifest_has_no_params() {
    // design §4.3: instJsonSingle carries no parameter values (sim tools
    // don't need them).
    let output = assert_ok(&format!(
        r#"{}
module ramWrapM {{
    input clk = Bool
    input we = Bool
    input addr = UInt[6]
    input din = UInt[8]
    output dout = UInt[8]
    let ram = SyncRam.create[64, 8]
    ram.clk := clk
    ram.we := we
    ram.addr := addr
    ram.din := din
    dout := ram.dout
}}
println(moduleJsonFull(headModuleDef(ramWrapM.create.tree.data)))
"#,
        SYNC_RAM_DECL
    ));
    assert!(
        output.contains("{\"inst\": \"ram\", \"module\": \"SyncRam\"}"),
        "instance JSON without parameter values, got: {}", output
    );
}
