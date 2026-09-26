// Verilator simulation pipeline integration tests.
//
// These compile a real model with verilator + make, so they are skipped
// (not failed) when the tools are not installed — same policy as
// tools/spinalhdl-verify/verify.py.

use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::Duration;

use elaboration_zoo_lsp::sim::{find_iverilog, find_verilator, Dut, SimConfig, Simulator};

fn example_path(name: &str) -> PathBuf {
    PathBuf::from(format!("{}/examples/hdl/{name}", env!("CARGO_MANIFEST_DIR")))
}

fn case_path(name: &str) -> PathBuf {
    PathBuf::from(format!("{}/tools/spinalhdl-verify/cases/{name}", env!("CARGO_MANIFEST_DIR")))
}

fn workdir(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "typort-sim-tests-{}-{tag}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// A live model process speaking the harness line protocol (raw, without
/// the Dut wrapper — used by the pipeline tests).
struct Model {
    stdin: std::process::ChildStdin,
    stdout: BufReader<std::process::ChildStdout>,
    child: std::process::Child,
}

impl Model {
    fn spawn(exe: &std::path::Path) -> Self {
        let mut child = Command::new(exe)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .expect("spawn model");
        let stdin = child.stdin.take().unwrap();
        let stdout = BufReader::new(child.stdout.take().unwrap());
        Model { stdin, stdout, child }
    }

    fn cmd(&mut self, line: &str) -> String {
        self.stdin.write_all(line.as_bytes()).unwrap();
        self.stdin.write_all(b"\n").unwrap();
        self.stdin.flush().unwrap();
        let mut out = String::new();
        self.stdout.read_line(&mut out).expect("model response");
        out.trim_end().to_string()
    }

    fn finish(mut self) {
        let _ = self.stdin.write_all(b"finish\n");
        let _ = self.stdin.flush();
        let _ = self.child.wait();
    }
}

// ---------------------------------------------------------------------------
// Commit-3 pipeline tests (raw protocol)
// ---------------------------------------------------------------------------

#[test]
fn compile_and_drive_hierarchy_model() {
    if find_verilator().is_none() {
        eprintln!("[SKIP] verilator not found — sim integration unavailable");
        return;
    }
    let cfg = SimConfig {
        top: "topWithPorts".to_string(),
        sources: vec![example_path("09-hierarchy.typort")],
        workdir: workdir("hierarchy"),
        simulator: Simulator::Verilator,
        verilator_args: vec![],
        trace: false,
    };
    let model = cfg.compile().expect("compile model");
    assert!(model.exe.is_file(), "model exe at {}", model.exe.display());

    let mut m = Model::spawn(&model.exe);
    assert_eq!(m.cmd("set a 03"), "ok");
    assert_eq!(m.cmd("set b 05"), "ok");
    assert_eq!(m.cmd("set en 1"), "ok");
    assert_eq!(m.cmd("eval"), "ok");
    assert_eq!(m.cmd("get sum"), "8");
    // an unknown port must be rejected, not silently ignored
    assert!(m.cmd("get nosuch").starts_with("ERR"));
    m.finish();
}

#[test]
fn compile_param_top_bakes_width() {
    if find_verilator().is_none() {
        eprintln!("[SKIP] verilator not found — sim integration unavailable");
        return;
    }
    let cfg = SimConfig {
        top: "basicDecls[8]".to_string(),
        sources: vec![example_path("01-basics.typort")],
        workdir: workdir("param"),
        simulator: Simulator::Verilator,
        verilator_args: vec![],
        trace: false,
    };
    let model = cfg.compile().expect("compile model");
    let top = model.manifest.top_module().expect("top in manifest");
    assert_eq!(top.name, "basicDecls");
    // x is an 8-bit input of the parameterized module
    let x = top.port("x").expect("port x");
    assert_eq!(x.width, 8);
    assert!(model.exe.is_file());
}

// ---------------------------------------------------------------------------
// Dut API tests
// ---------------------------------------------------------------------------

#[test]
fn dut_validates_ports_and_widths() {
    if find_verilator().is_none() {
        eprintln!("[SKIP] verilator not found — sim integration unavailable");
        return;
    }
    let cfg = SimConfig {
        top: "topWithPorts".to_string(),
        sources: vec![example_path("09-hierarchy.typort")],
        workdir: workdir("dut-validate"),
        simulator: Simulator::Verilator,
        verilator_args: vec![],
        trace: false,
    };
    let model = cfg.compile().expect("compile model");
    let mut dut = Dut::spawn(&model).expect("spawn dut");

    // unknown port
    assert!(dut.set("nosuch", 1).is_err());
    // output port is not drivable
    assert!(dut.set("sum", 1).is_err());
    // input port is not readable
    assert!(dut.get("a").is_err());
    // value wider than the 8-bit port
    assert!(dut.set("a", 0x100).is_err());
    // max representable value fits; 8-bit sum truncates (HDL wrap).
    // myAdder's `en` is a real enable now (it used to be a dead input the
    // HDL checker flagged): drive it high, or the adder output passes `a`.
    dut.set("a", 0xff).unwrap().set("b", 2).unwrap().set("en", 1).unwrap().eval().unwrap();
    assert_eq!(dut.get("sum").unwrap(), 0x01);
    dut.set("a", 0x0f).unwrap().set("b", 2).unwrap().set("en", 1).unwrap().eval().unwrap();
    assert_eq!(dut.get("sum").unwrap(), 0x11);
    dut.finish().unwrap();
}

/// counterOut (examples/hdl/17-output-reg): `output reg count = UInt[8] init 0`
/// plus `input en`, auto clk/reset ports, async active-high reset. Exercises
/// the full SpinalSim-style sequence: fork clock → reset → release → count
/// edges → assert register state.
#[test]
fn dut_counter_with_reset_sequence() {
    if find_verilator().is_none() {
        eprintln!("[SKIP] verilator not found — sim integration unavailable");
        return;
    }
    let cfg = SimConfig {
        top: "counterOut".to_string(),
        sources: vec![example_path("17-output-reg.typort")],
        workdir: workdir("counter"),
        simulator: Simulator::Verilator,
        verilator_args: vec![],
        trace: false,
    };
    let model = cfg.compile().expect("compile model");
    let mut dut = Dut::spawn(&model).expect("spawn dut");

    let clk_port = model.manifest.top_module().unwrap().clock.clk.clone();
    let reset_port = model.manifest.top_module().unwrap().clock.reset.clone();
    assert_eq!(clk_port, "clk");

    let clock = dut.clock_named(&clk_port);
    clock.fork(Duration::from_millis(2));

    // async reset: assert, let a few edges pass, verify count is held at 0
    dut.set(&reset_port, 1).unwrap().set("en", 1).unwrap();
    dut.wait_edges(3);
    assert_eq!(dut.get("count").unwrap(), 0, "count must stay 0 under reset");

    // release reset; count increments on every enabled posedge. One extra
    // boundary edge may slip between the release and the wait_edges sample
    // (both are lock-atomic, but their ORDER isn't) — hence the tolerance.
    dut.set(&reset_port, 0).unwrap();
    dut.wait_edges(5);
    let counted = dut.get("count").unwrap();
    assert!((5..=6).contains(&counted), "count after 5 enabled edges: {counted}");

    // gate: en=0 freezes the counter
    dut.set("en", 0).unwrap();
    dut.wait_edges(4);
    assert_eq!(dut.get("count").unwrap(), counted);

    dut.finish().unwrap();
}

/// flag toggles on every enabled posedge — checked on a SECOND Dut instance
/// with manual clocking (no stimulus thread): fully deterministic edge count.
#[test]
fn dut_flag_toggles_manual_clock() {
    if find_verilator().is_none() {
        eprintln!("[SKIP] verilator not found — sim integration unavailable");
        return;
    }
    let cfg = SimConfig {
        top: "counterOut".to_string(),
        sources: vec![example_path("17-output-reg.typort")],
        workdir: workdir("flag"),
        simulator: Simulator::Verilator,
        verilator_args: vec![],
        trace: false,
    };
    let model = cfg.compile().expect("compile model");
    let mut dut = Dut::spawn(&model).expect("spawn dut");
    // clean low start
    dut.set("clk", 0).unwrap().set("en", 0).unwrap().set("reset", 0).unwrap().eval().unwrap();
    // 3 enabled posedges → flag (zero-initialized) flips 3 times → 1
    dut.set("en", 1).unwrap();
    for _ in 0..3 {
        dut.set("clk", 1).unwrap().eval().unwrap();
        dut.set("clk", 0).unwrap().eval().unwrap();
    }
    assert_eq!(dut.get("flag").unwrap(), 1);
    // gated: no further flips
    dut.set("en", 0).unwrap();
    for _ in 0..2 {
        dut.set("clk", 1).unwrap().eval().unwrap();
        dut.set("clk", 0).unwrap().eval().unwrap();
    }
    assert_eq!(dut.get("flag").unwrap(), 1);
    dut.finish().unwrap();
}

/// Golden equivalence, ported from tools/spinalhdl-verify (ref_reverse):
/// vReverse reverses the bits of an 8-bit input.
#[test]
fn dut_golden_reverse() {
    if find_verilator().is_none() {
        eprintln!("[SKIP] verilator not found — sim integration unavailable");
        return;
    }
    let cfg = SimConfig {
        top: "vReverse".to_string(),
        sources: vec![case_path("v_utils_combinational.typort")],
        workdir: workdir("golden-reverse"),
        simulator: Simulator::Verilator,
        verilator_args: vec![],
        trace: false,
    };
    let model = cfg.compile().expect("compile model");
    let mut dut = Dut::spawn(&model).expect("spawn dut");
    let reverse = |a: u64| (0..8).fold(0u64, |acc, i| acc | (((a >> i) & 1) << (7 - i)));
    for a in [0u64, 1, 0x80, 0xaa, 0x5a, 0xff, 0x0f, 0x96] {
        let want = reverse(a);
        dut.set("a", a).unwrap().eval().unwrap();
        assert_eq!(dut.get("r").unwrap(), want, "reverse({a:#04x})");
    }
    dut.finish().unwrap();
}

/// Golden equivalence, ported from tools/spinalhdl-verify (ref_popcount):
/// vCountOne counts set bits.
#[test]
fn dut_golden_popcount() {
    if find_verilator().is_none() {
        eprintln!("[SKIP] verilator not found — sim integration unavailable");
        return;
    }
    let cfg = SimConfig {
        top: "vCountOne".to_string(),
        sources: vec![case_path("v_utils_combinational.typort")],
        workdir: workdir("golden-popcount"),
        simulator: Simulator::Verilator,
        verilator_args: vec![],
        trace: false,
    };
    let model = cfg.compile().expect("compile model");
    let mut dut = Dut::spawn(&model).expect("spawn dut");
    for a in [0u64, 1, 3, 0x0f, 0x81, 0xff, 0x55, 0xa7] {
        let want = a.count_ones() as u64;
        dut.set("a", a).unwrap().eval().unwrap();
        assert_eq!(dut.get("c").unwrap(), want, "popcount({a:#04x})");
    }
    dut.finish().unwrap();
}

/// Compiling with trace must produce a VCD in the workdir.
#[test]
fn dut_wave_trace_produces_vcd() {
    if find_verilator().is_none() {
        eprintln!("[SKIP] verilator not found — sim integration unavailable");
        return;
    }
    let cfg = SimConfig {
        top: "counterOut".to_string(),
        sources: vec![example_path("17-output-reg.typort")],
        workdir: workdir("trace"),
        simulator: Simulator::Verilator,
        verilator_args: vec![],
        trace: true,
    };
    let model = cfg.compile().expect("compile model");
    let mut dut = Dut::spawn(&model).expect("spawn dut");
    dut.clock().fork(Duration::from_millis(2));
    dut.set("en", 1).unwrap();
    dut.wait_edges(6);
    dut.finish().unwrap();

    let wave = model.workdir.join("wave.vcd");
    assert!(wave.is_file(), "no wave.vcd at {}", wave.display());
    let text = std::fs::read_to_string(&wave).unwrap();
    assert!(text.contains("$enddefinitions"), "not a VCD file");
    assert!(text.contains("clk"), "clock signal missing from trace");
}

// ---------------------------------------------------------------------------
// Icarus Verilog backend — same design, same Dut API, different simulator.
// The golden vectors match the verilator runs above, cross-checking both
// the backend and the emitted Verilog itself.
// ---------------------------------------------------------------------------

#[test]
fn icarus_compiles_and_drives_hierarchy_model() {
    if find_iverilog().is_none() {
        eprintln!("[SKIP] iverilog not found — icarus backend unavailable");
        return;
    }
    let cfg = SimConfig {
        top: "topWithPorts".to_string(),
        sources: vec![example_path("09-hierarchy.typort")],
        workdir: workdir("icarus-hierarchy"),
        simulator: Simulator::Icarus,
        verilator_args: vec![],
        trace: false,
    };
    let model = cfg.compile().expect("compile model (icarus)");
    let mut dut = Dut::spawn(&model).expect("spawn dut");
    assert_eq!(
        dut.set("a", 3).unwrap().set("b", 5).unwrap().set("en", 1).unwrap().eval().unwrap().get("sum").unwrap(),
        8
    );
    dut.finish().unwrap();
}

#[test]
fn icarus_golden_popcount_cross_checks_verilator() {
    if find_iverilog().is_none() {
        eprintln!("[SKIP] iverilog not found — icarus backend unavailable");
        return;
    }
    let cfg = SimConfig {
        top: "vCountOne".to_string(),
        sources: vec![case_path("v_utils_combinational.typort")],
        workdir: workdir("icarus-popcount"),
        simulator: Simulator::Icarus,
        verilator_args: vec![],
        trace: false,
    };
    let model = cfg.compile().expect("compile model (icarus)");
    let mut dut = Dut::spawn(&model).expect("spawn dut");
    for a in [0u64, 1, 3, 0x0f, 0x81, 0xff, 0x55, 0xa7] {
        let want = a.count_ones() as u64;
        dut.set("a", a).unwrap().eval().unwrap();
        assert_eq!(dut.get("c").unwrap(), want, "icarus popcount({a:#04x})");
    }
    dut.finish().unwrap();
}

/// Sequential design through the event-driven harness: manual clocking via
/// the same set/eval protocol (the #1 inside the harness's eval/get settles
/// nonblocking assignments before the response).
#[test]
fn icarus_counter_manual_clock() {
    if find_iverilog().is_none() {
        eprintln!("[SKIP] iverilog not found — icarus backend unavailable");
        return;
    }
    let cfg = SimConfig {
        top: "counterOut".to_string(),
        sources: vec![example_path("17-output-reg.typort")],
        workdir: workdir("icarus-counter"),
        simulator: Simulator::Icarus,
        verilator_args: vec![],
        trace: false,
    };
    let model = cfg.compile().expect("compile model (icarus)");
    let mut dut = Dut::spawn(&model).expect("spawn dut");
    // async reset holds the count, then release and count 5 enabled edges
    dut.set("reset", 1).unwrap().set("en", 1).unwrap().set("clk", 0).unwrap().eval().unwrap();
    for _ in 0..2 {
        dut.set("clk", 1).unwrap().eval().unwrap();
        dut.set("clk", 0).unwrap().eval().unwrap();
    }
    assert_eq!(dut.get("count").unwrap(), 0, "count held under async reset (icarus)");
    dut.set("reset", 0).unwrap();
    for _ in 0..5 {
        dut.set("clk", 1).unwrap().eval().unwrap();
        dut.set("clk", 0).unwrap().eval().unwrap();
    }
    assert_eq!(dut.get("count").unwrap(), 5);
    dut.finish().unwrap();
}

/// VCD via $dumpvars in the generated Verilog harness.
#[test]
fn icarus_wave_trace_produces_vcd() {
    if find_iverilog().is_none() {
        eprintln!("[SKIP] iverilog not found — icarus backend unavailable");
        return;
    }
    let cfg = SimConfig {
        top: "counterOut".to_string(),
        sources: vec![example_path("17-output-reg.typort")],
        workdir: workdir("icarus-trace"),
        simulator: Simulator::Icarus,
        verilator_args: vec![],
        trace: true,
    };
    let model = cfg.compile().expect("compile model (icarus)");
    let mut dut = Dut::spawn(&model).expect("spawn dut");
    dut.set("en", 1).unwrap();
    for _ in 0..3 {
        dut.set("clk", 1).unwrap().eval().unwrap();
        dut.set("clk", 0).unwrap().eval().unwrap();
    }
    dut.finish().unwrap();
    let wave = model.workdir.join("wave.vcd");
    assert!(wave.is_file(), "no wave.vcd at {}", wave.display());
    let text = std::fs::read_to_string(&wave).unwrap();
    assert!(text.contains("$enddefinitions"), "not a VCD file");
    assert!(text.contains("clk"), "clock missing from trace");
}

// ---------------------------------------------------------------------------
// Design-side assertions (docs/hdl-blackbox-sim-design.md §7.1): the model's
// translate_off-wrapped always block $displays `TYPORT_ASSERT_*` marker lines;
// the Dut roundtrip captures them off stdout, so a behavioral violation inside
// the design surfaces as a host-side failure.
// ---------------------------------------------------------------------------

/// aCounter (examples/hdl/26-assert.typort): `assert(count < 100, ...)` plus a
/// when-wrapped `count >= 50` guard. Holding the counter below the guards must
/// keep the failure list empty (expect_no_asserts passes).
#[test]
fn typort_assert_pass_below_threshold() {
    if find_iverilog().is_none() {
        eprintln!("[SKIP] iverilog not found — icarus backend unavailable");
        return;
    }
    let cfg = SimConfig {
        top: "aCounter".to_string(),
        sources: vec![example_path("26-assert.typort")],
        workdir: workdir("assert-pass"),
        simulator: Simulator::Icarus,
        verilator_args: vec![],
        trace: false,
    };
    let model = cfg.compile().expect("compile model (icarus)");
    let mut dut = Dut::spawn(&model).expect("spawn dut");
    dut.set("reset", 1).unwrap().set("en", 1).unwrap().set("clk", 0).unwrap().eval().unwrap();
    dut.set("reset", 0).unwrap();
    // 40 enabled posedges → count == 40: the `count >= 50` guard branch is
    // still dormant below 50, and the top-level guard holds by a wide margin.
    for _ in 0..40 {
        dut.set("clk", 1).unwrap().eval().unwrap();
        dut.set("clk", 0).unwrap().eval().unwrap();
    }
    assert_eq!(dut.get("count").unwrap(), 40);
    dut.expect_no_asserts().expect("no assertion may fire below the guards");
    dut.finish().unwrap();
}

/// Violation capture: run count to 100, gate `en`, then take one more posedge
/// (the assertion samples the PRE-update count, so the violation lands on the
/// gated edge where count reads 100). The host captures the ERROR marker lines
/// — including the %m hierarchical instance path — while the model stays
/// responsive (marker + keep-running semantics, design doc §8).
#[test]
fn typort_assert_violation_captured() {
    if find_iverilog().is_none() {
        eprintln!("[SKIP] iverilog not found — icarus backend unavailable");
        return;
    }
    let cfg = SimConfig {
        top: "aCounter".to_string(),
        sources: vec![example_path("26-assert.typort")],
        workdir: workdir("assert-violation"),
        simulator: Simulator::Icarus,
        verilator_args: vec![],
        trace: false,
    };
    let model = cfg.compile().expect("compile model (icarus)");
    let mut dut = Dut::spawn(&model).expect("spawn dut");
    dut.set("reset", 1).unwrap().set("en", 1).unwrap().set("clk", 0).unwrap().eval().unwrap();
    dut.set("reset", 0).unwrap();
    for _ in 0..100 {
        dut.set("clk", 1).unwrap().eval().unwrap();
        dut.set("clk", 0).unwrap().eval().unwrap();
    }
    assert_eq!(dut.get("count").unwrap(), 100);
    assert!(dut.assert_failures().is_empty(), "no fire while count only READS 99 pre-update");
    dut.set("en", 0).unwrap();
    dut.set("clk", 1).unwrap().eval().unwrap();
    dut.set("clk", 0).unwrap().eval().unwrap();
    let failures = dut.assert_failures();
    // count is frozen at 100, so both guards sample 100 exactly once: the
    // unconditional top assert AND the when-wrapped half-way guard.
    assert_eq!(failures.len(), 2, "both guards fire once: {failures:?}");
    assert_eq!(
        failures.iter().filter(|l| l.contains("count overflow")).count(),
        1,
        "top-level assert marker: {failures:?}"
    );
    assert_eq!(
        failures.iter().filter(|l| l.contains("half-way guard")).count(),
        1,
        "when-wrapped assert folds into the same block: {failures:?}"
    );
    for line in &failures {
        assert!(line.starts_with("TYPORT_ASSERT_ERROR"), "severity tag: {line}");
        assert!(line.contains("tb_aCounter.dut"), "%m instance path present: {line}");
    }
    // the model is still alive: marker + keep-running (no $finish on ERROR)
    assert_eq!(dut.get("count").unwrap(), 100);
    dut.finish().unwrap();
}

/// assertCd end-to-end (assert P2-1 acceptance): the design manifest carries
/// the extra-domain `clk2` port, so the generated harness declares and
/// connects it and the Dut can drive the extra domain (`set clk2 ...`) —
/// before the mirror, the manifest lacked clk2 and the port floated (z), so
/// the cd2 assertion could never fire in simulation. The source is written
/// into the workdir from the test (examples/ stays untouched): a counter
/// with `assertCd(count < 2, ...)` on clk2. Running count up to 2, gating
/// en, then taking one posedge clk2 must capture the cd2 marker in
/// assert_failures — the extra domain behaves like the main one.
#[test]
fn typort_assert_cd_domain_captured() {
    if find_iverilog().is_none() {
        eprintln!("[SKIP] iverilog not found — icarus backend unavailable");
        return;
    }
    let dir = workdir("assert-cd");
    let src = dir.join("27-assert-cd.typort");
    std::fs::write(
        &src,
        r#"
module aCounterCd {
    input en = Bool
    output reg count = UInt[8] init 0
    when en { count := count + 1 }
    assertCd(count < 2, "cd2 overflow", ClockDomain.mk "clk2" "reset2" Async RisingEdge ActiveHigh)
}
"#,
    )
    .unwrap();
    let cfg = SimConfig {
        top: "aCounterCd".to_string(),
        sources: vec![src],
        workdir: dir.join("build"),
        simulator: Simulator::Icarus,
        verilator_args: vec![],
        trace: false,
    };
    let model = cfg.compile().expect("compile model (icarus)");
    // P2-1: the manifest lists the extra-domain clock port (input, 1 bit)
    // and — no init regs on that cd — no reset2.
    let top = model.manifest.top_module().expect("top in manifest");
    let clk2 = top.port("clk2").expect("manifest must carry the extra-domain clk2 port");
    assert_eq!(clk2.dir, "input");
    assert_eq!(clk2.width, 1);
    assert!(top.port("reset2").is_none(), "no reset2 without init regs on cd2");

    let mut dut = Dut::spawn(&model).expect("spawn dut");
    dut.set("reset", 1).unwrap().set("en", 1).unwrap().set("clk", 0).unwrap().set("clk2", 0).unwrap().eval().unwrap();
    dut.set("reset", 0).unwrap();
    // 2 enabled posedges on the MAIN clock → count == 2
    for _ in 0..2 {
        dut.set("clk", 1).unwrap().eval().unwrap();
        dut.set("clk", 0).unwrap().eval().unwrap();
    }
    assert_eq!(dut.get("count").unwrap(), 2);
    // no violation yet: the cd2 guard still holds
    assert!(dut.assert_failures().is_empty(), "cd2 guard holds at count 2");
    // gate en (count frozen at 2), then take ONE posedge on the EXTRA domain:
    // the cd2 assertion samples count == 2 and must fire there.
    dut.set("en", 0).unwrap();
    dut.set("clk2", 1).unwrap().eval().unwrap();
    dut.set("clk2", 0).unwrap().eval().unwrap();
    let failures = dut.assert_failures();
    assert_eq!(failures.len(), 1, "exactly the cd2 marker: {failures:?}");
    assert!(failures[0].contains("cd2 overflow"), "cd2 message: {failures:?}");
    assert!(failures[0].starts_with("TYPORT_ASSERT_ERROR"), "severity tag: {failures:?}");
    assert!(failures[0].contains("tb_aCounterCd.dut"), "%m instance path: {failures:?}");
    // the model stays alive (marker + keep-running on ERROR)
    assert_eq!(dut.get("count").unwrap(), 2);
    dut.finish().unwrap();
}

// ---------------------------------------------------------------------------
// VCS / Vivado backends — command shapes follow veryl's runners; both are
// UNTESTED here (no license/install on this machine) and skip when the
// tools are missing. Same Dut API and golden vector as the other backends.
// ---------------------------------------------------------------------------

fn untested_backend_golden(sim: Simulator, tag: &str) {
    let cfg = SimConfig {
        top: "topWithPorts".to_string(),
        sources: vec![example_path("09-hierarchy.typort")],
        workdir: workdir(tag),
        simulator: sim,
        verilator_args: vec![],
        trace: false,
    };
    let model = cfg.compile().expect("compile model");
    let mut dut = Dut::spawn(&model).expect("spawn dut");
    assert_eq!(
        dut.set("a", 3).unwrap().set("b", 5).unwrap().set("en", 1).unwrap().eval().unwrap().get("sum").unwrap(),
        8
    );
    dut.finish().unwrap();
}

#[test]
fn vcs_backend_smoke() {
    if elaboration_zoo_lsp::sim::find_vcs().is_none() {
        eprintln!("[SKIP] vcs not found — backend untested on this machine");
        return;
    }
    untested_backend_golden(Simulator::Vcs, "vcs-smoke");
}

#[test]
fn vivado_backend_smoke() {
    if elaboration_zoo_lsp::sim::find_vivado().is_none() {
        eprintln!("[SKIP] vivado (xsim) not found — backend untested on this machine");
        return;
    }
    untested_backend_golden(Simulator::Vivado, "vivado-smoke");
}
