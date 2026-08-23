// Verilator simulation pipeline integration tests.
//
// These compile a real model with verilator + make, so they are skipped
// (not failed) when the tools are not installed — same policy as
// tools/spinalhdl-verify/verify.py.

use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::Duration;

use elaboration_zoo_lsp::sim::{find_verilator, Dut, SimConfig};

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
    // max representable value fits; 8-bit sum truncates (HDL wrap)
    dut.set("a", 0xff).unwrap().set("b", 2).unwrap().eval().unwrap();
    assert_eq!(dut.get("sum").unwrap(), 0x01);
    dut.set("a", 0x0f).unwrap().set("b", 2).unwrap().eval().unwrap();
    assert_eq!(dut.get("sum").unwrap(), 0x11);
    dut.finish().unwrap();
}

/// counterOut (examples/hdl/15-output-reg): `output reg count = UInt[8] init 0`
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
        sources: vec![example_path("15-output-reg.typort")],
        workdir: workdir("counter"),
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
        sources: vec![example_path("15-output-reg.typort")],
        workdir: workdir("flag"),
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
        sources: vec![example_path("15-output-reg.typort")],
        workdir: workdir("trace"),
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
