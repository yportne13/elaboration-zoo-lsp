// Verilator simulation pipeline integration tests.
//
// These compile a real model with verilator + make, so they are skipped
// (not failed) when the tools are not installed — same policy as
// tools/spinalhdl-verify/verify.py.

use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};

use elaboration_zoo_lsp::sim::{find_verilator, SimConfig};

fn example_path(name: &str) -> PathBuf {
    PathBuf::from(format!("{}/examples/hdl/{name}", env!("CARGO_MANIFEST_DIR")))
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

/// A live model process speaking the harness line protocol.
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
    };
    let model = cfg.compile().expect("compile model");
    assert!(model.exe.is_file(), "model exe at {}", model.exe.display());

    let mut m = Model::spawn(&model.exe);
    assert_eq!(m.cmd("set a 03"), "ok");
    assert_eq!(m.cmd("set b 05"), "ok");
    assert_eq!(m.cmd("set en 1"), "ok");
    assert_eq!(m.cmd("eval"), "ok");
    // myAdder computes a + b (en gates it in the top's instance ports, but
    // the emitted logic sums unconditionally — the manifest's port set is
    // what we assert against here).
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
    };
    let model = cfg.compile().expect("compile model");
    let top = model.manifest.top_module().expect("top in manifest");
    assert_eq!(top.name, "basicDecls");
    // x is an 8-bit input of the parameterized module
    let x = top.port("x").expect("port x");
    assert_eq!(x.width, 8);
    assert!(model.exe.is_file());
}
