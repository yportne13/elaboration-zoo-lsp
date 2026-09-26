//! Interactive DUT handle over a compiled simulation model.
//!
//! `Dut` owns the model process and speaks the harness line protocol
//! (`set PORT HEX` / `get PORT` / `eval` / `finish`). Port access is
//! validated against the design manifest (direction + width), so
//! testbench typos surface as Rust errors, not silent model behavior.
//!
//! Clocking follows the SpinalSim `forkStimulus` shape: `dut.clock().fork(period)`
//! spawns a thread that drives the clock port through the SAME channel
//! (each half-cycle's set/eval round trip is one critical section, so the
//! test thread and the clock thread never interleave inside a transaction).
//! Rising edges are counted in an atomic; `wait_edges(n)` blocks the test
//! thread until n more posedges have passed — that is the "sleep" of this
//! API (wall-clock period only paces the toggles, tests reason in edges).

use std::collections::HashMap;
use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

use super::runner::CompiledModel;
use super::{ClockDef, PortDef, SimError};

/// The model process's stdin/stdout pair. Every protocol round trip
/// (request line + response line) happens under one lock, which keeps the
/// clock thread and the test thread from interleaving mid-transaction.
struct Channel {
    stdin: ChildStdin,
    stdout: BufReader<std::process::ChildStdout>,
}

struct Shared {
    ch: Mutex<Channel>,
    edges: AtomicU64,
    stop: AtomicBool,
    /// Design-side assertion marker lines (`TYPORT_ASSERT_<SEV> %0t %m: msg`,
    /// $display'd by the model inside its translate_off block), captured in
    /// roundtrip so behavioral failures surface on the host side
    /// (docs/hdl-blackbox-sim-design.md §5.2). Capped at
    /// [`ASSERT_FAILURES_CAP`] markers (see roundtrip).
    failures: Mutex<Vec<String>>,
    /// Markers dropped after the capture cap was reached (kept so the
    /// synthetic truncation line can report an exact count).
    overflow: AtomicU64,
}

/// Upper bound on captured design-assertion markers: the first 100 are kept
/// verbatim, then a single synthetic truncation line (whose dropped-count is
/// refreshed on every further marker) closes the list — a runaway assertion
/// can neither exhaust host memory nor hide that it fired.
const ASSERT_FAILURES_CAP: usize = 100;

fn channel_poisoned() -> SimError {
    SimError::CommandFailed {
        tool: "model".into(),
        output: "model channel poisoned (a driver thread panicked)".into(),
    }
}

impl Shared {
    /// Send one protocol line and read its one-line response. Simulator
    /// chatter on stdout (vvp's "VCD info: ..." banner, and similar
    /// notices from other backends) is skipped so it cannot desynchronize
    /// the protocol.
    fn roundtrip(&self, line: &str) -> Result<String, SimError> {
        let mut ch = self.ch.lock().map_err(|_| channel_poisoned())?;
        ch.stdin
            .write_all(line.as_bytes())
            .and_then(|_| ch.stdin.write_all(b"\n"))
            .and_then(|_| ch.stdin.flush())
            .map_err(SimError::Io)?;
        let mut out = String::new();
        loop {
            out.clear();
            let n = ch.stdout.read_line(&mut out).map_err(SimError::Io)?;
            if n == 0 {
                return Err(SimError::CommandFailed {
                    tool: "model".into(),
                    output: "model closed stdout".into(),
                });
            }
            let trimmed = out.trim_end();
            if trimmed.starts_with("VCD ") {
                continue; // e.g. "VCD info: dumpfile wave.vcd opened..."
            }
            if trimmed.starts_with("TYPORT_ASSERT_") {
                // Design assertion marker ($display from the model's
                // translate_off block) — record it and keep the protocol
                // desynchronized-free by continuing to the next line.
                // Capture is capped: the first ASSERT_FAILURES_CAP markers
                // are kept verbatim; beyond that one synthetic truncation
                // line closes the list and its dropped-count is refreshed
                // per marker, so the list stays O(1) no matter how often a
                // hot assertion fires.
                if let Ok(mut f) = self.failures.lock() {
                    if f.len() < ASSERT_FAILURES_CAP {
                        f.push(trimmed.to_string());
                    } else {
                        let dropped = self.overflow.fetch_add(1, Ordering::SeqCst) + 1;
                        let line = format!(
                            "TYPORT_ASSERT_TRUNCATED: {} further design assertion \
                             marker(s) dropped (first {ASSERT_FAILURES_CAP} kept)",
                            dropped
                        );
                        if f.len() == ASSERT_FAILURES_CAP {
                            f.push(line);
                        } else {
                            f[ASSERT_FAILURES_CAP] = line;
                        }
                    }
                }
                continue;
            }
            return Ok(trimmed.to_string());
        }
    }
}

/// A handle onto a running simulation model.
pub struct Dut {
    child: Child,
    shared: Arc<Shared>,
    ports: HashMap<String, PortDef>,
    clock_def: ClockDef,
    workdir: PathBuf,
    forks: Vec<ClockFork>,
}

impl Dut {
    /// Spawn the compiled model (exe + exe_args: vvp/xsim carry the design
    /// file as an argument). The process runs with the workdir as its cwd
    /// (wave files land there) and the exe's directory prepended to PATH
    /// (runners like vvp load runtime modules needing toolchain DLLs).
    pub fn spawn(model: &CompiledModel) -> Result<Dut, SimError> {
        let top = model
            .manifest
            .top_module()
            .ok_or_else(|| SimError::BadManifest("top module missing from manifest".into()))?;
        let mut child = Command::new(&model.exe);
        child
            .args(&model.exe_args)
            .current_dir(&model.workdir)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped());
        if let Some(bin) = model.exe.parent() {
            if let Some(path) = std::env::var_os("PATH").and_then(|old| {
                std::env::join_paths(
                    std::iter::once(bin.to_path_buf()).chain(std::env::split_paths(&old)),
                )
                .ok()
            }) {
                child.env("PATH", path);
            }
        }
        let mut child = child.spawn().map_err(SimError::Io)?;
        let stdin = child.stdin.take().unwrap();
        let stdout = BufReader::new(child.stdout.take().unwrap());
        let shared = Arc::new(Shared {
            ch: Mutex::new(Channel { stdin, stdout }),
            edges: AtomicU64::new(0),
            stop: AtomicBool::new(false),
            failures: Mutex::new(Vec::new()),
            overflow: AtomicU64::new(0),
        });
        Ok(Dut {
            ports: top.ports.iter().cloned().map(|p| (p.name.clone(), p)).collect(),
            clock_def: top.clock.clone(),
            child,
            shared,
            workdir: model.workdir.clone(),
            forks: Vec::new(),
        })
    }

    pub fn port(&self, name: &str) -> Option<&PortDef> {
        self.ports.get(name)
    }

    /// The top module's default clock domain.
    pub fn clock(&self) -> Clock {
        self.clock_named(&self.clock_def.clk.clone())
    }

    /// A clock handle for an explicit port name (multi-clock designs).
    pub fn clock_named(&self, port: &str) -> Clock {
        Clock { shared: self.shared.clone(), port: port.to_string() }
    }

    /// Rising edges seen since spawn (across all forked clocks).
    pub fn edges(&self) -> u64 {
        self.shared.edges.load(Ordering::SeqCst)
    }

    /// Block until `n` more rising edges have passed.
    pub fn wait_edges(&self, n: u64) {
        let target = self.edges() + n;
        while self.edges() < target {
            thread::sleep(Duration::from_millis(1));
        }
    }

    /// Drive an input/inout port. Fails on unknown names, non-drivable
    /// directions, and values that don't fit the port width.
    pub fn set(&mut self, name: &str, value: u64) -> Result<&mut Self, SimError> {
        let p = self
            .ports
            .get(name)
            .ok_or_else(|| SimError::BadManifest(format!("no port named '{name}'")))?;
        if !p.is_drivable() {
            return Err(SimError::BadManifest(format!(
                "port '{name}' is {} and cannot be driven",
                p.dir
            )));
        }
        if p.width < 64 && value >> p.width != 0 {
            return Err(SimError::BadManifest(format!(
                "value {value:#x} does not fit port '{name}' ({} bits)",
                p.width
            )));
        }
        let resp = self.shared.roundtrip(&format!("set {name} {value:x}"))?;
        if resp != "ok" {
            return Err(SimError::CommandFailed { tool: "model".into(), output: resp });
        }
        Ok(self)
    }

    /// Read an output/inout port.
    pub fn get(&mut self, name: &str) -> Result<u64, SimError> {
        let p = self
            .ports
            .get(name)
            .ok_or_else(|| SimError::BadManifest(format!("no port named '{name}'")))?;
        if !p.is_readable() {
            return Err(SimError::BadManifest(format!(
                "port '{name}' is {} and cannot be read",
                p.dir
            )));
        }
        let resp = self.shared.roundtrip(&format!("get {name}"))?;
        u64::from_str_radix(&resp, 16)
            .map_err(|_| SimError::CommandFailed { tool: "model".into(), output: resp })
    }

    /// Propagate inputs to outputs (combinational settle).
    pub fn eval(&mut self) -> Result<&mut Self, SimError> {
        let resp = self.shared.roundtrip("eval")?;
        if resp != "ok" {
            return Err(SimError::CommandFailed { tool: "model".into(), output: resp });
        }
        Ok(self)
    }

    /// Path where the model writes its waveform (valid when compiled with
    /// `trace: true`).
    pub fn wave_path(&self) -> PathBuf {
        self.workdir.join("wave.vcd")
    }

    /// Design assertion marker lines captured from the model's stdout so far
    /// (`TYPORT_ASSERT_<SEV> <time> <instance path>: <msg>`), oldest first.
    pub fn assert_failures(&self) -> Vec<String> {
        self.shared
            .failures
            .lock()
            .map(|f| f.clone())
            .unwrap_or_default()
    }

    /// Ok iff no design assertion has fired. The error carries every captured
    /// marker line (%m instance path + message) for the test failure output.
    pub fn expect_no_asserts(&self) -> Result<(), SimError> {
        let f = self.assert_failures();
        if f.is_empty() {
            Ok(())
        } else {
            Err(SimError::CommandFailed {
                tool: "model".into(),
                output: format!(
                    "{} design assertion(s) fired:\n{}",
                    f.len(),
                    f.join("\n")
                ),
            })
        }
    }

    /// Stop all forked clocks, tell the model to finish, and wait for exit.
    ///
    /// Takes `&mut self` (not `self`) so callers can keep reading captured
    /// state — `assert_failures()` in particular — AFTER the finish
    /// handshake: the handshake's roundtrip routes any late
    /// `TYPORT_ASSERT_*` line into the same list without consuming it.
    /// Calling finish twice (or finishing near a `Drop`) is harmless: every
    /// step is idempotent or best-effort.
    pub fn finish(&mut self) -> Result<(), SimError> {
        self.stop_forks();
        let _ = self.shared.roundtrip("finish");
        self.child.wait().map_err(SimError::Io)?;
        Ok(())
    }

    fn stop_forks(&mut self) {
        self.shared.stop.store(true, Ordering::SeqCst);
        for fork in self.forks.drain(..) {
            if let Some(handle) = fork.handle {
                let _ = handle.join();
            }
        }
    }
}

impl Drop for Dut {
    fn drop(&mut self) {
        // Best-effort cleanup when the test forgot finish(): stop the
        // clock threads and release the model process.
        self.stop_forks();
        let _ = self.shared.roundtrip("finish");
        let _ = self.child.wait();
    }
}

/// A clock signal of a running Dut.
pub struct Clock {
    shared: Arc<Shared>,
    port: String,
}

impl Clock {
    /// Start toggling this clock with `period` per full cycle (half low,
    /// half high) on a background thread. The first transition is a
    /// low-going init so edge 0 starts clean.
    pub fn fork(self, period: Duration) -> ClockFork {
        let shared = self.shared;
        let port = self.port;
        let half = period / 2;
        let handle = thread::spawn(move || {
            let _ = shared.roundtrip(&format!("set {port} 0"));
            let _ = shared.roundtrip("eval");
            while !shared.stop.load(Ordering::SeqCst) {
                let _ = shared.roundtrip(&format!("set {port} 1"));
                let _ = shared.roundtrip("eval");
                shared.edges.fetch_add(1, Ordering::SeqCst);
                thread::sleep(half);
                if shared.stop.load(Ordering::SeqCst) {
                    break;
                }
                let _ = shared.roundtrip(&format!("set {port} 0"));
                let _ = shared.roundtrip("eval");
                thread::sleep(half);
            }
        });
        ClockFork { handle: Some(handle) }
    }
}

/// A running clock stimulus thread.
pub struct ClockFork {
    handle: Option<thread::JoinHandle<()>>,
}
