//! Verilator-based simulation pipeline (SpinalSim style).
//!
//! The testbench is HOST code (Rust) driving a compiled model, not emitted
//! HDL: `SimConfig::compile` elaborates the .typort sources via the emit
//! channel, then a per-simulator backend (`runner::SimulatorRunner`, veryl's
//! Runner pattern) generates a harness and compiles a model speaking the
//! line protocol (`set PORT HEX`, `get PORT`, `eval`, `finish`) that the
//! `Dut` handle (dut.rs) wraps. Because every backend speaks the same
//! protocol, testbenches are simulator-agnostic — run the same design on
//! verilator and iverilog to cross-check.

use std::fmt;
use std::fs;
use std::io;
use std::path::PathBuf;
use std::process::Command;

use crate::emit;

pub mod dut;
pub use dut::{Clock, ClockFork, Dut};
pub mod runner;
pub use runner::{BuildPlan, Simulator, SimulatorRunner};
mod iverilog;
mod vcs;
mod verilog_harness;
mod verilator;
mod vivado;

// Re-exports for tests / CLI probing tool availability.
pub use verilator::find_verilator;
pub use iverilog::find_iverilog;
pub use vcs::find_vcs;
pub use vivado::find_vivado;

/// Locate a backend's primary tool (None → unavailable; skip/report).
pub fn find_simulator_tool(sim: Simulator) -> Option<PathBuf> {
    sim.runner().find_tool()
}

// ---------------------------------------------------------------------------
// Design manifest (parsed from emit's designManifestVL JSON)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct PortDef {
    pub name: String,
    /// "input" | "output" | "inout"
    pub dir: String,
    pub width: u32,
    pub signed: bool,
    pub reg: bool,
}

impl PortDef {
    pub fn is_drivable(&self) -> bool {
        self.dir == "input" || self.dir == "inout"
    }
    pub fn is_readable(&self) -> bool {
        self.dir == "output" || self.dir == "inout"
    }
    /// Verilator's C++ scalar type for a port of this width.
    pub fn ctype(&self) -> &'static str {
        match self.width {
            0..=8 => "CData",
            9..=16 => "SData",
            17..=32 => "IData",
            _ => "QData",
        }
    }
}

#[derive(Debug, Clone)]
pub struct ClockDef {
    pub clk: String,
    pub reset: String,
    pub kind: String,
    pub edge: String,
    pub reset_active: String,
}

#[derive(Debug, Clone)]
pub struct ModuleInfo {
    pub name: String,
    pub clock: ClockDef,
    pub ports: Vec<PortDef>,
    /// (instance name, module name)
    pub instances: Vec<(String, String)>,
}

impl ModuleInfo {
    pub fn port(&self, name: &str) -> Option<&PortDef> {
        self.ports.iter().find(|p| p.name == name)
    }
}

#[derive(Debug, Clone)]
pub struct DesignManifest {
    pub top: String,
    pub modules: Vec<ModuleInfo>,
}

impl DesignManifest {
    pub fn from_json(json: &str) -> Result<Self, SimError> {
        let v: serde_json::Value =
            serde_json::from_str(json).map_err(|e| SimError::BadManifest(e.to_string()))?;
        let top = v["top"].as_str().unwrap_or_default().to_string();
        let mut modules = Vec::new();
        for m in v["modules"].as_array().map(|a| a.as_slice()).unwrap_or(&[]) {
            let clock = &m["clock"];
            let mut ports = Vec::new();
            for p in m["ports"].as_array().map(|a| a.as_slice()).unwrap_or(&[]) {
                ports.push(PortDef {
                    name: p["name"].as_str().unwrap_or_default().to_string(),
                    dir: p["dir"].as_str().unwrap_or_default().to_string(),
                    width: p["width"].as_u64().unwrap_or(1) as u32,
                    signed: p["signed"].as_bool().unwrap_or(false),
                    reg: p["reg"].as_bool().unwrap_or(false),
                });
            }
            let mut instances = Vec::new();
            for i in m["instances"].as_array().map(|a| a.as_slice()).unwrap_or(&[]) {
                instances.push((
                    i["inst"].as_str().unwrap_or_default().to_string(),
                    i["module"].as_str().unwrap_or_default().to_string(),
                ));
            }
            modules.push(ModuleInfo {
                name: m["name"].as_str().unwrap_or_default().to_string(),
                clock: ClockDef {
                    clk: clock["clk"].as_str().unwrap_or("clk").to_string(),
                    reset: clock["reset"].as_str().unwrap_or("reset").to_string(),
                    kind: clock["kind"].as_str().unwrap_or("async").to_string(),
                    edge: clock["edge"].as_str().unwrap_or("posedge").to_string(),
                    reset_active: clock["resetActive"].as_str().unwrap_or("high").to_string(),
                },
                ports,
                instances,
            });
        }
        Ok(DesignManifest { top, modules })
    }

    pub fn top_module(&self) -> Option<&ModuleInfo> {
        self.modules.iter().find(|m| m.name == self.top)
    }
}

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

#[derive(Debug)]
pub enum SimError {
    Emit(emit::EmitError),
    BadManifest(String),
    Io(io::Error),
    /// A required external tool is not installed / not on PATH.
    ToolMissing(String),
    /// An external tool ran and failed; carries the tail of its output.
    CommandFailed { tool: String, output: String },
}

impl fmt::Display for SimError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SimError::Emit(e) => write!(f, "{e}"),
            SimError::BadManifest(msg) => write!(f, "bad design manifest: {msg}"),
            SimError::Io(e) => write!(f, "{e}"),
            SimError::ToolMissing(msg) => write!(f, "{msg}"),
            SimError::CommandFailed { tool, output } => {
                write!(f, "{tool} failed:\n{output}")
            }
        }
    }
}

impl From<io::Error> for SimError {
    fn from(e: io::Error) -> Self {
        SimError::Io(e)
    }
}

impl From<emit::EmitError> for SimError {
    fn from(e: emit::EmitError) -> Self {
        SimError::Emit(e)
    }
}

impl std::error::Error for SimError {}

// ---------------------------------------------------------------------------
// Shared tool helpers
// ---------------------------------------------------------------------------

/// Search PATH for an executable name (Windows tries .exe too).
pub(crate) fn find_in_path(name: &str) -> Option<PathBuf> {
    let path = std::env::var_os("PATH")?;
    let candidates: Vec<String> = if cfg!(windows) && !name.ends_with(".exe") {
        vec![format!("{name}.exe"), name.to_string()]
    } else {
        vec![name.to_string()]
    };
    for dir in std::env::split_paths(&path) {
        for cand in &candidates {
            let p = dir.join(cand);
            if p.is_file() {
                return Some(p);
            }
        }
    }
    None
}

/// Run a build tool to completion, capturing output for error reporting.
pub(crate) fn run_tool(cmd: &mut Command, tool: &str) -> Result<String, SimError> {
    let output = cmd
        .output()
        .map_err(|e| SimError::CommandFailed { tool: tool.to_string(), output: e.to_string() })?;
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    if !output.status.success() {
        // Keep the tail: tool errors point at the offending line.
        let tail: String = text.chars().rev().take(2000).collect::<Vec<_>>().into_iter().rev().collect();
        return Err(SimError::CommandFailed { tool: tool.to_string(), output: tail });
    }
    Ok(text)
}

// ---------------------------------------------------------------------------
// Compile pipeline
// ---------------------------------------------------------------------------

/// Everything needed to build a simulation model from .typort sources.
#[derive(Debug, Clone)]
pub struct SimConfig {
    /// Top module instantiation, e.g. "topWithPorts" or "adder[8]".
    pub top: String,
    /// .typort source files (compiled in order).
    pub sources: Vec<PathBuf>,
    /// Build directory (created if missing).
    pub workdir: PathBuf,
    /// Which simulator backend to build with.
    pub simulator: Simulator,
    /// Extra compile arguments for the backend.
    pub verilator_args: Vec<String>,
    /// Compile with VCD tracing; the model writes wave.vcd in its cwd.
    pub trace: bool,
}

impl SimConfig {
    /// Elaborate the sources, then let the configured backend compile a
    /// model. Returns the spawn command line and manifest.
    pub fn compile(&self) -> Result<runner::CompiledModel, SimError> {
        let top_name = emit::top_module_name(&self.top).map_err(SimError::Emit)?.to_string();

        let mut sources = Vec::with_capacity(self.sources.len());
        for path in &self.sources {
            let canonical = path.canonicalize().unwrap_or_else(|_| path.clone());
            let text = fs::read_to_string(path).map_err(|e| {
                SimError::Io(io::Error::new(e.kind(), format!("reading {}: {e}", path.display())))
            })?;
            let uri = lsp_types::Url::from_file_path(&canonical)
                .map_err(|()| SimError::Emit(emit::EmitError::BadTop(path.display().to_string())))?;
            sources.push((uri, text));
        }
        let emitted = emit::emit_design(&sources, &self.top, true)?;
        let manifest = DesignManifest::from_json(emitted.manifest.as_deref().unwrap_or("{}"))?;

        fs::create_dir_all(&self.workdir)?;
        fs::write(self.workdir.join(format!("{top_name}.v")), &emitted.verilog)?;
        fs::write(
            self.workdir.join(format!("{top_name}.manifest.json")),
            emitted.manifest.as_deref().unwrap_or("{}"),
        )?;

        let plan = BuildPlan {
            top_name,
            workdir: self.workdir.clone(),
            manifest,
            extra_args: self.verilator_args.clone(),
            trace: self.trace,
        };
        self.simulator.runner().build(&plan)
    }
}
