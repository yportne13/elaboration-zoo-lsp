//! Simulator backend abstraction (veryl's Runner pattern, adapted).
//!
//! Each backend owns its toolchain invocation and harness style but must
//! produce a model that speaks the SAME stdin/stdout line protocol, so the
//! `Dut` handle and every testbench written against it are
//! simulator-agnostic. Two harness styles exist:
//!
//! - Verilator: a generated C++ harness (cycle-accurate, needs eval).
//! - Event-driven simulators (Icarus/VCS/Vivado xsim): a generated
//!   Verilog testbench wrapper (`verilog_harness`) implementing the
//!   protocol with $fscanf/$display — settles deltas inside `eval`.

use std::path::PathBuf;

use serde::Deserialize;

use super::{DesignManifest, SimError};

/// The simulator a SimConfig builds with.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Simulator {
    #[default]
    Verilator,
    #[serde(alias = "iverilog")]
    Icarus,
    Vcs,
    #[serde(alias = "xsim")]
    Vivado,
}

impl Simulator {
    pub fn parse(s: &str) -> Option<Simulator> {
        match s {
            "verilator" => Some(Simulator::Verilator),
            "icarus" | "iverilog" => Some(Simulator::Icarus),
            "vcs" => Some(Simulator::Vcs),
            "vivado" | "xsim" => Some(Simulator::Vivado),
            _ => None,
        }
    }

    pub fn name(&self) -> &'static str {
        match self {
            Simulator::Verilator => "verilator",
            Simulator::Icarus => "icarus",
            Simulator::Vcs => "vcs",
            Simulator::Vivado => "vivado",
        }
    }

    pub fn runner(&self) -> Box<dyn SimulatorRunner> {
        match self {
            Simulator::Verilator => Box::new(super::verilator::Verilator),
            Simulator::Icarus => Box::new(super::iverilog::Icarus),
            Simulator::Vcs => Box::new(super::vcs::Vcs),
            Simulator::Vivado => Box::new(super::vivado::Vivado),
        }
    }
}

/// Everything a backend needs to turn an elaborated design into a running
/// model. The Verilog file is already written at `<workdir>/<top>.v`.
pub struct BuildPlan {
    pub top_name: String,
    pub workdir: PathBuf,
    pub manifest: DesignManifest,
    /// Extra compile arguments from config/CLI.
    pub extra_args: Vec<String>,
    /// Compile with VCD tracing.
    pub trace: bool,
}

/// A built model. `exe` + `exe_args` is the spawn command line: backends
/// whose "binary" is a runner (vvp, xsim) use exe_args to carry the
/// snapshot/design file.
pub struct CompiledModel {
    pub exe: PathBuf,
    pub exe_args: Vec<String>,
    pub workdir: PathBuf,
    pub manifest: DesignManifest,
}

pub trait SimulatorRunner {
    fn name(&self) -> &'static str;

    /// Locate the backend's primary tool (None → backend unavailable;
    /// callers skip tests / report a friendly error).
    fn find_tool(&self) -> Option<PathBuf>;

    /// Write the harness and run the compile pipeline.
    fn build(&self, plan: &BuildPlan) -> Result<CompiledModel, SimError>;
}
