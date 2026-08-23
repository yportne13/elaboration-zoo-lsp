//! AMD/Xilinx Vivado xsim backend (event-driven; shares the Verilog
//! testbench harness with Icarus/VCS).
//!
//! UNTESTED on this machine (no Vivado install): the three-phase command
//! shape follows veryl's runner (crates/veryl/src/runner/vivado.rs) —
//! `xvlog` → `xelab <tb> -s <snapshot>` → `xsim <snapshot> -R` (batch
//! run-to-completion; the harness loops on stdin until `finish`, and the
//! design's $fscanf stdin reads are expected to receive the process stdin
//! in -R mode).
//!
//! Tool resolution: $XVLOG/$XELAB/$XSIM, then PATH, then
//! %XILINX_VIVADO%/bin (the classic settings64.bat layout).

use std::fs;
use std::path::PathBuf;
use std::process::Command;

use super::runner::{BuildPlan, CompiledModel, SimulatorRunner};
use super::verilog_harness::harness_verilog;
use super::{find_in_path, run_tool, SimError};

fn vivado_bin_dirs() -> Vec<PathBuf> {
    let mut dirs = Vec::new();
    if let Some(root) = std::env::var_os("XILINX_VIVADO") {
        dirs.push(PathBuf::from(root).join("bin"));
    }
    dirs
}

fn find_vivado_tool(env_var: &str, name: &str) -> Option<PathBuf> {
    if let Some(explicit) = std::env::var_os(env_var) {
        let p = PathBuf::from(explicit);
        if p.is_file() {
            return Some(p);
        }
    }
    if let Some(p) = find_in_path(name) {
        return Some(p);
    }
    for dir in vivado_bin_dirs() {
        let p = dir.join(format!("{name}.bat")); // Windows wrappers
        if p.is_file() {
            return Some(p);
        }
        let p = dir.join(name);
        if p.is_file() {
            return Some(p);
        }
    }
    None
}

/// Locate the xsim runner (the primary tool of this backend).
pub fn find_vivado() -> Option<PathBuf> {
    find_vivado_tool("XSIM", "xsim")
}

pub struct Vivado;

impl SimulatorRunner for Vivado {
    fn name(&self) -> &'static str {
        "vivado"
    }

    fn find_tool(&self) -> Option<PathBuf> {
        find_vivado()
    }

    fn build(&self, plan: &BuildPlan) -> Result<CompiledModel, SimError> {
        let top_name = &plan.top_name;
        let top_info = plan
            .manifest
            .top_module()
            .ok_or_else(|| SimError::BadManifest(format!("top module '{top_name}' missing from manifest")))?
            .clone();

        let xvlog = find_vivado_tool("XVLOG", "xvlog").ok_or_else(|| {
            SimError::ToolMissing("xvlog not found (install Vivado, source settings64, or set XVLOG)".into())
        })?;
        let xelab = find_vivado_tool("XELAB", "xelab")
            .ok_or_else(|| SimError::ToolMissing("xelab not found (set XELAB or PATH)".into()))?;
        let xsim = find_vivado().ok_or_else(|| SimError::ToolMissing("xsim not found (set XSIM or PATH)".into()))?;

        let tb_name = format!("tb_{top_name}");
        let snapshot = format!("snap_{top_name}");
        fs::write(
            plan.workdir.join(format!("{tb_name}.v")),
            harness_verilog(&top_info, plan.trace)?,
        )?;

        // Phase 1: analyze.
        let mut cmd = Command::new(&xvlog);
        cmd.current_dir(&plan.workdir)
            .args(&plan.extra_args)
            .arg(format!("{tb_name}.v"))
            .arg(format!("{top_name}.v"));
        run_tool(&mut cmd, "xvlog")?;

        // Phase 2: elaborate the testbench top into a snapshot.
        let mut cmd = Command::new(&xelab);
        cmd.current_dir(&plan.workdir)
            .arg(&tb_name)
            .arg("-s")
            .arg(&snapshot)
            .arg("-debug")
            .arg("typical");
        run_tool(&mut cmd, "xelab")?;

        // Phase 3: run. -R = run to completion (no TCL console competing
        // for stdin); the harness exits on `finish` / EOF.
        Ok(CompiledModel {
            exe: xsim,
            exe_args: vec![snapshot, "-R".to_string()],
            workdir: plan.workdir.clone(),
            manifest: plan.manifest.clone(),
        })
    }
}
