//! Synopsys VCS backend (event-driven; shares the Verilog testbench
//! harness with Icarus/Vivado).
//!
//! UNTESTED on this machine (no VCS license): command shape follows veryl's
//! runner (crates/veryl/src/runner/vcs.rs) — `vcs -full64 -o simv` then
//! `./simv +vcs+lic+wait`. VCS is Linux-only, so no Windows path quirks
//! apply.

use std::fs;
use std::path::PathBuf;
use std::process::Command;

use super::runner::{BuildPlan, CompiledModel, SimulatorRunner};
use super::verilog_harness::harness_verilog;
use super::{find_in_path, run_tool, SimError};

/// Locate vcs: $VCS env var, then PATH.
pub fn find_vcs() -> Option<PathBuf> {
    if let Some(explicit) = std::env::var_os("VCS") {
        let p = PathBuf::from(explicit);
        if p.is_file() {
            return Some(p);
        }
    }
    find_in_path("vcs")
}

pub struct Vcs;

impl SimulatorRunner for Vcs {
    fn name(&self) -> &'static str {
        "vcs"
    }

    fn find_tool(&self) -> Option<PathBuf> {
        find_vcs()
    }

    fn build(&self, plan: &BuildPlan) -> Result<CompiledModel, SimError> {
        let top_name = &plan.top_name;
        let top_info = plan
            .manifest
            .top_module()
            .ok_or_else(|| SimError::BadManifest(format!("top module '{top_name}' missing from manifest")))?
            .clone();

        let vcs = find_vcs().ok_or_else(|| {
            SimError::ToolMissing("vcs not found (set VCS or add it to PATH)".into())
        })?;

        let tb_name = format!("tb_{top_name}");
        fs::write(
            plan.workdir.join(format!("{tb_name}.v")),
            harness_verilog(&top_info, plan.trace)?,
        )?;

        // vcs compiles everything into ./simv (plus csrc/ etc.) in cwd.
        let mut cmd = Command::new(&vcs);
        cmd.current_dir(&plan.workdir)
            .arg("-full64")
            .arg("-o")
            .arg("simv")
            .args(&plan.extra_args)
            .arg(format!("{tb_name}.v"))
            .arg(format!("{top_name}.v"));
        run_tool(&mut cmd, "vcs")?;

        let exe = plan.workdir.join("simv");
        if !exe.is_file() {
            return Err(SimError::CommandFailed {
                tool: "vcs".into(),
                output: format!("simv not produced at {}", exe.display()),
            });
        }
        Ok(CompiledModel {
            exe,
            // veryl's runner passes +vcs+lic+wait at run time.
            exe_args: vec!["+vcs+lic+wait".to_string()],
            workdir: plan.workdir.clone(),
            manifest: plan.manifest.clone(),
        })
    }
}
