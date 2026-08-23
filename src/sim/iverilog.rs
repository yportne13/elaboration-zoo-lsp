//! Icarus Verilog backend (event-driven; shares the Verilog testbench
//! harness with VCS/Vivado).
//!
//! `iverilog -o model.vvp tb_<top>.v <top>.v` then run with `vvp
//! model.vvp` — the model is a runner invocation, hence exe=vvp,
//! exe_args=[model.vvp]. No make step.
//!
//! Windows/MSYS2 notes (probed on iverilog 12.0):
//! - the driver shells out its `ivlpp | ivl` pipeline via system(); the
//!   children live in <prefix>/lib/ivl and need the runtime DLLs from
//!   <prefix>/bin, so every invocation runs with the toolchain bin dir
//!   prepended to PATH;
//! - the MSYS2 mingw64 package is BROKEN on this machine (its ivl dies
//!   silently against the stale 2020 libstdc++); the ucrt64 package works,
//!   so common-location probing prefers ucrt64.

use std::fs;
use std::path::PathBuf;
use std::process::Command;

use super::runner::{BuildPlan, CompiledModel, SimulatorRunner};
use super::verilog_harness::harness_verilog;
use super::{find_in_path, run_tool, SimError};

/// Locate iverilog: $IVERILOG env, PATH, then common MSYS2 locations.
/// An MSYS2 mingw64 hit is upgraded to its ucrt64 twin when present — the
/// mingw64 package ships a stale runtime that kills ivl silently (see
/// module notes).
pub fn find_iverilog() -> Option<PathBuf> {
    if let Some(explicit) = std::env::var_os("IVERILOG") {
        let p = PathBuf::from(explicit);
        if p.is_file() {
            return Some(p);
        }
    }
    let found = find_in_path("iverilog").or_else(|| {
        for prefix in ["C:/msys64", "C:/msys32", "C:/tools/msys64"] {
            for abi in ["ucrt64", "mingw64"] {
                let p = PathBuf::from(prefix).join(format!("{abi}/bin/iverilog.exe"));
                if p.is_file() {
                    return Some(p);
                }
            }
        }
        None
    })?;
    let s = found.display().to_string();
    if s.contains("mingw64") {
        let twin = PathBuf::from(s.replace("mingw64", "ucrt64"));
        if twin.is_file() {
            return Some(twin);
        }
    }
    Some(found)
}

/// vvp lives next to iverilog.
fn find_vvp(iverilog: &std::path::Path) -> Option<PathBuf> {
    if let Some(explicit) = std::env::var_os("VVP") {
        let p = PathBuf::from(explicit);
        if p.is_file() {
            return Some(p);
        }
    }
    let sibling = iverilog
        .parent()?
        .join(if cfg!(windows) { "vvp.exe" } else { "vvp" });
    if sibling.is_file() {
        return Some(sibling);
    }
    find_in_path("vvp")
}

/// The driver's child pipeline needs the toolchain runtime DLLs; prepend
/// the bin dir to PATH for the compile (also re-exported for Dut::spawn).
pub(crate) fn toolchain_path_env(bin_dir: &std::path::Path) -> Option<std::ffi::OsString> {
    let old_path = std::env::var_os("PATH")?;
    std::env::join_paths(
        std::iter::once(bin_dir.to_path_buf()).chain(std::env::split_paths(&old_path)),
    )
    .ok()
}

pub struct Icarus;

impl SimulatorRunner for Icarus {
    fn name(&self) -> &'static str {
        "icarus"
    }

    fn find_tool(&self) -> Option<PathBuf> {
        find_iverilog()
    }

    fn build(&self, plan: &BuildPlan) -> Result<CompiledModel, SimError> {
        let top_name = &plan.top_name;
        let top_info = plan
            .manifest
            .top_module()
            .ok_or_else(|| SimError::BadManifest(format!("top module '{top_name}' missing from manifest")))?
            .clone();

        let iverilog = find_iverilog().ok_or_else(|| {
            SimError::ToolMissing("iverilog not found (set IVERILOG or install MSYS2/ucrt64 iverilog)".into())
        })?;
        let vvp = find_vvp(&iverilog).ok_or_else(|| SimError::ToolMissing("vvp not found next to iverilog".into()))?;

        let tb_name = format!("tb_{top_name}");
        fs::write(
            plan.workdir.join(format!("{tb_name}.v")),
            harness_verilog(&top_info, plan.trace)?,
        )?;

        // Relative file args with cwd=workdir (verilator_bin taught us
        // native tools misread absolute Windows paths); toolchain bin dir
        // on PATH for the driver's internal pipeline children.
        let mut cmd = Command::new(&iverilog);
        cmd.current_dir(&plan.workdir)
            .arg("-g2005")
            .arg("-o")
            .arg("model.vvp")
            .args(&plan.extra_args)
            .arg(format!("{tb_name}.v"))
            .arg(format!("{top_name}.v"));
        if let Some(bin) = iverilog.parent() {
            if let Some(path) = toolchain_path_env(bin) {
                cmd.env("PATH", path);
            }
        }
        run_tool(&mut cmd, "iverilog")?;

        let model = plan.workdir.join("model.vvp");
        if !model.is_file() {
            return Err(SimError::CommandFailed {
                tool: "iverilog".into(),
                output: format!("model not produced at {}", model.display()),
            });
        }
        Ok(CompiledModel {
            exe: vvp,
            exe_args: vec![model.display().to_string()],
            workdir: plan.workdir.clone(),
            manifest: plan.manifest.clone(),
        })
    }
}
