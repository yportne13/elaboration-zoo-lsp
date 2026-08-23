//! Verilator-based simulation pipeline (SpinalSim style).
//!
//! The testbench is HOST code (Rust) driving a compiled model, not emitted
//! HDL: `SimConfig::compile` elaborates the .typort sources via the emit
//! channel, generates a small C++ harness from the design manifest, runs
//! `verilator --cc --exe` + `make`, and hands back the model executable.
//! The harness speaks a line protocol over stdin/stdout (`set PORT HEX`,
//! `get PORT`, `eval`, `finish`) that the `Dut` handle (dut.rs) wraps.
//!
//! Windows/MSYS2 notes (probed on Verilator 4.024 mingw64):
//! - the `verilator` perl wrapper breaks under some PATHs; prefer
//!   `verilator_bin.exe` directly;
//! - the generated .mk hardcodes an MSYS2-style `VERILATOR_ROOT`
//!   (`/mingw64/...`) that native make cannot resolve — a command-line
//!   `VERILATOR_ROOT=<windows path>` override fixes it (command-line
//!   assignments beat in-file ones);
//! - the model link step needs the toolchain's g++/ranlib, so make runs
//!   with the verilator bin dir prepended to PATH.

use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::emit;

pub mod dut;
pub use dut::{Clock, ClockFork, Dut};

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
        for m in v["modules"].as_array().ok_or_else(|| SimError::BadManifest("no modules".into()))? {
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
// Tool discovery
// ---------------------------------------------------------------------------

/// Search PATH for an executable name (Windows tries .exe too).
fn find_in_path(name: &str) -> Option<PathBuf> {
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

/// Locate verilator. Resolution order: $VERILATOR, then `verilator_bin` on
/// PATH (the native binary — the perl wrapper breaks under some PATHs),
/// then `verilator` on PATH, then common MSYS2 locations.
pub fn find_verilator() -> Option<PathBuf> {
    if let Some(explicit) = std::env::var_os("VERILATOR") {
        let p = PathBuf::from(explicit);
        if p.is_file() {
            return Some(p);
        }
        // A bare name: search PATH with it.
        if let Some(found) = p.to_str().and_then(find_in_path) {
            return Some(found);
        }
    }
    if let Some(p) = find_in_path("verilator_bin") {
        return Some(p);
    }
    if let Some(p) = find_in_path("verilator") {
        // The perl wrapper — usable only if it runs; prefer _bin siblings.
        if let Some(bin) = p.parent() {
            let native = bin.join(if cfg!(windows) { "verilator_bin.exe" } else { "verilator_bin" });
            if native.is_file() {
                return Some(native);
            }
        }
        return Some(p);
    }
    // Common MSYS2 install locations.
    for prefix in ["C:/msys64", "C:/msys32", "C:/tools/msys64"] {
        let p = PathBuf::from(prefix).join("mingw64/bin/verilator_bin.exe");
        if p.is_file() {
            return Some(p);
        }
    }
    None
}

/// Locate make. Prefers `mingw32-make` from the verilator toolchain dir
/// (native binary, no MSYS runtime needed).
fn find_make(verilator: &Path) -> Option<PathBuf> {
    if let Some(explicit) = std::env::var_os("MAKE") {
        let p = PathBuf::from(explicit);
        if p.is_file() {
            return Some(p);
        }
    }
    let bin = verilator.parent()?;
    let candidate = bin.join(if cfg!(windows) { "mingw32-make.exe" } else { "make" });
    if candidate.is_file() {
        return Some(candidate);
    }
    find_in_path("mingw32-make").or_else(|| find_in_path("make"))
}

/// Windows-style VERILATOR_ROOT for the verilator toolchain at `verilator`
/// (`<prefix>/share/verilator`), verified to contain verilated.mk. None when
/// the layout doesn't match (make then uses the .mk's own path).
fn verilator_root(verilator: &Path) -> Option<PathBuf> {
    let prefix = verilator.parent()?.parent()?;
    let root = prefix.join("share/verilator");
    if root.join("include/verilated.mk").is_file() {
        Some(root)
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Harness generation
// ---------------------------------------------------------------------------

/// Generate the C++ harness for the compiled top module: a stdin/stdout line
/// protocol (`set PORT HEX` / `get PORT` / `eval` / `finish`) so host Rust
/// code can drive the model interactively. With `trace`, eval steps also
/// dump VCD frames to wave.vcd (requires `--trace` on the verilator run).
fn harness_cpp(top: &ModuleInfo, trace: bool) -> String {
    let mut set_cases = String::new();
    let mut get_cases = String::new();
    for p in &top.ports {
        let name = &p.name;
        set_cases.push_str(&format!(
            "        else if (!strcmp(name, \"{name}\")) dut->{name} = ({t})v;\n",
            t = p.ctype()
        ));
        get_cases.push_str(&format!(
            "        else if (!strcmp(name, \"{name}\")) printf(\"%llx\\n\", (unsigned long long)dut->{name});\n"
        ));
    }
    let (trace_include, trace_decl, trace_init, trace_dump, trace_close) = if trace {
        (
            "#include \"verilated_vcd_c.h\"\n",
            "static VerilatedVcdC* tfp = NULL;\nstatic vluint64_t sim_time = 0;\n",
            "    Verilated::traceEverOn(true);\n    tfp = new VerilatedVcdC;\n    dut->trace(tfp, 99);\n    tfp->open(\"wave.vcd\");\n",
            "            if (tfp) tfp->dump(sim_time++);\n",
            "    if (tfp) tfp->close();\n",
        )
    } else {
        ("", "", "", "", "")
    };
    format!(
        r#"// Auto-generated by typort sim (do not edit).
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include "V{top_name}.h"
#include "verilated.h"
{trace_include}{trace_decl}
int main(int argc, char** argv) {{
    Verilated::commandArgs(argc, argv);
    V{top_name}* dut = new V{top_name};
{trace_init}    char line[512];
    while (fgets(line, sizeof line, stdin)) {{
        if (strncmp(line, "set ", 4) == 0) {{
            char name[128]; char hex[128];
            if (sscanf(line + 4, "%127s %127s", name, hex) != 2) {{ printf("ERR set args\n"); fflush(stdout); continue; }}
            unsigned long long v = strtoull(hex, NULL, 16);
            if (0) {{}}
{set_cases}            else {{ printf("ERR unknown port %s\n", name); fflush(stdout); continue; }}
            printf("ok\n");
        }} else if (strncmp(line, "get ", 4) == 0) {{
            char name[128];
            sscanf(line + 4, "%127s", name);
            if (0) {{}}
{get_cases}            else printf("ERR unknown port %s\n", name);
        }} else if (strncmp(line, "eval", 4) == 0) {{
            dut->eval();
{trace_dump}            printf("ok\n");
        }} else if (strncmp(line, "finish", 6) == 0) {{
            break;
        }} else {{
            printf("ERR bad cmd\n");
        }}
        fflush(stdout);
    }}
    dut->final();
{trace_close}    delete dut;
    return 0;
}}
"#,
        top_name = top.name,
        set_cases = set_cases,
        get_cases = get_cases,
        trace_include = trace_include,
        trace_decl = trace_decl,
        trace_init = trace_init,
        trace_dump = trace_dump,
        trace_close = trace_close,
    )
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
    /// Extra verilator compile arguments.
    pub verilator_args: Vec<String>,
    /// Compile with VCD tracing (--trace + harness dump); the model writes
    /// wave.vcd in its working directory.
    pub trace: bool,
}

/// A successfully compiled simulation model.
pub struct CompiledModel {
    pub exe: PathBuf,
    pub workdir: PathBuf,
    pub manifest: DesignManifest,
}

fn run_tool(cmd: &mut Command, tool: &str) -> Result<String, SimError> {
    let output = cmd
        .output()
        .map_err(|e| SimError::CommandFailed { tool: tool.to_string(), output: e.to_string() })?;
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    if !output.status.success() {
        // Keep the tail: verilator errors point at the offending line.
        let tail: String = text.chars().rev().take(2000).collect::<Vec<_>>().into_iter().rev().collect();
        return Err(SimError::CommandFailed { tool: tool.to_string(), output: tail });
    }
    Ok(text)
}

impl SimConfig {
    /// Elaborate the sources, generate the harness, and compile the model
    /// with verilator + make. Returns the executable path and manifest.
    pub fn compile(&self) -> Result<CompiledModel, SimError> {
        let top_name = emit::top_module_name(&self.top)
            .map_err(|e| SimError::Emit(e))?
            .to_string();

        let mut sources = Vec::with_capacity(self.sources.len());
        for path in &self.sources {
            let canonical = path.canonicalize().unwrap_or_else(|_| path.clone());
            let text = fs::read_to_string(path)
                .map_err(|e| SimError::Io(io::Error::new(e.kind(), format!("reading {}: {e}", path.display()))))?;
            let uri = lsp_types::Url::from_file_path(&canonical)
                .map_err(|()| SimError::Emit(emit::EmitError::BadTop(path.display().to_string())))?;
            sources.push((uri, text));
        }
        let emitted = emit::emit_design(&sources, &self.top, true)?;
        let manifest = DesignManifest::from_json(
            emitted.manifest.as_deref().unwrap_or("{}"),
        )?;
        let top_info = manifest
            .top_module()
            .ok_or_else(|| SimError::BadManifest(format!("top module '{top_name}' missing from manifest")))?
            .clone();

        let verilator = find_verilator().ok_or_else(|| {
            SimError::ToolMissing("verilator not found (set VERILATOR or install MSYS2/mingw64 verilator)".into())
        })?;
        let make = find_make(&verilator).ok_or_else(|| {
            SimError::ToolMissing("make not found (mingw32-make or make on PATH, or set MAKE)".into())
        })?;

        fs::create_dir_all(&self.workdir)?;
        let verilog_path = self.workdir.join(format!("{top_name}.v"));
        fs::write(&verilog_path, &emitted.verilog)?;
        let harness_path = self.workdir.join("harness.cpp");
        fs::write(&harness_path, harness_cpp(&top_info, self.trace))?;
        let manifest_path = self.workdir.join(format!("{top_name}.manifest.json"));
        fs::write(&manifest_path, emitted.manifest.as_deref().unwrap_or("{}"))?;

        let objdir = self.workdir.join(format!("obj_{top_name}"));
        let model_name = "top_model";

        // 1. verilator: generate C++ + makefile. File arguments are passed
        //    RELATIVE with cwd=workdir: verilator_bin misparses absolute
        //    Windows paths (treats them as module names to -y-search).
        let mut vcmd = Command::new(&verilator);
        vcmd
            .current_dir(&self.workdir)
            .args(["--cc", "--exe", "-Wno-fatal"])
            .arg("--top-module").arg(&top_name)
            .arg("-Mdir").arg(format!("obj_{top_name}"))
            .arg("-o").arg(model_name)
            .args(&self.verilator_args);
        if self.trace {
            vcmd.arg("--trace");
        }
        vcmd.arg("harness.cpp").arg(format!("{top_name}.v"));
        run_tool(&mut vcmd, "verilator")?;

        // 2. make: build the model (run inside the obj dir, like the
        //    verified probe / verify.py invocation). VERILATOR_ROOT is
        //    passed as a command-line override (the generated .mk
        //    hardcodes an MSYS2-style path native make cannot read) and
        //    the toolchain bin dir is prepended to PATH so g++/ranlib
        //    resolve.
        let mut mcmd = Command::new(&make);
        mcmd
            .current_dir(&objdir)
            .arg("-f")
            .arg(format!("V{top_name}.mk"));
        if let Some(root) = verilator_root(&verilator) {
            // Forward slashes only: the mk feeds this path to perl (the
            // verilator_includer step), and perl eats backslashes as
            // escapes — C:\msys64\... becomes C:msys64...
            let root = root.display().to_string().replace('\\', "/");
            mcmd.arg(format!("VERILATOR_ROOT={root}"));
        }
        let old_path = std::env::var_os("PATH").unwrap_or_default();
        if let Some(bin) = verilator.parent() {
            mcmd.env(
                "PATH",
                std::env::join_paths(std::iter::once(bin.to_path_buf()).chain(std::env::split_paths(&old_path)))
                    .unwrap_or(old_path.clone()),
            );
        }
        run_tool(&mut mcmd, "make")?;

        let exe = objdir.join(if cfg!(windows) {
            format!("{model_name}.exe")
        } else {
            model_name.to_string()
        });
        if !exe.is_file() {
            return Err(SimError::CommandFailed {
                tool: "make".into(),
                output: format!("model binary not produced at {}", exe.display()),
            });
        }
        Ok(CompiledModel { exe, workdir: self.workdir.clone(), manifest })
    }
}
