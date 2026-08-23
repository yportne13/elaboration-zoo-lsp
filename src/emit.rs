//! `typort emit` — elaborate HDL sources and extract the generated Verilog.
//!
//! Verilog generation is a prelude library function (`designVL` in
//! `prelude/hdl/hdl-verilog.typort`); the only way to get the text out was
//! scraping `println` diagnostics off stderr (the approach
//! `tools/spinalhdl-verify/verify.py` regexes). This module is the
//! machine-facing channel instead: elaborate the sources, then a synthetic
//! `println(designVL(<top>.create.tree))` appended to the last source
//! file, and pull the emitted text back out through the diagnostics pipeline.

use std::fmt;
use std::sync::{Arc, Mutex};

use lsp_types::{Diagnostic, DiagnosticSeverity, MessageType, Url};

use crate::client::ClientLike;
use crate::Backend;

/// Diagnostics captured from a throwaway backend, shared so the data
/// outlives the backend that produced it.
#[derive(Clone, Default)]
struct Capture(Arc<Mutex<Vec<(Url, Vec<Diagnostic>)>>>);

/// A `ClientLike` that records published diagnostics instead of rendering them.
struct CapturingClient {
    captured: Capture,
}

impl ClientLike for CapturingClient {
    fn publish_diagnostics(&self, uri: Url, diagnostics: Vec<Diagnostic>, _version: Option<i32>) {
        self.captured.0.lock().unwrap().push((uri, diagnostics));
    }
    fn show_message(&self, _typ: MessageType, _message: String) {}
    fn log_message(&self, _typ: MessageType, _message: String) {}
}

#[derive(Debug)]
pub enum EmitError {
    /// `--top` is not a module name or `name[args]` instantiation.
    BadTop(String),
    /// Elaboration failed; the diagnostic messages (no source context).
    Elaboration(Vec<String>),
    /// The top expression elaborated but produced no output.
    NoOutput,
}

impl fmt::Display for EmitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EmitError::BadTop(top) => {
                write!(f, "invalid top module '{top}': expected a module name or name[args]")
            }
            EmitError::Elaboration(msgs) => {
                write!(f, "elaboration failed:\n{}", msgs.join("\n"))
            }
            EmitError::NoOutput => write!(f, "top module elaborated but emitted no Verilog"),
        }
    }
}

impl std::error::Error for EmitError {}

fn is_identifier(s: &str) -> bool {
    !s.is_empty()
        && s.chars().next().map(|c| c.is_alphabetic() || c == '_').unwrap_or(false)
        && s.chars().all(|c| c.is_alphanumeric() || c == '_')
}

/// `adder[8]` -> `adder.create[8]`, `adder` -> `adder.create`.
fn top_create_expr(top: &str) -> Result<String, EmitError> {
    let top = top.trim();
    match top.find('[') {
        Some(i) => {
            let (name, args) = (&top[..i], &top[i..]);
            if !args.ends_with(']') || !is_identifier(name) {
                return Err(EmitError::BadTop(top.to_string()));
            }
            Ok(format!("{name}.create{args}"))
        }
        None => {
            if !is_identifier(top) {
                return Err(EmitError::BadTop(top.to_string()));
            }
            Ok(format!("{top}.create"))
        }
    }
}

/// Module file stem for a `--top` argument (the part before the argument list).
pub fn top_module_name(top: &str) -> Result<&str, EmitError> {
    let top = top.trim();
    match top.find('[') {
        Some(i) if is_identifier(&top[..i]) => Ok(&top[..i]),
        Some(i) => Err(EmitError::BadTop(top[..i].to_string())),
        None if is_identifier(top) => Ok(top),
        None => Err(EmitError::BadTop(top.to_string())),
    }
}

/// Elaborate `files` (in order) and return the Verilog that `designVL`
/// produces for the `top` instantiation (the top module plus every
/// registered module it transitively instantiates).
///
/// The emit request is appended to the LAST file, not a separate unit:
/// elaboration state (meta variables, the ModuleTree side-effect chain) is
/// per-file, so `designVL` must run in the same file as the module
/// definitions — the same shape as the examples' trailing
/// `println(moduleTreeVL(...))`. Among that file's INFORMATION diagnostics
/// the appended println is the last one (println jobs run in decl order).
pub fn emit_verilog(files: &[(Url, String)], top: &str) -> Result<String, EmitError> {
    if files.is_empty() {
        return Err(EmitError::Elaboration(vec!["no input files".to_string()]));
    }
    // Leading newline terminates a trailing `//` comment in the source file.
    let request = format!("\nprintln(designVL({}.tree))\n", top_create_expr(top)?);
    let last_uri = files.last().unwrap().0.clone();

    let captured = Capture::default();
    let backend = Backend::new(CapturingClient { captured: captured.clone() });
    backend.load_prelude();

    for (uri, text) in files {
        let text = if uri == &last_uri {
            format!("{text}{request}")
        } else {
            text.clone()
        };
        backend.process_file(uri, &text, None);
    }

    let mut errors = Vec::new();
    let mut outputs = Vec::new();
    for (uri, diags) in captured.0.lock().unwrap().iter() {
        for d in diags {
            // Anything that is not a warning/note-class diagnostic (including
            // an unset severity, which is how bare parse errors arrive) fails
            // the emit.
            let is_error = !matches!(
                d.severity,
                Some(DiagnosticSeverity::WARNING)
                    | Some(DiagnosticSeverity::INFORMATION)
                    | Some(DiagnosticSeverity::HINT)
            );
            if is_error {
                errors.push(format!("{}: {}", uri.as_str(), d.message));
            } else if d.severity == Some(DiagnosticSeverity::INFORMATION) && *uri == last_uri {
                outputs.push(d.message.clone());
            }
        }
    }
    if !errors.is_empty() {
        return Err(EmitError::Elaboration(errors));
    }
    match outputs.pop() {
        Some(verilog) => Ok(verilog),
        None => Err(EmitError::NoOutput),
    }
}
