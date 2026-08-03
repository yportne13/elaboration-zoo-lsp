// Two-phase `println` tests for the LSP analysis path.
// Verifies that tyck errors are published before the (potentially slow)
// `nf` of `println` args runs, and that the deferred println results are
// published afterwards as INFORMATION diagnostics.

use std::sync::{Arc, Mutex};

use elaboration_zoo_lsp::client::ClientLike;
use elaboration_zoo_lsp::Backend;
use lsp_types::{Diagnostic, DiagnosticSeverity, MessageType, Url};

#[derive(Default)]
struct CapturingClient {
    diagnostics: Mutex<Vec<(Url, Vec<Diagnostic>, Option<i32>)>>,
}

impl ClientLike for CapturingClient {
    fn publish_diagnostics(&self, uri: Url, diagnostics: Vec<Diagnostic>, version: Option<i32>) {
        self.diagnostics.lock().unwrap().push((uri, diagnostics, version));
    }
    fn show_message(&self, _typ: MessageType, _message: String) {}
    fn log_message(&self, _typ: MessageType, _message: String) {}
}

fn publishes_for(
    b: &Arc<Backend<CapturingClient>>,
    uri: &Url,
) -> Vec<(Url, Vec<Diagnostic>, Option<i32>)> {
    b.client
        .diagnostics
        .lock()
        .unwrap()
        .iter()
        .filter(|(u, _, _)| u == uri)
        .cloned()
        .collect()
}

#[test]
fn deferred_println_phase1_errors_then_phase2_values() {
    let client = CapturingClient::default();
    let b = Backend::new(client);
    b.load_prelude_skip_hdl();
    let uri = Url::parse("file:///p.typort").unwrap();

    // Phase 1: tyck must succeed for this file, so the first publish has no
    // INFORMATION (println) diagnostics; phase 2 adds exactly one.
    b.process_file(&uri, "def foo: Nat = succ zero\nprintln foo\n", Some(1));

    let mine = publishes_for(&b, &uri);
    assert!(mine.len() >= 2, "expected phase1 + phase2 publishes, got {}", mine.len());

    let (_, first, _) = &mine[0];
    assert!(
        first.iter().all(|d| d.severity != Some(DiagnosticSeverity::INFORMATION)),
        "phase 1 must not contain println INFORMATION diagnostics"
    );

    let (_, last, _) = mine.last().unwrap();
    let info: Vec<_> = last
        .iter()
        .filter(|d| d.severity == Some(DiagnosticSeverity::INFORMATION))
        .collect();
    assert_eq!(info.len(), 1, "expected exactly one println INFORMATION diagnostic");
    assert_eq!(info[0].message, "1", "println value = {:?}", info[0].message);
}

#[test]
fn deferred_println_with_tyck_error_still_publishes_errors_first() {
    let client = CapturingClient::default();
    let b = Backend::new(client);
    b.load_prelude_skip_hdl();
    let uri = Url::parse("file:///err.typort").unwrap();

    // A well-typed `println` plus an independent type error later in the file:
    // phase 1 must carry the ERROR, phase 2 the println value.
    b.process_file(
        &uri,
        "def good: Nat = succ zero\nprintln good\ndef bad: Nat = true\n",
        Some(1),
    );

    let mine = publishes_for(&b, &uri);
    assert!(mine.len() >= 2, "expected phase1 + phase2 publishes, got {}", mine.len());

    let (_, first, _) = &mine[0];
    assert!(
        first.iter().any(|d| d.severity == Some(DiagnosticSeverity::ERROR)),
        "phase 1 must contain the tyck ERROR"
    );
    assert!(
        first.iter().all(|d| d.severity != Some(DiagnosticSeverity::INFORMATION)),
        "phase 1 must not yet contain println output"
    );

    let (_, last, _) = mine.last().unwrap();
    assert!(
        last.iter().any(|d| d.severity == Some(DiagnosticSeverity::ERROR)),
        "phase 2 must keep the tyck ERROR"
    );
    assert!(
        last.iter().any(|d| d.severity == Some(DiagnosticSeverity::INFORMATION)),
        "phase 2 must add the println output"
    );
}
