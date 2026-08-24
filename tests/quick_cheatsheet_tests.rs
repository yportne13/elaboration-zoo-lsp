//! Drift guard: every code snippet in the `typort quick` cheat-sheet must
//! still type-check against the current elaborator. `tests/quick_validate.typort`
//! is a curated sample of the exact syntax shown in `src/quick.rs`; if the
//! language changes and this stops compiling, the cheat-sheet needs updating.

use std::sync::{Arc, Mutex};

use elaboration_zoo_lsp::client::ClientLike;
use elaboration_zoo_lsp::Backend;
use lsp_types::{Diagnostic, DiagnosticSeverity, MessageType, Url};

#[derive(Default)]
struct Capture {
    diags: Mutex<Vec<Diagnostic>>,
}

struct CapturingClient {
    capture: Arc<Capture>,
}

impl ClientLike for CapturingClient {
    fn publish_diagnostics(&self, _uri: Url, diagnostics: Vec<Diagnostic>, _version: Option<i32>) {
        self.capture.diags.lock().unwrap().extend(diagnostics);
    }
    fn show_message(&self, _typ: MessageType, _message: String) {}
    fn log_message(&self, _typ: MessageType, _message: String) {}
}

#[test]
fn quick_cheatsheet_snippets_still_compile() {
    let capture = Arc::new(Capture::default());
    let backend = Backend::new(CapturingClient { capture: capture.clone() });
    backend.load_prelude();

    let text = include_str!("quick_validate.typort");
    let uri = Url::parse("file:///quick_validate.typort").unwrap();
    backend.on_change::<false>(elaboration_zoo_lsp::TextDocumentItem {
        uri,
        text,
        version: Some(1),
    });

    let diags = capture.diags.lock().unwrap().clone();
    let errors: Vec<&Diagnostic> = diags
        .iter()
        .filter(|d| d.severity == Some(DiagnosticSeverity::ERROR))
        .collect();
    assert!(
        errors.is_empty(),
        "cheat-sheet snippets regressed, {} errors:\n{:?}",
        errors.len(),
        errors.iter().map(|e| &e.message).collect::<Vec<_>>()
    );
}
