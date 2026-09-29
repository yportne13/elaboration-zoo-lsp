//! Drift guard: every code snippet in the `typort quick` cheat-sheet must
//! still type-check against the current elaborator. `tests/quick_validate.typort`
//! is a curated sample of the exact syntax shown in `src/quick.rs`; if the
//! language changes and this stops compiling, the cheat-sheet needs updating.
//!
//! A second guard covers the inverse direction: the grammar only accepts
//! newline separators for enum cases / struct fields / match arms, and the
//! cheat-sheet once showed one-line `;`-separated snippets that learners
//! copied verbatim and failed. The negative test pins those forms as
//! *invalid* so a parser relaxation or a sheet regression cannot slip past
//! the (positive-only) validate sample.

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

#[test]
fn quick_cheatsheet_one_line_semicolon_forms_stay_invalid() {
    // Negative drift guard: these are the one-line `;`-separated shapes that
    // used to be printed in src/quick.rs (enum cases, struct fields, match
    // arms). The grammar only accepts newline separators, so each snippet
    // must keep producing at least one ERROR diagnostic. If this starts
    // failing because the forms became valid, update src/quick.rs and
    // tests/quick_validate.typort deliberately — not by accident.
    let one_line_forms: &[&str] = &[
        // enum cases with payloads on one line (quick.rs `match` section)
        "enum Tree[T] { leaf(v: T); node(l: Tree[T], r: Tree[T]) }",
        // bare enum cases on one line (quick.rs `adt` section)
        "enum Color { red; green; blue }",
        // struct fields on one line (quick.rs `adt` section)
        "struct Pair[A, B] { first: A; second: B }",
        // match arms on one line (quick.rs `tc` section)
        concat!(
            "trait PrettyNeg {\n",
            "    def pretty: String\n",
            "}\n",
            "impl PrettyNeg for Boolean {\n",
            "    def pretty: String = match this { case true => \"true\"; case false => \"false\" }\n",
            "}",
        ),
    ];

    for (i, text) in one_line_forms.iter().enumerate() {
        let capture = Arc::new(Capture::default());
        let backend = Backend::new(CapturingClient { capture: capture.clone() });
        backend.load_prelude();

        let uri = Url::parse(&format!("file:///quick_negative_{i}.typort")).unwrap();
        backend.on_change::<false>(elaboration_zoo_lsp::TextDocumentItem {
            uri,
            text: *text,
            version: Some(1),
        });

        let diags = capture.diags.lock().unwrap().clone();
        let errors: Vec<&Diagnostic> = diags
            .iter()
            .filter(|d| d.severity == Some(DiagnosticSeverity::ERROR))
            .collect();
        assert!(
            !errors.is_empty(),
            "one-line `;` form #{i} unexpectedly elaborates cleanly; \
             the cheat-sheet drift guard assumes it is invalid",
        );
    }
}
