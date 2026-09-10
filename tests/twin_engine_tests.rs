// Twin-engine LSP wiring tests (stage 3a/4 of docs/lsp-twin-wiring-2026-09.md).
//
// The `Engine::Twin` path replays the prelude + a file through the bump
// elaborator (`run_decls_with_prelude`) and serves hover / goto / completion /
// inlay from the resulting owned snapshot.  These tests drive the real
// `Backend` surface (load_prelude -> process_file -> hover_at / completion_at)
// and check the twin results against the reference engine on the same source.

use std::sync::{Arc, Mutex};

use elaboration_zoo_lsp::client::ClientLike;
use elaboration_zoo_lsp::{Backend, Engine};
use lsp_types::{CompletionParams, CompletionResponse, MessageType, PartialResultParams, Position, TextDocumentIdentifier, TextDocumentPositionParams, Url, WorkDoneProgressParams};

#[derive(Default)]
struct CapturingClient {
    diagnostics: Mutex<Vec<(Url, Vec<lsp_types::Diagnostic>, Option<i32>)>>,
}

impl ClientLike for CapturingClient {
    fn publish_diagnostics(&self, uri: Url, diagnostics: Vec<lsp_types::Diagnostic>, version: Option<i32>) {
        self.diagnostics.lock().unwrap().push((uri, diagnostics, version));
    }
    fn show_message(&self, _typ: MessageType, _message: String) {}
    fn log_message(&self, _typ: MessageType, _message: String) {}
}

fn backend(engine: Engine) -> Arc<Backend<CapturingClient>> {
    let b = Backend::new_with_engine(CapturingClient::default(), engine);
    b.load_prelude_skip_hdl();
    b
}

fn errors(b: &Arc<Backend<CapturingClient>>, uri: &Url) -> Vec<String> {
    b.client.diagnostics.lock().unwrap().iter()
        .filter(|(u, _, _)| u == uri)
        .flat_map(|(_, d, _)| d.iter())
        .filter(|d| d.severity == Some(lsp_types::DiagnosticSeverity::ERROR))
        .map(|d| d.message.clone())
        .collect()
}

fn hover_text(b: &Arc<Backend<CapturingClient>>, uri: &Url, offset: usize) -> Option<String> {
    b.hover_at(uri, Position::new(0, offset as u32)).map(|h| match h.contents {
        lsp_types::HoverContents::Markup(m) => m.value,
        lsp_types::HoverContents::Scalar(_) => panic!("scalar hover"),
        lsp_types::HoverContents::Array(_) => panic!("array hover"),
        _ => panic!("unknown hover"),
    })
}

/// Hovering a tuple element resolves through the twin snapshot to the
/// element's own type, same as the reference engine.
#[test]
fn twin_hover_matches_reference_on_tuple_element() {
    let uri = Url::parse("file:///twin_tup.typort").unwrap();
    let src = "def foo(a: Nat, b: Boolean): Tuple2[Nat, Boolean] = (a, b)";
    let base = src.rfind("(a, b)").unwrap();

    let rb = backend(Engine::Reference);
    rb.process_file(&uri, src, Some(1));
    assert!(errors(&rb, &uri).is_empty(), "reference tyck errors: {:?}", errors(&rb, &uri));

    let tb = backend(Engine::Twin);
    tb.process_file(&uri, src, Some(1));
    // Twin diagnostics still come from the reference engine, so the source
    // must be error-free for both.
    assert!(errors(&tb, &uri).is_empty(), "twin tyck errors: {:?}", errors(&tb, &uri));

    for off in [base + 1, base + 4] {
        let r = hover_text(&rb, &uri, off);
        let t = hover_text(&tb, &uri, off);
        assert_eq!(t, r, "hover mismatch at offset {off}");
        assert!(t.is_some(), "twin produced no hover at offset {off}");
    }
}

/// A local variable hover (binder name) is served from the twin's push-site
/// entries with the same rendered type as the reference.
#[test]
fn twin_hover_matches_reference_on_local() {
    let uri = Url::parse("file:///twin_local.typort").unwrap();
    // Avoid prelude name collisions (`id` is a prelude def).
    let src = "def myfn(n: Nat): Nat = n";
    let n_use = src.rfind("= n").unwrap() + 2;

    let rb = backend(Engine::Reference);
    rb.process_file(&uri, src, Some(1));
    let tb = backend(Engine::Twin);
    tb.process_file(&uri, src, Some(1));

    let r = hover_text(&rb, &uri, n_use);
    let t = hover_text(&tb, &uri, n_use);
    assert_eq!(t, r, "local hover mismatch");
    assert!(t.is_some(), "twin produced no local hover");
}

/// Member-access completion is served from the twin completion table.
#[test]
fn twin_completion_matches_reference() {
    let uri = Url::parse("file:///twin_comp.typort").unwrap();
    // Member access so the completion table is populated; `Tuple2` is a
    // prelude struct with fields `_1`/`_2`.
    let src = "def f(p: Tuple2[Nat, Nat]): Nat = p.";
    let cursor = src.find("p.").unwrap() + 2;

    let rb = backend(Engine::Reference);
    rb.process_file(&uri, src, Some(1));
    let tb = backend(Engine::Twin);
    tb.process_file(&uri, src, Some(1));

    let labels = |b: &Arc<Backend<CapturingClient>>| -> Vec<String> {
        let params = CompletionParams {
            text_document_position: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri: uri.clone() },
                position: Position::new(0, cursor as u32),
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
            context: None,
        };
        match b.completion_at(params).unwrap() {
            Some(CompletionResponse::Array(items)) => items.into_iter().map(|i| i.label).collect(),
            other => panic!("unexpected completion response: {other:?}"),
        }
    };

    let mut r = labels(&rb);
    let mut t = labels(&tb);
    r.sort();
    t.sort();
    assert_eq!(t, r, "completion mismatch");
}

/// Inlay hints are served from the twin table.
#[test]
fn twin_inlay_matches_reference() {
    let uri = Url::parse("file:///twin_inlay.typort").unwrap();
    let src = "def f(n: Nat): Nat = n\n";

    let rb = backend(Engine::Reference);
    rb.process_file(&uri, src, Some(1));
    let tb = backend(Engine::Twin);
    tb.process_file(&uri, src, Some(1));

    // Compare through the engine-routing handler.
    fn hint_labels(b: &Arc<Backend<CapturingClient>>, uri: &Url) -> Vec<String> {
        b.inlay_hint_at(uri).unwrap_or_default().into_iter()
            .map(|h| match h.label {
                lsp_types::InlayHintLabel::String(s) => s,
                other => format!("{other:?}"),
            })
            .collect()
    }
    assert_eq!(hint_labels(&tb, &uri), hint_labels(&rb, &uri), "inlay mismatch");
}

/// End-to-end twin pass on a real HDL example (full HDL prelude, module with
/// `sum := u.sum` vconnT expansion): the twin must produce a non-empty
/// observation snapshot without panicking, and hovering a known signal
/// identifier must agree with the reference engine.
#[test]
fn twin_observes_real_hdl_example() {
    let src = include_str!("../examples/hdl/09-hierarchy.typort");
    // `root`/`u` are the module instance names in 09-hierarchy.
    let probe = src.find("u.").or_else(|| src.find("sum")).unwrap();

    let tb = {
        let b = Backend::new_with_engine(CapturingClient::default(), Engine::Twin);
        b.load_prelude();
        b
    };
    let uri = Url::parse("file:///twin_hdl.typort").unwrap();
    tb.process_file(&uri, src, Some(1));
    let snap = tb.twin_tables.get(uri.as_str())
        .unwrap_or_else(|| panic!("twin produced no HDL snapshot; diagnostics: {:?}", errors(&tb, &uri)));
    assert!(!snap.hover.is_empty(), "twin HDL snapshot has no hover entries");
    assert!(!snap.completion.is_empty(), "twin HDL snapshot has no completion entries");
    drop(snap);

    let rb = {
        let b = Backend::new_with_engine(CapturingClient::default(), Engine::Reference);
        b.load_prelude();
        b
    };
    rb.process_file(&uri, src, Some(1));

    // Hover a specific character and compare engines, allowing the reference
    // to have no entry (twin-only entries are permitted by the parity
    // contract, just not heterogeneous ones).
    if let Some(r) = hover_text(&rb, &uri, probe) {
        assert_eq!(hover_text(&tb, &uri, probe).as_deref(), Some(r.as_str()), "HDL hover mismatch");
    }
}
