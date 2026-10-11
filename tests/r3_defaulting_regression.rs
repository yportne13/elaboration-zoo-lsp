// R3 regression pin (2026-10-11 review round 3): Nat-defaulting visibility.
//
// `def t: Type 0 = _` used to elaborate silently with the type-valued meta
// defaulted to Nat (Lean-style fallback) -- program meaning changed with no
// diagnostic. Both engines now push a TY001 line on the CheckIssues channel;
// it must surface as a WARNING anchored at the def, without blocking the def.

use std::sync::{Arc, Mutex};

use elaboration_zoo_lsp::client::ClientLike;
use elaboration_zoo_lsp::{Backend, Engine, TextDocumentItem};
use lsp_types::{MessageType, Url};

#[derive(Default)]
struct Cap {
    diags: Mutex<Vec<(Url, Vec<lsp_types::Diagnostic>, Option<i32>)>>,
}

impl ClientLike for Cap {
    fn publish_diagnostics(&self, uri: Url, d: Vec<lsp_types::Diagnostic>, v: Option<i32>) {
        self.diags.lock().unwrap().push((uri, d, v));
    }
    fn show_message(&self, _: MessageType, _: String) {}
    fn log_message(&self, _: MessageType, _: String) {}
}

fn run(engine: Engine, text: &str) -> Vec<lsp_types::Diagnostic> {
    let b = Backend::new_with_engine(Cap::default(), engine);
    b.load_prelude();
    let uri = Url::parse("file:///probe/r3_pin.typort").unwrap();
    b.on_change::<false>(TextDocumentItem { uri: uri.clone(), text, version: None });
    b.client.diags.lock().unwrap().iter()
        .filter(|(u, _, _)| u == &uri)
        .flat_map(|(_, d, _)| d.iter().cloned())
        .collect()
}

#[test]
fn type0_hole_defaulting_warns_both_engines() {
    for engine in [Engine::Reference, Engine::Twin] {
        let ds = run(engine, "def t: Type 0 = _\nprintln(3)\n");
        let warns: Vec<_> = ds.iter()
            .filter(|d| d.severity == Some(lsp_types::DiagnosticSeverity::WARNING))
            .collect();
        assert!(
            warns.iter().any(|w| w.message.contains("TY001") && w.message.contains("defaulted to Nat")),
            "{engine:?}: expected a TY001 defaulting warning, got {ds:?}"
        );
        assert!(
            !ds.iter().any(|d| d.severity == Some(lsp_types::DiagnosticSeverity::ERROR)),
            "{engine:?}: defaulting must not turn into an error: {ds:?}"
        );
        // The def still works: println(3) produced its INFORMATION note.
        assert!(
            ds.iter().any(|d| d.severity == Some(lsp_types::DiagnosticSeverity::INFORMATION)),
            "{engine:?}: println note missing: {ds:?}"
        );
    }
}

#[test]
fn solved_holes_do_not_warn() {
    // `_ = 3` solves the annotation meta by unification -- no defaulting, so
    // no TY001. The lazy-domain lambda (`def f = x => x`) resolves at first
    // use and must not warn either (recorded quirk, not defaulting).
    for engine in [Engine::Reference, Engine::Twin] {
        let ds = run(engine, "def f: _ = 3\ndef g = x => x\nprintln(f)\nprintln(g(1))\n");
        assert!(
            !ds.iter().any(|d| d.severity == Some(lsp_types::DiagnosticSeverity::WARNING)
                && d.message.contains("TY001")),
            "{engine:?}: no TY001 expected here: {ds:?}"
        );
        assert!(
            !ds.iter().any(|d| d.severity == Some(lsp_types::DiagnosticSeverity::ERROR)),
            "{engine:?}: {ds:?}"
        );
    }
}
