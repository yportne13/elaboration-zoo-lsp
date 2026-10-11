// R4 regression pin (2026-10-11 review round 4): termination on
// annotation-driven lambdas.
//
// `def f: Nat -> Nat = n => match n { case succ(m) => f(m) }` was rejected
// ("cannot prove termination") because the walker's structural roots were
// only the *declared* params (params.len() == 0 here). Both engines now
// count the body's leading explicit lambdas as roots when the def has no
// declared params; non-structural self-calls in the same shape stay
// rejected.

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
    let uri = Url::parse("file:///probe/r4_pin.typort").unwrap();
    b.on_change::<false>(TextDocumentItem { uri: uri.clone(), text, version: None });
    b.client.diags.lock().unwrap().iter()
        .filter(|(u, _, _)| u == &uri)
        .flat_map(|(_, d, _)| d.iter().cloned())
        .collect()
}

fn has_err(ds: &[lsp_types::Diagnostic]) -> bool {
    ds.iter().any(|d| d.severity == Some(lsp_types::DiagnosticSeverity::ERROR))
}

#[test]
fn annotation_lambda_recursion_accepted() {
    let src = "def f: Nat -> Nat = n => match n {\n  case zero => 0\n  case succ(m) => f(m)\n}\nprintln(f(3))\n";
    for engine in [Engine::Reference, Engine::Twin] {
        let ds = run(engine, src);
        assert!(!has_err(&ds), "{engine:?}: structural recursion through a lambda must be accepted: {ds:?}");
        assert!(ds.iter().any(|d| d.severity == Some(lsp_types::DiagnosticSeverity::INFORMATION)),
            "{engine:?}: println note missing: {ds:?}");
    }
}

#[test]
fn annotation_lambda_nonstructural_still_rejected() {
    let src = "def bad2: Nat -> Nat = n => bad2(n)\n";
    for engine in [Engine::Reference, Engine::Twin] {
        let ds = run(engine, src);
        assert!(has_err(&ds), "{engine:?}: bare self-call must stay rejected: {ds:?}");
        assert!(ds.iter().any(|d| d.message.contains("termination")),
            "{engine:?}: expected the termination diagnostic: {ds:?}");
    }
}
