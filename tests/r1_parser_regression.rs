// R1 regression pins (2026-10-11 review round 1): parser surface fixes.
// 1. empty / comment-only files parse to zero declarations (was: "expected
//    at least one element");
// 2. block comments nest (Rust-style): `/* a /* b */ c */` blanks through the
//    matching close, the trailing `c */` no longer leaks as garbage tokens;
// 3. `Type 4294967295` (u32::MAX) errors with a span ON the level token in
//    both engines (was: empty span rendering at 1:1 in the reference engine,
//    and a bare wrapping `x + 1` in the twin machine).

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
    let uri = Url::parse("file:///probe/r1_pin.typort").unwrap();
    b.on_change::<false>(TextDocumentItem { uri: uri.clone(), text, version: None });
    b.client.diags.lock().unwrap().iter()
        .filter(|(u, _, _)| u == &uri)
        .flat_map(|(_, d, _)| d.iter().cloned())
        .collect()
}

fn errors_of(ds: &[lsp_types::Diagnostic]) -> Vec<&lsp_types::Diagnostic> {
    ds.iter().filter(|d| d.severity == Some(lsp_types::DiagnosticSeverity::ERROR)).collect()
}

#[test]
fn empty_file_is_not_an_error() {
    for (name, text) in [("empty", ""), ("comment-only", "// nothing\n/* block */\n"),
                         ("eof-comment", "// no trailing newline")] {
        let ds = run(Engine::Reference, text);
        let es = errors_of(&ds);
        assert!(es.is_empty(), "{name}: expected no errors, got {es:?}");
    }
}

#[test]
fn nested_block_comments() {
    // The def after the nested comment must elaborate and print.
    let ds = run(Engine::Reference,
        "/* outer /* inner */ still outer */\ndef x: Nat = 1\nprintln(x)\n");
    assert!(errors_of(&ds).is_empty(), "{ds:?}");
    assert!(ds.iter().any(|d| d.severity == Some(lsp_types::DiagnosticSeverity::INFORMATION)
        && d.message.contains('1')), "println note missing: {ds:?}");

    // Unterminated nested comment: everything to EOF is blanked, no garbage.
    let ds = run(Engine::Reference, "/* open /* deeper\ndef x: Nat = 1\n");
    assert!(errors_of(&ds).is_empty(), "{ds:?}");
}

#[test]
fn universe_max_level_error_has_real_span() {
    // Reference engine, exact semantics: u32::MAX level errors with the span
    // ON the level digits (offset 12 in this line), and u32::MAX - 1 with a
    // matching body is accepted (the largest usable level).
    let err = elaboration_zoo_lsp::L13_namespace::run_with_prelude(
        "def U: Type 4294967295 = Type 4294967294\n").unwrap_err();
    assert!(err.0.data.contains("too large"), "{:?}", err.0.data);
    assert_eq!(err.0.start_offset, 12, "span must sit on the level digits, not file start");

    elaboration_zoo_lsp::L13_namespace::run_with_prelude(
        "def U: Type 4294967294 = Type 4294967293\n").expect("MAX-1 is the largest usable level");

    // Through the Backend path the same program must also be rejected (the
    // reported message can differ -- error-path divergence is a recorded
    // quirk -- but it must never wrap around and be accepted).
    let ds = run(Engine::Reference, "def U: Type 4294967295 = Type 4294967294\n");
    assert!(!errors_of(&ds).is_empty(), "Backend must reject the MAX level");
}

#[test]
fn twin_universe_max_level_does_not_wrap() {
    // The twin machine arm previously did a bare `x + 1`; on u32::MAX that
    // panics (debug) or silently wraps to `Type 0` (release), accepting
    // `Type 4294967295 : Type 0`. It must take the same checked error path.
    let ds = run(Engine::Twin, "def U: Type 4294967295 = Type 0\n");
    let es = errors_of(&ds);
    assert!(es.iter().any(|d| d.message.contains("too large")),
        "twin should report the overflow: {ds:?}");
}
