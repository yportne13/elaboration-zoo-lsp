// Round-2 engine-quirks diagnostic pins (task-18).
//
// Pins the targeted, error-path-only diagnostic for the *unsupported*
// `(e : T)` type-ascription syntax:
//
//   * the directional hint IS emitted, and the pre-existing parse errors
//     (`expected ')' , found ':'` / `expected newline`) are still emitted too;
//   * valid code is untouched (binder form, plain groups, tuple literals);
//   * a clean HDL example gets NO ascription diagnostic.  This is a real
//     regression pin: the first implementation counted only `(`…`)` while
//     scanning, so Verilog part-select colons (`{w[7:0], w[15:8]}`) inside a
//     macro-expanded group were misread as ascriptions and 3 bogus errors were
//     published for examples/hdl/24-verilog-practice.typort (which also broke
//     twin/reference diagnostic ordering in tests/twin_engine_tests.rs).

use std::sync::{Arc, Mutex};

use elaboration_zoo_lsp::client::ClientLike;
use elaboration_zoo_lsp::{Backend, Engine};
use lsp_types::{DiagnosticSeverity, MessageType, Url};

#[derive(Default)]
struct CapturingClient {
    diagnostics: Mutex<Vec<(Url, Vec<lsp_types::Diagnostic>, Option<i32>)>>,
    #[allow(dead_code)]
    logs: Mutex<Vec<String>>,
}

impl ClientLike for CapturingClient {
    fn publish_diagnostics(
        &self,
        uri: Url,
        diagnostics: Vec<lsp_types::Diagnostic>,
        version: Option<i32>,
    ) {
        self.diagnostics.lock().unwrap().push((uri, diagnostics, version));
    }
    fn show_message(&self, _typ: MessageType, _message: String) {}
    fn log_message(&self, _typ: MessageType, message: String) {
        self.logs.lock().unwrap().push(message);
    }
}

/// Parser-level pins do not need the HDL prelude (keeps this file fast).
fn backend(engine: Engine) -> Arc<Backend<CapturingClient>> {
    let b = Backend::new_with_engine(CapturingClient::default(), engine);
    b.load_prelude_skip_hdl();
    b
}

fn backend_hdl(engine: Engine) -> Arc<Backend<CapturingClient>> {
    let b = Backend::new_with_engine(CapturingClient::default(), engine);
    b.load_prelude();
    b
}

const HINT: &str = "supports neither type ascription";

/// Diagnostics of the last publish for `uri`, as plain messages.
fn messages(b: &Arc<Backend<CapturingClient>>, uri: &Url) -> Vec<String> {
    let d = b.client.diagnostics.lock().unwrap();
    match d.iter().filter(|(x, _, _)| x == uri).last().cloned() {
        Some((_, ds, _)) => ds.into_iter().map(|d| d.message).collect(),
        None => Vec::new(),
    }
}

fn errors(msgs: &[String]) -> Vec<&String> {
    msgs.iter().filter(|m| m.contains("expected") || m.contains(HINT)).collect()
}

fn hint_count(msgs: &[String]) -> usize {
    msgs.iter().filter(|m| m.contains(HINT)).count()
}

fn run(src: &str) -> Vec<String> {
    let uri = Url::parse("file:///round2_engine.typort").unwrap();
    let b = backend(Engine::Reference);
    b.process_file(&uri, src, Some(1));
    messages(&b, &uri)
}

#[test]
fn ascription_hint_fires_and_keeps_original_parse_errors() {
    let msgs = run("def z = (left 9 : Either[Nat, Boolean])");
    assert!(
        msgs.iter().any(|m| m.contains(HINT)),
        "expected the ascription hint, got {msgs:?}"
    );
    // 窗口 16：同一处 `:` 只允许一条（此前实参位会重复输出）。
    assert_eq!(hint_count(&msgs), 1, "hint must be emitted once, got {msgs:?}");
    // The hint is added, not substituted: the original recovery errors survive.
    assert!(
        msgs.iter().any(|m| m.contains("expected `)`")),
        "expected the original `expected ')'` error to be retained, got {msgs:?}"
    );
    assert!(
        msgs.iter().any(|m| m.contains("expected newline")),
        "expected the original recovery error to be retained, got {msgs:?}"
    );
    assert!(
        errors(&msgs).len() >= 3,
        "hint must not replace the original errors, got {msgs:?}"
    );
}

/// 窗口 16（verifier task-19）：`(x: T) => e` 这种**注解 lambda binder**在 def 体
/// 与实参位都**不被支持**，文案不能只讲 type ascription，且每个位置只能出现一次。
#[test]
fn annotated_lambda_positions_get_one_two_meaning_hint() {
    for src in [
        "def z = ((y: Nat) => y)",
        "def h(g: Nat, f: Nat): Nat = f\ndef z2: Nat = h (1, ((y: Nat) => y))",
    ] {
        let msgs = run(src);
        assert_eq!(
            hint_count(&msgs),
            1,
            "annotated-lambda position must emit exactly one hint for {src:?}, got {msgs:?}"
        );
        let hint = msgs.iter().find(|m| m.contains(HINT)).unwrap();
        assert!(
            hint.contains("annotated lambda binder"),
            "the message must cover the binder meaning too, got {hint:?}"
        );
        assert!(
            hint.contains("type ascription"),
            "the message must still cover the ascription meaning, got {hint:?}"
        );
        assert!(
            msgs.iter().any(|m| m.contains("expected `)`")),
            "the original parse error must be retained for {src:?}, got {msgs:?}"
        );
    }
}

#[test]
fn ascription_hint_fires_on_a_simple_group_too() {
    let msgs = run("def z = (1 : Nat)");
    assert!(
        msgs.iter().any(|m| m.contains(HINT)),
        "expected the ascription hint on a plain group, got {msgs:?}"
    );
    assert_eq!(hint_count(&msgs), 1, "hint must be emitted once, got {msgs:?}");
    assert!(msgs.iter().any(|m| m.contains("expected `)`")), "got {msgs:?}");
}

#[test]
fn ascription_hint_absent_on_valid_code() {
    for src in [
        // The documented workaround / binder form.
        "def z: Either[Nat, Boolean] = left 9",
        "def z: Nat = 1",
        // Plain parenthesised expression and a tuple literal.
        "def z: Nat = (1)",
        "def p(a: Nat, b: Nat): Nat = a\n\n\ndef q: Nat = p (1, 2)",
        // `[msb:lsb]`-shaped colons inside brackets are not ascriptions.
        "def f(v: Vec[4]): Nat = 0",
        // 窗口 16 反例（verifier task-19 要求零命中）：
        // verilog 位选 `w[7:0]` / `w[7:4]`、声明冒号、`{a: b}`、方括号 binder。
        "def z = w[7:0]",
        "def z = w[7:4]",
        "def bar: Nat = 3",
        "def z = {a: b}",
        "def k[T: Type] (x: T): T = x",
    ] {
        let msgs = run(src);
        assert!(
            !msgs.iter().any(|m| m.contains(HINT)),
            "unexpected ascription hint for {src:?}: {msgs:?}"
        );
    }
}

/// Regression pin: the HDL example must stay free of ascription diagnostics
/// (the pre-fix lookahead misread `[7:0]` part-select colons).
#[test]
fn hdl_example_has_no_ascription_false_positive() {
    let src = std::fs::read_to_string("examples/hdl/24-verilog-practice.typort").unwrap();
    let uri = Url::parse("file:///round2_hdl24.typort").unwrap();
    let b = backend_hdl(Engine::Reference);
    b.process_file(&uri, &src, Some(1));
    let msgs = messages(&b, &uri);
    assert!(
        !msgs.iter().any(|m| m.contains(HINT)),
        "ascription false positive in the HDL corpus example: {msgs:?}"
    );
    assert!(
        !msgs.iter().any(|m| m.contains("expected `)`")),
        "unexpected parse error in a clean HDL example: {msgs:?}"
    );
    // The example's own (unrelated) HDL warning must still be published.
    assert!(
        msgs.iter().any(|m| m.contains("HDV002")),
        "the HDL warning disappeared: {msgs:?}"
    );
}

/// The reference and the twin must publish the same diagnostics for the HDL
/// example (same messages, same order) -- the ordering divergence the first
/// implementation caused is pinned here on one file, cheaply.
#[test]
fn hdl_example_diagnostics_agree_between_reference_and_twin() {
    let src = std::fs::read_to_string("examples/hdl/24-verilog-practice.typort").unwrap();
    let uri = Url::parse("file:///round2_hdl24_twin.typort").unwrap();

    let rb = backend_hdl(Engine::Reference);
    rb.process_file(&uri, &src, Some(1));
    let rt = backend_hdl(Engine::Twin);
    rt.process_file(&uri, &src, Some(1));
    assert_eq!(messages(&rb, &uri), messages(&rt, &uri));
}

#[test]
fn hint_severity_is_error() {
    let uri = Url::parse("file:///round2_sev.typort").unwrap();
    let b = backend(Engine::Reference);
    b.process_file(&uri, "def z = (1 : Nat)", Some(1));
    let d = b.client.diagnostics.lock().unwrap();
    let hint = d
        .iter()
        .filter(|(u, _, _)| u == &uri)
        .flat_map(|(_, ds, _)| ds.iter())
        .find(|d| d.message.contains(HINT))
        .cloned()
        .expect("hint diagnostic");
    assert_eq!(hint.severity, Some(DiagnosticSeverity::ERROR));
}
