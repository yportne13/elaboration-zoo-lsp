// HDL042 on BOTH engines — review-1 F1 pin (Lead probe 2026-09-29).
//
// WHY AN INTEGRATION TEST: the HDL checker tests in
// `src/L13_namespace/hdl_check_graph_tests.rs` run the reference engine only
// (`run_with_prelude`), which is exactly how the F1 false positive slipped past
// that suite — the LSP default engine is the twin (`Engine::lsp_default`), and
// the twin drives the module checker's rounds differently.  It also MUST stay
// here rather than in `src/L13_namespace/**`: those test files are re-compiled
// into other targets through `#[path = "../src/L13_namespace/mod.rs"]`
// (`tests/l13_fast_parity.rs`, `src/bin/l13bench.rs`, ...), where `crate` is
// that target's root and `crate::Backend` / `crate::Engine` / `crate::client`
// do not exist (`cargo check --all-targets` / `tools/gate_l13.sh` go red).
// An integration test links the real lib and uses only its public surface.
//
// F1: a PORT-LESS module with a `for` loop warned HDL042 twice on the twin
// while the reference stayed silent (errs and emitted Verilog were identical).
// Root cause: HDL042's signature counted every declaration, and a loop body's
// `let x` declaration materializes as `x` in one round and as x_0..x_n in
// another, while its width can be ground in one round and stuck in the next
// (`declKeysOf` skips non-ground widths), so the key set drifted between the
// checker's rounds.  The signature is now PORT declarations only
// (`isPortKind` in hdl-check-graph.typort), which are stable across rounds
// (the ground gate only lets a round through when its port widths are ground).

use std::sync::{Arc, Mutex};

use elaboration_zoo_lsp::client::ClientLike;
use elaboration_zoo_lsp::{Backend, Engine};
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

/// Every WARNING diagnostic one engine publishes for `src` on the real LSP
/// path (`Backend` + full HDL prelude + `process_file`).
fn engine_warnings(engine: Engine, src: &str, tag: &str) -> Vec<String> {
    let backend: Arc<Backend<CapturingClient>> =
        Backend::new_with_engine(CapturingClient::default(), engine);
    backend.load_prelude();
    let uri = Url::parse(&format!("file:///{tag}.typort")).unwrap();
    backend.process_file(&uri, src, Some(1));
    backend
        .client
        .diagnostics
        .lock()
        .unwrap()
        .iter()
        .flat_map(|(_, ds, _)| ds.iter())
        .filter(|d| d.severity == Some(DiagnosticSeverity::WARNING))
        .map(|d| d.message.clone())
        .collect()
}

/// F1 regression pin: one registration, never re-parameterized — no HDL042 on
/// either engine.  Before the port-only signature this failed on the twin with
/// two HDL042 lines while the reference reported none.
#[test]
fn hdl042_portless_for_loop_silent_on_both_engines() {
    let src = r#"
module forDemo {
    let a = UInt[8]
    for i in 0 until 4 {
        let x = UInt[8]
        x := a
    }
}
println(moduleTreeVL(forDemo.create.tree))
"#;
    for engine in [Engine::Reference, Engine::Twin] {
        let warns = engine_warnings(engine, src, "hdl042_for_loop");
        assert!(
            !warns.iter().any(|w| w.contains("HDL042")),
            "one registration, no collision: HDL042 must not fire on {engine:?}, got: {warns:?}"
        );
    }
}

/// The patch must not silently disable the rule: the real collision (two
/// parameterizations of one name, port widths baked differently) still warns on
/// both engines — this is the `twin` counterpart of the reference-only
/// `hdl042_second_parameterization_warns` in hdl_check_graph_tests.rs.
#[test]
fn hdl042_second_parameterization_fires_on_both_engines() {
    let src = r#"
module myAdder[w: Nat]
    input a = UInt[w]
    input b = UInt[w]
    output sum = UInt[w]
    input en = Bool
{
    sum := en.mux(a + b, a)
}
module top8 {
    input a = UInt[8]
    input b = UInt[8]
    input en = Bool
    output sum = UInt[8]
    let u = myAdder.create[8]
    u.a := a
    u.b := b
    u.en := en
    sum := u.sum
}
module top16 {
    input a = UInt[16]
    input b = UInt[16]
    input en = Bool
    output sum = UInt[16]
    let u = myAdder.create[16]
    u.a := a
    u.b := b
    u.en := en
    sum := u.sum
}
println(moduleTreeVL(top8.create.tree))
println(moduleTreeVL(top16.create.tree))
"#;
    for engine in [Engine::Reference, Engine::Twin] {
        let warns = engine_warnings(engine, src, "hdl042_param_collision");
        assert!(
            warns.iter().any(|w| w.contains("HDL042")),
            "myAdder[16] after myAdder[8] must still warn HDL042 on {engine:?}, got: {warns:?}"
        );
    }
}
