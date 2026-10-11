// R5 regression pins (2026-10-11 review round 5): typeclass fixes.
// 1. #[derive(Show)] on a single-case enum with ctor args used the struct
//    `this.field` projection path (fields are positional on enum values) and
//    failed with "`this`: Snack has no object `n`". It now takes the
//    match-binding path; structs keep the projection path.
// 2. An impl declaring a supertrait method before its own swapped the
//    instance-record slots positionally: `d.sm` ran the supertrait's `bm`
//    body. Records are now applied in the trait's field order (own methods
//    first, inherited after) in both engines.

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
    let uri = Url::parse("file:///probe/r5_pin.typort").unwrap();
    b.on_change::<false>(TextDocumentItem { uri: uri.clone(), text, version: None });
    b.client.diags.lock().unwrap().iter()
        .filter(|(u, _, _)| u == &uri)
        .flat_map(|(_, d, _)| d.iter().cloned())
        .collect()
}

fn errs(ds: &[lsp_types::Diagnostic]) -> Vec<&lsp_types::Diagnostic> {
    ds.iter().filter(|d| d.severity == Some(lsp_types::DiagnosticSeverity::ERROR)).collect()
}

fn notes(ds: &[lsp_types::Diagnostic]) -> Vec<&str> {
    ds.iter()
        .filter(|d| d.severity == Some(lsp_types::DiagnosticSeverity::INFORMATION))
        .map(|d| d.message.as_str())
        .collect()
}

#[test]
fn derive_show_single_case_enum_with_args() {
    let src = "#[derive(Show)]\nenum Snack {\n  bar(n: Nat)\n}\nprintln(bar(3).show)\n";
    for engine in [Engine::Reference, Engine::Twin] {
        let ds = run(engine, src);
        assert!(errs(&ds).is_empty(), "{engine:?}: {ds:?}");
        assert!(
            notes(&ds).iter().any(|m| m.contains("bar(3)")),
            "{engine:?}: expected the bar(3) note, got {ds:?}"
        );
    }
}

#[test]
fn derive_show_struct_uses_field_projection() {
    // The struct case must keep working (its single case is `X.mk`, fields
    // project via this.f).
    let src = "#[derive(Show)]\nstruct Pts {\n  x: Nat\n  y: Nat\n}\ndef p: Pts = Pts.mk(1, 2)\nprintln(p.show)\n";
    for engine in [Engine::Reference, Engine::Twin] {
        let ds = run(engine, src);
        assert!(errs(&ds).is_empty(), "{engine:?}: {ds:?}");
        assert!(
            notes(&ds).iter().any(|m| m.contains("Pts(1, 2)")),
            "{engine:?}: expected the Pts(1, 2) note, got {ds:?}"
        );
    }
}

#[test]
fn supertrait_record_slot_order() {
    // impl declares the supertrait method FIRST; projection must still bind
    // by name (d.sm -> 2, not the supertrait's bm body 1).
    let src = "trait B9 {\n  def bm: Nat\n}\ntrait S9: B9 {\n  def sm: Nat\n}\nimpl S9 for Nat {\n  def bm: Nat = 1\n  def sm: Nat = 2\n}\ndef useS[T][d: S9[T]](t: T): Nat = d.sm t\nprintln(useS(0))\n";
    for engine in [Engine::Reference, Engine::Twin] {
        let ds = run(engine, src);
        assert!(errs(&ds).is_empty(), "{engine:?}: {ds:?}");
        assert!(
            notes(&ds).iter().any(|m| m.trim() == "2"),
            "{engine:?}: expected note 2 (sm's body), got {ds:?}"
        );
    }
}
