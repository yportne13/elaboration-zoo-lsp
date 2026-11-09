// P0 known-bug pins (2026-11-09): **trait redefinition must not panic**.
//
// Background (P0 engine parity report, docs/optimal-design/P0-parity-report.md):
// `tests/trait_system_tests.typort` re-declares the prelude trait `Add` and then
// uses `+`.  Both engines used to panic with an index-out-of-bounds:
//   * reference: src/L13_namespace/unification.rs (head_index bucket holds stale
//     indices after `Synth::new_trait` reset `class_instances[name]`);
//   * twin: src/L13_namespace/bump_spine_iter/typeclass.rs (same stale-index
//     shape over the twin's instance table).
// Fix: when any indexed slot is >= instances.len(), fall back to the full
// instance scan (same candidate set as the no-index path).
//
// These pins exercise the minimal 9-line repro and the original fixture through
// the real `Backend` surface for BOTH engines; a panic fails the test.

use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::{Arc, Mutex};

use elaboration_zoo_lsp::client::ClientLike;
use elaboration_zoo_lsp::{Backend, Engine};
use lsp_types::{MessageType, Url};

#[derive(Default)]
struct Cap {
    diags: Mutex<Vec<(Url, Vec<lsp_types::Diagnostic>)>>,
}

impl ClientLike for Cap {
    fn publish_diagnostics(&self, uri: Url, d: Vec<lsp_types::Diagnostic>, _v: Option<i32>) {
        self.diags.lock().unwrap().push((uri, d));
    }
    fn show_message(&self, _: MessageType, _: String) {}
    fn log_message(&self, _: MessageType, _: String) {}
}

/// Minimal repro extracted during P0: re-declaring the prelude `Add` trait
/// (and one instance) is enough to leave a stale index in the head bucket.
const MINIMAL_REPRO: &str = "\
trait Add[T, O: outParam(Type 0)] {
    def +(that: T): O
}
impl Add[Nat, Nat] for Nat {
    def +(that: Nat): Nat = that
}
def two = succ (succ zero)
def three = succ two
def five = two + three
";

/// Original P0 fixture (re-declares Add/Sub/Not and defines several instances).
const FIXTURE: &str = include_str!("trait_system_tests.typort");

fn run_case(engine: Engine, name: &str, src: &str) {
    let b = Backend::new_with_engine(Cap::default(), engine);
    b.load_prelude_skip_hdl();
    let uri = Url::parse(&format!("file:///p0_pin/{name}.typort")).unwrap();
    let res = catch_unwind(AssertUnwindSafe(|| b.process_file(&uri, src, Some(1))));
    assert!(
        res.is_ok(),
        "P0 regression: {name} panicked on {engine:?} — stale trait head_index \
         (see tests/p0_known_bug_pins.rs / docs/optimal-design/P0-parity-report.md)"
    );
    // Either the twin owned the file or it declined with a recorded reason; a
    // silent crash would have been caught above, but this also ensures the run
    // actually reached the engine.
    if engine == Engine::Twin {
        let owned = b.twin_tables.contains_key(uri.as_str());
        let declined = b.twin_fallback_reason(uri.as_str()).is_some();
        assert!(owned || declined, "twin neither owned nor declined {name}");
    }
}

#[test]
fn p0_trait_redefinition_reference_does_not_panic() {
    run_case(Engine::Reference, "minimal", MINIMAL_REPRO);
    run_case(Engine::Reference, "fixture", FIXTURE);
}

#[test]
fn p0_trait_redefinition_twin_does_not_panic() {
    run_case(Engine::Twin, "minimal", MINIMAL_REPRO);
    run_case(Engine::Twin, "fixture", FIXTURE);
}
