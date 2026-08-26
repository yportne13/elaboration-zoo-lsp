// Trait-instance Nat-parameter tests: an impl's Nat type parameter used as a
// runtime value inside the method body must arrive as the value unified at
// the call site, not as a frozen unsolved meta (the typeclass instance Nat
// param bug — docs/l13-typeclass-instance-nat-param-bug.md).
//
// The re-eval fix in solve_trait Phase 2 (unification.rs) made the method
// closures capture the SOLVED instance parameters: `fixed=8` below was a
// hard elaboration error ("solve trait failed") before it.

use std::sync::{Arc, Mutex};

use elaboration_zoo_lsp::client::ClientLike;
use elaboration_zoo_lsp::Backend;
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

fn println_notes(src: &str) -> (Vec<String>, Vec<String>) {
    let client = CapturingClient::default();
    let b = Backend::new(client);
    b.load_prelude();
    let uri = Url::parse("file:///trait_nat.typort").unwrap();
    b.process_file(&uri, src, Some(1));
    let mut notes = Vec::new();
    let mut errors = Vec::new();
    for (_, diags, _) in b.client.diagnostics.lock().unwrap().iter() {
        for d in diags {
            match d.severity {
                Some(DiagnosticSeverity::INFORMATION) => notes.push(d.message.clone()),
                Some(DiagnosticSeverity::ERROR) | None => errors.push(d.message.clone()),
                _ => {}
            }
        }
    }
    (notes, errors)
}

const SRC: &str = "\
trait WProbe[T] {
    def wOf: Nat
}
impl[w: Nat] WProbe[UInt[w]] for UInt[w] {
    def wOf: Nat = w
}
def probeW[T][p: WProbe[T]](v: T): Nat = p.wOf(v)

def topFixed: Nat =
    let v: UInt[8] = UInt.mk(None, literal(0));
    probeW(v)

println(natToDec(topFixed))
";

// Ground width: the instance's w flows to the method body at runtime (the
// re-eval fix; was "solve trait failed: WProbe[...]" before).
#[test]
fn ground_instance_nat_param_reaches_runtime() {
    let (notes, errors) = println_notes(SRC);
    assert!(
        errors.is_empty(),
        "expected clean elaboration, got errors:\n{}",
        errors.join("\n")
    );
    assert!(
        notes.iter().any(|n| n.trim() == "8"),
        "println should emit the instance width 8, got notes: {:?}",
        notes
    );
}
