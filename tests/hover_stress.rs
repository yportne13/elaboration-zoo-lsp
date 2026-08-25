// Hover robustness: hovering ANY identifier in representative files must
// never panic (a panic in a hover handler would crash the whole LSP server)
// and must never emit a pretty-printer "Variable index out of bounds"
// degradation.  Every identifier byte position is hovered under catch_unwind.

use std::sync::{Arc, Mutex};

use elaboration_zoo_lsp::client::ClientLike;
use elaboration_zoo_lsp::Backend;
use lsp_types::{Diagnostic, HoverContents, MessageType, Url};

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

fn elaborate(b: &Arc<Backend<CapturingClient>>, uri: &Url, src: &str) {
    b.load_prelude_skip_hdl();
    b.process_file(uri, src, Some(1));
    let diags: Vec<_> = b.client.diagnostics.lock().unwrap().iter()
        .filter(|(u, _, _)| u == uri)
        .flat_map(|(_, d, _)| d.iter())
        .filter(|d| d.severity == Some(lsp_types::DiagnosticSeverity::ERROR))
        .map(|d| d.message.clone())
        .collect();
    assert!(diags.is_empty(), "unexpected tyck errors for:\n{src}\n{diags:?}");
}

/// Hover every identifier (letter/digit/underscore run) in `src`; fail if any
/// hover panics or renders an out-of-bounds placeholder.
fn hover_every_identifier(b: &Arc<Backend<CapturingClient>>, uri: &Url, src: &str, label: &str) {
    let rope = b.document_map.get(uri.as_str()).unwrap();
    let bytes = src.as_bytes();
    let mut i = 0;
    let mut hovered = 0usize;
    while i < bytes.len() {
        if bytes[i].is_ascii_alphabetic() || bytes[i] == b'_' {
            let pos = elaboration_zoo_lsp::offset_to_position(i, &rope).unwrap();
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                b.hover_at(uri, pos)
            }));
            let h = result.unwrap_or_else(|_| {
                panic!("[{label}] hover PANICKED at byte {i} char `{}`", src[i..].chars().next().unwrap())
            });
            if let Some(h) = h {
                hovered += 1;
                if let HoverContents::Markup(m) = h.contents {
                    assert!(
                        !m.value.contains("Variable index out of bounds")
                            && !m.value.contains("<out of bounds>"),
                        "[{label}] hover @{i} rendered an out-of-bounds placeholder:\n{}",
                        m.value
                    );
                }
            }
            while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                i += 1;
            }
        } else {
            i += 1;
        }
    }
    assert!(hovered > 0, "[{label}] no identifiers hovered");
}

#[test]
fn hover_never_panics_and_never_degrades() {
    let client = CapturingClient::default();
    let b = Backend::new(client);

    // Recursive enum + struct, match patterns, `new` construction, field access.
    {
        let uri = Url::parse("file:///robust1.typort").unwrap();
        let src = "enum Tree {\n    leaf(value: Nat)\n    node(left: Tree, right: Tree)\n}\n\nstruct Point {\n    x: Nat\n    y: Nat\n}\n\ndef depth(t: Tree): Nat = match t {\n    case leaf(_) => 1\n    case node(l, r) => depth l + depth r\n}\n\ndef origin: Point = new Point(0, 0)\n\ndef dist(p: Point): Nat = p.x + p.y";
        elaborate(&b, &uri, src);
        hover_every_identifier(&b, &uri, src, "tree+point");
    }

    // Nested generics and prelude enum constructors.
    {
        let uri = Url::parse("file:///robust2.typort").unwrap();
        let src = "def f(x: Option[List[Result[String, Nat]]]): Nat = match x {\n    case None => 0\n    case Some(_) => 1\n}";
        elaborate(&b, &uri, src);
        hover_every_identifier(&b, &uri, src, "nested generic");
    }

    // Prelude type mix in signatures.
    {
        let uri = Url::parse("file:///robust3.typort").unwrap();
        let src = "def idb(b: Boolean): Boolean = b\ndef add(x: Nat, y: Nat): Nat = x + y\ndef concat(a: String, b: String): String = a + b";
        elaborate(&b, &uri, src);
        hover_every_identifier(&b, &uri, src, "prelude mix");
    }

    // GADT index params + namespaced enums/structs.
    {
        let uri = Url::parse("file:///robust4.typort").unwrap();
        let src = "def vlen[A](v: Vec[A] 3): Nat = 3\ndef r: Result[Nat, String] = ok 1\ndef o: Option[Nat] = None\ndef e: Eq[Nat] 3 3 = refl[Nat] 3";
        elaborate(&b, &uri, src);
        hover_every_identifier(&b, &uri, src, "gadts+enums");
    }
}
