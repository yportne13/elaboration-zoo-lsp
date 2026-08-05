// Hover integration tests: drive the LSP `Backend` over a tuple-literal file
// and check that hovering an element of `(a, b)` resolves to the element's
// own hover entry (element type), not the whole-tuple `TupleN.mk` entry.

use std::sync::{Arc, Mutex};

use elaboration_zoo_lsp::client::ClientLike;
use elaboration_zoo_lsp::position_to_offset;
use elaboration_zoo_lsp::L13_namespace::pretty::pretty_tm;
use elaboration_zoo_lsp::Backend;
use lsp_types::{Diagnostic, MessageType, Url};

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

/// Type text of the hover entry that the LSP hover handler would pick for
/// `offset` (most specific span wins).
fn hover_type_at(b: &Arc<Backend<CapturingClient>>, uri: &Url, src: &str, offset: usize) -> String {
    let infer = b.hover_table.get(uri.as_str()).unwrap();
    let rope = b.document_map.get(uri.as_str()).unwrap();
    let id = b.document_id.get(uri.as_str()).unwrap();
    assert_eq!(offset, position_to_offset(
        lsp_types::Position::new(0, offset as u32),
        &rope,
    ).unwrap(), "single-line ASCII source: byte offset == character offset");
    let (_, _, hcxt, val) = infer
        .hover_entry_at(*id, offset)
        .unwrap_or_else(|| panic!("no hover entry at offset {offset} in:\n{src}"));
    pretty_tm(0, hcxt.names(), &infer.quote(&hcxt.decl, hcxt.lvl, val))
}

#[test]
fn hover_over_tuple_element_shows_element_type() {
    let client = CapturingClient::default();
    let b = Backend::new(client);
    let uri = Url::parse("file:///tup.typort").unwrap();
    let src = "def foo(a: Nat, b: Boolean): Tuple2[Nat, Boolean] = (a, b)";
    elaborate(&b, &uri, src);

    // `(a, b)` body tuple; elements `a` at base+1, `b` at base+4.
    let base = src.rfind("(a, b)").unwrap();
    assert_eq!(hover_type_at(&b, &uri, src, base + 1), "Nat");
    assert_eq!(hover_type_at(&b, &uri, src, base + 4), "Boolean");

    // Between the elements (the comma) only the whole-tuple entry matches.
    let infer = b.hover_table.get(uri.as_str()).unwrap();
    let rope = b.document_map.get(uri.as_str()).unwrap();
    let id = b.document_id.get(uri.as_str()).unwrap();
    let comma = position_to_offset(lsp_types::Position::new(0, (base + 2) as u32), &rope).unwrap();
    let (span, ..) = infer.hover_entry_at(*id, comma).unwrap();
    assert_eq!(
        (span.start_offset as usize, span.end_offset as usize),
        (base + 1, base + 5),
        "between elements, hover should resolve to the whole-tuple entry"
    );
}

#[test]
fn hover_over_literal_tuple_elements_shows_literal_types() {
    let client = CapturingClient::default();
    let b = Backend::new(client);
    let uri = Url::parse("file:///tup2.typort").unwrap();
    let src = "def bar: Tuple2[Nat, Nat] = (1, 2)";
    elaborate(&b, &uri, src);

    let base = src.rfind("(1, 2)").unwrap();
    assert_eq!(hover_type_at(&b, &uri, src, base + 1), "Nat");
    assert_eq!(hover_type_at(&b, &uri, src, base + 4), "Nat");
}

#[test]
fn hover_over_nested_tuple_element_is_most_specific() {
    let client = CapturingClient::default();
    let b = Backend::new(client);
    let uri = Url::parse("file:///tup3.typort").unwrap();
    let src = "def baz: Tuple2[Nat, Tuple2[Nat, Nat]] = (1, (2, 3))";
    elaborate(&b, &uri, src);

    // Hovering the inner tuple's elements shows their own type (most specific
    // span), not the inner tuple's type nor the outer tuple's.
    let base = src.rfind("(2, 3)").unwrap();
    assert_eq!(hover_type_at(&b, &uri, src, base + 1), "Nat");
    assert_eq!(hover_type_at(&b, &uri, src, base + 4), "Nat");
}
