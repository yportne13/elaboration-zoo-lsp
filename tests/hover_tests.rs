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

// ── Hover markup tests (rust-analyzer-style panels) ──────────────────────────

use lsp_types::HoverContents;

/// Full hover markup the LSP handler produces for `line`/`char`.
fn hover_markup_at(b: &Arc<Backend<CapturingClient>>, uri: &Url, line: u32, char: u32) -> String {
    let h = b.hover_at(uri, lsp_types::Position::new(line, char)).expect("no hover");
    match h.contents {
        HoverContents::Markup(m) => m.value,
        _ => panic!("expected markdown hover"),
    }
}

#[test]
fn hover_on_def_name_shows_signature_and_type_panels() {
    let client = CapturingClient::default();
    let b = Backend::new(client);
    let uri = Url::parse("file:///sig.typort").unwrap();
    let src = "def foo(a: Nat, b: Boolean): Boolean = b";
    elaborate(&b, &uri, src);

    let name_off = src.find("foo").unwrap() as u32;
    let value = hover_markup_at(&b, &uri, 0, name_off);
    // Definition panel first: `<name> : <type>` in a typort code fence …
    assert!(
        value.starts_with("```typort\nfoo : (a: Nat, b: Boolean) → Boolean\n```"),
        "missing definition panel, got:\n{value}"
    );
    // … then the hovered expression's own type panel.
    assert!(
        value.contains("\n\n```typort\n(a: Nat, b: Boolean) → Boolean\n```"),
        "missing type panel, got:\n{value}"
    );
}

#[test]
fn hover_on_def_use_shows_definition_panel_first() {
    let client = CapturingClient::default();
    let b = Backend::new(client);
    let uri = Url::parse("file:///use.typort").unwrap();
    let src = "def foo(a: Nat, b: Boolean): Boolean = b\ndef bar: Boolean = foo(1, true)";
    elaborate(&b, &uri, src);

    let line2 = src.find("def bar").unwrap();
    let use_off = src.rfind("foo").unwrap();
    let value = hover_markup_at(&b, &uri, 1, (use_off - line2) as u32);
    // The definition signature panel comes first, then the expression type.
    assert!(
        value.starts_with("```typort\nfoo : "),
        "definition panel must come first, got:\n{value}"
    );
    assert_eq!(
        value.matches("```typort").count(),
        2,
        "expected exactly two panels, got:\n{value}"
    );
}

#[test]
fn hover_on_local_variable_is_type_only() {
    let client = CapturingClient::default();
    let b = Backend::new(client);
    let uri = Url::parse("file:///loc.typort").unwrap();
    let src = "def foo(a: Nat, b: Boolean): Boolean = b";
    elaborate(&b, &uri, src);

    // The trailing `b` is a local reference: no global decl matches its
    // definition span, so the hover is a single fenced type block.
    let b_off = src.rfind("= b").unwrap() as u32 + 2;
    let value = hover_markup_at(&b, &uri, 0, b_off);
    assert_eq!(value, "```typort\nBoolean\n```");
}

// ── Doc-comment (`///`) rendering ────────────────────────────────────────────

#[test]
fn hover_on_def_with_doc_comment_shows_docs() {
    let client = CapturingClient::default();
    let b = Backend::new(client);
    let uri = Url::parse("file:///doc.typort").unwrap();
    let src = "/// Adds one to `a`.\n///\n/// Uses the prelude successor.\ndef inc(a: Nat): Nat = succ a";
    elaborate(&b, &uri, src);

    let line4 = src.find("def inc").unwrap();
    let name_off = src.find("inc").unwrap();
    let value = hover_markup_at(&b, &uri, 3, (name_off - line4) as u32);
    // Signature fence first …
    assert!(
        value.starts_with("```typort\ninc : (a: Nat) → Nat\n```"),
        "missing signature panel, got:\n{value}"
    );
    // … then the doc body (markers stripped, blank /// line becomes a
    // paragraph break), still before the type panel.
    assert!(
        value.contains(
            "\n\nAdds one to `a`.\n\nUses the prelude successor.\n\n```typort\n"
        ),
        "missing doc body between panels, got:\n{value}"
    );
}

#[test]
fn hover_on_use_site_shows_docs_too() {
    let client = CapturingClient::default();
    let b = Backend::new(client);
    let uri = Url::parse("file:///doc2.typort").unwrap();
    let src = "/// Doubles `a` via addition.\ndef dbl(a: Nat): Nat = a + a\ndef four: Nat = dbl 2";
    elaborate(&b, &uri, src);

    let line3 = src.find("def four").unwrap();
    let use_off = src.rfind("dbl").unwrap();
    let value = hover_markup_at(&b, &uri, 2, (use_off - line3) as u32);
    assert!(
        value.starts_with("```typort\ndbl : "),
        "definition panel must come first, got:\n{value}"
    );
    assert!(
        value.contains("\n\nDoubles `a` via addition."),
        "docs missing on use-site hover, got:\n{value}"
    );
}

#[test]
fn doc_scan_stops_at_blank_line() {
    let client = CapturingClient::default();
    let b = Backend::new(client);
    let uri = Url::parse("file:///doc3.typort").unwrap();
    // The `///` line is detached from the declaration by a blank line, so it
    // must NOT be picked up as its documentation.
    let src = "/// Some other note.\n\ndef dec(a: Nat): Nat = succ a";
    elaborate(&b, &uri, src);

    let line3 = src.find("def dec").unwrap();
    let name_off = src.find("dec").unwrap();
    let value = hover_markup_at(&b, &uri, 2, (name_off - line3) as u32);
    assert!(
        !value.contains("Some other note"),
        "detached doc must not render, got:\n{value}"
    );
}
