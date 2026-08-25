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
fn hover_on_def_name_shows_signature_panel() {
    let client = CapturingClient::default();
    let b = Backend::new(client);
    let uri = Url::parse("file:///sig.typort").unwrap();
    let src = "def foo(a: Nat, b: Boolean): Boolean = b";
    elaborate(&b, &uri, src);

    let name_off = src.find("foo").unwrap() as u32;
    let value = hover_markup_at(&b, &uri, 0, name_off);
    // The definition panel carries the full signature; the definition already
    // contains the type, so no separate expression-type panel is appended
    // (rust-analyzer shows just the item signature).
    assert_eq!(
        value,
        "```typort\nfoo : (a: Nat, b: Boolean) → Boolean\n```",
        "missing definition panel, got:\n{value}"
    );
}

#[test]
fn hover_on_def_use_shows_definition_panel() {
    let client = CapturingClient::default();
    let b = Backend::new(client);
    let uri = Url::parse("file:///use.typort").unwrap();
    let src = "def foo(a: Nat, b: Boolean): Boolean = b\ndef bar: Boolean = foo(1, true)";
    elaborate(&b, &uri, src);

    let line2 = src.find("def bar").unwrap();
    let use_off = src.rfind("foo").unwrap();
    let value = hover_markup_at(&b, &uri, 1, (use_off - line2) as u32);
    // The definition signature panel comes first (and only — the resolved
    // declaration already carries the type).
    assert!(
        value.starts_with("```typort\nfoo : "),
        "definition panel must come first, got:\n{value}"
    );
    assert_eq!(
        value.matches("```typort").count(),
        1,
        "expected a single panel, got:\n{value}"
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
    // … then the doc body (markers stripped; each `///` line kept a visible
    // line via hard break, blank `///` line becomes a paragraph break).  The
    // resolved declaration already carries the type, so no separate type
    // panel is appended after the docs.
    assert!(
        value.contains("\n\nAdds one to `a`.  \n\nUses the prelude successor.  "),
        "missing doc body between panels, got:\n{value}"
    );
    assert_eq!(
        value.matches("```typort").count(),
        1,
        "signature + docs only, no redundant type panel, got:\n{value}"
    );
}

#[test]
fn hover_doc_downscales_headings() {
    let client = CapturingClient::default();
    let b = Backend::new(client);
    let uri = Url::parse("file:///doch.typort").unwrap();
    // `#` headings must not blow up to screen-filling size in the tiny hover
    // panel: they are downscaled to `####`. `#inline` (no space) is plain
    // text in CommonMark and must stay untouched.
    let src = "/// # 示例\n/// 计算 `n` 的后继。\n/// ## 参数\n/// #inline\ndef inc(a: Nat): Nat = succ a";
    elaborate(&b, &uri, src);

    let line = src.find("def inc").unwrap();
    let name_off = src[line..].find("inc").unwrap() + line;
    let value = hover_markup_at(&b, &uri, src[..line].matches('\n').count() as u32, (name_off - line) as u32);
    assert!(
        value.contains("\n\n#### 示例\n计算 `n` 的后继。  \n##### 参数\n#inline  "),
        "headings must be downscaled, got:\n{value}"
    );
}

#[test]
fn hover_doc_keeps_code_fence_and_balances_unclosed() {
    let client = CapturingClient::default();
    let b = Backend::new(client);
    let uri = Url::parse("file:///docf.typort").unwrap();
    // Fenced code inside a doc is preserved verbatim; a doc that opens a
    // fence but never closes it gets a closer appended so the rest of the
    // hover (incl. the type panel) is not swallowed into the code block.
    let src = "/// 示例：\n/// ```typort\n/// inc 0\n/// ```\n/// 后续说明。\ndef inc(a: Nat): Nat = succ a";
    elaborate(&b, &uri, src);

    let line = src.find("def inc").unwrap();
    let name_off = src[line..].find("inc").unwrap() + line;
    let value = hover_markup_at(&b, &uri, src[..line].matches('\n').count() as u32, (name_off - line) as u32);
    // The fence keeps its code verbatim (no hard-break spaces inside) and the
    // prose after it still closes properly before the end of the hover (no
    // trailing type panel, so the fence is the last block).
    assert!(
        value.contains("\n\n示例：  \n```typort\ninc 0\n```\n后续说明。  "),
        "fenced doc must survive intact, got:\n{value}"
    );

    // Unclosed fence: the missing closer is appended by render_doc_text, so
    // the doc block stays balanced even without a following type panel.
    let src2 = "/// 用法：\n/// ```typort\n/// inc 0\ndef inc(a: Nat): Nat = succ a";
    elaborate(&b, &uri, src2);
    let line2 = src2.find("def inc").unwrap();
    let name_off2 = src2[line2..].find("inc").unwrap() + line2;
    let value2 = hover_markup_at(&b, &uri, src2[..line2].matches('\n').count() as u32, (name_off2 - line2) as u32);
    assert_eq!(
        value2.matches("```typort").count(),
        2,
        "unclosed fence must be balanced (signature + doc fence), got:\n{value2}"
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
        value.contains("\n\nDoubles `a` via addition.  "),
        "docs missing on use-site hover, got:\n{value}"
    );
    assert_eq!(
        value.matches("```typort").count(),
        1,
        "use-site hover = definition + docs only, got:\n{value}"
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

// ── Sum-type member rendering (enum / struct / trait) ────────────────────────
// Hovering a type reference shows the full definition — constructors/fields/
// methods — rust-analyzer style, instead of a bare `Name : Type 0`.

#[test]
fn hover_on_enum_type_shows_members() {
    let client = CapturingClient::default();
    let b = Backend::new(client);
    let uri = Url::parse("file:///enum1.typort").unwrap();
    let src = "def use_nat(n: Nat): Nat = succ n";
    elaborate(&b, &uri, src);

    let line = src.find("def use_nat").unwrap();
    let nat_off = src.find("Nat").unwrap();
    let value = hover_markup_at(&b, &uri, 0, (nat_off - line) as u32);
    assert_eq!(
        value,
        "```typort\nenum Nat {\n    zero\n    succ(n: Nat)\n}\n```",
        "enum hover must show members, got:\n{value}"
    );
}

#[test]
fn hover_on_local_enum_def_and_use_shows_members() {
    let client = CapturingClient::default();
    let b = Backend::new(client);
    let uri = Url::parse("file:///enum2.typort").unwrap();
    let src = "/// 颜色。\nenum Color {\n    red\n    green(weight: Nat)\n}\n\ndef pick(c: Color): Nat = match c {\n    case red => 0\n    case green(w) => w\n}";
    elaborate(&b, &uri, src);

    // On the enum's own definition name: members + docs.
    let line0 = src.find("enum Color").unwrap();
    let name_off = src.find("Color").unwrap();
    let value = hover_markup_at(&b, &uri, 1, (name_off - line0) as u32);
    assert!(
        value.starts_with("```typort\nenum Color {\n    red\n    green(weight: Nat)\n}\n```"),
        "enum def hover must show members, got:\n{value}"
    );
    assert!(
        value.contains("\n\n颜色。  "),
        "docs must follow the member list, got:\n{value}"
    );

    // On the `Color` type annotation in `def pick`: same definition panel
    // (members + the definition's doc comment).
    let line6 = src.find("def pick").unwrap();
    let c_off = src.find("c: Color").unwrap() + 3;
    let value = hover_markup_at(&b, &uri, 6, (c_off - line6) as u32);
    assert!(
        value.starts_with("```typort\nenum Color {\n    red\n    green(weight: Nat)\n}\n```"),
        "annotation hover must show the enum definition, got:\n{value}"
    );
    assert!(
        value.contains("颜色。  "),
        "annotation hover must carry the definition docs, got:\n{value}"
    );
}

#[test]
fn hover_on_struct_shows_fields() {
    let client = CapturingClient::default();
    let b = Backend::new(client);
    let uri = Url::parse("file:///struct1.typort").unwrap();
    let src = "struct Point {\n    x: Nat\n    y: Nat\n}\n\ndef origin: Point = new Point(0, 0)";
    elaborate(&b, &uri, src);

    let line = src.find("struct Point").unwrap();
    let name_off = src.find("Point").unwrap();
    let value = hover_markup_at(&b, &uri, 0, (name_off - line) as u32);
    assert_eq!(
        value,
        "```typort\nstruct Point(x: Nat, y: Nat)\n```",
        "struct hover must show fields inline, got:\n{value}"
    );
}

#[test]
fn hover_on_parameterized_enum_shows_members() {
    let client = CapturingClient::default();
    let b = Backend::new(client);
    let uri = Url::parse("file:///enum3.typort").unwrap();
    let src = "def foo[T](xs: List[T]): Nat = xs.length";
    elaborate(&b, &uri, src);

    let line = src.find("def foo").unwrap();
    let l_off = src.find("List[T]").unwrap();
    let value = hover_markup_at(&b, &uri, 0, (l_off - line) as u32);
    assert!(
        value.starts_with("```typort\nenum List[T] {\n    lnil\n    lcons(head: T, tail: "),
        "parameterized enum hover must show members, got:\n{value}"
    );
}

#[test]
fn hover_on_gadt_enum_shows_members() {
    let client = CapturingClient::default();
    let b = Backend::new(client);
    let uri = Url::parse("file:///enum4.typort").unwrap();
    let src = "def vlen[A](v: Vec[A] 3): Nat = 3";
    elaborate(&b, &uri, src);

    let line = src.find("def vlen").unwrap();
    let v_off = src.find("Vec[A] 3").unwrap();
    let value = hover_markup_at(&b, &uri, 0, (v_off - line) as u32);
    assert!(
        value.contains("enum Vec[A](len: Nat) {"),
        "GADT header must keep explicit params, got:\n{value}"
    );
    assert!(
        value.contains("cons[l: Nat](x: A, xs: Vec [A] l)"),
        "GADT constructor params must render, got:\n{value}"
    );
}

#[test]
fn hover_on_trait_shows_methods() {
    let client = CapturingClient::default();
    let b = Backend::new(client);
    let uri = Url::parse("file:///trait1.typort").unwrap();
    let src = "trait MyShow {\n    def show: String\n}\n\ndef describe(s: MyShow): String = \"\"";
    elaborate(&b, &uri, src);

    let line = src.find("trait MyShow").unwrap();
    let name_off = src.find("MyShow").unwrap();
    let value = hover_markup_at(&b, &uri, 0, (name_off - line) as u32);
    assert_eq!(
        value,
        "```typort\ntrait MyShow {\n    show(this: Self) → String\n}\n```",
        "trait hover must show methods, got:\n{value}"
    );
}

#[test]
fn hover_on_namespaced_trait_shows_methods() {
    // A prelude trait's name span is shared by its synthesized `.mk`
    // constructor (even a bare `mk` alias).  The def-panel key selection must
    // prefer the trait's own (Sum-typed) key over the constructor key, or the
    // hover degrades to a raw `mk : […]` constructor type.
    let client = CapturingClient::default();
    let b = Backend::new(client);
    let uri = Url::parse("file:///trait2.typort").unwrap();
    let src = "def keep(x: Add[Nat, Nat]): Add[Nat, Nat] = x";
    elaborate(&b, &uri, src);

    let line = src.find("def keep").unwrap();
    let a_off = src.find("Add").unwrap();
    let value = hover_markup_at(&b, &uri, 0, (a_off - line) as u32);
    assert_eq!(
        value,
        "```typort\ntrait Add[T, O] {\n    +(this: Self, that: T) → O\n}\n```",
        "namespaced trait hover must show methods, not the `mk` constructor, got:\n{value}"
    );
}

#[test]
fn hover_on_gadt_index_params_render() {
    // `Eq[A](x: A, y: A)` — the stored index-param types were quoted inside
    // the full λ-chain, so they must be rendered against the complete param
    // context (a partial context used to emit `y: <out of bounds>`).
    let client = CapturingClient::default();
    let b = Backend::new(client);
    let uri = Url::parse("file:///gadt2.typort").unwrap();
    let src = "def e: Eq[Nat] 3 3 = refl[Nat] 3";
    elaborate(&b, &uri, src);

    let line = src.find("def e").unwrap();
    let e_off = src.find("Eq").unwrap();
    let value = hover_markup_at(&b, &uri, 0, (e_off - line) as u32);
    assert!(
        value.contains("enum Eq[A](x: A, y: A) {"),
        "GADT index params must reference the type param, got:\n{value}"
    );
    assert!(
        !value.contains("out of bounds"),
        "GADT header must not mis-resolve de Bruijn indices, got:\n{value}"
    );
    assert!(
        value.contains("refl(a: A)"),
        "GADT constructor must render, got:\n{value}"
    );
}

#[test]
fn hover_on_namespaced_struct_shows_fields() {
    // Tuple2 is a prelude struct with implicit type params; the header must
    // splice its fields and keep `[A, B]`.
    let client = CapturingClient::default();
    let b = Backend::new(client);
    let uri = Url::parse("file:///struct2.typort").unwrap();
    let src = "def swap[A, B](t: Tuple2[A, B]): Tuple2[B, A] = (t._2, t._1)";
    elaborate(&b, &uri, src);

    let line = src.find("def swap").unwrap();
    let t_off = src.find("Tuple2").unwrap();
    let value = hover_markup_at(&b, &uri, 0, (t_off - line) as u32);
    assert_eq!(
        value,
        "```typort\nstruct Tuple2[A, B](_1: A, _2: B)\n```",
        "namespaced struct hover must show fields, got:\n{value}"
    );
}
