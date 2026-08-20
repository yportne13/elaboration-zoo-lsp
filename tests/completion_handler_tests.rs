// End-to-end completion handler tests: drive the REAL `completion_at` handler
// body on a live `Backend` (prelude loaded + file processed) instead of
// re-implementing its filtering logic.  CompletionParams with a raw byte
// offset on single-line ASCII sources (position character == byte offset).

use std::sync::{Arc, Mutex};

use elaboration_zoo_lsp::client::ClientLike;
use elaboration_zoo_lsp::Backend;
use lsp_types::{
    CompletionItem, CompletionParams, CompletionResponse, Diagnostic, MessageType, Position,
    TextDocumentIdentifier, TextDocumentPositionParams, Url,
};

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

fn backend() -> Arc<Backend<CapturingClient>> {
    let b = Backend::new(CapturingClient::default());
    b.load_prelude_skip_hdl();
    b
}

fn process(b: &Arc<Backend<CapturingClient>>, uri: &Url, src: &str) {
    b.process_file(uri, src, Some(1));
}

/// Convert a byte offset into a client Position exactly the way the LSP would
/// (line = byte->char->line; character = char index within the line).  Test
/// sources are ASCII apart from the explicit UTF-16 test, so the char index
/// equals the UTF-16 unit count there; that test derives its own Position.
fn byte_position(src: &str, byte_offset: usize) -> Position {
    let rope = ropey::Rope::from_str(src);
    let char_i = rope.byte_to_char(byte_offset);
    let line = rope.char_to_line(char_i);
    let line_char_start = rope.line_to_char(line);
    Position::new(line as u32, (char_i - line_char_start) as u32)
}

fn completion_at(
    b: &Arc<Backend<CapturingClient>>,
    uri: &Url,
    src: &str,
    byte_offset: usize,
) -> Vec<CompletionItem> {
    let params = CompletionParams {
        text_document_position: TextDocumentPositionParams {
            text_document: TextDocumentIdentifier { uri: uri.clone() },
            position: byte_position(src, byte_offset),
        },
        work_done_progress_params: Default::default(),
        partial_result_params: Default::default(),
        context: None,
    };
    let mut items: Vec<CompletionItem> = Vec::new();
    match b.completion_at(params).expect("completion request failed") {
        Some(CompletionResponse::Array(completion_items)) => items = completion_items,
        Some(CompletionResponse::List(list)) => items = list.items,
        None => {}
    }
    items
}

/// The `text_edit` range of an item as (start_line, start_char, end_line, end_char),
/// or None when the item carries no text edit.
fn edit_range(item: &CompletionItem) -> Option<(u32, u32, u32, u32)> {
    let te = item.text_edit.as_ref()?;
    let range = match te {
        lsp_types::CompletionTextEdit::Edit(e) => &e.range,
        lsp_types::CompletionTextEdit::InsertAndReplace(i) => &i.insert,
    };
    Some((
        range.start.line,
        range.start.character,
        range.end.line,
        range.end.character,
    ))
}

fn labels(items: &[CompletionItem]) -> Vec<String> {
    items.iter().map(|i| i.label.clone()).collect()
}

#[test]
fn member_completion_empty_dot_state() {
    let b = backend();
    let uri = Url::parse("file:///pt.typort").unwrap();
    let src = "struct Point[T] {\n    x: T\n    y: T\n}\n\ndef p: Point[Nat] = new Point(1, 2)\ndef test = p.";
    process(&b, &uri, src);

    let dot_off = src.rfind('.').unwrap();
    let got = completion_at(&b, &uri, src, dot_off + 1);
    let mut names = labels(&got);
    names.sort();
    assert!(names.contains(&"x".to_string()), "expected x: {names:?}");
    assert!(names.contains(&"y".to_string()), "expected y: {names:?}");

    // Text edit must be a zero-width insertion AT the cursor (no prefix to replace).
    let cursor_pos = byte_position(src, dot_off + 1);
    for item in got.iter().filter(|i| i.label == "x") {
        let (sl, sc, el, ec) = edit_range(item).expect("x should carry a text edit");
        assert_eq!((sl, sc), (el, ec), "empty-dot edit range must be zero-width");
        assert_eq!(
            (sl, sc),
            (cursor_pos.line, cursor_pos.character),
            "insertion must sit at the cursor"
        );
    }
}

#[test]
fn member_completion_typed_prefix() {
    let b = backend();
    let uri = Url::parse("file:///pt2.typort").unwrap();
    let src = "struct Point[T] {\n    x: T\n    y: T\n}\n\ndef p: Point[Nat] = new Point(1, 2)\ndef test = p.x";
    process(&b, &uri, src);

    let cursor = src.len();
    let got = completion_at(&b, &uri, src, cursor);
    let mut names = labels(&got);
    names.sort();
    assert!(names.contains(&"x".to_string()), "expected x: {names:?}");
    assert!(names.contains(&"y".to_string()), "expected y: {names:?}");

    // The edit must replace exactly the typed `x` prefix, not the whole `p.x`.
    let x_off = src.rfind('x').unwrap();
    let x_pos = byte_position(src, x_off);
    let cursor_pos = byte_position(src, cursor);
    for item in got.iter().filter(|i| i.label == "y") {
        let (sl, sc, el, ec) = edit_range(item).expect("y should carry a text edit");
        assert_eq!((sl, sc), (x_pos.line, x_pos.character), "replacement must start at the prefix");
        assert_eq!((el, ec), (cursor_pos.line, cursor_pos.character), "replacement must end at the cursor");
    }
}

#[test]
fn member_completion_utf16_cursor() {
    // A 4-byte emoji (1 char, 2 UTF-16 units) before the receiver shifts the
    // naive char-index math; the handler's UTF-16-aware byte offset must still
    // hit the `p.` span and produce a valid insertion position.
    let b = backend();
    let uri = Url::parse("file:///u.typort").unwrap();
    let src = "// \u{1F600}\nstruct Point[T] {\n    x: T\n    y: T\n}\n\ndef p: Point[Nat] = new Point(1, 2)\ndef test = p.";
    process(&b, &uri, src);

    let dot_off = src.rfind('.').unwrap();
    // Line 7 is `def test = p.` — all ASCII.  The cursor right after the `.`
    // is the 14th character of that line in UTF-16 units, i.e. character 13.
    // Lines above carry the emoji so a byte-based cursor would land wrong.
    let position = Position::new(7, 13);
    let rope = b.document_map.get(uri.as_str()).unwrap();
    assert_eq!(
        elaboration_zoo_lsp::position_to_offset(position, &rope).unwrap(),
        dot_off + 1,
        "UTF-16 cursor must map to the byte right after the dot"
    );
    let params = CompletionParams {
        text_document_position: TextDocumentPositionParams {
            text_document: TextDocumentIdentifier { uri: uri.clone() },
            position,
        },
        work_done_progress_params: Default::default(),
        partial_result_params: Default::default(),
        context: None,
    };
    let got = match b.completion_at(params).expect("completion request failed") {
        Some(CompletionResponse::Array(items)) => items,
        Some(CompletionResponse::List(list)) => list.items,
        None => Vec::new(),
    };
    assert!(!got.is_empty(), "expected completions after `p.` across a UTF-16 line");
}

#[test]
fn import_context_completion() {
    let b = backend();
    // File A defines a package with first-level members.
    let lib_uri = Url::parse("file:///mylib.typort").unwrap();
    let lib_src = "package mylib\n\ntrait HasVal {\n    def getVal: Nat\n}\n\nstruct Foo {\n    bar: String\n}\n\ndef mkFoo: Foo = new Foo(\"x\")";
    process(&b, &lib_uri, lib_src);

    // File B is mid-edit: an incomplete `import mylib.` — analysis fails, but
    // import-context completion must still work from the global symbol table.
    let use_uri = Url::parse("file:///use.typort").unwrap();
    let use_src = "import mylib.";
    process(&b, &use_uri, use_src);

    let dot_off = use_src.rfind('.').unwrap();
    let got = completion_at(&b, &use_uri, use_src, dot_off + 1);
    let mut names = labels(&got);
    names.sort();
    assert!(names.contains(&"Foo".to_string()), "expected Foo: {names:?}");
    assert!(names.contains(&"HasVal".to_string()), "expected HasVal: {names:?}");
    // Only first-level members: `Foo.bar` and `Foo`'s constructor must NOT appear.
    for name in &names {
        assert!(!name.contains('.'), "must not offer nested members: {name}");
    }
}

#[test]
fn no_member_completion_without_dot() {
    let b = backend();
    let uri = Url::parse("file:///n.typort").unwrap();
    let src = "def t: Nat = 1 + 2";
    process(&b, &uri, src);

    let got = completion_at(&b, &uri, src, src.len());
    assert!(got.is_empty(), "no `.` access → no completions, got: {:?}", labels(&got));
}

#[test]
fn typed_prefix_after_dot_preserves_receiver() {
    // `p.x` where the cursor sits mid-prefix: everything before the receiver
    // must be untouched by the text edit.
    let b = backend();
    let uri = Url::parse("file:///pt3.typort").unwrap();
    let src = "struct Point[T] {\n    x: T\n    y: T\n}\n\ndef p: Point[Nat] = new Point(1, 2)\ndef f = p.xy";
    process(&b, &uri, src);

    // Cursor right after `x` in `p.xy` (partial prefix `x`): the edit must
    // replace back to the member-prefix start (the `.` -> first typed char).
    let x_off = src.rfind("p.xy").unwrap() + 2;
    let got = completion_at(&b, &uri, src, x_off + 1);
    let mut names = labels(&got);
    names.sort();
    assert!(names.contains(&"x".to_string()), "expected x: {names:?}");
    assert!(names.contains(&"y".to_string()), "expected y: {names:?}");

    let prefix_start = byte_position(src, x_off);
    for item in got.iter().filter(|i| i.label == "x") {
        let (sl, sc, _, _) = edit_range(item).expect("text edit expected");
        assert_eq!((sl, sc), (prefix_start.line, prefix_start.character), "replacement starts at the typed prefix");
    }
}

#[test]
fn diagnostics_severity_unaffected_by_completion() {
    // Completion requests must not mutate diagnostics or the document store.
    let b = backend();
    let uri = Url::parse("file:///sev.typort").unwrap();
    let src = "def t: Nat = p.";
    process(&b, &uri, src);
    let before = b.client.diagnostics.lock().unwrap().len();
    let _ = completion_at(&b, &uri, src, src.len());
    assert_eq!(b.client.diagnostics.lock().unwrap().len(), before);
}

// =========================================================================
// HDL module-body completion — the real editing flow: the user types
// `outer1.` INSIDE a module body and stops; the file is mid-edit
// (incomplete statement) while the completion request fires.
// =========================================================================

fn bundle_module_src(extra_body_line: &str) -> String {
    format!(
        "#[derive(Bundle)]\n\
         struct InnerBus {{\n    value: UInt[8]\n    strobe: Bool\n}}\n\n\
         module top {{\n    let outer1 = InnerBus.create\n    let outer2 = InnerBus.create\n    {extra_body_line}\n}}"
    )
}

#[test]
fn module_body_mid_edit_member_completion() {
    let b = Backend::new(CapturingClient::default());
    b.load_prelude();
    let uri = Url::parse("file:///m.typort").unwrap();
    // Mid-edit: the last module-body statement is a dangling `outer1.`.
    let src = bundle_module_src("outer1.");
    process(&b, &uri, &src);

    // The member access must not blow up the whole-file analysis.
    let dot_off = src.rfind("outer1.").unwrap() + "outer1".len();
    let got = completion_at(&b, &uri, &src, dot_off + 1);
    let mut names = labels(&got);
    names.sort();
    assert!(names.contains(&"value".to_string()), "expected bundle field `value`: {names:?}");
    assert!(names.contains(&"strobe".to_string()), "expected bundle field `strobe`: {names:?}");
}

#[test]
fn module_body_mid_edit_nested_bundle_completion() {
    let b = Backend::new(CapturingClient::default());
    b.load_prelude();
    let uri = Url::parse("file:///mn.typort").unwrap();
    let src = format!(
        "#[derive(Bundle)]\n\
         struct InnerBus {{\n    value: UInt[8]\n    strobe: Bool\n}}\n\n\
         #[derive(Bundle)]\n\
         struct OuterBus {{\n    inner: InnerBus\n    ready: Bool\n}}\n\n\
         module top {{\n    let outer = OuterBus.create\n    outer.inner.\n}}"
    );
    process(&b, &uri, &src);

    let dot_off = src.rfind("outer.inner.").unwrap() + "outer.inner".len();
    let got = completion_at(&b, &uri, &src, dot_off + 1);
    let mut names = labels(&got);
    names.sort();
    assert!(names.contains(&"value".to_string()), "expected inner bundle field `value`: {names:?}");
    assert!(names.contains(&"strobe".to_string()), "expected inner bundle field `strobe`: {names:?}");
}

// =========================================================================
// Nested-bundle completion isolation — the receiver-keyed span scheme.
// Completion entries are keyed to the RECEIVER's span (not the whole access),
// and the handler matches an entry only when that span ends exactly at the
// dot before the cursor, so a nested access's receiver can never leak into an
// enclosing trailing dot.
// =========================================================================

/// `outer.inner.` inside a module body must offer only InnerBus fields —
/// NOT the sibling `ready`/`inner` (OuterBus fields) and NOT operators (`+`)
/// that are inapplicable to a bundle.
#[test]
fn module_nested_completion_offers_no_sibling_or_operators() {
    let b = Backend::new(CapturingClient::default());
    b.load_prelude();
    let uri = Url::parse("file:///mns.typort").unwrap();
    let src = format!(
        "#[derive(Bundle)]\n\
         struct InnerBus {{\n    value: UInt[8]\n    strobe: Bool\n}}\n\n\
         #[derive(Bundle)]\n\
         struct OuterBus {{\n    inner: InnerBus\n    ready: Bool\n}}\n\n\
         module top {{\n    let outer = OuterBus.create\n    outer.inner.\n}}"
    );
    process(&b, &uri, &src);
    let dot_off = src.rfind("outer.inner.").unwrap() + "outer.inner".len();
    let got = completion_at(&b, &uri, &src, dot_off + 1);
    let mut names = labels(&got);
    names.sort();
    assert!(names.contains(&"value".to_string()), "expected `value`: {names:?}");
    assert!(!names.contains(&"ready".to_string()), "must not offer sibling `ready`: {names:?}");
    assert!(!names.contains(&"+".to_string()), "must not offer operator `+` on a bundle: {names:?}");
}

/// `o.inner.` OUTSIDE any module body (top-level `def probe = o.inner.`) must
/// also offer the nested InnerBus fields.
#[test]
fn top_level_nested_completion_offers_inner_fields() {
    let b = Backend::new(CapturingClient::default());
    b.load_prelude();
    let uri = Url::parse("file:///tln.typort").unwrap();
    let src = "#[derive(Bundle)]\nstruct InnerBus {\n    value: UInt[8]\n    strobe: Bool\n}\n\n#[derive(Bundle)]\nstruct OuterBus {\n    inner: InnerBus\n    ready: Bool\n}\n\ndef o: OuterBus = OuterBus.create\ndef probe = o.inner.";
    process(&b, &uri, &src);
    let dot_off = src.rfind("o.inner.").unwrap() + "o.inner".len();
    let got = completion_at(&b, &uri, &src, dot_off + 1);
    let mut names = labels(&got);
    names.sort();
    assert!(names.contains(&"value".to_string()), "expected `value`: {names:?}");
    assert!(names.contains(&"strobe".to_string()), "expected `strobe`: {names:?}");
}

#[test]
fn module_body_mid_edit_typed_prefix_completion() {
    let b = Backend::new(CapturingClient::default());
    b.load_prelude();
    let uri = Url::parse("file:///mt.typort").unwrap();
    let src = bundle_module_src("outer1.val");
    process(&b, &uri, &src);

    // Cursor at the end of the typed prefix `val`.  `val` must not collide with
    // a real field (only `value`/`strobe` exist) — completion still offered.
    let prefix_off = src.rfind("outer1.val").unwrap() + "outer1.val".len();
    let got = completion_at(&b, &uri, &src, prefix_off);
    let mut names = labels(&got);
    names.sort();
    assert!(names.contains(&"value".to_string()), "expected `value` completion: {names:?}");

    // The text edit must replace exactly the typed prefix.
    let val_start = src.rfind("outer1.v").unwrap() + "outer1.".len();
    let vs = byte_position(&src, val_start);
    let ce = byte_position(&src, prefix_off);
    for item in got.iter().filter(|i| i.label == "value") {
        let (sl, sc, el, ec) = edit_range(item).expect("value should carry a text edit");
        assert_eq!((sl, sc), (vs.line, vs.character), "edit must start at the typed prefix");
        assert_eq!((el, ec), (ce.line, ce.character), "edit must end at the cursor");
    }
}