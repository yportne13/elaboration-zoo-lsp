// End-to-end formatting handler tests: drive the REAL `format_document_at`
// handler body on a live `Backend`, mirroring `completion_handler_tests.rs`.

use std::sync::{Arc, Mutex};

use elaboration_zoo_lsp::client::ClientLike;
use elaboration_zoo_lsp::Backend;
use lsp_types::{Diagnostic, FormattingOptions, MessageType, Position, Range, Url};

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

fn opts() -> FormattingOptions {
    FormattingOptions {
        tab_size: 4,
        insert_spaces: true,
        ..Default::default()
    }
}

#[test]
fn handler_returns_single_whole_document_edit() {
    let b = backend();
    let uri = Url::parse("file:///format_test.typort").unwrap();
    let src = "def f(x: Nat): Nat = {\nmatch x {\ncase zero => zero\n}\n}\n";
    b.process_file(&uri, src, Some(1));

    let edits = b.format_document_at(&uri, &opts()).expect("handler declined to format");
    assert_eq!(edits.len(), 1, "expected one whole-document edit");
    assert_eq!(
        edits[0].new_text,
        "def f(x: Nat): Nat = {\n    match x {\n        case zero => zero\n    }\n}\n"
    );
    assert_eq!(edits[0].range.start, Position::new(0, 0));
    assert_eq!(edits[0].range.end, Position::new(5, 0));
}

#[test]
fn handler_returns_no_edits_for_already_formatted() {
    let b = backend();
    let uri = Url::parse("file:///format_clean.typort").unwrap();
    b.process_file(&uri, "def f = 1\n", Some(1));
    let edits = b.format_document_at(&uri, &opts()).expect("handler declined");
    assert!(edits.is_empty(), "already-formatted file must yield no edits");
}

#[test]
fn handler_preserves_comment_text() {
    let b = backend();
    let uri = Url::parse("file:///format_comment.typort").unwrap();
    let src = "// top\ndef f = {\n// inner\n1\n}\n";
    b.process_file(&uri, src, Some(1));
    let edits = b.format_document_at(&uri, &opts()).expect("handler declined");
    assert_eq!(edits.len(), 1);
    assert!(edits[0].new_text.contains("// top"));
    assert!(edits[0].new_text.contains("    // inner"));
}

#[test]
fn range_handler_formats_only_selected_lines() {
    let b = backend();
    let uri = Url::parse("file:///format_range.typort").unwrap();
    let src = "def a = 1\ndef b = {\nx\n}\ndef c = 2\n";
    b.process_file(&uri, src, Some(1));
    // Select the whole `def b` block; the range ends at line 4 column 0, so
    // line 3 (`}`) is included and line 4 is not.
    let range = Range::new(Position::new(1, 0), Position::new(4, 0));
    let edits = b.format_range_at(&uri, range, &opts()).expect("declined");
    assert_eq!(edits.len(), 1);
    assert_eq!(edits[0].new_text, "def b = {\n    x\n}\n");
    assert_eq!(edits[0].range.start, Position::new(1, 0));
    assert_eq!(edits[0].range.end, Position::new(4, 0));
}

#[test]
fn range_handler_no_edits_when_already_formatted() {
    let b = backend();
    let uri = Url::parse("file:///format_range_clean.typort").unwrap();
    b.process_file(&uri, "def a = 1\ndef b = 2\n", Some(1));
    let range = Range::new(Position::new(0, 0), Position::new(2, 0));
    let edits = b.format_range_at(&uri, range, &opts()).expect("declined");
    assert!(edits.is_empty());
}

#[test]
fn initialization_options_set_indent_width() {
    let b = backend();
    b.apply_initialization_options(Some(serde_json::json!({
        "format": { "indentWidth": 2 }
    })));
    let uri = Url::parse("file:///format_cfg.typort").unwrap();
    b.process_file(&uri, "def b = {\nx\n}\n", Some(1));
    let edits = b.format_document_at(&uri, &opts()).expect("declined");
    assert_eq!(edits.len(), 1);
    assert_eq!(edits[0].new_text, "def b = {\n  x\n}\n");
}

#[test]
fn handler_declines_comment_opener_inside_string() {
    let b = backend();
    let uri = Url::parse("file:///format_string.typort").unwrap();
    // `preprocess` is not string-aware, so the token stream is unreliable here;
    // the formatter must decline rather than risk corrupting the literal.
    b.process_file(&uri, "def a = \"http://x\"\n", Some(1));
    assert!(b.format_document_at(&uri, &opts()).is_none());
}
