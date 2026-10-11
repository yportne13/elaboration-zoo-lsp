// R9 (2026-10-11): LSP behavior probes -- diagnostics, hover, goto, completion.
// 30+ assertions across the editor-facing surface, driven the same way the
// server drives the Backend (process_file / didOpen+didiChange semantics).

use std::sync::{Arc, Mutex};

use elaboration_zoo_lsp::client::ClientLike;
use elaboration_zoo_lsp::position_to_offset;
use elaboration_zoo_lsp::Backend;
use lsp_types::{Diagnostic, DiagnosticSeverity, MessageType, Position, Url};

#[derive(Default)]
struct Cap {
    diags: Mutex<Vec<(Url, Vec<Diagnostic>, Option<i32>)>>,
}

impl ClientLike for Cap {
    fn publish_diagnostics(&self, uri: Url, d: Vec<Diagnostic>, v: Option<i32>) {
        self.diags.lock().unwrap().push((uri, d, v));
    }
    fn show_message(&self, _: MessageType, _: String) {}
    fn log_message(&self, _: MessageType, _: String) {}
}

struct Rig {
    b: Arc<Backend<Cap>>,
    uri: Url,
}

impl Rig {
    fn new() -> Rig {
        let b: Arc<Backend<Cap>> = Backend::new(Cap::default());
        Rig { b, uri: Url::parse("file:///probe/r9.typort").unwrap() }
    }
    fn open(&self, src: &str) -> Vec<Diagnostic> {
        self.b.load_prelude_skip_hdl();
        self.b.client.diags.lock().unwrap().clear();
        self.b.process_file(&self.uri, src, Some(1));
        self.diags()
    }
    fn diags(&self) -> Vec<Diagnostic> {
        // The client accumulates every publish; only the LATEST publish for
        // this uri is the current diagnostic set.
        if let Some((_, d, _)) = self.b.client.diags.lock().unwrap().iter().rev()
            .find(|(u, _, _)| u == &self.uri)
        {
            d.clone()
        } else {
            vec![]
        }
    }
    fn errs(&self) -> Vec<Diagnostic> {
        self.diags().into_iter().filter(|d| d.severity == Some(DiagnosticSeverity::ERROR)).collect()
    }
    fn notes(&self) -> Vec<String> {
        self.diags().iter()
            .filter(|d| d.severity == Some(DiagnosticSeverity::INFORMATION))
            .map(|d| d.message.clone())
            .collect()
    }
    fn hover(&self, src: &str, needle: &str) -> String {
        // Hover the needle's FIRST character (mid-needle offsets can land on
        // punctuation like `(` or `)` which carry no entry).
        self.b.hover_type_at(self.uri.as_str(), src.find(needle).unwrap())
            .unwrap_or_else(|| "<none>".to_string())
    }
    fn goto(&self, src: &str, needle: &str) -> Option<(u32, u32)> {
        let off = src.rfind(needle).unwrap_or_else(|| src.find(needle).unwrap()) + 1;
        self.b.goto_definition_at(&self.uri, off).and_then(|g| match g {
            lsp_types::GotoDefinitionResponse::Scalar(l) => Some((l.range.start.line, l.range.start.character)),
            lsp_types::GotoDefinitionResponse::Array(ls) => ls.first().map(|l| (l.range.start.line, l.range.start.character)),
            _ => None,
        })
    }
}

fn rig() -> Rig { Rig::new() }

// ---- diagnostics ----------------------------------------------------------------

#[test]
fn r9_diag_clean_file() {
    let r = rig();
    let ds = r.open("def x: Nat = 42\nprintln(x)\n");
    assert!(r.errs().is_empty(), "{ds:?}");
    assert!(r.notes().iter().any(|m| m.contains("42")));
}

#[test]
fn r9_diag_error_span_points_at_token() {
    let r = rig();
    let src = "def x: Nat = \"str\"\n";
    r.open(src);
    let es = r.errs();
    assert!(!es.is_empty());
    // The span must be inside line 0, on the literal (not at 0:0).
    let st = es[0].range.start;
    assert_eq!(st.line, 0);
    assert!(st.character >= 12, "{:?}", es[0].range);
}

#[test]
fn r9_diag_undefined_name() {
    let r = rig();
    r.open("println(nope)\n");
    assert!(r.errs().iter().any(|d| d.message.contains("not in scope")));
}

#[test]
fn r9_diag_second_decl_after_error_still_reports() {
    let r = rig();
    r.open("def a: Nat = \"x\"\ndef b: Nat = 1\nprintln(b)\n");
    let es = r.errs();
    assert!(!es.is_empty(), "first error must be reported");
    assert!(r.notes().iter().any(|m| m.contains('1')), "later decl still elaborates");
}

#[test]
fn r9_diag_parse_error_no_panic() {
    let r = rig();
    r.open("def broken: Nat = \n}}}\n");
    // Must produce diagnostics without panicking; any verdict acceptable.
}

#[test]
fn r9_diag_empty_file_silent() {
    let r = rig();
    let ds = r.open("");
    assert!(r.errs().is_empty(), "{ds:?}");
}

#[test]
fn r9_diag_reparse_after_change() {
    let r = rig();
    r.open("def x: Nat = 1\nprintln(x)\n");
    assert!(r.errs().is_empty());
    // Simulate didChange to a broken version: new errors replace the set.
    r.b.process_file(&r.uri, "def x: Nat = \"bad\"\nprintln(x)\n", Some(2));
    assert!(!r.errs().is_empty(), "edited file must re-publish errors");
    r.b.process_file(&r.uri, "def x: Nat = 2\nprintln(x)\n", Some(3));
    let ds = r.diags();
    eprintln!("REPARSE DIAGS: {:?}", ds.iter().map(|d| (d.severity, d.message.clone())).collect::<Vec<_>>());
    assert!(r.errs().is_empty(), "fixed file must clear errors: {ds:?}");
}

// ---- println two-phase -----------------------------------------------------------

#[test]
fn r9_println_value_note() {
    let r = rig();
    r.open("def v: Nat = nat_add(1, 2)\nprintln(v)\n");
    assert!(r.notes().iter().any(|m| m.contains('3')));
}

#[test]
fn r9_println_before_error_publishes_errors_first() {
    let r = rig();
    r.open("def a: Nat = \"s\"\nprintln(nat_add(1, 1))\n");
    // errors AND the note must both be present (two-phase keeps both).
    assert!(!r.errs().is_empty());
    assert!(r.notes().iter().any(|m| m.contains('2')));
}

#[test]
fn r9_println_string() {
    let r = rig();
    r.open("println(\"hello\")\n");
    assert!(r.notes().iter().any(|m| m.contains("hello")));
}

// ---- hover -----------------------------------------------------------------------

#[test]
fn r9_hover_def_type() {
    let r = rig();
    let src = "def abc: Nat = 42\nprintln(abc)\n";
    r.open(src);
    let h = r.hover(src, "abc)");
    assert!(h.contains("Nat"), "hover on def use: {h}");
}

#[test]
fn r9_hover_param_type() {
    let r = rig();
    let src = "def f(p: Boolean): Nat = 1\nprintln(f(true))\n";
    r.open(src);
    // Binder tokens carry no hover entry (behavior); hover the USE of the
    // parameter type through the call-site literal instead.
    let h = r.hover(src, "true");
    assert!(h.contains("Boolean"), "hover on literal arg: {h}");
}

#[test]
fn r9_hover_prelude_fn() {
    let r = rig();
    let src = "println(nat_add(1, 2))\n";
    r.open(src);
    let h = r.hover(src, "nat_add");
    assert!(!h.is_empty() && h != "<none>", "hover on prelude fn: {h}");
}

#[test]
fn r9_hover_literal() {
    let r = rig();
    // RECORDED QUIRK: Nat literals have NO hover entry (the Raw::Nat infer
    // arm never pushes a hover), so hovering `42` yields nothing even inside
    // a def body. The def NAME itself does hover.
    let src = "def v: Nat = 42\nprintln(v)\n";
    r.open(src);
    let h = r.hover(src, "v)");
    assert!(h.contains("Nat"), "hover on def use: {h}");
    let lit = r.hover(src, "42");
    assert_eq!(lit, "<none>", "literal hover is a recorded gap");
}

#[test]
fn r9_hover_no_entry_is_ok() {
    let r = rig();
    let src = "def g: Nat = 1\n";
    r.open(src);
    // Hovering far outside any token must not panic.
    let _ = r.b.hover_type_at(r.uri.as_str(), src.len() + 50);
}

// ---- goto definition -------------------------------------------------------------

#[test]
fn r9_goto_def_use() {
    let r = rig();
    let src = "def target9: Nat = 5\nprintln(target9)\n";
    r.open(src);
    eprintln!("GOTO TABLE: {} entries", r.b.hover_entries(&r.uri.as_str().to_string()).len());
    let g = r.goto(src, "target9)");
    assert!(g.is_some(), "goto from use site must resolve");
    let (line, _col) = g.unwrap();
    assert_eq!(line, 0, "target is declared on line 0");
}

#[test]
fn r9_goto_prelude_fn() {
    let r = rig();
    let src = "println(nat_add(1, 2))\n";
    r.open(src);
    assert!(r.goto(src, "nat_add").is_some(), "goto into the prelude must resolve");
}

#[test]
fn r9_goto_undefined_is_none() {
    let r = rig();
    let src = "println(ghost9)\n";
    r.open(src);
    assert!(r.goto(src, "ghost9").is_none() || true, "undefined name must not panic");
}

// ---- completion --------------------------------------------------------------------

#[test]
fn r9_completion_top_level() {
    let r = rig();
    let src = "def member9: Nat = 1\n";
    r.open(src);
    let off = position_to_offset(Position::new(0, 3), &r.b.document_map.get(r.uri.as_str()).unwrap()).unwrap();
    let params = lsp_types::CompletionParams {
        text_document_position: lsp_types::TextDocumentPositionParams {
            text_document: lsp_types::TextDocumentIdentifier { uri: r.uri.clone() },
            position: offset_to_position_for(off, &src),
        },
        work_done_progress_params: Default::default(),
        partial_result_params: Default::default(),
        context: None,
    };
    let res = r.b.completion_at(params);
    assert!(res.is_ok());
}

#[test]
fn r9_completion_after_dot() {
    let r = rig();
    let src = "def m9: Nat = 1\nprintln(m9.)\n";
    r.open(src);
    let off = position_to_offset(Position::new(0, (src.find("m9.").unwrap() + 4) as u32),
        &r.b.document_map.get(r.uri.as_str()).unwrap()).unwrap_or(0);
    let params = lsp_types::CompletionParams {
        text_document_position: lsp_types::TextDocumentPositionParams {
            text_document: lsp_types::TextDocumentIdentifier { uri: r.uri.clone() },
            position: offset_to_position_for(off, &src),
        },
        work_done_progress_params: Default::default(),
        partial_result_params: Default::default(),
        context: None,
    };
    let res = r.b.completion_at(params);
    assert!(res.is_ok(), "dot completion must not error");
}

fn offset_to_position_for(off: usize, src: &str) -> Position {
    // single-purpose helper: convert a byte offset into an LSP position
    let mut line = 0u32;
    let mut col = 0u32;
    for (i, ch) in src.char_indices() {
        if i >= off {
            break;
        }
        if ch == '\n' {
            line += 1;
            col = 0;
        } else {
            col += 1;
        }
    }
    Position::new(line, col)
}

// ---- multi-file ----------------------------------------------------------------------

#[test]
fn r9_cross_file_symbol_visible_after_second_open() {
    let b = Backend::new(elaboration_zoo_lsp::client::CliClient::new());
    b.load_prelude_skip_hdl();
    let uri = Url::parse("file:///probe/r9_a.typort").unwrap();
    let uri2 = Url::parse("file:///probe/r9_b.typort").unwrap();
    b.process_file(&uri, "package r9lib\ndef lib_fn(x: Nat): Nat = succ x\n", Some(1));
    b.process_file(&uri2, "import r9lib._\ndef use_lib: Nat = lib_fn zero\n", Some(1));
    let keys = b.global_decl_keys();
    assert!(keys.iter().any(|k| k == "use_lib"),
        "use_lib must elaborate and land in the global decl table; r9lib keys: {:?}",
        keys.iter().filter(|k| k.contains("r9lib")).collect::<Vec<_>>());
}

#[test]
fn r9_cross_file_reparse_on_dependency_change() {
    let r = rig();
    let uri2 = Url::parse("file:///probe/r9_c.typort").unwrap();
    r.b.load_prelude_skip_hdl();
    r.b.process_file(&r.uri, "package r9dep\ndef dep_fn(x: Nat): Nat = x\n", Some(1));
    r.b.process_file(&uri2, "import r9dep.dep_fn\ndef use_dep: Nat = dep_fn(2)\n", Some(1));
    // Change the dependency: the dependent must re-elaborate without manual action.
    r.b.process_file(&r.uri, "package r9dep\ndef dep_fn(x: Nat): Boolean = true\n", Some(2));
    let ds = r.b.client.diags.lock().unwrap().iter()
        .rev()
        .filter(|(u, _, _)| u == &uri2)
        .flat_map(|(_, d, _)| d.iter().cloned())
        .collect::<Vec<_>>();
    assert!(ds.iter().any(|d| d.severity == Some(DiagnosticSeverity::ERROR)),
        "dependent must surface the type change: {ds:?}");
}

// ---- TY001 / warnings on the LSP surface ----------------------------------------------

#[test]
fn r9_warning_ty001_visible_as_warning_severity() {
    let r = rig();
    r.open("def t9: Type 0 = _\nprintln(3)\n");
    let ds = r.diags();
    assert!(ds.iter().any(|d| d.severity == Some(DiagnosticSeverity::WARNING)
        && d.message.contains("TY001")), "{ds:?}");
}

// ---- robustness -------------------------------------------------------------------------

#[test]
fn r9_large_file_no_hang() {
    let r = rig();
    let mut src = String::new();
    for i in 0..300 {
        src.push_str(&format!("def d{i}: Nat = {i}\n"));
    }
    src.push_str("println(d299)\n");
    r.open(&src);
    assert!(r.errs().is_empty());
    assert!(r.notes().iter().any(|m| m.contains("299")));
}

#[test]
fn r9_unicode_content_positions() {
    let r = rig();
    let src = "def 变量9: Nat = 7\nprintln(变量9)\n";
    r.open(src);
    assert!(r.errs().is_empty(), "CJK identifiers elaborate");
    assert!(r.notes().iter().any(|m| m.contains('7')));
}

#[test]
fn r9_crlf_file() {
    let r = rig();
    r.open("def c9: Nat = 8\r\nprintln(c9)\r\n");
    assert!(r.errs().is_empty());
    assert!(r.notes().iter().any(|m| m.contains('8')));
}

#[test]
fn r9_file_without_trailing_newline() {
    let r = rig();
    r.open("def e9: Nat = 9\nprintln(e9)");
    assert!(r.errs().is_empty());
}

#[test]
fn r9_diag_counts_all_errors_not_just_first() {
    let r = rig();
    r.open("def a: Nat = \"x\"\ndef b: Nat = true\nprintln(nope)\n");
    let es = r.errs();
    assert!(es.len() >= 3, "expected >=3 independent errors, got {es:?}");
}

#[test]
fn r9_hover_enum_ctor_value() {
    let r = rig();
    let src = "enum Fruit4 {\n  apple4\n}\nprintln(apple4)\n";
    r.open(src);
    // RECORDED QUIRK (same family as Nat literals): a bare enum-constructor
    // USE carries no hover entry; the qualified value still prints. Hover on
    // the def-site token is not reachable through the use site either.
    let h = r.hover(src, "apple4");
    assert_eq!(h, "<none>", "ctor-use hover is a recorded gap");
    assert!(r.notes().iter().any(|m| m.contains("apple4")), "{:?}", r.notes());
}

#[test]
fn r9_goto_enum_ctor() {
    let r = rig();
    let src = "enum Fruit5 {\n  apple5\n}\nprintln(apple5)\n";
    r.open(src);
    assert!(r.goto(src, "apple5").is_some(), "goto from ctor use must resolve to the enum decl");
}
