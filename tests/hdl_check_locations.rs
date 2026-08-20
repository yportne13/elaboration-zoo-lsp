// HDL self-check diagnostic LOCATION integration tests.
//
// hdl-check.typort reports issues at NAME level ("code|module|signal|message")
// with no source location; lib.rs re-derives a precise span by scanning the
// module body (docs/hdl-selfcheck-design.md §5 documents the original
// "warnings pinned to the module name" behavior that these tests pin the
// replacement for). This test drives the real LSP path (Backend::process_file
// -> elaborate) and asserts each warning squiggles the offending signal, not
// the `module Name` line.

use std::sync::{Arc, Mutex};

use elaboration_zoo_lsp::client::ClientLike;
use elaboration_zoo_lsp::{position_to_offset, Backend, TextDocumentItem};
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

const SRC: &str = r#"module badDrive[w: Nat]
    input a = UInt[w]
    input b = UInt[w]
    output y = UInt[w]
{
    y := a
    y := b
}
module dangling[w: Nat]
    input a = UInt[w]
    output y = UInt[w]
{
    let ghost = UInt[w]
    let dead = UInt[w]
    y := ghost
}
module noDrive[w: Nat]
    output z = UInt[w]
{
    let a = UInt[w]
    a := 1
}
module srcMod[w: Nat]
    output o = UInt[w]
{
    o := 1
}
module badConn
    input x = UInt[8]
{
    let u = srcMod.create[8]
    u.o := x
}
module unconn
    input x = UInt[8]
{
    let u = srcMod.create[8]
}
"#;

/// Slice of the source that a diagnostic's range covers.
fn range_slice(src: &str, d: &Diagnostic) -> String {
    let rope = ropey::Rope::from_str(src);
    let start = position_to_offset(d.range.start, &rope).unwrap();
    let end = position_to_offset(d.range.end, &rope).unwrap();
    src.get(start..end).unwrap().to_string()
}

fn hdl_warnings(b: &Arc<Backend<CapturingClient>>, uri: &Url) -> Vec<(String, String)> {
    b.client.diagnostics.lock().unwrap().iter()
        .filter(|(u, _, _)| u == uri)
        .flat_map(|(_, ds, _)| ds.iter())
        .filter(|d| d.severity == Some(DiagnosticSeverity::WARNING))
        .filter(|d| d.message.contains("[hdl][warning]"))
        .map(|d| (d.message.clone(), range_slice(SRC, d)))
        .collect()
}

#[test]
fn hdl_check_warnings_point_at_offending_signal() {
    let client = CapturingClient::default();
    let b = Backend::new(client);
    b.load_prelude();
    let uri = Url::parse("file:///hdl_check_locs.typort").unwrap();
    b.process_file(&uri, SRC, Some(1));

    let warnings = hdl_warnings(&b, &uri);
    // Each expected (message substring, exact source slice the squiggle covers).
    let expect: &[(&str, &str)] = &[
        // multiple unconditional assignments -> first driver site
        ("HDL010 [badDrive] y", "y"),
        // input port never read -> the port declaration in the header
        ("HDL002 [dangling] a", "a"),
        // dangling read -> the read site, not the module name
        ("HDL001 [dangling] ghost", "ghost"),
        // dead signal -> its declaration
        ("HDL002 [dangling] dead", "dead"),
        // undriven output -> the port declaration
        ("HDL003 [noDrive] z", "z"),
        ("HDL002 [noDrive] a", "a"),
        // parent drives child output -> the connection occurrence
        ("HDL020 [badConn] u.o", "u.o"),
        // unconnected child port -> the instance declaration, not the module name
        ("HDL022 [unconn] u.o", "u"),
        // the unconn module's own unused input also fires (points at its decl)
        ("HDL002 [unconn] x", "x"),
    ];

    assert_eq!(warnings.len(), expect.len(), "warning count mismatch: {warnings:?}");
    for (msg_sub, want_slice) in expect {
        let found = warnings.iter().find(|(m, _)| m.contains(msg_sub))
            .unwrap_or_else(|| panic!("warning {msg_sub:?} not found in {warnings:?}"));
        assert_eq!(&found.1, want_slice,
            "warning {msg_sub:?} should point at `{want_slice}` but pointed at `{}` (full: {})",
            found.1, found.0);
        // The squiggle must NOT be the module name token.
        assert!(!found.0.contains("badDrive") || found.1 != "badDrive",
            "HDL010 must not point at module name");
    }
}

/// Same file through the CLI fast path (on_change), which previously dropped
/// HDL self-check warnings entirely.
#[test]
fn hdl_check_warnings_visible_via_on_change() {
    let client = CapturingClient::default();
    let b = Backend::new(client);
    b.load_prelude();
    let uri = Url::parse("file:///hdl_check_locs_cli.typort").unwrap();
    b.on_change::<false>(TextDocumentItem {
        uri: uri.clone(),
        text: SRC,
        version: None,
    });

    let warnings = hdl_warnings(&b, &uri);
    assert_eq!(warnings.len(), 9, "on_change must surface HDL warnings: {warnings:?}");
    assert!(warnings.iter().any(|(m, s)| m.contains("HDL010 [badDrive] y") && s == "y"));
    assert!(warnings.iter().any(|(m, s)| m.contains("HDL001 [dangling] ghost") && s == "ghost"));
    assert!(warnings.iter().any(|(m, s)| m.contains("HDL020 [badConn] u.o") && s == "u.o"));
}
