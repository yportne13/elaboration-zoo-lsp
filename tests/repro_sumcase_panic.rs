// Regression: `SumCase expected Tm::Sum, but got Decl("Nat")` pretty panic.
//
// An UNANNOTATED module/class field (`let x = a + a`) used to get its
// inferred type recovered via `quote → tm_to_raw_type → Raw::SumCase chain →
// re-elaboration`, and the `Raw::SumCase` arm stored `typ` in the reference
// form (`Tm::Decl("Nat")`).  Hovering the module rendered the member list
// (`render_pi_member` → `pretty_tm`) and panicked on the non-Sum typ,
// crashing the LSP hover handler.  See docs/l13-sumcase-decl-typ-pretty-panic.md.
//
// Covered fixes:
//   - `tm_to_raw_type` recovers a concrete Nat width as `Raw::Nat(k)`;
//   - the `Raw::SumCase` elaboration arm stores the expanded (quoted) typ;
//   - pretty never panics on a SumCase typ (Nat-literal path accepts the
//     `Tm::Decl("Nat")` reference form; other non-Sum typs degrade).
use std::sync::{Arc, Mutex};

use elaboration_zoo_lsp::client::ClientLike;
use elaboration_zoo_lsp::Backend;
use lsp_types::{HoverContents, MessageType, Url};

#[derive(Default)]
struct CapturingClient {
    diagnostics: Mutex<Vec<(Url, Vec<lsp_types::Diagnostic>, Option<i32>)>>,
}
impl ClientLike for CapturingClient {
    fn publish_diagnostics(&self, uri: Url, diagnostics: Vec<lsp_types::Diagnostic>, version: Option<i32>) {
        self.diagnostics.lock().unwrap().push((uri, diagnostics, version));
    }
    fn show_message(&self, _typ: MessageType, _message: String) {}
    fn log_message(&self, _typ: MessageType, _message: String) {}
}

const SRC: &str = "\
module m {
    input a = UInt[8]
    let x = a + a
}
";

fn hover_text(b: &Arc<Backend<CapturingClient>>, uri: &Url, src: &str, offset: usize) -> String {
    let rope = b.document_map.get(uri.as_str()).unwrap();
    let pos = elaboration_zoo_lsp::offset_to_position(offset, &rope).unwrap();
    match b.hover_at(uri, pos) {
        Some(h) => match h.contents {
            HoverContents::Markup(m) => m.value,
            _ => String::new(),
        },
        // A miss is fine for the cursor-position probes below; the module
        // name hover itself must resolve (asserted by the caller).
        None => String::new(),
    }
}

#[test]
fn hover_module_class_member_list_renders_unannotated_width_field() {
    let client = CapturingClient::default();
    let b = Arc::new(Backend::new(client));
    b.load_prelude();

    let uri = Url::parse("file:///repro_sumcase.typort").unwrap();
    b.process_file(&uri, SRC, Some(1));

    // Hover the module name `m` (offset 7): the member list must render the
    // struct with the unannotated `x` field's width recovered as the literal
    // `8` — no panic, no degradation placeholder.
    let text = hover_text(&b, &uri, SRC, 7);
    assert!(!text.is_empty(), "hover over the module name must resolve");
    assert!(
        !text.contains("Variable index out of bounds") && !text.contains("::#"),
        "hover member list degraded:\n{text}"
    );
    assert!(
        text.contains("x: UInt [8]"),
        "unannotated field width should recover as the literal 8, got:\n{text}"
    );

    // Hovering every identifier must never panic (the LSP server survives
    // any cursor position) and never render a degraded SumCase.
    let bytes = SRC.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i].is_ascii_alphabetic() || bytes[i] == b'_' {
            let t = hover_text(&b, &uri, SRC, i);
            assert!(
                !t.contains("Variable index out of bounds") && !t.contains("::#"),
                "hover @{i} degraded:\n{t}"
            );
            while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                i += 1;
            }
        } else {
            i += 1;
        }
    }
}

/// The original trigger: hovering every identifier of the HDL example that
/// first exposed the panic (`examples/hdl/01-basics.typort`, module
/// `exprLet` with the unannotated `let x = a + b` width) must never panic.
#[test]
fn hover_all_identifiers_of_01_basics_never_panics() {
    let path = "examples/hdl/01-basics.typort";
    let Ok(src) = std::fs::read_to_string(path) else {
        eprintln!("skip: {path} not found");
        return;
    };
    let client = CapturingClient::default();
    let b = Arc::new(Backend::new(client));
    b.load_prelude();
    let uri = Url::parse("file:///probe_01_basics.typort").unwrap();
    b.process_file(&uri, &src, Some(1));

    let bytes = src.as_bytes();
    let mut i = 0;
    let mut hovered = 0usize;
    while i < bytes.len() {
        if bytes[i].is_ascii_alphabetic() || bytes[i] == b'_' {
            let t = hover_text(&b, &uri, &src, i);
            if !t.is_empty() {
                hovered += 1;
                assert!(
                    !t.contains("Variable index out of bounds") && !t.contains("::#"),
                    "hover @{i} degraded:\n{t}"
                );
            }
            while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                i += 1;
            }
        } else {
            i += 1;
        }
    }
    assert!(hovered > 50, "expected many hovers, got {hovered}");
}
