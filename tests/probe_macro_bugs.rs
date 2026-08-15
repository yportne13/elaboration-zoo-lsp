// TEMPORARY probe: dump hover + goto results at every byte offset of macro
// invocations, to locate remaining bugs. NOT a permanent test.

use std::sync::Mutex;

use elaboration_zoo_lsp::client::ClientLike;
use elaboration_zoo_lsp::{position_to_offset, Backend};
use lsp_types::{Diagnostic, GotoDefinitionResponse, MessageType, Url};

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

fn setup() -> (std::sync::Arc<Backend<CapturingClient>>, String) {
    let client = CapturingClient::default();
    let b = Backend::new(client);
    b.load_prelude();
    let hdl_macros = include_str!("../src/prelude/hdl/hdl-macros.typort").to_string();
    (b, hdl_macros)
}

fn hover_text(b: &Backend<CapturingClient>, uri: &Url, offset: usize) -> Option<String> {
    let infer = b.hover_table.get(uri.as_str())?;
    let id = b.document_id.get(uri.as_str())?;
    let (span, _, hcxt, val) = infer.hover_entry_at(*id, offset)?;
    Some(format!(
        "[{:?}..{:?}] {}",
        span.start_offset,
        span.end_offset,
        elaboration_zoo_lsp::L13_namespace::pretty::pretty_tm(0, hcxt.names(), &infer.quote(&hcxt.decl, hcxt.lvl, val))
    ))
}

fn goto_text(b: &Backend<CapturingClient>, uri: &Url, offset: usize) -> Option<String> {
    match b.goto_definition_at(uri, offset) {
        Some(GotoDefinitionResponse::Scalar(loc)) => {
            let rope = b.document_map.get(loc.uri.as_str()).unwrap();
            let start = position_to_offset(loc.range.start, &rope)?;
            let end = position_to_offset(loc.range.end, &rope)?;
            Some(format!("{}[{start}..{end}]", loc.uri.as_str()))
        }
        Some(GotoDefinitionResponse::Array(locs)) => {
            let mut parts = Vec::new();
            for loc in locs {
                let rope = b.document_map.get(loc.uri.as_str()).unwrap();
                let start = position_to_offset(loc.range.start, &rope)?;
                let end = position_to_offset(loc.range.end, &rope)?;
                parts.push(format!("{}[{start}..{end}]", loc.uri.as_str()));
            }
            Some(format!("[{}]", parts.join(", ")))
        }
        Some(GotoDefinitionResponse::Link(_)) => None,
        None => None,
    }
}

/// Print every hover-table entry whose span intersects [lo, hi].
fn dump_entries(b: &Backend<CapturingClient>, uri: &Url, src: &str, lo: usize, hi: usize, label: &str) {
    let infer = match b.hover_table.get(uri.as_str()) {
        Some(i) => i,
        None => { println!("{label}: NO hover table"); return; }
    };
    println!("\n-- entries of {label} intersecting [{lo}..{hi}] --");
    for (span, def, hcxt, val) in infer.hover_table.iter() {
        if span.start_offset as usize > hi || (span.end_offset as usize) < lo {
            continue;
        }
        let text = elaboration_zoo_lsp::L13_namespace::pretty::pretty_tm(0, hcxt.names(), &infer.quote(&hcxt.decl, hcxt.lvl, val));
        let def_uri = b.document_id.iter()
            .find(|e| *e.value() == def.path_id)
            .map(|e| e.key().clone())
            .unwrap_or_else(|| format!("path{}", def.path_id));
        println!(
            "  span=[{:?}..{:?}] path={} def=[{:?}..{:?}] defpath={} ({}) {}",
            span.start_offset, span.end_offset, span.path_id,
            def.start_offset, def.end_offset, def.path_id, def_uri,
            text
        );
    }
}

/// Print a line per offset; mark interesting offsets with `*`.
fn dump(b: &Backend<CapturingClient>, uri: &Url, src: &str, markers: &[usize]) {
    println!("\n=== {} ===", uri.as_str());
    println!("{src}");
    for off in 0..src.len() {
        let ch = &src[off..off + 1];
        if ch == "\n" || ch == " " || ch == "\r" || ch == "\t" {
            continue;
        }
        let h = hover_text(b, uri, off).map(|s| format!("hover={s}")).unwrap_or_default();
        let g = goto_text(b, uri, off).map(|s| format!("goto={s}")).unwrap_or_default();
        let mark = if markers.contains(&off) { " *" } else { "" };
        println!("@{off:4} {ch:<4} {h} {g}{mark}");
    }
}

#[test]
fn probe_macro_hover_goto() {
    let (b, _hdl_macros) = setup();

    // ---- calc: does the transcriber really drop $x2/$z? ----
    {
        let uri = Url::parse("file:///calc_x2_probe.typort").unwrap();
        let src = "\
def bad_calc(n: Nat): Eq(0 + n, n + 0) =
    calc {
        0 + n = n by add_zero_left(n)
        garbage1 = garbage2 by symm(add_zero_right(n))
    }
";
        b.process_file(&uri, src, Some(1));
        let diags: Vec<_> = b.client.diagnostics.lock().unwrap().iter()
            .filter(|(u, _, _)| u == &uri)
            .flat_map(|(_, d, _)| d.iter())
            .filter(|d| d.severity == Some(lsp_types::DiagnosticSeverity::ERROR))
            .map(|d| d.message.clone())
            .collect();
        println!("bad_calc (garbage step-2 terms) ERRORS: {diags:?}");
        if let Some(expansions) = b.macro_expansion_map.get(uri.as_str()) {
            for e in expansions.iter() {
                println!("  calc expansion text: {:?}", e.expanded_text);
            }
        }
        // Manual equivalent with an explicit per-step check-let: does it typecheck?
        let uri2 = Url::parse("file:///calc_manual_probe.typort").unwrap();
        let src2 = "\
def manual(n: Nat): Eq(0 + n, n + 0) =
    let _c : Eq (0 + n) (n) = (add_zero_left(n));
    let _ : Eq (n) (n + 0) = (symm(add_zero_right(n)));
    let _c = trans (_c) (symm(add_zero_right(n)));
    _c
";
        b.process_file(&uri2, src2, Some(1));
        let diags2: Vec<_> = b.client.diagnostics.lock().unwrap().iter()
            .filter(|(u, _, _)| u == &uri2)
            .flat_map(|(_, d, _)| d.iter())
            .filter(|d| d.severity == Some(lsp_types::DiagnosticSeverity::ERROR))
            .map(|d| d.message.clone())
            .collect();
        println!("manual per-step check-let ERRORS: {diags2:?}");

        // Single-line form: the chain's repetition unit must lead with `=`
        // (`= $x2 = $z by $q`); with the fix a two-step single-line chain
        // parses cleanly and its second-step written terms are checked.
        let uri3 = Url::parse("file:///single_ok_probe.typort").unwrap();
        let src5 = "def ok_one_line(n: Nat): Eq (0 + n) (n + 0) = calc 0 + n = n by add_zero_left n = n = n + 0 by symm (add_zero_right n)\n";
        b.process_file(&uri3, src5, Some(1));
        let diags5: Vec<_> = b.client.diagnostics.lock().unwrap().iter()
            .filter(|(u, _, _)| u == &uri3)
            .flat_map(|(_, d, _)| d.iter())
            .map(|d| format!("{:?}: {}", d.severity, d.message))
            .collect();
        println!("single ok line (fixed syntax) diags: {diags5:?}");
        let uri4 = Url::parse("file:///single_bad_probe.typort").unwrap();
        let src6 = "def neg_j: Eq (7 + 0) (0 + 7) = calc 7 + 0 = 7 by add_zero_right 7 = 7 = 5 by symm (add_zero_left 7)\n";
        b.process_file(&uri4, src6, Some(1));
        let diags6: Vec<_> = b.client.diagnostics.lock().unwrap().iter()
            .filter(|(u, _, _)| u == &uri4)
            .flat_map(|(_, d, _)| d.iter())
            .filter(|d| d.severity == Some(lsp_types::DiagnosticSeverity::ERROR))
            .map(|d| d.message.clone())
            .collect();
        println!("single bad line (wrong step-2 terms) ERRORS: {diags6:?}");
    }

    // Byte-offset sanity check on the hdl-types prelude (the `:=` def span).
    {
        let src = include_str!("../src/prelude/hdl/hdl-types.typort");
        let def_at = src.find("def :=").unwrap();
        println!("hdl-types: `def :=` at byte {def_at}; bytes[232..240]={:?}", &src[232..240]);
        println!("hdl-types bytes[226..236]={:?} bytes[248..254]={:?}", &src[226..236], &src[248..254]);
        let op = include_str!("../src/prelude/core/op.typort");
        println!("op.typort bytes[370..382]={:?}", &op[370..382]);
        let ops = include_str!("../src/prelude/hdl/hdl-ops.typort");
        println!("hdl-ops bytes[2978..2990]={:?}", &ops[2978..2990]);
    }

    // ---- calc ----
    {
        let uri = Url::parse("file:///calc_probe.typort").unwrap();
        let src = "\
def zero_add_comm_calc(n: Nat): Eq(0 + n, n + 0) =
    calc {
        0 + n = n by add_zero_left(n)
        n = n + 0 by symm(add_zero_right(n))
    }
";
        b.process_file(&uri, src, Some(1));
        let calc_off = src.find("calc {").unwrap();
        let by_off = src.find(" by ").unwrap() + 1;
        let eq_off = src.find("= n by").unwrap() + 1;
        dump(&b, &uri, src, &[calc_off, by_off, eq_off]);
        dump_entries(&b, &uri, src, calc_off, calc_off + 4, "calc invocation head");
        dump_entries(&b, &uri, src, 35, 46, "calc `0 + n, n + 0` args");
    }

    // ---- module ----
    {
        let uri = Url::parse("file:///mod_probe.typort").unwrap();
        let src = "\
module myAdder {
    let a = UInt[8]
    let sum = UInt[8]
    sum := a +^ a
}
";
        b.process_file(&uri, src, Some(1));
        let module_off = src.find("module").unwrap();
        let name_off = src.find("myAdder").unwrap();
        let let_off = src.find("let a").unwrap();
        let assign_off = src.find(":=").unwrap();
        let sum_use_off = src.find("sum := ").unwrap();
        let body_open_off = src.find('{').unwrap();
        dump(&b, &uri, src, &[module_off, name_off, let_off, assign_off, sum_use_off, body_open_off]);
        dump_entries(&b, &uri, src, 0, src.len(), "module file");
    }

    // ---- when inside module ----
    {
        let uri = Url::parse("file:///when_probe.typort").unwrap();
        let src = "\
module whenExample {
    let sel = Bool
    let out = UInt[8]
    let a = UInt[8]
    let b = UInt[8]
    when sel {
        out := a
    } otherwise {
        out := b
    }
}
";
        b.process_file(&uri, src, Some(1));
        let when_off = src.find("when sel").unwrap();
        let otherwise_off = src.find("otherwise").unwrap();
        let assign_off = src.find("out := a").unwrap() + 4;
        let out_use_off = src.find("out := a").unwrap();
        dump(&b, &uri, src, &[when_off, otherwise_off, assign_off, out_use_off]);
    }

    // ---- local macro ----
    {
        let uri = Url::parse("file:///local_probe.typort").unwrap();
        let src = "\
macro_rules twice {
    ($x: raw) => { $x + $x }
}
def y: Nat = twice 3
";
        b.process_file(&uri, src, Some(1));
        let twice_off = src.find("twice 3").unwrap();
        let three_off = src.find("twice 3").unwrap() + 6;
        dump(&b, &uri, src, &[twice_off, three_off]);
        dump_entries(&b, &uri, src, 0, src.len(), "local file ALL");
        let diags: Vec<_> = b.client.diagnostics.lock().unwrap().iter()
            .filter(|(u, _, _)| u == &uri)
            .flat_map(|(_, d, _)| d.iter())
            .filter(|d| d.severity == Some(lsp_types::DiagnosticSeverity::ERROR))
            .map(|d| d.message.clone())
            .collect();
        println!("local file ERRORS: {diags:?}");
        if let Some(expansions) = b.macro_expansion_map.get(uri.as_str()) {
            for e in expansions.iter() {
                println!("  expansion: name={:?} span=[{}..{}] name_token_is_macro={} def=({:?},{:?},{:?}) text={:?}",
                    e.name, e.start_offset, e.end_offset, e.name_token_is_macro,
                    e.def_start_offset, e.def_end_offset, e.def_path_id,
                    e.expanded_text.chars().take(40).collect::<String>());
            }
        }
    }

    // ---- control: direct `3 + 3` and `twice n` with a var arg ----
    {
        let uri = Url::parse("file:///ctrl2_probe.typort").unwrap();
        let src = "\
def d1: Nat = 3 + 3
def d2(n: Nat): Nat = n + 3
macro_rules twice {
    ($x: raw) => { $x + $x }
}
def d3(n: Nat): Nat = twice n
";
        b.process_file(&uri, src, Some(1));
        let d1_plus = src.find("d1: Nat = 3 + 3").unwrap() + 13;
        let d2_plus = src.find("n + 3").unwrap() + 2;
        let d3_plus = src.find("twice n").unwrap() + 7;
        dump_entries(&b, &uri, src, d1_plus - 3, d1_plus + 3, "d1 `3 + 3` (direct)");
        dump_entries(&b, &uri, src, d2_plus - 3, d2_plus + 3, "d2 `n + 3` (direct)");
        dump_entries(&b, &uri, src, src.find("twice n").unwrap() - 2, src.len(), "d3 `twice n` (macro, var arg)");
        if let Some(expansions) = b.macro_expansion_map.get(uri.as_str()) {
            for e in expansions.iter() {
                println!("  ctrl2 expansion: name={:?} span=[{}..{}] name_token_is_macro={} text={:?}",
                    e.name, e.start_offset, e.end_offset, e.name_token_is_macro,
                    e.expanded_text.chars().take(40).collect::<String>());
            }
        }
        let diags: Vec<_> = b.client.diagnostics.lock().unwrap().iter()
            .filter(|(u, _, _)| u == &uri)
            .flat_map(|(_, d, _)| d.iter())
            .filter(|d| d.severity == Some(lsp_types::DiagnosticSeverity::ERROR))
            .map(|d| d.message.clone())
            .collect();
        println!("ctrl2 ERRORS: {diags:?}");
        // Parse ctrl2 source and dump the Raw body of each def to see how the
        // macro-expanded `n + n` / `3 + 3` parses.
        use elaboration_zoo_lsp::L13_namespace::parser::{parser_with_macros, MacroExpansionInfo};
        use elaboration_zoo_lsp::L13_namespace::preprocess;
        use std::collections::HashMap;
        let global: HashMap<String, Vec<elaboration_zoo_lsp::L13_namespace::parser::macros::MacroRule>> = HashMap::new();
        let now_id = *b.document_id.get(uri.as_str()).unwrap();
        if let Some((decls, errs, _, exps)) = parser_with_macros(&preprocess(src), now_id, &global) {
            println!("ctrl2 parse errors: {}", errs.len());
            for d in decls.iter() {
                if let elaboration_zoo_lsp::L13_namespace::parser::syntax::Decl::Def { name, body, .. } = d {
                    println!("  def {} body = {body}", name.data);
                }
            }
        }
    }

    // ---- stringify ----
    {
        let uri = Url::parse("file:///str_probe.typort").unwrap();
        let src = "def s = stringify hello\n";
        b.process_file(&uri, src, Some(1));
        let str_off = src.find("stringify").unwrap();
        dump(&b, &uri, src, &[str_off]);
    }
}
