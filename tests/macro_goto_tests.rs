// Goto-definition for macro invocations: integration tests that drive the
// LSP `Backend` and assert that a click on a macro call name resolves to the
// matching `macro_rules` declaration — including cross-file jumps into the
// prelude's `hdl-macros.typort` (loaded as `builtin:///hdl-macros.typort`).

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

/// Byte offset of `needle` in `src` (single occurrence expected).
fn byte_offset(src: &str, needle: &str) -> usize {
    src.find(needle).unwrap_or_else(|| panic!("{needle:?} not found in:\n{src}"))
}

/// Byte span of the `macro_rules <name>` name token in the prelude macros
/// file, used as the expected goto target.
fn prelude_macro_def_span(macros_src: &str, name: &str) -> (usize, usize) {
    let def = macros_src.find(&format!("macro_rules {name}")).expect("macro def in prelude");
    let start = def + "macro_rules ".len();
    (start, start + name.len())
}

/// Location (uri + byte range) that `goto_macro_definition` returns for the
/// cursor at `offset` in the given document.
fn goto(b: &Backend<CapturingClient>, uri: &Url, offset: usize) -> Option<(String, usize, usize)> {
    match b.goto_macro_definition(uri, offset) {
        Some(GotoDefinitionResponse::Scalar(loc)) => {
            let rope = b.document_map.get(loc.uri.as_str()).unwrap();
            let start = position_to_offset(loc.range.start, &rope)
                .expect("start position should convert back to offset");
            let end = position_to_offset(loc.range.end, &rope)
                .expect("end position should convert back to offset");
            Some((loc.uri.to_string(), start, end))
        }
        Some(GotoDefinitionResponse::Array(_)) => panic!("expected a scalar location"),
        Some(GotoDefinitionResponse::Link(_)) => panic!("expected a scalar location"),
        None => None,
    }
}

/// Location (uri + byte range) that the full `goto_definition` resolution
/// (`Backend::goto_definition_at`, the same logic the LSP
/// `textDocument/definition` handler runs) returns for the cursor at `offset`.
fn goto_full(b: &Backend<CapturingClient>, uri: &Url, offset: usize) -> Option<(String, usize, usize)> {
    match b.goto_definition_at(uri, offset) {
        Some(GotoDefinitionResponse::Scalar(loc)) => {
            let rope = b.document_map.get(loc.uri.as_str()).unwrap();
            let start = position_to_offset(loc.range.start, &rope)
                .expect("start position should convert back to offset");
            let end = position_to_offset(loc.range.end, &rope)
                .expect("end position should convert back to offset");
            Some((loc.uri.to_string(), start, end))
        }
        Some(GotoDefinitionResponse::Array(_)) => panic!("expected a scalar location"),
        Some(GotoDefinitionResponse::Link(_)) => panic!("expected a scalar location"),
        None => None,
    }
}

/// Byte span of the name token of `def <name>` in a prelude source file.
fn prelude_def_span(src: &str, kw: &str, name: &str) -> (usize, usize) {
    let def = src.find(&format!("{kw} {name}")).expect("def in prelude");
    let start = def + kw.len() + 1;
    (start, start + name.len())
}

/// The prelude (including hdl-macros.typort) is loaded through the same
/// on_change path as the real server, so `document_id`/`document_map` contain
/// the builtin URIs and macro rules carry the prelude's path_id.
fn setup() -> (std::sync::Arc<Backend<CapturingClient>>, String) {
    let client = CapturingClient::default();
    let b = Backend::new(client);
    b.load_prelude();
    let hdl_macros = include_str!("../src/prelude/hdl/hdl-macros.typort").to_string();
    (b, hdl_macros)
}

#[test]
fn goto_module_macro_jumps_to_prelude_definition() {
    let (b, hdl_macros) = setup();
    let uri = Url::parse("file:///adder.typort").unwrap();
    // Real usage from examples/hdl/02-arithmetic.typort: `module name { ... }`
    let src = "module myAdder {\n    let a = UInt[8]\n}\n";
    b.process_file(&uri, src, Some(1));

    // Cursor on the macro name token `module` → jump to `macro_rules module`
    // in the prelude file (cross-file).
    let module_off = byte_offset(src, "module");
    let (def_uri, start, end) = goto(&b, &uri, module_off)
        .expect("click on the macro name should resolve to a definition");
    assert_eq!(def_uri, "builtin:///hdl-macros.typort",
        "module macro is defined in the prelude");
    let (exp_start, exp_end) = prelude_macro_def_span(&hdl_macros, "module");
    assert_eq!((start, end), (exp_start, exp_end),
        "target must be the `module` name token of `macro_rules module`");

    // Cursor anywhere else inside the invocation (here: the first argument)
    // also resolves to the macro definition via the full-span fallback.
    let arg_off = byte_offset(src, "myAdder");
    let (def_uri2, start2, end2) = goto(&b, &uri, arg_off)
        .expect("click inside the invocation should resolve via span fallback");
    assert_eq!(def_uri2, "builtin:///hdl-macros.typort");
    assert_eq!((start2, end2), (exp_start, exp_end));

    // The prelude rope must contain the target text `macro_rules module`.
    let rope = b.document_map.get("builtin:///hdl-macros.typort").unwrap();
    let text: String = rope.chars().collect();
    assert_eq!(&text[exp_start..exp_end], "module");
}

#[test]
fn goto_when_macro_inside_module_body_jumps_to_prelude() {
    let (b, hdl_macros) = setup();
    let uri = Url::parse("file:///ctrl.typort").unwrap();
    // Real usage from examples/hdl/08-control-flow.typort: `when` inside a
    // module body expands through the module macro's re-parse; the recorded
    // expansion still carries the user-file span and the prelude def info.
    let src = "module whenExample {\n    let sel = Bool\n    let out = UInt[8]\n    when sel {\n        out := a\n    } otherwise {\n        out := b\n    }\n}\n";
    b.process_file(&uri, src, Some(1));

    // Cursor on the `when` macro name token (inside the module body). The
    // when call is handled by the Expr macro's when-arm (the module body is
    // an Expr fragment), but the recorded expansion prefers the standalone
    // `macro_rules when` definition for the goto target.
    let when_off = byte_offset(src, "when sel");
    let (def_uri, start, end) = goto(&b, &uri, when_off)
        .expect("click on `when` should resolve to a definition");
    assert_eq!(def_uri, "builtin:///hdl-macros.typort",
        "when macro is defined in the prelude");
    let (exp_start, exp_end) = prelude_macro_def_span(&hdl_macros, "when");
    assert_eq!((start, end), (exp_start, exp_end),
        "target must be the `when` name token of `macro_rules when` (multi-rule macro)");
}

#[test]
fn goto_local_macro_jumps_to_same_file_definition() {
    let (b, _hdl_macros) = setup();
    let uri = Url::parse("file:///local.typort").unwrap();
    // A user-defined macro in the same file: the def span carries this file's
    // path_id, so the target lands back in this file.
    let src = "macro_rules twice {\n    ($x: raw) => { $x + $x }\n}\ndef y: Nat = twice 3\n";
    b.process_file(&uri, src, Some(1));

    let use_off = byte_offset(src, "twice 3");
    let (def_uri, start, end) = goto(&b, &uri, use_off)
        .expect("click on a local macro use should resolve to a definition");
    assert_eq!(def_uri, uri.to_string(), "local macro def lives in the same file");
    let def_start = byte_offset(src, "macro_rules twice") + "macro_rules ".len();
    assert_eq!((start, end), (def_start, def_start + "twice".len()),
        "target must be the `twice` name token of `macro_rules twice`");
}

#[test]
fn goto_builtin_macro_without_definition_returns_none() {
    let (b, _hdl_macros) = setup();
    let uri = Url::parse("file:///builtin.typort").unwrap();
    // `stringify` is a built-in macro with no textual definition: its
    // expansion carries no def info, so goto-definition must not resolve.
    let src = "def s = stringify hello\n";
    b.process_file(&uri, src, Some(1));

    let off = byte_offset(src, "stringify");
    assert!(goto(&b, &uri, off).is_none(),
        "built-in macros without a textual definition have no goto target");
}

#[test]
fn goto_macro_use_in_other_file_with_local_def_and_import() {
    // A macro exported from one user file and used from another: the def
    // span keeps the defining file's path_id, so the target lands in the
    // defining file (same mechanism as the prelude case).
    let (b, _hdl_macros) = setup();
    let def_uri = Url::parse("file:///lib.typort").unwrap();
    let def_src = "#[macro_export]\nmacro_rules shout {\n    ($x: raw) => { println $x }\n}\n";
    b.process_file(&def_uri, def_src, Some(1));

    let use_uri = Url::parse("file:///main.typort").unwrap();
    let use_src = "shout hello\n";
    b.process_file(&use_uri, use_src, Some(1));

    let off = byte_offset(use_src, "shout");
    let (target_uri, start, end) = goto(&b, &use_uri, off)
        .expect("click on an exported macro use should resolve to its definition");
    assert_eq!(target_uri, def_uri.to_string(),
        "def must point back to the exporting file");
    let def_start = byte_offset(def_src, "macro_rules shout") + "macro_rules ".len();
    assert_eq!((start, end), (def_start, def_start + "shout".len()));
}

#[test]
fn goto_calc_body_tokens_resolve_to_their_own_defs() {
    // Regression: a click on the `calc` keyword jumps to `macro_rules calc`,
    // but clicks on identifiers written inside the calc body (variables,
    // function names) must resolve to their own definitions — not to the
    // macro's. The macro expansion keeps call-site spans for captured tokens,
    // so the semantic hover table can resolve them; only the macro NAME token
    // is handled by the macro-invocation path.
    let (b, _hdl_macros) = setup();
    let uri = Url::parse("file:///calc_test.typort").unwrap();
    let src = "\
def zero_add_comm_calc(n: Nat): Eq(0 + n, n + 0) =
    calc {
        0 + n = n by add_zero_left(n)
        n = n + 0 by symm(add_zero_right(n))
    }
";
    b.process_file(&uri, src, Some(1));
    let calc_src = include_str!("../src/prelude/core/calc.typort");
    let nat_src = include_str!("../src/prelude/core/nat.typort");
    let eq_src = include_str!("../src/prelude/core/eq.typort");

    // Click on the `calc` keyword → `macro_rules calc` in the prelude.
    let calc_kw = byte_offset(src, "calc {");
    let (def_uri, start, end) = goto_full(&b, &uri, calc_kw)
        .expect("click on the calc keyword must resolve to the macro definition");
    assert_eq!(def_uri, "builtin:///calc.typort");
    let (exp_start, exp_end) = prelude_macro_def_span(calc_src, "calc");
    assert_eq!((start, end), (exp_start, exp_end),
        "calc keyword must target the `calc` name token of `macro_rules calc`");

    // Click on a function name used as a step proof → its own def in the prelude.
    let add_zero_left_off = byte_offset(src, "add_zero_left");
    let (def_uri, start, end) = goto_full(&b, &uri, add_zero_left_off)
        .expect("click on add_zero_left must resolve to its definition");
    assert_eq!(def_uri, "builtin:///nat.typort",
        "add_zero_left is defined in the nat prelude");
    let (exp_start, exp_end) = prelude_def_span(nat_src, "def", "add_zero_left");
    assert_eq!((start, end), (exp_start, exp_end));

    // Click on another proof helper → its own def in the eq prelude.
    let symm_off = byte_offset(src, "symm");
    let (def_uri, start, end) = goto_full(&b, &uri, symm_off)
        .expect("click on symm must resolve to its definition");
    assert_eq!(def_uri, "builtin:///eq.typort");
    let (exp_start, exp_end) = prelude_def_span(eq_src, "def", "symm");
    assert_eq!((start, end), (exp_start, exp_end));

    // Click on a variable inside a proof application → the function parameter.
    let n_arg_off = byte_offset(src, "add_zero_left(n)") + "add_zero_left(".len();
    let (def_uri, start, end) = goto_full(&b, &uri, n_arg_off)
        .expect("click on n inside add_zero_left(n) must resolve to the param");
    assert_eq!(def_uri, uri.to_string(), "the parameter lives in the same file");
    let param_n = byte_offset(src, "(n: Nat)") + 1;
    assert_eq!((start, end), (param_n, param_n + 1),
        "must target the `n` parameter of the def");

    // Click on a variable written as a step term → the function parameter.
    let step1_n_off = byte_offset(src, "0 + n = n by") + 4;
    let (def_uri, start, end) = goto_full(&b, &uri, step1_n_off)
        .expect("click on n in the first step must resolve to the param");
    assert_eq!(def_uri, uri.to_string());
    assert_eq!((start, end), (param_n, param_n + 1));
}

#[test]
fn goto_module_macro_full_path_keeps_fallbacks() {
    // The full goto_definition path must keep the module macro behavior:
    // the `module` keyword resolves to `macro_rules module` in the prelude
    // via the macro name-token match; the module name argument is a defining
    // occurrence (its `stringify` literal maps back to itself); positions with
    // no semantic entry (gaps inside the invocation) still fall back to the
    // macro definition via the full invocation span.
    let (b, hdl_macros) = setup();
    let uri = Url::parse("file:///adder.typort").unwrap();
    let src = "module myAdder {\n    let a = UInt[8]\n}\n";
    b.process_file(&uri, src, Some(1));
    let (exp_start, exp_end) = prelude_macro_def_span(&hdl_macros, "module");

    let module_off = byte_offset(src, "module");
    let (def_uri, start, end) = goto_full(&b, &uri, module_off)
        .expect("click on the module keyword should resolve to the macro def");
    assert_eq!(def_uri, "builtin:///hdl-macros.typort");
    assert_eq!((start, end), (exp_start, exp_end));

    // The argument is a defining occurrence: the semantic table maps it to
    // itself (the module name), not to the macro definition.
    let arg_off = byte_offset(src, "myAdder");
    let (def_uri2, start2, end2) = goto_full(&b, &uri, arg_off)
        .expect("click on the module name should resolve to itself");
    assert_eq!(def_uri2, uri.to_string());
    assert_eq!((start2, end2), (arg_off, arg_off + "myAdder".len()));

    // A gap inside the invocation with no semantic entry → macro def fallback.
    let gap_off = byte_offset(src, "myAdder") - 1;
    let (def_uri3, start3, end3) = goto_full(&b, &uri, gap_off)
        .expect("click inside the invocation should resolve via span fallback");
    assert_eq!(def_uri3, "builtin:///hdl-macros.typort");
    assert_eq!((start3, end3), (exp_start, exp_end));
}

#[test]
fn goto_when_keyword_full_path_jumps_to_prelude() {
    // The `when` macro call inside a module body: the full goto_definition
    // path still resolves the `when` keyword to `macro_rules when` via the
    // name-token match (the expansion is recorded through the module body's
    // Expr fragment).
    let (b, hdl_macros) = setup();
    let uri = Url::parse("file:///ctrl.typort").unwrap();
    let src = "module whenExample {\n    let sel = Bool\n    when sel {\n        out := a\n    } otherwise {\n        out := b\n    }\n}\n";
    b.process_file(&uri, src, Some(1));

    let when_off = byte_offset(src, "when sel");
    let (def_uri, start, end) = goto_full(&b, &uri, when_off)
        .expect("click on `when` should resolve to a definition");
    assert_eq!(def_uri, "builtin:///hdl-macros.typort");
    let (exp_start, exp_end) = prelude_macro_def_span(&hdl_macros, "when");
    assert_eq!((start, end), (exp_start, exp_end));
}

#[test]
fn goto_module_body_stmt_first_token_resolves_to_signal_def() {
    // Regression: the first token of an Expr statement in a module body
    // (`sum` in `sum := a +^ b`) must NOT jump to `macro_rules Expr`. The
    // module body is an Expr fragment, and the fragment records the first
    // call-site token as the expansion's `name` — which used to make the
    // level-1 macro-NAME-token match fire on plain user code. The token must
    // resolve through the semantic table to the signal's own definition, like
    // the other tokens of the same statement.
    let (b, hdl_macros) = setup();
    let uri = Url::parse("file:///adder.typort").unwrap();
    let src = "\
module arithmeticUInt {
    let a = UInt[8]
    let b = UInt[8]
    let sum = UInt[8]
    sum := a +^ b
}
";
    b.process_file(&uri, src, Some(1));
    let (expr_start, expr_end) = prelude_macro_def_span(&hdl_macros, "Expr");

    // First token of the body statement: the assignment target `sum`.
    let sum_off = byte_offset(src, "sum := a");
    let (def_uri, start, end) = goto_full(&b, &uri, sum_off)
        .expect("click on the statement's first token should resolve to a definition");
    assert_eq!(def_uri, uri.to_string(), "the signal is defined in the same file");
    let let_sum = byte_offset(src, "let sum") + "let ".len();
    assert_eq!((start, end), (let_sum, let_sum + 3),
        "must target the `sum` binder of `let sum`");
    assert_ne!((start, end), (expr_start, expr_end),
        "must not resolve to the Expr macro definition");

    // A later token of the same statement still resolves to its own def.
    let a_off = byte_offset(src, "sum := a") + "sum := ".len();
    let (def_uri2, start2, end2) = goto_full(&b, &uri, a_off)
        .expect("click on `a` should resolve to a definition");
    assert_eq!(def_uri2, uri.to_string());
    let let_a = byte_offset(src, "let a =") + "let ".len();
    assert_eq!((start2, end2), (let_a, let_a + 1),
        "must target the `a` binder of `let a`");

    // The operator keeps resolving to its prelude definition.
    let op_off = byte_offset(src, "a +^ b") + 2;
    let (def_uri3, start3, end3) = goto_full(&b, &uri, op_off)
        .expect("click on `+^` should resolve to a definition");
    assert_eq!(def_uri3, "builtin:///hdl-ops.typort",
        "`+^` is defined in the hdl-ops prelude");
    let hdl_ops = include_str!("../src/prelude/hdl/hdl-ops.typort");
    let (exp_op_start, exp_op_end) = prelude_def_span(hdl_ops, "def", "+^");
    assert_eq!((start3, end3), (exp_op_start, exp_op_end),
        "must target the `+^` name token of `def +^`");
}

/// Regression for the goto-definition def-span coincidence hijack (NEW-1 in
/// docs/l13-bugs-2026-08-08.md, fixed on branch task/l13-bugs2 by 32d8d221).
///
/// Step 2 of `goto_definition_at` used to end with an `.or({ ... })` fallback
/// that matched *hover-table entries whose DEF span contains the cursor
/// offset* (`Span::contains` ignores `path_id`) and then returned the entry's
/// USE span as the jump target. The two span families live in different files,
/// so a cursor byte in this file could byte-coincide with the def span of a
/// prelude declaration and silently jump to an unrelated use site in this
/// file:
///
///   use [581..584] (this file)  ->  def [549..552] (nat.typort, `Nat`)
///   click at 549/550/551 (bytes 7-9 of `macro_rules`) ->
///       Array([581..584])   // pre-fix: jumps to the `Nat` use site
///       None                // post-fix: no goto target
///
/// The fallback was removed: use-span hits are already resolved by the main
/// branch, and a def-span hit returning use sites is `references` semantics,
/// not `goto`. Non-semantic offsets now fall through to the macro-invocation
/// fallback or return `None`.
#[test]
fn goto_keyword_interior_not_hijacked_by_def_span_coincidence() {
    let (b, _hdl_macros) = setup();
    let body = "macro_rules foo { () => { 1 } }\ndef x: Nat = foo()\n";

    // (a) The original repro layout: `macro_rules` starts at offset 0, so the
    // keyword's bytes 7-9 are the file's offsets 7-9. On the current prelude
    // revision no def span starts this early (`Nat` is declared at [549..552]
    // in nat.typort, not [7..10] as in the 2026-08 prelude), so this exact
    // layout is already immune; pin the intended behaviour anyway.
    let plain_uri = Url::parse("file:///goto_probe_plain.typort").unwrap();
    b.process_file(&plain_uri, body, Some(1));
    for k in 7..=9 {
        assert!(
            b.goto_definition_at(&plain_uri, k).is_none(),
            "byte {k} of `macro_rules` (offset {k}) is not a semantic token and must not resolve"
        );
    }

    // (b) Deliberate byte-offset coincidence: pad the file with a comment so
    // that bytes 7-9 of the `macro_rules` keyword land exactly inside the DEF
    // span of the prelude `Nat`. This is the same mechanism as the original
    // report, just aligned with the def span of the current prelude (comments
    // are stripped byte-preservingly, so the padding does not change any
    // semantic span, and the coincidence offsets are derived from the hover
    // table rather than hardcoded, keeping the test valid if the prelude
    // shifts).
    let uri = Url::parse("file:///goto_probe_aligned.typort").unwrap();
    b.process_file(&uri, "def probe_nat: Nat = 1\n", Some(1));
    let nat_id = *b
        .document_id
        .get("builtin:///nat.typort")
        .expect("the nat prelude is loaded");
    let nat_def = b
        .hover_entries(uri.as_str())
        .into_iter()
        .find(|(_, def, _)| def.path_id == nat_id)
        .map(|(_, def, _)| def)
        .expect("a `Nat` use must carry a def span into nat.typort");
    let pad_len = nat_def.start_offset as usize - 7;
    assert!(pad_len > 2, "Nat def span {nat_def:?} is too small to align");
    let mut src = String::from("//");
    while src.len() < pad_len - 1 {
        src.push(' ');
    }
    src.push('\n');
    src.push_str(body);
    assert_eq!(src.len(), pad_len + body.len());
    assert_eq!(&src[pad_len..pad_len + "macro_rules".len()], "macro_rules");
    b.process_file(&uri, &src, Some(2));

    // Positive control: the `Nat` use itself still resolves to the prelude
    // declaration the def span points at (the fix only drops the fallback).
    let local_id = *b.document_id.get(uri.as_str()).unwrap();
    let (nat_use, nat_def_now) = b
        .hover_entries(uri.as_str())
        .into_iter()
        .find(|(u, d, _)| u.path_id == local_id && d.path_id == nat_id)
        .map(|(u, d, _)| (u, d))
        .expect("the padded file still holds a `Nat` use entry");
    assert_eq!((nat_def_now.start_offset, nat_def_now.end_offset),
               (nat_def.start_offset, nat_def.end_offset),
               "padding must not move the prelude def span");
    let loc = match b.goto_definition_at(&uri, nat_use.start_offset as usize) {
        Some(GotoDefinitionResponse::Scalar(loc)) => loc,
        _ => panic!("a `Nat` use must resolve to the prelude declaration"),
    };
    assert_eq!(loc.uri.as_str(), "builtin:///nat.typort");
    let def_rope = b.document_map.get(loc.uri.as_str()).unwrap();
    assert_eq!(
        position_to_offset(loc.range.start, &def_rope).unwrap(),
        nat_def.start_offset as usize,
        "goto must land on the `Nat` name token of `enum Nat`"
    );

    // The hijack: keyword bytes 7-9 coincide with `Nat`'s def span [549..552].
    // Pre-fix each returned `Array([<the Nat use span>])`; post-fix `None`.
    for k in 7..=9 {
        let off = pad_len + k;
        assert!(
            off >= nat_def.start_offset as usize && off < nat_def.end_offset as usize,
            "offset {off} must fall inside the Nat def span [{start}..{end}) for this test to exercise the coincidence",
            start = nat_def.start_offset,
            end = nat_def.end_offset,
        );
        assert!(
            b.goto_definition_at(&uri, off).is_none(),
            "byte {k} of `macro_rules` (offset {off}) byte-coincides with the def span of the prelude `Nat`; \
             goto-definition must not hijack it into the local `Nat` use site"
        );
    }
}
