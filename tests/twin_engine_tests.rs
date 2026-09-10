// Twin-engine LSP wiring tests (stage 3a/4 of docs/lsp-twin-wiring-2026-09.md).
//
// The `Engine::Twin` path replays the prelude + a file through the bump
// elaborator (`run_decls_with_prelude`) and serves hover / goto / completion /
// inlay from the resulting owned snapshot.  These tests drive the real
// `Backend` surface (load_prelude -> process_file -> hover_at / completion_at)
// and check the twin results against the reference engine on the same source.

use std::sync::{Arc, Mutex};

use elaboration_zoo_lsp::client::ClientLike;
use elaboration_zoo_lsp::{Backend, Engine};
use lsp_types::{CompletionParams, CompletionResponse, MessageType, PartialResultParams, Position, TextDocumentIdentifier, TextDocumentPositionParams, Url, WorkDoneProgressParams};

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

fn backend(engine: Engine) -> Arc<Backend<CapturingClient>> {
    let b = Backend::new_with_engine(CapturingClient::default(), engine);
    b.load_prelude_skip_hdl();
    b
}

fn errors(b: &Arc<Backend<CapturingClient>>, uri: &Url) -> Vec<String> {
    b.client.diagnostics.lock().unwrap().iter()
        .filter(|(u, _, _)| u == uri)
        .flat_map(|(_, d, _)| d.iter())
        .filter(|d| d.severity == Some(lsp_types::DiagnosticSeverity::ERROR))
        .map(|d| d.message.clone())
        .collect()
}

fn hover_text(b: &Arc<Backend<CapturingClient>>, uri: &Url, offset: usize) -> Option<String> {
    b.hover_at(uri, Position::new(0, offset as u32)).map(|h| match h.contents {
        lsp_types::HoverContents::Markup(m) => m.value,
        lsp_types::HoverContents::Scalar(_) => panic!("scalar hover"),
        lsp_types::HoverContents::Array(_) => panic!("array hover"),
        _ => panic!("unknown hover"),
    })
}

/// Hovering a tuple element resolves through the twin snapshot to the
/// element's own type, same as the reference engine.
#[test]
fn twin_hover_matches_reference_on_tuple_element() {
    let uri = Url::parse("file:///twin_tup.typort").unwrap();
    let src = "def foo(a: Nat, b: Boolean): Tuple2[Nat, Boolean] = (a, b)";
    let base = src.rfind("(a, b)").unwrap();

    let rb = backend(Engine::Reference);
    rb.process_file(&uri, src, Some(1));
    assert!(errors(&rb, &uri).is_empty(), "reference tyck errors: {:?}", errors(&rb, &uri));

    let tb = backend(Engine::Twin);
    tb.process_file(&uri, src, Some(1));
    // Twin diagnostics still come from the reference engine, so the source
    // must be error-free for both.
    assert!(errors(&tb, &uri).is_empty(), "twin tyck errors: {:?}", errors(&tb, &uri));

    for off in [base + 1, base + 4] {
        let r = hover_text(&rb, &uri, off);
        let t = hover_text(&tb, &uri, off);
        assert_eq!(t, r, "hover mismatch at offset {off}");
        assert!(t.is_some(), "twin produced no hover at offset {off}");
    }
}

/// A local variable hover (binder name) is served from the twin's push-site
/// entries with the same rendered type as the reference.
#[test]
fn twin_hover_matches_reference_on_local() {
    let uri = Url::parse("file:///twin_local.typort").unwrap();
    // Avoid prelude name collisions (`id` is a prelude def).
    let src = "def myfn(n: Nat): Nat = n";
    let n_use = src.rfind("= n").unwrap() + 2;

    let rb = backend(Engine::Reference);
    rb.process_file(&uri, src, Some(1));
    let tb = backend(Engine::Twin);
    tb.process_file(&uri, src, Some(1));

    let r = hover_text(&rb, &uri, n_use);
    let t = hover_text(&tb, &uri, n_use);
    assert_eq!(t, r, "local hover mismatch");
    assert!(t.is_some(), "twin produced no local hover");
}

/// Member-access completion is served from the twin completion table.
#[test]
fn twin_completion_matches_reference() {
    let uri = Url::parse("file:///twin_comp.typort").unwrap();
    // Member access so the completion table is populated; `Tuple2` is a
    // prelude struct with fields `_1`/`_2`.
    let src = "def f(p: Tuple2[Nat, Nat]): Nat = p.";
    let cursor = src.find("p.").unwrap() + 2;

    let rb = backend(Engine::Reference);
    rb.process_file(&uri, src, Some(1));
    let tb = backend(Engine::Twin);
    tb.process_file(&uri, src, Some(1));

    let labels = |b: &Arc<Backend<CapturingClient>>| -> Vec<String> {
        let params = CompletionParams {
            text_document_position: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri: uri.clone() },
                position: Position::new(0, cursor as u32),
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
            context: None,
        };
        match b.completion_at(params).unwrap() {
            Some(CompletionResponse::Array(items)) => items.into_iter().map(|i| i.label).collect(),
            other => panic!("unexpected completion response: {other:?}"),
        }
    };

    let mut r = labels(&rb);
    let mut t = labels(&tb);
    r.sort();
    t.sort();
    assert_eq!(t, r, "completion mismatch");
}

/// Inlay hints are served from the twin table.
#[test]
fn twin_inlay_matches_reference() {
    let uri = Url::parse("file:///twin_inlay.typort").unwrap();
    let src = "def f(n: Nat): Nat = n\n";

    let rb = backend(Engine::Reference);
    rb.process_file(&uri, src, Some(1));
    let tb = backend(Engine::Twin);
    tb.process_file(&uri, src, Some(1));

    // Compare through the engine-routing handler.
    fn hint_labels(b: &Arc<Backend<CapturingClient>>, uri: &Url) -> Vec<String> {
        b.inlay_hint_at(uri).unwrap_or_default().into_iter()
            .map(|h| match h.label {
                lsp_types::InlayHintLabel::String(s) => s,
                other => format!("{other:?}"),
            })
            .collect()
    }
    assert_eq!(hint_labels(&tb, &uri), hint_labels(&rb, &uri), "inlay mismatch");
}

/// Repeated kicks on the same file reuse the resident prelude and restore
/// per-kick state: the observation after an edit must equal a fresh
/// single-file Backend's, and must not carry over the previous edit's
/// entries.
#[test]
fn twin_resident_reuse_across_kicks_is_consistent() {
    let u = Url::parse("file:///twin_kick.typort").unwrap();
    let s1 = "def first(n: Nat): Nat = n";
    let s2 = "def second(a: Nat, b: Boolean): Tuple2[Nat, Boolean] = (a, b)";

    // One twin Backend, two sequential edits of the same file.
    let tb = backend(Engine::Twin);
    tb.process_file(&u, s1, Some(1));
    let after1 = tb.twin_tables.get(u.as_str()).map(|t| t.hover.clone()).unwrap_or_default();
    tb.process_file(&u, s2, Some(2));
    let after2 = tb.twin_tables.get(u.as_str()).map(|t| t.hover.clone()).unwrap_or_default();

    // Baselines: a fresh twin Backend per content.
    let fb1 = backend(Engine::Twin);
    fb1.process_file(&u, s1, Some(1));
    let want1 = fb1.twin_tables.get(u.as_str()).map(|t| t.hover.clone()).unwrap_or_default();
    let fb2 = backend(Engine::Twin);
    fb2.process_file(&u, s2, Some(1));
    let want2 = fb2.twin_tables.get(u.as_str()).map(|t| t.hover.clone()).unwrap_or_default();

    assert_eq!(after1, want1, "first kick diverged from fresh");
    assert_eq!(after2, want2, "second kick diverged from fresh (state leak?)");
}

/// Twin-authoritative diagnostics (stage 4) match the reference engine's on
/// an error corpus.  The twin now owns the file's diagnostics entirely, so
/// this guards message + span + severity parity through the real Backend.
#[test]
fn twin_diagnostics_match_reference() {
    let corpus: &[&str] = &[
        "def foo: Nat = true",
        "def qux: Nat = nope",
        "def a: Nat = true\ndef b: Boolean = 1",
        "def a: Nat = zero\ndef bad: Nat = true\ndef c: Nat = succ zero",
        "def inc(n: Nat): Nat = succ n\ndef use: Nat = inc true",
        "def s: String = 42",
        "def ok: Nat = zero",
    ];
    // (severity, message, start, end) of the last publish per engine.
    fn last_diags(b: &Arc<Backend<CapturingClient>>, uri: &Url) -> Vec<(Option<lsp_types::DiagnosticSeverity>, String, u32, u32)> {
        let d = b.client.diagnostics.lock().unwrap();
        let last = d.iter().filter(|(u, _, _)| u == uri).last().cloned();
        match last {
            Some((_, ds, _)) => ds.into_iter()
                .map(|d| (d.severity, d.message, d.range.start.character, d.range.end.character))
                .collect(),
            None => Vec::new(),
        }
    }
    for (i, src) in corpus.iter().enumerate() {
        let uri = Url::parse(&format!("file:///twin_diag_{i}.typort")).unwrap();
        let tb = backend(Engine::Twin);
        tb.process_file(&uri, src, Some(1));
        let rb = backend(Engine::Reference);
        rb.process_file(&uri, src, Some(1));
        assert_eq!(
            last_diags(&tb, &uri), last_diags(&rb, &uri),
            "diagnostic mismatch for:\n{src}",
        );
    }
}

/// A cross-file file (imports a project namespace) must fall back to the
/// reference engine: the twin replays only the prelude + the file, so it
/// cannot see the other file's symbols.  Hover across the boundary must still
/// resolve (through the reference), proving the fallback is wired.
#[test]
fn twin_falls_back_for_cross_file_and_still_resolves() {
    let a = Url::parse("file:///twin_xa.typort").unwrap();
    let b_uri = Url::parse("file:///twin_xb.typort").unwrap();
    let tb = backend(Engine::Twin);
    tb.process_file(&a, "package mylib\n\nstruct Tree {\n    h: Nat\n}\n", Some(1));
    let b_src = "import mylib._\n\ndef t: Tree = mylib.Tree.mk zero\n";
    tb.process_file(&b_uri, b_src, Some(1));
    // `Tree` in `mylib.Tree.mk` must resolve to the other file's struct.
    let off = b_src.rfind("Tree.mk").unwrap();
    let rope = ropey::Rope::from_str(b_src);
    let pos = elaboration_zoo_lsp::offset_to_position(off, &rope).unwrap();
    let h = tb.hover_at(&b_uri, pos);
    assert!(h.is_some(), "cross-file hover did not resolve under twin fallback");
    // Must match the reference engine's hover (and, since the reference path
    // is what the fallback uses, its diagnostics too).
    let rb = backend(Engine::Reference);
    rb.process_file(&a, "package mylib\n\nstruct Tree {\n    h: Nat\n}\n", Some(1));
    rb.process_file(&b_uri, b_src, Some(1));
    let hr = rb.hover_at(&b_uri, pos);
    assert_eq!(
        h.map(|x| format!("{:?}", x.contents)),
        hr.map(|x| format!("{:?}", x.contents)),
        "cross-file hover differed from reference",
    );
}

/// Two independent no-import files in one workspace are both twin-owned (the
/// gate is not "only one open file"), and both return correct diagnostics.
#[test]
fn twin_owns_multiple_independent_files() {
    let u1 = Url::parse("file:///twin_m1.typort").unwrap();
    let u2 = Url::parse("file:///twin_m2.typort").unwrap();
    let tb = backend(Engine::Twin);
    tb.process_file(&u1, "def f1(n: Nat): Nat = n", Some(1));
    tb.process_file(&u2, "def f2(a: Nat, b: Boolean): Tuple2[Nat, Boolean] = (a, b)", Some(1));
    for (u, s) in [(&u1, "def f1(n: Nat): Nat = n"), (&u2, "def f2(a: Nat, b: Boolean): Tuple2[Nat, Boolean] = (a, b)")] {
        assert!(errors(&tb, u).is_empty(), "unexpected errors for {u}: {:?}", errors(&tb, u));
        assert!(tb.twin_tables.contains_key(u.as_str()), "twin did not own {u}");
        // Reference comparison.
        let rb = backend(Engine::Reference);
        rb.process_file(u, s, Some(1));
        assert!(errors(&rb, u).is_empty());
    }
}

/// A no-import file that (illegally) uses another open file's symbol must fall
/// back to the reference engine rather than emit a spurious unresolved error.
#[test]
fn twin_falls_back_when_using_another_files_symbol_without_import() {
    let u1 = Url::parse("file:///twin_imp1.typort").unwrap();
    let u2 = Url::parse("file:///twin_imp2.typort").unwrap();
    let tb = backend(Engine::Twin);
    tb.process_file(&u1, "def shared: Nat = zero", Some(1));
    // No import; the reference's shared global table resolves `shared`.
    tb.process_file(&u2, "def use: Nat = shared", Some(1));
    // Either resolved (no error) or fell back — but never a spurious error on
    // a symbol the reference resolves.
    let rb = backend(Engine::Reference);
    rb.process_file(&u1, "def shared: Nat = zero", Some(1));
    rb.process_file(&u2, "def use: Nat = shared", Some(1));
    assert_eq!(errors(&tb, &u2).len(), errors(&rb, &u2).len(),
        "twin produced different error count than reference: twin={:?} ref={:?}",
        errors(&tb, &u2), errors(&rb, &u2));
}

/// End-to-end twin pass on a real HDL example (full HDL prelude, module with
/// `sum := u.sum` vconnT expansion): the twin must produce a non-empty
/// observation snapshot without panicking, and hovering a known signal
/// identifier must agree with the reference engine.
#[test]
fn twin_observes_real_hdl_example() {
    let src = include_str!("../examples/hdl/09-hierarchy.typort");
    // `root`/`u` are the module instance names in 09-hierarchy.
    let probe = src.find("u.").or_else(|| src.find("sum")).unwrap();

    let tb = {
        let b = Backend::new_with_engine(CapturingClient::default(), Engine::Twin);
        b.load_prelude();
        b
    };
    let uri = Url::parse("file:///twin_hdl.typort").unwrap();
    tb.process_file(&uri, src, Some(1));
    let snap = tb.twin_tables.get(uri.as_str())
        .unwrap_or_else(|| panic!("twin produced no HDL snapshot; diagnostics: {:?}", errors(&tb, &uri)));
    assert!(!snap.hover.is_empty(), "twin HDL snapshot has no hover entries");
    assert!(!snap.completion.is_empty(), "twin HDL snapshot has no completion entries");
    drop(snap);

    let rb = {
        let b = Backend::new_with_engine(CapturingClient::default(), Engine::Reference);
        b.load_prelude();
        b
    };
    rb.process_file(&uri, src, Some(1));

    // Hover a specific character and compare engines, allowing the reference
    // to have no entry (twin-only entries are permitted by the parity
    // contract, just not heterogeneous ones).
    if let Some(r) = hover_text(&rb, &uri, probe) {
        assert_eq!(hover_text(&tb, &uri, probe).as_deref(), Some(r.as_str()), "HDL hover mismatch");
    }
}
