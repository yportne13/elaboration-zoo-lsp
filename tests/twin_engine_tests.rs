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
    logs: Mutex<Vec<String>>,
}

impl ClientLike for CapturingClient {
    fn publish_diagnostics(&self, uri: Url, diagnostics: Vec<lsp_types::Diagnostic>, version: Option<i32>) {
        self.diagnostics.lock().unwrap().push((uri, diagnostics, version));
    }
    fn show_message(&self, _typ: MessageType, _message: String) {}
    fn log_message(&self, _typ: MessageType, message: String) {
        self.logs.lock().unwrap().push(message);
    }
}

fn backend(engine: Engine) -> Arc<Backend<CapturingClient>> {
    let b = Backend::new_with_engine(CapturingClient::default(), engine);
    b.load_prelude_skip_hdl();
    b
}

/// Backend with the FULL HDL prelude (for the HDL corpus tests).
fn backend_hdl(engine: Engine) -> Arc<Backend<CapturingClient>> {
    let b = Backend::new_with_engine(CapturingClient::default(), engine);
    b.load_prelude();
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

/// Every `window/logMessage` line the backend emitted (fallback reasons land here).
fn logs(b: &Arc<Backend<CapturingClient>>) -> Vec<String> {
    b.client.logs.lock().unwrap().clone()
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
        // println INFORMATION diagnostics (reference publishes them in a
        // second phase; the twin publishes them in one pass — the final set
        // must agree).
        "def foo: Nat = succ zero\nprintln foo\n",
        "def good: Nat = succ zero\nprintln good\ndef bad: Nat = true\n",
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

/// The full HDL example corpus: twin-authoritative elaboration must produce
/// the same diagnostics and the same hover entries as the reference engine on
/// every example (not just 09-hierarchy).  This is the takeover's real-
/// workload acceptance test.
#[test]
fn twin_matches_reference_on_all_hdl_examples() {
    let dir = std::path::Path::new("examples/hdl");
    let mut files: Vec<std::path::PathBuf> = std::fs::read_dir(dir)
        .expect("examples/hdl")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().map(|e| e == "typort").unwrap_or(false))
        .collect();
    files.sort();
    assert!(files.len() >= 20, "expected the HDL corpus, found {}", files.len());

    for (i, path) in files.iter().enumerate() {
        let src = std::fs::read_to_string(path).unwrap();
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        let uri = Url::parse(&format!("file:///hdl_{i}.typort")).unwrap();

        let tb = backend_hdl(Engine::Twin);
        tb.process_file(&uri, &src, Some(1));
        let rb = backend_hdl(Engine::Reference);
        rb.process_file(&uri, &src, Some(1));

        // Diagnostics: last publish, as (severity, message, range).
        fn last(b: &Arc<Backend<CapturingClient>>, u: &Url) -> Vec<(Option<lsp_types::DiagnosticSeverity>, String, u32, u32)> {
            let d = b.client.diagnostics.lock().unwrap();
            match d.iter().filter(|(x, _, _)| x == u).last().cloned() {
                Some((_, ds, _)) => ds.into_iter()
                    .map(|d| (d.severity, d.message, d.range.start.character, d.range.end.character))
                    .collect(),
                None => Vec::new(),
            }
        }
        assert_eq!(last(&tb, &uri), last(&rb, &uri), "diagnostics differ on {name}");

        // Hover: compare what the user actually sees — the resolved entry at
        // every identifier position in THIS file.  Comparing whole tables is
        // noisy on macro-heavy files because prelude rule-source tokens (same
        // offsets, different path_id) collide once path_id is normalized away
        // (wiring doc deviation 3/6), and those are never user hover targets.
        let rope = ropey::Rope::from_str(&src);
        let bytes = src.as_bytes();
        let mut i = 0usize;
        while i < bytes.len() {
            if bytes[i].is_ascii_alphabetic() || bytes[i] == b'_' {
                if let Some(pos) = elaboration_zoo_lsp::offset_to_position(i, &rope) {
                    let rt = rb.resolved_hover_entry(uri.as_str(), i);
                    // Only assert entries whose token AND definition are both
                    // in this file.  Macro-generated tokens resolve to prelude
                    // rule sources (deviation 3) and qualified member accesses
                    // on macro output render from a value the twin reaches via
                    // a different path (deviation 4 residual, e.g.
                    // `basicDecls.create[8].tree` renders the create signature
                    // in the twin vs the projected `ModuleTree` in the
                    // reference) — both are tracked deviations, not user-file
                    // symbol hovers.
                    if let Some((tspan, dspan, _)) = &rt {
                        if (tspan.start_offset as usize) < src.len()
                            && (dspan.start_offset as usize) < src.len()
                        {
                            let tt = tb.resolved_hover_entry(uri.as_str(), i);
                            // Assert the twin resolves a hover wherever the
                            // reference does (no missing entries) with the
                            // same use-site span.  The RENDERED text is not
                            // compared here: on macro-generated method /
                            // qualified paths the twin renders from a value it
                            // reaches via a different route (e.g. the generic
                            // `Vec.get` signature vs the instantiated
                            // `Stream` one) — a tracked deviation family
                            // (wiring doc deviations 4/6), covered strictly by
                            // the curated LSP guard suites.
                            assert!(
                                tt.is_some(),
                                "twin missing hover on {name} at byte {i} ({pos:?}): ref={:?}",
                                rt.as_ref().map(|(_, _, s)| s),
                            );
                            assert_eq!(
                                tt.map(|(a, _, _)| (a.start_offset, a.end_offset)),
                                rt.as_ref().map(|(a, _, _)| (a.start_offset, a.end_offset)),
                                "hover span mismatch on {name} at byte {i} ({pos:?})",
                            );
                        }
                    }
                }
                while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                    i += 1;
                }
            } else {
                i += 1;
            }
        }
    }
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

/// Error states whose error classes have verified parity stay twin-owned
/// (2026-09-14 gate narrowing): the typing period no longer pays the twin
/// pass *and* the full reference fallback.  The twin's own diagnostics are
/// published, and symbols from the last clean kick are kept (the
/// reference's decision 1-a).
#[test]
fn twin_owns_trusted_error_state_and_keeps_previous_symbols() {
    let u = Url::parse("file:///twin_err_own.typort").unwrap();
    let tb = backend(Engine::Twin);
    let clean = "def good: Nat = zero\ndef use: Nat = succ good\n";
    tb.process_file(&u, clean, Some(1));
    assert!(errors(&tb, &u).is_empty());
    assert!(tb.twin_tables.contains_key(u.as_str()), "clean kick not twin-owned");

    // Introduce a can't-unify error in a new decl.
    let dirty = "def good: Nat = zero\ndef use: Nat = succ good\ndef bad: Nat = true\n";
    tb.process_file(&u, dirty, Some(2));
    assert!(tb.twin_tables.contains_key(u.as_str()), "trusted error state fell back to reference");
    assert_eq!(errors(&tb, &u).len(), 1, "expected exactly the one can't-unify error: {:?}", errors(&tb, &u));

    // The published diagnostics must match the reference engine's on the
    // same dirty source.
    let rb = backend(Engine::Reference);
    rb.process_file(&u, dirty, Some(2));
    assert_eq!(errors(&tb, &u), errors(&rb, &u), "twin-owned error diagnostics differ from reference");

    // Previous symbols survive the error kick: `good` still resolves for
    // hover (kept symbols — no partial merge deletes them).
    let probe = dirty.rfind("good").unwrap();
    let rope = ropey::Rope::from_str(dirty);
    let pos = elaboration_zoo_lsp::offset_to_position(probe, &rope).unwrap();
    assert!(tb.hover_at(&u, pos).is_some(), "previous symbol hover lost during error state");
}

/// A rename transient: kick 1 defines `foo`, kick 2 renames the def so the
/// still-present uses of `foo` become unresolved.  The stale global entry
/// belongs to *this* file, so the reference's local cxt drops it too — both
/// engines must report the error, and the twin must stay in charge (the
/// own-previous-symbols exclusion in the trust gate).
#[test]
fn twin_owns_rename_transient_unresolved_error() {
    let u = Url::parse("file:///twin_rename.typort").unwrap();
    let tb = backend(Engine::Twin);
    tb.process_file(&u, "def foo: Nat = zero\ndef use: Nat = succ foo\n", Some(1));
    assert!(errors(&tb, &u).is_empty());
    tb.process_file(&u, "def foo2: Nat = zero\ndef use: Nat = succ foo\n", Some(2));
    assert!(tb.twin_tables.contains_key(u.as_str()), "rename transient fell back");
    assert_eq!(errors(&tb, &u).len(), 1, "expected unresolved-foo error: {:?}", errors(&tb, &u));
    let rb = backend(Engine::Reference);
    rb.process_file(&u, "def foo2: Nat = zero\ndef use: Nat = succ foo\n", Some(2));
    assert_eq!(errors(&tb, &u), errors(&rb, &u), "rename transient diagnostics differ");
}

/// Error classes WITHOUT verified parity (trait-solving failures) still
/// fall back to the reference — the 18-utils implicit-hole divergence
/// surfaces as a spurious "solve trait failed", so the reference's
/// diagnostics must be the published ones.
#[test]
fn twin_falls_back_on_solve_trait_failure() {
    let u = Url::parse("file:///twin_solve.typort").unwrap();
    // `Add` has instances for Nat/String/UInt, not Bool.
    let src = "def x = true + false\n";
    let tb = backend(Engine::Twin);
    tb.process_file(&u, src, Some(1));
    assert!(!tb.twin_tables.contains_key(u.as_str()), "solve-trait failure must not stay twin-owned");
    let rb = backend(Engine::Reference);
    rb.process_file(&u, src, Some(1));
    assert_eq!(errors(&tb, &u), errors(&rb, &u), "fallback diagnostics differ from reference");
    assert!(!errors(&tb, &u).is_empty(), "expected a solve-trait error for Bool + Bool");
}

/// A twin decline used to be silent: the output channel named the engine only
/// at startup, so "is this file running on the twin or did it fall back?" could
/// not be answered at runtime.  Every decline must now leave one log line
/// naming the reason, and the reason must be queryable
/// ([`Backend::twin_fallback_reason`]) — that query is also what makes the
/// difference between "the twin got it right" and "the reference covered for
/// it" testable, which the diagnostic-only assertions could not distinguish.
#[test]
fn twin_fallback_is_logged_with_its_reason() {
    // (1) Unverified error class: the twin runs, then declines.
    let err_uri = Url::parse("file:///twin_fb_err.typort").unwrap();
    let tb = backend(Engine::Twin);
    tb.process_file(&err_uri, "def x = true + false\n", Some(1));
    let reason = tb.twin_fallback_reason(err_uri.as_str()).expect("fallback not recorded");
    assert!(reason.starts_with("untrusted-error"), "unexpected reason: {reason}");
    assert!(!tb.twin_tables.contains_key(err_uri.as_str()), "untrusted file stayed twin-owned");
    assert!(
        logs(&tb).iter().any(|l| l.contains("twin fallback:") && l.contains("untrusted-error")),
        "no fallback log line: {:?}",
        logs(&tb),
    );

    // (2) A twin-owned file records nothing and logs nothing.
    let ok_uri = Url::parse("file:///twin_fb_ok.typort").unwrap();
    let tb2 = backend(Engine::Twin);
    tb2.process_file(&ok_uri, "def f(n: Nat): Nat = n\n", Some(1));
    assert!(tb2.twin_tables.contains_key(ok_uri.as_str()), "clean file was not twin-owned");
    assert_eq!(tb2.twin_fallback_reason(ok_uri.as_str()), None);
    assert!(!logs(&tb2).iter().any(|l| l.contains("twin fallback:")));

    // (3) Cross-file gate: the reason names the import / the declared package.
    let provider = Url::parse("file:///twin_fb_a.typort").unwrap();
    let dependent = Url::parse("file:///twin_fb_b.typort").unwrap();
    let tb3 = backend(Engine::Twin);
    tb3.process_file(&provider, "package mylib\n\nstruct Tree {\n    h: Nat\n}\n", Some(1));
    tb3.process_file(&dependent, "import mylib._\n\ndef t: Tree = mylib.Tree.mk zero\n", Some(1));
    let prov_reason = tb3.twin_fallback_reason(provider.as_str()).expect("package fallback not recorded");
    assert!(
        prov_reason.starts_with("cross-file") && prov_reason.contains("mylib"),
        "unexpected package reason: {prov_reason}",
    );
    let dep_reason = tb3.twin_fallback_reason(dependent.as_str()).expect("import fallback not recorded");
    assert!(
        dep_reason.starts_with("cross-file") && dep_reason.contains("mylib"),
        "unexpected import reason: {dep_reason}",
    );

    // (4) A parse *diagnostic* is not a decline: the resilient parser still
    // yields partial decls, so the twin owns the file and publishes the parse
    // errors itself (both engines run the same parser call).  The only decline
    // on the parse front is `no-parse-result`, which needs
    // `parser_with_macros` to return `None` — unreachable, since the lexer
    // accepts any input.
    let bad_uri = Url::parse("file:///twin_fb_parse.typort").unwrap();
    let tb4 = backend(Engine::Twin);
    tb4.process_file(&bad_uri, "def a: Nat = zero\ndef b: Nat = succ ze", Some(1));
    assert!(tb4.twin_tables.contains_key(bad_uri.as_str()), "parse state should stay twin-owned");
    assert_eq!(tb4.twin_fallback_reason(bad_uri.as_str()), None);
    assert!(!logs(&tb4).iter().any(|l| l.contains("twin fallback:")));

    // (5) The reference engine never reports a fallback: the twin is not run.
    let rb = backend(Engine::Reference);
    rb.process_file(&err_uri, "def x = true + false\n", Some(1));
    assert_eq!(rb.twin_fallback_reason(err_uri.as_str()), None);
    assert!(!logs(&rb).iter().any(|l| l.contains("twin fallback:")));
}

/// A parse error (the most common typing state) no longer forces a
/// reference fallback: both engines run the identical parser call, so the
/// parse diagnostics are equal by construction, and elaboration of the
/// partial decls stays twin-owned when its errors are trusted.
#[test]
fn twin_owns_parse_error_state() {
    let u = Url::parse("file:///twin_parse.typort").unwrap();
    // Truncate mid-decl: the resilient parser yields partial decls plus a
    // parse error.
    let src = "def a: Nat = zero\ndef b: Nat = succ ze";
    let tb = backend(Engine::Twin);
    tb.process_file(&u, src, Some(1));
    let rb = backend(Engine::Reference);
    rb.process_file(&u, src, Some(1));
    assert_eq!(errors(&tb, &u), errors(&rb, &u), "parse-state diagnostics differ: twin={:?} ref={:?}", errors(&tb, &u), errors(&rb, &u));
}

/// A type error *inside* a module body breaks the module decl in both
/// engines (no close-check expected from either), so the HDL gate must not
/// distrust the file: the typing-inside-a-module state stays twin-owned.
#[test]
fn twin_owns_module_body_error_state() {
    let u = Url::parse("file:///twin_mod_err.typort").unwrap();
    let tb = backend_hdl(Engine::Twin);
    let src = "module broken {\n    input a = UInt[8]\n    let bad: Nat = true\n    output sum = UInt[8]\n    sum := a + a\n}\n";
    tb.process_file(&u, src, Some(1));
    let rb = backend_hdl(Engine::Reference);
    rb.process_file(&u, src, Some(1));
    assert_eq!(errors(&tb, &u), errors(&rb, &u), "module-body error diagnostics differ: twin={:?} ref={:?}", errors(&tb, &u), errors(&rb, &u));
}

/// Regression (2026-09): a *reduced* nat primop must unify against the same
/// term built from the surface syntax.  `n + succ m` reduces to
/// `succ (nat_add n m)` whose chain base is a `XCell::Decl("nat_add")`; the
/// surface `succ (n + m)` reaches the same shape through a different
/// allocation, so the two bare `Decl` bases are distinct cells and the
/// bit-equality shortcut misses.  The unifier used to hit the prim "opaque
/// leaf" interception (`is_prim_application` on the base stub) before the
/// bare `Decl/Decl` same-name arm and report a spurious `can't unify`
/// (examples/adder_proof.typort: every lemma application whose goal contains
/// `n + succ m`).  Reference arm order (`unification.rs`) puts `Decl/Decl`
/// first; the twin must match it.
#[test]
fn twin_unifies_reduced_nat_primop_against_surface_form() {
    let corpus: &[&str] = &[
        // Lemma application whose result type contains the reduced primop.
        "def t(n: Nat, m: Nat): Eq (n + (succ m)) (succ (n + m)) = add_succ_right(n, m)",
        // Same under a `let` ascription.
        "def t(n: Nat, m: Nat): Eq (n + (succ m)) (succ (n + m)) =\n    let h: Eq (n + (succ m)) (succ (n + m)) = add_succ_right(n, m);\n    h",
        // adder_proof.typort's `add_succ_succ` shape.
        "def t(a: Nat, b: Nat): Eq((a+1)+(b+1), a+b+2) = add_succ_left(a, b + 1)",
    ];
    for (i, src) in corpus.iter().enumerate() {
        let uri = Url::parse(&format!("file:///twin_primapply_{i}.typort")).unwrap();
        let tb = backend_hdl(Engine::Twin);
        tb.process_file(&uri, src, Some(1));
        let rb = backend_hdl(Engine::Reference);
        rb.process_file(&uri, src, Some(1));
        assert!(
            errors(&tb, &uri).is_empty(),
            "twin invented errors for:\n{src}\n-> {:?}",
            errors(&tb, &uri),
        );
        assert_eq!(
            errors(&tb, &uri), errors(&rb, &uri),
            "twin/reference error mismatch for:\n{src}",
        );
    }
}


/// Regression (2026-09): a **nested** `unify` must not clobber the *shared*
/// `unify_stack` of an enclosing `unify_iter`.  `Machine::unify` used to
/// `stack.clear()` on entry; the flex-solving path re-enters `unify` through
/// `solve_multi_trait_ref` (trait instance synthesis), so the outer call's
/// still-pending work items were silently dropped and the outer loop returned
/// `true` with metas unsolved.  Symptom: `Eq ?x ?y = Eq 7 7` solved only the
/// first parameter, then the enclosing `cong` goal failed with a spurious
/// `can't unify` (examples/theorem_proving.typort).
///
/// The trigger needs an **unannotated** inline lambda whose body contains a
/// *stuck* nat primop (`5 + x`: `nat_add`'s second argument is a variable) --
/// that is what forces trait synthesis (and hence the nested `unify`)
/// mid-comparison.  `x => x + 5` reduces to `succ^5 x`; `def g(x: Nat) = 5 + x`,
/// `(x: Nat) => 5 + x` and swapping the argument order (`myc4(proof, lambda)`)
/// all avoid it.
#[test]
fn twin_solves_implicits_around_nested_unify() {
    let corpus: &[&str] = &[
        "def t: Eq(5 + (0 + 7), 5 + 7) = cong(x => 5 + x, add_zero_left(7))",
        "def myc2[A, B, x: A, y: A](f: A -> B, e: Eq x y): Eq (f x) (f y) = cong(f, e)\ndef t: Eq(5 + (0 + 7), 5 + 7) = myc2(x => 5 + x, add_zero_left(7))",
        "def t: Eq((5 + 0) + (0 + 7), 5 + 7) =\n    calc {\n        (5 + 0) + (0 + 7) = 5 + (0 + 7) by cong(x => x + (0 + 7), add_zero_right(5))\n        5 + (0 + 7) = 5 + 7 by cong(x => 5 + x, add_zero_left(7))\n    }",
    ];
    for (i, src) in corpus.iter().enumerate() {
        let uri = Url::parse(&format!("file:///twin_nested_unify_{i}.typort")).unwrap();
        let tb = backend_hdl(Engine::Twin);
        tb.process_file(&uri, src, Some(1));
        let rb = backend_hdl(Engine::Reference);
        rb.process_file(&uri, src, Some(1));
        assert_eq!(
            errors(&tb, &uri), errors(&rb, &uri),
            "twin/reference error mismatch for:\n{src}",
        );
        assert!(
            errors(&tb, &uri).is_empty(),
            "twin invented errors for:\n{src}\n-> {:?}",
            errors(&tb, &uri),
        );
    }
}


/// (severity, message, start line/char) for ERROR + WARNING diagnostics,
/// sorted — `Information` (println rendering) is allowed to differ.
fn errwarn(b: &Arc<Backend<CapturingClient>>, uri: &Url) -> Vec<(String, String, u32, u32)> {
    let mut v: Vec<(String, String, u32, u32)> = b.client.diagnostics.lock().unwrap().iter()
        .filter(|(u, _, _)| u == uri)
        .flat_map(|(_, ds, _)| ds.iter())
        .filter(|d| {
            d.severity == Some(lsp_types::DiagnosticSeverity::ERROR)
                || d.severity == Some(lsp_types::DiagnosticSeverity::WARNING)
        })
        .map(|d| {
            (format!("{:?}", d.severity), d.message.clone(), d.range.start.line, d.range.start.character)
        })
        .collect();
    v.sort();
    v
}

/// Error-diagnostic parity over the **whole** `examples/` tree.  The HDL-only
/// test above misses the top-level proof examples, which is where the
/// nested-`unify` bug (`twin_solves_implicits_around_nested_unify`) surfaced:
/// adder_proof and theorem_proving used to grow spurious `can't unify`
/// errors.  `Information` diagnostics (println rendering) are still allowed to
/// differ; this pins the user-visible contract that the twin never *invents*
/// an error on a shipping example.
#[test]
fn twin_error_diagnostics_match_reference_on_all_examples() {
    fn collect(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {
        let Ok(rd) = std::fs::read_dir(dir) else { return };
        for e in rd.flatten() {
            let p = e.path();
            if p.is_dir() {
                collect(&p, out);
            } else if p.extension().map(|e| e == "typort").unwrap_or(false) {
                out.push(p);
            }
        }
    }
    let mut files = Vec::new();
    collect(std::path::Path::new("examples"), &mut files);
    files.sort();
    assert!(files.len() >= 30, "expected the examples tree, found {}", files.len());
    for (i, path) in files.iter().enumerate() {
        let Ok(src) = std::fs::read_to_string(path) else { continue };
        let name = path.to_string_lossy().replace('\\', "/");
        let uri = Url::parse(&format!("file:///ex_err_{i}.typort")).unwrap();
        let tb = backend_hdl(Engine::Twin);
        tb.process_file(&uri, &src, Some(1));
        let rb = backend_hdl(Engine::Reference);
        rb.process_file(&uri, &src, Some(1));
        assert!(
            errors(&tb, &uri).is_empty(),
            "twin invented errors on {name}: {:?}",
            errors(&tb, &uri),
        );
        assert!(
            errors(&rb, &uri).is_empty(),
            "reference errors on {name}: {:?}",
            errors(&rb, &uri),
        );
    }
}

/// Ownership + **warning** parity over the whole `examples/` tree.
///
/// Both corpus walks above pass trivially when the twin declines (the reference
/// publishes), which is how the HDL self-check gate's double-run on 23/25 stayed
/// invisible.  This test pins the two things they could not see:
///
/// 1. **Ownership**: every file is either twin-owned or has a *recorded*
///    fallback reason, and the fallback set is exactly the documented one — a
///    file silently changing engines fails here.
/// 2. **Warning parity** for twin-owned files: the existing walk compared ERROR
///    severities only, so a twin that *under-reports* HDL warnings (the failure
///    mode the conservative gate exists for) was invisible.  This is the safety
///    check that lets the gate stay conservative while its waste is removed by
///    the sticky demotion.
#[test]
fn twin_ownership_and_warning_parity_on_all_examples() {
    /// `(path suffix, expected reason class)`.  Editing this list is the
    /// deliberate act that accompanies any engine/gate change.
    const EXPECTED_FALLBACKS: &[(&str, &str)] = &[
        ("examples/alu.typort", "hdl-check-gate"),
        ("examples/hdl/18-utils.typort", "untrusted-error"),
        ("examples/hdl/23-verilog-compat.typort", "hdl-check-gate"),
        ("examples/hdl/25-verilog-reset.typort", "hdl-check-gate"),
    ];
    fn collect(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {
        let Ok(rd) = std::fs::read_dir(dir) else { return };
        for e in rd.flatten() {
            let p = e.path();
            if p.is_dir() {
                collect(&p, out);
            } else if p.extension().map(|e| e == "typort").unwrap_or(false) {
                out.push(p);
            }
        }
    }
    let mut files = Vec::new();
    collect(std::path::Path::new("examples"), &mut files);
    files.sort();
    assert!(files.len() >= 30, "expected the examples tree, found {}", files.len());
    let mut seen_fallbacks: Vec<String> = Vec::new();
    for (i, path) in files.iter().enumerate() {
        let Ok(src) = std::fs::read_to_string(path) else { continue };
        let name = path.to_string_lossy().replace('\\', "/");
        let uri = Url::parse(&format!("file:///ex_own_{i}.typort")).unwrap();
        let tb = backend_hdl(Engine::Twin);
        tb.process_file(&uri, &src, Some(1));
        let rb = backend_hdl(Engine::Reference);
        rb.process_file(&uri, &src, Some(1));

        let owned = tb.twin_tables.contains_key(uri.as_str());
        let reason = tb.twin_fallback_reason(uri.as_str());
        let expected = EXPECTED_FALLBACKS.iter().find(|(p, _)| name.ends_with(p));
        match expected {
            Some((_, class)) => {
                assert!(!owned, "{name} is twin-owned again — update EXPECTED_FALLBACKS");
                let reason = reason.unwrap_or_else(|| panic!("{name} fell back without a reason"));
                assert!(
                    reason.starts_with(class),
                    "{name}: expected reason class {class}, got {reason}",
                );
                seen_fallbacks.push(name.clone());
            }
            None => {
                assert!(owned, "{name} is no longer twin-owned (reason: {reason:?})");
                assert_eq!(reason, None, "{name}: owned but a fallback reason was recorded");
            }
        }
        // Whichever engine published, the user-visible ERROR+WARNING set must
        // match the reference exactly.
        assert_eq!(
            errwarn(&tb, &uri),
            errwarn(&rb, &uri),
            "ERROR/WARNING diagnostics diverged on {name}",
        );
    }
    assert_eq!(
        seen_fallbacks.len(),
        EXPECTED_FALLBACKS.len(),
        "expected fallbacks {:?}, saw {seen_fallbacks:?}",
        EXPECTED_FALLBACKS.iter().map(|(p, _)| *p).collect::<Vec<_>>(),
    );
}

/// The HDL self-check demotion is sticky: the gate's note is emitted once and
/// later kicks skip the twin pass entirely (its diagnostics are discarded
/// anyway).  Correctness is unaffected — the reference still publishes, and the
/// published set must equal a fresh reference run.
#[test]
fn twin_hdl_gate_distrust_is_sticky() {
    let src = std::fs::read_to_string("examples/hdl/23-verilog-compat.typort")
        .expect("examples/hdl/23-verilog-compat.typort");
    let uri = Url::parse("file:///twin_gate_sticky.typort").unwrap();
    let tb = backend_hdl(Engine::Twin);
    for k in 0..3 {
        tb.process_file(&uri, &src, Some(k));
        assert!(!tb.twin_tables.contains_key(uri.as_str()), "gate file became twin-owned on kick {k}");
        let reason = tb.twin_fallback_reason(uri.as_str()).expect("gate reason missing");
        assert!(reason.starts_with("hdl-check-gate"), "unexpected reason: {reason}");
    }
    let notes = logs(&tb)
        .iter()
        .filter(|l| l.contains("twin fallback:") && l.contains("hdl-check-gate"))
        .count();
    assert_eq!(notes, 1, "expected exactly one gate note, got: {:?}", logs(&tb));

    let rb = backend_hdl(Engine::Reference);
    rb.process_file(&uri, &src, Some(2));
    assert_eq!(errwarn(&tb, &uri), errwarn(&rb, &uri), "sticky-demoted file diverged from the reference");
}

