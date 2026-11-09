// P0-1: engine parity report harness (branch `p0-p1-baseline-cleanup`).
//
// Purpose (docs/optimal-design/FRAMEWORK.md §2 / D7 §8 P0): produce a
// machine-readable baseline of **reference vs twin** behaviour over the whole
// checked-in corpus.  This is a *reporting* test: divergences are recorded, not
// asserted.  Assertions only cover the harness contract:
//   * corpus found (> 0 files),
//   * both engines ran every file,
//   * no panic escaped a per-file run,
//   * JSON+MD reports were written.
//
// Run explicitly (it is `#[ignore]`d so the default `cargo test` stays fast):
//   CARGO_TARGET_DIR=C:/ezl-target cargo test --release \
//       --test engine_parity_report -- --ignored --nocapture
//
// Env knobs:
//   ENGINE_PARITY_OUT        report directory (default: CARGO_TARGET_DIR, else <repo>/target)
//   ENGINE_PARITY_MAX_FILES  process at most N corpus files (smoke runs)
//   ENGINE_PARITY_ONLY       substring filter on the repo-relative path
//   ENGINE_PARITY_MODES      "all" (default) | "core" | "hdl"

use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::time::Instant;

use elaboration_zoo_lsp::client::ClientLike;
use elaboration_zoo_lsp::{Backend, Engine};
use lsp_types::{Diagnostic, DiagnosticSeverity, MessageType, Url};
use serde_json::{json, Value};

// ---------------------------------------------------------------------------
// Capturing client (same shape as tests/twin_engine_tests.rs)
// ---------------------------------------------------------------------------

#[derive(Default)]
struct CapturingClient {
    diagnostics: Mutex<Vec<(Url, Vec<Diagnostic>, Option<i32>)>>,
    logs: Mutex<Vec<String>>,
}

impl ClientLike for CapturingClient {
    fn publish_diagnostics(&self, uri: Url, diagnostics: Vec<Diagnostic>, version: Option<i32>) {
        self.diagnostics.lock().unwrap().push((uri, diagnostics, version));
    }
    fn show_message(&self, _typ: MessageType, _message: String) {}
    fn log_message(&self, _typ: MessageType, message: String) {
        self.logs.lock().unwrap().push(message);
    }
}

type Handle = Arc<Backend<CapturingClient>>;

// ---------------------------------------------------------------------------
// Corpus discovery
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PreludeMode {    Core,
    Hdl,
}

impl PreludeMode {
    fn as_str(self) -> &'static str {
        match self {
            PreludeMode::Core => "core",
            PreludeMode::Hdl => "hdl",
        }
    }
}

#[derive(Debug, Clone)]
struct CorpusFile {
    abs: PathBuf,
    rel: String,
    group: &'static str,
    mode: PreludeMode,
}

fn walk_typort(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries = match std::fs::read_dir(dir) {
        Ok(e) => e,
        Err(_) => return,
    };
    let mut paths: Vec<PathBuf> = entries.filter_map(|e| e.ok()).map(|e| e.path()).collect();
    paths.sort();
    for p in paths {
        if p.is_dir() {
            walk_typort(&p, out);
        } else if p.extension().and_then(|s| s.to_str()) == Some("typort") {
            out.push(p);
        }
    }
}

/// HDL files need the full prelude; everything else uses `load_prelude_skip_hdl`.
/// The check is path-based first (`examples/hdl/`) and then content-based so
/// HDL snippets living at the example root are classified correctly.
fn looks_like_hdl(rel: &str, text: &str) -> bool {
    if rel.contains("/hdl/") || rel.contains("\\hdl\\") {
        return true;
    }
    const HDL_MARKERS: &[&str] = &[
        "module ",
        "UInt",
        "SInt",
        "Bits[",
        "regNext",
        "fsmNew",
        "blackbox",
        "streamM2s",
        "moduleTree",
        "#[derive(HdlEnum)]",
        "#[derive(Bundle)]",
    ];
    HDL_MARKERS.iter().any(|m| text.contains(m))
}

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn corpus_files() -> Vec<CorpusFile> {
    let root = repo_root();
    let mut raw: Vec<(PathBuf, &'static str)> = Vec::new();

    let mut examples = Vec::new();
    walk_typort(&root.join("examples"), &mut examples);
    for p in examples {
        raw.push((p, "examples"));
    }
    // tests/*.typort are fixture corpora (some are cross-file fixtures: the
    // report records the resulting `cross-file` fallback class).
    let tests_dir = root.join("tests");
    if let Ok(entries) = std::fs::read_dir(&tests_dir) {
        let mut paths: Vec<PathBuf> = entries
            .filter_map(|e| e.ok())
            .map(|e| e.path())
            .filter(|p| p.extension().and_then(|s| s.to_str()) == Some("typort"))
            .collect();
        paths.sort();
        for p in paths {
            raw.push((p, "tests"));
        }
    }

    let mut files: Vec<CorpusFile> = raw
        .into_iter()
        .filter_map(|(abs, group)| {
            let rel = abs
                .strip_prefix(&root)
                .map(|p| p.to_string_lossy().replace('\\', "/"))
                .unwrap_or_else(|_| abs.to_string_lossy().into_owned());
            let text = std::fs::read_to_string(&abs).ok()?;
            let mode = if looks_like_hdl(&rel, &text) {
                PreludeMode::Hdl
            } else {
                PreludeMode::Core
            };
            Some(CorpusFile { abs, rel, group, mode })
        })
        .collect();
    files.sort_by(|a, b| a.rel.cmp(&b.rel));

    if let Some(only) = std::env::var_os("ENGINE_PARITY_ONLY") {
        let only = only.to_string_lossy().into_owned();
        files.retain(|f| f.rel.contains(&only));
    }
    if let Some(modes) = std::env::var_os("ENGINE_PARITY_MODES") {
        match modes.to_string_lossy().as_ref() {
            "core" => files.retain(|f| f.mode == PreludeMode::Core),
            "hdl" => files.retain(|f| f.mode == PreludeMode::Hdl),
            _ => {}
        }
    }
    if let Ok(n) = std::env::var("ENGINE_PARITY_MAX_FILES") {
        if let Ok(n) = n.parse::<usize>() {
            files.truncate(n);
        }
    }
    files
}

fn prelude_files() -> Vec<String> {
    let root = repo_root();
    let mut out = Vec::new();
    walk_typort(&root.join("src").join("prelude"), &mut out);
    let mut rel: Vec<String> = out
        .into_iter()
        .map(|p| {
            p.strip_prefix(&root)
                .map(|x| x.to_string_lossy().replace('\\', "/"))
                .unwrap_or_else(|_| p.to_string_lossy().into_owned())
        })
        .collect();
    rel.sort();
    rel
}

// ---------------------------------------------------------------------------
// Running one engine over one prelude-mode group
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
struct DiagTuple {
    severity: String,
    message: String,
    line: u32,
    ch: u32,
    end_line: u32,
    end_ch: u32,
}

impl DiagTuple {
    fn from(d: &Diagnostic) -> Self {
        DiagTuple {
            severity: match d.severity {
                Some(DiagnosticSeverity::ERROR) => "ERROR",
                Some(DiagnosticSeverity::WARNING) => "WARNING",
                Some(DiagnosticSeverity::INFORMATION) => "INFORMATION",
                Some(DiagnosticSeverity::HINT) => "HINT",
                _ => "NONE",
            }
            .to_string(),
            message: d.message.clone(),
            line: d.range.start.line,
            ch: d.range.start.character,
            end_line: d.range.end.line,
            end_ch: d.range.end.character,
        }
    }
}

#[derive(Debug, Clone)]
struct EngineRun {
    rel: String,
    group: &'static str,
    mode: PreludeMode,
    engine: &'static str,
    /// true = this file was actually analysed by the twin (not a fallback).
    twin_owned: Option<bool>,
    twin_fallback: Option<String>,
    panicked: bool,
    panic_payload: Option<String>,
    elapsed_ms: f64,
    prelude_load_ms: f64,
    diags: Vec<DiagTuple>,
    error_count: usize,
    warning_count: usize,
    info_count: usize,
    hint_count: usize,
    /// non-empty when the backend emitted log lines for this URI
    fallback_log: Option<String>,
}

fn engine_name(e: Engine) -> &'static str {
    match e {
        Engine::Reference => "reference",
        Engine::Twin => "twin",
    }
}

fn last_diags(handle: &Handle, uri: &Url) -> Vec<Diagnostic> {
    // A panic inside a previous file can poison this mutex; recover instead of
    // panicking in the harness (the panic itself is recorded per file).
    let guard = match handle.client.diagnostics.lock() {
        Ok(g) => g,
        Err(p) => p.into_inner(),
    };
    guard
        .iter()
        .filter(|(u, _, _)| u.as_str() == uri.as_str())
        .last()
        .map(|(_, d, _)| d.clone())
        .unwrap_or_default()
}

fn last_fallback_log(handle: &Handle, uri: &Url) -> Option<String> {
    let guard = match handle.client.logs.lock() {
        Ok(g) => g,
        Err(p) => p.into_inner(),
    };
    guard
        .iter()
        .rev()
        .find(|l| l.contains(uri.as_str()) && l.contains("fallback"))
        .cloned()
}

fn panic_message(p: &Box<dyn std::any::Any + Send>) -> String {
    if let Some(s) = p.downcast_ref::<&str>() {
        (*s).to_string()
    } else if let Some(s) = p.downcast_ref::<String>() {
        s.clone()
    } else {
        "<non-string panic>".to_string()
    }
}

/// Create a backend for `engine`/`mode` and load the prelude; returns the load
/// time in ms plus a flag telling whether the prelude reported failure (the
/// reference path currently only eprintln!s it).
fn make_backend(engine: Engine, mode: PreludeMode) -> (Handle, f64) {
    let b = Backend::new_with_engine(CapturingClient::default(), engine);
    let t0 = Instant::now();
    match mode {
        PreludeMode::Core => b.load_prelude_skip_hdl(),
        PreludeMode::Hdl => b.load_prelude(),
    }
    let ms = t0.elapsed().as_secs_f64() * 1000.0;
    (b, ms)
}

fn run_group(engine: Engine, mode: PreludeMode, files: &[CorpusFile]) -> (Vec<EngineRun>, f64, u32, f64) {
    // Isolation policy: a **fresh Backend per file, for BOTH engines**.
    //
    // Reusing one backend across files is unsound in the current tree:
    //   * the reference engine's `remove_file` does not purge the trait
    //     solver's `head_index`/instance tables (stale indices -> OOB panic in
    //     `L13_namespace/unification.rs`);
    //   * the twin engine's internal reference-domain fallback/export path
    //     accumulates the same kind of global state, and its resident machine
    //     keeps trait-solver buckets across kicks (OOB in
    //     `bump_spine_iter/typeclass.rs`);
    //   * a panic poisons the backend's `Mutex<Infer>`/`Mutex<Cxt>`, which then
    //     panics on every later lock.
    // The price is one prelude load per file; that load time is recorded
    // separately so per-file elaboration times stay comparable.
    let mut runs = Vec::with_capacity(files.len());
    let mut total_load_ms = 0.0f64;
    let mut loads: u32 = 0;
    let mut first_load_ms: Option<f64> = None;
    for (idx, f) in files.iter().enumerate() {
        let uri = Url::from_file_path(&f.abs).unwrap_or_else(|_| {
            Url::parse(&format!("file:///p0/{}/{}", mode.as_str(), idx)).unwrap()
        });
        let text = match std::fs::read_to_string(&f.abs) {
            Ok(t) => t,
            Err(e) => {
                runs.push(EngineRun {
                    rel: f.rel.clone(),
                    group: f.group,
                    mode,
                    engine: engine_name(engine),
                    twin_owned: None,
                    twin_fallback: None,
                    panicked: true,
                    panic_payload: Some(format!("read error: {e}")),
                    elapsed_ms: 0.0,
                    prelude_load_ms: 0.0,
                    diags: Vec::new(),
                    error_count: 0,
                    warning_count: 0,
                    info_count: 0,
                    hint_count: 0,
                    fallback_log: None,
                });
                continue;
            }
        };
        // A panic while loading the prelude must not abort the report either.
        let loaded = catch_unwind(AssertUnwindSafe(|| make_backend(engine, mode)));
        let (handle, load_ms) = match loaded {
            Ok((h, ms)) => (Some(h), ms),
            Err(p) => (None, 0.0),
        };
        total_load_ms += load_ms;
        if first_load_ms.is_none() {
            first_load_ms = Some(load_ms);
        }
        loads += 1;
        let (mut panicked, mut panic_payload) = match &handle {
            None => (true, Some(format!("prelude load panic: {}", "see hook output"))),
            Some(_) => (false, None),
        };
        let mut diags: Vec<DiagTuple> = Vec::new();
        let (mut twin_owned, mut twin_fallback, mut fallback_log) = (None, None, None);
        let mut elapsed_ms = 0.0f64;
        if let Some(handle) = &handle {
            let t0 = Instant::now();
            let res = catch_unwind(AssertUnwindSafe(|| {
                handle.process_file(&uri, &text, Some(1));
            }));
            elapsed_ms = t0.elapsed().as_secs_f64() * 1000.0;
            if let Err(p) = res {
                panicked = true;
                panic_payload = Some(panic_message(&p));
            }

            diags = last_diags(handle, &uri).iter().map(DiagTuple::from).collect();
            if engine == Engine::Twin {
                let reason = handle.twin_fallback_reason(uri.as_str());
                twin_owned = Some(reason.is_none() && handle.twin_tables.contains_key(uri.as_str()));
                twin_fallback = reason;
            }
            fallback_log = last_fallback_log(handle, &uri);
            // Per-URI tables are dropped with the backend, no cleanup needed.
        }
        let count = |sev: &str| diags.iter().filter(|d| d.severity == sev).count();
        runs.push(EngineRun {
            rel: f.rel.clone(),
            group: f.group,
            mode,
            engine: engine_name(engine),
            twin_owned,
            twin_fallback,
            panicked,
            panic_payload,
            elapsed_ms,
            prelude_load_ms: load_ms,
            error_count: count("ERROR"),
            warning_count: count("WARNING"),
            info_count: count("INFORMATION"),
            hint_count: count("HINT"),
            diags,
            fallback_log,
        });
        drop(handle);
    }
    (runs, total_load_ms, loads, first_load_ms.unwrap_or(0.0))
}
// ---------------------------------------------------------------------------
// Comparison + report rendering
// ---------------------------------------------------------------------------

fn compare(ref_run: &EngineRun, twin_run: &EngineRun) -> Value {
    let n = ref_run.diags.len().max(twin_run.diags.len());
    let mut diff_indices = Vec::new();
    for i in 0..n {
        let a = ref_run.diags.get(i);
        let b = twin_run.diags.get(i);
        if a.map(|d| (&d.severity, &d.message, d.line, d.ch, d.end_line, d.end_ch))
            != b.map(|d| (&d.severity, &d.message, d.line, d.ch, d.end_line, d.end_ch))
        {
            diff_indices.push(i);
        }
    }
    let msgs_equal = {
        let a: Vec<&str> = ref_run.diags.iter().map(|d| d.message.as_str()).collect();
        let b: Vec<&str> = twin_run.diags.iter().map(|d| d.message.as_str()).collect();
        a == b
    };
    let verdict_equal = (ref_run.error_count == 0) == (twin_run.error_count == 0);
    let counts_equal = ref_run.error_count == twin_run.error_count
        && ref_run.warning_count == twin_run.warning_count
        && ref_run.info_count == twin_run.info_count
        && ref_run.hint_count == twin_run.hint_count;

    let detail: Vec<Value> = diff_indices
        .iter()
        .take(8)
        .map(|&i| {
            json!({
                "index": i,
                "reference": ref_run.diags.get(i).map(|d| json!([d.severity, d.message, d.line, d.ch])),
                "twin": twin_run.diags.get(i).map(|d| json!([d.severity, d.message, d.line, d.ch])),
            })
        })
        .collect();

    json!({
        "verdict_equal": verdict_equal,
        "severity_counts_equal": counts_equal,
        "diagnostics_exact_equal": diff_indices.is_empty(),
        "messages_equal": msgs_equal,
        "diag_diff_count": diff_indices.len(),
        "diag_count": { "reference": ref_run.diags.len(), "twin": twin_run.diags.len() },
        "diff_detail": detail,
    })
}

fn run_to_json(r: &EngineRun) -> Value {
    json!({
        "engine": r.engine,
        "group": r.group,
        "prelude_mode": r.mode.as_str(),
        "twin_owned": r.twin_owned,
        "twin_fallback": r.twin_fallback,
        "fallback_log": r.fallback_log,
        "panicked": r.panicked,
        "panic_payload": r.panic_payload,
        "elapsed_ms": r.elapsed_ms,
        "prelude_load_ms": r.prelude_load_ms,
        "error_count": r.error_count,
        "warning_count": r.warning_count,
        "information_count": r.info_count,
        "hint_count": r.hint_count,
        "diag_count": r.diags.len(),
        "diagnostics": r.diags.iter().map(|d| json!({
            "severity": d.severity,
            "message": d.message,
            "start": [d.line, d.ch],
            "end": [d.end_line, d.end_ch],
        })).collect::<Vec<_>>(),
    })
}

fn read_git_head() -> (Option<String>, Option<String>) {
    let root = repo_root();
    let head = std::fs::read_to_string(root.join(".git").join("HEAD")).ok();
    match head {
        Some(h) => {
            let h = h.trim();
            if let Some(rest) = h.strip_prefix("ref: ") {
                let branch = rest.rsplit('/').next().map(|s| s.to_string());
                let hash = std::fs::read_to_string(root.join(".git").join(rest))
                    .ok()
                    .map(|s| s.trim().to_string());
                (branch, hash)
            } else {
                (None, Some(h.to_string()))
            }
        }
        None => (None, None),
    }
}

fn out_dir() -> PathBuf {
    let root = repo_root();
    let p = std::env::var_os("ENGINE_PARITY_OUT")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("CARGO_TARGET_DIR").map(PathBuf::from))
        .unwrap_or_else(|| root.join("target"));
    if p.is_absolute() {
        p
    } else {
        root.join(p)
    }
}

fn render_md(
    meta: &Value,
    rows: &[Value],
    summary: &Value,
    prelude_baseline: &Value,
    panics: &[String],
    slow: &[Value],
) -> String {
    let mut s = String::new();
    s.push_str("# P0 engine parity report (reference vs twin)\n\n");
    s.push_str(&format!(
        "Generated by `tests/engine_parity_report.rs` (P0-1). Branch: `{}`, HEAD: `{}`.\n\n",
        meta["branch"].as_str().unwrap_or("?"),
        meta["head"].as_str().unwrap_or("?")
    ));
    s.push_str("## Corpus\n\n");
    s.push_str(&format!(
        "- user files: **{}** (examples {} + tests {}); prelude `.typort`: {} not run as user files\n",
        summary["files"].as_u64().unwrap_or(0),
        summary["files_examples"].as_u64().unwrap_or(0),
        summary["files_tests"].as_u64().unwrap_or(0),
        summary["prelude_files"].as_u64().unwrap_or(0),
    ));
    s.push_str(&format!(
        "- twin-owned: **{}**, fallbacks: {}, panics: {}\n",
        summary["twin_owned"].as_u64().unwrap_or(0),
        summary["twin_fallback"].as_u64().unwrap_or(0),
        summary["panics"].as_u64().unwrap_or(0),
    ));
    s.push_str(&format!(
        "- verdict equal: **{}**, diagnostics exact equal: **{}**, differing files: {}\n\n",
        summary["verdict_equal"].as_u64().unwrap_or(0),
        summary["diagnostics_exact_equal"].as_u64().unwrap_or(0),
        summary["divergent_files"].as_u64().unwrap_or(0),
    ));
    s.push_str("## Per-file\n\n");
    s.push_str("| file | mode | twin-owned | ref E/W/I | twin E/W/I | verdict | diag exact | t_ref ms | t_twin ms |\n");
    s.push_str("|---|---|---|---|---|---|---|---:|---:|\n");
    for r in rows {
        let owned = r["twin_owned"]
            .as_bool()
            .map(|b| if b { "yes" } else { "no (fallback)" })
            .unwrap_or("-");
        s.push_str(&format!(
            "| `{}` | {} | {} | {}/{}/{} | {}/{}/{} | {} | {} | {:.1} | {:.1} |\n",
            r["file"].as_str().unwrap_or(""),
            r["prelude_mode"].as_str().unwrap_or(""),
            owned,
            r["reference"]["error_count"].as_u64().unwrap_or(0),
            r["reference"]["warning_count"].as_u64().unwrap_or(0),
            r["reference"]["information_count"].as_u64().unwrap_or(0),
            r["twin"]["error_count"].as_u64().unwrap_or(0),
            r["twin"]["warning_count"].as_u64().unwrap_or(0),
            r["twin"]["information_count"].as_u64().unwrap_or(0),
            if r["parity"]["verdict_equal"].as_bool().unwrap_or(false) { "=" } else { "DIFF" },
            if r["parity"]["diagnostics_exact_equal"].as_bool().unwrap_or(false) { "=" } else { "DIFF" },
            r["reference"]["elapsed_ms"].as_f64().unwrap_or(0.0),
            r["twin"]["elapsed_ms"].as_f64().unwrap_or(0.0),
        ));
    }
    s.push_str("\n## Divergences (verdict or diagnostics)\n\n");
    let mut any = false;
    for r in rows {
        let v_ok = r["parity"]["verdict_equal"].as_bool().unwrap_or(false);
        let d_ok = r["parity"]["diagnostics_exact_equal"].as_bool().unwrap_or(false);
        if v_ok && d_ok {
            continue;
        }
        any = true;
        s.push_str(&format!(
            "### `{}`\n- verdict_equal={}, diag_exact={}, diag_diff={} (ref {} / twin {} diags)\n",
            r["file"].as_str().unwrap_or(""),
            v_ok,
            d_ok,
            r["parity"]["diag_diff_count"].as_u64().unwrap_or(0),
            r["parity"]["diag_count"]["reference"].as_u64().unwrap_or(0),
            r["parity"]["diag_count"]["twin"].as_u64().unwrap_or(0),
        ));
        if let Some(details) = r["parity"]["diff_detail"].as_array() {
            for d in details {
                s.push_str(&format!("  - {}\n", d));
            }
        }
    }
    if !any {
        s.push_str("_none_\n");
    }
    s.push_str("\n## Prelude load baseline (fresh backend per file; cache after first)\n\n");
    s.push_str("| engine | mode | loads | total ms | mean ms | first ms | files |\n");
    s.push_str("|---|---|---:|---:|---:|---:|---:|\n");
    if let Some(bs) = prelude_baseline.as_array() {
        for b in bs {
            s.push_str(&format!(
                "| {} | {} | {} | {:.1} | {:.1} | {:.1} | {} |\n",
                b["engine"].as_str().unwrap_or(""),
                b["mode"].as_str().unwrap_or(""),
                b["loads"].as_u64().unwrap_or(0),
                b["total_load_ms"].as_f64().unwrap_or(0.0),
                b["mean_load_ms"].as_f64().unwrap_or(0.0),
                b["first_load_ms"].as_f64().unwrap_or(0.0),
                b["files"].as_u64().unwrap_or(0),
            ));
        }
    }
    s.push_str("\n## Known panics (whitelisted; root cause TODO P2)\n\n");
    if panics.is_empty() {
        s.push_str("_none_\n");
    } else {
        s.push_str("| file | note |\n|---|---|\n");
        for p in panics {
            s.push_str(&format!(
                "| `{}` | panic recorded by P0 parity harness (see P0 report) |\n",
                p
            ));
        }
    }
    s.push_str("\n## Slow files (>5s on either engine)\n\n");
    if slow.is_empty() {
        s.push_str("_none_\n");
    } else {
        for r in slow {
            s.push_str(&format!(
                "- `{}`: ref {:.1} ms / twin {:.1} ms\n",
                r["file"].as_str().unwrap_or(""),
                r["reference_ms"].as_f64().unwrap_or(0.0),
                r["twin_ms"].as_f64().unwrap_or(0.0),
            ));
        }
    }
    s.push_str("\n## Fallback classes\n\n");
    if let Some(classes) = summary["fallback_classes"].as_object() {
        for (k, v) in classes {
            s.push_str(&format!("- `{k}`: {v}\n"));
        }
    }
    s.push_str("\n### Fallback files\n\n");
    let mut any_fb = false;
    for r in rows {
        if let Some(fb) = r["twin_fallback"].as_str() {
            any_fb = true;
            s.push_str(&format!("- `{}` -> `{}`\n", r["file"].as_str().unwrap_or(""), fb));
        }
    }
    if !any_fb {
        s.push_str("_none_\n");
    }
    s.push_str("\n## Limitations\n\n");
    s.push_str("- Both engines use a **fresh `Backend` per file** (shared backends leak trait-solver instance indices across files: reference `unification.rs` and twin `typeclass.rs` both hit OOB panics in smoke runs; a panic also poisons the backend Mutexes). Prelude load time is therefore paid per file and is reported separately (`prelude_load_ms`). Cross-file fixtures report `cross-file` fallbacks.\n");
    s.push_str("- No hard per-file timeout: elapsed is recorded and files > 5000 ms are flagged `slow` in JSON; a hang would need an outer timeout (`tools/run_engine_parity.sh` does not add one today).\n");
    s.push_str("- Diagnostics compare the last publish per URI (severity/message/range); Ok-output byte parity is not captured here (it is covered by the parity suites).\n");
    s
}

// ---------------------------------------------------------------------------
// The report test
// ---------------------------------------------------------------------------

#[test]
#[ignore = "P0 engine parity report; run explicitly via tools/run_engine_parity.sh"]
fn engine_parity_report() {
    let files = corpus_files();
    assert!(!files.is_empty(), "corpus is empty — check examples/ and tests/*.typort");
    let prelude = prelude_files();
    let t_start = Instant::now();

    let mut core_files: Vec<CorpusFile> = Vec::new();
    let mut hdl_files: Vec<CorpusFile> = Vec::new();
    for f in &files {
        match f.mode {
            PreludeMode::Core => core_files.push(f.clone()),
            PreludeMode::Hdl => hdl_files.push(f.clone()),
        }
    }

    // Reference first, then twin, per mode group; backends are dropped between
    // groups so only one resident prelude is alive at a time.
    let (ref_core, ref_core_ms, ref_core_loads, ref_core_first) = if core_files.is_empty() {
        (Vec::new(), 0.0, 0, 0.0)
    } else {
        run_group(Engine::Reference, PreludeMode::Core, &core_files)
    };
    let (twin_core, twin_core_ms, twin_core_loads, twin_core_first) = if core_files.is_empty() {
        (Vec::new(), 0.0, 0, 0.0)
    } else {
        run_group(Engine::Twin, PreludeMode::Core, &core_files)
    };
    let (ref_hdl, ref_hdl_ms, ref_hdl_loads, ref_hdl_first) = if hdl_files.is_empty() {
        (Vec::new(), 0.0, 0, 0.0)
    } else {
        run_group(Engine::Reference, PreludeMode::Hdl, &hdl_files)
    };
    let (twin_hdl, twin_hdl_ms, twin_hdl_loads, twin_hdl_first) = if hdl_files.is_empty() {
        (Vec::new(), 0.0, 0, 0.0)
    } else {
        run_group(Engine::Twin, PreludeMode::Hdl, &hdl_files)
    };

    let mean = |total: f64, loads: u32| if loads > 0 { total / loads as f64 } else { 0.0 };
    let prelude_baseline = json!([
        {"engine": "reference", "mode": "core", "total_load_ms": ref_core_ms, "loads": ref_core_loads, "mean_load_ms": mean(ref_core_ms, ref_core_loads), "first_load_ms": ref_core_first, "files": core_files.len()},
        {"engine": "twin", "mode": "core", "total_load_ms": twin_core_ms, "loads": twin_core_loads, "mean_load_ms": mean(twin_core_ms, twin_core_loads), "first_load_ms": twin_core_first, "files": core_files.len()},
        {"engine": "reference", "mode": "hdl", "total_load_ms": ref_hdl_ms, "loads": ref_hdl_loads, "mean_load_ms": mean(ref_hdl_ms, ref_hdl_loads), "first_load_ms": ref_hdl_first, "files": hdl_files.len()},
        {"engine": "twin", "mode": "hdl", "total_load_ms": twin_hdl_ms, "loads": twin_hdl_loads, "mean_load_ms": mean(twin_hdl_ms, twin_hdl_loads), "first_load_ms": twin_hdl_first, "files": hdl_files.len()},
    ]);

    use std::collections::BTreeMap;
    let mut ref_map: BTreeMap<String, EngineRun> = BTreeMap::new();
    for r in ref_core.into_iter().chain(ref_hdl) {
        ref_map.insert(r.rel.clone(), r);
    }
    let mut twin_map: BTreeMap<String, EngineRun> = BTreeMap::new();
    for r in twin_core.into_iter().chain(twin_hdl) {
        twin_map.insert(r.rel.clone(), r);
    }

    let mut rows: Vec<Value> = Vec::new();
    let mut panics: Vec<String> = Vec::new();
    let mut panics_twin: Vec<String> = Vec::new();
    let mut fallback_classes: BTreeMap<String, u64> = BTreeMap::new();
    let mut twin_owned_n = 0u64;
    let mut verdict_equal_n = 0u64;
    let mut diag_equal_n = 0u64;
    let mut divergent_n = 0u64;
    let mut slow: Vec<Value> = Vec::new();
    let mut files_examples = 0u64;
    let mut files_tests = 0u64;
    let mut total_ref_ms = 0.0f64;
    let mut total_twin_ms = 0.0f64;

    for f in &files {
        let rr = ref_map.get(&f.rel);
        let tr = twin_map.get(&f.rel);
        let (Some(rr), Some(tr)) = (rr, tr) else {
            rows.push(json!({
                "file": f.rel, "group": f.group, "prelude_mode": f.mode.as_str(),
                "error": "missing run record",
            }));
            continue;
        };
        if rr.panicked {
            panics.push(f.rel.clone());
        }
        if tr.panicked {
            panics.push(format!("{} (twin)", f.rel));
            panics_twin.push(f.rel.clone());
        }
        match f.group {
            "tests" => files_tests += 1,
            _ => files_examples += 1,
        }
        if let Some(owned) = tr.twin_owned {
            if owned {
                twin_owned_n += 1;
            }
        }
        if let Some(class) = &tr.twin_fallback {
            let key = class.split_whitespace().next().unwrap_or(class).to_string();
            *fallback_classes.entry(key).or_insert(0) += 1;
        }
        let parity = compare(rr, tr);
        let v_ok = parity["verdict_equal"].as_bool().unwrap_or(false);
        let d_ok = parity["diagnostics_exact_equal"].as_bool().unwrap_or(false);
        if v_ok {
            verdict_equal_n += 1;
        }
        if d_ok {
            diag_equal_n += 1;
        }
        if !v_ok || !d_ok {
            divergent_n += 1;
        }
        total_ref_ms += rr.elapsed_ms;
        total_twin_ms += tr.elapsed_ms;
        if rr.elapsed_ms > 5000.0 || tr.elapsed_ms > 5000.0 {
            slow.push(json!({"file": f.rel, "reference_ms": rr.elapsed_ms, "twin_ms": tr.elapsed_ms}));
        }
        rows.push(json!({
            "file": f.rel,
            "group": f.group,
            "prelude_mode": f.mode.as_str(),
            "twin_owned": tr.twin_owned,
            "twin_fallback": tr.twin_fallback,
            "reference": run_to_json(rr),
            "twin": run_to_json(tr),
            "parity": parity,
        }));
    }

    let summary = json!({
        "files": files.len(),
        "files_examples": files_examples,
        "files_tests": files_tests,
        "prelude_files": prelude.len(),
        "twin_owned": twin_owned_n,
        "twin_fallback": files.len() as u64 - twin_owned_n,
        "fallback_classes": fallback_classes,
        "panics": panics.len(),
        "verdict_equal": verdict_equal_n,
        "diagnostics_exact_equal": diag_equal_n,
        "divergent_files": divergent_n,
        "total_reference_ms": total_ref_ms,
        "total_twin_ms": total_twin_ms,
        "wall_ms": t_start.elapsed().as_secs_f64() * 1000.0,
    });

    let (branch, head) = read_git_head();
    let meta = json!({
        "branch": branch.unwrap_or_else(|| "unknown".into()),
        "head": head.unwrap_or_else(|| "unknown".into()),
        "generated_at_unix": std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0),
        "profile": if cfg!(debug_assertions) { "debug" } else { "release" },
        "note": "P0-1 engine parity baseline report; divergences are recorded, not asserted",
    });

    let report = json!({
        "meta": meta,
        "corpus": {
            "files": files.iter().map(|f| json!({
                "path": f.rel, "group": f.group, "prelude_mode": f.mode.as_str()
            })).collect::<Vec<_>>(),
            "prelude_files": prelude,
        },
        "prelude_baseline": prelude_baseline,
        "runs": rows,
        "summary": summary,
        "panics": panics,
        "slow_files": slow,
    });

    let dir = out_dir();
    std::fs::create_dir_all(&dir).expect("create report dir");
    let json_path = dir.join("engine-parity-report.json");
    let md_path = dir.join("engine-parity-report.md");
    std::fs::write(&json_path, serde_json::to_string_pretty(&report).unwrap())
        .expect("write json report");
    let md = render_md(&meta, &rows, &summary, &prelude_baseline, &panics, &slow);
    std::fs::write(&md_path, md).expect("write md report");

    println!("\n===== engine parity report (P0-1) =====");
    println!("branch={} head={}", meta["branch"], meta["head"]);
    println!(
        "corpus: {} files (examples {}, tests {}) + {} prelude files",
        summary["files"], summary["files_examples"], summary["files_tests"], summary["prelude_files"]
    );
    println!(
        "twin-owned: {} / {} (divergent {}), verdict-equal {}, diag-exact-equal {}",
        summary["twin_owned"], summary["files"], summary["divergent_files"],
        summary["verdict_equal"], summary["diagnostics_exact_equal"]
    );
    println!(
        "panics: {}; wall {:.2}s; ref sum {:.1}ms; twin sum {:.1}ms",
        summary["panics"],
        t_start.elapsed().as_secs_f64(),
        total_ref_ms,
        total_twin_ms
    );
    println!("report json: {}", json_path.display());
    println!("report md:   {}", md_path.display());
    if !panics.is_empty() {
        println!("panic files: {panics:?}");
    }
    println!("=====================================\n");

    // Harness contract assertions (divergences are *not* asserted).
    assert!(files.len() > 0, "corpus empty");
    assert!(
        rows.len() == files.len(),
        "missing rows: {} vs {}",
        rows.len(),
        files.len()
    );
    // P0 fixed the only known panic (stale trait head_index after trait
    // redefinition; pins in tests/p0_known_bug_pins.rs).  Keep the whitelist
    // mechanism EMPTY: any new panic is a real regression and must fail.
    const KNOWN_PANICS: &[&str] = &[];
    let unknown: Vec<&String> = panics
        .iter()
        .filter(|p| {
            let base = p.strip_suffix(" (twin)").unwrap_or(p.as_str());
            !KNOWN_PANICS.contains(&base)
        })
        .collect();
    assert!(
        unknown.is_empty(),
        "unexpected panic (add to KNOWN_PANICS only with a linked bug): {unknown:?}"
    );
    assert!(json_path.exists(), "json report not written");
    assert!(md_path.exists(), "md report not written");
}
