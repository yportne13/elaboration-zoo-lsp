// Ignored-by-default measurement of the LSP per-kick cost under each engine
// (stage 3a seed-cost baseline requested by docs/lsp-twin-wiring-2026-09.md).
//
// Run explicitly in release:
//   cargo test --release --test twin_engine_bench -- --ignored --nocapture
//
// Findings (09-hierarchy, release):
// - Stage 3a (whole-prelude replay per kick): twin ~3285 ms vs reference
//   ~328 ms -> ~10x SLOWER.  The ~2.8 s prelude replay dominated.
// - Stage 3b (resident checkpoint): twin ~399 ms vs reference ~325 ms.
//   Seed tax gone, but the twin pass was still *additive* (reference ran for
//   diagnostics/cross-file state, then twin observation added ~74 ms).
// - Stage 4 (twin takeover, current): twin ~97 ms vs reference ~335 ms ->
//   ~3.4x FASTER.  The twin now owns diagnostics + observation + the global
//   decl merge for files with no imports (the HDL workload), so the
//   reference per-decl infer loop (~280 ms) is skipped entirely.  Files that
//   import a project namespace, or declare one, still fall back.
// - Error states (2026-09-14 gate narrowing): twin-owned for parity-verified
//   error classes (parse errors identical by construction, can't-unify /
//   genuinely-unresolved names by corpus) -> error-state kick ~98 ms, same
//   as the clean state; before, any twin error forced a full reference
//   fallback after the twin pass (~450 ms, ~30% worse than pure reference).
// See the wiring doc's 2026-09-10/09-14 progress logs.

use std::sync::Arc;
use std::time::Instant;

use elaboration_zoo_lsp::client::ClientLike;
use elaboration_zoo_lsp::{Backend, Engine};
use lsp_types::{MessageType, Url};

#[derive(Default)]
struct SilentClient;

impl ClientLike for SilentClient {
    fn publish_diagnostics(&self, _u: Url, _d: Vec<lsp_types::Diagnostic>, _v: Option<i32>) {}
    fn show_message(&self, _t: MessageType, _m: String) {}
    fn log_message(&self, _t: MessageType, _m: String) {}
}

#[test]
#[ignore = "manual perf measurement; run with --release --ignored --nocapture"]
fn bench_error_state_kick_cost_by_engine() {
    // Typing-period state: the file carries a `can't unify` ERROR in a def
    // while its modules stay well-formed (the common "error elsewhere in a
    // module file" shape).  Before the 2026-09-14 gate narrowing, any twin
    // error forced a full reference fallback *after* the twin pass already
    // ran — double pay, ~30% worse than the pure reference engine.
    let base = std::fs::read_to_string("examples/hdl/09-hierarchy.typort").unwrap();
    let src = format!("{base}\ndef benchErrInject(): Nat = true\n");
    for eng in [Engine::Reference, Engine::Twin] {
        let b: Arc<Backend<SilentClient>> = Backend::new_with_engine(SilentClient, eng);
        b.load_prelude();
        let uri = Url::parse("file:///bench_err.typort").unwrap();
        let t0 = Instant::now();
        b.process_file(&uri, &src, Some(0));
        let warmup = t0.elapsed().as_secs_f64() * 1000.0;
        let mut best = f64::MAX;
        let mut total = 0.0;
        let kicks = 5usize;
        for i in 0..kicks {
            let t0 = Instant::now();
            b.process_file(&uri, &src, Some(i as i32 + 1));
            let dt = t0.elapsed().as_secs_f64() * 1000.0;
            total += dt;
            if dt < best { best = dt; }
        }
        println!(
            "[BENCH-ERR] {eng:?}: warmup={warmup:.0} ms | steady-state min={best:.0} avg={:.0} ms/kick ({kicks})",
            total / kicks as f64,
        );
    }
}

#[test]
#[ignore = "manual perf measurement; run with --release --ignored --nocapture"]
fn bench_kick_cost_by_engine() {
    let src = std::fs::read_to_string("examples/hdl/09-hierarchy.typort").unwrap();
    // ONE Backend per engine, an explicit warm-up kick (which pays the
    // engine's one-time setup: the twin's resident prelude prime), then
    // steady-state kicks.  Measuring min over fresh Backends would hide the
    // twin's prime behind the thread-local resident (reused across the loop).
    for eng in [Engine::Reference, Engine::Twin] {
        let b: Arc<Backend<SilentClient>> = Backend::new_with_engine(SilentClient, eng);
        b.load_prelude();
        let uri = Url::parse("file:///bench.typort").unwrap();
        let t0 = Instant::now();
        b.process_file(&uri, &src, Some(0));
        let warmup = t0.elapsed().as_secs_f64() * 1000.0;
        let mut best = f64::MAX;
        let mut total = 0.0;
        let kicks = 5usize;
        for i in 0..kicks {
            let t0 = Instant::now();
            b.process_file(&uri, &src, Some(i as i32 + 1));
            let dt = t0.elapsed().as_secs_f64() * 1000.0;
            total += dt;
            if dt < best { best = dt; }
        }
        println!(
            "[BENCH] {eng:?}: warmup(first kick incl. setup)={warmup:.0} ms | steady-state min={best:.0} avg={:.0} ms/kick ({kicks})",
            total / kicks as f64,
        );
    }
}

/// Per-kick breakdown for `examples/adder_proof.typort`, both engines.
///
/// Added 2026-09-23 because the per-file sweep found this file at **0.36×**
/// (twin 1607 ms vs reference 573 ms) while every other proof/HDL file is
/// 1.5–4.9× *faster* on the twin.  Two things stand out in the sweep and this
/// bench prints what the sweep's min-only output hides:
///
/// - `min` was *larger* than `first` (1607 vs 1450 ms) — the twin gets slower
///   across kicks on this file, which is the signature of the resident
///   compaction / re-prime path rather than of elaboration cost;
/// - the 2026-09-14 wiring doc recorded adder_proof at ~278 ms/kick (313–475 ms
///   after the in-place-compaction fix), so this is a ~6× regression since.
///
/// `TYPORT_KICK_PROBE=1` additionally prints the per-kick
/// `restore(clones)=…ms loop+export=…ms` split (measured 225 ms + 1380 ms).
#[test]
#[ignore = "manual perf measurement; run with --release --ignored --nocapture"]
fn bench_adder_proof_kick_cost_by_engine() {
    let src = std::fs::read_to_string("examples/adder_proof.typort").unwrap();
    let kicks = 8usize;
    // 两种 prelude 都测：`hdl`（默认）与 `core`（`load_prelude_skip_hdl`）。
    // 对照价值——2026-09-24 实测同一份源码、同一天平下，孪生对常驻规模敏感
    // 2.07×（975→2019ms 采样口径）而参考版只 1.09×（484→527ms），且 core 下
    // 孪生已经是参考的 2.0×。这组数字是"常驻工作集 ⇒ 单位操作成本"的证据，
    // 也是"孪生还有独立于 prelude 规模的基础 2×"的证据。
    for core_only in [false, true] {
        for eng in [Engine::Reference, Engine::Twin] {
            let b: Arc<Backend<SilentClient>> = Backend::new_with_engine(SilentClient, eng);
            if core_only {
                b.load_prelude_skip_hdl();
            } else {
                b.load_prelude();
            }
            let uri = Url::parse("file:///bench_adder.typort").unwrap();
            let t0 = Instant::now();
            b.process_file(&uri, &src, Some(0));
            let first = t0.elapsed().as_secs_f64() * 1000.0;
            let mut times = Vec::with_capacity(kicks);
            for k in 0..kicks {
                let t0 = Instant::now();
                b.process_file(&uri, &src, Some(k as i32 + 1));
                times.push(t0.elapsed().as_secs_f64() * 1000.0);
            }
            let min = times.iter().cloned().fold(f64::MAX, f64::min);
            let max = times.iter().cloned().fold(0.0f64, f64::max);
            let prelude = if core_only { "core" } else { "hdl" };
            println!(
                "[BENCH-ADDER] {prelude:>4} {eng:?}: first={first:.0} ms | kicks=[{}] min={min:.0} max={max:.0}",
                times.iter().map(|t| format!("{t:.0}")).collect::<Vec<_>>().join(", "),
            );
        }
    }
}

/// Recursively collect every `.typort` under `dir`, sorted for stable output.
fn collect_typort(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {    let Ok(entries) = std::fs::read_dir(dir) else { return };
    for entry in entries.flatten() {
        let p = entry.path();
        if p.is_dir() {
            collect_typort(&p, out);
        } else if p.extension().map(|e| e == "typort").unwrap_or(false) {
            out.push(p);
        }
    }
}

/// Per-file LSP kick cost for every `examples/**/*.typort`, both engines.
///
/// One fresh `Backend` per (file, engine) so no symbol from a previous file
/// pollutes the next (the examples deliberately reuse names like `add`).  The
/// twin's resident prelude is thread-local and reused, and the reference
/// prelude is the cached clone, so neither engine pays its prelude load more
/// than once per thread.  `first` is the opening kick (didOpen, includes any
/// per-file setup); `min` is the best of `kicks` steady-state edits.
#[test]
#[ignore = "manual perf measurement; run with --release --ignored --nocapture"]
fn bench_examples_per_file_by_engine() {
    let mut files = Vec::new();
    collect_typort(std::path::Path::new("examples"), &mut files);
    files.sort();
    let kicks = 5usize;
    let root = std::fs::canonicalize(".").unwrap();
    println!("[BENCH-EX] {} files, kicks={kicks}, min-of-{kicks} steady-state", files.len());
    let mut tot_ref = 0.0f64;
    let mut tot_twin = 0.0f64;
    for (i, path) in files.iter().enumerate() {
        let Ok(src) = std::fs::read_to_string(path) else { continue };
        let rel = path.strip_prefix(&root).unwrap_or(path).display().to_string();
        let rel = rel.replace('\\', "/");
        let mut line = format!("[BENCH-EX] {rel:<40}");
        let mut mins = [0.0f64; 2];
        for (slot, eng) in [Engine::Reference, Engine::Twin].into_iter().enumerate() {
            let b: Arc<Backend<SilentClient>> = Backend::new_with_engine(SilentClient, eng);
            b.load_prelude();
            let uri = Url::parse(&format!("file:///bench/{i}.typort")).unwrap();
            let t0 = Instant::now();
            b.process_file(&uri, &src, Some(0));
            let first = t0.elapsed().as_secs_f64() * 1000.0;
            let mut best = f64::MAX;
            for k in 0..kicks {
                let t0 = Instant::now();
                b.process_file(&uri, &src, Some(k as i32 + 1));
                let dt = t0.elapsed().as_secs_f64() * 1000.0;
                if dt < best { best = dt; }
            }
            mins[slot] = best;
            line.push_str(&format!(" {eng:?}: first={first:>7.1} min={best:>7.1} ms |"));
        }
        tot_ref += mins[0];
        tot_twin += mins[1];
        let speedup = if mins[1] > 0.0 { mins[0] / mins[1] } else { 0.0 };
        println!("{line} x{speedup:.2}");
    }
    println!(
        "[BENCH-EX] TOTAL ref={tot_ref:.0} ms twin={tot_twin:.0} ms ({:.2}x)",
        if tot_twin > 0.0 { tot_ref / tot_twin } else { 0.0 }
    );
}
