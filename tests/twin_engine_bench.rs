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
// See the wiring doc's 2026-09-10 progress log.

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
fn bench_kick_cost_by_engine() {
    let src = std::fs::read_to_string("examples/hdl/09-hierarchy.typort").unwrap();
    let kicks = 5usize;
    for eng in [Engine::Reference, Engine::Twin] {
        let mut best = f64::MAX;
        for _ in 0..kicks {
            let b: Arc<Backend<SilentClient>> = Backend::new_with_engine(SilentClient, eng);
            b.load_prelude();
            let uri = Url::parse("file:///bench.typort").unwrap();
            let t0 = Instant::now();
            b.process_file(&uri, &src, Some(1));
            let dt = t0.elapsed().as_secs_f64() * 1000.0;
            if dt < best {
                best = dt;
            }
        }
        println!("[BENCH] {eng:?}: {best:.1} ms/kick (min of {kicks})");
    }
}
