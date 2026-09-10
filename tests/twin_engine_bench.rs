// Ignored-by-default measurement of the LSP per-kick cost under each engine
// (stage 3a seed-cost baseline requested by docs/lsp-twin-wiring-2026-09.md).
//
// Run explicitly in release:
//   cargo test --release --test twin_engine_bench -- --ignored --nocapture
//
// Finding (2026-09-10, 09-hierarchy, release): the twin path replays the
// entire ~943-decl prelude on every kick (`run_decls_with_prelude`), which is
// ~10x the reference engine's cached-prelude kick.  A resident twin prelude
// is required before twin can be a net win; see the wiring doc's progress log.

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
