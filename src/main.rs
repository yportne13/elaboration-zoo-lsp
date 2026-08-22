use std::error::Error;

// The elaborator's evaluator allocates 1-3 small nodes (32-100 bytes) per
// machine step (~40M steps during prelude load).  The Windows default heap
// is measurably slower than mimalloc on this pattern; see
// docs/l13-perf-review-4.md round 17 for the measurement.
#[global_allocator]
static ALLOC: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() -> Result<(), Box<dyn Error + Sync + Send>> {
    elaboration_zoo_lsp::run_lsp_server()
}
