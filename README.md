# Elaboration Zoo Lsp

create a language server for a dependent type language

## Inspired By

this project is inspired by

- [elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo)

- [ShiTT2](https://github.com/KonjacSource/ShiTT2)

- [PM](https://gist.github.com/Guest0x0/844688233e1ea27b0a2307734271644d)

- [tabled-typeclass-resolution](https://github.com/purefunctor/tabled-typeclass-resolution)

- [rust-nbe-for-mltt](https://github.com/brendanzab/rust-nbe-for-mltt)

- [Canonical-min](https://github.com/chasenorman/Canonical-min) - A sound and complete solver for type inhabitation and unification in dependent type theory

- [aya](https://github.com/aya-prover/aya-dev)

- [lean4](https://github.com/leanprover/lean4)

- [miniagda](https://github.com/andreasabel/miniagda)

- [vscode-extension-samples](https://github.com/microsoft/vscode-extension-samples)

- [rust-analyzer](https://github.com/rust-lang/rust-analyzer)

- [tower-lsp](https://github.com/ebkalderon/tower-lsp)

- [resilient-ll-parsing](https://github.com/matklad/resilient-ll-parsing)

- [nom](https://github.com/rust-bakery/nom)

- [chumsky](https://github.com/zesterer/chumsky)

## Benchmarking

Quick memory benchmark after prelude loading:

```bash
cargo run --release --bin typort -- --stats
```

Output (JSON):

```json
{
  "peak_working_set_mb": "1826",
  "pagefile_usage_mb":  "1777",
  "infer_stats": {
    "meta_entries": {
      "total": 298743,
      "solved": 42826,
      "unsolved": 255917,
      "vec_allocation_bytes": 142606336
    },
    "hover_table": { "capacity": 524288 },
    "completion_table": { "len": 0 }
  }
}
```

### Deep heap profiling with dhat

For per-allocation-callsite breakdown (slow, ~3min):

```bash
cargo run --release --features dhat-heap --bin typort -- --stats
```

This produces `dhat-heap.json` (viewable with `dhat/dh_view.html`).
Only the `dhat-heap` feature flag activates the profiler; normal builds
are unaffected.

### Key metrics to track

| Metric | What it measures |
|--------|-----------------|
| `peak_working_set_mb` | Peak physical RAM (Windows) |
| `pagefile_usage_mb` | Peak committed virtual memory |
| `meta_entries.unsolved` | Count of unsolved meta variables |
| `meta_entries.vec_allocation_bytes` | Vec backing store for meta entries |
| `hover_table.capacity` | Residual capacity after clear |
| dhat peak phases | Per-backtrace allocation breakdown |
