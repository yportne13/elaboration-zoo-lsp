# Elaboration Zoo Lsp

A dependently-typed programming language with an LSP server and built-in HDL (Hardware Description Language) support that generates Verilog.

## Features

### Core Language
- **Dependent types**: full-spectrum dependent types with cumulative universes (`Type 0`, `Type 1`, …)
- **Inductive families**: `enum` with indices and parameters (similar to Agda/GADTs)
- **Structural records**: `struct` with named fields
- **Pattern matching**: with dependent pattern matching and absurd patterns
- **Implicit arguments**: `[param: Type]` syntax with instance resolution
- **Typeclasses / Traits**: with `trait` / `impl`, instance synthesis, and `where` clauses
- **Macros**: `macro_rules` with pattern matching on syntax fragments (`ident`, `raw`, `params`)
- **Mutable globals**: `create_global` / `change_mutable` / `get_global` for state

### Theorem Proving
- Inductive `Eq` type with `refl`, `cong`, `trans`, `symm`, `subst`
- Pre-proven lemmas: `add_zero_right`, `add_comm`, `add_assoc`, `mul_one_right`
- Typeclass-based solver with associated types and supertrait support

### HDL (Hardware Description Language)
| Feature | Example | Description |
|---------|---------|-------------|
| UInt / SInt / Bits | `let a = UInt[8]` | Unsigned, signed, bit-vector types |
| Bool signals | `let cond = Bool` | Boolean wire type |
| Arithmetic | `sum := a + b` | `+`, `-`, `*`, `/`, `%`, `+^` (carry) |
| Bitwise | `x := a & b` | `&`, `|`, `^`, `~` |
| Comparators | `lt := a < b` | `<`, `<=`, `>`, `>=`, `===`, `=/=` |
| Bool logic | `r := a && b` | `&&`, `||`, `!`, `^` |
| Bit extraction | `b := a.apply[7]` | `a[N]` bracket sugar also works |
| Range slice | `low := a.slice[3, 0]` | Extracts `(hi-lo+1)` bits |
| LHS bit-select | `t[0] := x` | Assign to individual bits |
| Mux | `r := cond.mux(a, b)` | Conditional multiplexer (SpinalHDL-style) |
| Ternary | `r := cond ? a : b` | C-style ternary operator (desugars to `.mux`) |
| Concatenation | `f := e ## d` | Bit concatenation |
| Variable shift | `r := a |<< sh` / `a |>> sh` | Width-preserving variable shifts (UInt shift amount; SInt `|>>` is arithmetic) |
| SInt abs/expand | `a := sa.abs` / `sa.expand` | Absolute value (UInt) / sign-extend (+1 bit; UInt `expand` zero-extends) |
| Registers | `reg a = UInt[8]` | Sequential elements with clock/reset |
| Reg with init | `reg a = UInt[8] init 42` | Register with async reset value |
| Output reg ports | `output reg x = UInt[8]` | Register output ports (`output reg [7:0] x`); `x := v` drives clocked, `init v` adds async reset |
| Delayed register | `regNext(a)` / `regNextWhen(a, cond)` | SpinalHDL-style delay registers, works for any Data (UInt/SInt/Bits/Bool) |
| Counter | `let c = counter(8)` / `counterInc(8, en)` | SpinalHDL-style counters: free-running or enable-gated increment, `c.value` (reg) + `c.willOverflow` (combinational, `~value == 0`) |
| Memory | `let m = memUInt(8, 256)` | SpinalHDL-style `Mem` as a `reg [w-1:0] name [0:wordCount-1]` array; `m.write(addr, data, en)` (sync write port), `m.readAsync(addr)` (combinational read), `m.readSync(addr)` (registered read), `m.readSyncCC(addr, cd)` (cross-clock read) |
| Type casts | `a.asBits` / `b.asUInt` / `c.asBool` | Explicit type conversion |
| Inout ports | `inout io = UInt[8]` | Tri-state bidirectional ports (`inout wire [7:0] io`); Bundle `inout()` directions (declared in `impl IMasterSlave`'s `asMaster`) become inout ports on both master and slave |
| Sub-modules | `mkInstance("u", "Adder")` | Module instantiation |
| Bundle | `#[derive(Bundle)]` + `impl IMasterSlave` | SpinalHDL-style bulk assignment; auto-named factory (`TypeName.create`, binding name prefix, nested bundles recurse); direction introduced in `impl IMasterSlave`'s `asMaster` (struct fields carry no in()/out() markers), `asSlave` auto-flips, nested bundle fields recurse through the child's asMaster/asSlave |

HDL code is written inside a `module` block and compiles to Verilog:

```typort
module adder[w: Nat] {
    input a = UInt[w]
    input b = UInt[w]
    output sum = UInt[w + 1]
    sum := a +^ b
}

println(moduleTreeVL(adder.create[8].tree))
```

More feature demos live in [`examples/hdl/`](examples/hdl/), one file per feature
group (declarations, arithmetic, bitwise, comparison, bool, bit select & concat,
registers, control flow, hierarchy, bundle). Each file prints its Verilog when
run and doubles as a regression test (`test_examples_hdl_dir`).

### LSP Server
- **Go to definition** – navigate to declarations
- **Hover info** – type and doc display
- **Completions** – field and method suggestions
- **Semantic tokens** – syntax highlighting
- **Inlay hints** – inferred type annotations
- **Diagnostics** – inline error reporting
- **Code actions** – quick fixes
- **Rename** – symbol rename across files
- **References** – find all references

## Getting Started

```bash
# Build
cargo build --release

# Run a .typort file
cargo run --release --bin typort -- check examples/hdl_ops.typort

# Start LSP server
cargo run --release --bin typort -- lsp

# Memory benchmark (requires mem-profile feature)
cargo run --release --features mem-profile --bin typort -- stats

# Interactive tutorial: learn the language step by step
cargo run --release --bin typort -- tutorial

# List lessons / start at lesson 3 / clear progress
cargo run --release --bin typort -- tutorial --list
cargo run --release --bin typort -- tutorial --lesson 3
cargo run --release --bin typort -- tutorial --reset

# Dense cheat-sheet for Verilog+SpinalHDL+Lean engineers (or AI)
cargo run --release --bin typort -- quick        # whole reference
cargo run --release --bin typort -- quick hdl    # one topic
cargo run --release --bin typort -- quick --list
```

### VS Code Extension

The repo includes a VS Code extension in `vscode_extension/` for syntax highlighting and LSP integration.

## Examples

| File | Topics |
|------|--------|
| `examples/theorem_proving.typort` | Eq, trans, symm, cong, add_comm, add_assoc |
| `examples/typeclass_complex.typort` | Traits, instances, generic impls, Eq proofs |
| `examples/alu.typort` | HDL module, UInt arithmetic, Into trait |
| `examples/hdl_ops.typort` | apply, slice, bool ops, sub-modules, LHS bit-select |
| `examples/adder_proof.typort` | Adder correctness proof, Agda-style, Eq/refl/trans/symm/cong |

## Architecture

The project is structured as an **elaboration zoo** — each module (`L01_*` … `L13_*`) incrementally adds a language feature:

| Module | Feature |
|--------|---------|
| `L01_nbe` | Evaluation (NBE) — 12 representation variants, benchmarked via standalone `l01bench` |
| `L02_tyck` | Type checking basics |
| `L03_holes` | Meta variables (holes) |
| `L04_implicit` | Implicit argument inference |
| `L05_pruning` | Pruning (occurs check) |
| `L06_string` | String literals |
| `L07_sum_type` | Sum types (enums) |
| `L07a_depend_pm` | Dependent pattern matching |
| `L08_product_type` | Product types (structs) |
| `L09_mltt` | MLTT-style universes |
| `L10_typeclass` | Typeclass / trait system |
| `L11_macro` | Macro system |
| `L12_canonical` | Canonical forms for typeclass resolution |
| `L13_namespace` | Namespace / package system, HDL Verilog codegen |

## Benchmarking

```bash
# Quick memory stats after prelude loading
cargo run --release --features mem-profile --bin typort -- --stats

# Deep dhat heap profiling (~3 min)
cargo run --release --features dhat-heap --bin typort -- --stats
```

### Key Metrics

| Metric | What it measures |
|--------|-----------------|
| `peak_working_set_mb` | Peak physical RAM (Windows) |
| `meta_entries.unsolved` | Unsolved meta variables |
| `timings.total_secs` | Total loading time |
| dhat peak phases | Per-backtrace allocation breakdown |

## Inspired By

[elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo) ·
[ShiTT2](https://github.com/KonjacSource/ShiTT2) ·
[PM](https://gist.github.com/Guest0x0/844688233e1ea27b0a2307734271644d) ·
[tabled-typeclass-resolution](https://github.com/purefunctor/tabled-typeclass-resolution) ·
[rust-nbe-for-mltt](https://github.com/brendanzab/rust-nbe-for-mltt) ·
[Canonical-min](https://github.com/chasenorman/Canonical-min) ·
[aya](https://github.com/aya-prover/aya-dev) ·
[lean4](https://github.com/leanprover/lean4) ·
[miniagda](https://github.com/andreasabel/miniagda) ·
[rust-analyzer](https://github.com/rust-lang/rust-analyzer) ·
[tower-lsp](https://github.com/ebkalderon/tower-lsp) ·
[resilient-ll-parsing](https://github.com/matklad/resilient-ll-parsing) ·
[chumsky](https://github.com/zesterer/chumsky)
