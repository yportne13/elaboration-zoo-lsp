use super::*;

#[test]
fn probe_timing() {
    let files = [
        ("01-basics", include_str!("../../examples/hdl/01-basics.typort")),
        ("02-arithmetic", include_str!("../../examples/hdl/02-arithmetic.typort")),
        ("03-bitwise", include_str!("../../examples/hdl/03-bitwise.typort")),
        ("04-compare", include_str!("../../examples/hdl/04-compare.typort")),
        ("05-bool", include_str!("../../examples/hdl/05-bool.typort")),
        ("06-select-cat", include_str!("../../examples/hdl/06-select-cat.typort")),
        ("07-registers", include_str!("../../examples/hdl/07-registers.typort")),
        ("08-control-flow", include_str!("../../examples/hdl/08-control-flow.typort")),
        ("09-hierarchy", include_str!("../../examples/hdl/09-hierarchy.typort")),
        ("10-bundle", include_str!("../../examples/hdl/10-bundle.typort")),
        ("11-memory", include_str!("../../examples/hdl/11-memory.typort")),
    ];
    let _ = run_with_prelude("def warm: Nat = 0");
    let mut out = String::new();
    for (name, input) in files {
        let start = std::time::Instant::now();
        match run_with_prelude(input) {
            Ok(o) => out.push_str(&format!("T_{}: {:?}\n", name, start.elapsed())),
            Err(e) => out.push_str(&format!("T_{}_ERR: {}\n", name, e.0.data)),
        }
    }
    std::fs::write("F:/projects/hermes/elaboration-zoo-lsp/probe-out.txt", out).unwrap();
}

// ── example 12: adder tree with width proof ──
// The example file is elaborated as a whole (like the other hdl examples);
// the proof chain inside adder_tree (calc + .cast) must type-check during
// elaboration, and the runtime prints must show the expected widths.

#[test]
fn example_12_adder_tree() {
    let input = include_str!("../../examples/hdl/12-adder-tree.typort");
    let output = match run_with_prelude(input) {
        Ok(o) => o,
        Err(e) => panic!("expected OK, got error: '{}' @ {}:{}", e.0.data, e.0.path_id, e.0.start_offset),
    };
    assert!(output.contains("module adderTree8"), "expected module header, got: {}", output);
    assert!(output.contains("wire [10:0] sum"), "expected [10:0] sum (8 + log2Up 8 = 11), got: {}", output);
    assert!(output.contains("wire [17:0] sum"), "expected [17:0] sum (16 + log2Up 4 = 18), got: {}", output);
    assert!(output.contains("wire [9:0] sum"), "expected [9:0] sum (8 + log2Up 3 = 10), got: {}", output);
    assert!(output.contains("\n11\n"), "expected log2Up print 11, got: {}", output);
    assert!(output.contains("\n18\n"), "expected log2Up print 18, got: {}", output);
    assert!(output.contains("\n10\n"), "expected log2Up print 10, got: {}", output);
}
