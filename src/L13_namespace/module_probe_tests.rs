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
        ("12-arithmetic2", include_str!("../../examples/hdl/12-arithmetic2.typort")),
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
