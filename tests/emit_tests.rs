// `typort emit` integration tests: elaborate examples/hdl sources and pull
// the generated Verilog out through the machine-facing emit channel (the
// synthetic `println(allModulesVL(...))` unit), instead of scraping stderr.

use std::fs;

use elaboration_zoo_lsp::emit::{emit_verilog, top_module_name, EmitError};
use lsp_types::Url;

fn example(name: &str) -> (Url, String) {
    let path = format!("{}/examples/hdl/{name}", env!("CARGO_MANIFEST_DIR"));
    let contents = fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {path}: {e}"));
    (Url::from_file_path(path).unwrap(), contents)
}

#[test]
fn emit_param_top_produces_verilog() {
    let (v, err) = match emit_verilog(&[example("01-basics.typort")], "basicDecls[8]") {
        Ok(v) => (v, String::new()),
        Err(e) => (String::new(), e.to_string()),
    };
    assert!(
        v.contains("module basicDecls"),
        "expected basicDecls module in emitted Verilog, got error: {err}"
    );
    // 01-basics declares basicDecls[w] with an 8-bit port; the param must be
    // baked in (no Verilog parameters in the output).
    assert!(!v.contains("#("), "parameterized Verilog module header leaked: {}", &v[..v.len().min(400)]);
}

#[test]
fn emit_plain_top_produces_verilog() {
    let v = emit_verilog(&[example("02-arithmetic.typort")], "arithmeticUInt").unwrap();
    assert!(v.contains("module arithmeticUInt"));
    assert!(v.contains("endmodule"));
}

#[test]
fn emit_hierarchy_includes_submodules() {
    // 09-hierarchy's topWithAdder instantiates myAdder; allModulesVL must
    // emit every module in the tree, not just the top.
    let v = emit_verilog(&[example("09-hierarchy.typort")], "topWithAdder").unwrap();
    let module_count = v.matches("module ").count();
    assert!(
        module_count >= 2,
        "expected submodule definitions in hierarchy emit, found {module_count}:\n{}",
        &v[..v.len().min(600)]
    );
    assert!(v.contains("module topWithAdder"));
    assert!(v.contains("module myAdder"));
}

#[test]
fn emit_unknown_top_is_elaboration_error() {
    let err = emit_verilog(&[example("01-basics.typort")], "nosuchmodule");
    assert!(matches!(err, Err(EmitError::Elaboration(_))), "got {err:?}");
}

#[test]
fn emit_syntax_error_in_source_is_elaboration_error() {
    let (uri, _) = example("01-basics.typort");
    let bad = format!("module broken\ninput a = UInt[8\n{{}}\n");
    let err = emit_verilog(&[(uri, bad)], "broken");
    assert!(
        matches!(err, Err(EmitError::Elaboration(_)) | Err(EmitError::NoOutput)),
        "got {err:?}"
    );
}

#[test]
fn top_module_name_strips_args() {
    assert_eq!(top_module_name("adder[8]").unwrap(), "adder");
    assert_eq!(top_module_name("adder").unwrap(), "adder");
    assert!(top_module_name("bad name").is_err());
    assert!(top_module_name("").is_err());
}
