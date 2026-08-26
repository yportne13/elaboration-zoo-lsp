// `typort emit` integration tests: elaborate examples/hdl sources and pull
// the generated Verilog out through the machine-facing emit channel (the
// synthetic `println(allModulesVL(...))` unit), instead of scraping stderr.

use std::fs;

use elaboration_zoo_lsp::emit::{emit_design, emit_verilog, top_module_name, EmitError};
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

#[test]
fn manifest_describes_ports_clock_and_instances() {
    let out = emit_design(&[example("09-hierarchy.typort")], "topWithPorts", true).unwrap();
    let manifest = out.manifest.expect("manifest requested");
    let m: serde_json::Value = serde_json::from_str(&manifest)
        .unwrap_or_else(|e| panic!("manifest is not valid JSON ({e}):\n{manifest}"));

    assert_eq!(m["top"], "topWithPorts");
    let modules = m["modules"].as_array().expect("modules array");
    assert_eq!(modules.len(), 2, "top + myAdder, got: {manifest}");

    let top = modules
        .iter()
        .find(|x| x["name"] == "topWithPorts")
        .expect("topWithPorts entry");
    // topWithPorts ports: a, b (input 8), en (input 1), sum (output 8)
    let ports = top["ports"].as_array().unwrap();
    let find_port = |name: &str| {
        ports
            .iter()
            .find(|p| p["name"] == name)
            .unwrap_or_else(|| panic!("no port {name} in {manifest}"))
            .clone()
    };
    assert_eq!(find_port("a")["dir"], "input");
    assert_eq!(find_port("a")["width"], 8);
    assert_eq!(find_port("en")["width"], 1);
    assert_eq!(find_port("sum")["dir"], "output");
    assert_eq!(find_port("sum")["width"], 8);

    // defaultClockDomain: clk/reset, async, posedge, active-high
    assert_eq!(top["clock"]["clk"], "clk");
    assert_eq!(top["clock"]["reset"], "reset");
    assert_eq!(top["clock"]["kind"], "async");
    assert_eq!(top["clock"]["edge"], "posedge");
    assert_eq!(top["clock"]["resetActive"], "high");

    // top instantiates myAdder as u
    let insts = top["instances"].as_array().unwrap();
    assert_eq!(insts.len(), 1);
    assert_eq!(insts[0]["inst"], "u");
    assert_eq!(insts[0]["module"], "myAdder");

    // the child module is itself described
    assert!(
        modules.iter().any(|x| x["name"] == "myAdder"),
        "myAdder entry missing: {manifest}"
    );
}

#[test]
fn manifest_matches_verilog_module_set() {
    let out = emit_design(&[example("09-hierarchy.typort")], "topWithAdder", true).unwrap();
    let m: serde_json::Value = serde_json::from_str(&out.manifest.unwrap()).unwrap();
    let n_manifest = m["modules"].as_array().unwrap().len();
    let n_verilog = out.verilog.matches("endmodule").count();
    assert_eq!(
        n_manifest, n_verilog,
        "manifest and Verilog must describe the same module set"
    );
}

// `let x = a + b` in a module body materializes a named wire instead of
// inlining the expression at every use site (SpinalHDL semantics, LetNamed
// instances in the prelude's hdl-types.typort).
#[test]
fn emit_expression_let_becomes_named_wire() {
    let (uri, _) = example("01-basics.typort");
    let src = "module exprLet {\n\
               \x20   input a = UInt[8]\n\
               \x20   input b = UInt[8]\n\
               \x20   output y = UInt[8]\n\
               \x20   let x = a + b\n\
               \x20   y := x\n\
               }\n";
    let v = emit_verilog(&[(uri, src.to_string())], "exprLet").unwrap();
    assert!(
        v.contains("wire [7:0] x;"),
        "expected a named wire for the expression let, got:\n{v}"
    );
    assert!(
        v.contains("assign x = (a + b);"),
        "expected the wire to be driven by the let expression, got:\n{v}"
    );
    assert!(
        v.contains("assign y = x;"),
        "later uses must reference the wire, not re-inline the expression, got:\n{v}"
    );
}

// A let that aliases an already-declared signal (factory product, port) is
// plain aliasing — no extra wire may be created for it.
#[test]
fn emit_aliasing_let_adds_no_extra_wire() {
    let (uri, _) = example("01-basics.typort");
    let src = "module aliasLet {\n\
               \x20   input a = UInt[8]\n\
               \x20   output y = UInt[8]\n\
               \x20   let s = UInt[8]\n\
               \x20   let alias = s\n\
               \x20   s := a\n\
               \x20   y := alias\n\
               }\n";
    let v = emit_verilog(&[(uri, src.to_string())], "aliasLet").unwrap();
    assert!(
        !v.contains("wire [7:0] alias;"),
        "aliasing let must not create a wire, got:\n{v}"
    );
    assert!(
        v.contains("assign y = s;"),
        "the alias must keep referencing the original signal, got:\n{v}"
    );
}
