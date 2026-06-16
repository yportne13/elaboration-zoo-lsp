use super::*;

#[test]
fn debug_module_simple() {
    let input = r#"module Test {
    let sel = UInt[4]
}
println(moduleTreeVL(Test))
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("OUTPUT_START\n{}OUTPUT_END", output);
        }
        Err(e) => println!("ERR: {} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}
