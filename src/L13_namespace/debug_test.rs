use super::*;

#[test]
fn test_manual_frame_stack() {
    // Just test pushFrame + popFrame returns correct tree
    let input = r#"
def mkTest: ModuleTree =
    let _ = pushFrame("test");
    popFrame()

println(moduleTreeVL(mkTest()))
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("OUTPUT:\n{}", output);
            // Should at least have "module test" (with the name)
            assert!(output.contains("test"), "should have module name 'test', got: {}", output);
        }
        Err(e) => panic!("Error: {:?}", e),
    }
}
