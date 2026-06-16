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

#[test]
fn let_pattern_tuple() {
    // let (a, b) = (1, 2); a
    // Tuple2 has a single constructor → irrefutable
    let input = r#"println(let (a, b) = (1, 2); a)"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("OUTPUT_START\n{}OUTPUT_END", output);
            assert!(output.trim() == "1", "expected 1, got: {}", output);
        }
        Err(e) => panic!("unexpected error: {} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn let_pattern_constructor() {
    // let Product { a, b } = new Product(1, 2); a
    // Product has a single constructor → irrefutable
    let input = r#"println(let Product { a, b } = new Product(1, 2); a)"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("OUTPUT_START\n{}OUTPUT_END", output);
            assert!(output.trim() == "1", "expected 1, got: {}", output);
        }
        Err(e) => panic!("unexpected error: {} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn let_pattern_wildcard() {
    // let _ = 99; 42  → discards 99, returns 42
    let input = r#"println(let _ = 99; 42)"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("OUTPUT_START\n{}OUTPUT_END", output);
            assert!(output.trim() == "42", "expected 42, got: {}", output);
        }
        Err(e) => panic!("unexpected error: {} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn let_binder_simple() {
    // Old fast path: let x = 7; x  (no match desugaring)
    let input = r#"println(let x = 7; x)"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("OUTPUT_START\n{}OUTPUT_END", output);
            assert!(output.trim() == "7", "expected 7, got: {}", output);
        }
        Err(e) => panic!("unexpected error: {} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn let_binder_with_type() {
    // let x : Nat = 5; x + 2
    let input = r#"println(let x : Nat = 5; x + 2)"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("OUTPUT_START\n{}OUTPUT_END", output);
            assert!(output.trim() == "7", "expected 7, got: {}", output);
        }
        Err(e) => panic!("unexpected error: {} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn let_pattern_refutable_errors() {
    // let Some(x) = val where val : Option[Nat]; val is None, so Some is refutable
    let input = r#"
def test: Nat =
    let val: Option[Nat] = None;
    let Some(x) = val;
    x
println(test)
"#;
    match run_with_prelude(input) {
        Ok(_) => panic!("expected error for refutable pattern, but got Ok"),
        Err(e) => {
            println!("expected error (refutable pattern): {}", e.0.data);
            assert!(e.0.data.contains("non-exhaustive") || e.0.data.contains("not covered"),
                "expected non-exhaustive error, got: {}", e.0.data);
        }
    }
}
