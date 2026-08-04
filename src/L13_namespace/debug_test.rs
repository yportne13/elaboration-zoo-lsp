use super::*;

#[test]
fn debug_module_simple() {
    let input = r#"module Test {
    let sel = UInt[4]
}
println(moduleTreeVL(Test.create.tree))
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

#[test]
fn tuple_hover_element_entries() {
    // `(a, b)` desugars to `Tuple2.mk a b`; the `Tuple2.mk` hover entry spans
    // the whole element list, but each element must ALSO get its own entry
    // (span = element span, type = element type) so the LSP can show the
    // element's type on hover instead of the whole tuple's.
    let input = r#"def foo(a: Nat, b: Bool): Tuple2[Nat, Bool] = (a, b)"#;
    let infer = elaborate_infer(input);
    let base = input.rfind("(a, b)").unwrap();
    let a_span = (base + 1, base + 2); // `a` inside the body tuple
    let b_span = (base + 4, base + 5); // `b` inside the body tuple

    // Element entries: exact element span, quoted element type.
    let entries = |span: (usize, usize)| infer.hover_table.iter()
        .filter(|(s, _, _, _)| s.start_offset as usize == span.0 && s.end_offset as usize == span.1)
        .collect::<Vec<_>>();
    let a_entries = entries(a_span);
    assert!(!a_entries.is_empty(), "no hover entry for tuple element `a`");
    assert!(a_entries.iter().any(|(_, _, h, v)| pretty_tm(0, h.names(), &infer.quote(&h.decl, h.lvl, v)) == "Nat"));
    let b_entries = entries(b_span);
    assert!(!b_entries.is_empty(), "no hover entry for tuple element `b`");
    assert!(b_entries.iter().any(|(_, _, h, v)| pretty_tm(0, h.names(), &infer.quote(&h.decl, h.lvl, v)) == "Bool"));

    // The tuple's own `Tuple2.mk` entry still spans the whole element list.
    assert!(infer.hover_table.iter().any(|(s, _, _, _)|
        s.start_offset as usize == a_span.0 && s.end_offset as usize == b_span.1
    ), "expected a hover entry spanning the whole tuple element list");

    // LSP hover selection (`hover_entry_at`: most specific / smallest span
    // wins): hovering either element shows that element's type.
    let pick = |off: usize| infer.hover_entry_at(24, off)
        .map(|(_, _, h, v)| (h.names(), infer.quote(&h.decl, h.lvl, v)))
        .map(|(names, v)| pretty_tm(0, names, &v))
        .unwrap();
    assert_eq!(pick(a_span.0), "Nat", "hover over `a` should show Nat");
    assert_eq!(pick(b_span.0), "Bool", "hover over `b` should show Bool");
    // Between elements only the whole-tuple entry matches: still the mk entry.
    let comma_span = (a_span.1, b_span.0);
    let wide = infer.hover_entry_at(24, comma_span.0).unwrap();
    assert_eq!((wide.0.start_offset as usize, wide.0.end_offset as usize), (a_span.0, b_span.1));
}

#[test]
fn tuple_hover_literal_elements() {
    // Literal elements (`1`, `2`) have no variable entry of their own, so the
    // elaboration-side element entries are what make hover show `Nat` here.
    let input = r#"def bar: Tuple2[Nat, Nat] = (1, 2)"#;
    let infer = elaborate_infer(input);
    let base = input.rfind("(1, 2)").unwrap();
    for (elem_off, elem_end) in [(base + 1, base + 2), (base + 4, base + 5)] {
        let entries = infer.hover_table.iter()
            .filter(|(s, _, _, _)| s.start_offset as usize == elem_off && s.end_offset as usize == elem_end)
            .collect::<Vec<_>>();
        assert!(!entries.is_empty(), "no hover entry for literal tuple element at {elem_off}");
        assert!(entries.iter().any(|(_, _, h, v)| pretty_tm(0, h.names(), &infer.quote(&h.decl, h.lvl, v)) == "Nat"));
    }
}

/// Elaborate `input` (after the prelude) and return the Infer with its
/// populated hover_table.
fn elaborate_infer(input: &str) -> Infer {
    let cache = PRELUDE_CACHE.get_or_init(|| std::sync::Mutex::new(None));
    let (mut infer, mut cxt, global_macros) = {
        let mut guard = cache.lock().unwrap();
        if guard.is_none() {
            *guard = Some(load_prelude_state().unwrap());
        }
        let state = guard.as_ref().unwrap();
        let mut infer = state.infer.clone();
        infer.mutable_map = Rc::new(std::sync::RwLock::new(
            state.infer.mutable_map.read().unwrap().clone(),
        ));
        (infer, state.cxt.clone(), state.global_macros.clone())
    };
    let ast = parser::parser_with_macros(&preprocess(input), 24, &global_macros)
        .map(|(d, e, _, _)| (d, e)).unwrap();
    for tm in ast.0 {
        let (_, _, new_cxt) = infer.infer(&cxt, tm.clone()).unwrap();
        cxt = new_cxt;
    }
    infer
}

