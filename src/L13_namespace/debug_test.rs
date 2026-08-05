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

#[test]
fn pm_ctor_hover_prelude_boolean() {
    // Constructor patterns (`case true`) must hover like constructor
    // expressions: the nullary `Boolean.true` shows `Boolean::true` and
    // goto-definition points into the prelude (path_id != input's 24) —
    // NOT the bound-variable type (`Boolean`) that `case x` shows.
    let input = r#"def f(b: Boolean): Nat =
    match b {
        case true => 1
        case false => 0
    }"#;
    let infer = elaborate_infer(input);
    let entries_at = |span: (usize, usize)| infer.hover_table.iter()
        .filter(|(s, _, _, _)| s.start_offset as usize == span.0 && s.end_offset as usize == span.1)
        .collect::<Vec<_>>();
    let true_base = input.find("case true").unwrap() + 5; // token `true`
    let true_span = (true_base, true_base + 4);
    let false_base = input.find("case false").unwrap() + 5; // token `false`
    let false_span = (false_base, false_base + 5);

    // Entries exist on the pattern tokens themselves, render as the
    // constructor (`Boolean::true` / `Boolean::false`), and their
    // definition span points at the prelude declaration, not the input.
    let true_entries = entries_at(true_span);
    assert!(!true_entries.is_empty(), "no hover entry for `true` pattern");
    assert!(true_entries.iter().any(|(_, d, h, v)| {
        d.path_id != 24
            && pretty_tm(0, h.names(), &infer.quote(&h.decl, h.lvl, v)) == "Boolean::true"
    }), "expected a `Boolean::true` entry with prelude definition span for `true`");
    let false_entries = entries_at(false_span);
    assert!(!false_entries.is_empty(), "no hover entry for `false` pattern");
    assert!(false_entries.iter().any(|(_, d, h, v)| {
        d.path_id != 24
            && pretty_tm(0, h.names(), &infer.quote(&h.decl, h.lvl, v)) == "Boolean::false"
    }), "expected a `Boolean::false` entry with prelude definition span for `false`");

    // LSP hover selection picks the constructor entry at the token.
    let pick = |off: usize| infer.hover_entry_at(24, off)
        .map(|(_, _, h, v)| pretty_tm(0, h.names(), &infer.quote(&h.decl, h.lvl, v)))
        .unwrap();
    assert_eq!(pick(true_span.0), "Boolean::true", "hover over pattern `true`");
    assert_eq!(pick(false_span.0), "Boolean::false", "hover over pattern `false`");
}

#[test]
fn pm_ctor_hover_goto_def_local_enum() {
    // goto-definition for a user-defined enum: each pattern token's entry
    // definition span must equal the case-name span in the enum declaration.
    let input = r#"
enum Color {
    red
    green
    blue
}
def pick(c: Color): Nat =
    match c {
        case red => 1
        case green => 2
        case blue => 3
    }
"#;
    let infer = elaborate_infer(input);
    // Definition spans: first occurrence of each name is in the enum decl.
    let def_span = |name: &str| {
        let s = input.find(name).unwrap();
        (s, s + name.len())
    };
    let entries_at = |span: (usize, usize)| infer.hover_table.iter()
        .filter(|(s, _, _, _)| s.start_offset as usize == span.0 && s.end_offset as usize == span.1)
        .collect::<Vec<_>>();
    for (name, case) in [("red", "case red"), ("green", "case green"), ("blue", "case blue")] {
        let pat_base = input.find(case).unwrap() + 5;
        let pat_span = (pat_base, pat_base + name.len());
        let (def_s, def_e) = def_span(name);
        let entries = entries_at(pat_span);
        assert!(!entries.is_empty(), "no hover entry for pattern `{name}`");
        assert!(entries.iter().any(|(_, d, h, v)| {
            d.start_offset as usize == def_s
                && d.end_offset as usize == def_e
                && d.path_id == 24
                && pretty_tm(0, h.names(), &infer.quote(&h.decl, h.lvl, v)).contains("Color")
        }), "pattern `{name}` entry must point at the enum declaration case span");
    }
}

#[test]
fn pm_ctor_hover_differs_from_bound_var() {
    // `true` (constructor pattern) hovers as the constructor, while `x`
    // (bare-variable pattern) keeps showing the bound variable's type.
    let input = r#"def g(b: Boolean): Nat =
    match b {
        case true => 1
        case x => 0
    }"#;
    let infer = elaborate_infer(input);
    let pick = |off: usize| infer.hover_entry_at(24, off)
        .map(|(_, _, h, v)| pretty_tm(0, h.names(), &infer.quote(&h.decl, h.lvl, v)))
        .unwrap();
    let true_off = input.find("case true").unwrap() + 5;
    let x_off = input.find("case x").unwrap() + 5;
    let true_rendered = pick(true_off);
    let x_rendered = pick(x_off);
    assert_eq!(x_rendered, "Boolean", "bare-variable pattern `x` keeps its type hover");
    assert_ne!(true_rendered, "Boolean", "constructor `true` must NOT render as the bound type");
    assert_eq!(true_rendered, "Boolean::true");
}

#[test]
fn pm_ctor_hover_param_constructor_pi_signature() {
    // Parameterized constructor pattern: hover shows the constructor's Pi
    // signature (not an unreadable lambda), and bound fields keep their
    // type hover.  Nullary `leaf` renders as `Tree::leaf`.
    let input = r#"
enum Tree {
    leaf
    node(l: Tree, r: Tree)
}
def depth(t: Tree): Nat =
    match t {
        case leaf => 0
        case node(l, r) => 1
    }
"#;
    let infer = elaborate_infer(input);
    let pick = |off: usize| infer.hover_entry_at(24, off)
        .map(|(_, _, h, v)| pretty_tm(0, h.names(), &infer.quote(&h.decl, h.lvl, v)))
        .unwrap();
    // `node` pattern token → Pi signature mentioning Tree.
    let node_off = input.find("case node").unwrap() + 5;
    let node_rendered = pick(node_off);
    assert!(node_rendered.contains("Tree"), "node hover should mention Tree, got: {node_rendered}");
    assert_ne!(node_rendered, "Tree", "node hover should be a Pi signature, not the bare type");
    // `leaf` pattern token → constructor value `Tree::leaf`.
    let leaf_off = input.find("case leaf").unwrap() + 5;
    assert_eq!(pick(leaf_off), "Tree::leaf", "hover over pattern `leaf`");
    // Bound fields `l`/`r` keep the binding-variable type hover.
    // `node(l, r)` — `l` at +5, `r` at +8 (after `node(l, `).
    let pats_base = input.find("node(l, r)").unwrap();
    assert_eq!(pick(pats_base + 5), "Tree", "hover over field binding `l`");
    assert_eq!(pick(pats_base + 8), "Tree", "hover over field binding `r`");
}



#[test]
fn probe_completion_table_states() {
    // Probe: completion entries at the `p.` (empty member) state vs the
    // `p.z` (typed member) state — is the table empty once a prefix is typed?
    let empty_state = r#"
struct Point {
    x: Nat
    y: Nat
}
def f(p: Point): Nat = p.
"#;
    let cache0 = PRELUDE_CACHE.get_or_init(|| std::sync::Mutex::new(None));
    let (mut infer0, mut cxt0, global_macros0) = {
        let mut guard = cache0.lock().unwrap();
        let state = guard.as_ref().unwrap();
        let mut infer = state.infer.clone();
        infer.mutable_map = Rc::new(std::sync::RwLock::new(
            state.infer.mutable_map.read().unwrap().clone(),
        ));
        (infer, state.cxt.clone(), state.global_macros.clone())
    };
    let ast0 = parser::parser_with_macros(&preprocess(empty_state), 24, &global_macros0)
        .map(|(d, e, _, _)| (d, e)).unwrap();
    for tm in ast0.0 {
        let r = infer0.infer(&cxt0, tm.clone());
        if let Err(ref e) = r { println!("ERR: {}", e.0.data); }
        if let Ok((_, _, c)) = r { cxt0 = c; }
    }
    println!("=== empty state p. ===");
    for (span, name) in &infer0.completion_table {
        println!("COMPLETION [{}..{}] {}", span.start_offset, span.end_offset, name);
    }

    // Typed-prefix state: `p.z` (unknown member) — elaborated directly so
    // the member-lookup error does not abort the probe.
    let typed_state = r#"
struct Point {
    x: Nat
    y: Nat
}
def f(p: Point): Nat = p.z
"#;
    let cache = PRELUDE_CACHE.get_or_init(|| std::sync::Mutex::new(None));
    let (mut infer2, mut cxt2, global_macros) = {
        let mut guard = cache.lock().unwrap();
        let state = guard.as_ref().unwrap();
        let mut infer = state.infer.clone();
        infer.mutable_map = Rc::new(std::sync::RwLock::new(
            state.infer.mutable_map.read().unwrap().clone(),
        ));
        (infer, state.cxt.clone(), state.global_macros.clone())
    };
    let ast2 = parser::parser_with_macros(&preprocess(typed_state), 24, &global_macros)
        .map(|(d, e, _, _)| (d, e)).unwrap();
    for tm in ast2.0 {
        let r = infer2.infer(&cxt2, tm.clone());
        if let Err(ref e) = r { println!("ERR: {}", e.0.data); }
        if let Ok((_, _, c)) = r { cxt2 = c; }
    }
    println!("=== typed state p.z ===");
    for (span, name) in &infer2.completion_table {
        println!("COMPLETION [{}..{}] {}", span.start_offset, span.end_offset, name);
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

