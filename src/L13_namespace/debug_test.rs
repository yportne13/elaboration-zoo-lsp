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

fn hover_type_of(input: &str, name: &str) -> String {
    let infer = elaborate_infer(input);
    let pos = input.find(name).unwrap();
    let (_, _, s) = infer.hover_entry_at(24, pos).unwrap();
    s.clone()
}

#[test]
fn hover_type_folds_independent_params() {
    // Multi-param function types fold into one group when later params do
    // not depend on earlier ones (`(x: Nat, y: Bool) → Bool` instead of the
    // `(x: Nat) → (y: Bool) → Bool` arrow chain), and implicit binders use
    // the parser's square-bracket syntax (`[A: Type 0]`, not `{A: Type 0}`).
    assert_eq!(
        hover_type_of("def foo(x: Nat, y: Bool): Bool = y", "foo"),
        "(x: Nat, y: Bool) → Bool"
    );
    // x and y both depend on A, so they stay behind A's own `→`, but they
    // are independent of each other and fold together.
    assert_eq!(
        hover_type_of("def bar[A](x: A, y: A): A = x", "bar"),
        "[A: Type 0] → (x: A, y: A) → A"
    );
    // f's domain `A → Nat` depends on A (outside the merged group) but not
    // on x or y, so x, y, f fold into one explicit group.
    assert_eq!(
        hover_type_of("def dep4[A](x: A, y: Nat, f: A -> Nat): Nat = y", "dep4"),
        "[A: Type 0] → (x: A, y: Nat, f: A → Nat) → Nat"
    );
    // Single-binder types are unchanged.
    assert_eq!(
        hover_type_of("def idd[A](x: A): A = x", "idd"),
        "[A: Type 0] → (x: A) → A"
    );
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
        .filter(|(s, _, _)| s.start_offset as usize == span.0 && s.end_offset as usize == span.1)
        .collect::<Vec<_>>();
    let a_entries = entries(a_span);
    assert!(!a_entries.is_empty(), "no hover entry for tuple element `a`");
    assert!(a_entries.iter().any(|(_, _, s)| s.clone() == "Nat"));
    let b_entries = entries(b_span);
    assert!(!b_entries.is_empty(), "no hover entry for tuple element `b`");
    assert!(b_entries.iter().any(|(_, _, s)| s.clone() == "Bool"));

    // The tuple's own `Tuple2.mk` entry still spans the whole element list.
    assert!(infer.hover_table.iter().any(|(s, _, _)|
        s.start_offset as usize == a_span.0 && s.end_offset as usize == b_span.1
    ), "expected a hover entry spanning the whole tuple element list");

    // LSP hover selection (`hover_entry_at`: most specific / smallest span
    // wins): hovering either element shows that element's type.
    let pick = |off: usize| infer.hover_entry_at(24, off)
        .map(|(_, _, s)| s.clone())
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
            .filter(|(s, _, _)| s.start_offset as usize == elem_off && s.end_offset as usize == elem_end)
            .collect::<Vec<_>>();
        assert!(!entries.is_empty(), "no hover entry for literal tuple element at {elem_off}");
        assert!(entries.iter().any(|(_, _, s)| s.clone() == "Nat"));
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
        .filter(|(s, _, _)| s.start_offset as usize == span.0 && s.end_offset as usize == span.1)
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
    assert!(true_entries.iter().any(|(_, d, s)| {
        d.path_id != 24
            && s.clone() == "Boolean::true"
    }), "expected a `Boolean::true` entry with prelude definition span for `true`");
    let false_entries = entries_at(false_span);
    assert!(!false_entries.is_empty(), "no hover entry for `false` pattern");
    assert!(false_entries.iter().any(|(_, d, s)| {
        d.path_id != 24
            && s.clone() == "Boolean::false"
    }), "expected a `Boolean::false` entry with prelude definition span for `false`");

    // LSP hover selection picks the constructor entry at the token.
    let pick = |off: usize| infer.hover_entry_at(24, off)
        .map(|(_, _, s)| s.clone())
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
        .filter(|(s, _, _)| s.start_offset as usize == span.0 && s.end_offset as usize == span.1)
        .collect::<Vec<_>>();
    for (name, case) in [("red", "case red"), ("green", "case green"), ("blue", "case blue")] {
        let pat_base = input.find(case).unwrap() + 5;
        let pat_span = (pat_base, pat_base + name.len());
        let (def_s, def_e) = def_span(name);
        let entries = entries_at(pat_span);
        assert!(!entries.is_empty(), "no hover entry for pattern `{name}`");
        assert!(entries.iter().any(|(_, d, s)| {
            d.start_offset as usize == def_s
                && d.end_offset as usize == def_e
                && d.path_id == 24
                && s.clone().contains("Color")
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
        .map(|(_, _, s)| s.clone())
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
        .map(|(_, _, s)| s.clone())
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
    let (mut infer0, mut cxt0, global_macros0) = {
        PRELUDE_CACHE.with(|c: &super::PreludeSlot| {
            let mut guard = c.cell.borrow_mut();
            if guard.is_none() {
                *guard = Some(load_prelude_state().unwrap());
            }
            let state = guard.as_ref().unwrap();
            let mut infer = state.infer.clone();
            infer.mutable_map = Rc::new(std::sync::RwLock::new(
                state.infer.mutable_map.read().unwrap().clone(),
            ));
            (infer, state.cxt.clone(), state.global_macros.clone())
        })
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
    let (mut infer2, mut cxt2, global_macros) = {
        PRELUDE_CACHE.with(|c: &super::PreludeSlot| {
            let mut guard = c.cell.borrow_mut();
            if guard.is_none() {
                *guard = Some(load_prelude_state().unwrap());
            }
            let state = guard.as_ref().unwrap();
            let mut infer = state.infer.clone();
            infer.mutable_map = Rc::new(std::sync::RwLock::new(
                state.infer.mutable_map.read().unwrap().clone(),
            ));
            (infer, state.cxt.clone(), state.global_macros.clone())
        })
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

/// 同 [`elaborate_infer`]，但**关闭观察面采集**（`lsp_collect = false`）——
/// 复杂度探针的对照组（只差采集开关，其余完全相同）。
fn elaborate_infer_no_collect(input: &str) -> Infer {
    let (mut infer, mut cxt, global_macros) = prelude_state_for_probe();
    infer.lsp_collect = false;
    let ast = parser::parser_with_macros(&preprocess(input), 24, &global_macros)
        .map(|(d, e, _, _)| (d, e)).unwrap();
    for tm in ast.0 {
        let (_, _, new_cxt) = infer.infer(&cxt, tm.clone()).unwrap();
        cxt = new_cxt;
    }
    infer
}

fn elaborate_infer_pair(input: &str) -> Option<(Infer, super::Cxt)> {
    Some(elaborate_infer_ctx(input))
}

fn prelude_state_for_probe() -> (Infer, super::Cxt, super::PreludeMacros) {
    PRELUDE_CACHE.with(|c: &super::PreludeSlot| {
        let mut guard = c.cell.borrow_mut();
        if guard.is_none() {
            *guard = Some(load_prelude_state().unwrap());
        }
        let state = guard.as_ref().unwrap();
        let mut infer = state.infer.clone();
        infer.mutable_map = Rc::new(std::sync::RwLock::new(
            state.infer.mutable_map.read().unwrap().clone(),
        ));
        (infer, state.cxt.clone(), state.global_macros.clone())
    })
}

/// 同 [`elaborate_infer`]，但同时返回**最终 Cxt**（读 decl 表里登记期渲染串用）。
fn elaborate_infer_ctx(input: &str) -> (Infer, super::Cxt) {
    let (mut infer, mut cxt, global_macros) = {
        PRELUDE_CACHE.with(|c: &super::PreludeSlot| {
            let mut guard = c.cell.borrow_mut();
            if guard.is_none() {
                *guard = Some(load_prelude_state().unwrap());
            }
            let state = guard.as_ref().unwrap();
            let mut infer = state.infer.clone();
            infer.mutable_map = Rc::new(std::sync::RwLock::new(
                state.infer.mutable_map.read().unwrap().clone(),
            ));
            (infer, state.cxt.clone(), state.global_macros.clone())
        })
    };
    let ast = parser::parser_with_macros(&preprocess(input), 24, &global_macros)
        .map(|(d, e, _, _)| (d, e)).unwrap();
    for tm in ast.0 {
        let (_, _, new_cxt) = infer.infer(&cxt, tm.clone()).unwrap();
        cxt = new_cxt;
    }
    (infer, cxt)
}

/// Elaborate `input` (after the prelude) and return the Infer with its
/// populated hover_table.
fn elaborate_infer(input: &str) -> Infer {
    let (mut infer, mut cxt, global_macros) = {
        PRELUDE_CACHE.with(|c: &super::PreludeSlot| {
            let mut guard = c.cell.borrow_mut();
            if guard.is_none() {
                *guard = Some(load_prelude_state().unwrap());
            }
            let state = guard.as_ref().unwrap();
            let mut infer = state.infer.clone();
            infer.mutable_map = Rc::new(std::sync::RwLock::new(
                state.infer.mutable_map.read().unwrap().clone(),
            ));
            (infer, state.cxt.clone(), state.global_macros.clone())
        })
    };
    let ast = parser::parser_with_macros(&preprocess(input), 24, &global_macros)
        .map(|(d, e, _, _)| (d, e)).unwrap();
    for tm in ast.0 {
        let (_, _, new_cxt) = infer.infer(&cxt, tm.clone()).unwrap();
        cxt = new_cxt;
    }
    infer
}

/// 源码注解渲染（2026-11-23）：有显式类型注解的 def，`typ_pretty` 直接是**源码文本**——
/// 于是 `def g(n: Nat): T n` 显示 `(n: Nat) → T n`，不会展开成 `match n { … }`，
/// 也完全绕开 `quote`/`quote_nat`（后者对 `Val::Nat(k)` 要建 k 层 SumCase 链）。
#[test]
fn def_with_source_annotation_renders_source_form() {
    // prelude 已定义 Nat / Bool，这里只加类型函数与有注解的 def。
    let input = r#"
def T(n: Nat): Type 0 =
    match n {
        case zero => Boolean
        case succ(m) => Nat
    }
def g(n: Nat): T n =
    match n {
        case zero => true
        case succ(m) => zero
    }
"#;
    let (infer, cxt) = elaborate_infer_ctx(input);
    let e = cxt.decl.get("g").expect("g 已登记");
    let _ = &infer;
    // decl 条目是元组：.6 是登记期 `typ_pretty`（与 lib.rs 的 `e.6` 同口径）。
    let typ_pretty = e.6.as_str();
    // L13 的显示口径：冒号前无空格（与 pretty_tm 的 `(x: A, y: B) → C` 一致）。
    assert_eq!(typ_pretty, "(n: Nat) → T n", "应为源码形态");
    assert!(!typ_pretty.contains("match"), "不得展开: {typ_pretty}");
}

/// 无注解的 def 仍走值渲染（源码里没有类型文本可打）——不应崩、应给出类型。
#[test]
fn def_without_source_annotation_still_renders() {
    let input = r#"
def g(n: Nat): Nat = n
def h(n: Nat) = g n
"#;
    let (infer, cxt) = elaborate_infer_ctx(input);
    let e = cxt.decl.get("h").expect("h 已登记");
    let _ = &infer;
    assert!(!e.6.is_empty());
}

/// 复杂度证据：带大 Nat 字面量的类型注解，源码渲染**不建链**。
/// 旧路径 `nf → quote → quote_nat` 会为 `Val::Nat(k)` 建 k 层 `SumCase` 节点；
/// 源码渲染只拼字符串。这里用 k = 100_000（旧路径按 ~100 B/节点 ≈ 10 MB，
/// 且 O(k) 时间）。
#[test]
fn big_nat_literal_in_annotation_does_not_expand() {
    // Box 不在 prelude 里：用一个 def 参数承载大 Nat 索引。
    let input = r#"
def Box(n: Nat): Type 0 = Nat
def big(n: Nat): Box 100000 = n
"#;
    let (_, cxt) = elaborate_infer_ctx(input);
    let e = cxt.decl.get("big").expect("big 已登记");
    let typ_pretty = e.6.as_str();
    // 源码形态：`(n : Nat) → Box 100000`（字面量原样，不展开成 succ 链）
    assert!(
        typ_pretty.contains("100000"),
        "字面量应原样保留: {typ_pretty}"
    );
    assert!(
        typ_pretty.len() < 60,
        "串长应线性于源码，而非 O(k): len={} {typ_pretty}",
        typ_pretty.len()
    );
}

/// 形状认回（方案 3）：无注解 def 的类型也能打回 `T n`（不是展开的 match）。
#[test]
fn unannotated_def_recovers_type_level_name() {
    let input = r#"
def T(n: Nat): Type 0 =
    match n {
        case zero => Boolean
        case succ(m) => Nat
    }
def g(n: Nat): T n =
    match n {
        case zero => true
        case succ(m) => zero
    }
def h(n: Nat) = g n
"#;
    let infer = elaborate_infer(input);
    // `h` 的 hover 条目（使用处 = def 名，同 span）
    let entries: Vec<_> = infer.hover_table.iter()
        .filter(|(s, _, _)| {
            // h 的定义处：源码里 "def h(" 之后的名字
            let off = input.find("def h(").unwrap() + 4;
            s.start_offset as usize == off
        })
        .collect();
    assert!(!entries.is_empty(), "h 应有 hover 条目");
    let text = &entries[0].2;
    assert!(
        text.contains("T n"),
        "应认回类型级 def 名 `T n`，而不是展开的 match: {text}"
    );
    assert!(!text.contains("match"), "不得展开: {text}");
}

/// L13 `LspSurface` 快照：六通道从 `Infer` 的散表收敛成 owned 值。
#[test]
fn lsp_surface_snapshot_has_hover_entries() {
    let input = r#"
def g(n: Nat): Nat = n
def h(n: Nat) = g n
"#;
    let infer = elaborate_infer(input);
    let s = infer.lsp_surface();
    assert!(s.is_empty() == false, "应有 hover 条目");
    // 同一张表：快照与 live Infer 逐条一致
    assert_eq!(s.hover.len(), infer.hover_table.len());
    // 查询口径：按偏移取最窄条目
    let off = input.find("def g(").unwrap() + 4;
    let t = s.hover_text_at(24, off).expect("g 的条目");
    // 注意：def-site hover 走 L13 的「独立参数折叠」约定（单参数时无差异）。
    assert_eq!(t, "(n: Nat) → Nat", "源码注解渲染: {t}");
}

/// 快照是 owned 值：拿到后原 `Infer` 可以释放（这里用 drop 语义验证不再引用）。
#[test]
fn lsp_surface_is_owned() {
    let input = "def g(n: Nat): Nat = n\n";
    let s = {
        let infer = elaborate_infer(input);
        infer.lsp_surface()
    };
    let off = input.find("def g(").unwrap() + 4;
    assert_eq!(s.hover_text_at(24, off).expect("条目"), "(n: Nat) → Nat");
}

/// 查询口径（`SurfaceQuery`）：只采光标处的 hover。
#[test]
fn surface_query_filters_hover_collection() {
    let input = r#"
def f(n: Nat): Nat = n
def g(m: Nat): Nat = m
"#;
    let probe = input.find("def g(").unwrap() + 4;
    let (mut infer, cxt, macros) = {
        PRELUDE_CACHE.with(|c: &super::PreludeSlot| {
            let mut guard = c.cell.borrow_mut();
            if guard.is_none() {
                *guard = Some(load_prelude_state().unwrap());
            }
            let state = guard.as_ref().unwrap();
            let mut infer = state.infer.clone();
            infer.mutable_map = Rc::new(std::sync::RwLock::new(
                state.infer.mutable_map.read().unwrap().clone(),
            ));
            (infer, state.cxt.clone(), state.global_macros.clone())
        })
    };
    infer.set_surface_query(super::surface::SurfaceQuery::hover_only(probe));
    let ast = parser::parser_with_macros(&preprocess(input), 24, &macros)
        .map(|(d, e, _, _)| (d, e)).unwrap();
    let mut c = cxt;
    for tm in ast.0 {
        let (_, _, nc) = infer.infer(&c, tm.clone()).unwrap();
        c = nc;
    }
    let s = infer.lsp_surface();
    // 只采到光标覆盖的那个 def 名
    let hits: Vec<_> = s.hover.iter().filter(|(sp, _, _)| sp.contains(probe)).collect();
    assert_eq!(hits.len(), 1, "只应采到光标处一条: {}", s.hover.len());
}

#[test]
fn dbg_probe() {
    let input = "def foo(x: Nat, y: Bool): Bool = y";
    let infer = elaborate_infer(input);
    println!("lsp_collect={} hover_len={} hq={:?}", infer.lsp_collect, infer.hover_table.len(), infer.hover_query);
    for (s, d, t) in infer.hover_table.iter().take(6) {
        println!("H {}..{} :: {t}", s.start_offset, s.end_offset);
    }
    let pos = input.find("foo").unwrap();
    println!("pos={pos} entry={:?}", infer.hover_entry_at(24, pos).map(|x| x.2.clone()));
}



/// 复杂度探针（单一来源）：所有数值打印到 stdout，供文档引用。
///
/// A) `lsp_surface()` 相对直接 `hover_table.clone()` 的额外开销（应 ≈ 0）
/// B) 采集开启（`lsp_collect = true`）相对关闭时的**整轮推断**开销
/// C) `match_to_decl` 的扫描成本随形状表条目数增长
///
/// 默认不跑（耗时 ~10s，且只打印不断言）：`cargo test --release --lib
/// L13_namespace::debug_test::complexity_probe -- --ignored --nocapture`。
#[test]
#[ignore = "复杂度探针：只打印不断言，需 --ignored 显式跑"]
fn complexity_probe() {
    fn per_call<F: FnMut()>(n: usize, mut f: F) -> f64 {
        f();
        let t = std::time::Instant::now();
        for _ in 0..n { f(); }
        t.elapsed().as_secs_f64() * 1e6 / n as f64
    }

    println!("--- A: lsp_surface() vs hover_table.clone() ---");
    for d in [20usize, 100, 400] {
        let mut src = String::from("def T(n: Nat): Type 0 =\n    match n {\n        case zero => Boolean\n        case succ(m) => Nat\n    }\n");
        for i in 0..d {
            src.push_str(&format!("def f{i}(n: Nat): Nat = n\n"));
        }
        let infer = elaborate_infer(&src);
        let a_snap = per_call(200, || { let _ = infer.lsp_surface(); });
        let a_clone = per_call(200, || { let _: Vec<(Span<()>, Span<()>, String)> = infer.hover_table.clone(); });
        println!(
            "D={d:<4} hover={:<5} | lsp_surface={a_snap:>7.2}µs  hover.clone={a_clone:>7.2}µs  delta={:+.2}µs",
            infer.hover_table.len(),
            a_snap - a_clone
        );
    }

    println!("--- B: lsp_collect on/off（整轮推断，D 个有注解 def）---");
    for d in [10usize, 50, 200] {
        let mut src = String::from("def T(n: Nat): Type 0 =\n    match n {\n        case zero => Boolean\n        case succ(m) => Nat\n    }\n");
        for i in 0..d {
            src.push_str(&format!("def g{i}(n: Nat): T n =\n    match n {{\n        case zero => true\n        case succ(m) => zero\n    }}\n"));
        }
        let on = per_call(5, || { let _ = elaborate_infer(&src); });
        // 关闭采集：同一份源码，把 gate 关掉重跑
        let off = per_call(5, || {
            let infer = elaborate_infer_no_collect(&src);
            let _ = infer;
        });
        println!("D={d:<4} on={on:>9.1}µs  off={off:>9.1}µs  ratio={:.3}x", on / off);
    }

    println!("--- C: 形状表扫描（match_to_decl 的线性扫描）---");
    for n in [1usize, 10, 50, 200] {
        let mut m: rustc_hash::FxHashMap<SmolStr, Vec<super::shape::MatchShape>> = Default::default();
        for i in 0..n {
            m.insert(
                SmolStr::new(format!("T{i}")),
                vec![super::shape::MatchShape {
                    pats: vec![
                        super::PatternDetail::Any(empty_span(SmolStr::new("_0")), None, Icit::Expl),
                        super::PatternDetail::Bind(empty_span(SmolStr::new("_0"))),
                    ],
                    env_len: 0,
                    source: super::shape::ShapeSource::FromValue,
                    type_level: true,
                }],
            );
        }
        // 直接对扫描本身计时：模拟一条命中/未命中的查找
        let probe: rustc_hash::FxHashMap<SmolStr, Vec<super::shape::MatchShape>> = m.clone();
        let per = per_call(2000, || {
            let mut hits = 0usize;
            for (_k, v) in probe.iter() {
                for s in v.iter() {
                    if s.type_level && s.pats.len() == 2 { hits += 1; }
                }
            }
            std::hint::black_box(hits);
        });
        println!("shapes={n:<4} full_scan={per:>8.2}µs  per_entry={:>8.3}µs", per / n as f64);
    }
}

/// 复杂度探针 D：**旧路径 vs 源码路径**的直接对照。
///
/// 旧路径 = `nf(quote_vtyp)`（`pretty_tm` 之前的那一步），对 `Val::Nat(k)` 会走
/// `quote_nat` 建 k 层 `SumCase` 链；源码路径 = `raw_pretty::def_type_from_source`（纯拼串）。
#[test]
#[ignore = "复杂度探针：只打印不断言，需 --ignored 显式跑"]
fn complexity_probe_old_vs_source() {
    fn per_call<F: FnMut()>(n: usize, mut f: F) -> f64 {
        f();
        let t = std::time::Instant::now();
        for _ in 0..n { f(); }
        t.elapsed().as_secs_f64() * 1e6 / n as f64
    }
    println!("--- D: 注解 `Box K`（K 个字面量）的渲染成本 ---");
    for k in [10u64, 100, 1000, 10000] {
        let src = format!("def Box(n: Nat): Type 0 = Nat\ndef big(n: Nat): Box {k} = n\n");
        // 源码路径：只拼串（不碰 Infer）
        let raw_src = parser::parser_with_macros(&preprocess(&src), 24, &Default::default())
            .map(|(d, _, _, _)| d).unwrap();
        // 从 AST 里取 big 的签名
        let mut params: Vec<(Span<SmolStr>, parser::syntax::Raw, Icit)> = Vec::new();
        let mut ret: Option<parser::syntax::Raw> = None;
        for d in raw_src.iter() {
            if let parser::syntax::Decl::Def { name, params: p, ret_type, .. } = d {
                if name.data.as_str() == "big" {
                    params = p.clone();
                    ret = Some(ret_type.clone());
                }
            }
        }
        let (params, ret) = (params, ret.expect("big"));
        let source_us = per_call(200, || {
            let _ = std::hint::black_box(super::raw_pretty::def_type_from_source(&params, &ret));
        });
        // 旧路径：真做一次 nf+quote（用 elaborate_infer 里同样的 Infer）
        let infer = elaborate_infer(&src);
        let cxt = { elaborate_infer_pair(&src) };
        let mut old_us = f64::NAN;
        if let Some((_inf, c)) = cxt {
            if let Some(e) = c.decl.get("big") {
                let typ_tm = e.3.clone();
                old_us = per_call(50, || {
                    let _ = std::hint::black_box(infer.nf(&c.decl, &c.env, &typ_tm));
                });
            }
        }
        println!("K={k:<6} source={source_us:>8.2}µs  old(nf+quote)={old_us:>12.1}µs");
    }
}

/// 复杂度探针 E：`lsp_surface()` 里**非 hover** 通道的拷贝成本（hover 只是其中之一）。
///
/// 关键：`lsp_surface()` 每次都给六个通道各做一次 clone。LSP 每按一个键都会调它
/// （hover/completion/inlay 三个请求各一次），所以要看清**每个通道**的量级。
#[test]
#[ignore = "复杂度探针：只打印不断言"]
fn complexity_probe_channels() {
    fn per_call<F: FnMut()>(n: usize, mut f: F) -> f64 {
        f();
        let t = std::time::Instant::now();
        for _ in 0..n { f(); }
        t.elapsed().as_secs_f64() * 1e6 / n as f64
    }
    println!("--- E: lsp_surface() 各通道拷贝成本 ---");
    for d in [20usize, 100, 400] {
        let mut src = String::from("def T(n: Nat): Type 0 =\n    match n {\n        case zero => Boolean\n        case succ(m) => Nat\n    }\n");
        for i in 0..d {
            src.push_str(&format!("def f{i}(n: Nat): Nat = n\n"));
        }
        let infer = elaborate_infer(&src);
        let full = per_call(200, || { let _ = infer.lsp_surface(); });
        let hover_only = per_call(200, || { let _: Vec<_> = infer.hover_table.clone(); });
        let comp_only = per_call(200, || { let _: Vec<_> = infer.completion_table.clone(); });
        let inlay_only = per_call(200, || { let _: Vec<_> = infer.inlay_hint_table.clone(); });
        // println_spans 是**迭代 + 分配**（不是 clone）
        let pl_only = per_call(200, || { let _ = infer.println_spans(); });
        println!(
            "D={d:<4} hover={:<5} comp={:<5} | full={full:>7.2}  hover={hover_only:>7.2} comp={comp_only:>7.2} inlay={inlay_only:>7.2} println={pl_only:>7.2}µs",
            infer.hover_table.len(),
            infer.completion_table.len(),
        );
    }
}

/// 复杂度探针 F：**我引入的一个真实回退** —— `lsp_surface()` 六通道全克隆。
///
/// 原 `hover_entries_owned` 只 clone hover 一张表；改成 `lsp_surface().hover` 后，
/// 每次请求都会连带克隆 completion / inlay / 迭代 println_jobs / errors / failed_decls。
/// 本探针把 completion 与 inlay 表填满，量化这个额外开销。
#[test]
#[ignore = "复杂度探针：只打印不断言"]
fn complexity_probe_full_vs_channel() {
    fn per_call<F: FnMut()>(n: usize, mut f: F) -> f64 {
        f();
        let t = std::time::Instant::now();
        for _ in 0..n { f(); }
        t.elapsed().as_secs_f64() * 1e6 / n as f64
    }
    println!("--- F: 单通道 clone vs lsp_surface() 全通道 ---");
    for d in [100usize, 400] {
        let mut src = String::from("def T(n: Nat): Type 0 =\n    match n {\n        case zero => Boolean\n        case succ(m) => Nat\n    }\n");
        for i in 0..d {
            src.push_str(&format!("def f{i}(n: Nat): Nat = n\n"));
        }
        let mut infer = elaborate_infer(&src);
        // 人为把 completion / inlay 填到与 hover 同量级（模拟真实 LSP 满载）
        for i in 0..infer.hover_table.len() {
            infer.completion_table.push((empty_span(()), SmolStr::new(format!("member{i}"))));
            infer.inlay_hint_table.push((i as u32, format!(": Nat{0}", i)));
        }
        let full = per_call(100, || { let _ = infer.lsp_surface(); });
        let ch = per_call(100, || { let _: Vec<_> = infer.hover_table.clone(); });
        println!(
            "D={d:<4} hover={:<5} comp={:<5} inlay={:<5} | lsp_surface={full:>8.2}  hover.clone={ch:>8.2}µs  ratio={:.2}x",
            infer.hover_table.len(), infer.completion_table.len(), infer.inlay_hint_table.len(),
            full / ch
        );
    }
}

/// 复杂度探针 G：`hover_entry_at` 的**线性扫描**成本（表大时的真实热点）。
///
/// `src/lib.rs` 的 hover 请求走 `hover_entry_owned` → `Infer::hover_entry_at`，
/// 它对全表做 `filter(contains)` + `min_by_key(span 宽度)`。表越大越慢。
/// 本探针对同一张表在不同大小下测 N 次查询。
#[test]
#[ignore = "复杂度探针：只打印不断言"]
fn complexity_probe_hover_scan() {
    fn per_call<F: FnMut()>(n: usize, mut f: F) -> f64 {
        f();
        let t = std::time::Instant::now();
        for _ in 0..n { f(); }
        t.elapsed().as_secs_f64() * 1e6 / n as f64
    }
    println!("--- G: hover_entry_at 线性扫描 ---");
    for d in [100usize, 400, 1600, 6400] {
        let mut src = String::from("def T(n: Nat): Type 0 =\n    match n {\n        case zero => Boolean\n        case succ(m) => Nat\n    }\n");
        for i in 0..d {
            src.push_str(&format!("def f{i}(n: Nat): Nat = n\n"));
        }
        let infer = elaborate_infer(&src);
        let n = infer.hover_table.len();
        // 光标打在中段某个条目上（最坏情形：扫描一半）
        let mid = n / 2;
        let off = infer.hover_table[mid].0.start_offset as usize;
        let t = per_call(200, || {
            let _ = infer.hover_entry_at(24, off);
        });
        println!("entries={n:<6} per_query={t:>8.2}µs  per_entry={:>7.3}ns", t * 1000.0 / n as f64);
    }
}

/// 复杂度探针 H：**整表克隆**的真实成本（goto / inlay / completion 的现状）。
///
/// `goto_definition_at` 与 `inlay_hint_at` 都要先 `hover_entries_owned()` /
/// `inlay_entries_owned()` 拿到**整表**（含全部 String），再自己扫。表大时这部分
/// 是纯拷贝开销。本探针量化它。
#[test]
#[ignore = "复杂度探针：只打印不断言"]
fn complexity_probe_table_clone_cost() {
    fn per_call<F: FnMut()>(n: usize, mut f: F) -> f64 {
        f();
        let t = std::time::Instant::now();
        for _ in 0..n { f(); }
        t.elapsed().as_secs_f64() * 1e6 / n as f64
    }
    println!("--- H: 整表克隆 vs 借用迭代（goto/inlay 的现状 vs 目标）---");
    for d in [400usize, 1600, 6400] {
        let mut src = String::from("def T(n: Nat): Type 0 =\n    match n {\n        case zero => Boolean\n        case succ(m) => Nat\n    }\n");
        for i in 0..d {
            src.push_str(&format!("def f{i}(n: Nat): Nat = n\n"));
        }
        let infer = elaborate_infer(&src);
        let n = infer.hover_table.len();
        let mid = n / 2;
        let off = infer.hover_table[mid].0.start_offset as usize;
        // 现状：克隆整表后再扫
        let clone_then_scan = per_call(200, || {
            let table = infer.lsp_hover();
            let r = table.iter().filter(|x| x.0.contains(off)).min_by_key(|x| x.0.end_offset - x.0.start_offset);
            std::hint::black_box(r.map(|x| x.2.len()));
        });
        // 目标：借用表直接扫（零拷贝）
        let borrow_scan = per_call(200, || {
            let r = infer.hover_table.iter().filter(|x| x.0.contains(off)).min_by_key(|x| x.0.end_offset - x.0.start_offset);
            std::hint::black_box(r.map(|x| x.2.len()));
        });
        println!(
            "entries={n:<6} clone+scan={clone_then_scan:>9.2}µs  borrow={borrow_scan:>6.2}µs  ratio={:.1}x",
            clone_then_scan / borrow_scan.max(0.001)
        );
    }
}


/// 复杂度探针 I：真实 example 规模下的 hover 查询成本（core prelude 可跑的例子）。
#[test]
#[ignore = "复杂度探针：只打印不断言"]
fn complexity_probe_real_sizes() {
    fn per_call<F: FnMut()>(n: usize, mut f: F) -> f64 {
        f();
        let t = std::time::Instant::now();
        for _ in 0..n { f(); }
        t.elapsed().as_secs_f64() * 1e6 / n as f64
    }
    println!("--- I: 真实 example 的表规模与查询成本 ---");
    for name in ["typeclass_complex.typort", "theorem_proving.typort", "alu.typort", "hdl_ops.typort"] {
        let p = format!("examples/{name}");
        let src = match std::fs::read_to_string(&p) { Ok(s) => s, Err(_) => continue };
        let infer = match std::panic::catch_unwind(|| elaborate_infer(&src)) {
            Ok(i) => i,
            Err(_) => { println!("{name:<24} <load failed (needs hdl prelude)>"); continue; }
        };
        let n = infer.hover_table.len();
        let off = if n > 0 { infer.hover_table[n / 2].0.start_offset as usize } else { 0 };
        let query = per_call(200, || { let _ = infer.hover_entry_at(24, off); });
        let clone = per_call(200, || { let _ = infer.lsp_hover(); });
        println!("{name:<24} hover={n:<6} query={query:>7.2}µs  clone={clone:>7.2}µs");
    }
}
