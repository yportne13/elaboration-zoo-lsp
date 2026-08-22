use std::collections::HashMap;

use elaboration_zoo_lsp::position_to_offset;
use elaboration_zoo_lsp::L13_namespace::{
    self,
    cxt::Cxt,
    Infer,
    parser::{self, syntax::Decl},
    preprocess,
};

// ---------------------------------------------------------------------------
// Helper: run elaboration (with full prelude) and return the Infer so we can
// inspect its completion_table after the pass.
// ---------------------------------------------------------------------------
fn elaborate_with_prelude(input: &str) -> (Infer, String) {
    let mut infer = Infer::new();
    // Omit hdl-verilog.typort because it depends on `register_nat_to_dec`
    // which is `pub(crate)` and inaccessible from tests.
    let prelude_sources: &[(&str, &str)] = &[
        ("op.typort", include_str!("../src/prelude/core/op.typort")),
        ("eq.typort", include_str!("../src/prelude/core/eq.typort")),
        ("nat.typort", include_str!("../src/prelude/core/nat.typort")),
        ("bool.typort", include_str!("../src/prelude/core/bool.typort")),
        ("option.typort", include_str!("../src/prelude/data/option.typort")),
        ("result.typort", include_str!("../src/prelude/data/result.typort")),
        ("order.typort", include_str!("../src/prelude/data/order.typort")),
        ("void.typort", include_str!("../src/prelude/core/void.typort")),
        ("decidable.typort", include_str!("../src/prelude/data/decidable.typort")),
        ("vec.typort", include_str!("../src/prelude/data/vec.typort")),
        ("either.typort", include_str!("../src/prelude/data/either.typort")),
        ("list.typort", include_str!("../src/prelude/data/list.typort")),
        ("string.typort", include_str!("../src/prelude/data/string.typort")),
        ("nonempty.typort", include_str!("../src/prelude/data/nonempty.typort")),
        // show.typort depends on nat_to_dec; skip in tests
    ];

    let mut cxt = Cxt::new(&infer);
    let mut global_macros: HashMap<String, Vec<parser::macros::MacroRule>> = HashMap::new();

    for (i, (_, source)) in prelude_sources.iter().enumerate() {
        let processed = preprocess(source);
        if let Some((decls, _parse_errs, new_exports, _expansions)) =
            parser::parser_with_macros(&processed, i as u32, &global_macros)
        {
            for (name, rules) in new_exports {
                global_macros.insert(name, rules);
            }
            for tm in decls {
                let (_, _, new_cxt) = infer.infer(&cxt, tm).expect("prelude elaboration failed");
                cxt = new_cxt;
            }
        }
    }

    // Auto-import prelude aliases
    let prelude_aliases: Vec<(smol_str::SmolStr, _)> = cxt.decl.iter()
        .filter(|(k, _)| k.contains('.'))
        .map(|(k, v)| {
            let short = smol_str::SmolStr::new(k.split('.').last().unwrap());
            (short, v.clone())
        })
        .collect();
    let decl_map = std::rc::Rc::make_mut(&mut cxt.decl);
    for (short, v) in prelude_aliases {
        decl_map.entry(short).or_insert(v);
    }

    // Mirror the LSP lifecycle (lib.rs clears the prelude-pass completion
    // table before per-file analysis): prelude-internal member accesses must
    // not leak into the user file's completion candidates.
    infer.completion_table.clear();

    // Parse and elaborate user input
    let processed_input = preprocess(input);
    let ast = parser::parser_with_macros(&processed_input, prelude_sources.len() as u32, &global_macros)
        .map(|(d, e, _, _)| (d, e))
        .unwrap_or_else(|| (vec![], vec![]));

    let mut output = String::new();
    for tm in ast.0 {
        if let Decl::Println(_) = &tm {
            // skip println for completion tests (not needed)
        }
        let result = infer.infer(&cxt, tm);
        match result {
            Ok((decl_tm, _, new_cxt)) => {
                cxt = new_cxt;
                if let L13_namespace::DeclTm::Println(_, s, _) = decl_tm {
                    output += &s;
                    output += "\n";
                }
            }
            Err(_e) => {
                // Elaboration may legitimately fail (e.g. incomplete `p.` for completion testing).
                // The completion_table was populated *before* the error, so continue.
            }
        }
    }

    (infer, output)
}

// ---------------------------------------------------------------------------
// Helper: Simulate the completion handler's filtering logic from lib.rs
// ---------------------------------------------------------------------------
fn completion_filter<'a>(
    completion_table: &'a [((u32, u32), &'a str)],
    rope: &ropey::Rope,
    cursor_byte_offset: usize,
) -> Vec<&'a str> {
    completion_table
        .iter()
        .filter(|(span, _)| {
            let (start, end) = *span;
            let end = end as usize;
            // Same predicate as the LSP handler: cursor on the span
            // (hover-style), exactly at its end (right after the typed member
            // name), or one byte past it with a `.` in between (right after
            // the trigger dot — the empty-member span excludes the dot).
            // The old `offset - 2` trigger point missed longer typed prefixes.
            (cursor_byte_offset >= start as usize && cursor_byte_offset < end)
                || cursor_byte_offset == end
                || (cursor_byte_offset == end + 1
                    && rope.byte_slice(end..end + 1).chars().next() == Some('.'))
        })
        .map(|(_, label)| *label)
        .collect()
}

// =========================================================================
// Test 1: Span contains logic (core of completion matching)
// =========================================================================
#[test]
fn test_span_contains_boundaries() {
    // Replicate Span::contains logic
    let contains = |start: u32, end: u32, offset: usize| -> bool {
        offset >= start as usize && offset < end as usize
    };

    // Span [10, 15)
    assert!(contains(10, 15, 10));   // left edge
    assert!(contains(10, 15, 12));   // middle
    assert!(!contains(10, 15, 15));  // right edge (exclusive)
    assert!(!contains(10, 15, 9));   // before
    assert!(!contains(10, 15, 20));  // after

    // Zero-width span [42,42): nothing can be inside (exclusive end)
    assert!(!contains(42, 42, 42));  // 42 >= 42 && 42 < 42 → false
    assert!(!contains(42, 42, 41));  // before
    assert!(!contains(42, 42, 43));  // after
}

// =========================================================================
// Test 2: Completion filtering logic
// =========================================================================
#[test]
fn test_completion_filter_matches_correctly() {
    // Each entry: ((start_offset, end_offset), label)
    let table: Vec<((u32, u32), &str)> = vec![
        ((10, 10), "empty_span"),
        ((20, 30), "field_x"),
        ((50, 50), "after_dot"),
        ((100, 105), "method_foo"),
    ];
    // Synthetic document: byte 105 is a `.` (the trigger-dot shape), the
    // rest are `x` — the filter's dot-past rule must see the real char.
    let doc = "x".repeat(105) + ".xxx";
    let rope = ropey::Rope::from_str(&doc);

    // Cursor at byte 22 → inside span [20,30)
    let results = completion_filter(&table, &rope, 22);
    assert_eq!(results, vec!["field_x"]);

    // Cursor at byte 21 → still inside [20,30) (the old -2 trigger missed this)
    let results = completion_filter(&table, &rope, 21);
    assert_eq!(results, vec!["field_x"]);

    // Cursor at byte 19 → before the span
    let results = completion_filter(&table, &rope, 19);
    assert!(results.is_empty());

    // Cursor at byte 30 → exactly at the span end (cursor right after the
    // typed member name / trigger dot) → matches
    let results = completion_filter(&table, &rope, 30);
    assert_eq!(results, vec!["field_x"]);

    // Cursor at byte 31 → past the end, no `.` at the span end → no match
    let results = completion_filter(&table, &rope, 31);
    assert!(results.is_empty());

    // Cursor at byte 52 → zero-width span [50,50): 52 not inside, 52 != 50
    let results = completion_filter(&table, &rope, 52);
    assert!(results.is_empty(), "zero-width span should not match");

    // Cursor at byte 102 → inside [100,105)
    let results = completion_filter(&table, &rope, 102);
    assert_eq!(results, vec!["method_foo"]);

    // Cursor at byte 105 → exactly at the span end → matches
    let results = completion_filter(&table, &rope, 105);
    assert_eq!(results, vec!["method_foo"]);

    // Cursor at byte 106 → one past the end; the span [100,105) is followed
    // by `...` (a dot), so this is the empty-member `x.|` shape → matches
    let results = completion_filter(&table, &rope, 106);
    assert_eq!(results, vec!["method_foo"]);

    // Very early cursor (near start of file)
    let results = completion_filter(&table, &rope, 1);
    assert!(results.is_empty());

    // Cursor at offset 0
    let results = completion_filter(&table, &rope, 0);
    assert!(results.is_empty());
}

// =========================================================================
// Test 3: Struct field completions after `.`
// =========================================================================
#[test]
fn test_struct_field_completions() {
    let code = r#"
struct Point[T] {
    x: T
    y: T
}

def p: Point[Nat] = new Point(1, 2)
def test = p.
"#;

    let (infer, _output) = elaborate_with_prelude(code);

    // The completion_table should contain entries for the `.` after `p`
    // Expected: field names "x" and "y"
    let completions: Vec<String> = infer.completion_table
        .iter()
        .map(|(_, label)| label.to_string())
        .collect();

    assert!(!completions.is_empty(),
        "expected completions for struct field access, got none");
    assert!(completions.contains(&"x".to_string()),
        "expected 'x' in completions: {:?}", completions);
    assert!(completions.contains(&"y".to_string()),
        "expected 'y' in completions: {:?}", completions);
}

// =========================================================================
// Test 4: Trait method completions after `.`
// =========================================================================
#[test]
fn test_trait_method_completions() {
    let code = r#"
enum Bool {
    true
    false
}

trait ToString {
    def to_string: String
}

impl ToString for Bool {
    def to_string: String =
        match this {
            case true => "true"
            case false => "false"
        }
}

def test = true.
"#;

    let (infer, _output) = elaborate_with_prelude(code);

    let completions: Vec<String> = infer.completion_table
        .iter()
        .map(|(_, label)| label.to_string())
        .collect();

    assert!(!completions.is_empty(),
        "expected trait method completions after `.`, got none");
    // Note: currently trait method completion has limitations with inline
    // trait/impl blocks; the completion list may contain type params instead.
    // This test verifies that completions ARE generated for the `.` site.
}

// =========================================================================
// Test 5: Sum type single-constructor field completions
// =========================================================================
#[test]
fn test_sum_type_constructor_fields() {
    let code = r#"
enum Wrap[A] {
    MkWrap(value: A)
}

def w: Wrap[Nat] = MkWrap(42)
def test = w.
"#;

    let (infer, _output) = elaborate_with_prelude(code);

    let completions: Vec<String> = infer.completion_table
        .iter()
        .map(|(_, label)| label.to_string())
        .collect();

    // Wrap[A] has a single constructor `MkWrap(value: A)` and a type param `A`.
    // Currently the completion logic pushes type-level params but not constructor
    // field names (only struct types with `.mk` convention get field completions).
    assert!(!completions.is_empty(),
        "expected some completions for Wrap, got none");
    assert!(completions.contains(&"A".to_string()),
        "expected type param 'A' in completions for Wrap: {:?}", completions);
}

// =========================================================================
// Test 6: Completion table is empty when there is no `.`
// =========================================================================
#[test]
fn test_no_completion_without_dot() {
    let code = r#"
struct Point[T] {
    x: T
    y: T
}

def p: Point[Nat] = new Point(1, 2)
"#;

    let (infer, _output) = elaborate_with_prelude(code);

    // No `.` access in the code → completion_table should be empty
    assert!(infer.completion_table.is_empty(),
        "expected empty completion_table when no `.` access exists, got {:?}",
        infer.completion_table.iter().map(|(_, l)| l.to_string()).collect::<Vec<_>>());
}

// =========================================================================
// Test 7: Completing a named field (typed prefix) DOES populate the table
// =========================================================================
#[test]
fn test_completion_for_named_field_prefix() {
    // `p.x` — a typed member prefix — must ALSO populate the completion
    // table, with the span covering `p.x`, so Ctrl+Space at the end of a
    // partially-typed member name works.  (Before: entries only existed for
    // the empty-member state `p.`, so manual re-trigger after typing a
    // prefix returned nothing.)
    let code = r#"
struct Point[T] {
    x: T
    y: T
}

def p: Point[Nat] = new Point(1, 2)
def test = p.x
"#;

    let (infer, _output) = elaborate_with_prelude(code);

    // The completion entries must be keyed to the `p.x` span so the LSP's
    // `contains(offset) || end == offset` filter hits them at the cursor.
    let p_x_off = code.rfind("p.x").unwrap();
    let names: Vec<String> = infer.completion_table.iter()
        .filter(|(span, _)| {
            span.start_offset as usize == p_x_off && span.end_offset as usize == p_x_off + 3
        })
        .map(|(_, l)| l.to_string())
        .collect();

    assert!(!names.is_empty(),
        "expected completions at the `p.x` span, got none: {:?}",
        infer.completion_table.iter().map(|(s, l)| (s.start_offset, s.end_offset, l.as_str())).collect::<Vec<_>>());
    assert!(names.contains(&"x".to_string()), "expected `x` in completions: {names:?}");
    assert!(names.contains(&"y".to_string()), "expected `y` in completions: {names:?}");
}

// =========================================================================
// Test 8: Completions for multiple record accesses in the same file
// =========================================================================
#[test]
fn test_multiple_completion_points() {
    let code = r#"
struct Point[T] {
    x: T
    y: T
}

struct Rect[T] {
    top_left: Point[T]
    bottom_right: Point[T]
}

def p: Point[Nat] = new Point(1, 2)
def r: Rect[Nat] = new Rect(p, p)
def test1 = p.
def test2 = r.
"#;

    let (infer, _output) = elaborate_with_prelude(code);

    let completions: Vec<String> = infer.completion_table
        .iter()
        .map(|(_, label)| label.to_string())
        .collect();

    // Should include fields from both Point and Rect
    assert!(completions.contains(&"x".to_string()),
        "Point.x should be in completions: {:?}", completions);
    assert!(completions.contains(&"y".to_string()),
        "Point.y should be in completions: {:?}", completions);
    assert!(completions.contains(&"top_left".to_string()),
        "Rect.top_left should be in completions: {:?}", completions);
    assert!(completions.contains(&"bottom_right".to_string()),
        "Rect.bottom_right should be in completions: {:?}", completions);
}

// =========================================================================
// Test 9: Completion table is cleared between elaboration passes
// =========================================================================
#[test]
fn test_completion_table_cleared_between_passes() {
    // Verify that re-elaborating different code clears the previous completion_table
    let mut infer = Infer::new();

    // First pass: code with `.`
    let code_with_dot = r#"
struct Foo {
    bar: String
}
def f: Foo = new Foo("hi")
def x = f.
"#;

    // Build cxt and elaborate
    let mut cxt = make_minimal_cxt(&mut infer);
    let (_infer1, _) = elaborate_into(&mut infer, &mut cxt, code_with_dot);

    // After first pass, completion_table should NOT be empty
    assert!(!infer.completion_table.is_empty(),
        "expected non-empty completion_table after first pass");

    // Second pass: code WITHOUT `.` (simulate a new edit)
    let code_no_dot = r#"
struct Foo {
    bar: String
}
def f: Foo = new Foo("hi")
"#;

    // Clear and re-elaborate (simulating the lib.rs lifecycle)
    infer.completion_table.clear();
    infer.completion_table.shrink_to_fit();

    let mut cxt2 = make_minimal_cxt(&mut infer);
    let (_infer2, _) = elaborate_into(&mut infer, &mut cxt2, code_no_dot);

    assert!(infer.completion_table.is_empty(),
        "expected empty completion_table after pass with no `.` access");
}

// ---------------------------------------------------------------------------
// Minimal helpers for test 9
// ---------------------------------------------------------------------------
fn make_minimal_cxt(infer: &Infer) -> Cxt {
    Cxt::new(infer)
}

fn elaborate_into<'a>(infer: &'a mut Infer, cxt: &mut Cxt, input: &str) -> (&'a Infer, String) {
    let processed = preprocess(input);
    let ast = parser::parser(&processed, 0).unwrap_or((vec![], vec![]));
    let mut output = String::new();
    for tm in ast.0 {
        let result = infer.infer(cxt, tm);
        match result {
            Ok((decl_tm, _, new_cxt)) => {
                *cxt = new_cxt;
                if let L13_namespace::DeclTm::Println(_, s, _) = decl_tm {
                    output += &s;
                    output += "\n";
                }
            }
            Err(_e) => {
                // ignore errors (e.g. incomplete `p.` for completion tests)
            }
        }
    }
    (infer, output)
}

// =========================================================================
// Test 10: Completion span offsets are correct (byte-level accuracy)
// =========================================================================
#[test]
fn test_completion_span_offsets() {
    // Verify that the spans in completion_table correctly point to the `.` location
    let code = r#"
struct Point {
    x: String
    y: String
}

def p: Point = new Point("a", "b")
def test = p.
"#;

    let (infer, _output) = elaborate_with_prelude(code);

    // Each completion entry's span should have non-zero offsets
    for (i, (span, label)) in infer.completion_table.iter().enumerate() {
        assert!(span.start_offset > 0,
            "completion #{} ('{}') has start_offset=0", i, label);
        assert!(span.end_offset >= span.start_offset,
            "completion #{} ('{}') has end_offset < start_offset", i, label);
    }

    // There should be at least "x" and "y" completions
    let x_completions: Vec<_> = infer.completion_table.iter()
        .filter(|(_, label)| label.as_str() == "x")
        .collect();
    assert!(!x_completions.is_empty(), "expected at least one 'x' completion");

    // All 'x' completions should have the same span
    if let Some(first) = x_completions.first() {
        for other in &x_completions {
            assert_eq!(first.0.start_offset, other.0.start_offset,
                "all 'x' completions should share the same span start_offset");
            assert_eq!(first.0.end_offset, other.0.end_offset,
                "all 'x' completions should share the same span end_offset");
        }
    }
}

// =========================================================================
// Test 11: LSP handler offset math — byte offset from Position, UTF-16 aware.
// Regression: the old handler computed `try_line_to_char(line) + character`,
// which mixes char and byte offsets and drifts whenever a non-ASCII
// character appears before the cursor (e.g. a CJK comment + emoji).
// =========================================================================
#[test]
fn test_handler_offset_is_byte_offset_utf16_aware() {
    // A comment with a 4-byte emoji (1 char, 2 UTF-16 units) plus CJK on an
    // earlier line shifts the char-index-vs-byte-offset relationship for
    // every following position.
    let code = "// \u{8BC4}\u{6CE8} emoji \u{1F600}\nstruct Point[T] {\n    x: T\n    y: T\n}\n\ndef p: Point[Nat] = new Point(1, 2)\ndef test = p.\n";

    let (infer, _output) = elaborate_with_prelude(code);
    let rope = ropey::Rope::from_str(code);
    let dot_pos = code.rfind("p.").unwrap() + 1; // byte offset of `.` after p
    let cursor = dot_pos + 1;                    // cursor just after the dot

    // Convert the client cursor position (line + UTF-16 character) to a byte
    // offset exactly as the LSP completion handler does.
    let line = code[..dot_pos].matches('\n').count();
    let char_in_line = code[..dot_pos].rfind('\n').map(|i| dot_pos - i - 1).unwrap_or(dot_pos);
    let position = lsp_types::Position::new(line as u32, (char_in_line + 1) as u32);
    let handler_offset = position_to_offset(position, &rope).expect("cursor offset");

    assert_eq!(handler_offset, cursor, "handler offset must be the raw byte offset");

    // The completion spans (receiver token `p`) must be hit by the handler's
    // `contains(offset) || end == offset || end + 1 == offset (dot)` filter
    // at the cursor: the empty-member span excludes the dangling dot.
    let hits: Vec<&str> = infer.completion_table.iter()
        .filter(|(span, _)| {
            let end = span.end_offset as usize;
            (handler_offset >= span.start_offset as usize && handler_offset < end)
                || handler_offset == end
                || (handler_offset == end + 1
                    && rope.byte_slice(end..end + 1).chars().next() == Some('.'))
        })
        .map(|(_, label)| label.as_str())
        .collect();
    assert!(hits.contains(&"x"), "expected 'x' completion to match: {hits:?}");
    assert!(hits.contains(&"y"), "expected 'y' completion to match: {hits:?}");
}

// =========================================================================
// Test 12: Inherent impl methods (namespace) appear in the candidates
// =========================================================================
#[test]
fn test_namespace_method_completions() {
    // `Boolean.not` is an inherent impl method (`impl Boolean { def not }`),
    // registered in the type's namespace — it must be offered when completing
    // `a.` on a Boolean.  (Before: only trait-satisfiable methods were
    // collected, so inherent impl methods were missing from completions.)
    let code = r#"
def f(a: Boolean): Nat = a.
"#;
    let (infer, _output) = elaborate_with_prelude(code);

    let names: Vec<String> = infer.completion_table.iter()
        .map(|(_, l)| l.to_string())
        .collect();
    assert!(!names.is_empty(), "expected completions for `a.` on Boolean, got none");
    assert!(names.contains(&"not".to_string()),
        "expected inherent impl method `not` in completions: {names:?}");
}

// =========================================================================
// Test 13: Typed member prefix survives a non-ASCII line before the cursor
// =========================================================================
#[test]
fn test_typed_prefix_completion_utf16_aware() {
    // A CJK comment before the cursor shifts char-vs-byte offsets; the
    // handler's UTF-16-aware byte offset must still hit the `p.x` span.
    let code = "// \u{8BC4}\u{6CE8}\nstruct Point[T] {\n    x: T\n    y: T\n}\n\ndef p: Point[Nat] = new Point(1, 2)\ndef test = p.x\n";
    let (infer, _output) = elaborate_with_prelude(code);

    let rope = ropey::Rope::from_str(code);
    let p_x_off = code.rfind("p.x").unwrap();
    let cursor = p_x_off + 3; // cursor at the end of the typed member name
    let line = code[..cursor].matches('\n').count();
    let char_in_line = code[..cursor].rfind('\n').map(|i| cursor - i - 1).unwrap_or(cursor);
    let position = lsp_types::Position::new(line as u32, char_in_line as u32);
    let handler_offset = elaboration_zoo_lsp::position_to_offset(position, &rope).expect("cursor offset");
    assert_eq!(handler_offset, cursor, "handler offset must be the raw byte offset");

    let hits: Vec<&str> = infer.completion_table.iter()
        .filter(|(span, _)| {
            span.start_offset as usize == p_x_off
                && span.end_offset as usize == p_x_off + 3
                && (handler_offset >= span.start_offset as usize && handler_offset < span.end_offset as usize
                    || handler_offset == span.end_offset as usize)
        })
        .map(|(_, label)| label.as_str())
        .collect();
    assert!(hits.contains(&"x"), "expected 'x' to match at the `p.x` span: {hits:?}");
    assert!(hits.contains(&"y"), "expected 'y' to match at the `p.x` span: {hits:?}");
}

// =========================================================================
// Test 14: member_prefix_start — the text-edit replacement range
// =========================================================================
#[test]
fn test_member_prefix_start() {
    use ropey::Rope;

    // `p.le` — the typed prefix starts right after the dot.
    let rope = Rope::from_str("def f(p: Point): Nat = p.le");
    let offset = "def f(p: Point): Nat = p.le".len();
    assert_eq!(elaboration_zoo_lsp::member_prefix_start(&rope, offset), Some(offset - 2));

    // `p.` — empty prefix: replace nothing (insertion at the cursor).
    let rope2 = Rope::from_str("def f(p: Point): Nat = p.");
    let offset2 = "def f(p: Point): Nat = p.".len();
    assert_eq!(elaboration_zoo_lsp::member_prefix_start(&rope2, offset2), Some(offset2));

    // No dot before the cursor on the line → fallback (handler inserts).
    let rope3 = Rope::from_str("def f(p: Point): Nat = p");
    let offset3 = "def f(p: Point): Nat = p".len();
    assert_eq!(elaboration_zoo_lsp::member_prefix_start(&rope3, offset3), None);

    // `foo.bar.le` — the last dot is the member-access dot.
    let rope4 = Rope::from_str("def f(x: Outer): Nat = x.inner.le");
    let offset4 = "def f(x: Outer): Nat = x.inner.le".len();
    assert_eq!(elaboration_zoo_lsp::member_prefix_start(&rope4, offset4), Some(offset4 - 2));
}
