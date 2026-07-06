//! # Parser Error-Reporting & Error-Recovery Test Suite
//!
//! This file contains structured test cases for upgrading the L13 (Typort) parser
//! to support chumsky-like advanced error reporting and recovery.
//!
//! ## Organization
//!
//! Each top-level `mod` corresponds to a category of syntax errors.
//! Every test case documents:
//!
//! - **What** the erroneous input is
//! - **Why** it is tricky (edge cases, recovery challenges, diagnostic quality)
//! - **Expected properties** — not exact error texts (those will change as the
//!   parser improves), but invariants such as "at least one error is reported",
//!   "no crash", "partial AST is still produced", etc.
//!
//! ## Upgrade Checklist
//!
//! As you improve the parser, make each test case pass and then annotate it with
//! more precise assertions (expected error count, expected context labels,
//! expected recovery results, etc.).

use elaboration_zoo_lsp::L13_namespace::parser::{parser, parser_test, IError};
use elaboration_zoo_lsp::L13_namespace::parser::syntax::{Decl, Raw};

// ---------------------------------------------------------------------------
// Helper
// ---------------------------------------------------------------------------

/// Assert that parsing `input` as a full file produces at least one parse error.
fn assert_parse_errors(input: &str) -> Vec<IError> {
    let result = parser(input, 0);
    assert!(result.is_some(), "parser should never return None for valid UTF-8 input");
    let (decls, errors) = result.unwrap();
    assert!(!errors.is_empty(),
        "expected at least one parse error in:\n---\n{}---", input);
    errors
}

/// Assert that parsing `input` as a full file succeeds without *parse* errors.
/// (Elaboration/type errors are not checked here.)
fn assert_parse_ok(input: &str) -> (Vec<Decl>, Vec<IError>) {
    let result = parser(input, 0);
    assert!(result.is_some(), "parser returned None for valid UTF-8 input");
    let (decls, errors) = result.unwrap();
    if !errors.is_empty() {
        panic!("expected zero parse errors, got {}:\n{:?}\n---input---\n{}---",
            errors.len(), errors, input);
    }
    (decls, errors)
}

/// Assert that parsing `input` as a raw expression produces at least one error.
fn assert_raw_errors(input: &str) -> Vec<IError> {
    let result = parser_test(input, 0);
    assert!(result.is_some(), "parser_test should never return None for valid UTF-8 input");
    let (raws, errors) = result.unwrap();
    assert!(!errors.is_empty(),
        "expected at least one expression-level parse error in:\n---\n{}---", input);
    errors
}

/// Assert that parsing `input` as a raw expression succeeds (errors optional).
/// Returns the parsed raws and errors.
fn assert_raw_ok(input: &str) -> (Vec<Raw>, Vec<IError>) {
    let result = parser_test(input, 0);
    assert!(result.is_some(), "parser_test returned None");
    result.unwrap()
}

// ===========================================================================
// Category 1: Token-level / Lexer Errors
// ===========================================================================
//
// The lexer is built on `parser_lib::Parser` (non-resilient).  If the lexer
// itself fails, the parser never starts.  A chumsky-like upgrade should make
// the lexer *error-tolerant* as well, producing `ErrToken` placeholders so
// the parser can still run and collect multiple diagnostics.
//
mod token_errors {
    use super::*;

    /// Unknown / unsupported characters should not crash the lexer.
    /// The lexer currently emits `ErrToken` for them, which is good.
    #[test]
    fn unknown_symbols() {
        // `@`, `#`, `$`, `?` are not Typort tokens — the lexer should skip them
        // or turn them into ErrToken so parsing continues.
        let input = r#"
def foo(x: Nat): Nat = x @ # $ ?
"#;
        let errors = assert_parse_errors(input);
        // UPGRADE: should produce at least 1 error about unexpected char `@`
        assert!(errors.len() >= 1, "expected at least 1 lexer error, got {}", errors.len());
    }

    /// Unterminated string literal — the lexer should not hang or crash.
    #[test]
    fn unterminated_string() {
        let input = r#"
def msg: String = "hello world
"#;
        let errors = assert_parse_errors(input);
        // UPGRADE: error should mention unterminated string literal
        assert!(errors.len() >= 1, "expected error for unterminated string");
    }

    /// Empty file (no declarations) — should parse to an empty Vec, not crash.
    #[test]
    fn empty_file() {
        let input = "";
        let result = parser(input, 0);
        assert!(result.is_some(), "empty file should parse");
        let (decls, errors) = result.unwrap();
        // Currently the parser wraps everything in many1_sep(EndLine),
        // so an empty file returns the remaining input, which triggers
        // an "expected EndLine" error.  This is a minor nuisance.
        // UPGRADE: empty file should be valid (zero declarations, zero errors).
        assert!(decls.is_empty(), "empty file should yield zero declarations");
    }

    /// Whitespace-only / blank lines only.
    #[test]
    fn whitespace_only() {
        let input = "   \n\n  \n  ";
        let result = parser(input, 0);
        assert!(result.is_some(), "whitespace-only file should parse");
    }

    /// File that contains only comments (after preprocess).
    /// The preprocessor strips comments, so lines become blank.
    #[test]
    fn comments_only() {
        let input = "// this is a comment\n// another one\n";
        let result = parser(input, 0);
        assert!(result.is_some(), "comments-only file should parse");
    }
}

// ===========================================================================
// Category 2: Declaration-Level Errors
// ===========================================================================
//
// These errors occur when the top-level declaration parser cannot match any
// known declaration form.  The current `skip_until_decl` recovery attempts
// to find the next newline + keyword boundary.
//
mod decl_errors {
    use super::*;

    /// Missing the `def` keyword for a function definition.
    #[test]
    fn missing_def_keyword() {
        let input = r#"
foo(x: Nat): Nat = x
"#;
        let errors = assert_parse_errors(input);
        // UPGRADE: error should say "expected `def`, `enum`, `struct`, …"
        //          and show the span at `foo`.
        assert!(!errors.is_empty(), "missing def keyword should be an error");
    }

    /// `def` with no name.
    #[test]
    fn def_missing_name() {
        let input = r#"
def (x: Nat): Nat = x
"#;
        let errors = assert_parse_errors(input);
        assert!(!errors.is_empty(), "def without name should error");
    }

    /// `def` with name but missing `=`.
    #[test]
    fn def_missing_eq() {
        let input = r#"
def foo(x: Nat): Nat x
"#;
        let errors = assert_parse_errors(input);
        assert!(!errors.is_empty(), "def without `=` should error");
        // Grouped (Eq, EndLine, p_raw) tuple: = fails → body never parsed.
        // Single error Expect(Eq), no secondary error at 0-0.
    }
	
	    /// `def` with name but body is blank / ends prematurely.
    #[test]
    fn def_missing_body() {
        let input = r#"
def foo(x: Nat): Nat =
"#;
        let errors = assert_parse_errors(input);
        assert!(!errors.is_empty(), "def without body should error");
    }

    /// `def` with name, `=`, but expression is on next line without valid
    /// continuation (e.g. missing EndLine before next decl).
    #[test]
    fn def_body_unexpected_eof() {
        let input = "def foo: Nat = ";
        let result = parser(input, 0);
        // Should not crash; should produce an error.
        assert!(result.is_some(), "should not crash on EOF inside def body");
        let (_decls, errors) = result.unwrap();
        assert!(!errors.is_empty(), "def body at EOF should error");
    }

    /// `struct` without any fields.
    #[test]
    fn struct_empty_body() {
        let input = r#"
struct Empty {

}
"#;
        let (decls, errors) = assert_parse_ok(input);
        // An empty struct is actually valid Typort?  Let's check.
        // If it is valid, no error; if it isn't, one should appear.
        // UPGRADE: decide if empty structs are valid or a warning.
    }

    /// `struct` with a field that has no type.
    #[test]
    fn struct_field_missing_type() {
        let input = r#"
struct Point {
    x
}
"#;
        let errors = assert_parse_errors(input);
        assert!(!errors.is_empty(), "struct field without type should error");
    }

    /// `enum` with no constructors.
    #[test]
    fn enum_empty_body() {
        let input = r#"
enum Empty {

}
"#;
        // This might be valid (empty enum = uninhabited type).
        // UPGRADE: this should be valid; no error expected.
    }

    /// `enum` with a constructor that has no type annotation but has a body.
    #[test]
    fn enum_ctor_bad_syntax() {
        let input = r#"
enum Foo {
    Bar(x)
}
"#;
        // `Bar(x)` is actually valid if `x` is a shorthand for field `x: T`.
        // Let's test with truly bad syntax:
        let input = r#"
enum Foo {
    Bar :
}
"#;
        let errors = assert_parse_errors(input);
        assert!(!errors.is_empty(), "enum ctor with `:` but no type should error");
    }

    /// `package` path missing component.
    #[test]
    fn package_empty_path() {
        let input = r#"
package
"#;
        let errors = assert_parse_errors(input);
        assert!(!errors.is_empty(), "package with empty path should error");
    }

    /// `import` missing path.
    #[test]
    fn import_missing_path() {
        let input = r#"
import
"#;
        let errors = assert_parse_errors(input);
        assert!(!errors.is_empty(), "import with missing path should error");
    }

    /// Junk text that is not a valid declaration.
    #[test]
    fn invalid_declaration_keyword() {
        let input = r#"
xyzzy foo bar
"#;
        let errors = assert_parse_errors(input);
        assert!(!errors.is_empty(), "nonsense should produce a parse error");
    }

    /// Declaration where the error is in the second declaration —
    /// tests that recovery from the first error still parses the rest.
    #[test]
    fn error_then_ok_decl() {
        let input = r#"
xyzzy bad decl

def ok(x: Nat): Nat = x
"#;
        let result = parser(input, 0);
        assert!(result.is_some(), "should recover from bad decl");
        let (decls, errors) = result.unwrap();
        assert!(!errors.is_empty(), "bad decl must produce errors");
        // The `def ok` should still have been parsed.
        let has_ok = decls.iter().any(|d| matches!(d, Decl::Def { name, .. } if name.data == "ok"));
        assert!(has_ok, "parser should recover and still parse `def ok`");
    }
}

// ===========================================================================
// Category 3: Expression-Level Errors
// ===========================================================================
//
// These test the `p_raw` (expression) parser via `parser_test`.
// UPGRADE: expressions should get labelled errors like "in expression",
//          "in atom", "in function application", etc.
//
mod expr_errors {
    use super::*;

    /// Mismatched parentheses — extra `)`.
    #[test]
    fn extra_rparen() {
        let input = r#"(a + b))"#;
        let errors = assert_raw_errors(input);
        assert!(errors.len() >= 1, "extra ')' should produce an error");
    }

    /// Mismatched brackets — missing `]`.
    #[test]
    fn missing_rbracket() {
        let input = r#"[x : Nat"#;
        let errors = assert_raw_errors(input);
        assert!(!errors.is_empty(), "unclosed '[' should produce an error");
    }

    /// Incomplete lambda — no `=>`.
    #[test]
    /// Incomplete lambda — `x =>` with no body expression.
    /// After Cut+p_raw fix: parsed as Lam(x, Hole), 1 error (expected expression).
    #[test]
    fn incomplete_lambda() {
        let input = r#"x =>"#;
        let errors = assert_raw_errors(input);
        assert!(!errors.is_empty(), "lambda without body should error");
	        // After fix: single error about expected expression (not "expected newline")
	    }
	
	    /// Lambda with implicit binder but missing body.
    #[test]
    fn incomplete_implicit_lambda() {
        let input = r#"[x] =>"#;
        let errors = assert_raw_errors(input);
        assert!(!errors.is_empty(), "implicit lambda without body should error");
    }

    /// Incomplete application — operator at end of line.
    #[test]
    fn dangling_operator() {
        let input = r#"a +"#;
        let errors = assert_raw_errors(input);
        assert!(!errors.is_empty(), "trailing operator should error");
        // After fixes: error is "expected atom" at op.end_offset (right after +)
    }

    /// Empty parentheses — `()` used as an expression.
    #[test]
    fn empty_parens() {
        let input = r#"()"#;
        let errors = assert_raw_errors(input);
        // `()` might be a unit type/value if the language supports it.
        // UPGRADE: if unit is not supported, error; otherwise OK.
    }

    /// Unknown / undefined variable reference (should not be a *parse* error,
    /// but a type/elaboration error — the parser should accept any identifier).
    #[test]
    fn unknown_var_is_not_parse_error() {
        let input = r#"foobarbazquux"#;
        let (raws, errors) = assert_raw_ok(input);
        // Parser should accept any identifier; errors come later from elaboration.
        assert!(errors.is_empty(), "unknown var should not be a parse error");
        assert_eq!(raws.len(), 1, "should parse one expression");
    }

    /// Expression with hole only — `_` is valid.
    #[test]
    fn hole_expression() {
        let input = r#"_"#;
        let (raws, errors) = assert_raw_ok(input);
        assert!(errors.is_empty(), "hole `_` should be a valid expression");
        assert_eq!(raws.len(), 1);
    }

    /// Nested parentheses mismatched: `((a + b)`.
    #[test]
    fn nested_mismatched_parens() {
        let input = r#"((a + b)"#;
        let errors = assert_raw_errors(input);
        assert!(!errors.is_empty(), "unmatched '(' should error");
        // UPGRADE: error span should point at the unmatched opening paren
        //          and say "expected ')'"
    }
}

// ===========================================================================
// Category 4: Type-Level Errors
// ===========================================================================
//
// Pi types, universes, type annotations.
//
mod type_errors {
    use super::*;

    /// Missing codomain after `->`.
    #[test]
    fn pi_missing_codomain() {
        let input = r#"(x : Nat) ->"#;
        let errors = assert_raw_errors(input);
        assert!(!errors.is_empty(), "Pi type missing codomain should error");
        // NOTE: p_pi has the same issue as p_lam had — no Cut around (kw(Arrow), p_raw).
        // When p_raw fails after `->`, the tuple fails and .or() falls back to
        // fun_or_spine, which may parse (x : Nat) differently.
        // UPGRADE: same Cut fix as p_lam: wrap (kw(Arrow), p_raw)
        // UPGRADE: error should say "expected type after `->`"
    }

    /// Implicit Pi with missing codomain.
    #[test]
    fn implicit_pi_missing_codomain() {
        let input = r#"[x : Nat] ->"#;
        let errors = assert_raw_errors(input);
        assert!(!errors.is_empty(), "implicit Pi missing codomain should error");
    }

    /// Annotation missing colon and type.
    #[test]
    fn binder_missing_type() {
        let input = r#"(x : ) -> Nat"#;
        let errors = assert_raw_errors(input);
        assert!(!errors.is_empty(), "binder with empty type should error");
    }

    /// Universes with bad level.
    #[test]
    fn bad_universe() {
        // Type  is valid.  Type0, Type1, etc.  But `Type-1` or `Type` without
        // number is valid too (default U0?).
        // Let's test with unexpected token.
        let input = r#"Type @ "#;
        let errors = assert_raw_errors(input);
        // The parser might parse `Type` and then fail on `@`.
        assert!(!errors.is_empty(), "Type followed by garbage should error");
    }

    /// `let` expression missing `=`.
    #[test]
    fn let_missing_eq() {
        let input = r#"let x : Nat;"#;
        let errors = assert_raw_errors(input);
        assert!(!errors.is_empty(), "let without `=` should error");
    }

    /// `let` expression with `=` but no body.
    #[test]
    fn let_missing_body() {
        let input = r#"let x : Nat = ;"#;
        let errors = assert_raw_errors(input);
        assert!(!errors.is_empty(), "let without value should error");
    }
}

// ===========================================================================
// Category 5: Pattern / Match Errors
// ===========================================================================
//
// `match` expressions and their arms.
//
mod match_errors {
    use super::*;

    /// `match` without any case arms.
    #[test]
    fn match_no_arms() {
        let input = r#"
def t = match x {

}
"#;
        // Empty match might be valid syntactically; check.
        let result = parser(input, 0);
        assert!(result.is_some(), "empty match should not crash");
    }

    /// `match` arm missing `=>`.
    #[test]
    fn match_arm_missing_arrow() {
        let input = r#"
def t = match x {
    case zero
}
"#;
        let errors = assert_parse_errors(input);
        assert!(!errors.is_empty(), "match arm without `=>` should error");
        // NOTE: errors point at `zero` not at `case`.
        // The match arm tuple fails at kw(=>), error is SILENTLY DISCARDED
        // by many0_sep's while let Ok(...). Visible errors are from
        // remaining-input check / brace recovery, not from the actual problem.
        // UPGRADE: error should say "expected '=>' after pattern" at `case`.
    }

    /// `match` arm with `=>` but no body expression.
    #[test]
    fn match_arm_missing_body() {
        let input = r#"
def t = match x {
    case zero =>
}
"#;
        let errors = assert_parse_errors(input);
        assert!(!errors.is_empty(), "match arm without body should error");
        // NOTE: same issue as missing_arrow — error is silently discarded.
        // UPGRADE: error should say "expected expression after '=>'" at `case`.
    }

    /// Nested match with unbalanced delimiters.
    #[test]
    fn match_unbalanced_braces() {
        let input = r#"
def t = match x {
    case zero => match y {
        case true => 1
}
"#;
        let errors = assert_parse_errors(input);
        assert!(!errors.is_empty(), "unbalanced braces in match should error");
    }

    /// `match` on an expression that is itself invalid.
    #[test]
    fn match_bad_scrutinee() {
        let input = r#"
def t = match (1 +) {
    case zero => 1
}
"#;
        let errors = assert_parse_errors(input);
        assert!(!errors.is_empty(), "match on bad expression should error");
        // UPGRADE: ideally only one error about `(1 +)` not about the match itself
    }
}

// ===========================================================================
// Category 6: Enum / Struct Definition Errors
// ===========================================================================
//
// GADT syntax, field definitions, etc.
//
mod enum_struct_errors {
    use super::*;

    /// Enum with constructor that has a bad parameter list.
    /// NOTE: current parser accepts `Bar[A](x: A) -> Foo A` without error
    /// because it does not strictly validate GADT return-type syntax.
    /// UPGRADE: should either parse this correctly or give a clear error
    /// about `(` vs `[` usage in constructor parameters.
    #[test]
    fn enum_ctor_bad_param() {
        let input = r#"
enum Foo[A] {
    Bar[A](x: A) -> Foo A
}
"#;
        // Current parser accepts this without parse errors (may still
        // fail later during elaboration).  At minimum, should not crash.
        let result = parser(input, 0);
        assert!(result.is_some(), "should not crash on GADT syntax");
    }

    /// Struct with duplicate field names.
    #[test]
    fn struct_duplicate_field() {
        let input = r#"
struct Point {
    x: Nat
    x: Bool
}
"#;
        // Duplicate field names might be a semantic error, not a parse error.
        // UPGRADE: parser could warn or the elab could error.
        let result = parser(input, 0);
        assert!(result.is_some(), "duplicate field should not crash the parser");
    }

    /// Enum with missing return type in GADT syntax.
    #[test]
    fn gadt_missing_return_type() {
        let input = r#"
enum Vec[A](len: Nat) {
    Nil -> 
}
"#;
        let errors = assert_parse_errors(input);
        assert!(!errors.is_empty(), "GADT constructor without return type should error");
    }

    /// Struct with field type that contains a parse error.
    #[test]
    fn struct_field_bad_type() {
        let input = r#"
struct Foo {
    x: (Nat ->
}
"#;
        let errors = assert_parse_errors(input);
        assert!(!errors.is_empty(), "struct field with bad type should error");
    }
}

// ===========================================================================
// Category 7: Trait / Impl Errors
// ===========================================================================
//
// Trait declarations and implementations have complex syntax.
//
mod trait_impl_errors {
    use super::*;

    /// Trait with empty body (no methods).
    #[test]
    fn trait_empty_body() {
        let input = r#"
trait Empty {

}
"#;
        // This could be valid (marker trait).
        let result = parser(input, 0);
        assert!(result.is_some(), "empty trait should not crash");
    }

    /// Trait method without a type signature.
    #[test]
    fn trait_method_no_type() {
        let input = r#"
trait Foo {
    def bar
}
"#;
        let errors = assert_parse_errors(input);
        assert!(!errors.is_empty(), "trait method without type should error");
    }

    /// Impl missing `for`.
    /// NOTE: the current parser accepts `impl Foo { … }` without `for` —
    /// it may interpret it as a different construct.
    /// UPGRADE: should error: `impl` requires `for <trait>` syntax.
    #[test]
    fn impl_missing_for() {
        let input = r#"
impl Foo {

}
"#;
        // Current parser accepts it — at least don't crash.
        let result = parser(input, 0);
        assert!(result.is_some(), "impl without `for` should not crash");
        // UPGRADE: uncomment:
        // let (_decls, errors) = result.unwrap();
        // assert!(!errors.is_empty(), "impl without `for` should error");
    }

    /// Impl with `for` but missing trait name.
    #[test]
    fn impl_missing_trait_name() {
        let input = r#"
impl for Nat {
    def foo: Nat = 0
}
"#;
        let errors = assert_parse_errors(input);
        assert!(!errors.is_empty(), "impl without trait name should error");
    }

    /// Impl for a non-existent type — this is not a parse error but a
    /// type-checking error.  Parser should accept it.
    #[test]
    fn impl_nonexistent_type_parses_ok() {
        let input = r#"
impl Foo for Bar {
    def foo: Nat = 0
}
"#;
        let (decls, errors) = assert_parse_ok(input);
        // `Foo` and `Bar` not defined, but that's an elaboration error.
        assert!(decls.iter().any(|d| matches!(d, Decl::ImplDecl { .. })),
            "should parse as ImplDecl");
    }

    /// Impl body with an invalid method definition.
    #[test]
    fn impl_bad_method() {
        let input = r#"
trait Foo {
    def foo: Nat
}
impl Foo for Nat {
    def foo = 
}
"#;
        let errors = assert_parse_errors(input);
        assert!(!errors.is_empty(), "impl method without body should error");
    }
}

// ===========================================================================
// Category 8: Macro Errors
// ===========================================================================
//
// Macro definition and invocation syntax is complex and error-prone.
//
mod macro_errors {
    use super::*;

    /// `macro_rules` without a name.
    #[test]
    fn macro_missing_name() {
        let input = r#"
macro_rules {
    ($x: ident) => { $x }
}
"#;
        let errors = assert_parse_errors(input);
        assert!(!errors.is_empty(), "macro_rules without name should error");
    }

    /// `macro_rules` with name but no rules.
    #[test]
    fn macro_empty_rules() {
        let input = r#"
macro_rules foo {
    
}
"#;
        // Empty macro might be valid syntactically.
        let result = parser(input, 0);
        assert!(result.is_some(), "empty macro_rules should not crash");
    }

    /// Macro matcher with unrecognized fragment specifier.
    /// NOTE: the current macro parser does NOT validate fragment specifiers,
    /// so `$x: blah` is silently accepted.
    /// UPGRADE: should error on unknown fragment specifiers.
    #[test]
    fn macro_bad_fragment() {
        let input = r#"
macro_rules foo {
    ($x: blah) => { $x }
}
"#;
        // `blah` is not a valid fragment specifier (valid: ident, raw, etc.).
        // Current parser accepts it silently — at least don't crash.
        let result = parser(input, 0);
        assert!(result.is_some(), "bad macro fragment should not crash");
        // UPGRADE: uncomment:
        // let (_decls, errors) = result.unwrap();
        // assert!(!errors.is_empty(), "bad macro fragment specifier should error");
    }

    /// Macro invocation that is incomplete.
    #[test]
    fn macro_incomplete_invocation() {
        let input = r#"
println stringify
"#;
        // `stringify` takes one argument; if missing, the macro expansion
        // might fail, but parsing should produce some AST.
        // This may or may not produce a parse error depending on how
        // stringify is implemented.
        let result = parser(input, 0);
        assert!(result.is_some(), "incomplete macro invocation should not crash");
    }
}

// ===========================================================================
// Category 9: Import / Package Errors
// ===========================================================================
//
// Module system syntax.
//
mod import_package_errors {
    use super::*;

    /// `import` with empty braces.
    #[test]
    fn import_empty_braces() {
        let input = r#"
import foo.bar.{}
"#;
        let errors = assert_parse_errors(input);
        assert!(!errors.is_empty(), "import with empty braces should error");
    }

    /// `import` with missing closing brace.
    #[test]
    fn import_unclosed_brace() {
        let input = r#"
import foo.{ bar, baz
"#;
        let errors = assert_parse_errors(input);
        assert!(!errors.is_empty(), "import with unclosed brace should error");
    }

    /// `import` with a malformed path (trailing dot).
    #[test]
    fn import_trailing_dot() {
        let input = r#"
import foo.
"#;
        let errors = assert_parse_errors(input);
        assert!(!errors.is_empty(), "import with trailing dot should error");
    }

    /// `package` with dots but missing names.
    #[test]
    fn package_trailing_dot() {
        let input = r#"
package foo.
"#;
        let errors = assert_parse_errors(input);
        assert!(!errors.is_empty(), "package with trailing dot should error");
    }
}

// ===========================================================================
// Category 10: Error Recovery (Multi-Error Scenarios)
// ===========================================================================
//
// The most important category: can the parser find multiple errors in one file
// without the first error causing cascading failures for the rest?
//
// UPGRADE: each of these should report ALL errors, not just the first one.
//
mod error_recovery {
    use super::*;

    /// Two separate bad declarations — both should be reported.
    /// NOTE: current parser only reports 1 error because recovery from
    /// the first bad decl skips the rest of the file via `skip_until_decl`.
    /// UPGRADE: should report 2 errors (one for each bad line).
    #[test]
    fn two_bad_decls() {
        let input = r#"
xyzzy

bazbang
"#;
        let result = parser(input, 0);
        assert!(result.is_some(), "should not crash on two bad decls");
        let (_decls, errors) = result.unwrap();
        // UPGRADE: should report at least 2 errors
        assert!(errors.len() >= 1,
            "expected at least 1 error for bad decls, got {}:\n{:?}",
            errors.len(), errors);
    }

    /// Good decl, bad decl, good decl — middle bad decl should be recovered
    /// and both good decls should be present in the AST.
    #[test]
    fn good_bad_good_decls() {
        let input = r#"
def one: Nat = 1

garbage nonsense

def two: Nat = 2
"#;
        let result = parser(input, 0);
        assert!(result.is_some(), "should recover from middle bad decl");
        let (decls, errors) = result.unwrap();
        // Only 1 error (at `garbage`). The leading \n before `def one`
        // is ALSO recovered via skip_until_decl, but its error is pushed
        // before the separator advances past it, so it's counted. (Currently
        // only 1 error — the first recovery's error is somehow absorbed.)
        // UPGRADE: 2 errors (one per recovery) is more accurate.
        assert!(!errors.is_empty(), "the garbage line should produce an error");
        let names: Vec<_> = decls.iter().filter_map(|d| {
            if let Decl::Def { name, .. } = d { Some(name.data.as_str()) } else { None }
        }).collect();
        assert!(names.contains(&"one"), "def one should be parsed");
        assert!(names.contains(&"two"), "def two should be parsed despite earlier error");
    }

    /// Multiple consecutive bad decls — should recover past all of them.
    /// NOTE: current parser only reports 1 error because `skip_until_decl`
    /// hasn't found a sync point, so it falls through to `Err`, which the
    /// outer `many1_sep` treats as a stop signal and returns the accumulated
    /// results so far.  The survivor is never reached.
    /// UPGRADE: should report 3+ errors and still parse `def survivor`.
    #[test]
    fn many_bad_decls() {
        let input = r#"
junk1

junk2

junk3

def survivor: Nat = 42
"#;
        let result = parser(input, 0);
        assert!(result.is_some(), "should recover through many bad decls");
        let (decls, errors) = result.unwrap();
        // UPGRADE: should report at least 3 errors
        assert!(errors.len() >= 1,
            "expected at least 1 error for 3 bad decls, got {}",
            errors.len());
    }

    /// Error inside a `def` body should be recovered, and the rest of the file
    /// should still be parsed.
    /// After `opt_trail_nl` fix: the EndLine before `def good` is no longer eaten,
    /// so `def good` survives.
    #[test]
    fn error_in_def_body() {
        let input = r#"
def bad_body: Nat = (1 +

def good: Nat = 2
"#;
        let result = parser(input, 0);
        assert!(result.is_some(), "should recover from bad def body");
        let (decls, errors) = result.unwrap();
        assert!(!errors.is_empty(), "unbalanced paren in body should error");
        // After opt_trail_nl: `def good` survives
        let has_good = decls.iter().any(|d| {
            matches!(d, Decl::Def { name, .. } if name.data == "good")
        });
        assert!(has_good, "should still parse `def good` after bad body");
    }

    /// Two errors in the same declaration (e.g., missing both `:` and `=`).
    #[test]
    fn multiple_errors_same_decl() {
        let input = r#"
def foo(x Nat) Nat x
"#;
        let errors = assert_parse_errors(input);
        // UPGRADE: might report multiple errors: expected `:`, expected `=`
        assert!(errors.len() >= 1);
    }

    /// Unclosed delimiter at end of file — should not hang.
    #[test]
    fn unclosed_delimiter_eof() {
        let input = r#"
def foo: Nat = (1 + 2
"#;
        let result = parser(input, 0);
        assert!(result.is_some(), "unclosed delimiter at EOF should not hang");
        let (_decls, errors) = result.unwrap();
        assert!(!errors.is_empty(), "unclosed paren should error");
    }

    /// String containing newline (multi-line string) — the lexer should
    /// handle it gracefully.
    #[test]
    fn multiline_string() {
        let input = r#"
def msg: String = "hello
world"
"#;
        let result = parser(input, 0);
        assert!(result.is_some(), "multi-line string should not crash");
    }

    /// Deeply nested error that causes many tokens to be skipped.
    /// The parser should terminate eventually.
    #[test]
    fn deep_nesting_error() {
        let input = r#"
def foo: Nat = (((((((((1 + )))))))))
"#;
        let result = parser(input, 0);
        assert!(result.is_some(), "deeply nested error should not hang");
        let (_decls, errors) = result.unwrap();
        assert!(!errors.is_empty(), "should report the inner error");
    }

    /// Mixed content: valid Typort followed by binary garbage (simulated
    /// as non-Typort symbols).  Should recover at the next valid point.
    #[test]
    fn recovery_after_garbage() {
        let input = r#"
def a: Nat = 1

@#$%^&

def b: Nat = 2
"#;
        let result = parser(input, 0);
        assert!(result.is_some(), "should recover after garbage symbols");
        let (decls, errors) = result.unwrap();
        assert!(!errors.is_empty(), "garbage should produce error(s)");
        let has_b = decls.iter().any(|d| {
            matches!(d, Decl::Def { name, .. } if name.data == "b")
        });
        assert!(has_b, "should parse `def b` after garbage");
    }
}

// ===========================================================================
// Category 11: Edge-Case Boundary Conditions
// ===========================================================================
//
// These tests probe the edges of what the parser can handle — boundaries
// between tokens, unusual spacing, corner cases in the grammar.
//
mod edge_cases {
    use super::*;

    /// Extremely long identifier (potential buffer overflow or slowdown).
    #[test]
    fn very_long_identifier() {
        let long_name = "a".repeat(10_000);
        let input = format!("def {}: Nat = 0", long_name);
        let result = parser(&input, 0);
        assert!(result.is_some(), "very long identifier should not crash");
        let (decls, errors) = result.unwrap();
        assert!(errors.is_empty(), "very long identifier should not cause parse errors");
        assert!(decls.iter().any(|d| {
            matches!(d, Decl::Def { name, .. } if name.data.len() == 10_000)
        }), "def with long name should be parsed");
    }

    /// Identifier containing Unicode (CJK characters).
    #[test]
    fn unicode_identifiers() {
        let input = r#"
def 变量: Type0 = Type0
def 加法(x: Nat, y: Nat): Nat = x
"#;
        let result = parser(input, 0);
        assert!(result.is_some(), "Unicode identifiers should not crash");
    }

    /// Mixed tab and space indentation.
    #[test]
    fn mixed_indentation() {
        let input = "\t def a: Nat = 1\n\t def b: Nat = 2\n";
        let result = parser(input, 0);
        assert!(result.is_some(), "mixed tab/space indentation should not crash");
    }

    /// Leading zeros in numeric literal.
    #[test]
    fn leading_zeros() {
        let input = r#"
def x: Nat = 007
"#;
        let result = parser(input, 0);
        assert!(result.is_some(), "leading zeros should not crash");
        // 007 may or may not parse as 7 — depends on lexer.
    }

    /// Empty string literal `""`.
    #[test]
    fn empty_string() {
        let input = r#"
def x: String = ""
"#;
        let (decls, errors) = assert_parse_ok(input);
    }

    /// String literal with escaped characters.
    #[test]
    fn string_with_escapes() {
        let input = r#"def x: String = "hello\nworld\t\"quoted\""#;
        let result = parser(input, 0);
        assert!(result.is_some(), "escaped string should not crash");
    }

    /// Using keywords as identifiers (should fail as parse error or
    /// elaboration error depending on implementation).
    #[test]
    fn keyword_as_identifier() {
        let input = "def def: Nat = 0";
        let result = parser(input, 0);
        assert!(result.is_some(),
            "keyword as identifier should not crash");
        // `def def` — the parser might interpret first `def` as keyword,
        // second `def` as name, or it might fail.
    }

    /// Negative integer literal (if not supported, should error gracefully).
    #[test]
    fn negative_literal() {
        let input = r#"
def x: Int = -1
"#;
        // Typort may not have `Int` or negative literals at all.
        // But `-1` may parse as `Neg` applied to `1`.
        let result = parser(input, 0);
        assert!(result.is_some(), "negative literal should not crash");
    }
}

// ===========================================================================
// Category 12: Cascading Error Behaviour
// ===========================================================================
//
// These tests specifically target the quality of secondary / cascading errors.
// A chumsky-like parser should minimise them: one syntax mistake should not
// produce 10 meaningless follow-up errors on the same line.
//
mod cascade_behaviour {
    use super::*;

    /// A single missing `(` should produce ONE primary error, not many.
    /// Now: `def bar` survives because `opt_trail_nl` no longer eats the
    /// declaration separator.  Only 1 error (`expected ')'`) is produced.
    /// UPGRADE: still want better span info and secondary note pointing to `(`.
    #[test]
    fn single_missing_paren() {
        let input = r#"
def foo: Nat = (1 + 2

def bar: Nat = 3
"#;
        let result = parser(input, 0);
        assert!(result.is_some());
        let (decls, errors) = result.unwrap();
        // After opt_trail_nl fix: only 1 error (Expect(RParen)), and def bar survives.
        // Verify def bar is actually parsed:
        let names: Vec<&str> = decls.iter().filter_map(|d| {
            if let Decl::Def { name, .. } = d { Some(name.data.as_str()) } else { None }
        }).collect();
        assert!(names.contains(&"foo"), "should parse def foo");
        assert!(names.contains(&"bar"), "should parse def bar (was being eaten)");
        assert_eq!(errors.len(), 1,
            "expected exactly 1 error (missing `)`), got {}: {:?}",
            errors.len(), errors.iter().map(|e| format!("{}", e.msg.data)).collect::<Vec<_>>());
    }

    /// One bad token in the middle of an expression — the error should be
    /// localised, not kill the whole sub-expression.
    #[test]
    fn bad_token_in_expr() {
        // ROOT CAUSE of double error:
        // 1. `@` is lexed as `Op` (see lex.rs line 258: `':' ..= '@'` includes @)
        //    NOT as ErrToken as one might expect.
        // 2. `prefix_binding_power` returns None for `@` → prefix fail
        // 3. `p_atom` can't parse `@` as any atom → `In(Atom, Expect(LParen))` at `@`
        // 4. `infix_binding_power` has a catch-all (line 741) → returns (7,8) for `@`
        // 5. So `@` is treated as ANOTHER infix operator after the first RHS fails!
        // 6. This advances the input past `@` to the next `+`, which ALSO atom-fails
        // 7. Result: 2 identical errors at different positions (@ and next +)
        //
        // UPGRADE: `@` should NOT have infix binding power; or,
        //          errors with the same type at adjacent positions should be merged.
        let input = r#"
def foo: Nat = 1 + @ + 2
"#;
        let result = parser(input, 0);
        assert!(result.is_some(), "bad token in expression should not crash");
        let (_decls, errors) = result.unwrap();
        // Current: 2 errors because `@` is caught by the catch-all infix binding power
        // UPGRADE: ideally 1 error about `@`
        assert!(!errors.is_empty(), "bad token should produce at least one error");
        // UPGRADE: ideally 1 error about unexpected `@`, not cascading errors
        assert!(errors.len() <= 3,
            "expected ≤3 errors for one bad infix token, got {}",
            errors.len());
    }

    /// Missing then-branch in a `let` should not cause errors on subsequent lines.
    #[test]
    fn let_cascade() {
        let input = r#"
def foo: Nat =
    let x = ;
    x + 1
"#;
        let result = parser(input, 0);
        assert!(result.is_some(), "bad let should not cascade fatally");
        let (_decls, errors) = result.unwrap();
        // UPGRADE: ideally just 1 error about missing let-body
        assert!(errors.len() <= 3,
            "expected ≤3 errors for missing let-body, got {}",
            errors.len());
    }

    /// Deeply nested wrong bracket types: `(]` etc.
    #[test]
    fn mismatched_bracket_types() {
        let input = r#"
def foo: Nat = (1 + 2]
"#;
        let result = parser(input, 0);
        assert!(result.is_some(), "mismatched bracket should not crash");
        let (_decls, errors) = result.unwrap();
        assert!(!errors.is_empty(), "mismatched bracket should produce at least one error");
        // UPGRADE: error should say "expected ')' but found ']'"
        //          with a useful secondary note about where '(' was opened.
    }
}

// ===========================================================================
// Category 13: Delimiter / Block Structure Errors
// ===========================================================================
//
// The language uses `;` (EndLine) as a declaration separator, but parentheses,
// brackets, and braces for grouping.  These tests probe delimiter handling.
//
mod delimiter_errors {
    use super::*;

    /// Missing semicolon / newline between declarations.
    #[test]
    fn missing_decl_separator() {
        let input = r#"
def a: Nat = 1 def b: Nat = 2
"#;
        let result = parser(input, 0);
        assert!(result.is_some(), "missing newline between decls should not crash");
        // Currently declarations are separated by EndLine (newline).
        // Without it, `def b` might be parsed as part of `def a`'s body.
        // UPGRADE: diagnostics should help the user spot the missing newline.
    }

    /// Extra semicolon / blank line between declarations — should be fine.
    #[test]
    fn extra_blank_lines() {
        let input = "def a: Nat = 1\n\n\n\n\ndef b: Nat = 2\n";
        let (decls, errors) = assert_parse_ok(input);
        assert_eq!(decls.len(), 2, "should parse exactly 2 declarations");
    }

    /// Lexer producing EndLine where it shouldn't (inside parens).
    /// NOTE: the current parser does NOT treat newlines inside `(…)` as
    /// whitespace — it produces errors:
    ///   In(Atom, Expect(LParen)), Base(Expect(RParen)), Base(Expect(EndLine))
    /// UPGRADE: newlines inside matching delimiters should be ignored.
    #[test]
    fn newline_inside_parens() {
        let input = r#"
def foo: Nat = (1 +
    2)
"#;
        // Current: 3 errors; UPGRADE: 0 errors, valid parse
        let result = parser(input, 0);
        assert!(result.is_some(), "should not crash on multi-line parens");
        let (_decls, errors) = result.unwrap();
        // eprintln!("newline_inside_parens errors: {:?}", errors);
        assert!(errors.len() >= 1, "expected at least 1 error (current behaviour)");
    }

    /// Opening brace `{` where not expected.
    #[test]
    fn unexpected_brace() {
        let input = r#"
def foo: Nat = { 1
"#;
        let result = parser(input, 0);
        assert!(result.is_some(), "unexpected brace should not crash");
    }
}

// ===========================================================================
// Category 14: Recovery During Expression Parsing (via parser_test)
// ===========================================================================
//
// These test that `p_raw.many0()` can recover and continue parsing multiple
// expressions when one contains an error.
//
mod expr_recovery {
    use super::*;

    /// Multiple raw expressions, one bad — should get both the good one
    /// and an error for the bad one.
    #[test]
    fn raw_multi_expr_one_bad() {
        let input = "1 + 2\n(3 +\n4 + 5\n";
        let result = parser_test(input, 0);
        assert!(result.is_some(), "multiple raw expressions should not crash");
        let (raws, errors) = result.unwrap();
        // First expression `1 + 2` is valid.
        // Second `(3 +` is incomplete.
        // Third `4 + 5` might or might not be reached depending on recovery.
        assert!(!errors.is_empty(), "incomplete expression should error");
        // UPGRADE: should get at least 1 raw expression back
        assert!(raws.len() >= 1, "should get at least the valid first expression");
    }

    /// Empty raw expression list.
    #[test]
    fn raw_empty() {
        let input = "";
        let (raws, errors) = assert_raw_ok(input);
        assert!(raws.is_empty(), "empty input should yield zero raw expressions");
    }

    /// Raw expression with a trailing operator — should error but not crash.
    #[test]
    fn raw_trailing_op() {
        let input = "1 + 2 +";
        let errors = assert_raw_errors(input);
        assert!(errors.len() >= 1, "trailing operator should error");
    }
}

// ===========================================================================
// Category 15: Derive Attribute Errors
// ===========================================================================
//
// The `#[derive(...)]` attribute before enum/struct declarations.
//
mod derive_errors {
    use super::*;

    /// `#[derive]` with no trait names.
    #[test]
    fn derive_empty_parens() {
        let input = r#"
#[derive()]
enum Foo {
    Bar
}
"#;
        let result = parser(input, 0);
        assert!(result.is_some(), "empty #[derive] should not crash");
    }

    /// `#[derive` missing closing bracket.
    #[test]
    fn derive_unclosed() {
        let input = r#"
#[derive(Show
enum Foo {
    Bar
}
"#;
        let errors = assert_parse_errors(input);
        assert!(!errors.is_empty(), "unclosed #[derive should error");
    }

    /// `#[derive(...)]` attached to a `def`, not enum/struct.
    #[test]
    fn derive_on_def() {
        let input = r#"
#[derive(Show)]
def foo: Nat = 1
"#;
        let result = parser(input, 0);
        assert!(result.is_some(), "derive on def should not crash");
        // Parser might treat this as Derive wrapper around a Def, or error.
    }
}

// ===========================================================================
// Category 16: Operator / Precedence Errors
// ===========================================================================
//
// Operators in Typort are parsed as applications of function names like `+`.
//
mod op_errors {
    use super::*;

    /// Operator with no left operand.
    #[test]
    fn leading_operator() {
        let input = r#"+ 1"#;
        let errors = assert_raw_errors(input);
        assert!(!errors.is_empty(), "leading operator should error");
    }

    /// Double operator `1 + + 2`.
    #[test]
    fn double_operator() {
        let input = r#"1 + + 2"#;
        let (raws, errors) = assert_raw_ok(input);
        // This might parse as `1 + (+ 2)` if `+` is a prefix function,
        // or error.  Depends on current implementation.
    }

    /// Consecutive operators with different precedence — no parens.
    #[test]
    fn mixed_precedence() {
        let input = r#"1 + 2 * 3"#;
        let (raws, errors) = assert_raw_ok(input);
        // The parser currently parses left-to-right: `((1 + 2) * 3)`.
        // This is not a parse error, but the test documents precedence behaviour.
    }
}
