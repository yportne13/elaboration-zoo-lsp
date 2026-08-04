// ============================================================
// Scala-style class mechanism tests
//
// Class is pure desugaring: `class Name[P] impl T1, T2 { ... }` expands to
//   struct (Name.mk) + def Name.create + inherent impl (namespace methods)
//   + trait impls (records referencing the namespace defs).
// These tests pin the behavior of the desugared pieces and their
// interop with the existing trait/derive machinery.
// ============================================================

use super::*;

fn assert_ok(input: &str) -> String {
    match run_with_prelude(input) {
        Ok(output) => output,
        Err(e) => panic!("expected OK, got error: '{}' @ {}:{}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

fn assert_err_contains(input: &str, needle: &str) {
    match run_with_prelude(input) {
        Ok(output) => panic!("expected error containing '{}', got OK: {}", needle, output.trim()),
        Err(e) => {
            assert!(
                e.0.data.contains(needle),
                "expected error containing '{}', got: '{}'",
                needle,
                e.0.data
            );
        }
    }
}

// ── fields / methods / this ──

#[test]
fn class_fields_methods_this() {
    let output = assert_ok(r#"
class Point {
    let x: Nat = succ zero
    let y: Nat = succ (succ zero)
    def sum: Nat = this.x + this.y
}
println (Point.create.sum)
println (Point.create.x)
"#);
    let lines: Vec<&str> = output.trim().lines().collect();
    assert!(lines.iter().any(|l| l.trim() == "3"), "sum should be 3, got: {}", output);
    assert!(lines.iter().any(|l| l.trim() == "1"), "x should be 1, got: {}", output);
}

#[test]
fn class_let_instance_field_and_method() {
    let output = assert_ok(r#"
class Point {
    let x: Nat = 2
    def double: Nat = this.x * 2
}
def p = Point.create
println (p.x)
println (p.double)
"#);
    let lines: Vec<&str> = output.trim().lines().collect();
    assert!(lines.iter().any(|l| l.trim() == "2"), "field via instance: {}", output);
    assert!(lines.iter().any(|l| l.trim() == "4"), "method via instance: {}", output);
}

#[test]
fn class_method_with_params_and_chain() {
    let output = assert_ok(r#"
class Counter {
    let n: Nat = 2
    def add(dx: Nat): Counter = Counter.mk (this.n + dx)
    def get: Nat = this.n
    def add2: Nat = this.add(2).get
}
println (Counter.create.add(3).get)
println (Counter.create.add2)
"#);
    let lines: Vec<&str> = output.trim().lines().collect();
    assert!(lines.iter().any(|l| l.trim() == "5"), "add(3).get should be 5: {}", output);
    assert!(lines.iter().any(|l| l.trim() == "4"), "add2 should be 4: {}", output);
}

// ── parameterized classes ──

#[test]
fn class_param_trait_impl() {
    let output = assert_ok(r#"
trait Named {
    def name: Nat
}
class Adder[w: Nat] impl Named {
    let zz_name: Nat = w + 1
    def name: Nat = this.zz_name
}
println (Adder.create[5].name)
"#);
    assert!(output.contains("6"), "name should be w+1 = 6, got: {}", output);
}

// ── trait impls: record references namespace defs (single elaboration) ──

#[test]
fn class_trait_impl_sibling_method_call() {
    // Regression: trait-impl method bodies used to be elaborated before the
    // inherent impl registered the namespace methods, so `this.double` failed
    // with "Counter has no object `double`".
    let output = assert_ok(r#"
trait Named {
    def name: Nat
}
class Counter impl Named {
    let base: Nat = 5
    def double: Nat = this.base + this.base
    def name: Nat = this.double + 1
}
println (Counter.create.name)
"#);
    assert!(output.contains("11"), "name should call sibling double = 11, got: {}", output);
}

#[test]
fn class_trait_impl_method_calls_another_trait_method() {
    let output = assert_ok(r#"
trait Named {
    def name: Nat
    def label: Nat
}
class Foo impl Named {
    let zz: Nat = 3
    def name: Nat = this.zz
    def label: Nat = this.name + 1
}
println (Foo.create.label)
"#);
    assert!(output.contains("4"), "label should call sibling name = 4, got: {}", output);
}

#[test]
fn class_multi_trait() {
    let output = assert_ok(r#"
trait Named {
    def name: Nat
}
trait Sized {
    def size: Nat
}
class Foo impl Named, Sized {
    let zz: Nat = 2
    def name: Nat = this.zz
    def size: Nat = this.zz + 1
}
println (Foo.create.name)
println (Foo.create.size)
"#);
    let lines: Vec<&str> = output.trim().lines().collect();
    assert!(lines.iter().any(|l| l.trim() == "2"), "name: {}", output);
    assert!(lines.iter().any(|l| l.trim() == "3"), "size: {}", output);
}

#[test]
fn class_trait_default_method() {
    // Trait method without a class implementation falls back to the default body.
    let output = assert_ok(r#"
trait Named {
    def name: Nat
    def label: Nat = this.name + 100
}
class Foo impl Named {
    let zz: Nat = 1
    def name: Nat = this.zz
}
println (Foo.create.label)
"#);
    assert!(output.contains("101"), "default label should be name+100 = 101, got: {}", output);
}

#[test]
fn class_generic_trait_dispatch() {
    // A class's trait record must be usable from generic code: the where-clause
    // synthesizes `_named_N : Named[N]` (the record), whose `name` field
    // references the class's namespace def `Fooname`.
    let output = assert_ok(r#"
trait Named {
    def name: Nat
}
class Foo impl Named {
    let zz: Nat = 5
    def name: Nat = this.zz
}
def getName[N](x: N): Nat where N: Named = _named_N.name x
println (getName (Foo.create))
"#);
    assert!(output.contains("5"), "generic dispatch should yield 5, got: {}", output);
}

#[test]
fn class_trait_with_params() {
    // `impl WithVal[3]` — trait params flow from the class header into the
    // record instance (`WithVal.mk [C] [3] (Cval)`).
    let output = assert_ok(r#"
trait WithVal[n: Nat] {
    def val: Nat
}
class C impl WithVal[3] {
    let zz: Nat = 7
    def val: Nat = this.zz
}
def getVal[n: Nat, C2](x: C2): Nat where C2: WithVal[n] = _withval_C2.val x
println (getVal[3] (C.create))
println (C.create.val)
"#);
    let lines: Vec<&str> = output.trim().lines().collect();
    assert!(lines.iter().any(|l| l.trim() == "7"), "trait-param generic dispatch: {}", output);
}

// ── statics ──

#[test]
fn class_static_method() {
    let output = assert_ok(r#"
class Point {
    let x: Nat = 1
    def get: Nat = this.x
    static def make: Point = Point.create
    static def doubleX(p: Point): Nat = p.x * 2
}
println (Point.make.get)
println (Point.doubleX (Point.make))
"#);
    let lines: Vec<&str> = output.trim().lines().collect();
    assert!(lines.iter().any(|l| l.trim() == "1"), "static make/get: {}", output);
    assert!(lines.iter().any(|l| l.trim() == "2"), "static with args: {}", output);
}

// ── constructor statements ──

#[test]
fn class_ctor_statements() {
    // Bare expressions in the class body are constructor statements: they are
    // elaborated (type-checked) in order before the fields are assembled.
    let output = assert_ok(r#"
class Counter {
    let n: Nat = 1
    1 + 1
    def get: Nat = this.n
}
println (Counter.create.get)
"#);
    assert!(output.contains("1"), "ctor statements should not disturb fields: {}", output);
}

// ── operator methods ──

#[test]
fn class_operator_method() {
    let output = assert_ok(r#"
class Counter {
    let n: Nat = 2
    def + (that: Counter): Nat = this.n + that.n
}
println (Counter.create + Counter.create)
"#);
    assert!(output.contains("4"), "operator method should yield 4, got: {}", output);
}

// ── interop with derive and impl-for (desugared output is ordinary decls) ──

#[test]
fn class_derive_show() {
    // #[derive(Show)] on a class derives on its struct, like a plain struct.
    let output = assert_ok(r#"
#[derive(Show)]
class Point {
    let x: Nat = 1
    let y: Nat = 2
}
println (Point.create.show)
"#);
    assert!(output.contains("Point"), "derive Show on class should print, got: {}", output);
}

#[test]
fn class_impl_for_extra_trait() {
    // A plain `impl Trait for ClassType` written after the class works
    // exactly as for any other struct.
    let output = assert_ok(r#"
class Point {
    let x: Nat = 1
    def get: Nat = this.x
}
trait Desc {
    def desc: Nat
}
impl Desc for Point {
    def desc: Nat = 99
}
println (Point.create.get)
println (Point.create.desc)
"#);
    let lines: Vec<&str> = output.trim().lines().collect();
    assert!(lines.iter().any(|l| l.trim() == "1"), "class method: {}", output);
    assert!(lines.iter().any(|l| l.trim() == "99"), "impl-for on class type: {}", output);
}

// ── negative cases ──

#[test]
fn class_err_missing_trait_method() {
    assert_err_contains(r#"
trait Named {
    def name: Nat
}
class Foo impl Named {
    let zz: Nat = 1
}
"#, "has no default implementation");
}

#[test]
fn class_err_unknown_this_method() {
    assert_err_contains(r#"
class Foo {
    let x: Nat = 1
    def get: Nat = this.unknown
}
"#, "no object");
}

#[test]
fn class_err_forward_method_reference() {
    // Methods are elaborated in declaration order (like top-level defs), so a
    // method may call earlier siblings (`this.double`) but not later ones.
    assert_err_contains(r#"
class Foo {
    def a: Nat = this.b
    def b: Nat = 1
}
"#, "b");
}

// ── dotted method keys vs constructor bare-name resolution ──

#[test]
fn class_method_key_does_not_shadow_constructor() {
    // `bar` is both a constructor (Foo.bar) and a class method (Baz.bar).
    // The bare-name fallback must exclude namespace-registered methods, so
    // patterns/expressions still resolve the constructor.
    let output = assert_ok(r#"
enum Foo {
    bar
}
class Baz {
    let x: Nat = 1
    def bar: Nat = this.x
}
def t: Foo = bar
println (Baz.create.bar)
"#);
    let lines: Vec<&str> = output.trim().lines().collect();
    assert!(lines.iter().any(|l| l.trim() == "1"), "method call on instance: {}", output);
}

#[test]
fn class_method_not_callable_by_bare_name() {
    // Instance methods are only reachable through `x.method` dispatch — a bare
    // reference must not silently resolve to a method.
    assert_err_contains(r#"
class Baz {
    let x: Nat = 1
    def bar: Nat = this.x
}
def t: Nat = bar
"#, "not in scope");
}
