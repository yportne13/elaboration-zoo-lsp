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
class Tally {
    let n: Nat = 2
    def add(dx: Nat): Tally = Tally.mk (this.n + dx)
    def get: Nat = this.n
    def add2: Nat = this.add(2).get
}
println (Tally.create.add(3).get)
println (Tally.create.add2)
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
    // with "Tally has no object `double`".
    let output = assert_ok(r#"
trait Named {
    def name: Nat
}
class Tally impl Named {
    let base: Nat = 5
    def double: Nat = this.base + this.base
    def name: Nat = this.double + 1
}
println (Tally.create.name)
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

// ── unannotated lets in parameterized classes ──
// `let x = e` WITHOUT a type annotation is still a struct field — its type
// is inferred from the value. Class elaboration is two-phase: the field
// values are checked in the create's parameter context first and each
// unannotated field's type is inferred from its value; only then is the
// struct assembled with concrete field types (never a pre-created Hole slot
// whose meta would be instantiated with the constructor's fresh implicit
// arguments — the old "can't unify for unsolved meta" failure).

#[test]
fn class_param_unannotated_field_inferred() {
    // No annotation: `f` is a struct field with inferred type Nat, and it is
    // reachable from outside via `c.create[3].f`.
    let output = assert_ok(r#"
class c[w: Nat] {
    let f = 5
    def get: Nat = w + this.f
}
println (c.create[3].get)
println (c.create[3].f)
"#);
    assert!(output.contains("8"), "field visible to methods, got: {}", output);
    assert!(output.contains("5"), "unannotated field reachable from outside: {}", output);
}

#[test]
fn class_param_unannotated_field_type_depends_on_param() {
    // The inferred field type itself references the class parameter
    // (`u : other[w]`), so it is not a closed solution.  Regression: this
    // used to fail with "can't unify for unsolved meta" (the struct's Hole
    // field meta was instantiated with the constructor's fresh implicit
    // metas and invert could not solve a non-closed rhs); the two-phase
    // elaboration infers `u`'s type in the create's parameter context and
    // puts the concrete `other[w]` into the struct.
    let output = assert_ok(r#"
class other[w: Nat] {
    let x = w + 1
}
class c[w: Nat] {
    let u = other.create[w]
    def getx: Nat = this.u.x
    def getu: Nat = w
}
println (c.create[3].getx)
println (c.create[3].getu)
"#);
    assert!(output.contains("4"), "field of param-typed field: {}", output);
    assert!(output.contains("3"), "class param still usable: {}", output);
}

#[test]
fn class_param_unannotated_field_closed_value() {
    // A closed value (`other.create[8]`) infers to the concrete applied type
    // `other[8]`; the struct field carries the real type instead of relying
    // on the unifier's closed-rhs fallback.
    let output = assert_ok(r#"
class other[w: Nat] {
    let x = w + 1
}
class c[w: Nat] {
    let u = other.create[8]
    def getx: Nat = this.u.x
}
println (c.create[3].getx)
"#);
    assert!(output.contains("9"), "closed field value reachable: {}", output);
}

#[test]
fn class_param_unannotated_field_visible_to_later_items() {
    // Fields bind in the constructor's scope in declaration order, so later
    // items can reference earlier unannotated fields.
    let output = assert_ok(r#"
class c[w: Nat] {
    let n = w + 1
    let m: Nat = n + 1
    def get: Nat = this.m
}
println (c.create[3].get)
"#);
    assert!(output.contains("5"), "field should be visible to later items: {}", output);
}

#[test]
fn class_param_bare_stmt_and_method_param_use() {
    // Bare statements and methods referencing the class parameter work in
    // parameterized classes.
    let output = assert_ok(r#"
class c[w: Nat] {
    1 + 1
    let n: Nat = w
    def get: Nat = w + this.n
}
println (c.create[3].get)
"#);
    assert!(output.contains("6"), "method using param + field: {}", output);
}

// ── inferred (hole-typed) fields ──

#[test]
fn class_param_hole_field_annotation() {
    // `let f: _ = e` — an explicit hole annotation still means "field with
    // inferred type".  The two-phase class elaboration treats it exactly like
    // an unannotated field: the fresh meta is solved (spine-free) by the
    // value check in the create's parameter context, and the struct gets the
    // inferred concrete type.
    let output = assert_ok(r#"
class c[w: Nat] {
    let f: _ = 5
    def get: Nat = this.f
}
println (c.create[3].get)
"#);
    assert!(output.contains("5"), "hole-annotated field under params: {}", output);
}

#[test]
fn struct_param_hole_field() {
    // A plain struct has no field values to infer from, so `struct S[w] { f: _ }`
    // keeps a meta field type; solving its constructor application still relies
    // on the unifier's closed-rhs fallback (see unification.rs `solve`).
    let output = assert_ok(r#"
struct S[w: Nat] { f: _ }
def mkk[w: Nat]: S[w] = S.mk 5
println (mkk[3].f)
"#);
    assert!(output.contains("5"), "hole-typed struct field under params: {}", output);
}

// ── module-macro target shape: module body flattened into class items ──
// The future module macro flattens its side-effect chain into class items:
// unannotated scaffold bindings become create-locals, annotated port fields
// stay struct fields (last-wins dedup picks the subSignal handle), and
// `def tree` re-runs the chain on every access. This test pins the shape.

#[test]
fn class_module_shape_flattened_chain() {
    let output = assert_ok(r#"
class probeMod[w: Nat] impl Module {
    let _ = change_mutable_default("ModuleTree", x => x, ModuleTree.mk(0, nil))
    let _ = create_global("WhenStack", whenStackEmpty)
    let _prev = get_global("ModuleTree")
    let _ = change_mutable("ModuleTree", x => ModuleTree.mk(0 + 1, ModuleDef.mk("probeMod", defaultClockDomain, 0, nil) :: nil))
    let a: UInt[w] = UInt.mk(Some("a"), createPortExpr("input", "UInt", "a", w))
    let b: UInt[w] = UInt.mk(Some("b"), createPortExpr("input", "UInt", "b", w))
    let sum: UInt[w + 1] = UInt.mk(Some("sum"), createPortExpr("output", "UInt", "sum", w + 1))
    let _ = sum := a +^ b
    let _res = get_global("ModuleTree")
    let _ = create_global("ModuleTree", _prev)
    let _ = mkInstanceIfParent(bn.name, "probeMod")
    _res
    let a: UInt[w] = UInt.mk(None, subSignal(bn.name, "a"))
    let b: UInt[w] = UInt.mk(None, subSignal(bn.name, "b"))
    let sum: UInt[w + 1] = UInt.mk(None, subSignal(bn.name, "sum"))
    def tree: ModuleTree =
        let _ = change_mutable_default("ModuleTree", x => x, ModuleTree.mk(0, nil));
        let _ = create_global("WhenStack", whenStackEmpty);
        let _prev = get_global("ModuleTree");
        let _ = change_mutable("ModuleTree", x => ModuleTree.mk(0 + 1, ModuleDef.mk("probeMod", defaultClockDomain, 0, nil) :: nil));
        let a: UInt[w] = UInt.mk(Some("a"), createPortExpr("input", "UInt", "a", w));
        let b: UInt[w] = UInt.mk(Some("b"), createPortExpr("input", "UInt", "b", w));
        let sum: UInt[w + 1] = UInt.mk(Some("sum"), createPortExpr("output", "UInt", "sum", w + 1));
        let _ = sum := a +^ b;
        let _res = get_global("ModuleTree");
        let _ = create_global("ModuleTree", _prev);
        _res
}
println(moduleTreeVL(probeMod.create[8].tree))
println(moduleTreeVL(probeMod.create[8].tree))
"#);
    let expected = r#"module probeMod (
  input wire [7:0] a,
  input wire [7:0] b,
  output wire [8:0] sum
);
  assign sum = (a +^ b);
endmodule"#;
    // Two identical prints: the def-tree chain re-runs cleanly each access
    // (idempotent, no leftover global tree state).
    assert_eq!(output.matches(expected).count(), 2,
        "flattened module class should print identical verilog twice, got: {}", output);
}

// ── constructor statements ──

#[test]
fn class_ctor_statements() {
    // Bare expressions in the class body are constructor statements: they are
    // elaborated (type-checked) in order before the fields are assembled.
    let output = assert_ok(r#"
class Tally {
    let n: Nat = 1
    1 + 1
    def get: Nat = this.n
}
println (Tally.create.get)
"#);
    assert!(output.contains("1"), "ctor statements should not disturb fields: {}", output);
}

// ── operator methods ──

#[test]
fn class_operator_method() {
    let output = assert_ok(r#"
class Tally {
    let n: Nat = 2
    def + (that: Tally): Nat = this.n + that.n
}
println (Tally.create + Tally.create)
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
