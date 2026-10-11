#!/usr/bin/env python3
"""Generate round-5 (typeclass / instance resolution) probes — canonical idioms.

Adjudicated conventions (examples/typeclass_complex.typort + docs §4/§5):
- traits usually declared WITHOUT type params (Self is the implicit first
  param; `Trait[T]` in a constraint fills Self);
- constrained generics: `def f[T][d: Trait[T]](x: T) = d.method x`
  (dict projection; method bodies use `this`);
- receiver dot-call works on CONCRETE values (`four.dbl_m`), NOT on type
  variables (recorded limitation F5-1);
- prelude-instance dicts can stay silently neutral (recorded F5-2);
- generic *conditional* instances (`impl[T: C] ...`) unsupported (prelude
  show.typort documents this);
- supertraits: `trait Sub: Base` bare form.
"""
from pathlib import Path

D = Path(__file__).resolve().parent / "r05-typeclass"
D.mkdir(exist_ok=True)
for f in D.glob("*.typort"):
    f.unlink()

P = {}

def add(fid, src, probe, expect, expect_not=None):
    P[fid] = (src, probe, expect, expect_not)

TC = (
    "trait Doubles {\n"
    "  def dbl_val: Nat\n"
    "}\n"
    "impl Doubles for Nat {\n"
    "  def dbl_val: Nat = this + this\n"
    "}\n"
)

# ---- basic trait / impl / method call -------------------------------------
add("q01_receiver_method", TC + "def useD0[T][d: Doubles[T]](t: T): Nat = d.dbl_val t\nprintln(useD0(4))\n",
    "dict-projected call on a concrete instance", "stdout /8/")
add("q02_inherent_impl", "impl Nat {\n  def triple: Nat = this * 3\n}\ndef five: Nat = 5\nprintln(five.triple)\n",
    "inherent impl adds a method (receiver dot-call)", "stdout /15/")
add("q04_default_method", "trait Greet {\n  def hello: String = \"hi\"\n}\nimpl Greet for Nat {\n}\ndef useG[T][d: Greet[T]](t: T): String = d.hello t\nprintln(useG(1))\n",
    "default method body used when impl is empty", "stdout /hi/")
add("q05_no_instance", "trait Marks {\n  def mark: Nat\n}\nimpl Marks for Boolean {\n  def mark: Nat = 1\n}\ndef tt0 = true\nprintln(tt0.mark)\n",
    "control: instance exists -> works", "stdout /1/")
add("q06_dup_impl", "trait Dup5 {\n  def m5(x: Nat): Nat\n}\nimpl Dup5 for Nat {\n  def m5(x: Nat): Nat = 1\n}\nimpl Dup5 for Nat {\n  def m5(x: Nat): Nat = 2\n}\nprintln(Dup5.m5(0))\n",
    "duplicate instance for the same type (probe)", "error /error/")

# ---- constraint contexts (canonical dict idiom) -----------------------------
add("q07_dict_constraint", TC + "def useD[T][d: Doubles[T]](t: T): Nat = d.dbl_val t\nprintln(useD(6))\n",
    "[T][d: Doubles[T]] implicit fills the dict (canonical idiom)", "stdout /12/")
add("q08_two_instances", TC + "impl Doubles for Boolean {\n  def dbl_val: Nat = 1\n}\ndef useD[T][d: Doubles[T]](t: T): Nat = d.dbl_val t\nprintln(useD(6))\nprintln(useD(true))\n",
    "search picks the matching instance among several", "stdout /12/")
add("q09_param_type_instance", "enum Box2[A: Type 0] {\n  mk(v: A) -> Box2[A]\n}\ntrait Unbox {\n  def un_n: Nat\n}\nimpl[A: Type 0] Unbox for Box2[A] {\n  def un_n: Nat = 1\n}\ndef b: Box2[Nat] = Box2.mk(3)\nprintln(b.un_n)\n",
    "impl[A] Trait for Box2[A] (generic instance, unconditional)", "stdout /1/")
add("q10_conditional_instance", "trait Half {\n  def half_v(x: Nat): Nat\n}\nimpl Half for Nat {\n  def half_v(x: Nat): Nat = nat_div(x, 2)\n}\ntrait Quarter {\n  def quarter_v(x: Nat): Nat\n}\nimpl[T: Half] Quarter for T {\n  def quarter_v(x: Nat): Nat = 4\n}\n",
    "impl[T: Half] conditional instance: NOT supported (prelude show.typort documents)", "error /error/")
add("q11_supertrait_basic", "trait Base2 {\n  def baseM: Nat\n}\ntrait Sub2: Base2 {\n  def subM: Nat\n}\nimpl Sub2 for Nat {\n  def baseM: Nat = 1\n  def subM: Nat = 2\n}\ndef useS2[T][d: Sub2[T]](t: T): Nat = d.subM t\nprintln(useS2(0))\n",
    "bare supertrait decl; impl provides both methods", "stdout /2/")
add("q12_supertrait_dispatch", "trait Base3 {\n  def baseM: Nat\n}\ntrait Sub3: Base3 {\n  def subM: Nat\n}\nimpl Sub3 for Nat {\n  def baseM: Nat = 1\n  def subM: Nat = 2\n}\ndef wantBase[T][d: Base3[T]](t: T): Nat = d.baseM t\nprintln(wantBase(9))\n",
    "supertrait dict satisfied by subtrait instance", "stdout /1/")

# ---- operators ---------------------------------------------------------------
add("q13_operator_trait", "println(2 + 3)\nprintln(2 * 4)\n",
    "prelude operator traits resolve on Nat", "stdout /5/")
add("q14_custom_operator", "trait Plus2[T, O: outParam(Type 0)] {\n  def ++(that: T): O\n}\nimpl Plus2[Nat, Nat] for Nat {\n  def ++(that: Nat): Nat = this + 100\n}\nprintln(1 ++ 2)\n",
    "user operator trait ++ as infix WORKS", "stdout /101/")

# ---- derive ---------------------------------------------------------------------
add("q18_derive_show", "#[derive(Show)]\nenum Fruit {\n  apple\n  pear\n}\nprintln(apple.show)\n",
    "#[derive(Show)] zero-arg ctors", "stdout /apple/")
add("q19_derive_show_data", "#[derive(Show)]\nenum Snack {\n  bar(n: Nat)\n}\nprintln(bar(3).show)\n",
    "derive(Show) single-case enum WITH ctor args (fixed R5)", "stdout /bar\\(3\\)/")
add("q19b_derive_show_multi_data", "#[derive(Show)]\nenum Snack2 {\n  plain\n  bar2(n: Nat)\n}\nprintln(bar2(4).show)\nprintln(plain.show)\n",
    "derive(Show) multi-case with args", "stdout /bar2\\(4\\)/")
add("q38_derive_show_struct", "#[derive(Show)]\nstruct Pts {\n  x: Nat\n  y: Nat\n}\ndef p: Pts = Pts.mk(1, 2)\nprintln(p.show)\n",
    "derive(Show) on struct (X.mk case keeps this.field path)", "stdout /Pts\\(1, 2\\)/")

# ---- recorded findings ---------------------------------------------------------
add("f5_1_typevar_receiver", TC + "def useR[T][d: Doubles[T]](t: T): Nat = t.dbl_val 3\nprintln(useR(6))\n",
    "F5-1: receiver method on a type VARIABLE ignores the constraint (unsupported)", "error /error/")
add("f5_2_prelude_dict_silent", "def print_it[T][s: Show[T]](x: T): String = s.show x\nprintln(print_it(9))\n",
    "F5-2: prelude-instance dict can stay silently neutral (prints ?m.show, no error)", "ok")
add("f5_4_trait_arity_lax", "trait TwoP[A, B] {\n  def m2(a: A): B\n}\nimpl TwoP[Nat] for Nat {\n  def m2(a: Nat): Nat = a\n}\n\n",
    "impl arity < trait arity accepted without error (probe; laxness quirk)", "ok")

# ---- error paths ------------------------------------------------------------------
add("q20_wrong_instance_type", TC + "println(Doubles.dbl_val(true))\n",
    "method used at a type with no instance errors", "error /error/")
add("q21_missing_method", "trait Half2 {\n  def half_v(x: Nat): Nat\n}\nimpl Half2 for Nat {\n}\nprintln(Half2.half_v(4))\n",
    "impl missing a required method (probe: error at impl or at use)", "error /error/")
add("q22_trait_as_value", "trait Half3 {\n  def half_v(x: Nat): Nat\n}\nprintln(Half3)\n",
    "printing a trait name (probe)", "ok")

# ---- prelude interplay ---------------------------------------------------------------
add("q24_prelude_show_nat", "def ff: Nat = 42\nprintln(ff.show)\n",
    "prelude show on Nat via receiver", "stdout /42/")
add("q25_prelude_show_string", "println(\"abc\".show)\n",
    "prelude Show on String", "stdout /abc/")
add("q27_eq_fn", "println(nat_eq(3, 3))\n",
    "nat_eq works", "stdout /true/")
add("q27b_eq_sugar", "println(3 == 3)\n",
    "== sugar on Nat (probe)", "error /error/")
add("q28_compare_operator", "println(1 < 2)\nprintln(2 < 1)\n",
    "< on Nat via prelude trait", "stdout /true/")

# ---- methods / contexts --------------------------------------------
add("q31_method_with_arg", "trait Picker {\n  def pickN(k: Nat): Nat\n}\nimpl Picker for Nat {\n  def pickN(k: Nat): Nat = this + k\n}\ndef t3: Nat = 3\nprintln(t3.pickN 4)\n",
    "one-arg method called `obj.method arg` (this receiver)", "stdout /7/")
add("q32_method_default_uses_other", "trait Chain2 {\n  def one(x: Nat): Nat\n  def two(x: Nat): Nat = one(x) + 1\n}\nimpl Chain2 for Nat {\n  def one(x: Nat): Nat = 10\n}\nprintln(Chain2.two(0))\n",
    "default method calls the impl's override (probe: qualified dict form)", "error /error/")
add("q33_dict_via_prelude_show", "trait Needs {\n  def need_v(x: Nat): Nat\n}\nimpl[T][s: Show[T]] Needs for T {\n  def need_v(x: Nat): Nat = 1\n}\n",
    "impl constrained by a prelude trait (probe)", "error /error/")
add("q34_impl_for_fn_type", "trait FnMark {\n  def marked(x: Nat): Nat\n}\nimpl FnMark for (Nat -> Nat) {\n  def marked(x: Nat): Nat = 3\n}\ndef g: Nat -> Nat = n => n\nprintln(FnMark.marked(g))\n",
    "instance for a function type (probe)", "error /error/")
add("q35_two_constraints", "trait CA {\n  def ca_v: Nat\n}\ntrait CB {\n  def cb_v: Nat\n}\nimpl CA for Nat {\n  def ca_v: Nat = 1\n}\nimpl CB for Nat {\n  def cb_v: Nat = 2\n}\ndef both[T][a: CA[T], b: CB[T]](t: T): Nat = (a.ca_v t) + (b.cb_v t)\nprintln(both(0))\n",
    "two dict constraints; unparenthesized d.m t + e.n t binds t as + lhs (precedence quirk)", "stdout /3/")
add("q36_instance_on_tuple", "trait TupM {\n  def tm_v: Nat\n}\nimpl TupM for (Nat, Nat) {\n  def tm_v: Nat = 4\n}\ndef t: (Nat, Nat) = (1, 2)\nprintln(t.tm_v)\n",
    "instance for a tuple type (probe)", "error /error/")
add("q37_shadowed_method_name", "trait SameN {\n  def m7: Nat\n}\nimpl SameN for Nat {\n  def m7: Nat = 5\n}\ndef m7(x: Nat): Nat = 6\ndef zz: Nat = 0\nprintln(zz.m7)\nprintln(m7(0))\n",
    "top-level fn and trait method coexist with the same name", "stdout /5/")
add("q40_trait_result_chain", "trait Maker {\n  def make: String\n}\nimpl Maker for Nat {\n  def make: String = \"made\"\n}\ndef useMaker[T][d: Maker[T]](t: T): String = d.make t\nprintln(useMaker(0))\n",
    "trait method result feeding another constrained call", "stdout /made/")
add("q41_chained_receivers", "impl Nat {\n  def deep: Nat = this + 1\n}\ndef one2: Nat = 1\nprintln(one2.deep.deep)\n",
    "chained receiver calls on a concrete type", "stdout /3/")
add("q42_polymorphic_recursion", "enum L2[A: Type 0] {\n  n2 -> L2[A]\n  c2(x: A, tl: L2[A]) -> L2[A]\n}\nimpl[A: Type 0] L2[A] {\n  def lenOf: Nat = match this {\n    case n2 => 0\n    case c2(x, tl) => tl.lenOf + 1\n  }\n}\ndef ll: L2[Nat] = c2(1, c2(2, n2[Nat]))\nprintln(ll.lenOf)\n",
    "generic inherent impl with receiver recursion", "stdout /2/")
add("q43_empty_trait_marker", "trait Empty5 {\n}\ndef useE[T][d: Empty5[T]](t: T): Nat = 1\nimpl Empty5 for Nat {\n}\ndef z: Nat = 0\nprintln(useE(z))\n",
    "empty trait round-trips as a marker via dict", "stdout /1/")
add("q44_ambiguity_detection", "trait FooQ { def methodQ(x: Nat): String }\ntrait BarQ { def methodQ(x: Nat): String }\nimpl FooQ for Boolean {\n  def methodQ(x: Nat): String = \"foo\"\n}\nimpl BarQ for Boolean {\n  def methodQ(x: Nat): String = \"bar\"\n}\ndef tt2 = true\nprintln(tt2.methodQ)\n",
    "same method in two satisfied traits -> ambiguity error (doc §5.2)", "error /ambiguous|error/")

hdr = "// probe: {p}\n// expect: {e}\n"
for fid, (src, probe, expect, expect_not) in P.items():
    text = hdr.format(p=probe, e=expect)
    if expect_not:
        text += f"// expect-not: {expect_not}\n"
    (D / f"{fid}.typort").write_text(text + src, encoding="utf-8")

print(f"wrote {len(P)} probes to {D}")
