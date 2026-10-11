#!/usr/bin/env python3
"""Generate round-4 (sum/product types, pattern matching, exhaustiveness, GADT) probes.

Layout conventions (adjudicated in round 1/4): enum constructors, struct
fields, and match arms each occupy their own line. Prelude names (sum, len,
head, Show, Eq...) are never shadowed.
"""
from pathlib import Path

D = Path(__file__).resolve().parent / "r04-match"
D.mkdir(exist_ok=True)
for f in D.glob("*.typort"):
    f.unlink()

P = {}

def add(fid, src, probe, expect, expect_not=None):
    P[fid] = (src, probe, expect, expect_not)

VECD = (
    "enum MyVec[A: Type 0](len: Nat) {\n"
    "  nil -> MyVec[A] 0\n"
    "  cons[l: Nat](x: A, xs: MyVec[A] l) -> MyVec[A] (l + 1)\n"
    "}\n"
)
FIND = (
    "enum MyFin(n: Nat) {\n"
    "  fz[m: Nat] -> MyFin(m + 1)\n"
    "  fs[m: Nat](i: MyFin(m)) -> MyFin(m + 1)\n"
    "}\n"
)
OPTD = (
    "enum Opt[A: Type 0] {\n"
    "  none -> Opt[A]\n"
    "  some(v: A) -> Opt[A]\n"
    "}\n"
)
COLORD = (
    "enum Color {\n"
    "  red\n"
    "  green\n"
    "  blue\n"
    "}\n"
)

# ---- exhaustiveness ---------------------------------------------------------
add("m01_missing_case", COLORD + "def f(c: Color): Nat = match c {\n  case red => 1\n  case green => 2\n}\n",
    "missing constructor blue -> non-exhaustive error", "error /exhaustive|error/")
add("m02_full_coverage", COLORD + "def f(c: Color): Nat = match c {\n  case red => 1\n  case green => 2\n  case blue => 3\n}\nprintln(f(blue))\n",
    "all constructors covered", "stdout /3/")
add("m03_wildcard_covers", COLORD + "def f(c: Color): Nat = match c {\n  case _ => 9\n}\nprintln(f(red))\n",
    "wildcard arm covers everything", "stdout /9/")
add("m04_bool_both", "def f(b: Boolean): Nat = match b {\n  case true => 1\n  case false => 0\n}\nprintln(f(false))\n",
    "Boolean exhaustive", "stdout /0/")
add("m05_nat_cases", "def f(n: Nat): Nat = match n {\n  case zero => 0\n  case succ(m) => m\n}\nprintln(f(5))\n",
    "Nat zero/succ exhaustive", "stdout /4/")
add("m06_option_cases", OPTD + "def f[A: Type 0](o: Opt[A]): Nat = match o {\n  case none => 0\n  case some(v) => 1\n}\nprintln(f(none))\nprintln(f(some(8)))\n",
    "Opt none/some exhaustive", "stdout /0/")
add("m07_wildcard_then_case", "enum Color2 {\n  red\n  green\n}\ndef f(c: Color2): Nat = match c {\n  case _ => 0\n  case red => 1\n}\nprintln(f(green))\n",
    "case after wildcard (probe: unreachable or accepted)", "error /error/")
add("m08_dup_case", "def f(n: Nat): Nat = match n {\n  case zero => 0\n  case zero => 1\n  case succ(m) => m\n}\nprintln(f(2))\n",
    "duplicate arm accepted silently (quirk; expect first-wins)", "stdout /1/")

# ---- nested / deep patterns ----------------------------------------------------
add("m09_deep_succ", "def f(n: Nat): Nat = match n {\n  case zero => 0\n  case succ(zero) => 1\n  case succ(succ(m)) => 2\n}\nprintln(f(5))\n",
    "deep succ(succ(m)) pattern", "stdout /2/")
add("m10_nested_opt", OPTD + "def f(o: Opt[Opt[Nat]]): Nat = match o {\n  case none => 0\n  case some(none) => 1\n  case some(some(v)) => v\n}\nprintln(f(some(none)))\nprintln(f(some(some(7))))\n",
    "nested constructor patterns", "stdout /1/")
add("m11_nested_in_arm_body", "def f(n: Nat, m: Nat): Nat = match n {\n  case zero => match m {\n    case zero => 100\n    case succ(k) => k\n  }\n  case succ(k) => k\n}\nprintln(f(0)(0))\n",
    "match inside an arm body; curried call", "stdout /100/")
add("m12_nested_in_arm_body2", "def f(n: Nat, m: Nat): Nat = match n {\n  case zero => match m {\n    case zero => 100\n    case succ(k) => k\n  }\n  case succ(k) => k\n}\nprintln(f(0, 0))\n",
    "match inside an arm body, two-arg call", "stdout /100/")

# ---- dependent matching / GADT ------------------------------------------------
add("m13_vec_nil_cons", VECD + "def vlen[A: Type 0][l: Nat](v: MyVec[A] l): Nat = match v {\n  case nil => 0\n  case cons(w, xs) => 1\n}\ndef v0: MyVec[Nat] 0 = MyVec.nil\ndef v1: MyVec[Nat] 1 = MyVec.cons[Nat][0](1, MyVec.nil)\nprintln(vlen(v0))\nprintln(vlen(v1))\n",
    "Vec nil/cons match with implicit length index (qualified ctors; bare nil/cons hit prelude Vec per D1)", "stdout /0/")
add("m14_fin_cases", FIND + "def toNat(i: MyFin(3)): Nat = match i {\n  case fz => 0\n  case fs(j) => 1\n}\nprintln(toNat(fz))\nprintln(toNat(fs(fz)))\n",
    "Fin indexed match", "stdout /0/")
add("m15_eq_refl_j", "def useEq[A: Type 0](x: A)(e: Eq(x, x)): Nat = match e {\n  case refl(a) => 1\n}\nprintln(useEq(3)(rfl))\n",
    "J-style match on Eq refl", "stdout /1/")
add("m16_eq_motive_dependent", "def f[A: Type 0](x: A, y: A)(e: Eq(x, y)): Eq(y, x) = match e {\n  case refl(a) => rfl\n}\nprintln(f(1, 1)(rfl))\n",
    "dependent motive: refl arm transports x to y", "ok")
add("m17_gadt_refine_index", VECD + "def vhead[A: Type 0](v: MyVec[A] 1): A = match v {\n  case cons(w, xs) => w\n}\nprintln(vhead(cons(9, nil)))\n",
    "GADT: index 1 refines to cons arm (nil impossible; probe exhaustiveness)", "error /error/")
add("m18_match_scrut_reduce", "def f: Nat = match 2 + 1 {\n  case zero => 0\n  case succ(m) => m\n}\nprintln(f)\n",
    "scrutinee reduces before match", "stdout /2/")

# ---- structs / products -----------------------------------------------------------
add("s01_struct_basic", "struct Pair {\n  fst: Nat\n  snd: Nat\n}\ndef p: Pair = Pair.mk(3, 4)\nprintln(p.fst * 10 + p.snd)\n",
    "struct make + field access", "stdout /34/")
add("s02_struct_dependent", "struct DPair[A: Type 0] {\n  fst: A\n  snd: A\n}\ndef p: DPair[Nat] = DPair.mk(2, 5)\nprintln(p.fst + p.snd)\n",
    "parametrized struct", "stdout /7/")
add("s03_struct_nested", "struct Inner {\n  v: Nat\n}\nstruct Outer {\n  i: Inner\n}\ndef o: Outer = Outer.mk(Inner.mk(6))\nprintln(o.i.v)\n",
    "nested struct field chain", "stdout /6/")
add("s04_struct_missing_field", "struct Pair3 {\n  fst: Nat\n  snd: Nat\n}\ndef p: Pair3 = Pair3.mk(3)\n",
    "missing field in literal errors", "error /error/")
add("s05_struct_wrong_type", "struct Pair4 {\n  fst: Nat\n  snd: Nat\n}\ndef p: Pair4 = Pair4.mk(true, 4)\n",
    "wrong field type errors", "error /error/")
add("s06_struct_extra_field", "struct Pair5 {\n  fst: Nat\n  snd: Nat\n}\ndef p: Pair5 = Pair5.mk(3, 4, 5)\n",
    "extra argument in literal errors", "error /error/")
add("s07_struct_pattern_match", "struct Pair6 {\n  fst: Nat\n  snd: Nat\n}\ndef f(p: Pair6): Nat = match p {\n  case Pair6.mk(a, b) => a + b\n}\nprintln(f(Pair6.mk(10, 20)))\n",
    "struct ctor patterns (P.mk(a, b)) NOT supported in match (parse error; quirk)", "error /error/")
add("s08_struct_field_of_expr", "struct W {\n  n: Nat\n}\ndef f(w: W): Nat = match w.n {\n  case zero => 0\n  case succ(m) => m\n}\nprintln(f(W.mk(4)))\n",
    "field access as scrutinee", "stdout /3/")

# ---- tuples ---------------------------------------------------------------------------
add("t01_tuple_literal", "def t = (1, 2)\nprintln(t)\n",
    "tuple literal creates value", "ok")
add("t02_tuple_match", "def f(t: (Nat, Nat)): Nat = match t {\n  case (a, b) => a + b\n}\nprintln(f((3, 4)))\n",
    "tuple pattern in match NOT supported (bizarre error; quirk)", "error /error/")
add("t03_tuple_arity3", "def t = (1, 2, 3)\nprintln(t)\n",
    "3-tuple literal", "ok")
add("t04_nested_tuple", "def t = ((1, 2), 3)\nprintln(t)\n",
    "nested tuple", "ok")

# ---- sum type semantics ------------------------------------------------------------------
add("u01_enum_data_carrying", "enum Shape {\n  circle(r: Nat)\n  rect(w: Nat, h: Nat)\n}\ndef shArea(s: Shape): Nat = match s {\n  case circle(r) => 3 * r * r\n  case rect(w, h) => w * h\n}\nprintln(shArea(rect(3, 4)))\nprintln(shArea(circle(2)))\n",
    "data-carrying enum match (1-arg and 2-arg ctors)", "stdout /12/")
add("u02_enum_recursive", "enum Tree {\n  leaf(v: Nat)\n  node(l: Tree, r: Tree)\n}\ndef treeSum(t: Tree): Nat = match t {\n  case leaf(v) => v\n  case node(l, r) => treeSum(l) + treeSum(r)\n}\nprintln(treeSum(node(leaf(1), node(leaf(2), leaf(3)))))\n",
    "recursive enum + recursion", "stdout /6/")
add("u03_ctor_qualified", "enum Color7 {\n  red\n  green\n}\ndef f(c: Color7): Nat = match c {\n  case Color7.red => 1\n  case Color7.green => 2\n}\nprintln(f(Color7.green))\n",
    "qualified ctor names (Color7.red) NOT supported in patterns (quirk)", "error /error/")
add("u04_void_match", "enum Void {\n}\ndef absurd[A: Type 0](v: Void): A = match v { }\nprintln(0)\n",
    "empty enum: absurd function (probe: empty match allowed?)", "error /error/")
add("u05_single_ctor", "enum UOne {\n  u1\n}\ndef f(u: UOne): Nat = match u {\n  case u1 => 1\n}\nprintln(f(u1))\n",
    "single-constructor match", "stdout /1/")

# ---- coverage subtleties -------------------------------------------------------------------
add("x01_zero_and_wildcard", "def f(n: Nat): Nat = match n {\n  case zero => 0\n  case _ => 1\n}\nprintln(f(3))\nprintln(f(0))\n",
    "zero + wildcard coverage", "stdout /1/")
add("x02_shadowed_binder", "def f(n: Nat): Nat = match n {\n  case zero => 0\n  case succ(n) => n\n}\nprintln(f(4))\n",
    "pattern binder shadows scrutinee name", "stdout /3/")
add("x03_match_result_is_value", "def f(b: Boolean): Nat = match b {\n  case true => 1\n  case false => 0\n}\ndef g: Nat = f(true) + f(false)\nprintln(g)\n",
    "match expression used inside arithmetic", "stdout /1/")
add("x04_arm_type_mismatch", "def f(b: Boolean): Nat = match b {\n  case true => 1\n  case false => \"no\"\n}\n",
    "arm body type mismatch errors", "error /error/")
add("x05_scrut_type_unknown", "def f(x: _): Nat = match x {\n  case zero => 0\n  case succ(m) => m\n}\nprintln(f(3))\n",
    "scrutinee type hole (probe)", "error /unsolved|error/")
add("x06_wildcard_binder_mix", COLORD + "def f(c: Color): Nat = match c {\n  case red => 1\n  case _ => 2\n}\nprintln(f(blue) + f(red))\n",
    "specific + wildcard mix", "stdout /3/")
add("x07_deep_pattern_3", "def f(n: Nat): Nat = match n {\n  case zero => 0\n  case succ(zero) => 1\n  case succ(succ(zero)) => 2\n  case succ(succ(succ(m))) => m\n}\nprintln(f(6))\n",
    "3-deep succ patterns + default", "stdout /3/")
add("x08_qualified_ctor_expr", "enum Color9 {\n  red\n  green\n}\nprintln(Color9.red)\n",
    "qualified constructor expression", "stdout /red/")

hdr = "// probe: {p}\n// expect: {e}\n"
for fid, (src, probe, expect, expect_not) in P.items():
    text = hdr.format(p=probe, e=expect)
    if expect_not:
        text += f"// expect-not: {expect_not}\n"
    (D / f"{fid}.typort").write_text(text + src, encoding="utf-8")

print(f"wrote {len(P)} probes to {D}")
