#!/usr/bin/env python3
"""Generate round-2 (core evaluation / conversion / universes) probe corpus.

Conventions learned from adjudication (docs/review-2026-10-11/r02-core.md):
- never shadow prelude names (id, double, count, eq, Show, ... are taken);
- match arms, enum constructors, struct fields each need their own line
  (the parser is layout-sensitive inside brace groups).
"""
from pathlib import Path

D = Path(__file__).resolve().parent / "r02-core"
D.mkdir(exist_ok=True)
for f in D.glob("*.typort"):
    f.unlink()

P = {}

def add(fid, src, probe, expect, expect_not=None):
    P[fid] = (src, probe, expect, expect_not)

# ---- beta / application semantics ---------------------------------------
add("c01_beta_id", "def myid(A: Type 0)(x: A): A = x\nprintln(myid(Nat)(41) + 1)\n",
    "beta: identity application evaluates", "stdout /42/")
add("c02_beta_nested", "def add(x: Nat, y: Nat): Nat = x + y\nprintln(add(add(1,2), add(3,4)))\n",
    "nested beta redexes fully evaluate", "stdout /10/")
add("c03_delta_prelude", "println(nat_add(2, 3))\n",
    "delta: prelude def unfolds in evaluation", "stdout /5/")
add("c04_eval_order", "def f(x: Nat): Nat = x * 0\nprintln(f(nat_add(2, 3)))\n",
    "arguments evaluate inside applications", "stdout /0/")

# ---- conversion / definitional equality -----------------------------------
add("c05_conv_beta", "def two: Nat = 1 + 1\nprintln(two)\n",
    "conversion under beta: 1+1 =?= 2 evaluates", "stdout /2/")
add("c06_conv_in_type", "def f(n: Nat): Eq(n + 0, n) = _\n",
    "types convert under arithmetic (hole keeps it unsolved)", "error /unsolved/")
add("c07_noncumulativity", "def T: Type 1 = Type 0\nprintln(0)\n",
    "Type 0 : Type 1 (a single step is fine)", "ok")
add("c08_noncumulativity_fail", "def T: Type 5 = Type 0\n",
    "NO cumulativity: Type 0 does not check against Type 5", "error /unify|can't unify|error/")
add("c09_universe_of_pi", "def f: Nat -> Type 0 = n => Boolean\nprintln(0)\n",
    "Pi over small types; polymorphic fn typechecks", "ok")
add("c10_universe_pi_level", "def g: (A: Type 1) -> A -> A = A => x => x\nprintln(0)\n",
    "large elimination Pi at Type 1", "ok")

# ---- eta / extensionality ----------------------------------------------------
add("c11_eta_lam", "def f: Nat -> Nat = n => n + 1\ndef g: Nat -> Nat = n => f(n)\nprintln(g(1))\n",
    "eta-expanded application still evaluates", "stdout /2/")
add("c12_conv_eta", "def idn: Nat -> Nat = n => n\ndef h: Nat -> Nat = idn\nprintln(h(5))\n",
    "eta-related terms are definitionally equal via def aliasing", "stdout /5/")

# ---- neutrality / stuck terms -------------------------------------------------
add("c13_neutral_var", "def f(n: Nat): Nat = n + 1\nprintln(f)\n",
    "printing a function value (neutral) must not crash", "ok")
add("c14_stuck_add", "def f(n: Nat): Nat = n + 1\ndef pEq: Eq(f(0), 1) = rfl\nprintln(pEq)\n",
    "stuck term reduces when instantiated: Eq(f 0, 1) holds by rfl", "ok")
add("c15_neutral_index", "def f(l: Nat)(n: Nat): Nat = l + n\nprintln(f(1)(2))\n",
    "neutral-headed application on variables stays well-typed", "stdout /3/")

# ---- definitional proof checks ---------------------------------------------
add("c16_refl_add0", "def p: Eq(nat_add(2,3), 5) = rfl\nprintln(p)\n",
    "rfl proves closed arithmetic equalities", "ok")
add("c17_refl_fail", "def p: Eq(nat_add(2,3), 6) = rfl\n",
    "rfl must FAIL on false closed equality", "error /error/")
add("c18_eq_symm", "def p: Eq(5, nat_add(2,3)) = symm(rfl)\nprintln(p)\n",
    "symm of a definitional equality", "ok")
add("c19_cong", "def f(x: Nat): Nat = x * 2\ndef p: Eq(f(nat_add(1,1)), 4) = rfl\nprintln(p)\n",
    "conversion under cong target: f(1+1) =?= f(2) =?= 4", "ok")

# ---- recursion & fixpoints ------------------------------------------------------
add("c20_recursion", "def dbl2(n: Nat): Nat = match n {\n  case zero => 0\n  case succ(m) => dbl2(m) + 2\n}\nprintln(dbl2(4))\n",
    "structural recursion evaluates", "stdout /8/")
add("c21_deep_eval", "def cnt1(n: Nat): Nat = match n {\n  case zero => 0\n  case succ(m) => cnt1(m) + 1\n}\nprintln(cnt1(50))\n",
    "50-deep recursion evaluates", "stdout /50/")
add("c22_nonterm_guard", "def bad(n: Nat): Nat = bad(n)\n",
    "self-call with no structural decrease: termination checker verdict", "error /termination|error/")
add("c23_ackermann_small", "def ack(m: Nat, n: Nat): Nat = match m {\n  case zero => n + 1\n  case succ(mm) => match n {\n    case zero => ack(mm, 1)\n    case succ(nn) => ack(mm, ack(m, nn))\n  }\n}\nprintln(ack(2, 3))\n",
    "nested recursion (ack 2 3 = 9) evaluates", "stdout /9/")

# ---- pattern-match evaluation -----------------------------------------------------
add("c24_match_bool", "def b(v: Boolean): Nat = match v {\n  case true => 1\n  case false => 0\n}\nprintln(b(true))\n",
    "match on Boolean evaluates", "stdout /1/")
add("c25_match_nat_deep", "def prd(n: Nat): Nat = match n {\n  case zero => 0\n  case succ(m) => m\n}\nprintln(prd(7))\n",
    "match binds constructor args", "stdout /6/")
add("c26_match_expr_reduction", "def f(n: Nat): Nat = match nat_add(n, 1) {\n  case zero => 99\n  case succ(m) => m\n}\nprintln(f(4))\n",
    "scrutinee reduces before matching", "stdout /4/")

# ---- closures / environments --------------------------------------------------------
add("c27_closure_capture", "def adder(n: Nat): Nat -> Nat = m => n + m\ndef five: Nat -> Nat = adder(5)\nprintln(five(3))\n",
    "closure captures environment", "stdout /8/")
add("c28_shadowing", "def f(x: Nat): Nat =\n  let x: Nat = 10;\n  x\nprintln(f(1))\n",
    "let shadows parameter", "stdout /10/")
add("c29_higher_order", "def twice(f: Nat -> Nat, x: Nat): Nat = f(f(x))\nprintln(twice(n => n + 3, 1))\n",
    "higher-order application", "stdout /7/")
add("c30_partial_app", "def add(x: Nat, y: Nat): Nat = x + y\ndef inc: Nat -> Nat = add(1)\nprintln(inc(41))\n",
    "partial application via currying", "stdout /42/")

# ---- literal & primop edges -----------------------------------------------------------
add("c31_arith_mixed", "println((1 + 2) * (3 + 4) - 1)\n",
    "operator precedence and mixed arithmetic", "stdout /20/")
add("c32_div_mod", "println(nat_div(7, 2))\nprintln(nat_mod(7, 2))\n",
    "prelude div/mod primops (nat_mod absent is the recorded quirk)", "error /error/")
add("c33_zero_div", "println(nat_div(5, 0))\n",
    "division by zero: saturating (returns dividend), must not hang", "stdout /5/")
add("c34_sub_underflow", "println(nat_sub(1, 5))\n",
    "truncated subtraction underflow semantics", "stdout /0/")
add("c35_eq_nat_op", "println(nat_eq(3, 3))\nprintln(nat_eq(3, 4))\n",
    "Nat equality decision", "ok")

# ---- linearity of results (quote/print) ---------------------------------------------------
add("c36_print_deep", "def big2(n: Nat): Nat = match n {\n  case zero => 0\n  case succ(m) => big2(m) + 1\n}\nprintln(big2(100))\n",
    "100-deep result quoting round-trips", "stdout /100/")
add("c37_print_type", "println(Nat)\n",
    "printing a type value", "ok")
add("c38_print_string_concat", 'println(string_concat("foo", "bar"))\n',
    "string primop evaluates", "stdout /foobar/")

# ---- error paths -----------------------------------------------------------------------------
add("c39_wrong_ann", "def x: Nat = \"str\"\n",
    "String literal against Nat annotation errors", "error /error/")
add("c40_apply_nonfn", "def x: Nat = 3\nprintln(x(1))\n",
    "applying a non-function errors cleanly", "error /error/")
add("c41_undefined_var", "println(no_such_name)\n",
    "undefined name errors with span", "error /not in scope|error/")
add("c42_type_in_term", "def f: Nat -> Nat = Nat\n",
    "using a type as a function body errors", "error /error/")
add("c43_big_product", "def p: Nat = 1 * 2 * 3 * 4 * 5 * 6 * 7 * 8 * 9 * 10\nprintln(p)\n",
    "chained multiplication evaluates (3628800)", "stdout /3628800/")

hdr = "// probe: {p}\n// expect: {e}\n"
for fid, (src, probe, expect, expect_not) in P.items():
    text = hdr.format(p=probe, e=expect)
    if expect_not:
        text += f"// expect-not: {expect_not}\n"
    (D / f"{fid}.typort").write_text(text + src, encoding="utf-8")

print(f"wrote {len(P)} probes to {D}")
