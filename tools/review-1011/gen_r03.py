#!/usr/bin/env python3
"""Generate round-3 (holes, implicit arguments, elaboration) probe corpus."""
from pathlib import Path

D = Path(__file__).resolve().parent / "r03-implicit"
D.mkdir(exist_ok=True)
for f in D.glob("*.typort"):
    f.unlink()

P = {}

def add(fid, src, probe, expect, expect_not=None):
    P[fid] = (src, probe, expect, expect_not)

# ---- holes ----------------------------------------------------------------
add("i01_hole_body", "def x: Nat = _\n",
    "hole in def body -> unsolved meta error", "error /unsolved/")
add("i02_hole_infer_type", "def x = (_: Nat)\n",
    "annotated hole expression (typed hole syntax probe)", "error /error/")
add("i03_hole_let", "def f: Nat =\n  let y: Nat = _;\n  y\n",
    "hole in let RHS", "error /unsolved/")
add("i04_hole_match_arm", "def f(v: Boolean): Nat = match v {\n  case true => 1\n  case false => _\n}\n",
    "hole in one match arm (arms on separate lines: layout)", "error /unsolved/")
add("i05_hole_scrutinee", "def f: Nat = match _ { case zero => 0 }\n",
    "hole as scrutinee", "error /error/")
add("i06_many_holes", "def f(a: Nat): Nat = _ + _ + a\n",
    "several holes in one expression", "error /unsolved/")
add("i07_hole_type_pos", "def f: _ = 3\nprintln(f)\n",
    "hole in type annotation solves to Nat by unification", "stdout /3/")
add("i08_hole_print", "println(_: Nat)\n",
    "hole directly in println", "error /unsolved|error/")

# ---- implicit arguments -----------------------------------------------------
add("i09_implicit_auto", "def idd[A: Type 0](x: A): A = x\nprintln(idd(5))\n",
    "implicit A auto-solved from the explicit argument", "stdout /5/")
add("i10_implicit_explicit", "def idd[A: Type 0](x: A): A = x\nprintln(idd[Nat](5))\n",
    "explicit implicit application", "stdout /5/")
add("i11_implicit_named", "def idd[A: Type 0](x: A): A = x\nprintln(idd[A = Nat](5))\n",
    "named implicit application", "stdout /5/")
add("i12_implicit_lambda", "def idf: [A: Type 0] -> A -> A = [A] => x => x\nprintln(idf[Nat](7))\n",
    "implicit lambda binds the implicit Pi", "stdout /7/")
add("i13_implicit_wrong_type", "def idd[A: Type 0](x: A): A = x\nprintln(idd[Nat](true))\n",
    "explicit implicit mismatch (Nat vs Boolean arg) must fail", "error /unify|error/")
add("i14_implicit_order", "def f[A: Type 0, B: Type 0](g: A -> B, x: A): B = g(x)\ndef inc(n: Nat): Nat = n + 1\nprintln(f[Nat, Nat](inc, 2))\n",
    "multiple implicits resolved in order", "stdout /3/")
add("i15_implicit_dep_chain", "def f[A: Type 0](x: A, y: A): A = x\nprintln(f(3, 4))\n",
    "dependent implicit chain: both args share A", "stdout /3/")
add("i16_implicit_partially_explicit", "def f[A: Type 0, B: Type 0](x: A, y: B): B = y\nprintln(f[Nat](1, true))\n",
    "partial implicit application: B from y", "stdout /true/")
add("i17_implicit_expected_type", "def the[A: Type 0](x: A): A = x\ndef u: Nat = the(3)\nprintln(u)\n",
    "annotation-driven implicit solving (bidirectional)", "stdout /3/")
add("i18_implicit_in_pattern", "enum Option[A: Type 0] { none -> Option[A] some(v: A) -> Option[A] }\ndef d[A: Type 0](o: Option[A]): A = match o { case none => _ case some(v) => v }\nprintln(d(some(9)))\n",
    "implicit type parameter on a match function (hole in dead arm)", "error /unsolved/")

# ---- lambda checking ----------------------------------------------------------
add("i19_check_lambda", "def f: Nat -> Nat = x => x + 1\nprintln(f(1))\n",
    "lambda checked against Pi (check mode)", "stdout /2/")
add("i20_check_lambda_implicit_pi", "def f: (x: Nat) -> [b: Boolean] -> Nat = x => [b] => x\nprintln(f(2))\n",
    "implicit lambda inserted when checking against implicit Pi", "stdout /2/")
add("i21_lambda_wrong_domain", "def f: Nat -> Nat = x => x && true\n",
    "body type error under check mode points into the body", "error /error/")
add("i22_check_nested", "def f: Nat -> Nat -> Nat = x => y => x + y\nprintln(f(1)(2))\n",
    "curried lambda check", "stdout /3/")
add("i23_insert_implicit_lam", "def idq: [A: Type 0] -> A -> A = x => x\nprintln(idq[Nat](4))\n",
    "elaborator inserts implicit lambda around explicit-only body", "stdout /4/")

# ---- metas & errors --------------------------------------------------------------
add("i24_meta_no_solution", "def f[A: Type 0](x: A): A = x\ndef g: Nat = f(3) && true\n",
    "solved meta reused in wrong position fails", "error /error/")
add("i25_occurs_check", "def f(x: Nat): Nat = x\n",
    "sanity: plain def before occurs probes", "ok")
add("i26_unsolved_prints_meta", "def f[A: Type 0](x: A): A = x\ndef h: Boolean = f(true)\nprintln(h)\n",
    "implicit solves through a def alias chain", "stdout /true/")
add("i27_implicit_typeclass_style", "trait MyShow[T] { def show(t: T): String }\nimpl MyShow[Nat] { def show(t: Nat) = \"nat\" }\nprintln(MyShow.show(3))\n",
    "Trait.method(x) static form is NOT supported (use x.method())", "error /error/")
add("i28_implicit_enum_param", "enum Wrap[A: Type 0] { wrap(v: A) -> Wrap[A] }\ndef unwrap[A: Type 0](w: Wrap[A]): A = match w { case wrap(v) => v }\nprintln(unwrap(wrap(11)))\n",
    "GADT-style enum implicit parameter solved by constructor", "stdout /11/")
add("i29_implicit_shadow", "def f[A: Type 0](A: Nat): Nat = A\nprintln(f[Nat](8))\n",
    "term binder shadowing an implicit type name", "stdout /8/")
add("i30_implicit_unused", "def f[A: Type 0](x: Nat): Nat = x\nprintln(f(6))\n",
    "unused implicit stays unsolved but does not block a Nat result", "stdout /6/")

# ---- elaboration order / bidirectionality ------------------------------------------
add("i31_infer_lambda_no_ann", "def f = x => x\nprintln(f(1))\n",
    "bare lambda: lazy domain meta, monomorphic after first use (quirk)", "stdout /1/", expect_not="error:")
add("i32_ann_drives_match", "def f: Nat -> Nat = n => match n {\n  case zero => 1\n  case succ(m) => f(m)\n}\nprintln(f(3))\n",
    "annotation drives recursive function elaboration", "stdout /1/")
add("i33_tuple_ann", "struct Pair {\n  fst: Nat\n  snd: Nat\n}\ndef p: Pair = Pair.mk(1, 2)\nprintln(p.fst + p.snd)\n",
    "struct literal checked against annotation", "stdout /3/")
add("i34_ann_wrong_arity", "def f: Nat -> Nat -> Nat = x => x\n",
    "arity mismatch between annotation and lambda", "error /error/")
add("i35_poly_id_id", "def idd[A: Type 0](x: A): A = x\nprintln(idd[Nat -> Nat](idd[Nat])(4))\n",
    "higher-kinded implicit: A := Nat -> Nat", "stdout /4/")
add("i36_implicit_nat_index", "enum MyFin(n: Nat) {\n  fz[m: Nat] -> MyFin(m + 1)\n  fs[m: Nat](i: MyFin(m)) -> MyFin(m + 1)\n}\ndef val(i: MyFin(2)): Nat = match i {\n  case fz => 0\n  case fs(j) => 1\n}\nprintln(val(fz))\n",
    "indexed constructor elaborates with implicit index metas", "stdout /0/")
add("i37_expected_hole_type", "def f: Nat -> _ = n => n\nprintln(f(2))\n",
    "hole in codomain solved from the body (bidirectional)", "stdout /2/")
add("i38_deep_implicit_nesting", "def a[A: Type 0](x: A): A = x\ndef b[B: Type 0](y: B): B = a(y)\ndef c[C: Type 0](z: C): C = b(z)\nprintln(c(12))\n",
    "three-level implicit alias chain", "stdout /12/")
add("i39_implicit_bool_dual", "def pick[A: Type 0](c: Boolean)(t: A, f: A): A = match c {\n  case true => t\n  case false => f\n}\nprintln(pick(true, 1, 2))\n",
    "implicit solved from two positions consistently", "stdout /1/")
add("i40_named_arg_explicit_probe", "def sub(x: Nat, y: Nat): Nat = x - y\nprintln(sub(y = 1, x = 5))\n",
    "named EXPLICIT args (probe: supported?)", "error /error/")
add("i41_implicit_from_annotation_only", "def empty[A: Type 0]: List0[A] = _\n",
    "type-only implicit with no explicit args (probe)", "error /unsolved|error/")
add("i42_hole_in_implicit_arg", "def idd[A: Type 0](x: A): A = x\nprintln(idd[_](3))\n",
    "hole passed as an explicit implicit: solved from the next arg", "stdout /3/")
add("i43_implicit_mixed_icit", "def f[A: Type 0](x: A)[B: Type 0](y: B): A = x\nprintln(f(1)[Boolean](true))\n",
    "interleaved explicit/implicit parameter groups", "stdout /1/")

hdr = "// probe: {p}\n// expect: {e}\n"
add("i44_type0_hole_defaulting_warns", "def t: Type 0 = _\nprintln(3)\n",
    "Type-0 hole silently defaulting to Nat now surfaces TY001", "warn /TY001/")

hdr = "// probe: {p}\n// expect: {e}\n"
for fid, (src, probe, expect, expect_not) in P.items():
    text = hdr.format(p=probe, e=expect)
    if expect_not:
        text += f"// expect-not: {expect_not}\n"
    (D / f"{fid}.typort").write_text(text + src, encoding="utf-8")

print(f"wrote {len(P)} probes to {D}")
