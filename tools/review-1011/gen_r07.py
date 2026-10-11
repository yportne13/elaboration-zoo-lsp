#!/usr/bin/env python3
"""Generate round-7 (namespaces / packages / imports) probes."""
from pathlib import Path

D = Path(__file__).resolve().parent / "r07-namespace"
D.mkdir(exist_ok=True)
for f in D.glob("*.typort"):
    f.unlink()

P = {}

def add(fid, src, probe, expect, expect_not=None):
    P[fid] = (src, probe, expect, expect_not)

PKG = (
    "package mylib.math\n"
    "def sq(x: Nat): Nat = x * x\n"
    "def half(x: Nat): Nat = nat_div(x, 2)\n"
    "package other\n"
    "def other_fn(x: Nat): Nat = x + 100\n"
)

# ---- package basics ---------------------------------------------------------
add("n01_qualified_call", PKG + "println(mylib.math.sq(4))\n",
    "package-prefixed def called with full path", "stdout /16/")
add("n02_package_switch", PKG + "println(other.other_fn(1))\n",
    "second package block switches the prefix", "stdout /101/")
add("n03_import_single", PKG + "import mylib.math.sq\nprintln(sq(5))\n",
    "single-name import brings the bare name", "stdout /25/")
add("n04_import_braces", PKG + "import mylib.math.{ sq, half }\nprintln(sq(6) + half(8))\n",
    "braced selective import", "stdout /40/")
add("n05_import_wildcard", PKG + "import mylib.math._\nprintln(sq(7) + half(9))\n",
    "wildcard import", "stdout /53/")
add("n06_import_type_not_brought", PKG + "import mylib.math.sq\nprintln(mylib.math.half(10))\n",
    "import sq only; other members still reachable qualified", "stdout /5/")
add("n07_import_no_prefix_leak", PKG + "import mylib.math.{ sq }\nprintln(sq(2))\n",
    "braced import does NOT bring the mylib prefix itself (S3)", "stdout /4/")

# ---- shadowing / precedence ---------------------------------------------------
add("n08_shadow_prelude", "package mm\ndef nat_add(x: Nat, y: Nat): Nat = x * 10 + y\nimport mm.nat_add\nprintln(nat_add(1, 2))\n",
    "D1 confirmed: prelude bare alias wins over imported user def", "stdout /3/")
add("n09_local_beats_import", PKG + "import mylib.math.sq\ndef sq(x: Nat): Nat = x + 1000\nprintln(sq(1))\n",
    "QUIRK: import alias beats same-file decl defined after it", "stdout /1/")
add("n10_qualified_beats_local", PKG + "import mylib.math.sq\ndef sq(x: Nat): Nat = x + 1000\nprintln(mylib.math.sq(1))\n",
    "qualified access ignores the local shadow", "stdout /1/")

# ---- nested namespaces ----------------------------------------------------------
add("n11_deep_package", "package a.b.c.d\ndef deep_fn(x: Nat): Nat = x + 1\nprintln(a.b.c.d.deep_fn(9))\n",
    "four-level package path", "stdout /10/")
add("n12_import_middle_segment", PKG + "import mylib.math\nprintln(math.sq(3))\n",
    "import middle segment NOT supported (D2: last seg is a member)", "error /error/")
add("n13_import_wildcard_scope", PKG + "import mylib.math._\ndef sq(x: Nat): Nat = x\nprintln(sq(5))\nprintln(mylib.math.sq(5))\n",
    "wildcard import then local def of same name", "stdout /5/")

# ---- cross-file (simulated via package in same file) -----------------------------
add("n14_two_packages_same_file", PKG + "println(mylib.math.sq(2) + other.other_fn(2))\n",
    "both packages usable in one file", "stdout /106/")
add("n15_package_empty", "package lonely\nprintln(0)\n",
    "package decl with no members still parses", "stdout /0/")
add("n16_package_dotted_call_chain", PKG + "def h(x: Nat): Nat = mylib.math.half(x) + mylib.math.half(x)\nprintln(h(8))\n",
    "qualified calls inside another package's def", "stdout /8/")

# ---- type / constructor namespaces --------------------------------------------------
add("n17_enum_in_package", "package shapes\nenum Color2 {\n  red2\n  blue2\n}\ndef pick(c: Color2): Nat = match c {\n  case red2 => 1\n  case blue2 => 2\n}\nprintln(shapes.Color2.red2)\n",
    "enum ctor via package prints qualified", "stdout /red2/")
add("n18_struct_in_package", "package boxes\nstruct W2 {\n  v: Nat\n}\ndef mk(x: Nat): W2 = W2.mk(x)\nprintln(boxes.mk(7).v)\n",
    "struct + factory in a package", "stdout /7/")
add("n19_import_enum_ctor", "package shapes2\nenum Fruit2 {\n  apple2\n}\nimport shapes2.Fruit2._\nprintln(apple2)\n",
    "import Type._ brings constructors (S1/S3 semantics)", "stdout /apple2/")
add("n20_import_enum_type_itself", "package shapes3\nenum Fruit3 {\n  apple3\n}\nimport shapes3.Fruit3\ndef f(x: Fruit3): Nat = 1\nprintln(f(apple3))\n",
    "import the type; ctor via prelude-like bare alias (probe)", "stdout /1/")

# ---- resolution edge cases -----------------------------------------------------------
add("n21_undefined_ns", "println(nosuch.fn(1))\n",
    "unknown namespace prefix errors", "error /error/")
add("n22_undefined_member", PKG + "println(mylib.math.nope(1))\n",
    "unknown member in known namespace errors", "error /error/")
add("n23_import_missing", PKG + "import mylib.math.missing_fn\nprintln(0)\n",
    "import of a missing member (probe: error or lazy)", "error /error/")
add("n24_suffix_fallback", "package ff\nstruct TT {\n  n: Nat\n}\nimpl TT {\n  def mux(k: Nat): Nat = k\n}\ndef tt: TT = TT.mk(4)\nprintln(tt.mux(9))\n",
    "suffix fallback only for known decl-key heads (works here)", "stdout /9/")
add("n25_suffix_fallback_denied", "def plain(x: Nat): Nat = x\nprintln(plain.mux(1))\n",
    "suffix fallback denied on a plain function value", "error /error/")
add("n26_ns_method_on_result", PKG + "impl Nat {\n  def double2: Nat = this + this\n}\ndef six: Nat = 6\nprintln(six.double2)\n",
    "inherent impl method in a package still resolves", "stdout /12/")
add("n27_import_conflict", PKG + "package p2\ndef dup(x: Nat): Nat = x + 1\nimport mylib.math.sq\nimport p2.dup\nprintln(sq(1) + dup(1))\n",
    "two imports of different names coexist", "stdout /3/")
add("n28_package_then_use_before", PKG + "println(sq(3))\n",
    "same-package members NOT auto-visible; must qualify (quirk)", "error /error/")
add("n29_nested_ns_hover_shape", "package n29\nenum E9 {\n  c9\n}\ndef g(x: E9): Nat = 1\nprintln(n29.g(n29.E9.c9))\n",
    "fully-qualified type and ctor paths compose", "stdout /1/")
add("n30_wildcard_prelude_clash", PKG + "def zero(x: Nat): Nat = x\nimport mylib.math._\nprintln(zero(3))\nprintln(nat_add(1, 1))\n",
    "user zero shadows prelude ctor ambiguously (probe: unify error)", "error /error/")

hdr = "// probe: {p}\n// expect: {e}\n"
for fid, (src, probe, expect, expect_not) in P.items():
    text = hdr.format(p=probe, e=expect)
    if expect_not:
        text += f"// expect-not: {expect_not}\n"
    (D / f"{fid}.typort").write_text(text + src, encoding="utf-8")

print(f"wrote {len(P)} probes to {D}")
