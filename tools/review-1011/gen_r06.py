#!/usr/bin/env python3
"""Generate round-6 (macros / canonical forms) probes.

Canonical macro forms (tests/l11_fast_parity.rs + prelude hdl-macros.typort):
fragments: $x:ident, $x:raw, $x:param, $x:name; invocation by bare name;
declaration-level macros expand to decls; `stringify` builtin.
"""
from pathlib import Path

D = Path(__file__).resolve().parent / "r06-macros"
D.mkdir(exist_ok=True)
for f in D.glob("*.typort"):
    f.unlink()

P = {}

def add(fid, src, probe, expect, expect_not=None):
    P[fid] = (src, probe, expect, expect_not)

# ---- basic expansion --------------------------------------------------------
add("x01_decl_macro", "macro_rules make_bool {\n  (yes) => {\n    enum Yes { y }\n  };\n}\nmake_bool yes\n\ndef b = y\nprintln(b)\n",
    "declaration-level macro expands to an enum", "stdout /y/")
add("x02_ident_fragment", "macro_rules mk {\n  ($n:ident) => {\n    def $n: Nat = 7\n  };\n}\nmk seven\nprintln(seven)\n",
    "$n:ident substitution in def name", "stdout /7/")
add("x03_raw_fragment", "macro_rules twice {\n  ($e:raw) => {\n    def r2: Nat = $e + $e\n  };\n}\ntwice (3)\nprintln(r2)\n",
    "$e:raw substitution in expression", "stdout /6/")
add("x04_stringify", "println(stringify hello123)\n",
    "stringify builtin on an identifier", "stdout /hello123/")
add("x05_no_match_macro", "macro_rules one {\n  (a) => { def only_a: Nat = 1 }\n}\none b\n",
    "invocation not matching any rule errors", "error /error/")
add("x06_multi_rule", "macro_rules pick {\n  (a) => { def picked: Nat = 1 };\n  (b) => { def picked: Nat = 2 };\n}\npick b\nprintln(picked)\n",
    "second rule matches", "stdout /2/")
add("x07_first_match_wins", "macro_rules fm {\n  ($x:ident) => { def fm_r: Nat = 1 };\n  (zz) => { def fm_r: Nat = 2 };\n}\nfm zz\nprintln(fm_r)\n",
    "generic rule shadows the literal rule (first match wins)", "stdout /1/")
add("x08_param_fragment", "macro_rules fnum {\n  ($p:param) => {\n    def fnm: Nat -> Nat = $p\n  };\n}\nfnum (n => n + 1)\ndef v8: Nat -> Nat = fnm\nprintln(v8(2))\n",
    "$p:param matches a binder LIST (x: A), not a lambda expr (recorded)", "error /error/")
add("x09_macro_recursion_depth", "macro_rules chain {\n  ($n:ident) => { def $n: Nat = 5 }\n}\nchain a1\nprintln(a1)\n",
    "single-level expansion sanity", "stdout /5/")
add("x10_macro_name_collision", "macro_rules mydup {\n  (a) => { def dupd: Nat = 1 }\n}\nmydup a\nmacro_rules mydup {\n  (a) => { def dupd: Nat = 2 }\n}\nmydup a\nprintln(dupd)\n",
    "macro name redefinition (probe: shadow or error)", "error /error/")

# ---- token hygiene / splicing ------------------------------------------------
add("x11_splice_in_type", "macro_rules ty {\n  ($n:ident) => {\n    def tv: Nat = 3\n  }\n}\nty Nat9\nprintln(tv)\n",
    "macro in type position via def name", "stdout /3/")
add("x12_expr_macro", "macro_rules five {\n  () => { 5 }\n}\ndef f5: Nat = five\nprintln(f5)\n",
    "expression-position macro WORKS (bare () => { 5 } body)", "stdout /5/")
add("x13_nested_macro_call", "macro_rules inner {\n  ($n:ident) => { def $n: Nat = 9 };\n}\nmacro_rules outer {\n  ($m:ident) => { inner $m };\n}\nouter inner_res\nprintln(inner_res)\n",
    "macro expanding to another macro invocation", "stdout /9/")
add("x14_macro_defines_macro", "macro_rules outer2 {\n  () => { macro_rules inner2 { (a) => { def i2: Nat = 4 } } }\n}\nouter2\ninner2 a\nprintln(i2)\n",
    "macro defining a macro (probe)", "error /error/")
add("x15_hygiene_shadow", "macro_rules hy {\n  ($n:ident) => { def $n: Nat = 1 };\n}\ndef shadow_test: Nat =\n  let hy: Nat = 99;\n  hy\nprintln(shadow_test)\n",
    "macro name as let binder does not trigger expansion", "stdout /99/")

# ---- stringify / debug ----------------------------------------------------------
add("x16_stringify_expr", "println(stringify xy_z)\n",
    "stringify on an underscore ident", "stdout /xy_z/")
add("x17_stringify_in_macro", "macro_rules nm {\n  ($n:ident) => { println(stringify $n) };\n}\nnm foo\n",
    "stringify inside macro transcriber", "stdout /foo/")

# ---- errors ---------------------------------------------------------------------
add("x18_macro_no_name", "macro_rules {\n  (a) => { def q: Nat = 1 }\n}\n",
    "macro_rules without a name errors", "error /error/")
add("x19_unknown_fragment", "macro_rules uf {\n  ($x:bogus) => { def uf_r: Nat = 1 }\n}\n",
    "unknown fragment kind is silently accepted, rule never matches (quirk)", "ok")
add("x20_unclosed_rules", "macro_rules uc {\n  (a) => { def uc_r: Nat = 1 }\n",
    "unclosed macro_rules braces error", "error /error/")
add("x21_unfinished_transcriber", "macro_rules ut {\n  (a) => { def ut_r: Nat = 1 }\n  (b) => {\n}\ndef zz2: Nat = 0\nprintln(zz2)\n",
    "empty transcriber arm is a parse error", "error /error/")

# ---- interaction with layout / existing macros -----------------------------------
add("x22_calc_still_works", "def r: Eq(nat_add(1, 1), 2) =\n  calc {\n    nat_add(1, 1) = 2 by rfl\n  }\nprintln(r)\n",
    "prelude calc macro on a trivial chain", "ok")
add("x23_macro_before_use_order", "println(later)\nmacro_rules later_m {\n  (a) => { def later: Nat = 8 }\n}\nlater_m a\n",
    "macro use before its definition line (probe: top-to-bottom)", "error /error/")
add("x24_macro_exports", "macro_rules pubm {\n  (a) => { def pubmed: Nat = 3 }\n}\npubm a\nprintln(pubmed)\n",
    "same-file macro defined+used", "stdout /3/")
add("x25_macro_arg_spacing", "macro_rules sp {\n  ($n:ident) => { def $n: Nat = 6 };\n}\nsp   spaced\nprintln(spaced)\n",
    "extra spaces between macro name and argument", "stdout /6/")
add("x26_two_arg_macro", "macro_rules pair2 {\n  ($a:ident, $b:ident) => { def $a: Nat = 1; def $b: Nat = 2 };\n}\npair2 (p1, p2)\nprintln(p1)\nprintln(p2)\n",
    "two-arg matcher (a, b) needs the SAME call shape; paren call fails (quirk)", "error /error/")
add("x27_macro_in_match_body", "macro_rules mcase {\n  ($n:ident) => { def $n: Nat = 11 };\n}\nmcase mc\nprintln(mc)\n",
    "control: macro at top level still fine after layout checks", "stdout /11/")
add("x28_stringify_num", "println(stringify 42)\n",
    "stringify needs an identifier; numbers error", "error /error/")
add("x29_macro_shadow_prelude", "macro_rules nat_add {\n  (a) => { def nat_add: Nat = 50 };\n}\nnat_add a\nprintln(nat_add)\n",
    "macro shadowing a prelude function name (probe)", "error /error/")
add("x30_empty_rule_list", "macro_rules er {\n}\n",
    "macro with no rules (probe)", "error /error/")
add("x31_ident_used_twice", "macro_rules two_use {\n  ($n:ident) => { def $n: Nat = 1; def $n: Nat = 2 };\n}\ntwo_use tu\n",
    "$n used twice creates duplicate defs (probe)", "error /error/")
add("x32_raw_multiline", "macro_rules ml {\n  ($e:raw) => { def mlr: Nat = $e };\n}\nml (nat_add(2,\n  3))\nprintln(mlr)\n",
    "raw fragment spanning lines", "stdout /5/")
add("x33_macro_keeps_layout", "macro_rules lay {\n  ($n:ident) => { def $n: Nat = match 1 {\n  case zero => 0\n  case succ(m) => m\n} };\n}\nlay lr\nprintln(lr)\n",
    "macro-expanded match: succ(zero) binds m=zero, prints 0", "stdout /0/")
add("x34_recursive_macro_expansion_limit", "macro_rules rl {\n  (a) => { rl a }\n}\nrl a\n",
    "self-referential macro hits the depth limit (256) immediately", "error /too deep/")
add("x35_macro_named_stringify2", "macro_rules sfn {\n  ($n:ident) => { def $n: Nat = 2 };\n}\nsfn strfn\nprintln(strfn)\n",
    "identifier close to builtin names", "stdout /2/")

hdr = "// probe: {p}\n// expect: {e}\n"
for fid, (src, probe, expect, expect_not) in P.items():
    text = hdr.format(p=probe, e=expect)
    if expect_not:
        text += f"// expect-not: {expect_not}\n"
    (D / f"{fid}.typort").write_text(text + src, encoding="utf-8")

print(f"wrote {len(P)} probes to {D}")
