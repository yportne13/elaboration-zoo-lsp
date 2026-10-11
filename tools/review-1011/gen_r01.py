#!/usr/bin/env python3
"""Generate round-1 (parser & surface syntax) probe corpus."""
from pathlib import Path

D = Path(__file__).resolve().parent / "r01-parser"
D.mkdir(exist_ok=True)
for f in D.glob("*.typort"):
    f.unlink()

P = {}  # id -> (bytes_or_str, probe, expect)

def add(fid, src, probe, expect, expect_not=None, binary=False):
    P[fid] = (src, probe, expect, expect_not, binary)

# ---- comments ---------------------------------------------------------
add("e01_comment_eof_no_newline", "// just a comment, no trailing newline",
    "single-line comment at EOF without newline", "ok")
add("e02_nested_block_comment", "/* outer /* inner */ still outer */ def x: Nat = 1\nprintln(x)\n",
    "nested block comments (are they nesting?)", "ok")
add("e03_unterminated_block_comment", "/* never closed\ndef x: Nat = 1\n",
    "unterminated block comment", "error /unterminated|expected|error/")
add("e04_unbalanced_close_comment", "/* ok */ */ extra\ndef x: Nat = 1\n",
    "stray closing comment delimiter", "error /error/")
add("e39_comment_between_args", "def r: Nat = succ( // c\n  zero)\nprintln(r)\n",
    "line comment inside call args", "ok")

# ---- unicode ------------------------------------------------------------
add("e05_unicode_ident_cjk", "def \u53d8\u91cf: Nat = 1\nprintln(\u53d8\u91cf)\n",
    "CJK identifier accepted and printable", "ok")
add("e06_nbsp_between_tokens", "def\u00a0x: Nat = 1\n",
    "NBSP between tokens should be rejected (not silently accepted)", "error /error/")
add("e07_zero_width_in_ident", "def a\u200bb: Nat = 1\n",
    "zero-width space inside identifier should error", "error /error/")
add("e08_bom_at_start", "\ufeffdef x: Nat = 1\nprintln(x)\n",
    "UTF-8 BOM at file start is tolerated", "ok")
add("e09_crlf_endings", "def x: Nat = 1\r\nprintln(x)\r\n",
    "CRLF line endings", "ok")
add("e10_tab_indent", "def f(x: Nat): Nat =\n\tx + 1\nprintln(f(1))\n",
    "tab indentation", "ok")

# ---- numbers & universes -------------------------------------------------
add("e11_num_formats", "println(0)\nprintln(007)\nprintln(99999)\n",
    "leading-zero and large decimal literals", "stdout /7/")
add("e12_universe_max", "def U: Type 4294967295 = Type 4294967294\n",
    "universe level u32::MAX rejected (max usable is MAX-1)", "error /too large/")
add("e13_universe_overflow", "def U: Type 4294967296 = Type 0\n",
    "universe level beyond u32 must be a parser error (F2 pin)", "error /error/")
add("e14_big_nat_literal", "def big: Nat = 1000000000000000000000\nprintln(big)\n",
    "huge Nat literal: >u64 rejected with cascade noise (quirk)", "error /does not fit/")
add("e15_negative_literal", "def x: Nat = -1\n",
    "negative literal is not a Nat", "error /error/")
add("e16_leading_plus", "def x: Nat = +1\n",
    "leading + on literal", "error /error/")

# ---- strings ---------------------------------------------------------------
add("e17_string_escapes", 'def s: String = "a\\nb\\"c"\nprintln(s)\n',
    "string escape sequences parse", "ok")
add("e18_string_unterminated", 'def s: String = "abc\n',
    "unterminated string literal", "error /error/")
add("e19_string_comment", 'def s: String = "// not a comment"\nprintln(s)\n',
    "// inside string is not a comment", "ok")

# ---- nesting depth / size robustness ---------------------------------------
add("e20_deep_parens_200", "def x: Nat = " + "(" * 200 + "1" + ")" * 200 + "\nprintln(x)\n",
    "200 nested parens", "ok")
add("e21_deep_parens_3000", "def x: Nat = " + "(" * 3000 + "1" + ")" * 3000 + "\nprintln(x)\n",
    "3000 nested parens must not crash (depth guard or iteration)", "ok", expect_not="panicked")
add("e22_long_ident", "def " + "a" * 8000 + ": Nat = 1\n",
    "8000-char identifier", "ok")
add("e23_many_decls", "".join(f"def d{i}: Nat = {i}\n" for i in range(300)) + "println(d299)\n",
    "300 top-level defs", "ok")
add("e24_empty_file", "", "completely empty file", "ok")
add("e25_only_comments", "// nothing here\n/* really nothing */\n", "only comments", "ok")

# ---- recovery / shape errors ------------------------------------------------
add("e26_def_missing_body", "def broken: Nat = \n",
    "def with missing body errors gracefully", "error /error/")
add("e27_unbalanced_brace_enum", "enum X {\n  a\n",
    "unclosed enum brace: error, no panic", "error /error/")
add("e28_extra_close_brace", "def x: Nat = 1\n}\n",
    "stray closing brace at top level", "error /error/")
add("e29_semicolon_after_def", "def x: Nat = 1;\nprintln(x)\n",
    "semicolon after decl (probe: accepted or error?)", "error /error/")

# ---- separator conventions ---------------------------------------------------
add("e30_trailing_comma_call", "def r: Nat = succ(zero,)\nprintln(r)\n",
    "trailing comma in call args is accepted", "ok")
add("e31_trailing_comma_params", "def f(x: Nat,): Nat = x\nprintln(f(1))\n",
    "trailing comma in parameter list is accepted", "ok")
add("e32_mixed_sep_args", "def add2(x: Nat, y: Nat): Nat = x + y\nprintln(add2(1 2))\n",
    "space-separated args inside call parens", "error /error/")

# ---- expression syntax ---------------------------------------------------------
add("e33_precedence_mul_add", "println(1 + 2 * 3)\n",
    "* binds tighter than +: prints 7", "stdout /7/")
add("e34_tight_arrow", "def f: Nat->Nat = x => x\nprintln(f(1))\n",
    "no-space -> arrow in type", "ok")
add("e35_lambda_two_args", "def g: Nat -> Nat -> Nat = (x, y) => x\nprintln(g(1)(2))\n",
    "(x, y) => ... multi-arg lambda is NOT supported (curry instead)", "error /error/")
add("e36_keyword_as_ident", "def enum: Nat = 1\n",
    "keyword as identifier rejected", "error /error/")
add("e37_duplicate_def", "def x: Nat = 1\ndef x: Nat = 2\n",
    "duplicate definition is an error or warning", "error /error|warn/")
add("e38_hole_expr", "def x: Nat = _\n",
    "hole expression -> unsolved meta error", "error /unsolved/")
add("e40_derive_show", "#[derive(Show)]\nenum Color { red green }\nprintln(Color.red)\n",
    "#[derive(Show)] enum; one-line multi-ctor braces need newlines (layout)", "error /error/")
add("e41_let_in_def", "def x: Nat =\n  let y: Nat = 2;\n  y * y\nprintln(x)\n",
    "let-binding with semicolon inside def", "stdout /4/")
add("e42_named_implicit_call", "def f[A: Type 0](x: A): A = x\nprintln(f[Nat](1))\n",
    "explicit implicit application f[Nat]", "stdout /1/")
add("e43_match_spacing", "def n: Nat = 2\ndef r: String = match n {\n  case zero => \"z\"\n  case succ(m) => \"s\"\n}\nprintln(r)\n",
    "match arms parse with varied spacing", "stdout /s/")

hdr = "// probe: {p}\n// expect: {e}\n"
for fid, (src, probe, expect, expect_not, binary) in P.items():
    text = hdr.format(p=probe, e=expect)
    if expect_not:
        text += f"// expect-not: {expect_not}\n"
    text += ("// mode: check\n" if False else "")
    payload = text + src
    data = payload.encode("utf-8")
    (D / f"{fid}.typort").write_bytes(data)

print(f"wrote {len(P)} probes to {D}")
