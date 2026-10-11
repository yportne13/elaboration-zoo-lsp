# r06-macros — 实验结果

- probes: 35  PASS: 33  FAIL: 2  TIMEOUT: 0  NOEXPECT: 0

| id | verdict | time | probe | note |
|---|---|---|---|---|
| x01_decl_macro | PASS | 6.83s | declaration-level macro expands to an enum |  |
| x02_ident_fragment | PASS | 6.47s | $n:ident substitution in def name |  |
| x03_raw_fragment | PASS | 6.86s | $e:raw substitution in expression |  |
| x04_stringify | PASS | 6.70s | stringify builtin on an identifier |  |
| x05_no_match_macro | PASS | 7.14s | invocation not matching any rule errors |  |
| x06_multi_rule | PASS | 7.31s | second rule matches |  |
| x07_first_match_wins | PASS | 7.06s | generic rule shadows the literal rule (first match wins) |  |
| x08_param_fragment | FAIL | 6.61s | $p:param fragment | expected program output but errors present |
| x09_macro_recursion_depth | PASS | 6.73s | single-level expansion sanity |  |
| x10_macro_name_collision | PASS | 6.73s | macro name redefinition (probe: shadow or error) |  |
| x11_splice_in_type | PASS | 6.64s | macro in type position via def name |  |
| x12_expr_macro | PASS | 6.08s | expression-position macro WORKS (bare () => { 5 } body) |  |
| x13_nested_macro_call | PASS | 12.84s | macro expanding to another macro invocation |  |
| x14_macro_defines_macro | PASS | 14.58s | macro defining a macro (probe) |  |
| x15_hygiene_shadow | PASS | 10.48s | macro name as let binder does not trigger expansion |  |
| x16_stringify_expr | PASS | 7.94s | stringify on an underscore ident |  |
| x17_stringify_in_macro | PASS | 12.84s | stringify inside macro transcriber |  |
| x18_macro_no_name | PASS | 13.89s | macro_rules without a name errors |  |
| x19_unknown_fragment | PASS | 15.53s | unknown fragment kind is silently accepted, rule never matches (quirk) |  |
| x20_unclosed_rules | PASS | 12.52s | unclosed macro_rules braces error |  |
| x21_unfinished_transcriber | PASS | 6.73s | empty transcriber arm is a parse error |  |
| x22_calc_still_works | PASS | 6.39s | prelude calc macro on a trivial chain |  |
| x23_macro_before_use_order | PASS | 6.30s | macro use before its definition line (probe: top-to-bottom) |  |
| x24_macro_exports | PASS | 6.34s | same-file macro defined+used |  |
| x25_macro_arg_spacing | PASS | 6.34s | extra spaces between macro name and argument |  |
| x26_two_arg_macro | FAIL | 6.33s | two-parameter macro with ; inside transcriber | expected program output but errors present |
| x27_macro_in_match_body | PASS | 6.27s | control: macro at top level still fine after layout checks |  |
| x28_stringify_num | PASS | 7.83s | stringify needs an identifier; numbers error |  |
| x29_macro_shadow_prelude | PASS | 11.97s | macro shadowing a prelude function name (probe) |  |
| x30_empty_rule_list | PASS | 13.36s | macro with no rules (probe) |  |
| x31_ident_used_twice | PASS | 11.67s | $n used twice creates duplicate defs (probe) |  |
| x32_raw_multiline | PASS | 7.89s | raw fragment spanning lines |  |
| x33_macro_keeps_layout | PASS | 7.91s | macro-expanded match: succ(zero) binds m=zero, prints 0 |  |
| x34_recursive_macro_expansion_limit | PASS | 7.97s | self-referential macro hits the depth limit (256) immediately |  |
| x35_macro_named_stringify2 | PASS | 6.97s | identifier close to builtin names |  |

## 非 PASS 详情

### x08_param_fragment — FAIL
`expected program output but errors present`

```text
--- stdout ---

--- stderr ---
Analyzing: file:///F:/projects/hermes/elaboration-zoo-lsp/tools/review-1011/r06-macros/x08_param_fragment.typort (191 bytes)
[LOG log] change: file:///F:/projects/hermes/elaboration-zoo-lsp/tools/review-1011/r06-macros/x08_param_fragment.typort
[LOG log] parser 0.0004278
[LOG log] infer 0.0007268
error: error name not in scope: fnm
  ┌─ /F:/projects/hermes/elaboration-zoo-lsp/tools/review-1011/r06-macros/x08_param_fragment.typort:9:22
  │
9 │ def v8: Nat -> Nat = fnm
  │                      ^^^

error: error name not in scope: v8 (declaration failed to elaborate above)
   ┌─ /F:/projects/hermes/elaboration-zoo-lsp/tools/review-1011/r06-macros/x08_param_fragment.typort:10:9
   │
10 │ println(v8(2))
   │         ^^

error: expected `)`
  ┌─ /F:/projects/hermes/elaboration-zoo-lsp/tools/review-1011/r06-macros/x08_param_fragment.typort:4:4
  │
4 │   ($p:param) => {
  │    ^^

error: expected newline
  ┌─ /F:/projects/hermes/elaboration-zoo-lsp/tools/review-1011/r06-macros/x08_param_fragment.typort:8:6
  │
8 │ fnum (n => n + 1)
  │      ^

[LOG log] change 0.0025943
```

### x26_two_arg_macro — FAIL
`expected program output but errors present`

```text
--- stdout ---

--- stderr ---
Analyzing: file:///F:/projects/hermes/elaboration-zoo-lsp/tools/review-1011/r06-macros/x26_two_arg_macro.typort (211 bytes)
[LOG log] change: file:///F:/projects/hermes/elaboration-zoo-lsp/tools/review-1011/r06-macros/x26_two_arg_macro.typort
[LOG log] parser 0.0003028
[LOG log] infer 0.0002629
error: error name not in scope: p1
  ┌─ /F:/projects/hermes/elaboration-zoo-lsp/tools/review-1011/r06-macros/x26_two_arg_macro.typort:7:9
  │
7 │ println(p1)
  │         ^^

error: error name not in scope: p2
  ┌─ /F:/projects/hermes/elaboration-zoo-lsp/tools/review-1011/r06-macros/x26_two_arg_macro.typort:8:9
  │
8 │ println(p2)
  │         ^^

error: expected identifier
  ┌─ /F:/projects/hermes/elaboration-zoo-lsp/tools/review-1011/r06-macros/x26_two_arg_macro.typort:6:7
  │
6 │ pair2 (p1, p2)
  │       ^

error: expected newline
  ┌─ /F:/projects/hermes/elaboration-zoo-lsp/tools/review-1011/r06-macros/x26_two_arg_macro.typort:6:7
  │
6 │ pair2 (p1, p2)
  │       ^

[LOG log] change 0.0020651
```
