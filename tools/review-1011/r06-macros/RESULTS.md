# r06-macros — 实验结果

- probes: 35  PASS: 35  FAIL: 0  TIMEOUT: 0  NOEXPECT: 0

| id | verdict | time | probe | note |
|---|---|---|---|---|
| x01_decl_macro | PASS | 5.64s | declaration-level macro expands to an enum |  |
| x02_ident_fragment | PASS | 5.61s | $n:ident substitution in def name |  |
| x03_raw_fragment | PASS | 5.72s | $e:raw substitution in expression |  |
| x04_stringify | PASS | 5.23s | stringify builtin on an identifier |  |
| x05_no_match_macro | PASS | 5.58s | invocation not matching any rule errors |  |
| x06_multi_rule | PASS | 5.47s | second rule matches |  |
| x07_first_match_wins | PASS | 5.25s | generic rule shadows the literal rule (first match wins) |  |
| x08_param_fragment | PASS | 5.70s | $p:param matches a binder LIST (x: A), not a lambda expr (recorded) |  |
| x09_macro_recursion_depth | PASS | 5.73s | single-level expansion sanity |  |
| x10_macro_name_collision | PASS | 5.70s | macro name redefinition (probe: shadow or error) |  |
| x11_splice_in_type | PASS | 5.69s | macro in type position via def name |  |
| x12_expr_macro | PASS | 5.67s | expression-position macro WORKS (bare () => { 5 } body) |  |
| x13_nested_macro_call | PASS | 5.70s | macro expanding to another macro invocation |  |
| x14_macro_defines_macro | PASS | 5.72s | macro defining a macro (probe) |  |
| x15_hygiene_shadow | PASS | 5.64s | macro name as let binder does not trigger expansion |  |
| x16_stringify_expr | PASS | 5.64s | stringify on an underscore ident |  |
| x17_stringify_in_macro | PASS | 5.92s | stringify inside macro transcriber |  |
| x18_macro_no_name | PASS | 5.66s | macro_rules without a name errors |  |
| x19_unknown_fragment | PASS | 5.61s | unknown fragment kind is silently accepted, rule never matches (quirk) |  |
| x20_unclosed_rules | PASS | 5.61s | unclosed macro_rules braces error |  |
| x21_unfinished_transcriber | PASS | 5.67s | empty transcriber arm is a parse error |  |
| x22_calc_still_works | PASS | 5.67s | prelude calc macro on a trivial chain |  |
| x23_macro_before_use_order | PASS | 5.62s | macro use before its definition line (probe: top-to-bottom) |  |
| x24_macro_exports | PASS | 5.67s | same-file macro defined+used |  |
| x25_macro_arg_spacing | PASS | 5.62s | extra spaces between macro name and argument |  |
| x26_two_arg_macro | PASS | 5.67s | two-arg matcher (a, b) needs the SAME call shape; paren call fails (quirk) |  |
| x27_macro_in_match_body | PASS | 5.69s | control: macro at top level still fine after layout checks |  |
| x28_stringify_num | PASS | 5.84s | stringify needs an identifier; numbers error |  |
| x29_macro_shadow_prelude | PASS | 5.72s | macro shadowing a prelude function name (probe) |  |
| x30_empty_rule_list | PASS | 5.67s | macro with no rules (probe) |  |
| x31_ident_used_twice | PASS | 5.62s | $n used twice creates duplicate defs (probe) |  |
| x32_raw_multiline | PASS | 5.69s | raw fragment spanning lines |  |
| x33_macro_keeps_layout | PASS | 5.69s | macro-expanded match: succ(zero) binds m=zero, prints 0 |  |
| x34_recursive_macro_expansion_limit | PASS | 5.86s | self-referential macro hits the depth limit (256) immediately |  |
| x35_macro_named_stringify2 | PASS | 5.70s | identifier close to builtin names |  |