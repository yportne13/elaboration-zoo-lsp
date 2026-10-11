# r01-parser — 实验结果

- probes: 43  PASS: 42  FAIL: 1  TIMEOUT: 0  NOEXPECT: 0

| id | verdict | time | probe | note |
|---|---|---|---|---|
| e01_comment_eof_no_newline | PASS | 4.97s | single-line comment at EOF without newline |  |
| e02_nested_block_comment | PASS | 4.94s | nested block comments (are they nesting?) |  |
| e03_unterminated_block_comment | PASS | 4.94s | unterminated block comment |  |
| e04_unbalanced_close_comment | PASS | 4.94s | stray closing comment delimiter |  |
| e05_unicode_ident_cjk | PASS | 4.95s | CJK identifier accepted and printable |  |
| e06_nbsp_between_tokens | PASS | 4.91s | NBSP between tokens should be rejected (not silently accepted) |  |
| e07_zero_width_in_ident | PASS | 4.98s | zero-width space inside identifier should error |  |
| e08_bom_at_start | PASS | 4.92s | UTF-8 BOM at file start is tolerated |  |
| e09_crlf_endings | PASS | 4.91s | CRLF line endings |  |
| e10_tab_indent | PASS | 5.03s | tab indentation |  |
| e11_num_formats | PASS | 5.02s | leading-zero and large decimal literals |  |
| e12_universe_max | PASS | 4.94s | universe level u32::MAX rejected (max usable is MAX-1) |  |
| e13_universe_overflow | PASS | 4.97s | universe level beyond u32 must be a parser error (F2 pin) |  |
| e14_big_nat_literal | FAIL | 4.97s | huge Nat literal (bignum display) | error: find unsolved meta with type `Nat` | error: error name not in scope: big (declaration failed to elaborate above) |
| e15_negative_literal | PASS | 4.97s | negative literal is not a Nat |  |
| e16_leading_plus | PASS | 4.95s | leading + on literal |  |
| e17_string_escapes | PASS | 4.94s | string escape sequences parse |  |
| e18_string_unterminated | PASS | 4.95s | unterminated string literal |  |
| e19_string_comment | PASS | 4.92s | // inside string is not a comment |  |
| e20_deep_parens_200 | PASS | 4.94s | 200 nested parens |  |
| e21_deep_parens_3000 | PASS | 4.95s | 3000 nested parens must not crash (depth guard or iteration) |  |
| e22_long_ident | PASS | 4.94s | 8000-char identifier |  |
| e23_many_decls | PASS | 4.97s | 300 top-level defs |  |
| e24_empty_file | PASS | 4.94s | completely empty file |  |
| e25_only_comments | PASS | 4.92s | only comments |  |
| e26_def_missing_body | PASS | 4.94s | def with missing body errors gracefully |  |
| e27_unbalanced_brace_enum | PASS | 4.91s | unclosed enum brace: error, no panic |  |
| e28_extra_close_brace | PASS | 4.94s | stray closing brace at top level |  |
| e29_semicolon_after_def | PASS | 4.95s | semicolon after decl (probe: accepted or error?) |  |
| e30_trailing_comma_call | PASS | 4.92s | trailing comma in call args is accepted |  |
| e31_trailing_comma_params | PASS | 4.95s | trailing comma in parameter list is accepted |  |
| e32_mixed_sep_args | PASS | 4.97s | space-separated args inside call parens |  |
| e33_precedence_mul_add | PASS | 4.91s | * binds tighter than +: prints 7 |  |
| e34_tight_arrow | PASS | 4.98s | no-space -> arrow in type |  |
| e35_lambda_two_args | PASS | 4.94s | (x, y) => ... multi-arg lambda is NOT supported (curry instead) |  |
| e36_keyword_as_ident | PASS | 4.92s | keyword as identifier rejected |  |
| e37_duplicate_def | PASS | 4.95s | duplicate definition is an error or warning |  |
| e38_hole_expr | PASS | 4.97s | hole expression -> unsolved meta error |  |
| e39_comment_between_args | PASS | 4.95s | line comment inside call args |  |
| e40_derive_show | PASS | 4.94s | #[derive(Show)] enum; one-line multi-ctor braces need newlines (layout) |  |
| e41_let_in_def | PASS | 4.95s | let-binding with semicolon inside def |  |
| e42_named_implicit_call | PASS | 4.89s | explicit implicit application f[Nat] |  |
| e43_match_spacing | PASS | 5.00s | match arms parse with varied spacing |  |

## 非 PASS 详情

### e14_big_nat_literal — FAIL
`error: find unsolved meta with type `Nat` | error: error name not in scope: big (declaration failed to elaborate above)`

```text
--- stdout ---

--- stderr ---
Analyzing: file:///F:/projects/hermes/elaboration-zoo-lsp/tools/review-1011/r01-parser/e14_big_nat_literal.typort (109 bytes)
[LOG log] change: file:///F:/projects/hermes/elaboration-zoo-lsp/tools/review-1011/r01-parser/e14_big_nat_literal.typort
[LOG log] parser 0.0003055
[LOG log] infer 0.0026051
error: find unsolved meta with type `Nat`
  ┌─ /F:/projects/hermes/elaboration-zoo-lsp/tools/review-1011/r01-parser/e14_big_nat_literal.typort:3:16
  │
3 │ def big: Nat = 1000000000000000000000
  │                ^^^^^^^^^^^^^^^^^^^^^^

error: error name not in scope: big (declaration failed to elaborate above)
  ┌─ /F:/projects/hermes/elaboration-zoo-lsp/tools/review-1011/r01-parser/e14_big_nat_literal.typort:4:9
  │
4 │ println(big)
  │         ^^^

error: integer literal does not fit in u64
  ┌─ /F:/projects/hermes/elaboration-zoo-lsp/tools/review-1011/r01-parser/e14_big_nat_literal.typort:3:16
  │
3 │ def big: Nat = 1000000000000000000000
  │                ^^^^^^^^^^^^^^^^^^^^^^

[LOG log] change 0.004037
```
