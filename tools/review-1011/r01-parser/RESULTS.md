# r01-parser — 实验结果

- probes: 43  PASS: 43  FAIL: 0  TIMEOUT: 0  NOEXPECT: 0

| id | verdict | time | probe | note |
|---|---|---|---|---|
| e01_comment_eof_no_newline | PASS | 5.05s | single-line comment at EOF without newline |  |
| e02_nested_block_comment | PASS | 5.23s | nested block comments (are they nesting?) |  |
| e03_unterminated_block_comment | PASS | 5.25s | unterminated block comment |  |
| e04_unbalanced_close_comment | PASS | 5.14s | stray closing comment delimiter |  |
| e05_unicode_ident_cjk | PASS | 5.12s | CJK identifier accepted and printable |  |
| e06_nbsp_between_tokens | PASS | 5.34s | NBSP between tokens should be rejected (not silently accepted) |  |
| e07_zero_width_in_ident | PASS | 5.24s | zero-width space inside identifier should error |  |
| e08_bom_at_start | PASS | 5.22s | UTF-8 BOM at file start is tolerated |  |
| e09_crlf_endings | PASS | 5.22s | CRLF line endings |  |
| e10_tab_indent | PASS | 5.23s | tab indentation |  |
| e11_num_formats | PASS | 5.25s | leading-zero and large decimal literals |  |
| e12_universe_max | PASS | 5.27s | universe level u32::MAX rejected (max usable is MAX-1) |  |
| e13_universe_overflow | PASS | 5.17s | universe level beyond u32 must be a parser error (F2 pin) |  |
| e14_big_nat_literal | PASS | 5.17s | huge Nat literal: >u64 rejected with cascade noise (quirk) |  |
| e15_negative_literal | PASS | 5.23s | negative literal is not a Nat |  |
| e16_leading_plus | PASS | 5.53s | leading + on literal |  |
| e17_string_escapes | PASS | 5.25s | string escape sequences parse |  |
| e18_string_unterminated | PASS | 5.23s | unterminated string literal |  |
| e19_string_comment | PASS | 5.00s | // inside string is not a comment |  |
| e20_deep_parens_200 | PASS | 4.98s | 200 nested parens |  |
| e21_deep_parens_3000 | PASS | 4.97s | 3000 nested parens must not crash (depth guard or iteration) |  |
| e22_long_ident | PASS | 5.03s | 8000-char identifier |  |
| e23_many_decls | PASS | 5.03s | 300 top-level defs |  |
| e24_empty_file | PASS | 4.98s | completely empty file |  |
| e25_only_comments | PASS | 5.14s | only comments |  |
| e26_def_missing_body | PASS | 5.42s | def with missing body errors gracefully |  |
| e27_unbalanced_brace_enum | PASS | 5.14s | unclosed enum brace: error, no panic |  |
| e28_extra_close_brace | PASS | 5.19s | stray closing brace at top level |  |
| e29_semicolon_after_def | PASS | 5.12s | semicolon after decl (probe: accepted or error?) |  |
| e30_trailing_comma_call | PASS | 5.17s | trailing comma in call args is accepted |  |
| e31_trailing_comma_params | PASS | 5.30s | trailing comma in parameter list is accepted |  |
| e32_mixed_sep_args | PASS | 5.33s | space-separated args inside call parens |  |
| e33_precedence_mul_add | PASS | 5.20s | * binds tighter than +: prints 7 |  |
| e34_tight_arrow | PASS | 5.14s | no-space -> arrow in type |  |
| e35_lambda_two_args | PASS | 5.17s | (x, y) => ... multi-arg lambda is NOT supported (curry instead) |  |
| e36_keyword_as_ident | PASS | 5.22s | keyword as identifier rejected |  |
| e37_duplicate_def | PASS | 5.22s | duplicate definition is an error or warning |  |
| e38_hole_expr | PASS | 5.14s | hole expression -> unsolved meta error |  |
| e39_comment_between_args | PASS | 5.27s | line comment inside call args |  |
| e40_derive_show | PASS | 5.52s | #[derive(Show)] enum; one-line multi-ctor braces need newlines (layout) |  |
| e41_let_in_def | PASS | 5.78s | let-binding with semicolon inside def |  |
| e42_named_implicit_call | PASS | 5.76s | explicit implicit application f[Nat] |  |
| e43_match_spacing | PASS | 5.94s | match arms parse with varied spacing |  |