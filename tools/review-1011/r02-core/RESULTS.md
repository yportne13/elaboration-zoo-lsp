# r02-core — 实验结果

- probes: 43  PASS: 43  FAIL: 0  TIMEOUT: 0  NOEXPECT: 0

| id | verdict | time | probe | note |
|---|---|---|---|---|
| c01_beta_id | PASS | 6.75s | beta: identity application evaluates |  |
| c02_beta_nested | PASS | 5.23s | nested beta redexes fully evaluate |  |
| c03_delta_prelude | PASS | 5.59s | delta: prelude def unfolds in evaluation |  |
| c04_eval_order | PASS | 5.66s | arguments evaluate inside applications (call-by-value NBE) |  |
| c05_conv_beta | PASS | 5.62s | conversion under beta: 1+1 =?= 2 evaluates |  |
| c06_conv_in_type | PASS | 5.53s | types convert under arithmetic (Vec index n+0 vs n) |  |
| c07_noncumulativity | PASS | 6.45s | Type 0 : Type 1 (a single step is fine) |  |
| c08_noncumulativity_fail | PASS | 6.72s | NO cumulativity: Type 0 does not check against Type 5 |  |
| c09_universe_of_pi | PASS | 5.49s | Pi over small types lives in Type 1; polymorphic fn typechecks |  |
| c10_universe_pi_level | PASS | 5.61s | large elimination Pi at Type 1 |  |
| c11_eta_lam | PASS | 5.81s | eta-expanded application still evaluates |  |
| c12_conv_eta | PASS | 5.39s | eta-related terms are definitionally equal via def aliasing |  |
| c13_neutral_var | PASS | 5.58s | printing a function value (neutral) must not crash |  |
| c14_stuck_add | PASS | 5.30s | stuck term reduces when instantiated: Eq(f 0, 1) holds by refl |  |
| c15_neutral_index | PASS | 10.06s | GADT-index function type checks with neutral index |  |
| c16_refl_add0 | PASS | 12.70s | refl proves closed arithmetic equalities |  |
| c17_refl_fail | PASS | 11.25s | refl must FAIL on false closed equality |  |
| c18_eq_symm | PASS | 6.22s | symm of a definitional equality |  |
| c19_cong | PASS | 12.73s | conversion under cong target: f(1+1) =?= f(2) =?= 4 |  |
| c20_recursion | PASS | 12.95s | structural recursion evaluates |  |
| c21_deep_eval | PASS | 12.14s | 50-deep recursion evaluates |  |
| c22_nonterm_guard | PASS | 10.44s | self-call with no structural decrease: termination checker verdict |  |
| c23_ackermann_small | PASS | 5.50s | nested recursion (ack 2 3 = 9) evaluates |  |
| c24_match_bool | PASS | 5.25s | match on Boolean evaluates |  |
| c25_match_nat_deep | PASS | 5.22s | match binds constructor args |  |
| c26_match_expr_reduction | PASS | 5.25s | scrutinee reduces before matching |  |
| c27_closure_capture | PASS | 5.30s | closure captures environment |  |
| c28_shadowing | PASS | 5.22s | let shadows parameter |  |
| c29_higher_order | PASS | 5.22s | higher-order application |  |
| c30_partial_app | PASS | 6.61s | partial application via currying |  |
| c31_arith_mixed | PASS | 10.67s | operator precedence and mixed arithmetic |  |
| c32_div_mod | PASS | 11.36s | prelude div/mod primops |  |
| c33_zero_div | PASS | 10.31s | division by zero: must not hang or crash |  |
| c34_sub_underflow | PASS | 6.73s | truncated subtraction underflow semantics (probe: 0 or error) |  |
| c35_eq_nat_op | PASS | 6.58s | Nat equality decision |  |
| c36_print_deep | PASS | 6.86s | 100-deep result quoting round-trips |  |
| c37_print_type | PASS | 6.25s | printing a type value |  |
| c38_print_string_concat | PASS | 6.06s | string primop evaluates |  |
| c39_wrong_ann | PASS | 5.98s | String literal against Nat annotation errors |  |
| c40_apply_nonfn | PASS | 6.28s | applying a non-function errors cleanly |  |
| c41_undefined_var | PASS | 6.02s | undefined name errors with span |  |
| c42_type_in_term | PASS | 6.17s | using a type as a function body errors |  |
| c43_big_product | PASS | 6.20s | chained multiplication evaluates (3628800) |  |