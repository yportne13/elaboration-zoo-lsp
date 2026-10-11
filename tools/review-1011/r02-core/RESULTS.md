# r02-core — 实验结果

- probes: 43  PASS: 43  FAIL: 0  TIMEOUT: 0  NOEXPECT: 0

| id | verdict | time | probe | note |
|---|---|---|---|---|
| c01_beta_id | PASS | 5.62s | beta: identity application evaluates |  |
| c02_beta_nested | PASS | 5.58s | nested beta redexes fully evaluate |  |
| c03_delta_prelude | PASS | 5.59s | delta: prelude def unfolds in evaluation |  |
| c04_eval_order | PASS | 5.56s | arguments evaluate inside applications |  |
| c05_conv_beta | PASS | 5.59s | conversion under beta: 1+1 =?= 2 evaluates |  |
| c06_conv_in_type | PASS | 5.66s | types convert under arithmetic (hole keeps it unsolved) |  |
| c07_noncumulativity | PASS | 5.56s | Type 0 : Type 1 (a single step is fine) |  |
| c08_noncumulativity_fail | PASS | 5.58s | NO cumulativity: Type 0 does not check against Type 5 |  |
| c09_universe_of_pi | PASS | 5.64s | Pi over small types; polymorphic fn typechecks |  |
| c10_universe_pi_level | PASS | 5.56s | large elimination Pi at Type 1 |  |
| c11_eta_lam | PASS | 5.59s | eta-expanded application still evaluates |  |
| c12_conv_eta | PASS | 5.52s | eta-related terms are definitionally equal via def aliasing |  |
| c13_neutral_var | PASS | 5.58s | printing a function value (neutral) must not crash |  |
| c14_stuck_add | PASS | 5.61s | stuck term reduces when instantiated: Eq(f 0, 1) holds by rfl |  |
| c15_neutral_index | PASS | 5.61s | neutral-headed application on variables stays well-typed |  |
| c16_refl_add0 | PASS | 5.59s | rfl proves closed arithmetic equalities |  |
| c17_refl_fail | PASS | 5.62s | rfl must FAIL on false closed equality |  |
| c18_eq_symm | PASS | 5.70s | symm of a definitional equality |  |
| c19_cong | PASS | 5.67s | conversion under cong target: f(1+1) =?= f(2) =?= 4 |  |
| c20_recursion | PASS | 5.78s | structural recursion evaluates |  |
| c21_deep_eval | PASS | 5.84s | 50-deep recursion evaluates |  |
| c22_nonterm_guard | PASS | 5.55s | self-call with no structural decrease: termination checker verdict |  |
| c23_ackermann_small | PASS | 5.55s | nested recursion (ack 2 3 = 9) evaluates |  |
| c24_match_bool | PASS | 5.67s | match on Boolean evaluates |  |
| c25_match_nat_deep | PASS | 6.14s | match binds constructor args |  |
| c26_match_expr_reduction | PASS | 5.72s | scrutinee reduces before matching |  |
| c27_closure_capture | PASS | 5.73s | closure captures environment |  |
| c28_shadowing | PASS | 5.61s | let shadows parameter |  |
| c29_higher_order | PASS | 5.52s | higher-order application |  |
| c30_partial_app | PASS | 5.58s | partial application via currying |  |
| c31_arith_mixed | PASS | 5.50s | operator precedence and mixed arithmetic |  |
| c32_div_mod | PASS | 5.58s | prelude div/mod primops (nat_mod absent is the recorded quirk) |  |
| c33_zero_div | PASS | 5.59s | division by zero: saturating (returns dividend), must not hang |  |
| c34_sub_underflow | PASS | 5.62s | truncated subtraction underflow semantics |  |
| c35_eq_nat_op | PASS | 5.48s | Nat equality decision |  |
| c36_print_deep | PASS | 5.53s | 100-deep result quoting round-trips |  |
| c37_print_type | PASS | 5.50s | printing a type value |  |
| c38_print_string_concat | PASS | 5.55s | string primop evaluates |  |
| c39_wrong_ann | PASS | 5.52s | String literal against Nat annotation errors |  |
| c40_apply_nonfn | PASS | 5.56s | applying a non-function errors cleanly |  |
| c41_undefined_var | PASS | 5.50s | undefined name errors with span |  |
| c42_type_in_term | PASS | 5.53s | using a type as a function body errors |  |
| c43_big_product | PASS | 5.58s | chained multiplication evaluates (3628800) |  |