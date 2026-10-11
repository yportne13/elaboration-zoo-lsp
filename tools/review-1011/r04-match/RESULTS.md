# r04-match — 实验结果

- probes: 43  PASS: 43  FAIL: 0  TIMEOUT: 0  NOEXPECT: 0

| id | verdict | time | probe | note |
|---|---|---|---|---|
| m01_missing_case | PASS | 5.78s | missing constructor blue -> non-exhaustive error |  |
| m02_full_coverage | PASS | 5.67s | all constructors covered |  |
| m03_wildcard_covers | PASS | 5.67s | wildcard arm covers everything |  |
| m04_bool_both | PASS | 5.69s | Boolean exhaustive |  |
| m05_nat_cases | PASS | 5.59s | Nat zero/succ exhaustive |  |
| m06_option_cases | PASS | 5.61s | Opt none/some exhaustive |  |
| m07_wildcard_then_case | PASS | 5.64s | case after wildcard (probe: unreachable or accepted) |  |
| m08_dup_case | PASS | 5.67s | duplicate arm accepted silently (quirk; expect first-wins) |  |
| m09_deep_succ | PASS | 5.67s | deep succ(succ(m)) pattern |  |
| m10_nested_opt | PASS | 5.64s | nested constructor patterns |  |
| m11_nested_in_arm_body | PASS | 5.62s | match inside an arm body; curried call |  |
| m12_nested_in_arm_body2 | PASS | 5.66s | match inside an arm body, two-arg call |  |
| m13_vec_nil_cons | PASS | 5.62s | Vec nil/cons match with implicit length index (qualified ctors; bare nil/cons hit prelude Vec per D1) |  |
| m14_fin_cases | PASS | 5.66s | Fin indexed match |  |
| m15_eq_refl_j | PASS | 5.61s | J-style match on Eq refl |  |
| m16_eq_motive_dependent | PASS | 5.80s | dependent motive: refl arm transports x to y |  |
| m17_gadt_refine_index | PASS | 5.69s | GADT: index 1 refines to cons arm (nil impossible; probe exhaustiveness) |  |
| m18_match_scrut_reduce | PASS | 5.62s | scrutinee reduces before match |  |
| s01_struct_basic | PASS | 5.66s | struct make + field access |  |
| s02_struct_dependent | PASS | 5.69s | parametrized struct |  |
| s03_struct_nested | PASS | 5.72s | nested struct field chain |  |
| s04_struct_missing_field | PASS | 5.75s | missing field in literal errors |  |
| s05_struct_wrong_type | PASS | 5.61s | wrong field type errors |  |
| s06_struct_extra_field | PASS | 5.80s | extra argument in literal errors |  |
| s07_struct_pattern_match | PASS | 5.62s | struct ctor patterns (P.mk(a, b)) NOT supported in match (parse error; quirk) |  |
| s08_struct_field_of_expr | PASS | 5.56s | field access as scrutinee |  |
| t01_tuple_literal | PASS | 5.64s | tuple literal creates value |  |
| t02_tuple_match | PASS | 6.31s | tuple pattern in match NOT supported (bizarre error; quirk) |  |
| t03_tuple_arity3 | PASS | 5.84s | 3-tuple literal |  |
| t04_nested_tuple | PASS | 5.62s | nested tuple |  |
| u01_enum_data_carrying | PASS | 5.25s | data-carrying enum match (1-arg and 2-arg ctors) |  |
| u02_enum_recursive | PASS | 5.25s | recursive enum + recursion |  |
| u03_ctor_qualified | PASS | 5.47s | qualified ctor names (Color7.red) NOT supported in patterns (quirk) |  |
| u04_void_match | PASS | 5.47s | empty enum: absurd function (probe: empty match allowed?) |  |
| u05_single_ctor | PASS | 5.55s | single-constructor match |  |
| x01_zero_and_wildcard | PASS | 6.00s | zero + wildcard coverage |  |
| x02_shadowed_binder | PASS | 5.95s | pattern binder shadows scrutinee name |  |
| x03_match_result_is_value | PASS | 5.58s | match expression used inside arithmetic |  |
| x04_arm_type_mismatch | PASS | 5.59s | arm body type mismatch errors |  |
| x05_scrut_type_unknown | PASS | 5.48s | scrutinee type hole (probe) |  |
| x06_wildcard_binder_mix | PASS | 5.56s | specific + wildcard mix |  |
| x07_deep_pattern_3 | PASS | 5.62s | 3-deep succ patterns + default |  |
| x08_qualified_ctor_expr | PASS | 5.59s | qualified constructor expression |  |