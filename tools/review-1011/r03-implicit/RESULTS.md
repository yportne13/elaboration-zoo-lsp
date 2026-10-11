# r03-implicit — 实验结果

- probes: 44  PASS: 44  FAIL: 0  TIMEOUT: 0  NOEXPECT: 0

| id | verdict | time | probe | note |
|---|---|---|---|---|
| i01_hole_body | PASS | 5.39s | hole in def body -> unsolved meta error |  |
| i02_hole_infer_type | PASS | 5.34s | annotated hole expression (typed hole syntax probe) |  |
| i03_hole_let | PASS | 5.42s | hole in let RHS |  |
| i04_hole_match_arm | PASS | 5.47s | hole in one match arm (arms on separate lines: layout) |  |
| i05_hole_scrutinee | PASS | 5.39s | hole as scrutinee |  |
| i06_many_holes | PASS | 5.56s | several holes in one expression |  |
| i07_hole_type_pos | PASS | 5.44s | hole in type annotation solves to Nat by unification |  |
| i08_hole_print | PASS | 5.61s | hole directly in println |  |
| i09_implicit_auto | PASS | 5.70s | implicit A auto-solved from the explicit argument |  |
| i10_implicit_explicit | PASS | 5.89s | explicit implicit application |  |
| i11_implicit_named | PASS | 5.98s | named implicit application |  |
| i12_implicit_lambda | PASS | 5.81s | implicit lambda binds the implicit Pi |  |
| i13_implicit_wrong_type | PASS | 5.86s | explicit implicit mismatch (Nat vs Boolean arg) must fail |  |
| i14_implicit_order | PASS | 5.81s | multiple implicits resolved in order |  |
| i15_implicit_dep_chain | PASS | 5.77s | dependent implicit chain: both args share A |  |
| i16_implicit_partially_explicit | PASS | 5.53s | partial implicit application: B from y |  |
| i17_implicit_expected_type | PASS | 5.17s | annotation-driven implicit solving (bidirectional) |  |
| i18_implicit_in_pattern | PASS | 5.08s | implicit type parameter on a match function (hole in dead arm) |  |
| i19_check_lambda | PASS | 5.16s | lambda checked against Pi (check mode) |  |
| i20_check_lambda_implicit_pi | PASS | 5.08s | implicit lambda inserted when checking against implicit Pi |  |
| i21_lambda_wrong_domain | PASS | 5.12s | body type error under check mode points into the body |  |
| i22_check_nested | PASS | 5.11s | curried lambda check |  |
| i23_insert_implicit_lam | PASS | 5.14s | elaborator inserts implicit lambda around explicit-only body |  |
| i24_meta_no_solution | PASS | 5.12s | solved meta reused in wrong position fails |  |
| i25_occurs_check | PASS | 5.12s | sanity: plain def before occurs probes |  |
| i26_unsolved_prints_meta | PASS | 5.08s | implicit solves through a def alias chain |  |
| i27_implicit_typeclass_style | PASS | 5.12s | Trait.method(x) static form is NOT supported (use x.method()) |  |
| i28_implicit_enum_param | PASS | 5.08s | GADT-style enum implicit parameter solved by constructor |  |
| i29_implicit_shadow | PASS | 5.27s | term binder shadowing an implicit type name |  |
| i30_implicit_unused | PASS | 5.16s | unused implicit stays unsolved but does not block a Nat result |  |
| i31_infer_lambda_no_ann | PASS | 5.47s | bare lambda: lazy domain meta, monomorphic after first use (quirk) |  |
| i32_ann_drives_match | PASS | 5.17s | annotation drives recursive function elaboration |  |
| i33_tuple_ann | PASS | 5.12s | struct literal checked against annotation |  |
| i34_ann_wrong_arity | PASS | 5.39s | arity mismatch between annotation and lambda |  |
| i35_poly_id_id | PASS | 5.77s | higher-kinded implicit: A := Nat -> Nat |  |
| i36_implicit_nat_index | PASS | 5.69s | indexed constructor elaborates with implicit index metas |  |
| i37_expected_hole_type | PASS | 5.75s | hole in codomain solved from the body (bidirectional) |  |
| i38_deep_implicit_nesting | PASS | 5.62s | three-level implicit alias chain |  |
| i39_implicit_bool_dual | PASS | 5.62s | implicit solved from two positions consistently |  |
| i40_named_arg_explicit_probe | PASS | 5.67s | named EXPLICIT args (probe: supported?) |  |
| i41_implicit_from_annotation_only | PASS | 5.67s | type-only implicit with no explicit args (probe) |  |
| i42_hole_in_implicit_arg | PASS | 5.67s | hole passed as an explicit implicit: solved from the next arg |  |
| i43_implicit_mixed_icit | PASS | 5.67s | interleaved explicit/implicit parameter groups |  |
| i44_type0_hole_defaulting_warns | PASS | 5.69s | Type-0 hole silently defaulting to Nat now surfaces TY001 |  |