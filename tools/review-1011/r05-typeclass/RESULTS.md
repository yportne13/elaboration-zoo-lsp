# r05-typeclass — 实验结果

- probes: 40  PASS: 40  FAIL: 0  TIMEOUT: 0  NOEXPECT: 0

| id | verdict | time | probe | note |
|---|---|---|---|---|
| f5_1_typevar_receiver | PASS | 4.95s | F5-1: receiver method on a type VARIABLE ignores the constraint (unsupported) |  |
| f5_2_prelude_dict_silent | PASS | 4.91s | F5-2: prelude-instance dict can stay silently neutral (prints ?m.show, no error) |  |
| f5_4_trait_arity_lax | PASS | 4.94s | impl arity < trait arity accepted without error (probe; laxness quirk) |  |
| q01_receiver_method | PASS | 4.89s | dict-projected call on a concrete instance |  |
| q02_inherent_impl | PASS | 4.94s | inherent impl adds a method (receiver dot-call) |  |
| q04_default_method | PASS | 4.94s | default method body used when impl is empty |  |
| q05_no_instance | PASS | 4.89s | control: instance exists -> works |  |
| q06_dup_impl | PASS | 5.08s | duplicate instance for the same type (probe) |  |
| q07_dict_constraint | PASS | 4.95s | [T][d: Doubles[T]] implicit fills the dict (canonical idiom) |  |
| q08_two_instances | PASS | 4.92s | search picks the matching instance among several |  |
| q09_param_type_instance | PASS | 4.89s | impl[A] Trait for Box2[A] (generic instance, unconditional) |  |
| q10_conditional_instance | PASS | 4.91s | impl[T: Half] conditional instance: NOT supported (prelude show.typort documents) |  |
| q11_supertrait_basic | PASS | 4.89s | bare supertrait decl; impl provides both methods |  |
| q12_supertrait_dispatch | PASS | 4.91s | supertrait dict satisfied by subtrait instance |  |
| q13_operator_trait | PASS | 4.92s | prelude operator traits resolve on Nat |  |
| q14_custom_operator | PASS | 4.94s | user operator trait ++ as infix WORKS |  |
| q18_derive_show | PASS | 4.89s | #[derive(Show)] zero-arg ctors |  |
| q19_derive_show_data | PASS | 4.92s | derive(Show) single-case enum WITH ctor args (fixed R5) |  |
| q19b_derive_show_multi_data | PASS | 4.92s | derive(Show) multi-case with args |  |
| q20_wrong_instance_type | PASS | 4.97s | method used at a type with no instance errors |  |
| q21_missing_method | PASS | 4.95s | impl missing a required method (probe: error at impl or at use) |  |
| q22_trait_as_value | PASS | 4.95s | printing a trait name (probe) |  |
| q24_prelude_show_nat | PASS | 4.91s | prelude show on Nat via receiver |  |
| q25_prelude_show_string | PASS | 4.95s | prelude Show on String |  |
| q27_eq_fn | PASS | 4.91s | nat_eq works |  |
| q27b_eq_sugar | PASS | 4.97s | == sugar on Nat (probe) |  |
| q28_compare_operator | PASS | 4.92s | < on Nat via prelude trait |  |
| q31_method_with_arg | PASS | 4.92s | one-arg method called `obj.method arg` (this receiver) |  |
| q32_method_default_uses_other | PASS | 4.91s | default method calls the impl's override (probe: qualified dict form) |  |
| q33_dict_via_prelude_show | PASS | 4.88s | impl constrained by a prelude trait (probe) |  |
| q34_impl_for_fn_type | PASS | 4.95s | instance for a function type (probe) |  |
| q35_two_constraints | PASS | 4.89s | two dict constraints; unparenthesized d.m t + e.n t binds t as + lhs (precedence quirk) |  |
| q36_instance_on_tuple | PASS | 4.91s | instance for a tuple type (probe) |  |
| q37_shadowed_method_name | PASS | 4.92s | top-level fn and trait method coexist with the same name |  |
| q38_derive_show_struct | PASS | 4.91s | derive(Show) on struct (X.mk case keeps this.field path) |  |
| q40_trait_result_chain | PASS | 4.92s | trait method result feeding another constrained call |  |
| q41_chained_receivers | PASS | 4.89s | chained receiver calls on a concrete type |  |
| q42_polymorphic_recursion | PASS | 4.92s | generic inherent impl with receiver recursion |  |
| q43_empty_trait_marker | PASS | 4.91s | empty trait round-trips as a marker via dict |  |
| q44_ambiguity_detection | PASS | 4.92s | same method in two satisfied traits -> ambiguity error (doc §5.2) |  |