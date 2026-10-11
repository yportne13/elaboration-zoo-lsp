# r07-namespace — 实验结果

- probes: 30  PASS: 30  FAIL: 0  TIMEOUT: 0  NOEXPECT: 0

| id | verdict | time | probe | note |
|---|---|---|---|---|
| n01_qualified_call | PASS | 5.67s | package-prefixed def called with full path |  |
| n02_package_switch | PASS | 5.70s | second package block switches the prefix |  |
| n03_import_single | PASS | 5.73s | single-name import brings the bare name |  |
| n04_import_braces | PASS | 5.69s | braced selective import |  |
| n05_import_wildcard | PASS | 5.69s | wildcard import |  |
| n06_import_type_not_brought | PASS | 5.70s | import sq only; other members still reachable qualified |  |
| n07_import_no_prefix_leak | PASS | 5.78s | braced import does NOT bring the mylib prefix itself (S3) |  |
| n08_shadow_prelude | PASS | 5.72s | D1 confirmed: prelude bare alias wins over imported user def |  |
| n09_local_beats_import | PASS | 5.88s | QUIRK: import alias beats same-file decl defined after it |  |
| n10_qualified_beats_local | PASS | 5.77s | qualified access ignores the local shadow |  |
| n11_deep_package | PASS | 5.72s | four-level package path |  |
| n12_import_middle_segment | PASS | 5.77s | import middle segment NOT supported (D2: last seg is a member) |  |
| n13_import_wildcard_scope | PASS | 5.75s | wildcard import then local def of same name |  |
| n14_two_packages_same_file | PASS | 5.70s | both packages usable in one file |  |
| n15_package_empty | PASS | 5.75s | package decl with no members still parses |  |
| n16_package_dotted_call_chain | PASS | 5.66s | qualified calls inside another package's def |  |
| n17_enum_in_package | PASS | 5.59s | enum ctor via package prints qualified |  |
| n18_struct_in_package | PASS | 5.66s | struct + factory in a package |  |
| n19_import_enum_ctor | PASS | 5.67s | import Type._ brings constructors (S1/S3 semantics) |  |
| n20_import_enum_type_itself | PASS | 5.70s | import the type; ctor via prelude-like bare alias (probe) |  |
| n21_undefined_ns | PASS | 5.67s | unknown namespace prefix errors |  |
| n22_undefined_member | PASS | 5.62s | unknown member in known namespace errors |  |
| n23_import_missing | PASS | 5.70s | import of a missing member (probe: error or lazy) |  |
| n24_suffix_fallback | PASS | 5.78s | suffix fallback only for known decl-key heads (works here) |  |
| n25_suffix_fallback_denied | PASS | 5.80s | suffix fallback denied on a plain function value |  |
| n26_ns_method_on_result | PASS | 5.84s | inherent impl method in a package still resolves |  |
| n27_import_conflict | PASS | 5.84s | two imports of different names coexist |  |
| n28_package_then_use_before | PASS | 5.73s | same-package members NOT auto-visible; must qualify (quirk) |  |
| n29_nested_ns_hover_shape | PASS | 5.75s | fully-qualified type and ctor paths compose |  |
| n30_wildcard_prelude_clash | PASS | 5.89s | user zero shadows prelude ctor ambiguously (probe: unify error) |  |