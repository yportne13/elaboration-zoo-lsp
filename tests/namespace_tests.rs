// Namespace/import tests for the import_map refactor (stage 1 of the
// namespace-completion plan, docs/namespace-completion-plan.md).
//
// Verifies that import aliases are file-local visibility (kept on the
// per-file `Infer.import_map`, NOT inserted into `cxt.decl`), that import
// diagnostics fire (ambiguous / not-in-scope / single-name), that importing
// a type brings its `.mk` member, and that a local def legally shadows an
// import.

use std::sync::Arc;

use elaboration_zoo_lsp::client::CliClient;
use elaboration_zoo_lsp::Backend;
use lsp_types::Url;

fn backend() -> Arc<Backend<CliClient>> {
    let b = Backend::new(CliClient::new());
    b.load_prelude_skip_hdl();
    b
}

fn global_decl_keys(b: &Arc<Backend<CliClient>>) -> Vec<String> {
    b.global_decl_keys()
}

fn has_key(b: &Arc<Backend<CliClient>>, key: &str) -> bool {
    global_decl_keys(b).iter().any(|k| k == key)
}

// G1: import aliases must NOT leak into the global symbol table.
// File B imports `mylib._`; the bare alias `foo` must not appear in the
// global decl (only the fully-qualified `mylib.foo` does). Before the
// import_map refactor the whole-map write-back leaked `foo` into global.
#[test]
fn import_alias_not_leaked_to_global() {
    let b = backend();

    b.process_file(
        &Url::parse("file:///a.typort").unwrap(),
        "package mylib\n\ndef foo(x: Nat): Nat = succ x\n",
        Some(1),
    );
    b.process_file(
        &Url::parse("file:///b.typort").unwrap(),
        "import mylib._\n\ndef bar: Nat = foo zero\n",
        Some(1),
    );

    let keys = global_decl_keys(&b);
    assert!(has_key(&b, "mylib.foo"), "A 应导出 mylib.foo，keys: {:?}", keys);
    assert!(has_key(&b, "bar"), "B 的 bar 应成功解析 foo，keys: {:?}", keys);
    assert!(!has_key(&b, "foo"), "import 别名 foo 不得泄漏进全局，keys: {:?}", keys);
}

// G1a: importing a namespace whose member collides with a prelude alias
// (`mylib.zero` vs prelude `Nat.zero → zero`) must NOT overwrite the prelude
// alias in the global decl. The prelude alias wins (decl-exact), so `succ zero`
// still type-checks.
#[test]
fn import_does_not_overwrite_prelude_alias() {
    let b = backend();

    b.process_file(
        &Url::parse("file:///a.typort").unwrap(),
        "package mylib\n\ndef zero: Boolean = true\n",
        Some(1),
    );
    b.process_file(
        &Url::parse("file:///b.typort").unwrap(),
        "import mylib._\n\ndef check: Nat = succ zero\n",
        Some(1),
    );

    assert!(has_key(&b, "check"),
        "prelude 别名 zero 应优先于 import 的 mylib.zero，check 应编译通过，keys: {:?}",
        global_decl_keys(&b));
}

// I1: two wildcard imports exposing the same bare name must error
// (`ambiguous import`), not silently let the last one win.
#[test]
fn double_wildcard_import_conflicts() {
    let b = backend();

    b.process_file(
        &Url::parse("file:///a.typort").unwrap(),
        "package liba\n\ndef add(x: Nat): Nat = succ x\n",
        Some(1),
    );
    b.process_file(
        &Url::parse("file:///c.typort").unwrap(),
        "package libb\n\ndef add(x: Nat): Nat = succ x\n",
        Some(1),
    );
    b.process_file(
        &Url::parse("file:///b.typort").unwrap(),
        "import liba._\nimport libb._\n\ndef bar: Nat = add zero\n",
        Some(1),
    );

    assert!(has_key(&b, "liba.add"), "liba.add 应存在");
    assert!(has_key(&b, "libb.add"), "libb.add 应存在");
    assert!(!has_key(&b, "bar"),
        "冲突 import 应报错，bar 不应进入全局，keys: {:?}",
        global_decl_keys(&b));
}

// I2: importing a nonexistent namespace must error, not silently no-op.
#[test]
fn nonexistent_import_errors() {
    let b = backend();

    b.process_file(
        &Url::parse("file:///b.typort").unwrap(),
        "import nosuch._\n\ndef bar: Nat = zero\n",
        Some(1),
    );

    assert!(!has_key(&b, "bar"),
        "不存在的 namespace 应报错，bar 不应进入全局，keys: {:?}",
        global_decl_keys(&b));
}

// Dotted aliases: `import mylib.Tree` must bring the type AND its `.mk`
// member, so both the type annotation `Tree` and the constructor `Tree.mk`
// keep working.
#[test]
fn import_type_brings_mk_member() {
    let b = backend();

    b.process_file(
        &Url::parse("file:///a.typort").unwrap(),
        "package mylib\n\nstruct Tree {\n    h: Nat\n}\n",
        Some(1),
    );
    b.process_file(
        &Url::parse("file:///b.typort").unwrap(),
        "import mylib.Tree\n\ndef t: Tree = Tree.mk zero\n",
        Some(1),
    );

    assert!(has_key(&b, "t"),
        "import mylib.Tree 后 Tree/Tree.mk 应可用，keys: {:?}",
        global_decl_keys(&b));
}

// Local def shadows an import (legal): `import mylib._` then `def foo` — the
// local def wins over the imported alias, so `bar` compiles.
#[test]
fn local_def_shadows_import() {
    let b = backend();

    b.process_file(
        &Url::parse("file:///a.typort").unwrap(),
        "package mylib\n\ndef foo(x: Nat): Nat = succ x\n",
        Some(1),
    );
    b.process_file(
        &Url::parse("file:///b.typort").unwrap(),
        "import mylib._\n\ndef foo(x: Nat): Nat = succ x\n\ndef bar: Nat = foo zero\n",
        Some(1),
    );

    assert!(has_key(&b, "foo"), "本地 def foo 应写回全局");
    assert!(has_key(&b, "bar"),
        "本地 def 应覆盖 import 别名（合法 shadowing），bar 应编译通过，keys: {:?}",
        global_decl_keys(&b));
}

// G4: a single-name import (`import foo`, no dotted namespace) is rejected.
#[test]
fn single_name_import_rejected() {
    let b = backend();

    b.process_file(
        &Url::parse("file:///b.typort").unwrap(),
        "import foo\n\ndef bar: Nat = zero\n",
        Some(1),
    );

    assert!(!has_key(&b, "bar"),
        "单名 import 应报错，bar 不应进入全局，keys: {:?}",
        global_decl_keys(&b));
}

// G1a'（实测修正）：top-level defs cannot shadow prelude aliases — a bare
// `def zero` is rejected with `redefine zero` by the def-elaboration guard
// (fake_bind).  So the prelude alias is never clobbered by a user def, and it
// must still resolve as `Nat.zero` afterwards.
#[test]
fn real_def_cannot_clobber_prelude_alias() {
    let b = backend();

    // B tries to shadow the prelude alias; the def is rejected, so the file
    // fails and nothing reaches the global symbol table.
    b.process_file(
        &Url::parse("file:///b.typort").unwrap(),
        "def zero: Boolean = true\n\ndef check: Boolean = zero\n",
        Some(1),
    );
    assert!(!has_key(&b, "check"),
        "def zero 应被 redefine 检查拒绝，check 不应进入全局，keys: {:?}",
        global_decl_keys(&b));

    b.remove_file(&Url::parse("file:///b.typort").unwrap());

    // C still resolves `zero` as the prelude `Nat.zero`.
    b.process_file(
        &Url::parse("file:///c.typort").unwrap(),
        "def t: Nat = succ zero\n",
        Some(1),
    );
    assert!(has_key(&b, "t"),
        "prelude 别名 zero 应保持可用，t 应编译通过，keys: {:?}",
        global_decl_keys(&b));
}

// I4: `x.method` dispatch for a type + inherent impl defined in the SAME
// package file.  Was broken (probe confirmed `mylib.Foo has no object
// double`): prefix_decl_name prefixed the method name (`mylib.double`) so the
// namespace registry / trait_wrap dispatch (bare `double`) missed.  Fixed by
// not prefixing inherent impl methods and registering `TypeName.method` via
// `infer_after_prefix`.
#[test]
fn inherent_method_in_package_dispatches() {
    let b = backend();

    b.process_file(
        &Url::parse("file:///p.typort").unwrap(),
        "package mylib\n\nstruct Foo {\n    h: Nat\n}\n\nimpl Foo {\n    def double: Nat = this.h + this.h\n}\n\ndef use(f: Foo): Nat = f.double\n",
        Some(1),
    );

    assert!(has_key(&b, "mylib.Foo"), "struct 类型应注册");
    assert!(has_key(&b, "mylib.use"),
        "同文件 `f.double` 应可解析（I4 修复后，use 在 package 内注册为 mylib.use），keys: {:?}",
        global_decl_keys(&b));
}

// PROBE (X2): a class defined in a package — are its phase-B generated defs
// correctly package-prefixed?  Expect the struct/methods to be reachable.
#[test]
fn probe_class_in_package() {
    let b = backend();

    b.process_file(
        &Url::parse("file:///p.typort").unwrap(),
        "package mylib\n\nclass Adder {\n    def add(x: Nat): Nat = x\n}\n\ndef mk: Adder = Adder.mk\n",
        Some(1),
    );

    assert!(has_key(&b, "mylib.Adder"),
        "PROBE X2: 类类型应带包前缀注册，keys: {:?}",
        global_decl_keys(&b));
}

// Regression: a `trait` declared inside a `package` must be registered with a
// SINGLE package prefix.  (Discovered by the X3 probe: the trait re-elaborates
// as its record enum via `self.infer`, which re-applied `prefix_decl_name` and
// produced `mylib.mylib.HasVal`.  Fixed by using `infer_after_prefix`.)
#[test]
fn trait_in_package_single_prefixed() {
    let b = backend();

    b.process_file(
        &Url::parse("file:///p.typort").unwrap(),
        "package mylib\n\ntrait HasVal {\n    def getVal: Nat\n}\n\ndef probe: Nat = zero\n",
        Some(1),
    );

    let keys = global_decl_keys(&b);
    assert!(keys.iter().any(|k| k == "mylib.HasVal"),
        "trait 应单前缀注册为 mylib.HasVal，keys: {:?}", keys);
    assert!(!keys.iter().any(|k| k.contains("mylib.mylib")),
        "trait 不得双前缀（mylib.mylib.HasVal），keys: {:?}", keys);
    assert!(keys.iter().any(|k| k == "mylib.probe"),
        "package 内 def 应前缀为 mylib.probe");
}

// X3: supertrait references inside a package must resolve through the package
// prefix.  `trait HasVal2: HasVal` in `package mylib` must inherit HasVal's
// methods — so `impl HasVal2 for Foo` that omits the (defaultless) inherited
// `getVal` must fail, and one that provides it must compile.
#[test]
fn supertrait_in_package_inherits_methods() {
    let b = backend();

    // Without providing the inherited (defaultless) getVal: must fail.
    b.process_file(
        &Url::parse("file:///p.typort").unwrap(),
        "package mylib\n\ntrait HasVal {\n    def getVal: Nat\n}\n\ntrait HasVal2: HasVal {\n    def getVal2: Nat\n}\n\nstruct Foo {\n    h: Nat\n}\n\nimpl HasVal2 for Foo {\n    def getVal2: Nat = this.h\n}\n\ndef probe: Nat = zero\n",
        Some(1),
    );
    assert!(!has_key(&b, "mylib.probe"),
        "supertrait 方法 getVal 应被 HasVal2 继承并要求实现（X3 修复后），probe 不应编译，keys: {:?}",
        global_decl_keys(&b));

    // With the inherited method provided: must compile.
    b.process_file(
        &Url::parse("file:///p.typort").unwrap(),
        "package mylib\n\ntrait HasVal {\n    def getVal: Nat\n}\n\ntrait HasVal2: HasVal {\n    def getVal2: Nat\n}\n\nstruct Foo {\n    h: Nat\n}\n\nimpl HasVal2 for Foo {\n    def getVal: Nat = this.h\n    def getVal2: Nat = this.h\n}\n\ndef probe: Nat = zero\n",
        Some(2),
    );
    assert!(has_key(&b, "mylib.probe"),
        "提供继承方法后应编译通过（X3 修复后），keys: {:?}",
        global_decl_keys(&b));
}

// G5: a file's exported macros must be removed from the global table when the
// file closes (before: `exported_macros` only ever grew).
#[test]
fn closing_file_removes_exported_macro() {
    let b = backend();

    let uri = Url::parse("file:///a.typort").unwrap();
    b.process_file(
        &uri,
        "#[macro_export]\nmacro_rules mym {\n    ($x: raw) => { $x $x }\n}\n",
        Some(1),
    );
    assert!(b.exported_macros.contains_key("mym"),
        "A 应导出宏 mym，exported_macros: {:?}",
        b.exported_macros.iter().map(|e| e.key().clone()).collect::<Vec<_>>());

    b.remove_file(&uri);
    assert!(!b.exported_macros.contains_key("mym"),
        "关闭 A 后宏 mym 应移除，exported_macros: {:?}",
        b.exported_macros.iter().map(|e| e.key().clone()).collect::<Vec<_>>());
}

// G5: two files exporting the same macro name — closing one must NOT remove
// the macro (it is still exported by the other file).
#[test]
fn closing_one_of_two_same_name_macros_keeps_it() {
    let b = backend();

    let a = Url::parse("file:///a.typort").unwrap();
    let c = Url::parse("file:///c.typort").unwrap();
    b.process_file(&a, "#[macro_export]\nmacro_rules mym {\n    ($x: raw) => { $x $x }\n}\n", Some(1));
    b.process_file(&c, "#[macro_export]\nmacro_rules mym {\n    ($x: raw) => { $x }\n}\n", Some(1));
    assert!(b.exported_macros.contains_key("mym"), "两文件均应导出 mym");

    b.remove_file(&c);
    assert!(b.exported_macros.contains_key("mym"),
        "关闭 C 后 mym 仍应由 A 导出，exported_macros: {:?}",
        b.exported_macros.iter().map(|e| e.key().clone()).collect::<Vec<_>>());
}

// G8: a parse failure must clear the file's exported macros (its exports are
// unknown/stale), without touching symbols from the last successful parse.
#[test]
fn parse_failure_clears_exported_macros() {
    let b = backend();

    let uri = Url::parse("file:///a.typort").unwrap();
    b.process_file(&uri, "#[macro_export]\nmacro_rules mym {\n    ($x: raw) => { $x $x }\n}\n", Some(1));
    assert!(b.exported_macros.contains_key("mym"), "A 应导出宏 mym");

    b.process_file(&uri, "def ok: Nat = zero\nthis is not valid {{{", Some(2));
    assert!(!b.exported_macros.contains_key("mym"),
        "A 解析失败后宏 mym 应移除，exported_macros: {:?}",
        b.exported_macros.iter().map(|e| e.key().clone()).collect::<Vec<_>>());
}

// G2: a sub-namespace import (`import mylib.Tree._`) must record a dependency
// edge to its provider (`package mylib`), so editing/closing the provider
// rebuilds the dependent.  Before: the dep was recorded as `mylib.Tree` and
// never matched the provider's `mylib`.
#[test]
fn sub_namespace_import_dep_recorded() {
    let b = backend();

    b.process_file(
        &Url::parse("file:///a.typort").unwrap(),
        "package mylib\n\nstruct Tree {\n    h: Nat\n}\n",
        Some(1),
    );
    b.process_file(
        &Url::parse("file:///b.typort").unwrap(),
        "import mylib.Tree._\n\ndef bar: Tree = Tree.mk zero\n",
        Some(1),
    );
    assert!(has_key(&b, "bar"),
        "import mylib.Tree._ 应可用，bar 应编译通过，keys: {:?}",
        global_decl_keys(&b));

    // The dependency edge must be the sub-namespace path `mylib.Tree`.
    let deps = b.file_deps.get("file:///b.typort")
        .map(|e| e.value().clone())
        .unwrap_or_default();
    assert!(deps.contains("mylib.Tree"),
        "B 的依赖应含子命名空间 mylib.Tree，实际: {:?}", deps);

    // Closing the provider (package mylib) removes the sub-namespace symbol.
    b.remove_file(&Url::parse("file:///a.typort").unwrap());
    assert!(!has_key(&b, "mylib.Tree"),
        "关闭 A 后 mylib.Tree 应移除，keys: {:?}",
        global_decl_keys(&b));
}

// G2: editing the provider of a sub-namespace import must rebuild the
// dependent.  A v1 makes `Tree.mk` take Nat; A v2 flips it to Boolean, so B's
// `Tree.mk zero` must fail on re-elaboration.  Since decision 1-a keeps B's
// old global symbols, the rebuild is observed via B's `type_map` (the failed
// `bar` drops out of B's re-elaborated terms).
#[test]
fn editing_sub_namespace_provider_rebuilds_dependent() {
    let b = backend();
    let a = Url::parse("file:///a.typort").unwrap();
    let b_uri = "file:///b.typort";

    b.process_file(&a, "package mylib\n\nstruct Tree {\n    h: Nat\n}\n", Some(1));
    b.process_file(
        &Url::parse(b_uri).unwrap(),
        "import mylib.Tree._\n\ndef bar: Tree = Tree.mk zero\n\ndef baz: Nat = zero\n",
        Some(1),
    );
    assert!(has_key(&b, "bar"), "初始 bar 应可解析");
    // terms = [Import, bar, baz]
    assert_eq!(b.type_map.get(b_uri).map(|e| e.value().len()).unwrap_or(0), 3,
        "B 应有 Import + bar + baz 三个 term");

    // A v2: `Tree.mk` now takes Boolean — B must be rebuilt and `bar` fails.
    b.process_file(&a, "package mylib\n\nstruct Tree {\n    w: Boolean\n}\n", Some(2));
    let terms = b.type_map.get(b_uri).map(|e| e.value().len()).unwrap_or(0);
    assert_eq!(terms, 2,
        "B 应被子命名空间依赖触发重建，bar 失败后 type_map 只剩 Import + baz（terms={}），当前: {:?}",
        terms, b.type_map.get(b_uri).map(|e| e.value().len()).unwrap_or(0));
}

// G3: a single file declaring multiple `package`s must register as a provider
// for ALL of them, and closing it must remove symbols from all.
#[test]
fn multi_package_file_registers_all() {
    let b = backend();

    b.process_file(
        &Url::parse("file:///a.typort").unwrap(),
        "package liba\n\ndef x: Nat = zero\n\npackage libb\n\ndef y: Nat = succ zero\n",
        Some(1),
    );
    assert!(has_key(&b, "liba.x"), "liba.x 应注册");
    assert!(has_key(&b, "libb.y"), "libb.y 应注册");

    // Both packages must be usable as import sources.
    b.process_file(
        &Url::parse("file:///b.typort").unwrap(),
        "import liba._\n\ndef bx: Nat = x\n",
        Some(1),
    );
    b.process_file(
        &Url::parse("file:///c.typort").unwrap(),
        "import libb._\n\ndef cy: Nat = y\n",
        Some(1),
    );
    assert!(has_key(&b, "bx"), "import liba._ 应可用");
    assert!(has_key(&b, "cy"), "import libb._ 应可用");

    // Closing A removes symbols from BOTH packages.
    b.remove_file(&Url::parse("file:///a.typort").unwrap());
    let keys = global_decl_keys(&b);
    assert!(!keys.iter().any(|k| k.starts_with("liba.")), "关闭 A 后 liba.* 应移除，keys: {:?}", keys);
    assert!(!keys.iter().any(|k| k.starts_with("libb.")), "关闭 A 后 libb.* 应移除，keys: {:?}", keys);
}

// I3b: a trait IMPL (`impl HasVal for Foo`) inside a package must resolve the
// trait name through the package prefix (`mylib.HasVal`).  Was broken with
// `trait 'HasVal' not declared`; fixed by resolving `trait_name` via
// `cxt.namespace_prefix` in the trait-impl branch.
#[test]
fn trait_impl_in_package_resolves() {
    let b = backend();

    b.process_file(
        &Url::parse("file:///p.typort").unwrap(),
        "package mylib\n\ntrait HasVal {\n    def getVal: Nat\n}\n\nstruct Foo {\n    h: Nat\n}\n\nimpl HasVal for Foo {\n    def getVal: Nat = this.h\n}\n\ndef use(f: Foo): Nat = f.getVal\n\ndef probe: Nat = zero\n",
        Some(1),
    );

    assert!(has_key(&b, "mylib.probe"),
        "trait impl 定义应编译通过（I3b 修复后），keys: {:?}",
        global_decl_keys(&b));
    assert!(has_key(&b, "mylib.use"),
        "trait 方法 `f.getVal` 应经实例派发（I3b），use 应编译通过，keys: {:?}",
        global_decl_keys(&b));
}

// V3: an imported type must work in TYPE positions (function params, return
// annotations), not just in value positions — types resolve through the same
// `infer_expr` path as values.
#[test]
fn imported_type_in_type_position() {
    let b = backend();

    b.process_file(
        &Url::parse("file:///a.typort").unwrap(),
        "package mylib\n\nstruct Tree {\n    h: Nat\n}\n",
        Some(1),
    );
    b.process_file(
        &Url::parse("file:///b.typort").unwrap(),
        "import mylib.Tree\n\ndef height(t: Tree): Tree = Tree.mk zero\n\ndef param_type: Nat = height (Tree.mk zero).h\n",
        Some(1),
    );

    assert!(has_key(&b, "height"),
        "import 的类型在函数参数/返回类型位置应可用（B 无 package，def 为裸名），keys: {:?}",
        global_decl_keys(&b));
}

// L1: a bare name that is not in scope but matches a unique `TypeName.name`
// in the global decl offers an import fix (`add import liba.foo`).  Reachable
// thanks to G6 (the fallback no longer resolves namespace-level bare names).
#[test]
fn not_in_scope_name_offers_import_fix() {
    let b = backend();

    b.process_file(
        &Url::parse("file:///a.typort").unwrap(),
        "package liba\n\ndef foo(x: Nat): Nat = succ x\n",
        Some(1),
    );
    b.process_file(
        &Url::parse("file:///b.typort").unwrap(),
        "def bar: Nat = foo zero\n",
        Some(1),
    );

    let fixes: Vec<String> = b.quickfix_map.get("file:///b.typort")
        .map(|m| m.value().values().flatten().filter_map(|f| f()).collect())
        .unwrap_or_default();
    assert!(fixes.iter().any(|f| f.contains("liba.foo")),
        "应建议 import liba.foo，fixes: {:?}", fixes);
}

// L5: hovering an intermediate segment of a qualified access (`mylib.Tree.mk`)
// should have a hover entry keyed to that segment's span (the `Tree` token),
// not just the whole-expression entry.
#[test]
fn qualified_access_hovers_intermediate_segments() {
    let b = backend();

    b.process_file(
        &Url::parse("file:///a.typort").unwrap(),
        "package mylib\n\nstruct Tree {\n    h: Nat\n}\n",
        Some(1),
    );
    let b_text = "import mylib._\n\ndef t: Tree = mylib.Tree.mk zero\n";
    b.process_file(&Url::parse("file:///b.typort").unwrap(), b_text, Some(1));

    let rope = ropey::Rope::from_str(b_text);
    let segments: Vec<String> = b.hover_table.get("file:///b.typort")
        .map(|infer| {
            infer.value().hover_table.iter()
                .map(|(span, _, _, _)| {
                    rope.byte_slice(span.start_offset as usize..span.end_offset as usize).to_string()
                })
                .collect()
        })
        .unwrap_or_default();
    assert!(segments.iter().any(|s| s == "Tree"),
        "应 hover 中间段 Tree（类型），segments: {:?}", segments);
}

// G6: the suffix fallback must NOT resolve namespace-level bare names
// (`foo` → `mylib.foo`) in a file that never imported/declared `mylib`.
// The fallback only matches first-level type heads (`TypeName.name` where
// `TypeName` is itself a decl key, e.g. `Expr.mux`).
#[test]
fn non_importing_file_does_not_leak_via_fallback() {
    let b = backend();

    b.process_file(
        &Url::parse("file:///a.typort").unwrap(),
        "package mylib\n\ndef foo(x: Nat): Nat = succ x\n",
        Some(1),
    );
    // C does NOT import mylib — `foo` must be not-in-scope.
    b.process_file(
        &Url::parse("file:///c.typort").unwrap(),
        "def usesFoo: Nat = foo zero\n",
        Some(1),
    );
    assert!(!has_key(&b, "usesFoo"),
        "G6: 不 import 的文件 C 不应经 fallback 解析 mylib.foo，usesFoo 不应编译，keys: {:?}",
        global_decl_keys(&b));

    // After importing mylib._ it resolves via import_map.
    b.process_file(
        &Url::parse("file:///c.typort").unwrap(),
        "import mylib._\n\ndef usesFoo: Nat = foo zero\n",
        Some(2),
    );
    assert!(has_key(&b, "usesFoo"),
        "import mylib._ 后 foo 应可解析，keys: {:?}",
        global_decl_keys(&b));
}

// G7: the LSP backend's prelude auto-import must exclude namespace-registered
// instance methods (e.g. `Boolean.not`) from the bare-name aliases — methods
// are reachable only through `x.method` dispatch or qualified access.  This
// aligns lib.rs with the test/cache path (mod.rs::load_prelude_state) and
// makes the alias winner deterministic.
#[test]
fn prelude_alias_excludes_instance_methods() {
    let b = backend();

    let keys = global_decl_keys(&b);
    assert!(has_key(&b, "zero"),
        "构造子别名 zero（Nat.zero）应存在，keys: {:?}", keys);
    assert!(has_key(&b, "true"),
        "构造子别名 true（Boolean.true）应存在，keys: {:?}", keys);
    assert!(!has_key(&b, "not"),
        "实例方法别名 not（Boolean.not）不得出现为裸名，keys: {:?}", keys);
}
