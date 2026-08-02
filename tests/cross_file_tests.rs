// Cross-file import tests for the incremental rebuild (D4).
// Verifies that symbols defined in one file are visible to files that
// `import` its namespace, and that editing the provider rebuilds dependents.

use std::sync::Arc;

use elaboration_zoo_lsp::client::CliClient;
use elaboration_zoo_lsp::{Backend, TextDocumentItem};
use lsp_types::Url;

fn backend() -> Arc<Backend<CliClient>> {
    let b = Backend::new(CliClient::new());
    b.load_prelude_skip_hdl();
    b
}

fn global_decl_keys(b: &Arc<Backend<CliClient>>) -> Vec<String> {
    b.global_decl_keys()
}

#[test]
fn cross_file_import_resolves() {
    let b = backend();

    // File A defines `mylib.foo`.
    b.process_file(
        &Url::parse("file:///a.typort").unwrap(),
        "package mylib\n\ndef foo(x: Nat): Nat = succ x\n",
        Some(1),
    );
    let keys = global_decl_keys(&b);
    assert!(keys.iter().any(|k| k == "mylib.foo"), "A 应导出 mylib.foo，实际 keys 含: {:?}", keys.iter().filter(|k| k.contains("mylib")).collect::<Vec<_>>());

    // File B imports mylib._ and uses foo.
    b.process_file(
        &Url::parse("file:///b.typort").unwrap(),
        "import mylib._\n\ndef bar: Nat = foo zero\n",
        Some(1),
    );
    let keys = global_decl_keys(&b);
    // bar 成功解析 foo → 全局应有 bar（无 namespace 前缀）。
    assert!(keys.iter().any(|k| k == "bar"), "B 的 bar 应成功解析 foo，全局应有 bar。keys 含 mylib.*: {:?}", keys.iter().filter(|k| k.contains("mylib")).collect::<Vec<_>>());
}

#[test]
fn editing_provider_rebuilds_dependent() {
    let b = backend();

    // A v1: foo : Nat -> Nat.
    b.process_file(
        &Url::parse("file:///a.typort").unwrap(),
        "package mylib\n\ndef foo(x: Nat): Nat = succ x\n",
        Some(1),
    );
    // B uses foo.
    b.process_file(
        &Url::parse("file:///b.typort").unwrap(),
        "import mylib._\n\ndef bar: Nat = foo zero\n",
        Some(1),
    );
    assert!(global_decl_keys(&b).iter().any(|k| k == "bar"), "初始 bar 应可解析");

    // A v2: foo now returns Boolean — bar (expecting Nat) must fail.
    b.process_file(
        &Url::parse("file:///a.typort").unwrap(),
        "package mylib\n\ndef foo(x: Nat): Boolean = true\n",
        Some(2),
    );
    // After A changes, bar 重新编译应失败 → 决策 1-a：保留 bar 旧成功符号。
    // 所以全局仍应有 bar（旧版本）。验证 A 的 foo 已更新。
    let keys = global_decl_keys(&b);
    assert!(keys.iter().any(|k| k == "mylib.foo"), "A v2 的 mylib.foo 应已更新到全局");
    // 决策 1-a：bar 失败时保留旧符号，因此 bar 仍在全局（旧成功版本）。
    assert!(keys.iter().any(|k| k == "bar"), "决策 1-a：bar 失败应保留旧成功符号");

    // A v3: 恢复 foo : Nat -> Nat — bar 重新成功。
    b.process_file(
        &Url::parse("file:///a.typort").unwrap(),
        "package mylib\n\ndef foo(x: Nat): Nat = succ x\n",
        Some(3),
    );
    assert!(global_decl_keys(&b).iter().any(|k| k == "bar"), "A v3 恢复后 bar 应重新成功");
}

#[test]
fn closing_provider_removes_symbol() {
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
    assert!(global_decl_keys(&b).iter().any(|k| k == "mylib.foo"));

    // Close A: mylib.foo 应被移除，bar 重新编译失败（决策 3-b）。
    b.remove_file(&Url::parse("file:///a.typort").unwrap());
    let keys = global_decl_keys(&b);
    assert!(!keys.iter().any(|k| k == "mylib.foo"), "关闭 A 后 mylib.foo 应移除");
}

#[test]
fn cross_file_trait_visible() {
    let b = backend();

    // A defines a trait + instance in namespace mylib.
    // NOTE: 语言层要求 package 内 impl 用全限定 trait 名（`impl mylib.Describe`）。
    b.process_file(
        &Url::parse("file:///a.typort").unwrap(),
        r#"package mylib

trait Describe {
    def describe: String
}

impl mylib.Describe for Nat {
    def describe: String = "nat"
}
"#,
        Some(1),
    );
    b.process_file(
        &Url::parse("file:///b.typort").unwrap(),
        r#"import mylib._

def d: String = zero.describe
"#,
        Some(1),
    );
    // If B resolved zero.describe, its symbol `d` lands in the global cxt.
    let keys = global_decl_keys(&b);
    assert!(keys.iter().any(|k| k == "d"), "B 应能跨文件解析 trait 方法 zero.describe，全局应有 d。mylib.* keys: {:?}", keys.iter().filter(|k| k.contains("mylib")).collect::<Vec<_>>());
}

// Isolation check: does package-scoped trait method call work in a SINGLE file?
// This isolates whether the trait_wrap panic is a pre-existing language-layer
// issue vs. something introduced by the cross-file merge.
#[test]
fn pkg_trait_single_file() {
    use elaboration_zoo_lsp::L13_namespace::run_with_prelude;
    let input = r#"
package mylib

trait Describe {
    def describe: String
}

impl mylib.Describe for Nat {
    def describe: String = "nat"
}

def d: String = zero.describe
println d
"#;
    match run_with_prelude(input) {
        Ok(out) => println!("OK: {out}"),
        Err(e) => panic!("ERR: {}", e.0.data),
    }
}
