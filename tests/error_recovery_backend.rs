// Error-recovery (cascade) regression tests — 错误级联修复的行为钉。
//
// docs/l13-quirks-analysis-2026-10.md §3.1 的三个修复面，经 Backend
// （continue 型驱动：逐 decl 收诊断不中止）钉住：
//   A2 —— 失败 def 的下游引用报「引用了上方失败的声明」而非裸
//         "not in scope"，根因不被二阶错误淹没；无关 decl 照常求值。
//   B1 —— inherent impl/class 块内单个方法失败只影响该方法：好方法
//         照常注册求值，坏方法调用得到干净的 "has no object"。
//   B2 —— trait impl 失败方法以签名桩字段顶上：实例定义进表，好方法
//         可用，不再出现 "solve trait failed ... name not in scope"。
// 另钉 run_with_prelude 的排水口径：块内方法错误以 Err 冒出而非静默 OK。

use std::sync::{Arc, Mutex};

use elaboration_zoo_lsp::client::ClientLike;
use elaboration_zoo_lsp::{Backend, Engine, TextDocumentItem};
use lsp_types::{MessageType, Url};

#[derive(Default)]
struct CapturingClient {
    diagnostics: Mutex<Vec<(Url, Vec<lsp_types::Diagnostic>, Option<i32>)>>,
}

impl ClientLike for CapturingClient {
    fn publish_diagnostics(&self, uri: Url, diagnostics: Vec<lsp_types::Diagnostic>, version: Option<i32>) {
        self.diagnostics.lock().unwrap().push((uri, diagnostics, version));
    }
    fn show_message(&self, _typ: MessageType, _message: String) {}
    fn log_message(&self, _typ: MessageType, _message: String) {}
}

fn run_reference(text: &str) -> (Vec<String>, Vec<String>) {
    let b: Arc<Backend<CapturingClient>> = Backend::new_with_engine(CapturingClient::default(), Engine::Reference);
    b.load_prelude_skip_hdl();
    let uri = Url::from_file_path(std::env::temp_dir().join("error_recovery_probe.typort")).unwrap();
    b.on_change::<false>(TextDocumentItem { uri: uri.clone(), text, version: Some(0) });
    let diags: Vec<lsp_types::Diagnostic> = b
        .client
        .diagnostics
        .lock()
        .unwrap()
        .iter()
        .filter(|(u, _, _)| *u == uri)
        .flat_map(|(_, d, _)| d.iter())
        .cloned()
        .collect();
    let errors = diags
        .iter()
        .filter(|d| d.severity == Some(lsp_types::DiagnosticSeverity::ERROR))
        .map(|d| d.message.clone())
        .collect();
    // println 走 INFORMATION 诊断；只取消息首行（带源码回显时正文在前）。
    let printlns = diags
        .iter()
        .filter(|d| d.severity == Some(lsp_types::DiagnosticSeverity::INFORMATION))
        .map(|d| d.message.lines().next().unwrap_or("").to_string())
        .collect();
    (errors, printlns)
}

// ── A2：def 级联 ──

#[test]
fn def_cascade_root_cause_survives_downstream_downgraded() {
    let (errors, printlns) = run_reference(r#"
def broken: Nat = true
def use1: Nat = broken
def use2: Nat = succ broken
def independent: Nat = succ zero
println independent
"#);
    // 根因原样保留
    assert!(
        errors.iter().any(|e| e.contains("can't unify")),
        "root cause missing: {errors:?}"
    );
    // 下游引用降级为「引用了上方失败的声明」，不再是裸 not in scope
    assert!(
        errors.iter().any(|e| e.contains("declaration failed to elaborate above")),
        "downgraded downstream signal missing: {errors:?}"
    );
    // 无关 decl 照常求值（println 1 = succ zero）
    assert!(
        printlns.iter().any(|p| p.contains("1")),
        "independent def did not elaborate: {printlns:?}"
    );
}

// ── B1：inherent impl 好方法存活 ──

#[test]
fn inherent_impl_good_methods_survive_bad_sibling() {
    let (errors, printlns) = run_reference(r#"
enum QBox {
    qbox(n: Nat)
}
impl QBox {
    def good: Nat = 3
    def bad: Nat = true
    def good2: Nat = succ this.good
}
def qb: QBox = qbox 1
println qb.good
println qb.good2
println qb.bad
"#);
    // 坏方法的根因保留
    assert!(
        errors.iter().any(|e| e.contains("Boolean")),
        "bad method's error missing: {errors:?}"
    );
    // 好方法照常求值（3 与 succ 3 = 4）
    assert!(printlns.iter().any(|p| p.contains("3")), "good method lost: {printlns:?}");
    assert!(printlns.iter().any(|p| p.contains("4")), "good2 method lost: {printlns:?}");
    // 调用坏方法得到干净的 no-object（而非级联形态）
    assert!(
        errors.iter().any(|e| e.contains("no object") && e.contains("bad")),
        "clean no-object error for bad method missing: {errors:?}"
    );
}

// ── B2：trait impl 部分注册 ──

#[test]
fn trait_impl_partial_registration_good_method_usable() {
    let (errors, printlns) = run_reference(r#"
trait QShow {
    def qshow: String
    def qmark: String
}
enum QBox {
    qbox(n: Nat)
}
impl QShow for QBox {
    def qshow: String = "box"
    def qmark: String = nope_not_here
}
def qb: QBox = qbox 3
println qb.qshow
"#);
    // 根因保留
    assert!(
        errors.iter().any(|e| e.contains("nope_not_here")),
        "root cause missing: {errors:?}"
    );
    // 好方法经实例分派可用（实例定义已进表）
    assert!(
        printlns.iter().any(|p| p.contains("box")),
        "qshow via partially-registered instance lost: {printlns:?}"
    );
    // 不再出现旧的最迷惑级联形态
    assert!(
        !errors.iter().any(|e| e.contains("solve trait failed")),
        "solve-trait-failed cascade should be gone: {errors:?}"
    );
}

// ── run_with_prelude 排水口径：块内方法错误不静默 ──

#[test]
fn run_with_prelude_surfaces_class_method_errors() {
    let r = elaboration_zoo_lsp::L13_namespace::run_with_prelude(
        "class Foo {\n    let x: Nat = 1\n    def get: Nat = this.unknown\n}\n",
    );
    match r {
        Err(e) => assert!(
            e.0.data.contains("no object"),
            "expected no-object error, got: {}",
            e.0.data
        ),
        Ok(out) => panic!("class method error was swallowed (OK): {out}"),
    }
}
