// Big-Nat display compression regression tests — R4 修复钉
// （docs/l13-quirks-analysis-2026-10.md §4 R4）。
//
// quote 对原生 `XCell::Nat(k)`/`Val::Nat(k)` 的 k 节点一元 succ 链展开
// 使 `println (nat_mul 100000 100000)` 在显示管线挂死。
//
// **落地口径（2026-10-02）**：参考版 `nf` 内部换 `quote_dec`（原生 Nat →
// 十进制 `Tm::LiteralIntro`，nat_to_dec prim 同格式化）——大数/溢出/小数
// 基线全绿。孪生版 println 显示位**暂不接线**（Machine::quote_dec 已备、
// 未使用）：孪生值层不把 succ(原生 Nat) 折叠成 Nat(k+1)（参考版 eval
// 折叠），nat_dec 路径会把 `succ (nat_mul 3 4)` 渲染成 `12 + 1` 而参考版
// 是 `13`，诊断 parity 会分叉；接线前须先对齐值层折叠。孪生大数显示挂死
// 当前由 eval_budget 看门狗兜底（下方引擎级钉）。

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

/// 一次 println 的渲染串（末次发布的 INFORMATION 诊断首行）。
fn run_printlns(engine: Engine, src: &str, name: &str) -> Vec<String> {
    let b: Arc<Backend<CapturingClient>> = Backend::new_with_engine(CapturingClient::default(), engine);
    b.load_prelude_skip_hdl();
    let uri = Url::parse(&format!("file:///bignum_display_{name}.typort")).unwrap();
    b.process_file(&uri, src, Some(0));
    let diags = b
        .client
        .diagnostics
        .lock()
        .unwrap();
    let last = diags
        .iter()
        .filter(|(u, _, _)| *u == uri)
        .last()
        .map(|(_, d, _)| d.iter().cloned().collect::<Vec<_>>())
        .unwrap_or_default();
    drop(diags);
    last.iter()
        .filter(|d| d.severity == Some(lsp_types::DiagnosticSeverity::INFORMATION))
        .map(|d| d.message.lines().next().unwrap_or("").to_string())
        .collect()
}

/// 10^10 原生 Nat：原先 quote 展开亿级节点挂死，现参考版直接十进制。
/// （孪生显示压缩待接线，见文件头；本用例只钉参考版。）
#[test]
fn large_native_nat_prints_decimal_reference() {
    let out = run_printlns(Engine::Reference, "println (nat_mul 100000 100000)\n", "mul_big");
    assert_eq!(out, vec!["10000000000".to_string()]);
}

/// nat_pow 2 64 溢出 u64：值卡在 `nat_mul 2 (2^63)` 的 Decl spine 上，
/// 原先实参里的原生 2^63 被 quote 展开同样挂死；现渲染为紧凑中缀
/// （pretty 的 nat primop 符号恢复：nat_mul → `*`）。参考版口径。
#[test]
fn overflow_stuck_nat_mul_renders_compact_infix_reference() {
    let out = run_printlns(Engine::Reference, "println (nat_pow 2 64)\n", "pow64");
    assert_eq!(out, vec!["2 * 9223372036854775808".to_string()]);
}

/// 小数/一元链基线（修复前 CLI 实测逐项一致）：原生 Nat、用户写的一元
/// succ 链、zero、primop 结果、nat_to_dec 字符串、succ 包裹的 primop 结果
/// ——渲染与修复前完全相同。双引擎（孪生显示位未接线，行为同修复前）。
#[test]
fn small_nat_and_unary_chain_rendering_is_unchanged() {
    let src = concat!(
        "println 2\n",
        "println (succ (succ zero))\n",
        "println zero\n",
        "println (nat_mul 2 3)\n",
        "println (nat_add 5 7)\n",
        "println (nat_pow 2 10)\n",
        "println (nat_to_dec 5)\n",
        "println (succ (nat_mul 3 4))\n",
    );
    let expect = ["2", "2", "0", "6", "12", "1024", "5", "13"];
    for engine in [Engine::Reference, Engine::Twin] {
        let out = run_printlns(engine, src, "small");
        assert_eq!(
            out,
            expect.iter().map(|s| s.to_string()).collect::<Vec<_>>(),
            "{engine:?}"
        );
    }
}

// 注意：多行大数 println 的组合口径未钉——`1000000000` 这类**大字面量**
// 的 elaboration 本身走 succ 链展开是独立慢路径（非 R4 显示压缩范畴），
// 单行用例（上方两件）已覆盖显示压缩的核心，字面量成本问题见交接文档。

// 孪生大数显示的内存护栏钉在 lib 侧（孪生内部件不对集成测试公开）：
// L13_namespace::eval_budget_tests::twin_big_nat_display_aborts_via_chain_guard
// —— 2026-10-07 该钉的前身（…_pending_watchdog_catches）在链展开上把提交量
// 顶到 121.8 GB 并拖垮主机，故改为钉 guard_nat_chain（见 eval_budget.rs）。

