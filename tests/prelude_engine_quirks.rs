// ============================================================
// task-6 引擎怪癖回归钉：Nat 字面量 elaboration 深度护栏（L1 保守版 (c)）
//
// 背景（docs/prelude-stdlib-round-2026-10.md §3 / l13-quirks-analysis-2026-10.md
// §4「剩余敞口：大字面量 elaboration 慢路径」）：
//   `Raw::Nat(n)` 在 elaboration 期经 `quote`/`quote_nat` 展开成 n 层
//   `succ`/`zero` 链，之后 eval/force/unify/occurs/rename/pretty 与孪生转换
//   全部按 n 层递归。实测（HEAD 09:52 二进制，`l13bench --with-prelude core`）：
//     100000  → 0.75s 通过
//     1000000 → 109s 后 `thread '<unknown>' has overflowed its stack`（进程崩）
//   CLI `typort check` 同样炸在主线程。这不是"慢"，是"用户输入一个字面量就
//   崩服务端"。
//
// 修复：在**双引擎共用的 parser** 里，字面量 `n > NAT_LITERAL_ELAB_LIMIT`
// 时 `push_error` + 退化 `Raw::Hole`（与既有"整数超出 u64"路径同型），
// 报可诊断错误，不再把 n 层链交给 elaborator。阈值取值证据见
// `src/L13_namespace/parser/mod.rs::NAT_LITERAL_ELAB_LIMIT` 的文档注释。
//
// 边界为什么是 `>`（100000 保持可用）：100000 是仓库里实际使用的最大字面量
// （`legacy_tests.rs`、`eval_budget_tests.rs`、`tests/bignum_display.rs`），
// 复测整进程 0.6–0.9s PASS；真正病态的是再大一档（1e6 → 109s 后栈溢出）。
// 本轮曾出现「100000 是悬崖」的读数，事后证明是并发 `cargo build` 窗口内的
// 瞬时干扰假象（单次 TIMEOUT 不构成证据——详见常量注释的"读数纪律"）。
//
// 本文件钉四条：
//   1. 阈值**内**（含边界 100000）零解析错误 —— 不误伤现存写法；
//   2. 阈值**上**（100001 / 1000000）报错、且文案可诊断（含限制值与
//      `nat_mul` 改写建议）—— 错误而不是含糊的 internal error；
//   3. 推荐的分解式（`nat_mul`/`nat_add`）在阈值外仍可写 —— 有路可走；
//   4. LSP 端到端：超限字面量落成 ERROR 诊断而非崩溃/挂死。
// ============================================================

use elaboration_zoo_lsp::L13_namespace::parser::{parser, NAT_LITERAL_ELAB_LIMIT};

fn parse_errors(src: &str) -> (usize, Vec<String>) {
    let (decls, errors) = parser(src, 0).expect("parser never returns None for valid UTF-8");
    (
        decls.len(),
        errors.iter().map(|e| format!("{}", e.msg.data)).collect(),
    )
}

// ── 1. 边界内：正常 ──────────────────────────────────────────

#[test]
fn nat_literal_at_limit_parses_clean() {
    // 100000 = 仓库实际使用的最大字面量（下文各测试与 legacy/eval_budget/
    // bignum_display 都在用），复测整进程 0.6–0.9s PASS ⇒ 必须保持可用。
    let n = NAT_LITERAL_ELAB_LIMIT;
    let src = format!("def at_limit: Nat = {n}\n");
    let (decls, errs) = parse_errors(&src);
    assert!(
        errs.is_empty(),
        "阈值边界（{n}，仓库已验证可用的最大字面量）必须保持可用，errs: {errs:?}"
    );
    assert_eq!(decls, 1);
}

#[test]
fn small_nat_literal_parses_clean() {
    let (decls, errs) = parse_errors("def small: Nat = 4096\n");
    assert!(errs.is_empty(), "errs: {errs:?}");
    assert_eq!(decls, 1);
}

// ── 2. 阈值上：可诊断的报错（不是崩溃）──────────────────────

#[test]
fn nat_literal_just_above_limit_is_rejected_diagnosably() {
    let n = NAT_LITERAL_ELAB_LIMIT + 1;
    let (decls, errs) = parse_errors(&format!("def over: Nat = {n}\n"));
    assert_eq!(decls, 1, "退化 Raw::Hole 后声明仍应存活（错误恢复）");
    assert_eq!(errs.len(), 1, "应恰好一条诊断，errs: {errs:?}");
    let m = &errs[0];
    assert!(m.contains(&n.to_string()), "文案应含越界值 {n}，got: {m}");
    assert!(
        m.contains(&NAT_LITERAL_ELAB_LIMIT.to_string()),
        "文案应含限制值 {NAT_LITERAL_ELAB_LIMIT}，got: {m}"
    );
    assert!(
        m.contains("nat_mul") && m.contains("nat_add"),
        "文案应给出 `nat_mul`/`nat_add` 分解式建议，got: {m}"
    );
    assert!(
        m.to_lowercase().contains("elaboration"),
        "文案应说明这是 elaboration 展开深度限制，got: {m}"
    );
}

#[test]
fn huge_nat_literal_rejected_without_crash() {
    // 原崩溃复现值（10^6）：现在必须是"一条解析错误"，且解析立即返回。
    let (decls, errs) = parse_errors("def huge: Nat = 1000000\n");
    assert_eq!(decls, 1);
    assert_eq!(errs.len(), 1, "errs: {errs:?}");
    assert!(errs[0].contains("1000000"), "got: {}", errs[0]);
}

#[test]
fn oversized_u64_literal_still_takes_the_u64_path() {
    // 既有的 u64 溢出路径不能被新护栏吞掉（回归保护）。
    let (_decls, errs) = parse_errors("def x: Nat = 99999999999999999999999999\n");
    assert!(
        errs.iter().any(|m| m.contains("does not fit in u64")),
        "u64 溢出文案应保持不变，errs: {errs:?}"
    );
}

// ── 3. 推荐写法：阈值外的值用分解式仍然可写 ─────────────────

#[test]
fn decomposed_writing_beyond_limit_parses_clean() {
    // 10^6 不能用字面量写，但 `nat_mul` 分解式完全合法（走原生 primop）。
    let (decls, errs) = parse_errors("def big: Nat = nat_mul 1000 1000\n");
    assert!(errs.is_empty(), "分解式不应触发字面量护栏，errs: {errs:?}");
    assert_eq!(decls, 1);
}

// ── 4. LSP 端到端：诊断而非崩溃 ──────────────────────────────

mod lsp_e2e {
    use std::sync::Mutex;

    use elaboration_zoo_lsp::client::ClientLike;
    use elaboration_zoo_lsp::Backend;
    use lsp_types::{Diagnostic, DiagnosticSeverity, MessageType, Url};

    #[derive(Default)]
    struct CapturingClient {
        diagnostics: Mutex<Vec<(Url, Vec<Diagnostic>, Option<i32>)>>,
    }

    impl ClientLike for CapturingClient {
        fn publish_diagnostics(&self, uri: Url, diagnostics: Vec<Diagnostic>, version: Option<i32>) {
            self.diagnostics.lock().unwrap().push((uri, diagnostics, version));
        }
        fn show_message(&self, _typ: MessageType, _message: String) {}
        fn log_message(&self, _typ: MessageType, _message: String) {}
    }

    /// 走真实 LSP 路径（Backend::process_file → 完整 prelude → elaborate），
    /// 返回 (println INFORMATION 文本, 错误文本)。
    fn analyze(src: &str, tag: &str) -> (Vec<String>, Vec<String>) {
        let client = CapturingClient::default();
        let b = Backend::new(client);
        b.load_prelude();
        let uri = Url::parse(&format!("file:///{}.typort", tag)).unwrap();
        b.process_file(&uri, src, Some(1));
        let (mut infos, mut errs) = (Vec::new(), Vec::new());
        for (_, ds, _) in b.client.diagnostics.lock().unwrap().iter() {
            for d in ds {
                match d.severity {
                    Some(DiagnosticSeverity::INFORMATION) => infos.push(d.message.clone()),
                    Some(DiagnosticSeverity::ERROR) | None => errs.push(d.message.clone()),
                    _ => {}
                }
            }
        }
        (infos, errs)
    }

    #[test]
    fn over_limit_literal_is_a_diagnostic_not_a_crash() {
        // prelude 装载成功 + 文件分析返回（不挂死、不崩栈），错误可读。
        let (_infos, errs) = analyze(
            "def huge: Nat = 1000000\nprintln(\"still-alive\")\n",
            "equirks_big_literal",
        );
        assert!(
            errs.iter().any(|e| e.contains("elaboration limit")),
            "超限字面量应落成可诊断 ERROR，errs: {errs:?}"
        );
    }

    #[test]
    fn decomposed_value_beyond_limit_still_evaluates() {
        // 推荐的改写路径真的能跑：10^6 用 nat_mul 分解式求值并显示。
        let (infos, errs) = analyze("println(nat_mul 1000 1000)\n", "equirks_decomposed");
        assert!(errs.is_empty(), "分解式不应报错，errs: {errs:?}");
        assert!(
            infos.iter().any(|m| m.trim() == "1000000"),
            "nat_mul 1000 1000 应显示 1000000，infos: {infos:?}"
        );
    }
}
