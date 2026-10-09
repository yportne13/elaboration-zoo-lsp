// Round-2 engine-quirks diagnostic pins (task-18).
//
// Pins the targeted, error-path-only diagnostic for the *unsupported*
// `(e : T)` type-ascription syntax:
//
//   * the directional hint IS emitted, and the pre-existing parse errors
//     (`expected ')' , found ':'` / `expected newline`) are still emitted too;
//   * valid code is untouched (binder form, plain groups, tuple literals);
//   * a clean HDL example gets NO ascription diagnostic.  This is a real
//     regression pin: the first implementation counted only `(`…`)` while
//     scanning, so Verilog part-select colons (`{w[7:0], w[15:8]}`) inside a
//     macro-expanded group were misread as ascriptions and 3 bogus errors were
//     published for examples/hdl/24-verilog-practice.typort (which also broke
//     twin/reference diagnostic ordering in tests/twin_engine_tests.rs).

use std::sync::{Arc, Mutex};

use elaboration_zoo_lsp::client::ClientLike;
use elaboration_zoo_lsp::{Backend, Engine};
use lsp_types::{DiagnosticSeverity, MessageType, Url};

#[derive(Default)]
struct CapturingClient {
    diagnostics: Mutex<Vec<(Url, Vec<lsp_types::Diagnostic>, Option<i32>)>>,
    #[allow(dead_code)]
    logs: Mutex<Vec<String>>,
}

impl ClientLike for CapturingClient {
    fn publish_diagnostics(
        &self,
        uri: Url,
        diagnostics: Vec<lsp_types::Diagnostic>,
        version: Option<i32>,
    ) {
        self.diagnostics.lock().unwrap().push((uri, diagnostics, version));
    }
    fn show_message(&self, _typ: MessageType, _message: String) {}
    fn log_message(&self, _typ: MessageType, message: String) {
        self.logs.lock().unwrap().push(message);
    }
}

/// Parser-level pins do not need the HDL prelude (keeps this file fast).
fn backend(engine: Engine) -> Arc<Backend<CapturingClient>> {
    let b = Backend::new_with_engine(CapturingClient::default(), engine);
    b.load_prelude_skip_hdl();
    b
}

fn backend_hdl(engine: Engine) -> Arc<Backend<CapturingClient>> {
    let b = Backend::new_with_engine(CapturingClient::default(), engine);
    b.load_prelude();
    b
}

const HINT: &str = "supports neither type ascription";

/// Diagnostics of the last publish for `uri`, as plain messages.
fn messages(b: &Arc<Backend<CapturingClient>>, uri: &Url) -> Vec<String> {
    let d = b.client.diagnostics.lock().unwrap();
    match d.iter().filter(|(x, _, _)| x == uri).last().cloned() {
        Some((_, ds, _)) => ds.into_iter().map(|d| d.message).collect(),
        None => Vec::new(),
    }
}

fn errors(msgs: &[String]) -> Vec<&String> {
    msgs.iter().filter(|m| m.contains("expected") || m.contains(HINT)).collect()
}

fn hint_count(msgs: &[String]) -> usize {
    msgs.iter().filter(|m| m.contains(HINT)).count()
}

fn run(src: &str) -> Vec<String> {
    let uri = Url::parse("file:///round2_engine.typort").unwrap();
    let b = backend(Engine::Reference);
    b.process_file(&uri, src, Some(1));
    messages(&b, &uri)
}

#[test]
fn ascription_hint_fires_and_keeps_original_parse_errors() {
    let msgs = run("def z = (left 9 : Either[Nat, Boolean])");
    assert!(
        msgs.iter().any(|m| m.contains(HINT)),
        "expected the ascription hint, got {msgs:?}"
    );
    // 窗口 16：同一处 `:` 只允许一条（此前实参位会重复输出）。
    assert_eq!(hint_count(&msgs), 1, "hint must be emitted once, got {msgs:?}");
    // The hint is added, not substituted: the original recovery errors survive.
    assert!(
        msgs.iter().any(|m| m.contains("expected `)`")),
        "expected the original `expected ')'` error to be retained, got {msgs:?}"
    );
    assert!(
        msgs.iter().any(|m| m.contains("expected newline")),
        "expected the original recovery error to be retained, got {msgs:?}"
    );
    assert!(
        errors(&msgs).len() >= 3,
        "hint must not replace the original errors, got {msgs:?}"
    );
}

/// 窗口 16（verifier task-19）：`(x: T) => e` 这种**注解 lambda binder**在 def 体
/// 与实参位都**不被支持**，文案不能只讲 type ascription，且每个位置只能出现一次。
#[test]
fn annotated_lambda_positions_get_one_two_meaning_hint() {
    for src in [
        "def z = ((y: Nat) => y)",
        "def h(g: Nat, f: Nat): Nat = f\ndef z2: Nat = h (1, ((y: Nat) => y))",
    ] {
        let msgs = run(src);
        assert_eq!(
            hint_count(&msgs),
            1,
            "annotated-lambda position must emit exactly one hint for {src:?}, got {msgs:?}"
        );
        let hint = msgs.iter().find(|m| m.contains(HINT)).unwrap();
        assert!(
            hint.contains("annotated lambda binder"),
            "the message must cover the binder meaning too, got {hint:?}"
        );
        assert!(
            hint.contains("type ascription"),
            "the message must still cover the ascription meaning, got {hint:?}"
        );
        assert!(
            msgs.iter().any(|m| m.contains("expected `)`")),
            "the original parse error must be retained for {src:?}, got {msgs:?}"
        );
    }
}

#[test]
fn ascription_hint_fires_on_a_simple_group_too() {
    let msgs = run("def z = (1 : Nat)");
    assert!(
        msgs.iter().any(|m| m.contains(HINT)),
        "expected the ascription hint on a plain group, got {msgs:?}"
    );
    assert_eq!(hint_count(&msgs), 1, "hint must be emitted once, got {msgs:?}");
    assert!(msgs.iter().any(|m| m.contains("expected `)`")), "got {msgs:?}");
}

#[test]
fn ascription_hint_absent_on_valid_code() {
    for src in [
        // The documented workaround / binder form.
        "def z: Either[Nat, Boolean] = left 9",
        "def z: Nat = 1",
        // Plain parenthesised expression and a tuple literal.
        "def z: Nat = (1)",
        "def p(a: Nat, b: Nat): Nat = a\n\n\ndef q: Nat = p (1, 2)",
        // `[msb:lsb]`-shaped colons inside brackets are not ascriptions.
        "def f(v: Vec[4]): Nat = 0",
        // 窗口 16 反例（verifier task-19 要求零命中）：
        // verilog 位选 `w[7:0]` / `w[7:4]`、声明冒号、`{a: b}`、方括号 binder。
        "def z = w[7:0]",
        "def z = w[7:4]",
        "def bar: Nat = 3",
        "def z = {a: b}",
        "def k[T: Type] (x: T): T = x",
    ] {
        let msgs = run(src);
        assert!(
            !msgs.iter().any(|m| m.contains(HINT)),
            "unexpected ascription hint for {src:?}: {msgs:?}"
        );
    }
}

/// Regression pin: the HDL example must stay free of ascription diagnostics
/// (the pre-fix lookahead misread `[7:0]` part-select colons).
#[test]
fn hdl_example_has_no_ascription_false_positive() {
    let src = std::fs::read_to_string("examples/hdl/24-verilog-practice.typort").unwrap();
    let uri = Url::parse("file:///round2_hdl24.typort").unwrap();
    let b = backend_hdl(Engine::Reference);
    b.process_file(&uri, &src, Some(1));
    let msgs = messages(&b, &uri);
    assert!(
        !msgs.iter().any(|m| m.contains(HINT)),
        "ascription false positive in the HDL corpus example: {msgs:?}"
    );
    assert!(
        !msgs.iter().any(|m| m.contains("expected `)`")),
        "unexpected parse error in a clean HDL example: {msgs:?}"
    );
    // The example's own (unrelated) HDL warning must still be published.
    assert!(
        msgs.iter().any(|m| m.contains("HDV002")),
        "the HDL warning disappeared: {msgs:?}"
    );
}

/// The reference and the twin must publish the same diagnostics for the HDL
/// example (same messages, same order) -- the ordering divergence the first
/// implementation caused is pinned here on one file, cheaply.
#[test]
fn hdl_example_diagnostics_agree_between_reference_and_twin() {
    let src = std::fs::read_to_string("examples/hdl/24-verilog-practice.typort").unwrap();
    let uri = Url::parse("file:///round2_hdl24_twin.typort").unwrap();

    let rb = backend_hdl(Engine::Reference);
    rb.process_file(&uri, &src, Some(1));
    let rt = backend_hdl(Engine::Twin);
    rt.process_file(&uri, &src, Some(1));
    assert_eq!(messages(&rb, &uri), messages(&rt, &uri));
}

/// task-25 (J): `rfl[Nat] 3` -- the head's implicit binder is auto-filled by
/// `insert_t`, so the explicit `3` has no parameter left.  The failure keeps its
/// original `can't unify` and gains one directional note; all four workarounds
/// and ordinary implicit insertion stay clean.
const RFL_HINT: &str = "implicit argument was already filled in automatically";

#[test]
fn rfl_explicit_arg_gets_directional_note_and_keeps_cant_unify() {
    let msgs = run("def e_bad: Eq[Nat] 3 3 = rfl[Nat] 3");
    assert!(
        msgs.iter().any(|m| m.contains("can't unify")),
        "the original `can't unify` must be retained, got {msgs:?}"
    );
    assert!(
        msgs.iter().any(|m| m.contains(RFL_HINT) && m.contains("rfl[Nat] [3]")),
        "expected the bracketed-argument note, got {msgs:?}"
    );
    assert_eq!(
        msgs.iter().filter(|m| m.contains(RFL_HINT)).count(),
        1,
        "the note must appear once, got {msgs:?}"
    );
}

#[test]
fn rfl_note_absent_on_workarounds_and_implicit_insertion() {
    for src in [
        // 四个绕法（必须仍 PASS，不得有 note）
        "def e: Eq[Nat] 3 3 = rfl\ndef w: Nat = match e { case refl(a) => a }",
        "def e: Eq[Nat] 3 3 = rfl[Nat] [3]\ndef w: Nat = match e { case refl(a) => a }",
        "def e: Eq[Nat] 3 3 = rfl [Nat] [3]\ndef w: Nat = match e { case refl(a) => a }",
        "def e: Eq[Nat] 3 3 = rfl[Nat]\ndef w: Nat = match e { case refl(a) => a }",
        // 合法自动插隐式（不得误报）
        "def s: Option[Nat] = Some 3",
        "def f[A](a: A): A = a\ndef z: Nat = f 3",
    ] {
        let msgs = run(src);
        assert!(
            !msgs.iter().any(|m| m.contains(RFL_HINT)),
            "unexpected rfl note for {src:?}: {msgs:?}"
        );
        assert!(
            !msgs.iter().any(|m| m.contains("can't unify")),
            "unexpected unification failure for {src:?}: {msgs:?}"
        );
    }
}

#[test]
fn hint_severity_is_error() {
    let uri = Url::parse("file:///round2_sev.typort").unwrap();
    let b = backend(Engine::Reference);
    b.process_file(&uri, "def z = (1 : Nat)", Some(1));
    let d = b.client.diagnostics.lock().unwrap();
    let hint = d
        .iter()
        .filter(|(u, _, _)| u == &uri)
        .flat_map(|(_, ds, _)| ds.iter())
        .find(|d| d.message.contains(HINT))
        .cloned()
        .expect("hint diagnostic");
    assert_eq!(hint.severity, Some(DiagnosticSeverity::ERROR));
}

/// task-30（第 3 轮）：`NAT_LITERAL_ELAB_LIMIT` 的**解析期**边界必须是可诊断的，
/// 且阈值本身（100000）与 `nat_mul` 分解式都保持可用。
/// 注：这里只钉解析期决策——elaboration 的爆栈与否取决于**入口的栈预算**
/// （`typort check` 64→1024 MiB worker、`l13bench` 256 MiB），由 `src/bin/cli.rs`
/// 的入口对齐负责，不在本测试的栈上复现（测试线程栈小，跑大链会爆）。
#[test]
fn nat_literal_guard_boundary_is_diagnosable() {
    use elaboration_zoo_lsp::L13_namespace::parser::parser;

    let (decls, errs) = parser("def z: Nat = 100000", 0).expect("parse");
    assert!(errs.is_empty(), "100000 must stay usable, got {errs:?}");
    assert_eq!(decls.len(), 1);

    let (_d, errs) = parser("def z: Nat = 100001", 0).expect("parse");
    let msgs: Vec<String> = errs.iter().map(|e| format!("{:?}", e.msg.data)).collect();
    assert!(
        msgs.iter().any(|m| m.contains("exceeds the Nat literal elaboration limit 100000")),
        "100001 must be a diagnosable error, got {msgs:?}"
    );

    // 绕法（同阈值处）保持可用。
    let (_d, errs) = parser("def z: Nat = nat_mul 1000 1000", 0).expect("parse");
    assert!(errs.is_empty(), "nat_mul decomposition must parse, got {errs:?}");
}

/// The two worker-thread stack defaults must agree, and must be big enough for
/// the largest Nat literal the guardrail still allows.
///
/// This is a regression pin for a real bug (round 4 / (N)): `l13bench` defaulted
/// to a 256 MiB worker while the CLI defaulted to 1024 MiB, and that alone
/// decided whether an input survived.  On one binary `a*99999 + x*99998 + 5`
/// stack-overflowed at 256 MiB after 111.9s but completed at 1024 MiB in 13.3s
/// (`nf=600002`); `typort check` on the same probe was fine at 1024 MiB.
/// The shallow shape matrix consequently sat at AGREE 18 / TIMEOUT 1.
///
/// The pin is a source-level consistency check rather than a stack stress
/// test: a stress test would need a thread stack bigger than the harness
/// thread and would be slow and flaky.
#[test]
fn bench_and_cli_worker_stack_defaults_agree_and_clear_the_literal_guardrail() {
    fn default_stack_mb(path: &str, marker: &str) -> u32 {
        let src = std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("read {path}: {e}"));
        let at = src
            .find(marker)
            .unwrap_or_else(|| panic!("{path}: marker {marker:?} not found"));
        let tail = &src[at..];
        let kw = tail
            .find("unwrap_or(")
            .unwrap_or_else(|| panic!("{path}: no unwrap_or after {marker:?}"));
        let rest = &tail[kw + "unwrap_or(".len()..];
        let end = rest
            .find(')')
            .unwrap_or_else(|| panic!("{path}: unterminated unwrap_or"));
        rest[..end]
            .trim()
            .parse::<u32>()
            .unwrap_or_else(|e| panic!("{path}: default stack not a u32: {e}"))
    }

    let bench = default_stack_mb("src/bin/l13bench.rs", "let stack_mb: usize");
    let cli = default_stack_mb("src/bin/cli.rs", "let stack_mb: usize");

    assert_eq!(
        bench, cli,
        "l13bench and CLI worker stack defaults must stay in sync \
         (l13bench.rs vs cli.rs); they used to differ (256 vs 1024) and that \
         alone decided whether a deep Nat literal survived"
    );
    assert!(
        bench >= 1024,
        "both entry points must keep at least the calibrated 1024 MiB worker \
         stack (a*99999 + x*99998 + 5 overflows at 256), got {bench}"
    );
}
