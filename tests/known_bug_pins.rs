// 已知 bug 行为钉子（pin tests）。
//
// 本文件钉的是 2026-09-30（HEAD 09c78e9 基线）**实测**到的当前行为，不是文档
// 转述；每条钉子注释里写明实测结果与翻转条件。选题对应：
//
//   钉 1  parser Bug 1（docs/l13-known-bugs-2026-08.md Bug 1 /
//         docs/test-catalog.md G12-11）——已于 2026-09-29 修复（p_raw 宏展开
//         尾换行处理），catalog 里"先加钉锁现状、修复后翻转"的锚点缺口由此
//         补上：正向钉"宏 body `}` 后的末条声明不丢"。test(parser): 系列提交。
//   钉 2  GADT tuple 穷尽检查（docs/l13-gadt-exhaustive-bug-report.md）。
//   钉 3  typeclass 实例 Nat 参数位宽冻结的 HDL004 兜底
//         （docs/l13-typeclass-instance-nat-param-bug.md 复现 B，
//         docs/test-catalog.md G15-2）。
//   钉 4  eq-unify 复杂依赖匹配失败（docs/l13-eq-unify-failure.md）。
//
// 钉子语义（对齐 docs/test-catalog.md G12-10 的先例）：锁住实测现状，防止
// "顺手修掉/无声漂移"；行为变化时先翻转断言、再改行为。

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
/// 返回 (println INFORMATION 文本, 警告文本, 错误文本)。
fn analyze(src: &str, tag: &str) -> (Vec<String>, Vec<String>, Vec<String>) {
    let client = CapturingClient::default();
    let b = Backend::new(client);
    b.load_prelude();
    let uri = Url::parse(&format!("file:///{}.typort", tag)).unwrap();
    b.process_file(&uri, src, Some(1));
    let (mut infos, mut warns, mut errs) = (Vec::new(), Vec::new(), Vec::new());
    for (_, ds, _) in b.client.diagnostics.lock().unwrap().iter() {
        for d in ds {
            match d.severity {
                Some(DiagnosticSeverity::INFORMATION) => infos.push(d.message.clone()),
                Some(DiagnosticSeverity::WARNING) => warns.push(d.message.clone()),
                Some(DiagnosticSeverity::ERROR) | None => errs.push(d.message.clone()),
                _ => warns.push(format!("sev{:?}: {}", d.severity, d.message)),
            }
        }
    }
    (infos, warns, errs)
}

// ============================================================
// 钉 1 —— parser Bug 1 翻转（宏 body `}` 后的末条声明不丢）
// ============================================================
//
// docs/l13-known-bugs-2026-08.md Bug 1（test-catalog G12-11）：宏匹配器以
// `}` 字面量结尾（calc / when / switch / module）时吃掉身后的 EndLine，
// 文件**最后一条**声明被静默丢弃（只留 Expect(EndLine)，LSP 表现为
// "最后一行不工作"；典型案例 examples/theorem_proving.typort 末尾的
// println(subst_eg_calc)，当时靠补一条 println 绕过）。
//
// 实测（2026-09-30，commit 09c78e9 基线）：Bug 已随 2026-09-29 的 p_raw
// 尾换行修复关闭（known-bugs 文末追记）——下面三种 `}` 结尾宏 body 后、
// 作为文件末条声明的 println **全部存活**（INFORMATION 出现）且零错误
// （修复前这里是 Expect(EndLine) 解析错误 + println 被丢）。
//
// 翻转条件：无——这是正向回归钉。若哪条宏 body 的末条声明重新被丢/
// 报 Expect(EndLine)，本钉会红，说明 Bug 1 症状回归。
//
// 注：calc 形态即 Bug 1 文档的原始复现形状（theorem_proving.typort 的
// `def ... = calc { ... }` 后紧跟末条 println）；examples/theorem_proving.typort
// 末尾保留的"补偿 println"是文件级回归验证，本钉是套件级锚点。

const CALC_BODY_LAST_DECL: &str = r#"
def half_add_calc(a: Nat, b: Nat): Eq (a + b) (b + a) =
    calc {
        a + b = b + a by add_comm(a, b)
    }
println("calc-last-survives")
"#;

#[test]
fn bug1_pin_calc_body_trailing_decl_survives() {
    let (infos, warns, errs) = analyze(CALC_BODY_LAST_DECL, "bug1_calc");
    assert!(
        errs.is_empty(),
        "Bug 1 回归？calc body 后的末条声明应零错误存活（修复前是 Expect(EndLine) + 声明被丢），errs: {:?}",
        errs
    );
    assert!(
        infos.iter().any(|m| m.trim() == "calc-last-survives"),
        "Bug 1 回归？calc body 的末条 println 被静默丢弃，infos: {:?}",
        infos
    );
    assert!(warns.is_empty(), "unexpected warnings: {:?}", warns);
}

// switch 形态：module 内 switch body 以 `}` 结尾，module 自身的 `}` 之后
// 紧跟末条 println。
#[test]
fn bug1_pin_switch_body_trailing_decl_survives() {
    let (infos, warns, errs) = analyze(
        r#"
module switchMod
    input sel = UInt[4]
    input a = UInt[4]
    output result = UInt[4]
{
    switch sel {
        is 0 { result := a }
        default { result := 0 }
    }
}
println("switch-last-survives")
"#,
        "bug1_switch",
    );
    assert!(
        errs.is_empty(),
        "Bug 1 回归？switch body 后的末条声明应零错误存活，errs: {:?}",
        errs
    );
    assert!(
        infos.iter().any(|m| m.trim() == "switch-last-survives"),
        "Bug 1 回归？switch/module body 后的末条 println 被静默丢弃，infos: {:?}",
        infos
    );
    assert!(warns.is_empty(), "unexpected warnings: {:?}", warns);
}

// when 形态：module（花括号体，examples/hdl/08-control-flow.typort 的
// whenExample 原样形状）内 when/otherwise body 以 `}` 结尾，末条 println
// 紧跟 module `}` 之后。
#[test]
fn bug1_pin_when_body_trailing_decl_survives() {
    let (infos, warns, errs) = analyze(
        r#"
module whenExample {
    input a = UInt[8]
    input b = UInt[8]
    input sel = Bool
    output out = UInt[8]
    when sel {
        out := a
    } otherwise {
        out := b
    }
}
println("when-last-survives")
"#,
        "bug1_when",
    );
    assert!(
        errs.is_empty(),
        "Bug 1 回归？when body 后的末条声明应零错误存活，errs: {:?}",
        errs
    );
    assert!(
        infos.iter().any(|m| m.trim() == "when-last-survives"),
        "Bug 1 回归？when/module body 后的末条 println 被静默丢弃，infos: {:?}",
        infos
    );
    assert!(warns.is_empty(), "unexpected warnings: {:?}", warns);
}
