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

// ============================================================
// 钉 2 —— GADT tuple match 穷尽检查（docs/l13-gadt-exhaustive-bug-report.md）
// ============================================================
//
// 文档 bug：`match (l, x)`（l: Nat, x: Vec[Boolean] l）两臂 (zero,nil)/
// (succ,cons) 已被 GADT 约束证明完备，旧实现仍报 non-exhaustive
// （"non-exhaustive pattern: `Tuple2.mk(zero, cons)` not covered" 等——
// 第一个 head 的索引约束不传播到第二个 head，`filter_accessible_constrs`
// 看到的仍是未约束的 Vec[Boolean] l）。
//
// 实测（2026-09-30，commit 09c78e9 基线，LSP Backend 路径）：
//   1. 文档最小复现**已不复现**——零错误零警告，两臂求值正确
//      （test(nil) = true、test(cons(true, nil)) = false；
//      src/L13_namespace/legacy_tests.rs::test_pm_vec_bool_exhaustive 在
//      run_with_prelude 路径同样通过）。
//   2. 对照组证明检查器仍然活跃且 GADT 过滤生效：只留 (zero, nil) 一臂的
//      真·不完整 match 报 "match 不完整：模式位置 Tuple2.mk#1 缺少构造子
//      succ"——**只**缺 succ 侧（(zero, cons) 因 x: Vec[Boolean] zero 不可能
//      是 cons 而被正确过滤，不再像旧 bug 那样把不可达组合报成缺口）。
//
// 翻转条件：若文档 bug 复发（完备 match 重新报 non-exhaustive），测试 1 转红。
// 注意 println 的输出形态是 2026-09-30 的 pretty 形态（枚举限定名
// Boolean::true/false）；pretty 显示格式漂移时按显示锚点流程翻转文案，
// 不算 bug 回归。

#[test]
fn gadt_pin_tuple_match_doc_repro_is_exhaustive() {
    let (infos, warns, errs) = analyze(
        r#"
def test[l: Nat](x: Vec[Boolean] l): Boolean = match (l, x) {
    case (zero, nil) => true
    case (succ(m), cons(_, _)) => false
}
println(test(nil))
println(test(cons(true, nil)))
"#,
        "gadt_doc_repro",
    );
    assert!(
        errs.is_empty(),
        "GADT tuple 穷尽 bug 复发？文档最小复现 (zero,nil)/(succ,cons) 完备 match 被报错误，errs: {:?}",
        errs
    );
    assert!(warns.is_empty(), "unexpected warnings: {:?}", warns);
    assert_eq!(
        infos,
        vec!["Boolean::true".to_string(), "Boolean::false".to_string()],
        "两臂求值结果漂移（true 臂=zero/nil，false 臂=succ/cons），infos: {:?}",
        infos
    );
}

#[test]
fn gadt_pin_exhaustiveness_checker_still_active_control() {
    let (infos, _warns, errs) = analyze(
        r#"
def bad[l: Nat](x: Vec[Boolean] l): Boolean = match (l, x) {
    case (zero, nil) => true
}
println("never")
"#,
        "gadt_control",
    );
    assert!(
        errs.iter().any(|e| e.contains("match 不完整")),
        "穷尽检查器失效漂移？（zero, nil) 单臂 match 应报 match 不完整，errs: {:?}",
        errs
    );
    assert!(
        errs.iter().any(|e| e.contains("Tuple2.mk#1 缺少构造子 succ")),
        "缺口形态漂移？应只报第一 head 缺 succ（(zero, cons) 由 GADT 约束过滤、不得误报），errs: {:?}",
        errs
    );
    assert!(
        !infos.is_empty(),
        "解析恢复后 println 应存活（末条声明不丢，见钉 1），infos: {:?}",
        infos
    );
}

// ============================================================
// 钉 3 —— typeclass 实例 Nat 参数位宽冻结的 HDL004 兜底警告
//          （docs/l13-typeclass-instance-nat-param-bug.md 复现 B / test-catalog G15-2）
// ============================================================
//
// 文档 bug：`impl[w: Nat] Foo[UInt[w]] for UInt[w]` 形状的实例（prelude 里
// 即 `impl[w: Nat] RegNext[UInt[w]] for UInt[w]`）在参数化 module 里被使用
// 时，实例的 Nat 参数 w 到达消费点仍是冻结的 elaboration 变量，width_range
// 数出 0/1 → **静默**生成无位宽（1 位）硬件。现有兜底 = HDL004 显式警告
// （hdl-check.typort ruleWidthGround + Rust native nat_is_ground）。
//
// 实测（2026-09-30，09c78e9 基线，LSP Backend 路径）：
//  - 参数化 module + regNext 且模块内存在至少一个 ground 位宽信号时，
//    HDL004 对 regNext 产物 d（以及同为非 ground 的端口 a/y）出现，
//    文案含 "width is not a ground number"。
//  - 门控（hdl-check.typort ruleWidthGround 注释）：**全模块无任何 ground
//    位宽**的纯参数化 module（文档 B1 原样）保持静默——该形态被当作
//    Phase-A 一次性树丢弃；因此本钉在 B1 形状上加一个 ground 位宽信号
//    把门打开。
//  - 对照：固定宽度 module + regNext 零警告（位宽正确路径不受扰）。
//
// 翻转条件：复现 B 根治（meta 解支持消费点参数化）后，此钉按任务口径
// 翻转为 "无 HDL004 且 reg 位宽正确"；端口类非 ground 宽度若届时仍按
// 门控规则报告，以实测为准缩小断言范围。

#[test]
fn hdl004_pin_frozen_width_in_param_module_warns() {
    let (infos, warns, errs) = analyze(
        r#"
module p4[w: Nat]
    input a = UInt[w]
    output y = UInt[w]
{
    let fix = UInt[8]
    let d = regNext(a)
    y := d
}
"#,
        "hdl004_pin",
    );
    assert!(
        errs.is_empty(),
        "参数化 module + regNext 应能通过 elaboration（报错即另一形态的回归），errs: {:?}",
        errs
    );
    assert!(
        warns.iter().any(|w| w.contains("HDL004") && w.contains("[p4] d")),
        "HDL004 兜底消失？regNext 产物 d 的位宽冻结警告未出现（根治后按注释翻转此钉），warns: {:?}",
        warns
    );
}

#[test]
fn hdl004_pin_fixed_width_control_stays_clean() {
    let (infos, warns, errs) = analyze(
        r#"
module fixedReg
    input a = UInt[8]
    output y = UInt[8]
{
    let d = regNext(a)
    y := d
}
"#,
        "hdl004_fixed_control",
    );
    assert!(errs.is_empty(), "errs: {:?}", errs);
    assert!(
        !warns.iter().any(|w| w.contains("HDL004")),
        "固定宽度 module 不应报 HDL004（位宽冻结是参数化实例特有），warns: {:?}",
        warns
    );
}
