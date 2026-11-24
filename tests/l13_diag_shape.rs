//! L13 诊断形状钉子（2026-11-24，UPGRADE-L13-PLAN.md P1 + P3）。
//!
//! 背景：L13 顶层"缺失模式"诊断曾是 L10–L12 遗留的形态——把见证做成
//! `Pattern::Con(ctor, [Any; 999])`，Display 出来是**单行 3000+ 字符、约 2005 个
//! `_`** 的消息（用户不可读，见 docs/compare-l07-l13-shared/FINAL.md §4 #7）。
//! 本轮改成只带构造子名、文案对齐 L12/L07 的 "match 不完整：缺少构造子 {ctor}"。
//!
//! 本文件把这个形状钉死：文案变短、单行、包含构造子名；不要退回定长通配见证。

use elaboration_zoo_lsp::L13_namespace::run;

fn message_of(src: &str) -> String {
    match run(src, 0) {
        Ok(out) => panic!("expected a non-exhaustive diagnostic, got Ok:\n{out}"),
        Err(e) => e.0.data.to_string(),
    }
}

#[test]
fn missing_ctor_diagnostic_is_short_and_names_the_ctor() {
    let src = "enum Nat {\n  zero\n  succ(x: Nat)\n}\n\
               def mono(n: Nat): Nat = match n { case zero => zero }\n";
    let msg = message_of(src);
    assert!(msg.contains("succ"), "diagnostic should name the missing ctor, got: {msg}");
    assert!(
        msg.chars().count() < 200,
        "missing-ctor diagnostic regressed to a long witness pattern ({} chars): {msg}",
        msg.chars().count()
    );
    assert!(!msg.contains("_,"), "diagnostic must not contain a filler wildcard chain: {msg}");
    assert!(!msg.contains('\n'), "diagnostic must be a single line: {msg:?}");
}

#[test]
fn missing_ctor_diagnostic_uses_layer_neutral_wording() {
    // 与 L12/L07 的 "match 不完整：缺少构造子" 同口径（两边都接受英文遗留写法，
    // 但**必须**包含构造子名，否则说明见证被换成了别的东西）。
    let src = "enum Color {\n  red\n  green\n}\n\
               def pick(c: Color): Color = match c { case red => red }\n";
    let msg = message_of(src);
    assert!(msg.contains("green"), "diagnostic should name the missing ctor, got: {msg}");
    assert!(msg.chars().count() < 200, "diagnostic too long ({} chars): {msg}", msg.chars().count());
}
