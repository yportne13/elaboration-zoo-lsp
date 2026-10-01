// ============================================================
// 裸构造器成员访问测试（docs/l13-quirks-analysis-2026-10.md §3.2）
//
// 裸（未应用）构造子做成员访问接收者：`lnil.show` / `None.and x`。
// `Raw::Var` 直查分支返回存表原样的泛型 Pi（`[T: Type 0] → List[T]`），
// 成员访问驱动必须对 Impl-Pi 头接收者补跑 insert（fresh_meta 隐式前缀）
// 才能进实例头桶；否则 head_key 对 Pi 恒 None，误报 "has no object"。
// 这些用例把该行为钉住：裸构造子分派 + 既有的显式应用形态不回归 +
// 真·缺成员仍然报错（含 Expl-Pi 函数接收者——insert 须对其无操作）。
// ============================================================

use super::*;

fn assert_output(input: &str, expected: &[&str]) {
    let output = match run_with_prelude(input) {
        Ok(output) => output,
        Err(e) => panic!(
            "expected OK, got error: '{}' @ {}:{}",
            e.0.data, e.0.path_id, e.0.start_offset
        ),
    };
    let lines: Vec<&str> = output
        .lines()
        .map(str::trim_end)
        .filter(|l| !l.is_empty())
        .collect();
    assert_eq!(lines, expected, "program output mismatch; raw: {:?}", output);
}

fn assert_err_contains(input: &str, needle: &str) {
    match run_with_prelude(input) {
        Ok(output) => panic!("expected error containing '{}', got OK: {}", needle, output.trim()),
        Err(e) => {
            assert!(
                e.0.data.contains(needle),
                "expected error containing '{}', got: '{}'",
                needle,
                e.0.data
            );
        }
    }
}

// ── 裸构造子 .show（trait 实例路径）──

#[test]
fn bare_ctor_show() {
    // 修复前："`lnil`: [T: Type 0] → List[T] has no object `show`"
    assert_output(
        r#"
def a: String = lnil.show
println a
println lnil.show
println None.show
"#,
        &["[]", "[]", "none"],
    );
}

// ── 既有形态不回归（显式应用 / 具体接收者）──

#[test]
fn applied_and_concrete_receivers_still_show() {
    assert_output(
        r#"
println lnil[Nat].show
println (lcons(1, lnil)).show
println (Some 6).show
"#,
        &["[]", "[1]", "some 6"],
    );
}

// ── 裸构造子 .and / .or_else（inherent impl 命名空间路径）──

#[test]
fn bare_ctor_inherent_method() {
    // `and`：接收者 None ⇒ 恒 None；`or_else`：None ⇒ 取 other。
    // 修复前："`None`: [T: Type 0] → Option[T] has no object `and`"
    assert_output(
        r#"
def o: Option[Nat] = None
println (o.and (Some 6)).show
println (None.and (Some 6)).show
println (None.or_else (Some 6)).show
println ((None.and (Some 6)).is_none).show
"#,
        &["none", "none", "some 6", "true"],
    );
}

// ── 裸构造子接收者 + 方法实参反定向 ?T ──

#[test]
fn bare_ctor_method_arg_pins_type_param() {
    assert_output(
        r#"
println (None.unwrap_or 9)
println ((Some 6).and None).show
"#,
        &["9", "none"],
    );
}

// ── 负例：真·缺成员仍报错；函数（Expl-Pi）接收者不受 insert 影响 ──

#[test]
fn genuinely_missing_member_still_errors() {
    assert_err_contains(
        "println lnil.nosuchmethod",
        "has no object",
    );
}

#[test]
fn function_receiver_missing_member_still_errors() {
    // Expl-Pi 头接收者：insert 不消费显式 Pi，须原样报 "has no object"
    // 而非把函数类型误当实例。
    assert_err_contains(
        r#"
def f(x: Nat): Nat = x
println f.nosuchmethod
"#,
        "has no object",
    );
}
