//! Verilog 语法兼容层（M1 核心子集）回归测试。
//!
//! 覆盖 module 宏 Verilog 臂 + VExpr 语句表中**已确认可用**的能力：
//! wire/reg 声明、assign、always @(posedge clk)、if/else begin 形
//! （when/otherwise 转写）、实例化方向判定、typort 风格模块不受
//! Verilog 臂前置影响；以及 Verilog/typort 金样等价。
//!
//! 已知 M1 缺口（测试不覆盖，见 docs/verilog-compat.md 与
//! hdl-verilog-compat.typort 注释）：
//! - `==`/`!=` 别名：VEq trait 已定义但 method resolution 未命中
//!   （`a === b` 同样退化），if 条件里的 `d == 255` 输出原样 `==`
//! - `always @(posedge clk or negedge rst_n)`：复位仅折叠时钟域，
//!   复位体不生成复位分支；vCounter 输出缺 reset 端口
//! - `assign` 位选/部分选 LHS、`reg q = init` 的 Nat 初值统一
//! - `always @(*)/@*` 组合块

use super::*;

fn check_ok(input: &str) -> String {
    match run_with_prelude(input) {
        Ok(o) => o,
        Err(e) => panic!("expected OK, got error: '{}' @ {}:{}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

fn assert_output_contains(input: &str, needle: &str) {
    let out = check_ok(input);
    assert!(out.contains(needle),
        "expected output containing {:?}, got:\n{}", needle, out);
}

// ── module Verilog 臂：ANSI 头 + begin/end 语句 ──────────────────────

#[test]
fn compat_wire_assign_decl() {
    assert_output_contains(r#"
module m(input [7:0] a, output [7:0] y);
    wire [7:0] w;
    assign y = w;
endmodule
println (moduleTreeVL(m.create.tree))
"#, "assign y = w");
}

#[test]
fn compat_reg_decl() {
    // 无初值 reg：`reg [7:0] q;` → 时序保存（q <= 驱动）。
    assert_output_contains(r#"
module m(input clk, input [7:0] d, output reg [7:0] q);
    reg [7:0] q;
    always @(posedge clk) begin
        q <= d;
    end
endmodule
println (moduleTreeVL(m.create.tree))
"#, "reg [7:0] q");
}

#[test]
fn compat_always_clk() {
    // `always @(posedge clk)` 内的 reg 赋值 → 时钟沿 regAssign。
    assert_output_contains(r#"
module m(input clk, input [7:0] d, output reg [7:0] q);
    always @(posedge clk) begin
        q <= d;
    end
endmodule
println (moduleTreeVL(m.create.tree))
"#, "always @(posedge clk)");
}

#[test]
fn compat_if_else() {
    // if/else begin 形 → when/otherwise；条件原样输出（== 别名未通——
    // 已知 M1 缺口，此处断言 when 结构而非操作符）。
    let out = check_ok(r#"
module m(input clk, input [7:0] d, output reg [7:0] q);
    always @(posedge clk) begin
        if (d == 0)
            q <= d;
        else
            q <= 0;
    end
endmodule
println (moduleTreeVL(m.create.tree))
"#);
    assert!(out.contains("if (d == 0)"), "if branch missing:\n{out}");
}

#[test]
fn compat_instance_named_ports() {
    // 子模块实例化 `vSub u1 (.x(a), .y(w));` → create + conn 方向判定。
    assert_output_contains(r#"
module vSub(input [7:0] x, output [7:0] y);
    assign y = x;
endmodule
module vTop(input [7:0] a, output [7:0] b);
    wire [7:0] w;
    vSub u1 (.x(a), .y(w));
    assign b = w;
endmodule
println (moduleTreeVL(vTop.create.tree))
"#, "vSub u1 (");
}

#[test]
fn compat_sized_literal() {
    // 8'h2A 脱糖为数值（exprVL 以十进制渲染字面量）。
    let out = check_ok(r#"
module m(input [7:0] a, output [7:0] y);
    assign y = a + 8'h2A;
endmodule
println (moduleTreeVL(m.create.tree))
"#);
    assert!(out.contains("42"), "sized literal should desugar to 42:\n{out}");
}

#[test]
fn compat_typort_module_still_works() {
    // Verilog 臂前置不影响 typort 风格模块。
    assert_output_contains(r#"
module solo {
    let a = UInt[8]
    let b = UInt[8]
    let s = UInt[8]
    s := a + b
}
println (moduleTreeVL(solo.create.tree))
"#, "assign s = (a + b)");
}

// ── 金样等价：Verilog 写法 vs typort 写法逐字节一致 ─────────────────

#[test]
fn compat_golden_add8() {
    // 两写法输出除模块名外逐字节一致（模块名不同必然体现在输出上，
    // 归一化后比较）。
    let v = check_ok(r#"
module vAdd8(input [7:0] a, input [7:0] b, output [7:0] s);
    assign s = a + b;
endmodule
println (moduleTreeVL(vAdd8.create.tree))
"#);
    let t = check_ok(r#"
module tAdd8 {
    input a = UInt[8]
    input b = UInt[8]
    output s = UInt[8]
    s := a + b
}
println (moduleTreeVL(tAdd8.create.tree))
"#);
    let norm = |s: String| s.replace("vAdd8", "X").replace("tAdd8", "X");
    assert_eq!(norm(v), norm(t), "Verilog 与 typort 写法的金样输出不一致");
}
