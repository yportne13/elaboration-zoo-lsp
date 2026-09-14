//! Verilog 语法兼容层回归测试（M1 骨架 + M2 表达式/控制流/代码生成补齐）。
//!
//! 覆盖 module 宏 Verilog 臂 + VExpr 语句表中**已确认可用**的能力：
//! M1 —— wire/reg 声明、assign、always @(posedge clk)、if/else begin 形
//! （when/otherwise 转写）、always @(*) 组合块、实例化方向判定、sized
//! 字面量、typort 风格模块不受 Verilog 臂前置影响，以及 Verilog/typort
//! 金样等价。
//! M2 —— 位选/部分选（含 LHS）、拼接（含嵌套与常量位宽保真）、归约
//! `& | ^`、case/endcase（default 标签）、纯组合模块不加多余 clk 端口、
//! 体内 `reg q = <init>` 与同名 output reg 端口去重。
//!
//! 已知限制（测试不覆盖；见 docs/verilog-compat.md「已知限制」）：
//! parameter 头 / generate / initial / 延迟 / $display；always 体内手写
//! 复位分支（复位值请用 `reg q = <init>;`）；带时钟域子模块的实例化
//! （折叠的 clk 不是普通端口）；头部 `output reg [w] q = <init>` 形式。

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
    // if/else begin 形 → when/otherwise。
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
    // 8'h2A 脱糖为 sized 字面量（带位宽输出）。
    let out = check_ok(r#"
module m(input [7:0] a, output [7:0] y);
    assign y = a + 8'h2A;
endmodule
println (moduleTreeVL(m.create.tree))
"#);
    assert!(out.contains("8'd42"), "sized literal should render 8'd42:\n{out}");
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

// ════════════════════════════════════════════════════════════════════
//  M2：表达式（位选 / 部分选 / 拼接 / 归约）
// ════════════════════════════════════════════════════════════════════

#[test]
fn m2_partsel_read() {
    assert_output_contains(r#"
module m(input [7:0] a, output [3:0] y);
    assign y = a[7:4];
endmodule
println (moduleTreeVL(m.create.tree))
"#, "assign y = a[7:4];");
}

#[test]
fn m2_partsel_write() {
    assert_output_contains(r#"
module m(input [7:0] a, output [7:0] y);
    assign y[3:0] = a[7:4];
endmodule
println (moduleTreeVL(m.create.tree))
"#, "assign y[3:0] = a[7:4];");
}

#[test]
fn m2_bitsel_read_write() {
    let out = check_ok(r#"
module m(input [7:0] a, output [7:0] y);
    assign y[0] = a[3];
endmodule
println (moduleTreeVL(m.create.tree))
"#);
    assert!(out.contains("assign y[0] = a[3];"), "bit-select read/write:\n{out}");
}

#[test]
fn m2_concat() {
    assert_output_contains(r#"
module m(input [3:0] a, input [3:0] b, output [7:0] y);
    assign y = {a, b};
endmodule
println (moduleTreeVL(m.create.tree))
"#, "assign y = {a, b};");
}

#[test]
fn m2_concat_nested_slices() {
    let out = check_ok(r#"
module m(input [7:0] a, output [7:0] y);
    assign y = {a[3:0], a[7:4]};
endmodule
println (moduleTreeVL(m.create.tree))
"#);
    assert!(out.contains("assign y = {a[3:0], a[7:4]};"), "nested concat:\n{out}");
}

#[test]
fn m2_concat_const_width_kept() {
    // IEEE 1364 禁止拼接内无位宽常量：4'h3 必须输出为 4'd3（保留 4 bit）。
    let out = check_ok(r#"
module m(input [3:0] b, output [7:0] y);
    assign y = {4'h3, b};
endmodule
println (moduleTreeVL(m.create.tree))
"#);
    assert!(out.contains("{4'd3, b}"), "sized constant must keep width:\n{out}");
}

#[test]
fn m2_reduction_ops() {
    let out = check_ok(r#"
module m(input [7:0] a, output p, output allOne, output anyOne);
    assign p = ^a;
    assign allOne = &a;
    assign anyOne = |a;
endmodule
println (moduleTreeVL(m.create.tree))
"#);
    for needle in ["assign p = ^a;", "assign allOne = &a;", "assign anyOne = |a;"] {
        assert!(out.contains(needle), "reduction {needle:?} missing:\n{out}");
    }
}

// ════════════════════════════════════════════════════════════════════
//  M2：控制流（case/endcase）与代码生成修正
// ════════════════════════════════════════════════════════════════════

#[test]
fn m2_case_comb_default() {
    // case/default → 互斥 when 链（标签经 CaseEq；default 恒真）。
    let out = check_ok(r#"
module m(input [1:0] a, output reg [7:0] y);
    always @(*) begin
        case (a)
            2'b00: y = 8'h01;
            2'b01: y = 8'h02;
            default: y = 8'hFF;
        endcase
    end
endmodule
println (moduleTreeVL(m.create.tree))
"#);
    assert!(out.contains("if (a == 2'd0)"), "case label 0:\n{out}");
    assert!(out.contains("!(a == 2'd0)"), "case negation:\n{out}");
    assert!(out.contains("y = 8'd255;"), "default body:\n{out}");
}

#[test]
fn m2_case_inside_clocked() {
    let out = check_ok(r#"
module m(input clk, input [1:0] a, output reg [7:0] q);
    reg [7:0] q = 0;
    always @(posedge clk) begin
        case (a)
            2'b00: q <= 8'h01;
            default: q <= q;
        endcase
    end
endmodule
println (moduleTreeVL(m.create.tree))
"#);
    assert!(out.contains("always @(posedge clk or posedge reset)"), "clocked case:\n{out}");
    assert!(out.contains("if (a == 2'd0)"), "case label in clocked body:\n{out}");
}

#[test]
fn m2_comb_module_has_no_spurious_clock() {
    // 纯组合模块（output reg + always @(*)）不应出现 clk/reset 端口。
    let out = check_ok(r#"
module m(input [7:0] a, input [7:0] b, output reg [7:0] y);
    always @(*) begin
        y = a & b;
    end
endmodule
println (moduleTreeVL(m.create.tree))
"#);
    assert!(!out.contains("input wire clk"), "combinational module must not get a clk port:\n{out}");
    assert!(!out.contains("input wire reset"), "combinational module must not get a reset port:\n{out}");
    assert!(out.contains("output reg [7:0] y"), "out-reg port kept:\n{out}");
}

#[test]
fn m2_reg_init_port_dedup() {
    // 体内 `reg q = 0;` 与同名 output reg 端口：单一声明 + 复位分支赋值。
    let out = check_ok(r#"
module m(input clk, input [7:0] d, output reg [7:0] q);
    reg [7:0] q = 0;
    always @(posedge clk) begin
        q <= d;
    end
endmodule
println (moduleTreeVL(m.create.tree))
"#);
    assert!(out.contains("output reg [7:0] q,"), "port declared as reg:\n{out}");
    // 不能同时出现独立的 `reg [7:0] q;`（那是非法重复声明）。
    assert!(!out.contains("  reg [7:0] q;"), "reg redeclaration must be dropped:\n{out}");
    assert!(out.contains("if (reset) begin"), "reset branch:\n{out}");
    assert!(out.contains("q <= 0;"), "init value in reset branch:\n{out}");
}

// ════════════════════════════════════════════════════════════════════
//  示例 24 端到端（M2 全量写法）
// ════════════════════════════════════════════════════════════════════

#[test]
fn m2_example24_end_to_end() {
    let out = check_ok(include_str!("../../examples/hdl/24-verilog-practice.typort"));
    for needle in [
        "module vByteSwap",
        "assign y = {w[7:0], w[15:8]};",
        "assign p = ^a;",
        "assign allOne = &a;",
        "assign anyOne = |a;",
        "if (op == 2'd0)",
        "y = {a[3:0], b[3:0]};",
        "y = {7'd0, ^a};",
        "q <= {q[6:0], d[0]};",
        "vByteSwap u_swap (.w(w), .y(sw));",
        "vAlu u_alu (.op(op), .a(a), .b(b), .y(al));",
    ] {
        assert!(out.contains(needle), "example 24 missing {needle:?}:\n{out}");
    }
}
