// ============================================================
// prelude HDL C tests (owner: hdl-c, task-5)
//
// 本模块钉住 hdl-utils / hdl-stream / hdl-fsm / hdl-macros /
// hdl-verilog-compat / hdl-verilog 的修补与关键约定。
// 高危文件（hdl-verilog / hdl-macros）的行为改动必须在这里留下
// 「生成了什么」的可断言痕迹（配合 tests/emit_tests.rs 的前后对照）。
//
// 覆盖：
//   - hdl-utils metaDiv 的整除档语义 + 已记录的 deviation（非整除时上取整）
//     与 core nat_div 的正确 floor 对照
//   - hdl-utils endiannessSwap 的组序方向（语义方向铁律：G1 契约内行为）
//   - hdl-stream 三个 streamCombStage 变体（streamCombStageBool 此前全仓零调用）
//   - hdl-macros blackbox 参数串（stub `parameter K = v` 头 + 实例 `#(.K(v))`）
//   - hdl-macros/hdl-verilog assertFatal 的 ERROR 标记行 + `$finish;`
//   - X1 已入册限制：端口类型必须写 `Bool`，`Boolean`（bool.typort 的真名）
//     不被 module 宏的标量端口组接受，失败是响亮的宏不展开
// ============================================================

use super::*;

fn run_ok(input: &str) -> String {
    match run_with_prelude(input) {
        Ok(output) => output,
        Err(e) => panic!(
            "expected OK, got error: '{}' @ {}:{}",
            e.0.data, e.0.path_id, e.0.start_offset
        ),
    }
}

/// Exact-line assertion for value-only probes (no HDL self-check warnings):
/// assert_output in prelude_stdlib_tests has the same shape.
fn assert_output(input: &str, expected: &[&str]) {
    let output = run_ok(input);
    let lines: Vec<&str> = output
        .lines()
        .map(str::trim_end)
        .filter(|l| !l.is_empty())
        .collect();
    assert_eq!(lines, expected, "program output mismatch; raw: {:?}", output);
}

/// Containment assertion for module probes: the emitted Verilog is a single
/// multi-line `println` payload, and containment keeps the test robust against
/// unrelated section additions while still pinning the exact statement text.
fn assert_contains(input: &str, needles: &[&str]) {
    let output = run_ok(input);
    for n in needles {
        assert!(
            output.contains(n),
            "expected emitted Verilog to contain {:?}\n--- raw ---\n{}",
            n,
            output
        );
    }
}

// ── hdl-utils metaDiv：整除档是 floor（G1 裁定 (a) 的契约内保证） ──

#[test]
fn meta_div_exact_division_is_floor() {
    assert_output(
        r#"
println (metaDiv 0 3)
println (metaDiv 6 3)
println (metaDiv 9 3)
println (metaDiv 16 8)
println (metaDiv 32 8)
println (metaDiv 5 0)
"#,
        &["0", "2", "3", "2", "4", "5"],
    );
}

// metaDiv 的 KNOWN DEVIATION 与正路 nat_div：
//   - 非整除时 metaDiv 上取整（ceil），文档已如实记录；
//   - core `nat_div` 是正确 floor，需要 floor 时用它。
// 这条测试同时钉住「文档与行为一致」：若将来有人把 metaDiv 改成 floor，
// 本测试会失败并要求同时更新 hdl-utils 的 `///`（deviation 段落）。
#[test]
fn meta_div_off_exact_deviation_and_nat_div_floor() {
    assert_output(
        r#"
// ceil（deviation）：1/3 -> 1（floor 应为 0）、7/3 -> 3（应为 2）、8/3 -> 3（应为 2）
println (metaDiv 1 3)
println (metaDiv 7 3)
println (metaDiv 8 3)
// nat_div 是正确 floor
println (nat_div 1 3)
println (nat_div 7 3)
println (nat_div 8 3)
"#,
        &["1", "3", "3", "0", "2", "2"],
    );
}

// ── hdl-utils endiannessSwap：组序方向（语义方向铁律） ──
// 结果 MSB 侧取源最低组：16 位 / base 8 -> {es[7:0], es[15:8]}；
// 24 位 -> 3 组；32 位 -> 4 组，均为「按 base 分组后整组倒序」。
// 这是 metaDiv 唯一调用方的契约内（width % base == 0）行为，G1 前后逐字节一致。

#[test]
fn endianness_swap_group_order_direction() {
    assert_contains(
        r#"
module esEx {
    input es16 = Bits[16]
    output sw16 = Bits[16]
    input es24 = Bits[24]
    output sw24 = Bits[24]
    input es32 = Bits[32]
    output sw32 = Bits[32]
    output swu16 = UInt[16]
    sw16 := endiannessSwap(es16, 8)
    sw24 := endiannessSwap(es24, 8)
    sw32 := endiannessSwap(es32, 8)
    swu16 := endiannessSwapUInt(es16.asUInt, 8)
}
println(moduleTreeVL(esEx.create.tree))
"#,
        &[
            "assign sw16 = {es16[7:0], es16[15:8]};",
            "assign sw24 = {es24[7:0], {es24[15:8], es24[23:16]}};",
            "assign sw32 = {es32[7:0], {es32[15:8], {es32[23:16], es32[31:24]}}};",
            "assign swu16 = {es16[7:0], es16[15:8]};",
        ],
    );
}

// ── hdl-stream streamCombStage：三个 payload 变体 ──
// 组合级 = 零寄存器：一个 `<bn>_ready` 线网，valid/payload 直通，
// input.ready 由该线网驱动（消费者再驱动它，例中为 down_ready 端口）。
// streamCombStageBool 的 payload 是无宽 Bool，此前全仓（prelude/examples/tests）
// 除定义行外零出现。

#[test]
fn stream_comb_stage_uint_bits_bool() {
    let src = r#"
module csU {
    input in_valid = Bool
    output in_ready = Bool
    input in_data = UInt[8]
    input down_ready = Bool
    output out_valid = Bool
    output out_data = UInt[8]
    let s = Stream.mk(in_valid, in_ready, in_data)
    let out = streamCombStageUInt(s)
    out_valid := out.valid
    out_data := out.payload
    out.ready := down_ready
}
module csB {
    input in_valid = Bool
    output in_ready = Bool
    input in_data = Bits[4]
    input down_ready = Bool
    output out_valid = Bool
    output out_data = Bits[4]
    let s = Stream.mk(in_valid, in_ready, in_data)
    let out = streamCombStageBits(s)
    out_valid := out.valid
    out_data := out.payload
    out.ready := down_ready
}
module csBool {
    input in_valid = Bool
    output in_ready = Bool
    input in_data = Bool
    input down_ready = Bool
    output out_valid = Bool
    output out_data = Bool
    let s = Stream.mk(in_valid, in_ready, in_data)
    let out = streamCombStageBool(s)
    out_valid := out.valid
    out_data := out.payload
    out.ready := down_ready
}
println(moduleTreeVL(csU.create.tree))
println(moduleTreeVL(csB.create.tree))
println(moduleTreeVL(csBool.create.tree))
"#;
    // 三个变体共用同一段直通接线；各自的端口名/线网名逐一钉住。
    assert_contains(
        src,
        &[
            "module csU (",
            "input wire [7:0] in_data,",
            "output wire [7:0] out_data",
            "  wire out_ready;",
            "  assign in_ready = out_ready;",
            "  assign out_valid = in_valid;",
            "  assign out_data = in_data;",
            "  assign out_ready = down_ready;",
            "module csB (",
            "input wire [3:0] in_data,",
            "module csBool (",
            "input wire in_data,",
            "output wire out_data",
        ],
    );
}

// ── hdl-macros blackbox：参数串两端 ──
// stub 头（SELF marker，hdl-verilog 纯字面拾取）：
//   `module PbRam #(parameter WIDTH = 8, parameter DEPTH = 16) (`
// 实例行（INSTANCE marker，紧跟 instance 节点）：
//   `PbRam #(.WIDTH(8), .DEPTH(16)) ram (.clk(clk), .addr(a), .din(d), .dout(q));`
// 泛型值来自黑盒**声明**（不是实例化点），由 bbParamsDeclStr/bbInstParamsStr
// 在 create 期渲染。

#[test]
fn blackbox_parameter_strings_stub_and_instance() {
    assert_contains(
        r#"
blackbox PbRam[depth: Nat, w: Nat]
    generic WIDTH = w
    generic DEPTH = depth
    input  clk  = Bool
    input  addr = UInt[log2Up depth]
    input  din  = UInt[w]
    output dout = UInt[w]
{
}
module pbWrap {
    input clk = Bool
    input a = UInt[4]
    input d = UInt[8]
    output q = UInt[8]
    let ram = PbRam.create[16, 8]
    ram.clk := clk
    ram.addr := a
    ram.din := d
    q := ram.dout
}
println(moduleTreeVL(PbRam.create[16, 8].tree))
println(moduleTreeVL(pbWrap.create.tree))
"#,
        &[
            "`ifndef TYPORT_BB_PbRam",
            "module PbRam #(parameter WIDTH = 8, parameter DEPTH = 16) (",
            "  output wire [7:0] dout",
            "`endif",
            "PbRam #(.WIDTH(8), .DEPTH(16)) ram (.clk(clk), .addr(a), .din(d), .dout(q));",
        ],
    );
}

// ── hdl-macros + hdl-verilog assertFatal：ERROR 标记 + $finish ──
// assertSevTag(AssertFatal) = "ERROR"（不是独立 tag），assertIsFatal 追加
// `$finish;`；整块被 synthesis translate_off 包裹。断言恒为时钟块，
// 所以纯组合模块也被合成出 `input wire clk`。

#[test]
fn assert_fatal_marker_and_finish() {
    assert_contains(
        r#"
module afEx {
    input en = Bool
    assertFatal(en, "fatal stop")
}
println(moduleTreeVL(afEx.create.tree))
"#,
        &[
            "input wire clk",
            "  // synthesis translate_off",
            "  always @(posedge clk) begin",
            "    if (!(en)) begin",
            "      $display(\"TYPORT_ASSERT_ERROR %0t %m: fatal stop\", $time);",
            "      $finish;",
        ],
    );
}

// ── X1：`input x = Boolean` → 可定位诊断 + 响亮失败；错拼类型仍响亮失败 ──
// `src/prelude/core/bool.typort:10` 的真名是 `enum Boolean`，而端口匹配是**字面
// token**。窄设计（第 2 轮定稿）只对**字面 token `Boolean`** 特化：
//   formB（端口在体内 `{ }`）走 `Expr` 宏的 `= Boolean` 臂（input/output/inout/
//     output reg 各一条）；
//   formA（端口在 body 前）走 `module` 宏末尾的 `= Boolean` 兜底臂。
// 两者都**不创建端口** + 引用未定义名 `__port_type_must_be_the_literal_Bool__`
// 让 class body 失败 ⇒ 模块无法 elaborate ⇒ 绝不会静默变成 Bool 端口。
//
// 通用 `= $ty:ident` 臂**已被否决**（实测）：宏臂按「整次调用」选择，一旦端口表里
// 有任一端口不是 `Bool`，`= Bool` 臂整臂失败，通用臂的重复组会把**所有**标量端口
// （含合法的 `x = Bool`）都捕获并逐条报警 ⇒ 会误报合法端口。因此：
//   `input a = MyTypo` 保持**原有**的响亮失败（`expected def, found identifier`
//   + `name not in scope: <模块名>`），**不带** HDV004，仍不可诊断（入册第 3 轮）。
//   同理 formA 的**混合**端口表（`input sel = Boolean` + `output y = Bool`）不匹配
//   `= Boolean` 兜底臂 ⇒ 回到原有错误（已入册的覆盖缺口）。
//
// 观测口径（2026-10-08 实测）：class body 里那条未定义名错误会被引擎的
// "declaration failed to elaborate" 路径**吞掉**（stdout 也为空），因此 CLI 上
// 用户实际看到的可定位诊断是 **HDV004 警告**，硬失败表现为下游
// `error: name not in scope: <模块名>`。故本测试在 lib 口径只能断言 `Err`
// （= 模块未 elaborate）；HDV004 的文本/槽位/span 由 CLI 探针取证（原文存档于
// target/prelude_scratch/t10_x1_*_v6.err.txt）：
//   `warning: [hdl][warning] HDV004 [Boolean] sel: \`Boolean\` is \`Bool\`'s
//    defining type name - write \`Bool\` ...`，span 指向 `input sel = Boolean` 的 `sel`。
// 若将来有人把端口匹配放宽成"任意类型都当 Bool"（= 静默错编译），这些负例
// 会变成 Ok ⇒ 立刻红，正是本测试要守的红线。

fn assert_port_type_error(input: &str, label: &str) {
    match run_with_prelude(input) {
        Ok(out) => panic!(
            "{label}: an unsupported scalar port type must NOT elaborate \
             (it would silently become a Bool port); got OK: {out:?}"
        ),
        Err(_) => { /* loud failure: the module declaration did not elaborate */ }
    }
}

#[test]
fn x1_boolean_port_spelling_is_rejected_loudly() {
    // 正例：`Bool` 在两种形式下都正常展开并生成端口。
    assert_contains(
        r#"
module plainPortB {
    input sel = Bool
    output y = Bool
    y := sel
}
println(moduleTreeVL(plainPortB.create.tree))
"#,
        &["module plainPortB (", "input wire sel,", "output wire y", "assign y = sel;"],
    );
    assert_contains(
        r#"
module plainPortA
    input sel = Bool
    output y = Bool
{
    y := sel
}
println(moduleTreeVL(plainPortA.create.tree))
"#,
        &["module plainPortA (", "input wire sel,", "output wire y", "assign y = sel;"],
    );

    // formB（端口在体内）：`Boolean` 与错拼都响亮失败。
    // NOTE: every negative input MUST reference the module afterwards — the
    // engine's recovery parsing drops a failed module decl silently (run_with_prelude
    // then returns Ok("")), so only the downstream `println(... .create ...)` turns
    // the failure into an observable `Err`.  It is also exactly the guard we want:
    // if the port ever silently became Bool, the module WOULD elaborate and the
    // Ok branch of assert_port_type_error fires.
    assert_port_type_error(
        r#"
module aliasB {
    input sel = Boolean
    output y = Bool
    y := sel
}
println(moduleTreeVL(aliasB.create.tree))
"#,
        "formB Boolean",
    );
    assert_port_type_error(
        r#"
module typoB {
    input sel = MyTypo
    output y = Bool
    y := sel
}
println(moduleTreeVL(typoB.create.tree))
"#,
        "formB MyTypo",
    );

    // formA（端口在 body 前）：同样两条。
    assert_port_type_error(
        r#"
module aliasA
    input sel = Boolean
    output y = Bool
{
    y := sel
}
println(moduleTreeVL(aliasA.create.tree))
"#,
        "formA Boolean",
    );
    assert_port_type_error(
        r#"
module typoA
    input sel = MyTypo
    output y = Bool
{
    y := sel
}
println(moduleTreeVL(typoA.create.tree))
"#,
        "formA MyTypo",
    );

    // `output reg q = <non-Bool>` 也走同一条兜底。
    assert_port_type_error(
        r#"
module outRegBad {
    output reg q = Boolean
}
println(moduleTreeVL(outRegBad.create.tree))
"#,
        "output reg Boolean",
    );
}

// ── 事故回归钉（2026-10 round-2）：prelude 期不得泄漏任何 HDV004 ──
// 事故机理（实测）：早期实现把 report_check_issue 放进一个 helper def，而
// prelude 装载期的「声明检查」会求值 def body（stuck 参数下也求值）——
// module 槽位是常量 ⇒ `HDV004|module||` 被写进装载期 mutable map；该 map 成为
// CACHED 状态，而 clone_prelude_state 只 reset WhenStack/ModuleTree/HdlLoopIdx/
// CombCtx/ModulePortTable，**不 reset CheckIssues** ⇒ 警告泄进每一次
// run_with_prelude 输出，calc_tests / bare_ctor_member_tests /
// cong_projection_tests / termination_check_tests / debug_test / prelude_* 整片红。
// 本用例的形状就是当时最先炸的 bare_ctor_show；任何「prelude 期 warning 泄漏」
// 都会在这里立刻现形。
#[test]
fn no_hdv004_leak_in_core_only_programs() {
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
