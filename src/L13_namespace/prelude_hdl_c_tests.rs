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
//   + `name not in scope: <模块名>`），**不带** HDV004，仍不可诊断（第 3 轮入册；
//   第 4 轮 (Q) 复测：formA 的 `MyTypo` 仍无 HDV004，见
//   `formA_mixed_port_table_is_diagnosed` 的对照矩阵）。
//   第 3 轮还登记过「formA 的混合端口表（`input sel = Boolean` + `output y = Bool`）
//   不匹配兜底臂 ⇒ 回到原有错误」。**第 4 轮 (Q) 复测推翻该登记**：混合表**已被诊断**
//   （CLI 口径 HDV004 精确指向出错行；lib 口径见下面的
//   `formA_mixed_port_table_is_diagnosed`）。原因是兜底臂的 `= Boolean` 组只要求
//   **Boolean 端口自身连续成 run**，其余标量端口由前面严格臂各取所需——臂选择
//   按整次调用，但组内重复片段是按 run 匹配的，所以混合形状仍有臂可落。
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

// ── (K) round-3：when 内只含 regAssignCd 时不得被主域与 Cd 域各发射一次 ──
// 根因：collectClockLinesCd 的 when 分支在主域一侧曾用 cd-agnostic 的
// hasRegAssign（同时接受 regAssign / regAssignCd / memWrite），于是「只含
// regAssignCd(cd2)」的 when 既进主域 clocked 块、又（经 hasRegAssignCd）进 cd2
// 块 ⇒ 同一赋值双发射 = 双驱动。
//
// 复现形状：`:=` 不会产生 regAssignCd（hdl-core 的 pickAssign 只建 regAssign，
// 不看信号自身时钟域），所以必须在 `when` 体内显式调 createSignalExpr(regAssignCd(...))
// ——与 hdl-crossclock.typort / hdl_check_graph_tests.rs 的构造方式一致。
// 该形状下 BEFORE 会额外出现主域块 `always @(posedge clk) begin if (en) begin
// r2 <= a; end end`，AFTER 只剩 cd2 块。
//
// NOTE（判据只钉这一点）：修后主域 `input wire clk` 端口**仍存在**——那是另一半
// 主域/额外域混淆（`moduleDefVLPlain` 的 `has_seq` 用 main+extras 合并后的
// `clocked` 字符串判空，见同文件 p1），属本轮未修的独立发现，故此处不断言端口。
#[test]
fn when_with_only_cd_assign_is_emitted_once() {
    let out = run_ok(
        r#"
module whenCdRepro {
    input en = Bool
    input a = UInt[8]
    output q = UInt[8]
    let cd2 = ClockDomain.mk "clk2" "rst2" Async RisingEdge ActiveHigh
    let r2 = newUIntRegInitCdNamed("r2", 8, 0, cd2)
    when en {
        let _ = createSignalExpr("r2", regAssignCd(r2.zz_expr, a.zz_expr, cd2))
    }
    q := r2
}
println(moduleTreeVL(whenCdRepro.create.tree))
"#,
    );
    assert_eq!(
        out.matches("r2 <= a;").count(),
        1,
        "the cd assignment must be emitted exactly once (twice = double drive):\n{out}"
    );
    assert_eq!(
        out.matches("always @(").count(),
        1,
        "only the cd2 clocked block may exist; the main block must not collect a \
         when holding only regAssignCd:\n{out}"
    );
    assert!(
        out.contains("always @(posedge clk2 or posedge rst2)"),
        "cd2 clocked block missing:\n{out}"
    );
}

// ── (Q) round-4：formA 混合端口表**已被诊断**（更正第 3 轮入册缺口） ──
// 第 3 轮把「formA 混合端口表（`Boolean` 与 `Bool` 同一张表）不可诊断」登记为已入册
// 缺口，理由是 `module` 宏按整次调用匹配、兜底臂要求所有标量端口都是 `Boolean`。
// **第 4 轮复测（CLI 探针 target/prelude_scratch/r4_Q_matrix.typort，6 个形状）：
// 全部报出 HDV004 且点名出错端口**——包括 Boolean 在前、Bool 在前、output 槽、
// 紧贴 body 花括号、与 `output reg` 混合这 5 种混合形状。⇒ 该入册缺口已不存在。
//
// 本测试在 lib 口径钉住这三件事：
//   ① 混合表仍然**响亮失败**（不静默变成 Bool 端口）——这是红线；
//   ② `Boolean` 单独成 run 的形状（第 3 轮原覆盖）同样失败；
//   ③ 顺序不影响结论（两种排列都钉）。
// HDV004 的文本/槽位/span 走 CLI 口径取证（同 X1 的做法）。
#[test]
fn formA_mixed_port_table_is_diagnosed() {
    // ① 混合表：Boolean 在前、Bool 在后（第 3 轮判定"不匹配"的那个形状）。
    assert_port_type_error(
        r#"
module mixA {
    input sel = Boolean
    input en = Bool
    output y = Bool
    input d = UInt[4]
    output q = UInt[4]
    q := d
}
println(moduleTreeVL(mixA.create.tree))
"#,
        "formA mixed Boolean-first",
    );
    // ② 混合表：Bool 在前、Boolean 在后。
    assert_port_type_error(
        r#"
module mixA2 {
    input en = Bool
    input sel = Boolean
    output y = Bool
    input d = UInt[4]
    output q = UInt[4]
    q := d
}
println(moduleTreeVL(mixA2.create.tree))
"#,
        "formA mixed Bool-first",
    );
    // ③ Boolean 紧贴 body 花括号（最后位置）。
    assert_port_type_error(
        r#"
module mixA3 {
    input en = Bool
    input d = UInt[4]
    output q = UInt[4]
    output y = Boolean
    q := d
}
println(moduleTreeVL(mixA3.create.tree))
"#,
        "formA mixed boolean-last",
    );
    // ④ 对照：纯 `Boolean` run（第 3 轮原覆盖的形状）仍失败，行为未变。
    assert_port_type_error(
        r#"
module mixA4 {
    input a = Boolean
    input b = Boolean
    {
    }
}
println(moduleTreeVL(mixA4.create.tree))
"#,
        "formA all-Boolean",
    );
}

// ── (J①) round-4：formB 通用方向臂不得误报合法端口类型 ──
// `Expr` 宏按**单条语句**匹配（$x: Expr 片段一次解析一条端口声明），所以通用
// `= $ty:ident` 臂只捕获出问题的那一条；合法臂（= Bool / Bits[w] / UInt[w] /
// SInt[w]）对各自语句仍然先命中。对比：`module` 宏按**整次调用**匹配，其标量组
// 会捕获所有标量端口（含合法 `= Bool`），所以 formA 保持窄臂、混合端口表留待
// 第 4 轮（见 hdl-macros 的注释）。
//
// 判据：CLI 侧 5 种类型混在同一 formB 模块里 ⇒ HDV004 恰好 1 条且点名 `MyTypo`
// （探针 target/prelude_scratch/r3_hdlc/cx_mix.typort，实测 1 条）。lib 口径只能
// 观察「合法端口不受影响」——本用例正是这一侧的守卫：若通用臂误命中合法形状，
// 模块会失败 ⇒ run_ok panic。
#[test]
fn formb_generic_arm_does_not_break_legal_port_types() {
    let out = run_ok(
        r#"
module cxLegal {
    input b = Bool
    input u = UInt[4]
    input s = Bits[4]
    input si = SInt[4]
    output y = Bool
    output uo = UInt[4]
    output so = Bits[4]
    output sio = SInt[4]
    y := b
    uo := u
    so := s
    sio := si
}
println(moduleTreeVL(cxLegal.create.tree))
"#,
    );
    for needle in [
        "input wire b,",
        "input wire [3:0] u,",
        "input wire [3:0] s,",
        "input wire signed [3:0] si,",
        "output wire y",
        "output wire [3:0] uo",
        "output wire [3:0] so",
        "output wire signed [3:0] sio",
    ] {
        assert!(out.contains(needle), "missing {needle}:\n{out}");
    }
}
