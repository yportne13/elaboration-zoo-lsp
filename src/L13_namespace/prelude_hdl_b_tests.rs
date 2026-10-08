// ============================================================
// prelude HDL B tests (owner: hdl-b, task-4)
//
// 本模块钉住 hdl-clock / hdl-bus / hdl-bus-proto / hdl-signals /
// hdl-crossclock / hdl-enum / hdl-misc / hdl-misc-io 的修补与关键约定
// （时钟域、握手、宽度约定）。
// 写法参照 hdl_enum_tests.rs / hdl_blackbox_tests.rs：run_with_prelude +
// 逐条断言生成的 Verilog 结构。
//
// 覆盖的修补（task-4）：
//   P1 counterInc.willOverflow 由 enable 门控（hdl-signals）
//   P2 AxiLite4 方向函数 axiLite4AsMaster/AsSlave（hdl-bus-proto，additive）
//   P3 gpioCtrl 采样寄存器 + 上升沿粘滞中断（hdl-misc-io）
//   P4 Plru 树遍历 evict / 反向置位 update（hdl-misc）
//   P5 MemOps.readSyncCCD 真跨域读（hdl-clock）
//   G1 streamFifoCC 指针 wrap 位（hdl-crossclock）：full/empty 可区分
//   G1b when+Cd 赋值双域发射（hdl-crossclock）：rdPtr/toggle/buffer 单驱动
// ============================================================

use super::*;

fn assert_ok(input: &str) -> String {
    match run_with_prelude(input) {
        Ok(output) => output,
        Err(e) => panic!(
            "expected OK, got error: '{}' @ {}:{}",
            e.0.data, e.0.path_id, e.0.start_offset
        ),
    }
}

// ── P1: counterInc 的 willOverflow 必须被 enable 门控 ──
// 同 prelude 的 counterIncMod（hdl-utils）口径：willOverflow = inc && value==end。
// 自由运行 counter 不受影响（仍为 ~value == 0）。

#[test]
fn hdl_b_counter_inc_willoverflow_is_enable_gated() {
    let output = assert_ok(r#"
module bCounterInc {
    input en = Bool
    output ovf = Bool
    output val = UInt[4]
    let c = counterInc(4, en)
    ovf := c.willOverflow
    val := c.value
}
module bCounterFree {
    output ovf = Bool
    output val = UInt[4]
    let c = counter(4)
    ovf := c.willOverflow
    val := c.value
}
println(moduleTreeVL(bCounterInc.create.tree))
println(moduleTreeVL(bCounterFree.create.tree))
"#);
    // counterInc: 计数在 when(en) 内，溢出标志与 enable 相与
    assert!(
        output.contains("if (en) begin"),
        "counterInc increment must stay enable-gated, got:\n{}",
        output
    );
    assert!(
        output.contains("(en && (~c == 0))"),
        "counterInc willOverflow must be enable-gated, got:\n{}",
        output
    );
    // 自由运行 counter 保持不加门控（对照）
    assert!(
        output.contains("(~c == 0)"),
        "counter willOverflow must remain ungated, got:\n{}",
        output
    );
    assert!(
        !output.contains("&& (~c == 0)") || output.contains("(en && (~c == 0))"),
        "unexpected counter overflow form"
    );
}

// ── P5: MemOps.readSyncCCD —— 读寄存器挂在目标时钟域 ──
// 与 hdl-crossclock.readSyncCCUInt 同形：createRegWidthCd + regAssignCd，
// 生成第二个 always 块与额外 clk 端口；写端口仍在主时钟。

#[test]
fn hdl_b_mem_read_sync_ccd_uses_out_domain() {
    let output = assert_ok(r#"
def bCdA: ClockDomain = ClockDomain.mk "clk_a" "rst_a" Async RisingEdge ActiveHigh
def bCdB: ClockDomain = ClockDomain.mk "clk_b" "rst_b" Async RisingEdge ActiveHigh

module bMemCcd[bCd] {
    input addr = UInt[3]
    input wdata = UInt[8]
    input we = Bool
    output rd = UInt[8]
    let ram = memUInt(8, 8)
    ram.write(addr, wdata, we)
    let r = ram.readSyncCCD(addr, bCdB)
    rd := r
}
println(moduleTreeVL(bMemCcd.create[bCdA].tree))
"#);
    assert!(
        output.contains("reg [7:0] r;"),
        "readSyncCCD must create the read register, got:\n{}",
        output
    );
    // 读寄存器在 cdB 的 always 块里
    assert!(
        output.contains("always @(posedge clk_b"),
        "readSyncCCD must emit an always block for the out domain, got:\n{}",
        output
    );
    assert!(
        output.contains("input wire clk_b"),
        "readSyncCCD must add the out domain's clk port, got:\n{}",
        output
    );
    assert!(
        output.contains("r <= ram[addr];"),
        "readSyncCCD must sample memRead in the out domain, got:\n{}",
        output
    );
    // 写端口仍在主时钟（clk_a / 模块默认域）
    assert!(
        output.contains("always @(posedge clk_a"),
        "write port must stay in the main clock, got:\n{}",
        output
    );
}

// ── P2: AxiLite4 方向函数（master/slave 视角）──
// master: aw/w/ar 的 valid+payload 为输出、ready 为输入；b/r 的 valid+payload
// 为输入、ready 为输出。slave 完全翻转。

#[test]
fn hdl_b_axilite4_direction_helpers() {
    let output = assert_ok(r#"
module bAxiLiteMaster {
    input aw_v = Bool
    input aw_r = Bool
    input aw_addr = UInt[32]
    input aw_prot = Bits[3]
    input w_v = Bool
    input w_r = Bool
    input w_data = Bits[32]
    input w_strb = Bits[4]
    input b_v = Bool
    input b_r = Bool
    input b_resp = Bits[2]
    input ar_v = Bool
    input ar_r = Bool
    input ar_addr = UInt[32]
    input ar_prot = Bits[3]
    input r_v = Bool
    input r_r = Bool
    input r_data = Bits[32]
    input r_resp = Bits[2]
    let bus = AxiLite4.mk(
        Stream.mk(aw_v, aw_r, AxiLite4Ax.mk(aw_addr, aw_prot)),
        Stream.mk(w_v, w_r, AxiLite4W.mk(w_data, w_strb)),
        Stream.mk(b_v, b_r, AxiLite4B.mk(b_resp)),
        Stream.mk(ar_v, ar_r, AxiLite4Ax.mk(ar_addr, ar_prot)),
        Stream.mk(r_v, r_r, AxiLite4R.mk(r_data, r_resp)))
    let m = axiLite4AsMaster(bus)
    let _keep = m.aw.valid
    let _keep2 = m.r.ready
}
println(moduleTreeVL(bAxiLiteMaster.create.tree))
"#);
    // 读地址通道（master 驱动）：valid/payload 输出、ready 输入
    assert!(
        output.contains("output wire ar_v"),
        "master must drive ar.valid, got:\n{}",
        output
    );
    assert!(
        output.contains("input wire ar_r"),
        "master must sample ar.ready, got:\n{}",
        output
    );
    assert!(
        output.contains("output wire [31:0] ar_addr"),
        "master must drive ar payload, got:\n{}",
        output
    );
    // 写响应通道（slave 驱动）：valid/payload 输入、ready 输出
    assert!(
        output.contains("input wire b_v"),
        "master must sample b.valid, got:\n{}",
        output
    );
    assert!(
        output.contains("output wire b_r"),
        "master must drive b.ready, got:\n{}",
        output
    );
    assert!(
        output.contains("input wire [1:0] b_resp"),
        "master must sample b payload, got:\n{}",
        output
    );
    // 读数据通道
    assert!(
        output.contains("input wire r_v") && output.contains("output wire r_r"),
        "master r-channel directions, got:\n{}",
        output
    );
}

// ── P3: gpioCtrl 采样寄存器 + 上升沿粘滞中断 ──
// 字段注释承诺 input 是"采样后的输入（寄存器）"、函数注释承诺边沿检测；
// 实现改为：采样寄存器 + (pend | rise) & ~clear 的粘滞挂起。

#[test]
fn hdl_b_gpio_ctrl_samples_and_latches_edges() {
    let output = assert_ok(r#"
module bGpio {
    input pinRead = Bits[4]
    input clr = Bits[4]
    input g_out = Bits[4]
    input g_oe = Bits[4]
    output pinWrite = Bits[4]
    output pinWE = Bits[4]
    output sampled = Bits[4]
    output irq = Bits[4]
    let io = GpioIO.mk(pinRead, pinWrite, pinWE, newBitsNamed("b_g_in", 4), g_out, g_oe, newBitsNamed("b_g_int", 4))
    let _d = gpioCtrl(io, clr)
    sampled := io.input
    irq := io.interrupts
}
println(moduleTreeVL(bGpio.create.tree))
"#);
    // 采样寄存器 + 挂起寄存器
    assert!(
        output.contains("reg [3:0] _d_input;"),
        "gpioCtrl must sample pin_read into a register, got:\n{}",
        output
    );
    assert!(
        output.contains("reg [3:0] _d_pend;"),
        "gpioCtrl must keep a sticky pending register, got:\n{}",
        output
    );
    // 上升沿：pinRead & ~采样值
    assert!(
        output.contains("(pinRead & ~_d_input)"),
        "gpioCtrl must detect a rising edge, got:\n{}",
        output
    );
    // 粘滞 + clear 清零
    assert!(
        output.contains("((_d_pend | (pinRead & ~_d_input)) & ~clr)"),
        "gpioCtrl pending must be sticky and cleared by clearInterrupt, got:\n{}",
        output
    );
    // 旧的电平直通实现必须消失
    assert!(
        !output.contains("assign irq = (pinRead & ~clr);"),
        "level-only interrupt implementation must be gone, got:\n{}",
        output
    );
}

// ── P4: Plru 树遍历 evict / 反向置位 update ──
// 状态布局：way 数 2^log2n，state 宽 2^log2n-1，节点 k 的子为 2k+1/2k+2。
// log2n=2 时 evict 读 st[0]，再按 st[0] 读 st[1] 或 st[2]。

#[test]
fn hdl_b_plru_evict_walks_the_tree() {
    let output = assert_ok(r#"
module bPlru {
    input st = UInt[3]
    input way = UInt[2]
    output victim = UInt[3]
    output nextSt = UInt[3]
    victim := plruEvict(st, 2)
    nextSt := plruUpdate(st, way, 2)
}
println(moduleTreeVL(bPlru.create.tree))
"#);
    // 逐层读取状态位：至少两处动态位选（根 + 子节点）
    assert!(
        output.matches("st[").count() >= 2,
        "plruEvict must read one state bit per level, got:\n{}",
        output
    );
    // 旧的"state & mask"简化实现必须消失（log2n=2 → 旧式为 (st >> 0) & 3）
    assert!(
        !output.contains("& 3)"),
        "old mask-based plruEvict must be gone, got:\n{}",
        output
    );
    // update：清位掩码取反 + 置位掩码或起来，含动态左移
    assert!(
        output.contains("(1 <<"),
        "plruUpdate must set path bits with a dynamic shift, got:\n{}",
        output
    );
    assert!(
        output.contains("~("),
        "plruUpdate must clear the opposite path bits, got:\n{}",
        output
    );
}

// ── 时钟域/握手约定钉子：Stream.fire 与 Flow ──

#[test]
fn hdl_b_stream_fire_and_stage_contract() {
    let output = assert_ok(r#"
module bStreamFire {
    input v = Bool
    input r = Bool
    output f = Bool
    let s = Stream.mk(v, r, newUIntNamed("s_payload", 4))
    f := s.fire
}
println(moduleTreeVL(bStreamFire.create.tree))
"#);
    // fire = valid && ready（SpinalHDL 握手语义）
    assert!(
        output.contains("(v && r)"),
        "Stream.fire must be valid && ready, got:\n{}",
        output
    );
}

// ── Apb3RegBank 的读写相位与 when 顺序（文档承诺的结构）──
// 写：PENABLE && PSEL[0] && PWRITE && PADDR==addr → 时钟赋值 reg <= PWDATA；
// 读：PSEL[0] && !PWRITE && PADDR==addr → 组合 PRDATA = reg；
// readDefault 最后调用 → 它的 when 块排在后面（always @(*) 后写覆盖），
// 未命中地址读回 0。

#[test]
fn hdl_b_apb3_reg_bank_phase_and_priority() {
    let output = assert_ok(r#"
module bApb3Bank {
    output r0v = UInt[32]
    let bus = Apb3.mk(newUIntNamed("PADDR", 32), newBitsNamed("PSEL", 1), newBoolNamed("PENABLE"),
                      newBoolNamed("PREADY"), newBoolNamed("PWRITE"), newBitsNamed("PWDATA", 32),
                      newBitsNamed("PRDATA", 32), newBoolNamed("PSLVERROR"))
    let sbus = apb3AsSlave(bus)
    sbus.PREADY := true
    sbus.PSLVERROR := false
    let r0 = newUIntRegNamed("r0", 32)
    let bank = Apb3RegBank.mk(sbus)
    let _d = bank.regReadWrite(0, r0)
    let _d2 = bank.readDefault()
    r0v := r0
}
println(moduleTreeVL(bApb3Bank.create.tree))
"#);
    // 写：PENABLE 门控的时钟赋值
    assert!(
        output.contains("if ((PENABLE && (PSEL[0] && PWRITE)) && (PADDR == 0)) begin"),
        "APB3 write must gate on the access phase, got:\n{}",
        output
    );
    assert!(
        output.contains("r0 <= PWDATA;"),
        "APB3 write must be a clocked reg <= PWDATA, got:\n{}",
        output
    );
    // 读：组合赋值（无 PENABLE 门控，setup 相位即可读）
    assert!(
        output.contains("PRDATA = r0;"),
        "APB3 read must drive PRDATA combinationally, got:\n{}",
        output
    );
    assert!(
        output.contains("PRDATA = 0;"),
        "readDefault must drive PRDATA = 0, got:\n{}",
        output
    );
    // 顺序：readDefault 最后调用 ⇒ 其赋值排在 regReadWrite 的读之后（后写覆盖）
    let i_reg = output.find("PRDATA = r0;").expect("reg read assignment");
    let i_dflt = output.find("PRDATA = 0;").expect("readDefault assignment");
    assert!(
        i_reg < i_dflt,
        "readDefault must be emitted after the per-field read (call order = priority), got:\n{}",
        output
    );
    // 已知限制（文档已注明）：PRDATA 只在读条件下被驱动，写周期保持 → 自检报 HDL032 推断锁存
    assert!(
        output.contains("HDL032") && output.contains("PRDATA"),
        "conditional-only PRDATA drive must surface as HDL032, got:\n{}",
        output
    );
}

// ── G1: streamFifoCC 指针带 wrap 位，full/empty 可区分 ──
// 修复前：指针只有 log2Up depth 位，full 与 empty 判据相同（wr == rs2 /
// rd == ws2），复位后两者同时为真 → FIFO 常数死锁；verify.py 的 RefFifoCC
// 用同一组判据（同构对照），所以 L3 长期"全绿"。
// 修复后（depth=4 → ptrBits=2）：
//   指针宽度 2+1=3；empty 仍为全等比较；full 为「同步后读指针最高位取反」。

#[test]
fn hdl_b_stream_fifo_cc_pointers_carry_wrap_bit() {
    let output = assert_ok(r#"
def bCdA: ClockDomain = ClockDomain.mk "clk_a" "rst_a" Async RisingEdge ActiveHigh
def bCdB: ClockDomain = ClockDomain.mk "clk_b" "rst_b" Async RisingEdge ActiveHigh

module bFifoCC[cdA] {
    input pushValid = Bool
    input pushData = UInt[4]
    output pushReady = Bool
    output popValid = Bool
    output popData = UInt[4]
    let io = StreamFifoCCIO.mk[4, 4](
        pushValid, newBoolNamed("b_pushReady_i"), pushData,
        newBoolNamed("b_popValid_i"), newUIntNamed("b_popData_i", 4), newUIntNamed("b_occ", 3))
    let _d = streamFifoCC[4][4](io, cdA, bCdB)
    pushReady := io.pushReady
    popValid := io.popValid
    popData := io.popData
}
println(moduleTreeVL(bFifoCC.create[bCdA].tree))
"#);
    // 指针宽度 = log2Up depth + 1（wrap 位）
    assert!(
        output.contains("reg [2:0] _d_wrPtr;"),
        "write pointer must carry the wrap bit (3 bits for depth 4), got:\n{}",
        output
    );
    assert!(
        output.contains("reg [2:0] _d_rdPtr;"),
        "read pointer must carry the wrap bit, got:\n{}",
        output
    );
    // full 判据：同步后读指针最高位取反后与写指针全等比较（精确表达式）
    assert!(
        output.contains(
            "assign b_pushReady_i = !(_d_wrPtr == {~_d_rdPtrSync2[2], _d_rdPtrSync2[1:0]});"
        ),
        "full must compare against the inverted MSB of the synced read pointer, got:\n{}",
        output
    );
    // empty 判据保持全等比较（证明没有把 empty 一起改掉）
    assert!(
        output.contains("assign b_popValid_i = !(_d_rdPtr == _d_wrPtrSync2);"),
        "empty must stay an equality compare, got:\n{}",
        output
    );
    // RAM 寻址只用低 ptrBits 位（wrap 位不能进索引，否则 mem[4..7] 越界）
    assert!(
        output.contains("_d_mem[_d_wrPtr[1:0]]") && output.contains("_d_mem[_d_rdPtr[1:0]]"),
        "RAM must be addressed with the low pointer bits only, got:\n{}",
        output
    );
    // 双时钟域 always 块与自动端口
    assert!(
        output.contains("always @(posedge clk_a") && output.contains("always @(posedge clk_b"),
        "both clock domains must emit their own always block, got:\n{}",
        output
    );
    // 单驱动：`_d_rdPtr` 只属 clkB。曾经的 when+Cd 赋值会被两个域各发射一次
    // （clkA 块里也出现 `_d_rdPtr <= (_d_rdPtr + 1)`，双驱动/锁步仿真 +2）。
    let i_a = output.find("always @(posedge clk_a").expect("clkA block");
    let i_b = output.find("always @(posedge clk_b").expect("clkB block");
    let blk_a = &output[i_a..i_b];
    assert!(
        !blk_a.contains("_d_rdPtr <="),
        "clkA block must not drive _d_rdPtr (single driver in clkB), got:\n{}",
        output
    );
    assert_eq!(
        output.matches("_d_rdPtr <= (").count(),
        1,
        "exactly one conditional advance of _d_rdPtr (in clkB), got:\n{}",
        output
    );
}

// ── 双域发射（when + Cd 赋值）审计钉子：PulseCCByToggle / CCByToggle ──
// 同一构造在 pulseCCByToggle/ccByToggleUInt 里也是隐患（inCd ≠ 模块主域时
// 会被主域与该域各发射一次）。改为「条件进值」后每个寄存器只有一个驱动。

#[test]
fn hdl_b_cc_by_toggle_single_driver_per_register() {
    let output = assert_ok(r#"
def bCdA: ClockDomain = ClockDomain.mk "clk_a" "rst_a" Async RisingEdge ActiveHigh
def bCdB: ClockDomain = ClockDomain.mk "clk_b" "rst_b" Async RisingEdge ActiveHigh

module bCcPulse[inCd] {
    input pulseIn = Bool
    output pulseOut = Bool
    let outCd = bCdB
    let pl = pulseCCByToggle(pulseIn, inCd, outCd)
    pulseOut := pl
}
module bCcToggle[inCd] {
    input v = Bool
    input d = UInt[8]
    output oValid = Bool
    output oData = UInt[8]
    let outCd = bCdB
    let cc = ccByToggleUInt(v, d, inCd, outCd)
    oValid := cc.valid
    oData := cc.payload
}
println(moduleTreeVL(bCcPulse.create[bCdA].tree))
println(moduleTreeVL(bCcToggle.create[bCdA].tree))
"#);
    // 每个寄存器恰好一处时钟赋值（不再出现 when 包裹 + Cd 赋值的双域发射）
    assert_eq!(
        output.matches("pl_toggle <=").count(),
        1,
        "pulseCCByToggle toggle must have a single driver, got:\n{}",
        output
    );
    assert_eq!(
        output.matches("cc_toggle <=").count(),
        1,
        "ccByToggleUInt toggle must have a single driver, got:\n{}",
        output
    );
    assert_eq!(
        output.matches("cc_buffer <=").count(),
        1,
        "ccByToggleUInt buffer must have a single driver, got:\n{}",
        output
    );
    // 条件已并入赋值值（不再有 when 包裹）
    assert!(
        !output.contains("if (pulseIn) begin") && !output.contains("if (v) begin"),
        "condition must be folded into the value, not a when wrapper, got:\n{}",
        output
    );
    // 同步链仍在 outCd 块
    assert!(
        output.contains("pl_sync1 <= pl_toggle;") && output.contains("cc_sync1 <= cc_toggle;"),
        "outCd synchronizer chains expected, got:\n{}",
        output
    );
}

// ── task-16: mux 消费者不是同步链的下一级（HDL039 误报回归钉）──
// 2FF 链 [s1, s2] 的末级 s2 有两个合法读者：组合输出 q := s2 与同域寄存器经 mux
// （cons <= mux(en, s2, cons)）。修复前 chainNextOf 把 cons 当成链的下一级 ⇒ s2
// 被升级为中间级 ⇒ 对 q := s2 误报 HDL039。修复后：链仍识别（HDL038），无 HDL039。

#[test]
fn hdl_b_mux_consumer_is_not_a_chain_stage() {
    let output = assert_ok(r#"
def t16CdA: ClockDomain = ClockDomain.mk "clk_a" "rst_a" Async RisingEdge ActiveHigh
def t16CdB: ClockDomain = ClockDomain.mk "clk_b" "rst_b" Async RisingEdge ActiveHigh
module t16MuxConsumer[cdA] {
    input d = UInt[4]
    input en = Bool
    output q = UInt[4]
    output held = UInt[4]
    let src = newUIntRegCdNamed("src", 4, cdA)
    let _ = createSignalExpr("", regAssignCd(src.zz_expr, d.zz_expr, cdA))
    let s1 = newUIntRegCdNamed("s1", 4, t16CdB)
    let _ = createSignalExpr("", regAssignCd(s1.zz_expr, src.zz_expr, t16CdB))
    let s2 = newUIntRegCdNamed("s2", 4, t16CdB)
    let _ = createSignalExpr("", regAssignCd(s2.zz_expr, s1.zz_expr, t16CdB))
    q := s2
    let cons = newUIntRegCdNamed("cons", 4, t16CdB)
    let next = Expr.mux(en.zz_expr, s2.zz_expr, cons.zz_expr)
    let _ = createSignalExpr("", regAssignCd(cons.zz_expr, next, t16CdB))
    held := cons
}
println(moduleTreeVL(t16MuxConsumer.create[t16CdA].tree))
"#);
    assert!(
        output.contains("HDL038"),
        "the 2FF chain must still be recognized, got:\n{}",
        output
    );
    assert!(
        !output.contains("HDL039"),
        "a mux consumer of the last FF must not make it a mid stage, got:\n{}",
        output
    );
    assert!(
        !output.contains("HDL037"),
        "the chain must not be truncated, got:\n{}",
        output
    );
}

// ── task-16: memWrite 的读不得污染下一条 drive 的 srcs（pending 泄漏回归钉）──
// memWrite 不产生 DriveSrc，它的读（mem/addr/data/en）曾留在 pending 里并附着到
// 下一条 drive 的 srcs，使纯移位级 `s2 <= s1` 看起来读了 pushData/wrPtr/mem，
// 从而被「纯移位」判据拒掉、链被截断（HDL037）。修复：stmtAssign 开头清 pending。

#[test]
fn hdl_b_mem_write_reads_do_not_contaminate_next_drive() {
    let output = assert_ok(r#"
def t16wCdA: ClockDomain = ClockDomain.mk "clk_a" "rst_a" Async RisingEdge ActiveHigh
def t16wCdB: ClockDomain = ClockDomain.mk "clk_b" "rst_b" Async RisingEdge ActiveHigh
module t16WriteChain[cdA] {
    input pushValid = Bool
    input pushData = UInt[4]
    output q = UInt[4]
    let mem = newMemUIntNamed("m", 4, 4)
    let wr = newUIntRegInitNatNamed("wr", 3, 0)
    let s1 = newUIntRegCdNamed("s1", 4, t16wCdB)
    let _ = createSignalExpr("", regAssignCd(s1.zz_expr, wr.zz_expr, t16wCdB))
    let s2 = newUIntRegCdNamed("s2", 4, t16wCdB)
    let _ = createSignalExpr("", regAssignCd(s2.zz_expr, s1.zz_expr, t16wCdB))
    let _ = whenBegin(pushValid.zz_expr)
    let _ = createSignalExpr("", memWrite(mem.zz_expr, wr.zz_expr, pushData.zz_expr, literal(1)))
    let _ = createSignalExpr("", regAssign(wr.zz_expr, binary(wr.zz_expr, "+", literal(1))))
    let _ = whenEnd(unit)
    q := s2
}
println(moduleTreeVL(t16WriteChain.create[t16wCdA].tree))
"#);
    assert!(
        output.contains("HDL038"),
        "the chain after a memWrite must still be recognized, got:\n{}",
        output
    );
    assert!(
        !output.contains("HDL037"),
        "memWrite reads must not contaminate the next drive (chain truncated), got:\n{}",
        output
    );
}
