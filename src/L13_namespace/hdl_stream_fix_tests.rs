// ============================================================
// HDL Stream pipeline primitive defect-fix regression tests
//
// Pins the F1-F5 semantic fixes from docs/hdl-stream-fsm-design.md §1.2
// (each defect cites Stream.scala as the reference semantics):
//   F1  m2sPipe ready 满/空写反   → ready = outReady || !rValid
//   F2  s2mPipe 只打 ready 一拍   → skid buffer（rValidN/rData/bypass）
//   F3  throwWhen 缺丢弃拍强制消费 → ready = cond || outReady
//   F4  haltWhen/takeWhen 门控缺失 → continueWhen 正门控、takeWhen = throwWhen(!cond)
//   F5  flowMuxPayload 递归深度误写常量 0 → literal(k)
//
// Pattern follows module_tests.rs: inline typort module → moduleTreeVL →
// assert key Verilog lines.
// ============================================================

use super::*;

fn assert_ok(input: &str) -> String {
    match run_with_prelude(input) {
        Ok(output) => output,
        Err(e) => panic!("expected OK, got error: '{}' @ {}:{}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

// ── smoke: prelude loads ──
#[test]
fn stream_fix_prelude_smoke() {
    let output = assert_ok("println(1)");
    assert!(output.contains("1"), "smoke, got: {}", output);
}

// ── F1: m2sPipe ready = outReady || !rValid（空时随时收、满时等下游） ──

#[test]
fn stream_fix_f1_m2spipe_ready() {
    let output = assert_ok(r#"
module f1M2sPipe {
    input push_valid = Bool
    output push_ready = Bool
    input push_data = UInt[8]
    input dn_ready = Bool
    let push = Stream.mk(push_valid, push_ready, push_data)
    let p1 = streamM2sPipeUInt(push)
    output outValid = Bool
    output outData = UInt[8]
    outValid := p1.valid
    outData := p1.payload
    p1.ready := dn_ready
}
println(moduleTreeVL(f1M2sPipe.create.tree))
"#);
    // F1 修复点：ready = (outReady || !rValid)，原缺陷为 (rValid || outReady)
    assert!(output.contains("assign push_ready = (p1_ready || !p1_valid);"),
        "F1: m2sPipe ready should be (outReady || !rValid), got:\n{}", output);
    // 寄存器结构保持：valid/payload 各一拍
    assert!(output.contains("reg p1_valid;"), "F1: rValid register, got:\n{}", output);
    assert!(output.contains("reg [7:0] p1_data;"), "F1: rData register, got:\n{}", output);
    // 装载使能仍是 input.ready（fire 时刻写寄存器）
    assert!(output.contains("if (push_ready) begin"), "F1: load enable, got:\n{}", output);
    assert!(output.contains("p1_valid <= push_valid;"), "F1: rValid load, got:\n{}", output);
    assert!(output.contains("p1_data <= push_data;"), "F1: rData load, got:\n{}", output);
    // 输出侧：valid/payload 由寄存器直出
    assert!(output.contains("assign outValid = p1_valid;"), "F1: out valid = rValid, got:\n{}", output);
}

// ── F2: s2mPipe skid buffer（零延迟 + 反压不丢数） ──

#[test]
fn stream_fix_f2_s2mpipe_skid_buffer() {
    let output = assert_ok(r#"
module f2S2mPipe {
    input in_valid = Bool
    output in_ready = Bool
    input in_data = UInt[8]
    input dn_ready = Bool
    let si = Stream.mk(in_valid, in_ready, in_data)
    let so = streamS2mPipeUInt(si)
    output outValid = Bool
    output outData = UInt[8]
    outValid := so.valid
    outData := so.payload
    so.ready := dn_ready
}
println(moduleTreeVL(f2S2mPipe.create.tree))
"#);
    // skid 结构：rValidN（init 1）+ rData 两个寄存器
    assert!(output.contains("reg so_validN;"), "F2: rValidN register, got:\n{}", output);
    assert!(output.contains("reg [7:0] so_data;"), "F2: rData register, got:\n{}", output);
    // input.ready = rValidN（组合直通 → 零延迟）
    assert!(output.contains("assign in_ready = so_validN;"),
        "F2: input.ready = rValidN, got:\n{}", output);
    // out.valid = input.valid || !rValidN
    assert!(output.contains("assign outValid = (in_valid || !so_validN);"),
        "F2: out.valid bypass, got:\n{}", output);
    // out.payload = rValidN ? input.payload : rData
    assert!(output.contains("assign outData = (so_validN ? in_data : so_data);"),
        "F2: payload skid mux, got:\n{}", output);
    // rValidN 更新：input.valid 清 0、out.ready 置 1（后者覆盖，对齐 setWhen 优先序）
    assert!(output.contains("if (in_valid) begin"), "F2: clearWhen(input.valid), got:\n{}", output);
    assert!(output.contains("so_validN <= 0;"), "F2: rValidN clear, got:\n{}", output);
    assert!(output.contains("if (so_ready) begin"), "F2: setWhen(out.ready), got:\n{}", output);
    assert!(output.contains("so_validN <= 1;"), "F2: rValidN set, got:\n{}", output);
    // rData 装载使能 = input.ready（= rValidN，对齐 Stream.scala RegNextWhen(payload, self.ready)）
    assert!(output.contains("so_data <= in_data;"), "F2: rData load, got:\n{}", output);
}

// ── F2 附带：补齐的 s2mPipe Bool 版 ──

#[test]
fn stream_fix_f2_s2mpipe_bool_version() {
    let output = assert_ok(r#"
module f2S2mPipeBool {
    input in_valid = Bool
    output in_ready = Bool
    input in_data = Bool
    input dn_ready = Bool
    let si = Stream.mk(in_valid, in_ready, in_data)
    let so = streamS2mPipeBool(si)
    output outValid = Bool
    output outData = Bool
    outValid := so.valid
    outData := so.payload
    so.ready := dn_ready
}
println(moduleTreeVL(f2S2mPipeBool.create.tree))
"#);
    assert!(output.contains("assign in_ready = so_validN;"), "F2 Bool: ready = rValidN, got:\n{}", output);
    assert!(output.contains("assign outValid = (in_valid || !so_validN);"), "F2 Bool: bypass valid, got:\n{}", output);
    assert!(output.contains("assign outData = (so_validN ? in_data : so_data);"), "F2 Bool: skid mux, got:\n{}", output);
    assert!(output.contains("reg so_data;"), "F2 Bool: 1-bit rData register, got:\n{}", output);
}

// ── F3: throwWhen 丢弃拍强制消费（ready = cond || outReady） ──

#[test]
fn stream_fix_f3_throwwhen_forced_ready() {
    let output = assert_ok(r#"
module f3ThrowWhen {
    input in_valid = Bool
    output in_ready = Bool
    input in_data = UInt[8]
    input drop = Bool
    input dn_ready = Bool
    let si = Stream.mk(in_valid, in_ready, in_data)
    let sd = streamThrowWhenUInt(si, drop)
    output outValid = Bool
    outValid := sd.valid
    sd.ready := dn_ready
}
println(moduleTreeVL(f3ThrowWhen.create.tree))
"#);
    // F3 修复点：丢弃拍必须强制消费 —— ready = cond || outReady（原缺陷 ready = outReady）
    assert!(output.contains("assign in_ready = (drop || tw_ready);"),
        "F3: input.ready = cond || outReady, got:\n{}", output);
    // 丢拍时 valid 压低
    assert!(output.contains("assign outValid = (in_valid && !drop);"),
        "F3: out.valid = valid && !cond, got:\n{}", output);
    // payload 直通
    assert!(output.contains("assign tw_ready = dn_ready;"), "F3: outReady wiring, got:\n{}", output);
}

// ── F4: haltWhen —— out.valid 必须被 !cond 门控 ──

#[test]
fn stream_fix_f4_haltwhen_gates_valid() {
    let output = assert_ok(r#"
module f4HaltWhen {
    input in_valid = Bool
    output in_ready = Bool
    input in_data = UInt[8]
    input halt = Bool
    input dn_ready = Bool
    let si = Stream.mk(in_valid, in_ready, in_data)
    let sh = streamHaltWhenUInt(si, halt)
    output outValid = Bool
    outValid := sh.valid
    sh.ready := dn_ready
}
println(moduleTreeVL(f4HaltWhen.create.tree))
"#);
    // F4 修复点：out.valid = valid && !cond（原缺陷直通 input.valid）
    assert!(output.contains("assign outValid = (in_valid && !halt);"),
        "F4 haltWhen: out.valid gated by !cond, got:\n{}", output);
    // ready = out.ready && !cond（haltWhen = continueWhen(!cond)）
    assert!(output.contains("assign in_ready = (hw_ready && !halt);"),
        "F4 haltWhen: ready gated, got:\n{}", output);
    assert!(output.contains("assign hw_ready = dn_ready;"), "F4 haltWhen: outReady wiring, got:\n{}", output);
}

// ── F4: continueWhen —— 正向 cond 门控（原误实现为 haltWhen 的反相版） ──

#[test]
fn stream_fix_f4_continuewhen_positive_cond() {
    let output = assert_ok(r#"
module f4ContinueWhen {
    input in_valid = Bool
    output in_ready = Bool
    input in_data = UInt[8]
    input go = Bool
    input dn_ready = Bool
    let si = Stream.mk(in_valid, in_ready, in_data)
    let sc = streamContinueWhenUInt(si, go)
    output outValid = Bool
    outValid := sc.valid
    sc.ready := dn_ready
}
println(moduleTreeVL(f4ContinueWhen.create.tree))
"#);
    assert!(output.contains("assign outValid = (in_valid && go);"),
        "F4 continueWhen: out.valid = valid && cond, got:\n{}", output);
    assert!(output.contains("assign in_ready = (cw_ready && go);"),
        "F4 continueWhen: ready = outReady && cond, got:\n{}", output);
    assert!(output.contains("assign cw_ready = dn_ready;"), "F4 continueWhen: outReady wiring, got:\n{}", output);
}

// ── F4: takeWhen = throwWhen(!cond)（原误实现为 haltWhen 别名） ──

#[test]
fn stream_fix_f4_takewhen_is_throwwhen_of_not_cond() {
    let output = assert_ok(r#"
module f4TakeWhen {
    input in_valid = Bool
    output in_ready = Bool
    input in_data = UInt[8]
    input take = Bool
    input dn_ready = Bool
    let si = Stream.mk(in_valid, in_ready, in_data)
    let st = streamTakeWhenUInt(si, take)
    output outValid = Bool
    outValid := st.valid
    st.ready := dn_ready
}
println(moduleTreeVL(f4TakeWhen.create.tree))
"#);
    // takeWhen(take)：保留 take 的拍 —— out.valid = valid && !!take（throwWhen(!take) 展开）
    assert!(output.contains("assign outValid = (in_valid && !!take);"),
        "F4 takeWhen: out.valid keeps cond beats, got:\n{}", output);
    // 丢弃拍（take=0）强制消费：ready = !take || outReady
    assert!(output.contains("assign in_ready = (!take || tw_ready);"),
        "F4 takeWhen: ready = !cond || outReady, got:\n{}", output);
    assert!(output.contains("assign tw_ready = dn_ready;"), "F4 takeWhen: outReady wiring, got:\n{}", output);
}

// ── F5: flowMuxPayload 递归深度 literal(k)（原误写常量 0，永远选第 0 路） ──

#[test]
fn stream_fix_f5_flowmux_selects_by_index() {
    let output = assert_ok(r#"
module f5FlowMux {
    input av = Bool
    input ad = UInt[8]
    input bv = Bool
    input bd = UInt[8]
    input cv = Bool
    input cdd = UInt[8]
    input sel = UInt[2]
    output mValid = Bool
    output mData = UInt[8]
    let fa = Flow.mk(ad, av)
    let fb = Flow.mk(bd, bv)
    let fc = Flow.mk(cdd, cv)
    let m = flowMuxUInt(sel, cons(fa, cons(fb, cons(fc, nil))))
    mValid := m.valid
    mData := m.payload
}
println(moduleTreeVL(f5FlowMux.create.tree))
"#);
    // F5 修复点：payload 选择链的谓词应是 (sel == k) 逐级递增
    //（原缺陷三级全是 (sel == 0)，第 1/2 路永远选不中）
    assert!(output.contains("(sel == 0) ? ad : ((sel == 1) ? bd : ((sel == 2) ? cdd : 0))"),
        "F5: payload mux chain must index by k, got:\n{}", output);
    // valid 侧本就正确（对照不回归）
    assert!(output.contains("(sel == 0) ? av : ((sel == 1) ? bv : ((sel == 2) ? cv : 0))"),
        "F5: valid mux chain unchanged, got:\n{}", output);
}

// ── 设计文档 §11.1 验收级联：m2sPipe → s2mPipe（F1+F2 组合行为） ──

#[test]
fn stream_fix_cascade_m2spipe_s2mpipe() {
    let output = assert_ok(r#"
module f12PipeCascade {
    input push_valid = Bool
    output push_ready = Bool
    input push_data = UInt[8]
    input dn_ready = Bool
    let push = Stream.mk(push_valid, push_ready, push_data)
    let p1 = streamM2sPipeUInt(push)
    let p2 = streamS2mPipeUInt(p1)
    output outValid = Bool
    output outData = UInt[8]
    outValid := p2.valid
    outData := p2.payload
    p2.ready := dn_ready
}
println(moduleTreeVL(f12PipeCascade.create.tree))
"#);
    // F1：m2sPipe 的 ready = (outReady || !rValid)
    assert!(output.contains("assign push_ready = (p1_ready || !p1_valid);"),
        "cascade: F1 m2sPipe ready, got:\n{}", output);
    // F2：s2mPipe 的 ready 直通 + skid 结构（p1.ready 由 p2 的 rValidN 驱动）
    assert!(output.contains("assign p1_ready = p2_validN;"),
        "cascade: F2 s2mPipe ready passthrough, got:\n{}", output);
    assert!(output.contains("assign outValid = (p1_valid || !p2_validN);"),
        "cascade: F2 skid bypass valid, got:\n{}", output);
    assert!(output.contains("assign outData = (p2_validN ? p1_data : p2_data);"),
        "cascade: F2 skid payload mux, got:\n{}", output);
    assert!(output.contains("reg p2_validN;"), "cascade: rValidN register, got:\n{}", output);
    assert!(output.contains("reg [7:0] p2_data;"), "cascade: rData register, got:\n{}", output);
}
