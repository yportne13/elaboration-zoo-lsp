#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
SpinalHDL lib 复刻 —— L3 行为验证（真值表/时序仿真）

流程：
  1. 对每个验证用例 .typort 运行 `typort check`，抓取生成的 Verilog 模块
  2. 按 CASES（组合）与 SEQ_CASES（时序）表解析端口与 Python 参考实现
  3. 生成 C++ testbench + 激励文件，verilator 编译仿真
  4. 比对仿真输出与参考值；任何不一致 exit 1；仿真器缺失时打印跳过并 exit 0

用法：
  python3 tools/spinalhdl-verify/verify.py [--cases 文件...] [--keep]
"""
import os, re, subprocess, sys, tempfile, shutil, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from dualclock_runner import run_dualclock_case

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
TYPORT = os.environ.get("TYPORT", os.path.join(ROOT, "target", "release", "typort"))
VERILATOR = os.environ.get("VERILATOR", "verilator")
CASE_DIR = os.path.join(ROOT, "tools", "spinalhdl-verify", "cases")

# ---------------------------------------------------------------------------
# 组合参考实现
# ---------------------------------------------------------------------------
def ref_reverse(a, w=8):
    return int(f"{a:0{w}b}"[::-1], 2)

def ref_proplsb(a, w=8):
    out = 0
    for i in range(w):
        if (a >> i) != 0:
            out |= (1 << i)
    return out

def ref_propmsb(a, w=8):
    out = 0
    acc = 0
    for i in range(w):
        acc |= (a >> i) & 1
        if acc:
            out |= (1 << i)
    return out

def ref_popcount(a):
    return bin(a).count("1")

def ref_clz(a, w=8):
    for i in range(w - 1, -1, -1):
        if (a >> i) & 1:
            return w - 1 - i
    return w

def ref_ctz(a, w=8):
    for i in range(w):
        if (a >> i) & 1:
            return i
    return w

def ref_majority(a, w=7):
    return bin(a).count("1") >= (w // 2 + 1)

def ref_uinttooh(a):
    return 1 << a

def ref_uinttoohm1(a):
    return (1 << a) - 1

def ref_ohtouint(oh, w=8):
    out = 0
    bits = max(1, (w - 1).bit_length())
    for i in range(bits):
        for k in range(w):
            if ((k >> i) & 1) and ((oh >> k) & 1):
                out |= (1 << i)
    return out

def ref_ohlegal(oh, w=8):
    return oh == 0 or (oh & (oh - 1)) == 0

def ref_ohfirst(oh):
    if oh == 0:
        return 0
    return oh & (~(oh - 1) & 0xFFFFFFFF)

def ref_ohlast(oh, w=8):
    if oh == 0:
        return 0
    rev = ref_reverse(oh, w)
    f = ref_ohfirst(rev)
    return ref_reverse(f, w)

def ref_ohrr(req, pri, w=4):
    dbl = req | (req << w)
    grant = dbl & ~((dbl - pri) & 0xFFFFFFFF)
    return (grant & ((1 << w) - 1)) | ((grant >> w) & ((1 << w) - 1))

def ref_prioritymux(sel, vals, dflt):
    for i, v in enumerate(vals):
        if (sel >> i) & 1:
            return v
    return dflt

def ref_ohmxuor(sel, vals):
    out = 0
    for i, v in enumerate(vals):
        if (sel >> i) & 1:
            out |= v
    return out

def ref_min(a, b):
    return a if a < b else b

def ref_max(a, b):
    return a if a > b else b

def ref_clamp(a, lo, hi):
    return max(lo, min(a, hi))

def ref_togray(x):
    return (x >> 1) ^ x

def ref_fromgray(g, w=8):
    out = 0
    acc = 0
    for i in range(w - 1, -1, -1):
        acc ^= (g >> i) & 1
        out |= acc << i
    return out

def ref_endianswap(a, base=8, w=16):
    n = w // base
    out = 0
    for g in range(n):
        src_lo = g * base
        dst_lo = (n - 1 - g) * base
        out |= ((a >> src_lo) & ((1 << base) - 1)) << dst_lo
    return out

def ref_addcarry(a, b):
    s = a + b
    return (s & 0xFF, 1 if s > 0xFF else 0)

def ref_log2floor(a, w=8):
    return a.bit_length() - 1 if a else 0

def ref_log2ceil(a):
    f = ref_log2floor(a)
    if a == 0:
        return 0
    return f if (a & (a - 1)) == 0 else f + 1

def ref_setfromfirstone(a, w=8):
    out = 0
    acc = 0
    for i in range(w):
        acc |= (a >> i) & 1
        if acc:
            out |= (1 << i)
    return out

def ref_napot(a, w=4):
    return (ref_setfromfirstone((~a) & 0xF, w) << 1) & 0x1F

def ref_scrap(a, sh, w=8, sw=3):
    logic = a
    acc = 0
    for t in range(sw):
        shiftAmt = 1 << t
        low = logic & ((1 << shiftAmt) - 1) if shiftAmt > 0 else 0
        if (sh >> t) & 1:
            if low != 0:
                acc |= 1
        if (sh >> t) & 1:
            logic = ((logic >> shiftAmt) | logic)
    return (logic | acc) & 0xFF

def ref_countoneoneach(a, w=4):
    return [bin(a & ((1 << k) - 1)).count("1") for k in range(1, w + 1)]

# ---------------------------------------------------------------------------
# 组合用例表
# ---------------------------------------------------------------------------
CASES = {
    "vReverse":       ([("a", 8)], [("r", 8)], lambda d: [ref_reverse(d["a"])], "full"),
    "vReverseU":      ([("a", 8)], [("r", 8)], lambda d: [ref_reverse(d["a"])], "full"),
    "vPropLsb":       ([("a", 8)], [("r", 8)], lambda d: [ref_proplsb(d["a"])], "full"),
    "vPropMsb":       ([("a", 8)], [("r", 8)], lambda d: [ref_propmsb(d["a"])], "full"),
    "vCountOne":      ([("a", 8)], [("c", 4)], lambda d: [ref_popcount(d["a"])], "full"),
    "vCountOneU":     ([("a", 8)], [("c", 4)], lambda d: [ref_popcount(d["a"])], "full"),
    "vClz":           ([("a", 8)], [("c", 4)], lambda d: [ref_clz(d["a"])], "full"),
    "vCtz":           ([("a", 8)], [("c", 4)], lambda d: [ref_ctz(d["a"])], "full"),
    "vMajority":      ([("a", 7)], [("m", 1)], lambda d: [1 if ref_majority(d["a"]) else 0], "full"),
    "vUintToOh":      ([("a", 3)], [("oh", 8)], lambda d: [ref_uinttooh(d["a"])], "full"),
    "vUintToOhM1":    ([("a", 3)], [("oh", 8)], lambda d: [ref_uinttoohm1(d["a"])], "full"),
    "vOhToUInt":      ([("oh", 8)], [("idx", 3)], lambda d: [ref_ohtouint(d["oh"])], "full"),
    "vOhLegal":       ([("oh", 8)], [("legal", 1)], lambda d: [1 if ref_ohlegal(d["oh"]) else 0], "full"),
    "vOhFirst":       ([("oh", 8)], [("f", 8)], lambda d: [ref_ohfirst(d["oh"])], "full"),
    "vOhLast":        ([("oh", 8)], [("l", 8)], lambda d: [ref_ohlast(d["oh"])], "full"),
    "vOhRR":          ([("req", 4), ("pri", 4)], [("g", 4)], lambda d: [ref_ohrr(d["req"], d["pri"])], "full"),
    "vPriorityMux":   ([("sel", 4), ("a", 8), ("b", 8), ("c", 8), ("d", 8), ("dflt", 8)],
                      [("o", 8)], lambda d: [ref_prioritymux(d["sel"], [d["a"], d["b"], d["c"], d["d"]], d["dflt"])], "sample"),
    "vMuxOH":         ([("sel", 4), ("a", 8), ("b", 8), ("c", 8), ("d", 8)],
                      [("o", 8)], lambda d: [ref_prioritymux(d["sel"], [d["a"], d["b"], d["c"], d["d"]], d["a"])], "sample"),
    "vOhMuxOr":       ([("sel", 4), ("a", 8), ("b", 8), ("c", 8), ("d", 8)],
                      [("o", 8)], lambda d: [ref_ohmxuor(d["sel"], [d["a"], d["b"], d["c"], d["d"]])], "sample"),
    "vMinMax":        ([("a", 8), ("b", 8)], [("mn", 8), ("mx", 8)],
                      lambda d: [ref_min(d["a"], d["b"]), ref_max(d["a"], d["b"])], "sample"),
    "vClamp":         ([("a", 8), ("lo", 8), ("hi", 8)], [("cl", 8)],
                      lambda d: [ref_clamp(d["a"], d["lo"], d["hi"])], "sample"),
    "vGray":          ([("x", 8)], [("g", 8), ("back", 8)],
                      lambda d: [ref_togray(d["x"]), ref_fromgray(ref_togray(d["x"]))], "full"),
    "vEndianSwap":    ([("a", 16)], [("s", 16)], lambda d: [ref_endianswap(d["a"])], "full"),
    "vAddCarry":      ([("a", 8), ("b", 8)], [("sum", 8), ("carry", 1)],
                      lambda d: list(ref_addcarry(d["a"], d["b"])), "sample"),
    "vLog2Floor":     ([("a", 8)], [("lf", 3)], lambda d: [ref_log2floor(d["a"])], "full"),
    "vLog2Ceil":      ([("a", 8)], [("lc", 4)], lambda d: [ref_log2ceil(d["a"])], "full"),
    "vSetFromFirstOne": ([("a", 8)], [("s", 8)], lambda d: [ref_setfromfirstone(d["a"])], "full"),
    "vNapot":         ([("a", 4)], [("n", 5)], lambda d: [ref_napot(d["a"])], "full"),
    "vScrap":         ([("a", 8), ("sh", 3)], [("s", 8)], lambda d: [ref_scrap(d["a"], d["sh"])], "full"),
    "vCountOneOnEach": ([("a", 4)], [("c1", 3), ("c2", 3), ("c3", 3), ("c4", 3)],
                      lambda d: ref_countoneoneach(d["a"]), "full"),
}

# ---------------------------------------------------------------------------
# 时序参考状态机（step(rst, inputs) -> outputs dict，posedge 之后的值）
# ---------------------------------------------------------------------------
class RefCounterMod:
    def reset_state(self):
        self.v = 0
    def step(self, rst, inputs):
        if rst:
            self.v = 0
        else:
            self.v = (self.v + 1) % 10
        return {"value": self.v, "willOverflow": 1 if self.v == 9 else 0}

class RefCounterUpDown:
    def reset_state(self):
        self.v = 0
    def step(self, rst, inputs):
        inc, dec = inputs["inc"], inputs["dec"]
        incOnly = inc and not dec
        decOnly = dec and not inc
        if rst:
            self.v = 0
        else:
            if incOnly:
                self.v = 0 if self.v == 9 else self.v + 1
            if decOnly:
                self.v = 9 if self.v == 0 else self.v - 1
        return {"value": self.v,
                "willOverflowIfInc": 1 if self.v == 9 else 0,
                "willUnderflowIfDec": 1 if self.v == 0 else 0,
                "willOverflow": 1 if (incOnly and self.v == 9) else 0,
                "willUnderflow": 1 if (decOnly and self.v == 0) else 0}

class RefDownCounter:
    def reset_state(self):
        self.v = 9
    def step(self, rst, inputs):
        if rst:
            self.v = 9
        else:
            self.v = 9 if self.v == 0 else self.v - 1
        return {"value": self.v, "willOverflow": 1 if self.v == 0 else 0}

class RefOneHotCounter:
    def reset_state(self):
        self.v = 1
    def step(self, rst, inputs):
        if rst:
            self.v = 1
        else:
            self.v = (self.v << 1) & 0xF
            if self.v == 0:
                self.v = 1
        return {"value": self.v, "willOverflow": 1 if self.v == 8 else 0}

class RefJohnsonCounter:
    def reset_state(self):
        self.v = 0
    def step(self, rst, inputs):
        top2 = ((self.v >> 3) & 1) and not ((self.v >> 2) & 1)
        if rst:
            self.v = 0
        else:
            if top2:
                self.v = 0
            else:
                self.v = ((self.v & 0x7) << 1) | (0 if (self.v >> 3) & 1 else 1)
        top2 = ((self.v >> 3) & 1) and not ((self.v >> 2) & 1)
        return {"value": self.v, "willOverflow": 1 if top2 else 0}

class RefDelayEvent:
    def reset_state(self):
        self.run = 0
        self.cnt = 0
        self.cycle = 4
    def step(self, rst, inputs):
        if rst:
            self.run = 0
            self.cnt = 0
        else:
            ev = inputs["ev"]
            ovf = self.cnt == self.cycle - 1
            if ovf:
                self.run = 0
                self.cnt = 0
            if ev:
                self.run = 1
                self.cnt = 0
            if (not ev) and (not ovf):
                self.cnt += 1
        return {"de": 1 if (self.run and self.cnt == self.cycle - 1) else 0}

class RefTimeout:
    def reset_state(self):
        self.state = 0
        self.cnt = 0
        self.limit = 8
    def step(self, rst, inputs):
        if rst:
            self.state = 0
            self.cnt = 0
        else:
            ovf = self.cnt == self.limit - 1
            if ovf:
                self.state = 1
                self.cnt = 0
            if not ovf:
                self.cnt += 1
        return {"ts": self.state}

SEQ_CASES = {
    "vCounterMod":      ([("en", 1)], [("value", 4), ("willOverflow", 1)], RefCounterMod, 60),
    "vCounterUpDown":   ([("inc", 1), ("dec", 1)], [("value", 4), ("willOverflowIfInc", 1), ("willUnderflowIfDec", 1), ("willOverflow", 1), ("willUnderflow", 1)], RefCounterUpDown, 80),
    "vDownCounter":     ([("en", 1)], [("value", 4), ("willOverflow", 1)], RefDownCounter, 60),
    "vOneHotCounter":   ([("en", 1)], [("value", 4), ("willOverflow", 1)], RefOneHotCounter, 60),
    "vJohnsonCounter":  ([("en", 1)], [("value", 4), ("willOverflow", 1)], RefJohnsonCounter, 60),
    "vDelayEvent":      ([("ev", 1)], [("de", 1)], RefDelayEvent, 60),
    "vTimeout":         ([("en", 1)], [("ts", 1)], RefTimeout, 60),
}



# ---------------------------------------------------------------------------
# Stream 时序参考状态机
# ---------------------------------------------------------------------------
class RefStreamM2s:
    def reset_state(self):
        self.rValid = 0
        self.rData = 0
    def step(self, rst, inputs):
        if rst:
            self.rValid = 0
            self.rData = 0
        else:
            in_ready = self.rValid or inputs["pop_ready"]
            if in_ready:
                self.rValid = 1 if inputs["push_valid"] else 0
                self.rData = inputs["push_payload"]
        return {"push_ready": 1 if (self.rValid or inputs["pop_ready"]) else 0,
                "pop_valid": self.rValid,
                "pop_payload": self.rData}

class RefStreamFifo:
    def reset_state(self):
        self.pPush = 0
        self.pPop = 0
        self.mem = [0, 0, 0, 0]
        self.depth = 4
        self.pw = 3
    def step(self, rst, inputs):
        if rst:
            self.pPush = 0
            self.pPop = 0
            self.mem = [0, 0, 0, 0]
        else:
            full = (self.pPush ^ self.pPop) == (1 << (self.pw - 1))
            empty = self.pPush == self.pPop
            push_ready = 0 if full else 1
            pop_valid = 0 if empty else 1
            push_fire = inputs["push_valid"] and push_ready
            pop_fire = pop_valid and inputs["pop_ready"]
            if push_fire:
                self.mem[self.pPush & (self.depth - 1)] = inputs["push_payload"]
                self.pPush = (self.pPush + 1) & 0x7
            if pop_fire:
                self.pPop = (self.pPop + 1) & 0x7
            full = (self.pPush ^ self.pPop) == (1 << (self.pw - 1))
            empty = self.pPush == self.pPop
            return {"push_ready": 0 if full else 1,
                    "pop_valid": 0 if empty else 1,
                    "pop_payload": self.mem[self.pPop & (self.depth - 1)],
                    "occ": (self.pPush - self.pPop) & 0x7}
        full = (self.pPush ^ self.pPop) == (1 << (self.pw - 1))
        empty = self.pPush == self.pPop
        return {"push_ready": 0 if full else 1,
                "pop_valid": 0 if empty else 1,
                "pop_payload": self.mem[self.pPop & (self.depth - 1)],
                "occ": (self.pPush - self.pPop) & 0x7}

class RefStreamMux:
    def reset_state(self):
        pass
    def step(self, rst, inputs):
        sel = inputs["sel"]
        av, bv = inputs["a_valid"], inputs["b_valid"]
        ar = av and sel == 0
        br = bv and sel == 1
        # a_ready = (sel==0) && m_ready; b_ready = (sel==1) && m_ready
        a_ready = 1 if (sel == 0 and inputs["m_ready"]) else 0
        b_ready = 1 if (sel == 1 and inputs["m_ready"]) else 0
        m_valid = av if sel == 0 else bv
        m_payload = inputs["a_payload"] if sel == 0 else inputs["b_payload"]
        return {"a_ready": a_ready, "b_ready": b_ready,
                "m_valid": 1 if m_valid else 0, "m_payload": m_payload}

class RefStreamArb:
    def reset_state(self):
        pass
    def step(self, rst, inputs):
        av, bv = inputs["a_valid"], inputs["b_valid"]
        g_a = av
        g_b = bv and not av
        a_ready = 1 if (g_a and inputs["m_ready"]) else 0
        b_ready = 1 if (g_b and inputs["m_ready"]) else 0
        m_valid = av or bv
        if g_a:
            m_payload = inputs["a_payload"]
        elif g_b:
            m_payload = inputs["b_payload"]
        else:
            m_payload = 0
        return {"a_ready": a_ready, "b_ready": b_ready,
                "m_valid": 1 if m_valid else 0, "m_payload": m_payload}

class RefStreamFork:
    def reset_state(self):
        pass
    def step(self, rst, inputs):
        in_ready = 1 if (inputs["o0_ready"] and inputs["o1_ready"]) else 0
        return {"in_ready": in_ready,
                "o0_valid": 1 if inputs["in_valid"] else 0,
                "o0_payload": inputs["in_payload"],
                "o1_valid": 1 if inputs["in_valid"] else 0,
                "o1_payload": inputs["in_payload"]}

STREAM_SEQ_CASES = {
    "vStreamM2s":  ([("push_valid", 1), ("push_payload", 8), ("pop_ready", 1)],
                    [("push_ready", 1), ("pop_valid", 1), ("pop_payload", 8)], RefStreamM2s, 60),
    "vStreamFifo": ([("push_valid", 1), ("push_payload", 8), ("pop_ready", 1)],
                    [("push_ready", 1), ("pop_valid", 1), ("pop_payload", 8), ("occ", 3)], RefStreamFifo, 80),
    "vStreamMux":  ([("sel", 1), ("a_valid", 1), ("a_payload", 8), ("b_valid", 1), ("b_payload", 8), ("m_ready", 1)],
                    [("a_ready", 1), ("b_ready", 1), ("m_valid", 1), ("m_payload", 8)], RefStreamMux, 60),
    "vStreamArb":  ([("a_valid", 1), ("a_payload", 8), ("b_valid", 1), ("b_payload", 8), ("m_ready", 1)],
                    [("a_ready", 1), ("b_ready", 1), ("m_valid", 1), ("m_payload", 8)], RefStreamArb, 60),
    "vStreamFork": ([("in_valid", 1), ("in_payload", 8), ("o0_ready", 1), ("o1_ready", 1)],
                    [("in_ready", 1), ("o0_valid", 1), ("o0_payload", 8), ("o1_valid", 1), ("o1_payload", 8)], RefStreamFork, 60),
}



class RefPrescaler:
    def reset_state(self):
        self.c = 0
    def step(self, rst, inputs):
        if rst:
            self.c = 0
        else:
            limit = inputs["lim"]
            if self.c >= limit:
                self.c = 0
            else:
                self.c += 1
        return {"ov": 1 if self.c >= inputs["lim"] else 0}

class RefTimer:
    def reset_state(self):
        self.c = 0
        self.inhibit = 0
    def step(self, rst, inputs):
        if rst:
            self.c = 0
            self.inhibit = 0
        else:
            tick, clr = inputs["tick"], inputs["clr"]
            limit = inputs["lim"]
            hit = self.c == limit
            if tick:
                self.inhibit = 1 if hit else 0
                if not hit:
                    self.c += 1
            if clr:
                self.c = 0
                self.inhibit = 0
        return {"full": 1 if ((self.c == inputs["lim"]) and inputs["tick"] and not self.inhibit) else 0,
                "value": self.c}

class RefInterruptCtrl:
    def reset_state(self):
        self.p = 0
    def step(self, rst, inputs):
        if rst:
            self.p = 0
        else:
            self.p = (self.p & (~inputs["clears"] & 0xF)) | inputs["inputs"]
        return {"pend": (self.p & inputs["masks"]) & 0xF}

class RefWatchdog:
    def reset_state(self):
        self.c = 0
        self.t = 0
    def step(self, rst, inputs):
        if rst:
            self.c = 0
            self.t = 0
        else:
            limit = inputs["lim"]
            ovf = self.c == limit
            if ovf:
                self.t = 1
                self.c = 0
            if inputs["feed"]:
                self.t = 0
                self.c = 0
            if not inputs["feed"] and not ovf:
                self.c += 1
        return {"timeout": self.t}

MISC_SEQ_CASES = {
    "vPrescaler":      ([("lim", 8)], [("ov", 1)], RefPrescaler, 80),
    "vTimer":          ([("tick", 1), ("clr", 1), ("lim", 8)], [("full", 1), ("value", 8)], RefTimer, 80),
    "vInterruptCtrl":  ([("inputs", 4), ("clears", 4), ("masks", 4)], [("pend", 4)], RefInterruptCtrl, 60),
    "vWatchdog":       ([("feed", 1), ("lim", 8)], [("timeout", 1)], RefWatchdog, 80),
}

MISC_CASES = {
    "vBcdAdd":  ([("a", 4), ("b", 4), ("cin", 1)], [("s", 4), ("co", 1)],
                 lambda d: bcd_add(d["a"], d["b"], d["cin"]), "full"),
    "vMaskedEq": ([("hard", 4)], [("eq", 1)],
                 lambda d: [1 if ((d["hard"] & 6) == 2) else 0], "full"),
    "vDecoder": ([("oh", 4)], [("idx", 2)],
                 lambda d: [ref_ohtouint(d["oh"], 4)], "full"),
}

def bcd_add(a, b, cin):
    s = a + b + cin
    if s > 9:
        return (s + 6, 1) if s + 6 <= 15 else (((s + 6) & 0xF), 1)
    return (s, 0)


class RefPulseCC:
    def reset_state(self):
        self.toggle = 0
        self.s1 = 0
        self.s2 = 0
    def step(self, rst, inputs):
        if rst:
            self.toggle = 0
            self.s1 = 0
            self.s2 = 0
        else:
            # non-blocking semantics: s2 <= s1 (OLD s1), s1 <= toggle (NEW toggle)
            old_s1 = self.s1
            if inputs["pulseIn"]:
                self.toggle = 1 - self.toggle
            self.s1 = self.toggle
            self.s2 = old_s1
        return {"pulseOut": (self.s1 ^ self.s2) & 1}

class RefFifoCC:
    def reset_state(self):
        self.mem = [0] * 4
        self.wr = 0
        self.rd = 0
        self.ws1 = 0
        self.ws2 = 0
        self.rs1 = 0
        self.rs2 = 0
        self.popreg = 0
    def step(self, rst, inputs):
        if rst:
            self.mem = [0] * 4
            self.wr = 0
            self.rd = 0
            self.ws1 = 0
            self.ws2 = 0
            self.rs1 = 0
            self.rs2 = 0
            self.popreg = 0
        else:
            pv, pd = inputs["pushValid"], inputs["pushData"]
            full = self.wr == self.rs2
            empty = self.rd == self.ws2
            # clkA domain (main): sync rdPtr, push
            self.rs1 = self.rd
            self.rs2 = self.rs1
            if pv and not full:
                self.mem[self.wr] = pd
                self.wr = (self.wr + 1) & 3
            # clkB domain: sync wrPtr, pop
            self.ws1 = self.wr
            self.ws2 = self.ws1
            self.popreg = self.mem[self.rd]
            if not empty:
                self.rd = (self.rd + 1) & 3
        full = self.wr == self.rs2
        empty = self.rd == self.ws2
        return {"pushReady": 0 if full else 1, "popValid": 0 if empty else 1, "popData": self.popreg}

DUAL_CLOCK_CASES = {
    "vPulseCC": ([("pulseIn", 1)], [("pulseOut", 1)], RefPulseCC, 80, "clkA", "clkB"),
    "vFifoCC":  ([("pushValid", 1), ("pushData", 4)], [("pushReady", 1), ("popValid", 1), ("popData", 4)], RefFifoCC, 120, "clkA", "clkB"),
}

DEFAULT_CASES = ["v_utils_combinational.typort", "v_utils_sequential.typort", "v_stream_sequential.typort", "v_misc_combinational.typort", "v_dualclock.typort"]


def run_typort(case_file):
    proc = subprocess.run([TYPORT, "check", case_file], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out = proc.stdout.decode("utf-8", "replace") + proc.stderr.decode("utf-8", "replace")
    modules = {}
    for m in re.finditer(r"note: module (\w+) \(([^;]*)\);(.*?)endmodule", out, re.S):
        name, port_str, body = m.group(1), m.group(2), m.group(3)
        ports = {}
        for pm in re.finditer(r"(input|output)\s+(?:wire|reg)?\s*(?:signed\s+)?(?:\[(\d+):0\])?\s*(\w+)", port_str):
            d, w, pname = pm.group(1), pm.group(2), pm.group(3)
            ports[pname] = (d, int(w) if w else 1)
        modules[name] = (ports, "module %s (%s);%sendmodule" % (name, port_str, body))
    return modules


def gen_stimulus(ports_in, ref, strategy):
    inputs = []
    expected = []
    if strategy == "full":
        total = 1
        for _, w in ports_in:
            total *= (1 << w)
        sweep = range(min(total, 300000))
    else:
        random.seed(42)
        sweep = [random.randrange(1 << 32) for _ in range(4000)]
    for idx in sweep:
        d = {}
        for (name, w) in ports_in:
            d[name] = idx & ((1 << w) - 1)
            idx >>= w
        outs = ref(d)
        inputs.append(" ".join("%x" % d[n] for n, _ in ports_in))
        expected.append(" ".join("%x" % o for o in outs))
    return inputs, expected


def run_comb_case(name, ports_in, ports_out, ref, strategy, workdir, modules):
    inputs, expected = gen_stimulus(ports_in, ref, strategy)
    stim_file = os.path.join(workdir, name + ".stim")
    with open(stim_file, "w") as f:
        for ins in inputs:
            f.write(ins + "\n")
    inputs_decl = " ".join("uint64_t %s;" % n for n, _ in ports_in)
    scanf_fmt = " ".join(["%llx"] * len(ports_in))
    scanf_vars = ", ".join("&%s" % n for n, _ in ports_in)
    assigns = "\n    ".join("dut->%s = %s;" % (n, n) for n, _ in ports_in)
    reads = "".join("printf(\"%%x \", dut->%s);" % n for n, _ in ports_out)
    tb = r'''
#include "V%s.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    V%s* dut = new V%s;
    FILE* f = fopen("%s", "r");
    if (!f) return 2;
    %s
    while (fscanf(f, "%s", %s) == %d) {
        %s
        dut->eval();
        %s
        printf("\n");
    }
    fclose(f);
    delete dut;
    return 0;
}
''' % (name, name, name, stim_file, inputs_decl, scanf_fmt, scanf_vars, len(ports_in), assigns, reads)
    tb_file = os.path.join(workdir, name + "_tb.cpp")
    with open(tb_file, "w") as f:
        f.write(tb)
    objdir = os.path.join(workdir, "obj_" + name)
    verilog_file = os.path.join(workdir, name + ".v")
    with open(verilog_file, "w") as f:
        f.write(modules[name][1])
    comp = subprocess.run(
        [VERILATOR, "--cc", "--exe", "-Wno-fatal", "--top-module", name,
         "-Mdir", objdir, "-o", name + "_tb", tb_file, verilog_file],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=workdir)
    if comp.returncode != 0:
        print("  [COMPILE FAIL] %s:\n%s" % (name, comp.stderr.decode("utf-8", "replace")[-1500:]))
        return None
    bld = subprocess.run(["make", "-C", objdir, "-f", "V%s.mk" % name],
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=workdir)
    if bld.returncode != 0:
        print("  [MAKE FAIL] %s:\n%s" % (name, bld.stderr.decode("utf-8", "replace")[-1500:]))
        return None
    exe = os.path.join(objdir, name + "_tb")
    runp = subprocess.run([exe], stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=workdir)
    if runp.returncode != 0:
        print("  [RUN FAIL] %s: %s" % (name, runp.stderr.decode("utf-8", "replace")[-500:]))
        return None
    got_stdout = runp.stdout.decode("utf-8", "replace")
    got = got_stdout.strip().split("\n") if got_stdout.strip() else []
    ok = True
    bad = 0
    for i, (ins, exps) in enumerate(zip(inputs, expected)):
        if i >= len(got):
            ok = False
            break
        got_vals = [str(int(g, 16)) for g in got[i].split()]
        exp_vals = [str(int(e, 16)) for e in exps.split()]
        if got_vals != exp_vals:
            ok = False
            bad += 1
            if bad <= 3:
                print("  [MISMATCH] %s vec %d: in=%s got=%s expected=%s" % (name, i, ins, got_vals, exp_vals))
        if bad > 20:
            break
    return ok and bad == 0


def run_seq_case(name, ports_in, ports_out, ref, n_cycles, workdir, modules):
    random.seed(7)
    ref = ref()
    ref.reset_state()
    lines = []
    for _ in range(2):
        ins0 = {n: 0 for n, _ in ports_in}
        outs = ref.step(1, ins0)
        lines.append((1, ins0, outs))
    for _ in range(n_cycles):
        inputs = {}
        for pn, w in ports_in:
            inputs[pn] = random.randrange(1 << w) if w > 0 else 0
        outs = ref.step(0, inputs)
        lines.append((0, inputs, outs))
    stim_file = os.path.join(workdir, name + ".stim")
    with open(stim_file, "w") as f:
        for (rst, ins, outs) in lines:
            f.write("%d " % rst)
            for n, _ in ports_in:
                f.write("%x " % ins[n])
            for n, _ in ports_out:
                f.write("%x " % outs[n])
            f.write("\n")
    inputs_decl = " ".join("uint64_t %s = 0;" % n for n, _ in (ports_in + ports_out))
    assigns = "\n    ".join("dut->%s = %s;" % (n, n) for n, _ in ports_in)
    cmp_code = "\n    ".join(
        'if (dut->%s != %s) { printf("MISMATCH %s cycle %%llu: got %%llx expected %%llx\\n", c, dut->%s, %s); fail = 1; }'
        % (n, n, name, n, n) for n, _ in ports_out)
    scanf_fmt = " ".join(["%llu"] + ["%llx"] * (len(ports_in) + len(ports_out)))
    scanf_vars = ", ".join(["&rst"] + ["&" + n for n, _ in ports_in] + ["&" + n for n, _ in ports_out])
    nfields = 1 + len(ports_in) + len(ports_out)
    has_clk = "clk" in modules[name][0]
    if has_clk:
        clk_lines = "        dut->clk = 0; dut->eval();\n        dut->clk = 1; dut->eval();"
        rst_line = "        dut->reset = rst;"
    else:
        clk_lines = "        dut->eval();"
        rst_line = ""
    tb = r'''
#include "V%s.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    V%s* dut = new V%s;
    FILE* f = fopen("%s", "r");
    if (!f) return 2;
    uint64_t rst; uint64_t c = 0; int fail = 0;
    %s
    while (fscanf(f, "%s", %s) == %d) {
        %s
        %s
        %s
        %s
        c++;
    }
    fclose(f);
    delete dut;
    printf(fail ? "\nFAIL\n" : "\nPASS\n");
    return fail;
}
''' % (name, name, name, stim_file, inputs_decl, scanf_fmt, scanf_vars, nfields, rst_line, assigns, clk_lines, cmp_code)
    tb_file = os.path.join(workdir, name + "_tb.cpp")
    with open(tb_file, "w") as f:
        f.write(tb)
    objdir = os.path.join(workdir, "obj_" + name)
    verilog_file = os.path.join(workdir, name + ".v")
    with open(verilog_file, "w") as f:
        f.write(modules[name][1])
    comp = subprocess.run(
        [VERILATOR, "--cc", "--exe", "-Wno-fatal", "--top-module", name,
         "-Mdir", objdir, "-o", name + "_tb", tb_file, verilog_file],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=workdir)
    if comp.returncode != 0:
        print("  [COMPILE FAIL] %s:\n%s" % (name, comp.stderr.decode("utf-8", "replace")[-1500:]))
        return None
    bld = subprocess.run(["make", "-C", objdir, "-f", "V%s.mk" % name],
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=workdir)
    if bld.returncode != 0:
        print("  [MAKE FAIL] %s:\n%s" % (name, bld.stderr.decode("utf-8", "replace")[-1500:]))
        return None
    runp = subprocess.run([os.path.join(objdir, name + "_tb")],
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=workdir)
    out = runp.stdout.decode("utf-8", "replace")
    if runp.returncode != 0 or "MISMATCH" in out:
        for ln in out.split("\n"):
            if "MISMATCH" in ln:
                print("  [%s]" % ln.strip())
        return False
    print("  [OK] %s" % name)
    return True


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    keep = "--keep" in sys.argv
    case_files = args or [os.path.join(CASE_DIR, c) for c in DEFAULT_CASES]
    if not os.path.exists(TYPORT):
        print("typort binary not found at %s (run cargo build --release --bin typort)" % TYPORT)
        sys.exit(1)
    if shutil.which(VERILATOR) is None:
        print("[SKIP] verilator not found — behavioral verification unavailable (L1/L2 still enforced)")
        sys.exit(0)
    workdir = os.path.join(ROOT, "tools", "spinalhdl-verify", "work") if keep else tempfile.mkdtemp(prefix="typort-verify-")
    os.makedirs(workdir, exist_ok=True)
    total = passed = failed = 0
    for cf in case_files:
        if not os.path.exists(cf):
            print("  [MISSING CASEFILE] %s" % cf)
            continue
        print("== cases: %s ==" % os.path.basename(cf))
        modules = run_typort(cf)
        for name, (ports_in, ports_out, ref, strategy) in CASES.items():
            if name not in modules:
                continue
            total += 1
            res = run_comb_case(name, ports_in, ports_out, ref, strategy, workdir, modules)
            if res is True:
                print("  [OK] %s" % name)
                passed += 1
            else:
                failed += 1
        for name, (ports_in, ports_out, ref, n_cycles) in SEQ_CASES.items():
            if name not in modules:
                continue
            total += 1
            res = run_seq_case(name, ports_in, ports_out, ref, n_cycles, workdir, modules)
            if res is True:
                passed += 1
            else:
                failed += 1
        for name, (ports_in, ports_out, ref, n_cycles) in MISC_SEQ_CASES.items():
            if name not in modules:
                continue
            total += 1
            res = run_seq_case(name, ports_in, ports_out, ref, n_cycles, workdir, modules)
            if res is True:
                passed += 1
            else:
                failed += 1
        for name, (ports_in, ports_out, ref, strategy) in MISC_CASES.items():
            if name not in modules:
                continue
            total += 1
            res = run_comb_case(name, ports_in, ports_out, ref, strategy, workdir, modules)
            if res is True:
                print("  [OK] %s" % name)
                passed += 1
            else:
                failed += 1
        for name, (ports_in, ports_out, ref, n_cycles) in STREAM_SEQ_CASES.items():
            if name not in modules:
                continue
            total += 1
            res = run_seq_case(name, ports_in, ports_out, ref, n_cycles, workdir, modules)
            if res is True:
                passed += 1
            else:
                failed += 1
        for name, (ports_in, ports_out, ref, n_cycles, clk_a, clk_b) in DUAL_CLOCK_CASES.items():
            if name not in modules:
                continue
            total += 1
            res = run_dualclock_case(name, ports_in, ports_out, ref, n_cycles, workdir, modules, clk_a, clk_b)
            if res is True:
                passed += 1
            else:
                failed += 1
    print("== %d passed, %d failed, %d total ==" % (passed, failed, total))
    if not keep:
        shutil.rmtree(workdir, ignore_errors=True)
    sys.exit(0 if failed == 0 else 1)


if __name__ == "__main__":
    main()
