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

DEFAULT_CASES = ["v_utils_combinational.typort", "v_utils_sequential.typort"]


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
        dut->reset = rst;
        %s
        dut->clk = 0; dut->eval();
        dut->clk = 1; dut->eval();
        %s
        c++;
    }
    fclose(f);
    delete dut;
    printf(fail ? "\nFAIL\n" : "\nPASS\n");
    return fail;
}
''' % (name, name, name, stim_file, inputs_decl, scanf_fmt, scanf_vars, nfields, assigns, cmp_code)
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
    print("== %d passed, %d failed, %d total ==" % (passed, failed, total))
    if not keep:
        shutil.rmtree(workdir, ignore_errors=True)
    sys.exit(0 if failed == 0 else 1)


if __name__ == "__main__":
    main()
