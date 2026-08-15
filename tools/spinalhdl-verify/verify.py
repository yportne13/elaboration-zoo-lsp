#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
SpinalHDL lib 复刻 —— L3 行为验证（真值表/时序仿真）

驱动流程：
  1. 对每个验证用例 .typort 文件运行 `typort check`，抓取生成的 Verilog 模块
  2. 按 CASES 表解析端口与参考函数（Python 实现）
  3. 生成 C++ testbench + 激励文件（参考值），verilator 编译仿真
  4. 比对仿真输出与参考值，任何不一致 exit 1；仿真器缺失时打印跳过并 exit 0

用法：
  python3 tools/spinalhdl-verify/verify.py [--cases 文件1 文件2 ...] [--keep]
环境变量：
  TYPORT    typort 可执行路径（默认 target/release/typort）
  VERILATOR  verilator 路径（默认 verilator）
"""
import os, re, subprocess, sys, tempfile, shutil

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
TYPORT = os.environ.get("TYPORT", os.path.join(ROOT, "target", "release", "typort"))
VERILATOR = os.environ.get("VERILATOR", "verilator")
CASE_DIR = os.path.join(ROOT, "tools", "spinalhdl-verify", "cases")
WORK = os.path.join(ROOT, "tools", "spinalhdl-verify", "work")

# ---------------------------------------------------------------------------
# 参考实现（组合逻辑，输入/输出均为整数值）
# ---------------------------------------------------------------------------
def ref_reverse(a, w=8):
    v = f"{a:0{w}b}"[::-1]
    return int(v, 2)

def ref_proplsb(a, w=8):
    # out[i] = OR(in[i..w-1])
    out = 0
    for i in range(w):
        if ((a >> i) & 1) or (a >> i) != 0:  # placeholder
            pass
    out = 0
    for i in range(w):
        if (a >> i) != 0:
            out |= (1 << i)
    return out

def ref_propmsb(a, w=8):
    # out[i] = OR(in[0..i])
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
    # OR-per-bit：输出位 i = OR(输入线 k 的索引第 i 位为 1)
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
    if a == 0:
        return 0
    return a.bit_length() - 1

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
# 用例表：模块名 -> (输入端口, 输出端口, 参考函数, 采样策略)
# 输入端口: [(名, 位宽)]；输出端口: [(名, 位宽)]
# ---------------------------------------------------------------------------
def inp(*ports):
    return list(ports)

def outp(*ports):
    return list(ports)

CASES = {
    "vReverse":       (inp(("a", 8)), outp(("r", 8)), lambda d: [ref_reverse(d["a"])], "full"),
    "vReverseU":      (inp(("a", 8)), outp(("r", 8)), lambda d: [ref_reverse(d["a"])], "full"),
    "vPropLsb":       (inp(("a", 8)), outp(("r", 8)), lambda d: [ref_proplsb(d["a"])], "full"),
    "vPropMsb":       (inp(("a", 8)), outp(("r", 8)), lambda d: [ref_propmsb(d["a"])], "full"),
    "vCountOne":      (inp(("a", 8)), outp(("c", 4)), lambda d: [ref_popcount(d["a"])], "full"),
    "vCountOneU":     (inp(("a", 8)), outp(("c", 4)), lambda d: [ref_popcount(d["a"])], "full"),
    "vClz":           (inp(("a", 8)), outp(("c", 4)), lambda d: [ref_clz(d["a"])], "full"),
    "vCtz":           (inp(("a", 8)), outp(("c", 4)), lambda d: [ref_ctz(d["a"])], "full"),
    "vMajority":      (inp(("a", 7)), outp(("m", 1)), lambda d: [1 if ref_majority(d["a"]) else 0], "full"),
    "vUintToOh":      (inp(("a", 3)), outp(("oh", 8)), lambda d: [ref_uinttooh(d["a"])], "full"),
    "vUintToOhM1":    (inp(("a", 3)), outp(("oh", 8)), lambda d: [ref_uinttoohm1(d["a"])], "full"),
    "vOhToUInt":      (inp(("oh", 8)), outp(("idx", 3)), lambda d: [ref_ohtouint(d["oh"])], "full"),
    "vOhLegal":       (inp(("oh", 8)), outp(("legal", 1)), lambda d: [1 if ref_ohlegal(d["oh"]) else 0], "full"),
    "vOhFirst":       (inp(("oh", 8)), outp(("f", 8)), lambda d: [ref_ohfirst(d["oh"])], "full"),
    "vOhLast":        (inp(("oh", 8)), outp(("l", 8)), lambda d: [ref_ohlast(d["oh"])], "full"),
    "vOhRR":          (inp(("req", 4), ("pri", 4)), outp(("g", 4)), lambda d: [ref_ohrr(d["req"], d["pri"])], "full"),
    "vPriorityMux":   (inp(("sel", 4), ("a", 8), ("b", 8), ("c", 8), ("d", 8), ("dflt", 8)),
                      outp(("o", 8)), lambda d: [ref_prioritymux(d["sel"], [d["a"], d["b"], d["c"], d["d"]], d["dflt"])], "sample"),
    "vMuxOH":         (inp(("sel", 4), ("a", 8), ("b", 8), ("c", 8), ("d", 8)),
                      outp(("o", 8)), lambda d: [ref_prioritymux(d["sel"], [d["a"], d["b"], d["c"], d["d"]], d["a"])], "sample"),
    "vOhMuxOr":       (inp(("sel", 4), ("a", 8), ("b", 8), ("c", 8), ("d", 8)),
                      outp(("o", 8)), lambda d: [ref_ohmxuor(d["sel"], [d["a"], d["b"], d["c"], d["d"]])], "sample"),
    "vMinMax":        (inp(("a", 8), ("b", 8)), outp(("mn", 8), ("mx", 8)),
                      lambda d: [ref_min(d["a"], d["b"]), ref_max(d["a"], d["b"])], "sample"),
    "vClamp":         (inp(("a", 8), ("lo", 8), ("hi", 8)), outp(("cl", 8)),
                      lambda d: [ref_clamp(d["a"], d["lo"], d["hi"])], "sample"),
    "vGray":          (inp(("x", 8)), outp(("g", 8), ("back", 8)),
                      lambda d: [ref_togray(d["x"]), ref_fromgray(ref_togray(d["x"]))], "full"),
    "vEndianSwap":    (inp(("a", 16)), outp(("s", 16)), lambda d: [ref_endianswap(d["a"])], "full"),
    "vAddCarry":      (inp(("a", 8), ("b", 8)), outp(("sum", 8), ("carry", 1)),
                      lambda d: list(ref_addcarry(d["a"], d["b"])), "sample"),
    "vLog2Floor":     (inp(("a", 8)), outp(("lf", 3)), lambda d: [ref_log2floor(d["a"])], "full"),
    "vLog2Ceil":      (inp(("a", 8)), outp(("lc", 3)), lambda d: [ref_log2ceil(d["a"])], "full"),
    "vSetFromFirstOne": (inp(("a", 8)), outp(("s", 8)), lambda d: [ref_setfromfirstone(d["a"])], "full"),
    "vNapot":         (inp(("a", 4)), outp(("n", 5)), lambda d: [ref_napot(d["a"])], "full"),
    "vScrap":         (inp(("a", 8), ("sh", 3)), outp(("s", 8)), lambda d: [ref_scrap(d["a"], d["sh"])], "full"),
    "vCountOneOnEach": (inp(("a", 4)), outp(("c1", 3), ("c2", 3), ("c3", 3), ("c4", 3)),
                      lambda d: ref_countoneoneach(d["a"]), "full"),
}

DEFAULT_CASES = ["v_utils_combinational.typort"]


def run_typort(case_file):
    """运行 typort，返回 {模块名: Verilog 文本}"""
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


def gen_stimulus(ports_in, ports_out, ref, strategy):
    """生成激励：(输入行列表, 期望输出行列表)"""
    inputs = []; expected = []
    if strategy == "full":
        total = 1
        for _, w in ports_in:
            total *= (1 << w)
        limit = min(total, 200000)
        sweep = range(limit)
    else:
        import random
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


def gen_tb(module_name, ports_in, ports_out, stim_file):
    inputs = " ".join("uint64_t %s = 0;" % n for n, _ in ports_in)
    assigns = "\n    ".join("dut->%s = %s;" % (n, n) for n, _ in ports_in)
    reads = "".join("printf(\"%x\\n\", dut->%s);\n" % n for n, _ in ports_out)
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
    uint64_t a, b;
    while (fscanf(f, "%%llx %%llx", &a, &b) == 2) {
        (void)b;
        %s
        dut->eval();
        %s
    }
    fclose(f);
    delete dut;
    return 0;
}
''' % (module_name, module_name, module_name, stim_file, inputs, assigns, reads)
    return tb


def run_case(name, ports_in, ports_out, ref, strategy, workdir):
    stim = []
    inputs, expected = gen_stimulus(ports_in, ports_out, ref, strategy)
    stim_file = os.path.join(workdir, name + ".stim")
    with open(stim_file, "w") as f:
        for ins, exps in zip(inputs, expected):
            f.write(ins + " " + exps + "\n")
    # 简化：激励只含输入；期望值在 python 侧比对
    with open(stim_file, "w") as f:
        for ins in inputs:
            f.write(ins + "\n")
    # 生成 testbench（读一行输入，打一行输出）
    inputs_decl = " ".join("uint64_t %s;" % n for n, _ in ports_in)
    scanf = " ".join(["%llx"] * len(ports_in))
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
''' % (name, name, name, stim_file, inputs_decl, scanf, scanf_vars, len(ports_in), assigns, reads)
    tb_file = os.path.join(workdir, name + "_tb.cpp")
    with open(tb_file, "w") as f:
        f.write(tb)
    # 编译
    objdir = os.path.join(workdir, "obj_" + name)
    verilog_file = os.path.join(workdir, name + ".v")
    module_vl = modules[name][1]
    with open(verilog_file, "w") as f:
        f.write(module_vl)
    comp = subprocess.run(
        [VERILATOR, "--cc", "--exe", "-Wno-fatal",
         "--top-module", name, "-Mdir", objdir, "-o", name + "_tb",
         tb_file, verilog_file],
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
            ok = False; break
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


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    keep = "--keep" in sys.argv
    case_files = args or [os.path.join(CASE_DIR, c) for c in DEFAULT_CASES]
    if not os.path.exists(TYPORT):
        print("typort binary not found at %s (run cargo build --release --bin typort)" % TYPORT)
        sys.exit(1)
    if shutil.which(VERILATOR) is None:
        print("[SKIP] verilator not found — behavioral verification unavailable (structural L1/L2 still enforced by tests)")
        sys.exit(0)
    workdir = WORK if keep else tempfile.mkdtemp(prefix="typort-verify-")
    os.makedirs(workdir, exist_ok=True)
    total = passed = failed = 0
    for cf in case_files:
        print("== cases: %s ==" % os.path.basename(cf))
        global modules
        modules = run_typort(cf)
        for name, (ports_in, ports_out, ref, strategy) in CASES.items():
            if name not in modules:
                print("  [MISSING] module %s not emitted by typort" % name)
                failed += 1; total += 1
                continue
            total += 1
            res = run_case(name, ports_in, ports_out, ref, strategy, workdir)
            if res is True:
                print("  [OK] %s" % name)
                passed += 1
            elif res is False:
                failed += 1
            else:
                failed += 1
    print("== %d passed, %d failed, %d total ==" % (passed, failed, total))
    if not keep:
        shutil.rmtree(workdir, ignore_errors=True)
    sys.exit(0 if failed == 0 else 1)


modules = {}
if __name__ == "__main__":
    main()
