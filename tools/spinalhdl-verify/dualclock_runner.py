"""Dual-clock behavioral verification runner for verify.py.

Drives clkA/clkB in lockstep (same phase); the reference state machine
updates both clock domains per step. Inputs are sampled on the clkA edge
(module main clock). Written as a separate module to avoid heredoc
backslash mangling inside verify.py.
"""

import os
import subprocess
import sys

# verilator binary (same resolution as verify.py)
VERILATOR = os.environ.get("VERILATOR_BIN", "verilator")


def run_dualclock_case(name, ports_in, ports_out, ref, n_cycles, workdir, modules, clk_a, clk_b):
    import random
    random.seed(11)
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
    clk_lines = (
        "        dut->%s = 0; dut->eval();\n" % clk_a
        + "        dut->%s = 0; dut->eval();\n" % clk_b
        + "        dut->%s = 1; dut->eval();\n" % clk_a
        + "        dut->%s = 1; dut->eval();" % clk_b)
    rst_line = "        dut->rstA = rst;\n        dut->rstB = rst;"
    if "rstA" not in modules[name][1]:
        rst_line = ""
    elif "rstB" not in modules[name][1]:
        rst_line = "        dut->rstA = rst;"
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
