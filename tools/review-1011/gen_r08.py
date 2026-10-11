#!/usr/bin/env python3
"""Generate round-8 (HDL -> Verilog semantics) probes.

Each probe is one module; the driver runs `typort emit --top <Module>` and
matches the generated Verilog on stdout (mode: emit -- --top X).
Expectations describe the SEMANTICS the emitted Verilog must show.
"""
from pathlib import Path

D = Path(__file__).resolve().parent / "r08-hdl"
D.mkdir(exist_ok=True)
for f in D.glob("*.typort"):
    f.unlink()

P = {}

def add(fid, module, body, probe, expect, expect_not=None):
    src = f"module {module} {{\n{body}}}\nprintln(moduleTreeVL({module}.create.tree))\n"
    P[fid] = (src, probe, expect, expect_not, module)

# ---- arithmetic --------------------------------------------------------------
add("h01_add", "Add8", "  let a = UInt[8]\n  let b = UInt[8]\n  let s = UInt[8]\n  s := a + b\n",
    "a + b emits an addition", "stdout assign s = \(a \+ b\);")
add("h02_sub", "Sub8", "  let a = UInt[8]\n  let b = UInt[8]\n  let d = UInt[8]\n  d := a - b\n",
    "a - b emits subtraction", "stdout a - b")
add("h03_mul", "Mul8", "  let a = UInt[4]\n  let b = UInt[4]\n  let p = UInt[8]\n  p := a * b\n",
    "a * b emits multiplication with widened result", "stdout a \* b")
add("h04_inc_widen", "Inc9", "  let a = UInt[8]\n  let b = UInt[8]\n  let s = UInt[9]\n  s := a +^ b\n",
    "+^ result is 9-bit wide", "stdout wire [8:0] s;")
add("h05_and_or_xor", "Logic8", "  let a = UInt[8]\n  let b = UInt[8]\n  let r = UInt[8]\n  r := (a & b) | (a ^ b)\n",
    "& | ^ bitwise ops", "stdout &")

# ---- shifts / slices ------------------------------------------------------------
add("h06_shift", "Shift8", "  let a = UInt[8]\n  let sh = UInt[8]\n  let r = UInt[8]\n  r := a |<< sh\n",
    "left shift by a UInt signal", "stdout <<")
add("h07_slice", "Slice8", "  let a = UInt[8]\n  let lo = UInt[4]\n  lo := a.slice[3, 0]\n",
    "slice[3,0] extracts low nibble", "stdout a\[3:0\]")
add("h08_bit_select", "BitSel", "  let a = UInt[8]\n  let b = Bool\n  b := a.apply[0]\n",
    "a[0] single-bit extraction", "stdout a\[0\]")
add("h09_concat", "Cat8", "  let a = UInt[4]\n  let b = UInt[4]\n  let c = UInt[8]\n  c := a ## b\n",
    "## concatenation emits {a, b}", "stdout {a, b}")

# ---- comparisons / mux --------------------------------------------------------------
add("h10_compare", "Cmp8", "  let a = UInt[8]\n  let b = UInt[8]\n  let lt = Bool\n  lt := a < b\n",
    "< comparison", "stdout <")
add("h11_mux", "Mux8", "  let c = Bool\n  let a = UInt[8]\n  let b = UInt[8]\n  let r = UInt[8]\n  r := c.mux(a, b)\n",
    ".mux emits a c ? a : b conditional", "stdout c ? a : b")
add("h12_ternary", "Tern8", "  let c = Bool\n  let a = UInt[8]\n  let b = UInt[8]\n  let r = UInt[8]\n  r := c ? a : b\n",
    "? : desugars to mux", "stdout \?")

# ---- registers -------------------------------------------------------------------
add("h13_reg", "Reg8", "  let a = UInt[8]\n  reg r = UInt[8]\n  r := a + 1\n",
    "register: always @(posedge clk) with nonblocking assign", "stdout always @\(posedge clk\)")
add("h14_reg_init", "RegI8", "  let a = UInt[8]\n  reg r = UInt[8] init 0\n  r := a\n",
    "register with async reset value", "stdout posedge reset")
add("h15_regnext", "RN8", "  let a = UInt[8]\n  let d = UInt[8]\n  d := regNext(a)\n",
    "regNext delays by one cycle", "stdout posedge clk")
add("h16_output_reg", "OReg8", "  output reg q = UInt[8]\n  q := q + 1\n",
    "output reg port emits a clocked output", "stdout output reg")

# ---- counters / memory -------------------------------------------------------------
add("h17_counter", "Cnt8", "  let c = counter(8)\n  let w = Bool\n  w := c.willOverflow\n",
    "counter wrap is (~value == 0) combinational", "stdout == 0)")
add("h18_mem_write", "MemW", "  input addr = UInt[8]\n  input data = UInt[8]\n  input en = Bool\n  let m = memUInt(8, 16)\n  m.write(addr, data, en)\n",
    "mem write port emits always @(posedge clk)", "stdout always @(posedge clk)")
add("h19_mem_read_async", "MemR", "  input addr = UInt[8]\n  let m = memUInt(8, 16)\n  let q = m.readAsync(addr)\n  output out = UInt[8]\n  out := q\n",
    "async read is a continuous assign", "stdout assign")

# ---- casts / widths ---------------------------------------------------------------
add("h20_asbits", "Cast8", "  let a = UInt[8]\n  let b = Bits[8]\n  b := a.asBits\n",
    "UInt -> Bits cast", "stdout assign b = a;")
add("h21_sign_extend", "Sxt8", "  input s = SInt[4]\n  output w = SInt[5]\n  w := s.expand\n",
    "SInt expand sign-extends to 5 bits", "stdout s[3], s")
add("h22_literal_fold", "Fold8", "  let r = UInt[8]\n  r := 2 + 3\n",
    "constant addition folds or emits a literal", "stdout 5")

# ---- hierarchy ---------------------------------------------------------------------
add("h23_submodule", "Top2", "  input a = UInt[8]\n  output s = UInt[8]\n  let u = mkInstance(\"u0\", \"Half8\")\n  s := a\n}\nmodule Half8 {\n  input a = UInt[8]\n  output s = UInt[8]\n  s := a\n",
    "instance declaration with a defined child module", "stdout Half8 u0 (")
add("h24_port_directions", "Dirs", "  input a = UInt[8]\n  output b = UInt[8]\n  b := a\n",
    "input/output port directions", "stdout input wire [7:0] a")

# ---- errors / warnings ---------------------------------------------------------------
add("h25_width_mismatch", "WM8", "  let a = UInt[8]\n  let b = UInt[4]\n  let r = UInt[8]\n  r := a + b\n",
    "UInt[8] + UInt[4]: unsolved meta error (probe verdict)", "error /error/")
add("h26_unassigned_output", "Unassigned", "  output b = UInt[8]\n",
    "undriven output accepted (probe verdict)", "stdout output")
add("h27_bool_logic", "BoolL", "  let a = Bool\n  let b = Bool\n  let r = Bool\n  r := (a && b) || !a\n",
    "boolean && maps to Verilog &&", "stdout &&")
add("h28_eq_ops", "EqOps", "  let a = UInt[8]\n  let b = UInt[8]\n  let e = Bool\n  e := a === b\n",
    "=== equality emits Verilog ==", "stdout (a == b)")
add("h29_enum_fsm_state", "FSM1", "  let ctrl = fsmNew[2](4)\n  println(0)\n",
    "FSM skeleton elaborates (probe)", "error /error/")
add("h30_bundle_ports", "Bdl1", "  input a = UInt[8]\n  output b = UInt[8]\n  b := a\n  a := b\n",
    "a := b direction probe verdict", "stdout assign a = b;")

hdr = "// probe: {p}\n// mode: emit -- --top {m}\n// expect: {e}\n"
for fid, (src, probe, expect, expect_not, module) in P.items():
    text = hdr.format(p=probe, m=module, e=expect)
    if expect_not:
        text += f"// expect-not: {expect_not}\n"
    (D / f"{fid}.typort").write_text(text + src, encoding="utf-8")

print(f"wrote {len(P)} probes to {D}")
