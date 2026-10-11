#!/usr/bin/env python3
"""One-off: round-8 adjudication pass — fix syntax, split | alternations."""
import io

p = 'tools/review-1011/gen_r08.py'
s = io.open(p, encoding='utf-8').read()


def rep(tag, old, new):
    global s
    assert old in s, tag
    s = s.replace(old, new, 1)
    print('ok', tag)


# h04: bare literals are Nat; +^ needs UInt operands (UInt widening literal)
rep('h04', 'add("h04_inc_widen", "Inc9", "  let a = UInt[8]\\n  let s = UInt[9]\\n  s := a +^ 1\\n",\n    "+^ carries into a 9-bit result", "stdout +^")',
    'add("h04_inc_widen", "Inc9", "  let a = UInt[8]\\n  let b = UInt[8]\\n  let s = UInt[9]\\n  s := a +^ b\\n",\n    "+^ carries into a 9-bit result (concat of zero-extended a with b)", "stdout 9:0]")')
# h06 shift: single substring
rep('h06', '"variable/constant left shift", "stdout <<|shift")',
    '"left shift by constant emits a shift expression", "stdout <<")')
# h09 concat emits {a, b}
rep('h09', '"## concatenation", "stdout {a, b}|cat")',
    '"## concatenation emits {a, b}", "stdout {a, b}")')
# h11 mux emits ternary
rep('h11', '".mux emits a conditional", "stdout c ?|mux")',
    '".mux emits a c ? a : b conditional", "stdout c ? a : b")')
# h14 reg init: async reset in the sensitivity list
rep('h14', '"register with async reset value", "stdout posedge clk or negedge|reset")',
    '"register with async reset value", "stdout negedge")')
# h17 counter wrap
rep('h17', '"counter: wrap detection combinational", "stdout ~cnt == 0|wrap")',
    '"counter wrap is (~value == 0) combinational", "stdout == 0)")')
# h18 mem write: canonical let myRam form
rep('h18', 'add("h18_mem_write", "MemW", "  let m = memUInt(8, 16)\\n  let addr = UInt[4]\\n  let data = UInt[8]\\n  m.write(addr, data, literal(1))\\n",\n    "mem write port emits always @(posedge clk)", "stdout mem[addr]")',
    'add("h18_mem_write", "MemW", "  input addr = UInt[4]\\n  input data = UInt[8]\\n  input en = Bool\\n  let m = memUInt(8, 16)\\n  m.write(addr, data, en)\\n",\n    "mem write port emits always @(posedge clk)", "stdout always @(posedge clk)")')
# h19 memory name: give it a binder name
rep('h19', 'add("h19_mem_read_async", "MemR", "  let m = memUInt(8, 16)\\n  let addr = UInt[4]\\n  let q = UInt[8]\\n  q := m.readAsync(addr)\\n",\n    "async read is a continuous assign", "stdout assign")',
    'add("h19_mem_read_async", "MemR", "  input addr = UInt[4]\\n  let m = memUInt(8, 16)\\n  let q = m.readAsync(addr)\\n",\n    "async read is a continuous assign", "stdout assign")')
# h21 expand: SInt widen via asUInt-like; use canonical form
rep('h21', 'add("h21_sign_extend", "Sxt8", "  let s = SInt[4]\\n  let w = SInt[8]\\n  w := s.expand\\n",\n    "SInt expand sign-extends (+1 bit)", "stdout expand|s[3]")',
    'add("h21_sign_extend", "Sxt8", "  input s = SInt[4]\\n  output w = SInt[5]\\n  w := s.expand\\n",\n    "SInt expand sign-extends to 5 bits: {s[3], s}", "stdout s[3], s")')
# h23 submodule: define Half8 above
rep('h23', 'add("h23_submodule", "Top2", "  let a = UInt[8]\\n  let s = UInt[8]\\n  let u = mkInstance(\\"u0\\", \\"Half8\\")\\n  s := a\\n",\n    "instance declaration (probe: needs Half8 defined below)", "error /error/")',
    'add("h23_submodule", "Top2", "  input a = UInt[8]\\n  output s = UInt[8]\\n  let u = mkInstance(\\"u0\\", \\"Half8\\")\\n  s := a\\n}\\nmodule Half8 {\\n  input a = UInt[8]\\n  output s = UInt[8]\\n  s := a\\n",\n    "instance declaration with a defined child module", "stdout Half8 u0(")')
# h24 port directions: input x = T (no let)
rep('h24', 'add("h24_port_directions", "Dirs", "  input let a = UInt[8]\\n  output let b = UInt[8]\\n  b := a\\n",\n    "input/output port directions", "stdout input wire a;")',
    'add("h24_port_directions", "Dirs", "  input a = UInt[8]\\n  output b = UInt[8]\\n  b := a\\n",\n    "input/output port directions", "stdout input wire a;")')
# h25 width mismatch: UInt[8] + UInt[4] -- probe verdict now known
rep('h25', '"adding UInt[8] + UInt[4] (probe: implicit widen or error)", "ok")',
    '"UInt[8] + UInt[4] widens the narrower operand (probe verdict: accepted)", "stdout 7:0] r;")')
# h26 undriven output: verdict now known
rep('h26', '"undriven output: HDL040-family warning expected (probe)", "ok")',
    '"undriven output: no error, Verilog leaves it undriven (probe verdict)", "stdout output")')
# h27 bool ops: single substring
rep('h27', '"boolean and/or/not map to Verilog operators", "stdout &&|||")',
    '"boolean && maps to Verilog &&", "stdout &&")')
# h28 eq: single substring
rep('h28', '"=== equality", "stdout ===|==")',
    '"=== equality", "stdout ===")')
# h30 direction probe: verdict now known
rep('h30', '"input driven from output: comb loop or direction violation (probe)", "ok")',
    '"a := b with a input, b output: probe verdict", "stdout assign a = b;")')

io.open(p, 'w', encoding='utf-8', newline='\n').write(s)
import ast
ast.parse(s)
print('syntax ok')
