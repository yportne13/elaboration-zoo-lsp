#!/usr/bin/env python3
"""One-off: round-8 second adjudication pass (11 remaining probes)."""
import io, re, ast

p = 'tools/review-1011/gen_r08.py'
s = io.open(p, encoding='utf-8').read()


def rep(tag, old, new):
    global s
    assert old in s, tag
    s = s.replace(old, new, 1)
    print('ok', tag)


# h04: +^ between two UInt signals (bare numeric literals are Nat)
rep('h04src', 'add("h04_inc_widen", "Inc9", "  let a = UInt[8]\\n  let s = UInt[9]\\n  s := a +^ 1\\n",',
    'add("h04_inc_widen", "Inc9", "  let a = UInt[8]\\n  let b = UInt[8]\\n  let s = UInt[9]\\n  s := a +^ b\\n",')
rep('h04e', '"+^ carries into a 9-bit result", "stdout +^")',
    '"+^ result is 9-bit wide", "stdout 9:0] s;")')
# h06: shift amount must be a UInt signal
rep('h06src', 'add("h06_shift", "Shift8", "  let a = UInt[8]\\n  let r = UInt[8]\\n  r := a |<< 2\\n",',
    'add("h06_shift", "Shift8", "  let a = UInt[8]\\n  let sh = UInt[8]\\n  let r = UInt[8]\\n  r := a |<< sh\\n",')
rep('h06e', '"variable/constant left shift", "stdout <<|shift")',
    '"left shift by a UInt signal", "stdout <<")')
# h14: async reset is posedge reset
rep('h14e', '"register with async reset value", "stdout negedge")',
    '"register with async reset value", "stdout posedge reset")')
# h18: canonical memory module
rep('h18src', 'add("h18_mem_write", "MemW", "  let m = memUInt(8, 16)\\n  let addr = UInt[4]\\n  let data = UInt[8]\\n  m.write(addr, data, literal(1))\\n",',
    'add("h18_mem_write", "MemW", "  input addr = UInt[8]\\n  input data = UInt[8]\\n  input en = Bool\\n  let m = memUInt(8, 16)\\n  m.write(addr, data, en)\\n",')
# h21: expand needs SInt output width +1
rep('h21src', 'add("h21_sign_extend", "Sxt8", "  let s = SInt[4]\\n  let w = SInt[8]\\n  w := s.expand\\n",',
    'add("h21_sign_extend", "Sxt8", "  input s = SInt[4]\\n  output w = SInt[5]\\n  w := s.expand\\n",')
# h23: two modules in one file (Top2 references Half8)
rep('h23src', 'add("h23_submodule", "Top2", "  let a = UInt[8]\\n  let s = UInt[8]\\n  let u = mkInstance(\\"u0\\", \\"Half8\\")\\n  s := a\\n}\\nprintln(moduleTreeVL(Top2.create.tree))\\n",',
    'add("h23_submodule", "Top2", "  input a = UInt[8]\\n  output s = UInt[8]\\n  let u = mkInstance(\\"u0\\", \\"Half8\\")\\n  s := a\\n}\\nmodule Half8 {\\n  input a = UInt[8]\\n  output s = UInt[8]\\n  s := a\\n}\\nprintln(moduleTreeVL(Top2.create.tree))\\n",')
rep('h23e', '"instance declaration (probe: needs Half8 defined below)", "error /error/")',
    '"instance declaration with a defined child module", "stdout Half8 u0(")')
# h24: input x = T syntax
rep('h24src', 'add("h24_port_directions", "Dirs", "  input let a = UInt[8]\\n  output let b = UInt[8]\\n  b := a\\n",',
    'add("h24_port_directions", "Dirs", "  input a = UInt[8]\\n  output b = UInt[8]\\n  b := a\\n",')
# h25: verdict from run: exit=1 -- read the actual error first; make it error
rep('h25e', '"UInt[8] + UInt[4] accepted (probe verdict)", "stdout 7:0] r;")',
    '"UInt[8] + UInt[4]: width mismatch is NOT auto-widened (probe verdict)", "error /error/")')
# h26: verdict: exit=1 -- undriven output errors
rep('h26e', '"undriven output accepted (probe verdict)", "stdout output")',
    '"undriven output rejected (probe verdict)", "error /error/")')
# h28: === may not be accepted in source; verdict from run exit=0 but no === in output
rep('h28e', '"=== equality", "stdout ===")',
    '"=== equality maps to Verilog ==", "stdout ==")')
# h30: a := b probe verdict: exit=1
rep('h30e', '"a := b direction probe verdict", "stdout assign a = b;")',
    '"driving an input port rejected (probe verdict)", "error /error/")')

io.open(p, 'w', encoding='utf-8', newline='\n').write(s)
ast.parse(s)
print('syntax ok')
