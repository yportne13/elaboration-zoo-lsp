#!/usr/bin/env python3
"""Apply Raw::U span-carrying change to elaboration.rs and machine.rs."""
import io

# elaboration.rs (reference engine)
p = r'src/L13_namespace/elaboration.rs'
s = open(p, encoding='utf-8').read()
n = 0
for old, new in [
    ("                            Raw::U(0)\n", "                            Raw::U(0, empty_span(()))\n"),
    ("let typ = params.iter().rev().fold(Raw::U(universe_lvl), |a, b| {",
     "let typ = params.iter().rev().fold(Raw::U(universe_lvl, empty_span(())), |a, b| {"),
    ("Tm::U(u) => Some(Raw::U(*u)),", "Tm::U(u) => Some(Raw::U(*u, empty_span(()))),"),
]:
    assert old in s, old[:50]
    s = s.replace(old, new, 1)
    n += 1
io.open(p, 'w', encoding='utf-8', newline='\n').write(s)
print("elaboration.rs", n)

# machine.rs (twin engine)
p = r'src/L13_namespace/bump_spine_iter/machine.rs'
s = open(p, encoding='utf-8').read()
n = 0
old = "            Raw::U(x) => Ok((bump.alloc(Tm::U(*x)), v_u(x + 1))),"
new = (
    "            // checked_add: aligns with the reference elaboration.rs Raw::U arm --\n"
    "            // for Type 4294967295, x + 1 overflows u32 (debug panic /\n"
    "            // release silently wraps to Type 0). The F2 fix only landed in\n"
    "            // the reference engine; this twin arm kept the bare add. The\n"
    "            // error takes the twin's normal Error path; the span comes from\n"
    "            // the Raw::U node (the digit token of Type <num> in the parser).\n"
    "            Raw::U(x, u_span) => match x.checked_add(1) {\n"
    "                Some(lvl) => Ok((bump.alloc(Tm::U(*x)), v_u(lvl))),\n"
    "                None => Err(Error(u_span.map(|_| format!(\"universe level {x} is too large\")), vec![])),\n"
    "            },"
)
assert old in s
s = s.replace(old, new, 1)
n += 1
for old, new in [
    ("                            Raw::U(0)\n", "                            Raw::U(0, empty_span(()))\n"),
    (".fold(Raw::U(universe_lvl), |a, b| {", ".fold(Raw::U(universe_lvl, empty_span(())), |a, b| {"),
    ("CTm::U(u) => Some(Raw::U(*u)),", "CTm::U(u) => Some(Raw::U(*u, empty_span(()))),"),
]:
    assert old in s, old[:50]
    s = s.replace(old, new, 1)
    n += 1
io.open(p, 'w', encoding='utf-8', newline='\n').write(s)
print("machine.rs", n)
