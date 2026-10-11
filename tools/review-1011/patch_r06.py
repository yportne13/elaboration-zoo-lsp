#!/usr/bin/env python3
"""One-off: add missing ; rule separators + adjudicated expectation fixes in gen_r06."""
import io

p = 'tools/review-1011/gen_r06.py'
s = io.open(p, encoding='utf-8').read()
NL = chr(92) + 'n'


def rep(tag, old, new):
    global s
    o = old.replace('@', NL)
    n = new.replace('@', NL)
    assert o in s, tag
    s = s.replace(o, n, 1)
    print('ok', tag)


# rule-separator semicolons (parser: many1_sep((kw(Semi), EndLine.option())))
rep('x03', '($e:raw) => {@    def r2: Nat = $e + $e@  }@}', '($e:raw) => {@    def r2: Nat = $e + $e@  };@}')
rep('x06', '(a) => { def picked: Nat = 1 }@  (b) => { def picked: Nat = 2 }@}', '(a) => { def picked: Nat = 1 };@  (b) => { def picked: Nat = 2 };@}')
rep('x07', '($x:ident) => { def fm_r: Nat = 1 }@  (zz) => { def fm_r: Nat = 2 }@}', '($x:ident) => { def fm_r: Nat = 1 };@  (zz) => { def fm_r: Nat = 2 };@}')
rep('x08', '($p:param) => {@    def fnm: Nat -> Nat = $p@  }@}', '($p:param) => {@    def fnm: Nat -> Nat = $p@  };@}')
rep('x13', '($n:ident) => { def $n: Nat = 9 }@}', '($n:ident) => { def $n: Nat = 9 };@}')
rep('x13b', '($m:ident) => { inner $m }@}', '($m:ident) => { inner $m };@}')
rep('x15', '($n:ident) => { def $n: Nat = 1 }@}', '($n:ident) => { def $n: Nat = 1 };@}')
rep('x17', '($n:ident) => { println(stringify $n) }@}', '($n:ident) => { println(stringify $n) };@}')
rep('x25', '($n:ident) => { def $n: Nat = 6 }@}', '($n:ident) => { def $n: Nat = 6 };@}')
rep('x26', '($a:ident, $b:ident) => { def $a: Nat = 1 def $b: Nat = 2 }@}', '($a:ident, $b:ident) => { def $a: Nat = 1; def $b: Nat = 2 };@}')
rep('x27', '($n:ident) => { def $n: Nat = 11 }@}', '($n:ident) => { def $n: Nat = 11 };@}')
rep('x29', '(a) => { def nat_add: Nat = 50 }@}', '(a) => { def nat_add: Nat = 50 };@}')
rep('x31', '($n:ident) => { def $n: Nat = 1 def $n: Nat = 2 }@}', '($n:ident) => { def $n: Nat = 1; def $n: Nat = 2 };@}')
rep('x32', '($e:raw) => { def mlr: Nat = $e }@}', '($e:raw) => { def mlr: Nat = $e };@}')
rep('x33', '($n:ident) => { def $n: Nat = match 1 {@  case zero => 0@  case succ(m) => m@} }@}', '($n:ident) => { def $n: Nat = match 1 {@  case zero => 0@  case succ(m) => m@} };@}')
rep('x35', '($n:ident) => { def $n: Nat = 2 }@}', '($n:ident) => { def $n: Nat = 2 };@}')

# adjudicated expectation fixes
rep('x12e', '"expression-position macro (probe: bare () => 5)", "error /error/")',
    '"expression-position macro WORKS (bare () => { 5 } body)", "stdout /5/")')
rep('x19e', '"unknown fragment kind errors", "error /error/")',
    '"unknown fragment kind is silently accepted, rule never matches (quirk)", "ok")')
rep('x21e', '"empty transcriber arm (probe)", "ok")',
    '"empty transcriber arm is a parse error", "error /error/")')
rep('x28e', '"stringify on a number (probe)", "ok")',
    '"stringify needs an identifier; numbers error", "error /error/")')
rep('x33e', '"macro-expanded match keeps arm layout", "stdout /1/")',
    '"macro-expanded match: succ(zero) binds m=zero, prints 0", "stdout /0/")')
rep('x34e', '"self-referential macro must hit the depth limit, not hang", "timeout")',
    '"self-referential macro hits the depth limit (256) immediately", "error /too deep/")')
rep('x26e', '"two-parameter macro (probe comma form)", "error /error/")',
    '"two-parameter macro with ; inside transcriber", "stdout /1/")')

io.open(p, 'w', encoding='utf-8', newline='\n').write(s)
print('patched all')
