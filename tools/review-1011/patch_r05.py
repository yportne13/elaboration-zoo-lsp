#!/usr/bin/env python3
"""One-off: fix round-5 generator call forms (adjudicated conventions)."""
import io

p = 'tools/review-1011/gen_r05.py'
s = io.open(p, encoding='utf-8').read()
NL = chr(92) + 'n'


def rep(tag, old, new):
    global s
    o = old.replace('@', NL)
    n = new.replace('@', NL)
    assert o in s, tag
    s = s.replace(o, n, 1)
    print('ok', tag)


rep('q01', 'add("q01_receiver_method", TC + "println(Doubles.dbl_val(4))@",',
    'add("q01_receiver_method", TC + "def useD0[T][d: Doubles[T]](t: T): Nat = d.dbl_val t@println(useD0(4))@",')
rep('tc1', '  def dbl_val(x: Nat): Nat@', '  def dbl_val: Nat@')
rep('tc2', '  def dbl_val(x: Nat): Nat = x + x@', '  def dbl_val: Nat = this + this@')
rep('q04', 'add("q04_default_method", "trait Greet {@  def hello(x: Nat): String = \\"hi\\"@}@impl Greet for Nat {@}@println(Greet.hello(1))@",',
    'add("q04_default_method", "trait Greet {@  def hello: String = \\"hi\\"@}@impl Greet for Nat {@}@def useG[T][d: Greet[T]](t: T): String = d.hello t@println(useG(1))@",')
rep('q05', 'add("q05_no_instance", "trait Marks {@  def mark(x: Boolean): Nat@}@impl Marks for Boolean {@  def mark(x: Boolean): Nat = 1@}@println(Marks.mark(true))@",',
    'add("q05_no_instance", "trait Marks {@  def mark: Nat@}@impl Marks for Boolean {@  def mark: Nat = 1@}@def tt0 = true@println(tt0.mark)@",')
rep('q07', 'd.dbl_val 6@', 'd.dbl_val t@')
rep('q08a', 'impl Doubles for Boolean {@  def dbl_val(x: Nat): Nat = x@}', 'impl Doubles for Boolean {@  def dbl_val: Nat = 1@}')
rep('q08b', 'd.dbl_val 7@', 'd.dbl_val t@')
rep('q09', 'def b: Box2[Nat] = mk(3)@', 'def b: Box2[Nat] = Box2.mk(3)@')
rep('q11a', '  def baseM(x: Nat): Nat@', '  def baseM: Nat@')
rep('q11b', '  def subM(x: Nat): Nat@', '  def subM: Nat@')
rep('q11c1', '  def baseM(x: Nat): Nat = 1@', '  def baseM: Nat = 1@')
rep('q11c2', '  def subM(x: Nat): Nat = 2@', '  def subM: Nat = 2@')
rep('q11d', 'println(Sub2.subM(0))@', 'def useS2[T][d: Sub2[T]](t: T): Nat = d.subM t@println(useS2(0))@')
rep('q12a', '  def baseM(x: Nat): Nat@', '  def baseM: Nat@')
rep('q12b', '  def subM(x: Nat): Nat@', '  def subM: Nat@')
rep('q12c1', '  def baseM(x: Nat): Nat = 1@', '  def baseM: Nat = 1@')
rep('q12c2', '  def subM(x: Nat): Nat = 2@', '  def subM: Nat = 2@')
rep('q12d', 'def wantBase[T][d: Base3[T]](t: T): Nat = d.baseM 9@', 'def wantBase[T][d: Base3[T]](t: T): Nat = d.baseM t@')
rep('q14', '"user operator trait ++ as infix (probe)", "error /error/")', '"user operator trait ++ as infix WORKS", "stdout /101/")')
rep('q35a', '  def ca_v(x: Nat): Nat@', '  def ca_v: Nat@')
rep('q35b', '  def cb_v(x: Nat): Nat@', '  def cb_v: Nat@')
rep('q35c', '  def ca_v(x: Nat): Nat = 1@', '  def ca_v: Nat = 1@')
rep('q35d', '  def cb_v(x: Nat): Nat = 2@', '  def cb_v: Nat = 2@')
rep('q35e', 'a.ca_v(0) + b.cb_v(0)@', 'a.ca_v t + b.cb_v t@')
rep('q37', 'println(SameN.m7(0))@println(m7(0))@', 'def zz: Nat = 0@println(zz.m7)@println(m7(0))@')
rep('q37a', '  def m7(x: Nat): Nat@', '  def m7: Nat@')
rep('q37b', '  def m7(x: Nat): Nat = 5@', '  def m7: Nat = 5@')
rep('q40a', '  def make(x: Nat): String@', '  def make: String@')
rep('q40b', '  def make(x: Nat): String = \\"made\\"@', '  def make: String = \\"made\\"@')
rep('q40c', 'd.make 0@', 'd.make t@')
rep('f54', 'println(TwoP.m2(1))@",', '@",')

io.open(p, 'w', encoding='utf-8', newline='\n').write(s)
print('patched all')
