use super::*;

#[test]
fn test_trait() {
    let input = r#"
def outParam[A](a: A): A = a

enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

def two = succ (succ zero)

trait Say {
    def say(x: Nat): String
}

impl[T] Say for T {
    def say(x: Nat): String = "hello"
}

println (zero.say zero)

def not(x: Bool): Bool =
    match x {
        case true => false
        case false => true
    }

println (not true)

trait ToString {
    def to_string: String
}

impl ToString for Bool {
    def to_string: String =
        match this {
            case true => "true"
            case false => "false"
        }
}

def t[T][s: ToString[T]](x: T): String =
    s.to_string x

println (t true)

trait Add[T, O: outParam(Type 0)] {
    def +(that: T): O
}

def nat_add_helper(x: Nat, y: Nat): Nat =
    match y {
        case zero => x
        case succ(n) => succ (nat_add_helper x n)
    }

impl Add[Nat, Nat] for Nat {
    def +(that: Nat): Nat =
        nat_add_helper this that
}

def mul(x: Nat, y: Nat) = match x {
    case zero => zero
    case succ(n) => y + (mul n y)
}

def four = two + two

println four

struct Point[T] {
    x: T
    y: T
}

def get_x[T](p: Point[T]): T = p.x

impl Add[Point[Nat], Point[Nat]] for Point[Nat] {
    def +(that: Point[Nat]): Point[Nat] =
        new Point(this.x + that.x, this.y + that.y)
}

impl Add[Nat, Point[Nat]] for Point[Nat] {
    def +(that: Nat): Point[Nat] =
        new Point(this.x + that, this.y + that)
}

def start_point = new Point(zero, four)

def end_point = new Point(four, two)

println (get_x start_point)

println (start_point + end_point)

def test0: Type 1 = Type 0

def test1: Type 2 = Type 1 -> Type 0

enum HighLvl[A] {
    case1(a: A)
    case2(a: test1)
}

def test2: HighLvl[Nat] = case1 zero

def test3: Type 2 = HighLvl[Nat]

enum HighLvl2[A: Type 2] {
    case2_1(x: A)
    case2_2(x: Nat)
}

def test1_2: HighLvl2[HighLvl[Nat]] = case2_1 test2

def test1_3: Type 2 = HighLvl2[HighLvl[Nat]]

enum HighLvl3[A: Type 2] {
    case3_1
    case3_2(x: Nat)
}

def test2_2: HighLvl3[HighLvl[Nat]] = case3_1

def test2_3: Type 2 = HighLvl3[HighLvl[Nat]]

def Eq[A](x: A, y: A) = (P : A -> Type 0) -> P x -> P y

def refl[A, x: A]: Eq[A] x x = _ => px => px

struct Bits {
    name: String
    size: Nat
}

def get_name(x: Bits) = x.name

def assign(a: Bits, b: Bits)(eq: Eq[Nat] a.size b.size): String = a.name

def sigA = new Bits("A", four)

def sigB = new Bits("B", four)

def sigC = new Bits("C", two)

def sigD = new Bits("D", two)

def ab = assign sigA sigB refl

def cd = assign sigC sigD refl

"#;
    let result = run(input, 0).unwrap();
    println!("{}", result);
    assert!(result.contains("hello"));
    assert!(result.contains("Bool::false"));
    assert!(result.contains("true"));
    assert!(result.contains("4"));
    assert!(result.contains("0"));
    assert!(result.contains("Point[Nat]::Point.mk(4, 6)"));
}

#[test]
fn test5() {
    let input = r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

def t[len: Nat](x: Vec[Nat] len, y: Vec[Nat] len): Vec[Nat] (succ len) =
    match x {
        case nil => cons zero nil
        case cons(x, xs) => match y {
            case cons(y, ys) => cons(x, t xs ys)
        }
    }

impl[T, len: Nat] Vec[T](len) {
    def map[U](f: T -> U): Vec[U] len =
        match this {
            case nil => nil
            case cons(x, xs) => cons(f x, xs.map f)
        }
}

def tt = cons(zero, cons(zero, nil)).map[U=Nat](x => match x {
    case succ(z) => succ(zero)
    case zero => zero
})

def z[len: Nat](x: Vec[Nat]len) = match x {
    case nil => 1
    case cons[l=lll](x, xs) => lll
}

"#;
    println!("{}", run(input, 0).unwrap());
}

#[test]
fn test6() {
    let input = r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

def t[len: Nat](x: Vec[Nat] len, y: Vec[Nat] len): Vec[Nat] (succ len) =
    match x {
        case nil => cons zero nil
        case cons(x, xs) => match y {
            case cons(y, ys) => match t xs ys {
                case cons(z, zs) => cons(zero, cons zero zs)
            }
        }
    }

def ttt =
    let useless1 = create_global "Nat" 2;
    let useless2 = change_mutable("Nat", z => succ(z));
    get_global "Nat"

println ttt

println stringify t123

macro_rules module {
    ($name: ident $body: raw) => {def $name = string_concat(string_concat("module ", stringify $name), $body)};
    ($name: ident) => {def $name = string_concat("module ", stringify $name)};
}

module test1 " {}"

println test1

module test2

println test2

"#;
    println!("{}", run(input, 0).unwrap());
}

#[test]
fn test4() {
    let input = r#"
enum Nat {
    zero
    succ(x: Nat)
}

def add(x: Nat, y: Nat) =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def mul(x: Nat, y: Nat) =
    match x {
        case zero => zero
        case succ(n) => add(y, mul n y)
    }

enum Eq[A](x: A, y: A) {
    refl(a: A) -> Eq a a
}

def rfl[A][a: A]: Eq a a =
    refl a

def cong[A, B, f: A -> B, x: A, y: A](e: Eq x y): Eq (f x) (f y) =
    match e {
        case refl(a) => refl (f a)
    }

def cong_succ[x: Nat, y: Nat](e: Eq x y): Eq (succ x) (succ y) =
    cong[Nat][Nat][succ][x][y] e

def add_zero_right(a: Nat): Eq (add a zero) a =
    match a {
        case zero => refl zero
        case succ(t) => cong_succ (add_zero_right t)
    }

def symm[A, x, y: A](e: Eq[A] x y): Eq[A] y x =
    match e {
        case refl(a) => refl[A] a
    }

def trans[A, x, y, z: A](e1: Eq[A] x y, e2: Eq[A] y z): Eq[A] x z =
    match e1 {
        case refl(a) => e2
    }

def add_succ_right (n: Nat, m: Nat): Eq (add (n, succ m)) (succ (add n m)) =
    match n {
        case zero => refl[Nat] (succ m)
        case succ(k) => cong_succ (add_succ_right k m)
    }

def add_comm (n: Nat, m: Nat): Eq (add n m) (add m n) =
    match n {
        case zero => symm (add_zero_right m)
        case succ(k) => trans (cong_succ (add_comm k m)) (symm (add_succ_right m k))
    }

def add_assoc (n: Nat, m: Nat, k: Nat): Eq (add (add n m) k) (add(n, add m k)) =
    match n {
        case zero => rfl
        case succ(l) => cong_succ (add_assoc l m k)
    }

def double(n: Nat): Nat = add n n

def double_pow(k: Nat, n: Nat): Nat =
    match k {
        case zero => n
        case succ(k) => double(double_pow k n)
    }

def double_add(a: Nat, b: Nat): Eq(double(add a b), add(double a, double b)) =
    let e1 = add_assoc(a, b, add a b);
    let e2 = cong[f=add a](add_comm (b, add a b));
    let e3 = symm (add_assoc (a, add a b, b));
    let e4 = symm (cong[f=x => add x b] (add_assoc a a b));
    let e5 = add_assoc (add a a) b b;
    trans(e1, trans(e2, trans(e3, trans e4 e5)))

def prove(k: Nat, a: Nat, b: Nat): Eq(double_pow(k, add a b), add (double_pow k a) (double_pow k b)) =
    match k {
        case zero => rfl
        case succ(kk) => let ih = prove kk a b;
            let ih1 = cong[f=double] ih;
            let ih2 = double_add(double_pow(kk, a), double_pow(kk, b));
            trans ih1 ih2
    }
"#;
    let result = run(input, 0).unwrap();
    println!("{}", result);
    println!("success");
}

#[test]
fn test2() {
    let input = r#"
enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

def listid(x: List[Bool]): List[Bool] = x

def create0: List[Bool] = nil

def create1: List[Bool] = cons true nil

def create2: List[Bool] = cons (true, cons false nil)

def two = succ (succ zero)

def not(x: Bool): Bool =
    match x {
        case true => false
        case false => true
    }

println (not true)

def add(x: Nat, y: Nat) =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def mul(x: Nat, y: Nat) = match x {
    case zero => zero
    case succ(n) => add (y, mul n y)
}

def four = add two two

println four

struct Point[T] {
    x: T
    y: T
}

def get_x[T](p: Point[T]): T = p.x

def point_add(p1: Point[Nat], p2: Point[Nat]): Point[Nat] =
    new Point((add p1.x p2.x), (add p1.y p2.y))

def start_point = new Point(zero, four)

def end_point = new Point(four, two)

println (get_x start_point)

println (point_add start_point end_point)

def test0: Type 1 = Type 0

def test1: Type 2 = Type 1 -> Type 0

enum HighLvl[A] {
    case1(a: A)
    case2(a: test1)
}

def test2: HighLvl[Nat] = case1 zero

def test3: Type 2 = HighLvl[Nat]

enum HighLvl2[A: Type 2] {
    case2_1(x: A)
    case2_2(x: Nat)
}

def test1_2: HighLvl2[HighLvl[Nat]] = case2_1 test2

def test1_3: Type 2 = HighLvl2[HighLvl[Nat]]

enum HighLvl3[A: Type 2] {
    case3_1
    case3_2(x: Nat)
}

def test2_2: HighLvl3[HighLvl[Nat]] = case3_1

def test2_3: Type 2 = HighLvl3[HighLvl[Nat]]

def Eq[A](x: A, y: A) = (P : A -> Type 0) -> P x -> P y

def refl[A, x: A]: Eq[A] x x = _ => px => px

struct Bits {
    name: String
    size: Nat
}

def get_name(x: Bits) = x.name

def assign(a: Bits, b: Bits)(eq: Eq[Nat] a.size b.size): String = a.name

def sigA = new Bits("A", four)

def sigB = new Bits("B", four)

def sigC = new Bits("C", two)

def sigD = new Bits("D", two)

def ab = assign sigA sigB refl

def cd = assign sigC sigD refl

"#;
    let result = run(input, 0).unwrap();
    println!("{}", result);
    assert!(result.contains("Bool::false"));
    assert!(result.contains("4"));
    assert!(result.contains("0"));
    assert!(result.contains("Point[Nat]::Point.mk(4, 6)"));
    let input = r#"
enum Nat {
    zero
    succ(x: Nat)
}

def test1: Type 2 = Type 1 -> Type 0

struct HighLvl[A] {
    case1: A
    case2: test1
}

def test2_t: Type 1 -> Type 0 = t => Nat

def test2: HighLvl[Nat] = new HighLvl(zero, test2_t)

def test3: Type 2 = HighLvl[Nat]

struct HighLvl2[A: Type 2] {
    case2_1: A
    case2_2: Nat
}

def test1_2: HighLvl2[HighLvl[Nat]] = new HighLvl2(test2, zero)

def test1_3: Type 2 = HighLvl2[HighLvl[Nat]]

struct HighLvl3[A: Type 2] {
    case3_1: Nat
    case3_2: Nat
}

def test2_2: HighLvl3[HighLvl[Nat]] = new HighLvl3(zero, zero)

def test2_3: Type 2 = HighLvl3[HighLvl[Nat]]
"#;
    let result = run(input, 0).unwrap();
    println!("{}", result);
    println!("success");
}

#[test]
fn test0() {
    let input = r#"
enum Eq[A](x: A, y: A) {
    refl[a: A] -> Eq[A] a a
}

enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

enum Product[A, B] {
    product(a: A, b: B)
}

def half_adder(lhs: Bool, rhs: Bool): Product[Bool][Bool] =
    match lhs {
        case false => product false rhs
        case true => match rhs {
            case false => product false true
            case true => product true false
        }
    }

def full_adder(lhs: Bool, rhs: Bool, carrier: Bool): Product[Bool][Bool] =
    match lhs {
        case false => half_adder rhs carrier
        case true => match rhs {
            case false => half_adder true carrier
            case true => product true carrier
        }
    }

def bits_adder_carrier[len: Nat](lhs: Vec[Bool] len, rhs: Vec[Bool] len, carrier: Bool): Vec[Bool] (succ len) =
    match lhs {
        case nil => cons carrier nil
        case cons(n, taill) => match rhs {
            case cons(m, tailr) => match bits_adder_carrier taill tailr carrier {
                case cons(c, tail) => match full_adder n m c {
                    case product(a, b) => cons (a, cons b tail)
                }
            }
        }
    }

def bits_adder[len: Nat](lhs: Vec[Bool] len, rhs: Vec[Bool] len): Vec[Bool] (succ len) =
    bits_adder_carrier lhs rhs false

println bits_adder (cons true nil) (cons false nil)
"#;
    let result = run(input, 0).unwrap();
    println!("{}", result);
    assert!(result.contains("Vec[Bool]::cons(1, Bool::false, Vec[Bool]::cons(0, Bool::true, Vec[Bool]::nil)"));
}

#[test]
pub fn test_index() {
    let input = r#"
enum Eq[A](x: A, y: A) {
    refl[a: A] -> Eq[A] a a
}

enum Nat {
    zero
    succ(x: Nat)
}

def two = succ (succ zero)

def three = succ (succ (succ zero))

def test: Eq two two = refl

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

def t = cons (zero, cons(two, cons(three, cons two nil)))

println t.len

def head[T, L: Nat](x: Vec[T] (succ L)): T =
    match x {
        case cons(x, _) => x
    }

println (head (cons zero nil))

def length[T, l: Nat](x: (Vec[T] l)): Nat =
    match x {
        case nil => zero
        case cons(_, xs) => succ (xs.len)
    }

    "#;
    let result = run(input, 0).unwrap();
    println!("{}", result);
    assert!(result.contains("4"));
    assert!(result.contains("0"));
}

#[test]
fn test7() {
    let input = r#"
enum Eq[A](x: A, y: A) {
    refl[a: A] -> Eq[A] a a
}

enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

enum Product[A, B] {
    product(a: A, b: B)
}

def half_adder(lhs: Bool, rhs: Bool): Product[Bool][Bool] =
    match lhs {
        case false => product false rhs
        case true => match rhs {
            case false => product false true
            case true => product true false
        }
    }

def full_adder(lhs: Bool, rhs: Bool, carrier: Bool): Product[Bool][Bool] =
    match lhs {
        case false => half_adder rhs carrier
        case true => match rhs {
            case false => half_adder true carrier
            case true => product true carrier
        }
    }

def bits_adder_carrier[len: Nat](lhs: Vec[Bool] len, rhs: Vec[Bool] len, carrier: Bool): Vec[Bool] (succ len) =
    match lhs {
        case nil => cons carrier nil
        case cons[_](n, taill) => match rhs {
            case cons[_](m, tailr) => match bits_adder_carrier taill tailr carrier {
                case cons[_](c, tail) => match full_adder n m c {
                    case product(a, b) => cons(a, cons b tail)
                }
            }
        }
    }

def bits_adder[len: Nat](lhs: Vec[Bool] len, rhs: Vec[Bool] len): Vec[Bool] (succ len) =
    bits_adder_carrier lhs rhs false

println bits_adder (cons true nil) (cons false nil)"#;
    let result = run(input, 0).unwrap();
    println!("{}", result);
    assert!(result.contains("Vec[Bool]::cons(1, Bool::false, Vec[Bool]::cons(0, Bool::true, Vec[Bool]::nil)"));
}

#[test]
fn test8() {
    let input = r#"
enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

enum Eq[T](x: T, y: T) {
    refl(a: T) -> Eq a a
}

def rfl[A][a: A]: Eq a a =
    refl a

def listid(x: List[Bool]): List[Bool] = x

def create0: List[Bool] = nil

def create1: List[Bool] = cons true nil

def create2: List[Bool] = cons(true, cons false nil)

def two = succ (succ zero)

def not(x: Bool): Bool =
    match x {
        case true => false
        case false => true
    }

println (not true)

def add(x: Nat, y: Nat) =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def mul(x: Nat, y: Nat) = match x {
    case zero => zero
    case succ(n) => add(y, mul n y)
}

def four = add two two

println four

def cong[A, B, f: A -> B, x: A, y: A](e: Eq x y): Eq (f x) (f y) =
    match e {
        case refl(a) => refl (f a)
    }

def cong_succ[x: Nat, y: Nat](e: Eq x y): Eq (succ x) (succ y) =
    cong[Nat][Nat][succ][x][y] e

def add_zero_right(a: Nat): Eq (add a zero) a =
    match a {
        case zero => refl zero
        case succ(t) => cong_succ (add_zero_right t)
    }

def symm[A, x, y: A](e: Eq[A] x y): Eq[A] y x =
    match e {
        case refl(a) => refl[A] a
    }

def trans[A, x, y, z: A](e1: Eq[A] x y, e2: Eq[A] y z): Eq[A] x z =
    match e1 {
        case refl(a) => e2
    }

def add_succ_right (n: Nat, m: Nat): Eq[Nat] (add(n, succ m)) (succ (add n m)) =
    match n {
        case zero => refl[Nat] (succ m)
        case succ(k) => cong_succ (add_succ_right k m)
    }

def add_comm (n: Nat, m: Nat): Eq[Nat] (add n m) (add m n) =
    match n {
        case zero => symm (add_zero_right m)
        case succ(k) => trans (cong_succ (add_comm k m)) (symm (add_succ_right m k))
    }

def add_assoc (n: Nat, m: Nat, k: Nat): Eq[Nat] (add (add n m) k) (add(n, add m k)) =
    match n {
        case zero => rfl
        case succ(l) => cong_succ (add_assoc l m k)
    }

def add_zero_left(m: Nat): Eq[Nat] (add zero m) m =
    rfl

def mul_zero_right(n: Nat): Eq[Nat] (mul n zero) zero =
    match n {
        case zero => rfl
        case succ(k) => trans (refl (add(zero, mul k zero))) (mul_zero_right k)
    }

def add_succ_zero_left(k: Nat): Eq[Nat] (add (succ zero) k) (succ k) =
    cong_succ (add_zero_left k)

def mul_one_right(n: Nat): Eq[Nat] (mul (n, succ zero)) n =
    match n {
        case zero => rfl[Nat][zero]
        case succ(k) =>
            let ih = mul_one_right k;
            let lemma: Eq[Nat] (add (succ zero) k) (succ k) = cong_succ (add_zero_left k);
            trans (cong[Nat][Nat][add (succ zero)][mul (k, succ zero)][k] ih) lemma
    }

struct Exists[A: Type 0, P: A -> Type 0] {
    witness: A
    proof: P witness
}

def exists_two: Exists[Nat][x => Eq x two] = Exists.mk[Nat][x => Eq x two] two rfl

struct Point[T] {
    x: T
    y: T
}

def get_x[T](p: Point[T]): T = p.x

def point_add(p1: Point[Nat], p2: Point[Nat]): Point[Nat] =
    new Point((add p1.x p2.x), (add p1.y p2.y))

def start_point = new Point(zero, four)

def end_point = new Point(four, two)

println (get_x start_point)

println (point_add start_point end_point)

def test0: Type 1 = Type 0

def test1: Type 2 = Type 1 -> Type 0

enum HighLvl[A] {
    case1(x: A)
    case2(x: test1)
}

def test2: HighLvl[Nat] = case1 zero

def test3: Type 2 = HighLvl[Nat]

enum HighLvl2[A: Type 2] {
    case2_1(x: A)
    case2_2(x: Nat)
}

def test1_2: HighLvl2[HighLvl[Nat]] = case2_1 test2

def test1_3: Type 2 = HighLvl2[HighLvl[Nat]]

enum HighLvl3[A: Type 2] {
    case3_1
    case3_2(x: Nat)
}

def test2_2: HighLvl3[HighLvl[Nat]] = case3_1

def test2_3: Type 2 = HighLvl3[HighLvl[Nat]]

struct Bits {
    name: String
    size: Nat
}

def assign(a: Bits, b: Bits)(eq: Eq[Nat] a.size b.size): String = string_concat a.name b.name

def sigA = new Bits("A", four)

def sigB = new Bits("B", four)

def sigC = new Bits("C", two)

def sigD = new Bits("D", two)

def ab = assign sigA sigB rfl

def cd = assign sigC sigD rfl

def three = add(two, succ zero)

println 5
"#;
    let result = run(input, 0).unwrap();
    println!("{}", result);
    assert!(result.contains("Bool::false"));
    assert!(result.contains("4"));
    assert!(result.contains("0"));
    assert!(result.contains("Point[Nat]::Point.mk(4, 6)"));
    assert!(result.contains("5"));
}

#[test]
fn test_hdl_basic_types() {
    let input = r#"
module Test {
    let a = UInt[8]
    let b = UInt[8]
    let c = SInt[16]
    let d = Bits[32]
    let e = Bool
    let f = Bits[33]
    f := e ## d
}
"#;
    match run_with_prelude(input) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_arithmetic() {
    let input = r#"
module Test[w: Nat] {
    let a = UInt[w]
    let b = UInt[w]
    let sum = UInt[w]
    let carry = UInt[w + 1]
    sum := a + b
    carry := a +^ b
}
"#;
    match run_with_prelude(input) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_bitwise_ops() {
    let input = r#"
module Test[w: Nat] {
    let a = Bits[w]
    let b = Bits[w]
    let and_result = Bits[w]
    let or_result = Bits[w]
    let xor_result = Bits[w]
    and_result := a & b
    or_result := a | b
    xor_result := a ^ b
}
"#;
    match run_with_prelude(input) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_comparisons() {
    let input = r#"
module Test[w: Nat] {
    let a = UInt[w]
    let b = UInt[w]
    let lt = Bool
    let eq = Bool
    lt := a < b
    eq := a === b
}

println(moduleVL(Test[8]))
"#;
    match run_with_prelude(input) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_simple() {
    let input = r#"
module Test[w: Nat] {
    input a = UInt[w]
    input b = UInt[w]
    output result = UInt[w]
    result := a + b
}

println(moduleVL(Test[8]))

module adderNat {
    input a = UInt[8]
    output result = UInt[8]
    result := a + 42
}

println(moduleVL(adderNat))

"#;
    match run_with_prelude(input) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_conversions() {
    let input = r#"
module Test[w: Nat] {
    let a = UInt[w]
    let as_bits = Bits[w]
    let resized = UInt[w + 1]
    as_bits := a.asBits
    resized := a.resize[w + 1]
}
"#;
    match run_with_prelude(input) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_reduction() {
    let input = r#"
module Test[w: Nat] {
    let a = Bits[w]
    let all_ones = Bool
    let any_one = Bool
    all_ones := a.andR
    any_one := a.orR
}
"#;
    match run_with_prelude(input) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_mux() {
    let input = r#"
module Test[w: Nat] {
    let cond = Bool
    let a = UInt[w]
    let b = UInt[w]
    let result = UInt[w]
    result := cond.mux(a, b)
}
"#;
    match run_with_prelude(input) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_registers() {
    let input = r#"
module Test {
    let reg_val = UInt[8]
    let init_reg = UInt[8]
    init_reg := RegInit(init_reg, defaultClockDomain).value
    reg_val := RegNext(reg_val).value
}
"#;
    match run_with_prelude(input) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_sint_ports() {
    let input = r#"
module Test {
    input a = SInt[8]
    input b = SInt[8]
    output c = SInt[8]
    let sum = SInt[8]
    sum := a + b
    c := sum
}

println(moduleVL(Test))
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("{}", output);
            assert!(output.contains("signed"), "SInt ports must have 'signed' keyword, got:\n{}", output);
            assert!(output.contains("input wire signed"), "input SInt should be 'input wire signed', got:\n{}", output);
            assert!(output.contains("output wire signed"), "output SInt should be 'output wire signed', got:\n{}", output);
        }
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_sint_wires_and_regs() {
    let input = r#"
module Test {
    let a = SInt[8]
    let b = SInt[8]
    reg c = SInt[16]
    let sum = SInt[8]
    sum := a + b
}

println(moduleVL(Test))
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("{}", output);
            assert!(output.contains("wire signed"), "wire SInt should have 'wire signed', got:\n{}", output);
            assert!(output.contains("reg signed"), "reg SInt should have 'reg signed', got:\n{}", output);
        }
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_sint_arithmetic() {
    let input = r#"
module Test[w: Nat] {
    let a = SInt[w]
    let b = SInt[w]
    let sum = SInt[w]
    let diff = SInt[w]
    let carry = SInt[w + 1]
    sum := a + b
    diff := a - b
    carry := a +^ b
}
"#;
    match run_with_prelude(input) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_sint_shift() {
    let input = r#"
module Test {
    let a = SInt[8]
    let shl = SInt[8]
    let shr = SInt[8]
    shl := a << 2
    shr := a >> 2
}
"#;
    match run_with_prelude(input) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_sint_comparisons() {
    let input = r#"
module Test[w: Nat] {
    let a = SInt[w]
    let b = SInt[w]
    let lt = Bool
    let eq = Bool
    lt := a < b
    eq := a === b
}
"#;
    match run_with_prelude(input) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_sint_conversions() {
    let input = r#"
module Test[w: Nat] {
    let a = SInt[w]
    let as_bits = Bits[w]
    let as_uint = UInt[w]
    let resized = SInt[w + 1]
    as_bits := a.asBits
    as_uint := a.asUInt
    resized := a.resize[w + 1]
}
"#;
    match run_with_prelude(input) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_example_theorem_proving() {
    let input = include_str!("../../examples/theorem_proving.typort");
    match run_with_prelude(input) {
        Ok(output) => {
            println!("{}", output);
            assert!(output.contains("Eq"));
        }
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_example_typeclass_complex() {
    let input = include_str!("../../examples/typeclass_complex.typort");
    match run_with_prelude(input) {
        Ok(output) => {
            println!("{}", output);
            assert!(output.contains("3"), "expected 3, got: {}", output);
        }
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_apply_syntax() {
    let input = r#"
struct Wrapper {
    val: Nat
}

impl Wrapper {
    def apply(x: Nat): Nat = this.val + x
}

def w = new Wrapper(succ zero)
println (w (succ (succ zero)))
"#;
    let result = run_with_prelude(input);
    match result {
        Ok(output) => {
            println!("{}", output);
            assert!(output.contains("3"), "expected 3, got: {}", output);
        }
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_apply_multi_arg() {
    let input = r#"
struct Multi {
    val: Nat
}

impl Multi {
    def apply(x: Nat, y: Nat): Nat = this.val + x + y
}

def m = new Multi(succ (succ (succ zero)))
println (m (succ (succ zero), succ (succ zero)))
"#;
    let result = run_with_prelude(input);
    match result {
        Ok(output) => {
            println!("{}", output);
            assert!(output.contains("7"), "expected 7, got: {}", output);
        }
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_example_alu() {
    let input = include_str!("../../examples/alu.typort");
    match run_with_prelude(input) {
        Ok(output) => println!("{}", output),
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_reg_init_sint() {
    let input = r#"
module Test {
    let a = newSIntRegInitNat("myreg", 8, 0)
    a := a + 1
}

println(moduleVL(Test))
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("{}", output);
            assert!(output.contains("reg signed"), "SInt reg should be 'reg signed'");
            assert!(output.contains("myreg <= 0;"), "reset body should init to 0");
            assert!(output.contains("posedge reset"), "should have async reset");
            assert!(output.contains("input wire reset"), "should have reset port");
        }
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_reg_init_uint() {
    let input = r#"
module Test {
    let a = newUIntRegInitNat("myreg", 16, 42)
    a := a + 1
}

println(moduleVL(Test))
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("{}", output);
            assert!(!output.contains("signed"), "UInt reg should NOT have 'signed'");
            assert!(output.contains("myreg <= 42;"), "reset body should init to 42");
        }
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_reg_init_bits() {
    let input = r#"
module Test {
    let a = newBitsRegInitNat("myreg", 8, 1)
    let b = Bits[8]
    a := a ^ b
}

println(moduleVL(Test))
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("{}", output);
            assert!(output.contains("myreg <= 1;"), "reset body should init to 1");
            assert!(output.contains("posedge reset"), "should have async reset");
        }
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_reg_no_init() {
    let input = r#"
module Test {
    let a = newSIntReg("myreg", 8)
    a := a + 1
}

println(moduleVL(Test))
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("{}", output);
            assert!(output.contains("reg signed"), "SInt reg should be 'reg signed'");
            assert!(output.contains("input wire clk"), "should have clk port");
            assert!(!output.contains("input wire reset"), "should NOT have reset port");
            assert!(!output.contains("posedge reset"), "should NOT have async reset");
        }
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_multiple_reg_inits() {
    let input = r#"
module Test {
    let a = newSIntRegInitNat("reg_a", 8, 0)
    let b = newUIntRegInitNat("reg_b", 16, 3)
    let c = newBitsRegInitNat("reg_c", 32, 5)
    a := a + 1
    b := b - 1
    let d = Bits[32]
    c := c ^ d
}

println(moduleVL(Test))
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("{}", output);
            assert!(output.contains("reg_a <= 0;"), "reg_a init to 0");
            assert!(output.contains("reg_b <= 3;"), "reg_b init to 3");
            assert!(output.contains("reg_c <= 5;"), "reg_c init to 5");
            assert!(output.contains("posedge reset"), "should have async reset");
        }
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_mixed_reg_inits() {
    let input = r#"
module Test {
    let a = newSIntRegInitNat("reg_a", 8, 0)
    let b = newSIntReg("reg_b", 8)
    a := a + 1
    b := b + 2
}

println(moduleVL(Test))
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("{}", output);
            assert!(output.contains("reg_a <= 0;"), "init reg in reset body");
            assert!(output.contains("reg_b <= (reg_b + 2);"), "plain reg in else branch");
            assert!(output.contains("posedge reset"), "should have async reset");
        }
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_reg_init_with_ports_no_comma() {
    let input = r#"
module Test {
    input clk = Bool
    input rst = Bool
    let a = newSIntRegInitNat("myreg", 8, 0)
    a := a + 1
}

println(moduleVL(Test))
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("{}", output);
            assert!(!output.contains("(,"), "should NOT have leading comma");
            assert!(output.contains("input wire clk"), "should keep user clk");
            assert!(output.contains("input wire rst"), "should keep user rst");
            assert!(output.contains("myreg <= 0;"), "reset body present");
        }
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

#[test]
fn test_hdl_reg_init_in_when() {
    // Register inside when block — assignment is wrapped in when() expr,
    // so the clocked block (and its reset assistant) don't apply here.
    // The when generates combinational always @(*) with the regAssign inside.
    let input = r#"
module Test {
    let cond = Bool
    let a = newSIntRegInitNat("myreg", 8, 0)
    when(cond) {
        a := a + 1
    }
}

println(moduleVL(Test))
"#;
    match run_with_prelude(input) {
        Ok(output) => {
            println!("{}", output);
            // Reg declaration present
            assert!(output.contains("reg signed"), "reg signed present");
            // Reset port present (detected from init reg variant)
            assert!(output.contains("input wire reset"), "reset port present");
            // When block generated
            assert!(output.contains("cond) begin"), "when condition in always block");
        }
        Err(e) => panic!("{} @ {}: {}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}
