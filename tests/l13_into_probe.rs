// L13 阻塞 §7.2 探针 v7：镜像 hdl-ops 真实形态（字段投影方法体）
//
// v6 教训：无字段/无投影的裁剪版让参考版也 panic（lvl2ix family），
// 说明"参考版 Ok"依赖方法体里 this.expr 投影链的成分。
// v7 照抄真实形态（hdl-ops.typort:12-20 + hdl-types.typort:111-127 最小化）：
//   struct UInt[width: Nat] { name: Option[String], zz_expr: Expr }
//   impl[w] Add[UInt[w], UInt[w]] for UInt[w] { + = UInt.mk(None, binary(this.zz_expr, "+", that.zz_expr)) }
//   impl[w] Add[Nat, UInt[w]]   for UInt[w] { + = this + that.into }
//   impl[T] Into[T] for T / impl[w] Into[UInt[w]] for Nat（op.typort:40-46 + hdl-types:125）

#[path = "../src/list.rs"]
mod list;
#[path = "../src/bimap.rs"]
mod bimap;
#[path = "../src/parser_lib.rs"]
mod parser_lib;
#[path = "../src/parser_lib_resilient.rs"]
mod parser_lib_resilient;

#[path = "../src/L13_namespace/mod.rs"]
mod L13_namespace;

use L13_namespace::bump_spine_iter as fast;

fn panic_msg(e: Box<dyn std::any::Any + Send>) -> String {
    if let Some(s) = e.downcast_ref::<&str>() {
        s.to_string()
    } else if let Some(s) = e.downcast_ref::<String>() {
        s.clone()
    } else {
        "<non-string panic>".to_string()
    }
}

fn run_basic(src: &str) -> Result<String, String> {
    let input = src.to_owned();
    let handle = std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || L13_namespace::run(&input, 0).map_err(|e| e.0.data.to_string()))
        .unwrap();
    match handle.join() {
        Ok(r) => r,
        Err(e) => Err(format!("PANIC: {}", panic_msg(e))),
    }
}

fn run_fast(src: &str) -> Result<String, String> {
    let input = src.to_owned();
    let handle = std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || fast::run_fast(&input, 0).map_err(|e| e.0.data.to_string()))
        .unwrap();
    match handle.join() {
        Ok(r) => r,
        Err(e) => Err(format!("PANIC: {}", panic_msg(e))),
    }
}

fn probe(name: &str, src: &str) {
    let b = run_basic(src);
    let f = run_fast(src);
    let fmt = |r: &Result<String, String>| match r {
        Ok(s) => format!("Ok({:?})", s.lines().last().unwrap_or("")),
        Err(e) => format!("Err({})", e),
    };
    let (bs, fs) = (fmt(&b), fmt(&f));
    let verdict = if b.is_ok() == f.is_ok() && bs == fs { "MATCH" } else { "DIVERGE" };
    println!("[{verdict}] {name}\n  basic: {bs}\n  fast : {fs}");
}

#[test]
fn into_add_nat_uint_v7() {
    let src = r#"def outParam[A](a: A): A = a
enum Nat {
    zero
    succ(n: Nat)
}
enum Expr {
    binary(lhs: Expr, op: String, rhs: Expr)
    literal(v: Nat)
}
enum Option[A] {
    none
    some(a: A)
}
def nat_add(x: Nat, y: Nat): Nat =
    match x {
        case zero => y
        case succ(n) => succ (nat_add n y)
    }
trait Add[T, O: outParam(Type 0)] {
    def +(that: T): O
}
trait Into[O: outParam(Type 0)] {
    def into: O
}
struct UInt[width: Nat] {
    name: Option[String]
    zz_expr: Expr
}
def binary(lhs: Expr, op: String, rhs: Expr): Expr = Expr.binary(lhs, op, rhs)
impl[T] Into[T] for T {
    def into: T = this
}
impl[width: Nat] Into[UInt[width]] for Nat {
    def into: UInt[width] = UInt.mk(none, literal(this))
}
impl Add[Nat, Nat] for Nat {
    def +(that: Nat): Nat = nat_add this that
}
impl[width: Nat] Add[UInt[width], UInt[width]] for UInt[width] {
    def +(that: UInt[width]): UInt[width] = UInt.mk(none, binary(this.zz_expr, "+", that.zz_expr))
}
impl[width: Nat] Add[Nat, UInt[width]] for UInt[width] {
    def +(that: Nat): UInt[width] = this + that.into
}
def u: UInt[succ zero] = UInt.mk(none, literal(zero))
def lifted: UInt[succ zero] = u + (succ zero)
println lifted
"#;
    probe("v7 hdl-ops faithful (field projections)", src);
}
