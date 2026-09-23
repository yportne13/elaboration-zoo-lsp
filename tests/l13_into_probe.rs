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

/// 跑两版并返回 `(verdict, basic 摘要, fast 摘要)`。
///
/// **本探针在 2026-09-23 之前没有任何断言**：`verdict` 只被 `println!`，
/// 于是两版早已分叉（basic 报参考版加固后的 `lvl2ix ... out of scope` 诊断、
/// fast 报孪生裸减法的 `attempt to subtract with overflow`）而套件仍显示
/// "1 passed"。断言由调用方持有（见 `into_add_nat_uint_v7`）。
fn probe(name: &str, src: &str) -> (&'static str, String, String) {
    let b = run_basic(src);
    let f = run_fast(src);
    let fmt = |r: &Result<String, String>| match r {
        Ok(s) => format!("Ok({:?})", s.lines().last().unwrap_or("")),
        Err(e) => format!("Err({})", e),
    };
    let (bs, fs) = (fmt(&b), fmt(&f));
    let verdict = if b.is_ok() == f.is_ok() && bs == fs { "MATCH" } else { "DIVERGE" };
    println!("[{verdict}] {name}\n  basic: {bs}\n  fast : {fs}");
    (verdict, bs, fs)
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
    let (verdict, bs, fs) = probe("v7 hdl-ops faithful (field projections)", src);
    // 钉住判定：这条路径上两版**都必须**给出同一个结论。
    //
    // 2026-09-23 之前的实际状态是 DIVERGE 而套件仍绿——basic 走到参考版
    // 加固后的 `lvl2ix: level 0 is out of scope ...` 诊断 panic，fast 则在
    // 孪生 `quote.rs` 的裸减法上 panic 成 `attempt to subtract with
    // overflow`（release 下 wrap 成巨大 u32，行为随机）。孪生侧已按参考版
    // 同口径加固（`bump_spine_iter/syntax.rs::lvl2ix`），此处把结论钉死。
    assert_eq!(
        verdict, "MATCH",
        "REF/TWIN diverged on the hdl-ops field-projection shape:\n  basic: {bs}\n  fast : {fs}",
    );
    // 防空转：两侧都必须真的产生了结论。`Ok("")` 意味着探针源没被真正检查
    // （历史上单行枚举/宏吃换行一类形态就会退化成这样），那时 MATCH 无意义。
    assert!(
        bs != "Ok(\"\")" && fs != "Ok(\"\")",
        "探针退化：两侧都是空 Ok，判定失去判别力（basic={bs:?} fast={fs:?}）",
    );
}