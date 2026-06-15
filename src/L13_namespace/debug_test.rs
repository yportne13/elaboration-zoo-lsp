use super::*;

#[test]
fn debug_trait_impl() {
    let input = r#"
def outParam[A](a: A): A = a
trait Pls[T, O: outParam(Type 0)] { def +(that: T): O }
trait Cvt[O: outParam(Type 0)] { def into: O }
enum Nat {
    z
    s(x: Nat)
}
struct U[w: Nat] {}
struct S {}
impl[w: Nat] Cvt[U[w]] for Nat { def into: U[w] = U.mk() }
impl Cvt[S] for Nat { def into: S = S.mk() }
impl[w: Nat] Pls[Nat, U[w]] for U[w] { def +(that: Nat): U[w] = this + that.into }
"#;
    match run(input, 0) {
        Ok(output) => println!("OK:\n{output}"),
        Err(e) => println!("ERR: {:?}", e.0.data),
    }
}
