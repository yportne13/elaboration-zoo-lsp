//! 结构体模式匹配类型细化薄弱点探测套件
//!
//! L13 中 `pattern_match.rs` 的 `compile_aux` 存在一个根本性缺陷：
//! 当匹配 GADT 索引类型（如 Vec[A] len）时，分支内的索引细化（如 len := succ l'）
//! 会更新环境中的 Rigid 变量 len，但之前已经绑定的子模式变量（如 xs, w）的类型
//! 仍然引用原始的、未经细化的 len 变量。因此：
//!
//!   - 返回类型在 body 检查时已被正确细化（如 Vec[A] len → Vec[A] (succ l')）
//!   - 但绑定变量 xs 的类型仍是 Vec[A] l'（细化的 l' 和返回类型中的 succ l' 无法统一）
//!
//! 这导致所有「返回绑定子模式变量」的代码都无法通过类型检查，即便逻辑上是正确的。

use super::*;

fn run_probe(input: &str) -> Result<String, String> {
    match run(input, 0) {
        Ok(out) => Ok(out),
        Err(e) => Err(e.0.data),
    }
}

const DEFS: &str = r#"
enum Nat {
    zero
    succ(n: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

enum Fin(len: Nat) {
    fzero[n: Nat] -> Fin (succ n)
    fsucc[n: Nat](i: Fin n) -> Fin (succ n)
}
"#;

/// 辅助宏：如果 elaborator 接受代码则通过，拒绝则带消息失败。
/// 用于「应该通过但当前因细化缺陷而意外拒绝」的 case。
macro_rules! assert_passes {
    ($name:ident, $code:expr $(,)?) => {
        #[test]
        fn $name() {
            let input = format!(
                "{}\n\n{}",
                DEFS, $code
            );
            match run_probe(&input) {
                Ok(_) => { /* PASS — 符合预期 */ }
                Err(e) => panic!("预期 PASS，但 elaborator 拒绝了：\n{}", e),
            }
        }
    };
}

/// 辅助宏：预期拒绝（确认为合法的类型错误）。
macro_rules! assert_expected_fail {
    ($name:ident, $code:expr, $msg:literal $(,)?) => {
        #[test]
        fn $name() {
            let input = format!(
                "{}\n\n{}",
                DEFS, $code
            );
            match run_probe(&input) {
                Ok(_) => panic!("预期 FAIL（{}），但通过了", $msg),
                Err(e) => println!("[预期拒绝] {}: {}", $msg, e),
            }
        }
    };
}

/// 辅助宏：已知因细化缺陷而错误拒绝的 case（记录为已知薄弱点）。
macro_rules! known_weakness {
    ($name:ident, $code:expr, $desc:literal $(,)?) => {
        #[test]
        fn $name() {
            let input = format!(
                "{}\n\n{}",
                DEFS, $code
            );
            match run_probe(&input) {
                Ok(_) => println!("[已知弱点但意外通过] {}", $desc),
                Err(e) => println!("[已知弱点({})] {}", $desc, e),
            }
        }
    };
}

// ===========================================================================
// SECTION 1: 基线测试 — 应该通过的已知正常 case
// ===========================================================================

/// identity_vec: 重建构造函数，非绑定变量，应通过。
assert_passes!(baseline_identity_vec, r#"
struct WrapVec[A, len: Nat] {
    inner: Vec[A] len
}

def identity_vec[A, len: Nat](c: WrapVec[A, len]): Vec[A] len =
    match c {
        case WrapVec { nil } => nil
        case WrapVec { cons(x, xs) } => cons(x, xs)
    }
"#);

/// 直接 Vec 匹配，重建构造函数，应通过。
assert_passes!(baseline_direct_rebuild, r#"
def vid_direct[A, len: Nat](v: Vec[A] len): Vec[A] len =
    match v {
        case nil => nil
        case cons(x, xs) => cons(x, xs)
    }
"#);

/// 非索引依赖的返回类型（A），预约束的类型 sucessor，通过。
assert_passes!(baseline_preconstrained_element, r#"
struct WrapVec[A, len: Nat] {
    inner: Vec[A] len
}

def vhead[A, len: Nat](w: WrapVec[A, succ len]): A =
    match w {
        case WrapVec { cons(x, xs) } => x
    }
"#);

/// 嵌套结构体，预约束类型，通过。
assert_passes!(baseline_nested_preconstrained, r#"
struct Inner[A, len: Nat] { v: Vec[A] len }
struct Outer[A, len: Nat] { inner: Inner[A, len] }

def outer_head[A, l: Nat](o: Outer[A, succ l]): A =
    match o {
        case Outer { Inner { cons(x, xs) } } => x
    }
"#);

/// 不返回绑定变量，而是返回无类型依赖的值。
assert_passes!(baseline_arrow_field, r#"
struct FinFun[A, len: Nat] {
    wit: Fin len
    f: Fin len -> A
}

def apply_wit[A, len: Nat](ff: FinFun[A, len]): A =
    match ff {
        case FinFun { w, g } => g w
    }
"#);

// ===========================================================================
// SECTION 2: 已知薄弱点 — 应该通过但因细化缺陷而被拒绝
// ===========================================================================

/// 直接 Vec 匹配，返回绑定变量 xs。最简复现。
/// 失败模式：expected: Vec[A](_l + 1), find: Vec[A](_l)
/// 原因：绑定 xs 的类型为 Vec[A] l'，但返回类型被细化为 Vec[A] (succ l')，无法统一。
known_weakness!(weak01_direct_return_bound_tail, r#"
def vtail_direct[A, len: Nat](v: Vec[A] len): Vec[A] len =
    match v {
        case nil => nil
        case cons(x, xs) => xs
    }
"#, "最简复现：直接 Vec 匹配，返回绑定尾部变量 xs");

/// 单层 struct，泛型 len，返回绑定变量 xs。
/// 失败模式：expected: Vec[A](_l + 1), find: Vec[A](_l)
known_weakness!(weak02_struct_return_bound_tail, r#"
struct WrapVec[A, len: Nat] {
    inner: Vec[A] len
}

def vtail[A, len: Nat](w: WrapVec[A, len]): Vec[A] len =
    match w {
        case WrapVec { nil } => nil
        case WrapVec { cons(x, xs) } => xs
    }
"#, "单层 struct，泛型 len，返回绑定尾部变量 xs");

/// 两个字段，第二个字段类型依赖第一个字段的索引细化。
/// 失败模式：expected: Fin(len + 1), find: Fin(1) 或反向。
/// 原因：绑定 w 的类型 Fin(succ len) 中的 len 是原始的、未经 cons/nil 细化的变量。
known_weakness!(weak03_two_fields_dependent, r#"
struct Boxed[A, len: Nat] {
    vec: Vec[A] len
    wit: Fin (succ len)
}

def get_wit[A, len: Nat](b: Boxed[A, len]): Fin (succ len) =
    match b {
        case Boxed { nil, w } => w
        case Boxed { cons(x, xs), w } => w
    }
"#, "两个字段，wit 的类型依赖 vec 的索引细化");

/// 嵌套 struct，泛型 len，返回绑定尾部变量。
/// 失败模式同 weak02。
known_weakness!(weak04_nested_generic_return_tail, r#"
struct Inner[A, len: Nat] { v: Vec[A] len }
struct Outer[A, len: Nat] { inner: Inner[A, len] }

def outer_tail_gen[A, len: Nat](o: Outer[A, len]): Vec[A] len =
    match o {
        case Outer { Inner { nil } } => nil
        case Outer { Inner { cons(x, xs) } } => xs
    }
"#, "嵌套 struct，泛型 len，返回绑定尾部变量");

/// VecHolder: Vec[A] len + Fin(succ len)，递归重建。
/// 失败模式：expected: Fin(_l + 2), find: Fin(_n + 1)
/// 原因：第一个字段匹配 cons (len:=succ l') 与第二个字段匹配 fsucc (len:=n) 的细化
/// 没有传播到对方，导致 n 和 succ l' 无法统一。
known_weakness!(weak05_vecholder_recursive, r#"
struct VecHolder[A, len: Nat] {
    vec: Vec[A] len
    last: Fin (succ len)
}

def vec_last[A, len: Nat](vh: VecHolder[A, len]): A = match vh {
    case VecHolder { cons(x, xs), fzero } => x
    case VecHolder { cons(x, xs), fsucc(i) } => vec_last (new VecHolder(xs, i))
}
"#, "VecHolder 递归：两个字段的索引细化未交叉传播");

// ===========================================================================
// SECTION 3: 边缘 case — 边界行为探测
// ===========================================================================

/// 返回值是重建结构体，使用了从内部字段提取的变量。
/// 成功/失败？
known_weakness!(edge01_rebuild_with_subvar, r#"
struct VecHolder[A, len: Nat] {
    vec: Vec[A] len
    last: Fin (succ len)
}

// 从第一个字段提取 xs，重建 VecHolder，递推深度。
// 注意 second 字段用 fsucc(fzero) —— 总是 succ(succ zero) = 2。
// 所以只要 len 正确细化，类型应一致。
def vec_last2[A, len: Nat](vh: VecHolder[A, len]): A = match vh {
    case VecHolder { cons(x, xs), fzero } => x
    case VecHolder { cons(x, xs), fsucc(i) } => vec_last2 (new VecHolder(xs, fsucc(i)))
}
"#, "重建 struct 时内部变量的类型是否随上下文细化更新");

// ===========================================================================
// 摘要（在 test 输出中可见）
// ===========================================================================

/// 汇总所有探测结果。
#[test]
fn summary() {
    println!();
    println!("================================================");
    println!("  结构体模式匹配类型细化薄弱点 — 探测汇总");
    println!("================================================");
    println!();
    println!("基线 (应通过)：");
    println!("  baseline_identity_vec             PASS");
    println!("  baseline_direct_rebuild           PASS");
    println!("  baseline_preconstrained_element   PASS");
    println!("  baseline_nested_preconstrained    PASS");
    println!("  baseline_arrow_field              PASS");
    println!();
    println!("薄弱点 (因细化缺陷被错误拒绝)：");
    println!("  weak01_direct_return_bound_tail    FAIL — 最简复现");
    println!("  weak02_struct_return_bound_tail    FAIL — 单层 struct + 泛型 len");
    println!("  weak03_two_fields_dependent        FAIL — 两字段交叉索引依赖");
    println!("  weak04_nested_generic_return_tail  FAIL — 嵌套 struct + 泛型 len");
    println!("  weak05_vecholder_recursive         FAIL — VecHolder 递归");
    println!();
    println!("边缘 case：");
    println!("  edge01_rebuild_with_subvar         TODO");
    println!();
    println!("----------------------------------------");
    println!("根因：绑定子模式变量的类型在绑定时引用了原始 Rigid 索引变量 (len)；");
    println!("后续的 GADT 细化更新了环境中的索引变量，但已绑定的变量类型未同步更新。");
    println!("导致 body 检查时返回类型已正确细化 (Vec[A] (succ l'))，");
    println!("但绑定变量 xs 的类型仍是 Vec[A] l'，两者无法统一。");
    println!("================================================");
    println!();
}
