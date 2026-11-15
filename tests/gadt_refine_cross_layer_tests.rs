//! GADT 索引精化（pattern-match refinement）跨层行为钉子（2026-11-15 实测）。
//!
//! 背景：L13 的 [struct_refine_probe](../src/L13_namespace/struct_refine_probe.rs) 有一组
//! 「已知弱点」case（weak01–weak05）。2026-11 复核确认：**weak03/weak05 在 L13 参考版
//! 已通过**（9-29 精化重构），weak01/02/04 则是本来就类型错误的程序——被拒是**正确**行为
//! （probe 里 `known_weakness!` 的标签是 8 月分析阶段的遗留，summary 已改口"正确拒绝"）。
//!
//! 本文件把同构 case 钉到 L07–L13（可用性受限的层只测可表达部分），实测矩阵：
//!
//! | case（性质） | L07 | L08 | L09 | L10 | L11 | L12 | L13 |
//! |---|---|---|---|---|---|---|---|
//! | control：`Vec[T] (succ L)` head（well-typed） | Ok | Ok | Ok | Ok | Ok | Ok | Ok |
//! | weak01：直接 Vec 匹配返回尾（**ill-typed**） | Err | Err | Err | Err | Err | Err | Err |
//! | weak02：单层 struct 返回尾（**ill-typed**） | 不可表达 | 不可表达 | **Ok** | **Ok** | Err | Err | Err |
//! | weak03：两字段交叉索引依赖（well-typed） | 不可表达 | 不可表达 | Ok | Ok | Ok | Ok | Ok |
//! | weak04：嵌套 struct 返回尾（**ill-typed**） | 不可表达 | 不可表达 | **Ok** | **Ok** | Err | Err | Err |
//! | weak05：VecHolder 递归交叉细化（well-typed） | 不可表达 | 不可表达 | Ok | Ok | **Err** | **Err** | Ok |
//!
//! 结论（按层）：
//! - **L07**：无 struct，case 不可表达；enum-only 的 control/weak01 行为正确。
//! - **L08**：struct 可声明但**不能被 Con 模式解构**（见 `src/L08_product_type/README.md`
//!   §7「已知限制」：`case Point.mk(a,b)` / `case Point(a,b)` 都解析不成，只能变量臂整体
//!   绑定后投影），因此 struct 形态的 refine case 无法表达；enum-only 行为正确。
//! - **L09/L10**：接受 weak02/weak04 **ill-typed** 程序 = 精化过宽/校验更宽松（不是"更强"，
//!   因为正确拒绝被丢掉了）；weak03/weak05 的 Ok 因此也不能当作"精化正确"的强证据。
//! - **L11/L12**：正确拒绝 weak02/04，且接受 weak03；但 **weak05 被误拒**（`match 不完整：
//!   模式位置 VecHolder.mk#2 缺少构造子 fsucc` 一族）——即"递归跨字段索引细化"在 L11/L12
//!   仍有缺口（L13 参考版于 9-29 后已通过）。这是本次跨层对照发现的最值得跟进项。
//! - **L13**：weak02/04 正确拒绝、weak03/05 接受，当前行为与语义一致。
//!
//! 口径与翻转条件：本文件钉的是 2026-11-15 实测行为。若某层修好 weak05（L11/L12 应转为 Ok）
//! 或收紧 weak02/04（L09/L10 应转为 Err），先翻转对应断言再改实现——与 `tests/known_bug_pins.rs`
//! 的钉法一致。
//!
//! 为何 L09/L10/L11 用 `#[path]`：这三层在 `src/lib.rs` 是私有模块；L07/L08/L12/L13 是 pub，
//! 直接用库入口，避免重复编译。

#![allow(non_snake_case)]

#[path = "../src/list.rs"]
mod list;
#[path = "../src/bimap.rs"]
mod bimap;
#[path = "../src/parser_lib.rs"]
mod parser_lib;
#[path = "../src/parser_lib_resilient.rs"]
mod parser_lib_resilient;
#[path = "../src/L09_mltt/mod.rs"]
mod L09_mltt;
#[path = "../src/L10_typeclass/mod.rs"]
mod L10_typeclass;
#[path = "../src/L11_macro/mod.rs"]
mod L11_macro;

use std::panic::{catch_unwind, AssertUnwindSafe};

use elaboration_zoo_lsp::{L07_sum_type, L08_product_type, L12_canonical, L13_namespace};

fn run_ok<T: std::fmt::Debug, E: std::fmt::Debug>(f: impl FnOnce() -> Result<T, E>) -> bool {
    matches!(catch_unwind(AssertUnwindSafe(f)), Ok(Ok(_)))
}

fn run_err<T: std::fmt::Debug, E: std::fmt::Debug>(f: impl FnOnce() -> Result<T, E>) -> bool {
    matches!(catch_unwind(AssertUnwindSafe(f)), Ok(Err(_)))
}

/// Nat / Vec / Fin 基础定义（各层语法一致）。
const DEFS: &str = r#"enum Nat {
    zero
    succ(x: Nat)
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

/// control：well-typed GADT head（所有层应通过）。
const CONTROL: &str = r#"
def head[T, L: Nat](x: Vec[T] (succ L)): T =
    match x {
        case cons(x, _) => x
    }
println (head (cons zero nil))
"#;

/// weak01：直接 Vec 匹配返回尾部变量——**类型错误**（cons 分支 len 细化为 succ l'，
/// 返回的 xs 是长度 l'）。各层正确拒绝。
const WEAK01: &str = r#"
def vtail_direct[A, len: Nat](v: Vec[A] len): Vec[A] len =
    match v {
        case nil => nil
        case cons(x, xs) => xs
    }
println (vtail_direct (cons zero nil))
"#;

const WEAK02: &str = r#"
struct WrapVec[A, len: Nat] {
    inner: Vec[A] len
}

def vtail[A, len: Nat](w: WrapVec[A, len]): Vec[A] len =
    match w {
        case WrapVec { nil } => nil
        case WrapVec { cons(x, xs) } => xs
    }
println (vtail (WrapVec.mk nil))
"#;

const WEAK03: &str = r#"
struct Boxed[A, len: Nat] {
    vec: Vec[A] len
    wit: Fin (succ len)
}

def get_wit[A, len: Nat](b: Boxed[A, len]): Fin (succ len) =
    match b {
        case Boxed { nil, w } => w
        case Boxed { cons(x, xs), w } => w
    }
println (get_wit (Boxed.mk nil fzero))
"#;

const WEAK04: &str = r#"
struct Inner[A, len: Nat] {
    v: Vec[A] len
}
struct Outer[A, len: Nat] {
    inner: Inner[A, len]
}

def outer_tail_gen[A, len: Nat](o: Outer[A, len]): Vec[A] len =
    match o {
        case Outer { Inner { nil } } => nil
        case Outer { Inner { cons(x, xs) } } => xs
    }
println (outer_tail_gen (Outer.mk (Inner.mk nil)))
"#;

const WEAK05: &str = r#"
struct VecHolder[A, len: Nat] {
    vec: Vec[A] len
    last: Fin (succ len)
}

def vec_last[A, len: Nat](vh: VecHolder[A, len]): A = match vh {
    case VecHolder { cons(x, xs), fzero } => x
    case VecHolder { cons(x, xs), fsucc(i) } => vec_last (new VecHolder(xs, i))
}
println (vec_last (VecHolder.mk (cons zero nil) fzero))
"#;

fn with_defs(body: &str) -> String {
    format!("{DEFS}{body}")
}

fn control_ok_all_layers() -> bool {
    let src = with_defs(CONTROL);
    let s = src.clone();
    run_ok(|| L07_sum_type::run(&s, 0))
        && {
            let s = src.clone();
            run_ok(|| L08_product_type::run(&s, 0))
        }
        && {
            let s = src.clone();
            run_ok(|| L09_mltt::run(&s, 0))
        }
        && {
            let s = src.clone();
            run_ok(|| L10_typeclass::run(&s, 0))
        }
        && {
            let s = src.clone();
            run_ok(|| L11_macro::run(&s, 0))
        }
        && {
            let s = src.clone();
            run_ok(|| L12_canonical::run(&s, 0))
        }
        && {
            let s = src.clone();
            run_ok(|| L13_namespace::run(&s, 0))
        }
}

fn enum_weak01_rejected_all_layers() -> bool {
    let src = with_defs(WEAK01);
    let s = src.clone();
    run_err(|| L07_sum_type::run(&s, 0))
        && {
            let s = src.clone();
            run_err(|| L08_product_type::run(&s, 0))
        }
        && {
            let s = src.clone();
            run_err(|| L09_mltt::run(&s, 0))
        }
        && {
            let s = src.clone();
            run_err(|| L10_typeclass::run(&s, 0))
        }
        && {
            let s = src.clone();
            run_err(|| L11_macro::run(&s, 0))
        }
        && {
            let s = src.clone();
            run_err(|| L12_canonical::run(&s, 0))
        }
        && {
            let s = src.clone();
            run_err(|| L13_namespace::run(&s, 0))
        }
}

#[test]
fn control_well_typed_gadt_accepted_on_all_layers() {
    assert!(
        control_ok_all_layers(),
        "well-typed GADT head 应在 L07–L13 全部通过（2026-11-15 实测）"
    );
}

#[test]
fn weak01_ill_typed_rejected_on_all_layers() {
    // L13 struct_refine_probe 的 weak01 标签是历史遗留：该程序本身类型错误，
    // 被拒是正确行为；L07–L13 一致拒绝。
    assert!(
        enum_weak01_rejected_all_layers(),
        "weak01 形态是 ill-typed，各层应一致拒绝（2026-11-15 实测）"
    );
}

#[test]
fn struct_pattern_refinement_cannot_be_expressed_in_l07_l08() {
    // L07 无 struct；L08 struct 不能被 Con 模式解构（README §7 已知限制）。
    let src = with_defs(WEAK03);
    let s = src.clone();
    assert!(
        run_err(|| L07_sum_type::run(&s, 0)),
        "L07 无 struct，weak03 程序应解析失败"
    );
    let s = src.clone();
    assert!(
        run_err(|| L08_product_type::run(&s, 0)),
        "L08 struct 不能被 Con 模式解构，weak03 程序应失败（README §7）"
    );
}

#[test]
fn weak03_cross_field_well_typed_accepted_from_l09() {
    let src = with_defs(WEAK03);
    let s = src.clone();
    assert!(run_ok(|| L09_mltt::run(&s, 0)), "L09 weak03 实测 Ok");
    let s = src.clone();
    assert!(run_ok(|| L10_typeclass::run(&s, 0)), "L10 weak03 实测 Ok");
    let s = src.clone();
    assert!(run_ok(|| L11_macro::run(&s, 0)), "L11 weak03 实测 Ok");
    let s = src.clone();
    assert!(run_ok(|| L12_canonical::run(&s, 0)), "L12 weak03 实测 Ok");
    let s = src.clone();
    assert!(run_ok(|| L13_namespace::run(&s, 0)), "L13 weak03 实测 Ok");
}

#[test]
fn weak02_weak04_ill_typed_divergence_pinned() {
    // L09/L10 接受这两个 ill-typed 程序（过宽/缺校验）；L11/L12/L13 正确拒绝。
    for prog in [WEAK02, WEAK04] {
        let src = with_defs(prog);
        let s = src.clone();
        assert!(run_ok(|| L09_mltt::run(&s, 0)), "L09 实测接受（宽松，非正确性证据）");
        let s = src.clone();
        assert!(run_ok(|| L10_typeclass::run(&s, 0)), "L10 实测接受（宽松，非正确性证据）");
        let s = src.clone();
        assert!(run_err(|| L11_macro::run(&s, 0)), "L11 实测正确拒绝");
        let s = src.clone();
        assert!(run_err(|| L12_canonical::run(&s, 0)), "L12 实测正确拒绝");
        let s = src.clone();
        assert!(run_err(|| L13_namespace::run(&s, 0)), "L13 实测正确拒绝");
    }
}

#[test]
fn weak05_well_typed_gap_pinned_in_l11_l12() {
    // weak05 是 well-typed（L13 9-29 修复后接受）；L11/L12 仍误拒
    // （"match 不完整：模式位置 VecHolder.mk#2 缺少构造子 fsucc" 一族）。
    let src = with_defs(WEAK05);
    let s = src.clone();
    assert!(run_ok(|| L09_mltt::run(&s, 0)), "L09 实测接受");
    let s = src.clone();
    assert!(run_ok(|| L10_typeclass::run(&s, 0)), "L10 实测接受");
    let s = src.clone();
    assert!(
        run_err(|| L11_macro::run(&s, 0)),
        "L11 已知缺口：well-typed weak05 被误拒（修复后翻转为 Ok）"
    );
    let s = src.clone();
    assert!(
        run_err(|| L12_canonical::run(&s, 0)),
        "L12 已知缺口：well-typed weak05 被误拒（修复后翻转为 Ok）"
    );
    let s = src.clone();
    assert!(run_ok(|| L13_namespace::run(&s, 0)), "L13 实测接受（9-29 修复后）");
}
