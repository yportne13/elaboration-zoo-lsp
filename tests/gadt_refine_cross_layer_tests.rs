//! GADT 索引精化（pattern-match refinement）跨层行为钉子（2026-11-15 实测 + L08 修复后复测）。
//!
//! 背景：L13 的 src/L13_namespace/struct_refine_probe.rs 有一组「已知弱点」case
//! （weak01–weak05）。2026-11 复核：weak03/weak05 在 L13 参考版已通过（9-29 精化重构），
//! weak01/02/04 则是本来类型错误的程序——被拒是正确行为（probe 的 known_weakness 标签
//! 是 8 月分析阶段遗留）。
//!
//! 实测矩阵（同构 case 钉到 L07–L13）：
//!   control（well-typed GADT head）：            L07..L13 全 Ok
//!   weak01 （ill-typed 直接 Vec 返回尾）：       L07..L13 全 Err（正确拒绝）
//!   weak02 （ill-typed 单层 struct 返回尾）：    L07 无 struct；L08..L13 Err（正确拒绝）
//!   weak03 （well-typed 两字段交叉索引）：       L07 无 struct；L08..L13 Ok（具体值）
//!   weak04 （ill-typed 嵌套 struct 返回尾）：    L07 无 struct；L08..L13 Err（正确拒绝）
//!   weak05 （well-typed VecHolder 递归交叉）：   L07 无 struct；L08..L13 Ok（具体值）
//!
//! L09–L12 的第三轮修复（2026-11-15）：补齐 struct 模式糖后，L09–L12 的
//! check_pm_final 在跨字段索引精化上仍会失败（模式表达式推断出的独立 meta 与走查
//! Rigid 不连通），导致 weak03 卡住 / weak05 误拒。修复 = L08 walk_con 风格 fallback：
//! check_pm_final 失败时直接用走查阶段记录的节点索引方程（头部 Sum ≐ 走查返回类型，
//! 根节点 + 嵌套字段节点）解出 σ，再在终态 σ 下检查臂体/结算覆盖；L12 的 walk_pat
//! 也补上了与 L11 同款的 PendingNode(head, ret) 记账。实测 weak03/weak05 现在在
//! L09–L12 上均给出与 L08/L13 一致的具体值，ill-typed weak02/04 仍正确拒绝。
//!
//! L11/L12 的 weak05 误拒是真实缺口（match 不完整：模式位置 VecHolder.mk#2 缺少构造子
//! fsucc）；实验排除了 arm 顺序与递归体因素，根因在 nested-coverage 检查（pattern_match.rs
//! 的 nested_checks/cover_at）+ 精化传播：第一字段 cons 精化改变第二字段 Fin 索引后，
//! 第二字段的 fsucc 模式没有被记入覆盖矩阵。L13 的 9-29 精化重做（already_refined 传播、
//! 同族 e8ade220）没有回灌 L11/L12。
//!
//! 口径与翻转条件：钉 2026-11-15 实测行为；修好后先翻转断言再改实现
//! （L11/L12 weak05 -> Ok；L09/L10 变成真 Ok/正确值后重写「假 Ok」断言），
//! 与 tests/known_bug_pins.rs 的钉法一致。
//!
//! 为何 L09/L10/L11 用 #[path]：这三层在 src/lib.rs 是私有模块；L07/L08/L12/L13 是 pub，
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

const CONTROL: &str = r#"
def head[T, L: Nat](x: Vec[T] (succ L)): T =
    match x {
        case cons(x, _) => x
    }
println (head (cons zero nil))
"#;

const WEAK01: &str = r#"
def vtail_direct[A, len: Nat](v: Vec[A] len): Vec[A] len =
    match v {
        case nil => nil
        case cons(x, xs) => xs
    }
println (vtail_direct (cons zero nil))
"#;

const SIMPLE_STRUCT: &str = r#"
struct Pair2[A] {
    fst: A
    snd: A
}

def getf[A](p: Pair2[A]): A =
    match p {
        case Pair2 { fst, snd } => fst
    }
println (getf (Pair2.mk zero zero))
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

#[test]
fn control_well_typed_gadt_accepted_on_all_layers() {
    let src = with_defs(CONTROL);
    let s = src.clone();
    assert!(run_ok(|| L07_sum_type::run(&s, 0)), "L07");
    let s = src.clone();
    assert!(run_ok(|| L08_product_type::run(&s, 0)), "L08");
    let s = src.clone();
    assert!(run_ok(|| L09_mltt::run(&s, 0)), "L09");
    let s = src.clone();
    assert!(run_ok(|| L10_typeclass::run(&s, 0)), "L10");
    let s = src.clone();
    assert!(run_ok(|| L11_macro::run(&s, 0)), "L11");
    let s = src.clone();
    assert!(run_ok(|| L12_canonical::run(&s, 0)), "L12");
    let s = src.clone();
    assert!(run_ok(|| L13_namespace::run(&s, 0)), "L13");
}

#[test]
fn weak01_ill_typed_rejected_on_all_layers() {
    let src = with_defs(WEAK01);
    let s = src.clone();
    assert!(run_err(|| L07_sum_type::run(&s, 0)), "L07");
    let s = src.clone();
    assert!(run_err(|| L08_product_type::run(&s, 0)), "L08");
    let s = src.clone();
    assert!(run_err(|| L09_mltt::run(&s, 0)), "L09");
    let s = src.clone();
    assert!(run_err(|| L10_typeclass::run(&s, 0)), "L10");
    let s = src.clone();
    assert!(run_err(|| L11_macro::run(&s, 0)), "L11");
    let s = src.clone();
    assert!(run_err(|| L12_canonical::run(&s, 0)), "L12");
    let s = src.clone();
    assert!(run_err(|| L13_namespace::run(&s, 0)), "L13");
}

#[test]
fn l07_cannot_express_struct_patterns() {
    let src = with_defs(WEAK03);
    let s = src.clone();
    assert!(run_err(|| L07_sum_type::run(&s, 0)), "L07 无 struct");
}

#[test]
fn l08_struct_pattern_sugar_supported_after_2026_11_fix() {
    let src = with_defs(SIMPLE_STRUCT);
    let s = src.clone();
    assert!(run_ok(|| L08_product_type::run(&s, 0)), "L08 简单 struct 模式");
    let src = with_defs(WEAK02);
    let s = src.clone();
    assert!(run_err(|| L08_product_type::run(&s, 0)), "L08 weak02 应正确拒绝");
    let src = with_defs(WEAK04);
    let s = src.clone();
    assert!(run_err(|| L08_product_type::run(&s, 0)), "L08 weak04 应正确拒绝");
    let src = with_defs(WEAK03);
    let s = src.clone();
    assert!(run_ok(|| L08_product_type::run(&s, 0)), "L08 weak03 接受");
    let src = with_defs(WEAK05);
    let s = src.clone();
    assert!(run_ok(|| L08_product_type::run(&s, 0)), "L08 weak05 接受");
}

#[test]
fn l09_l10_struct_pattern_sugar_supported_after_2026_11_fix() {
    // 2026-11-15：L09/L10 的 p_pattern 补上 struct 模式臂；L09 的 match 入口在
    // 无臂命中时改为保留 Val::Match（不再 unwrap panic）。简单 struct 解构可求值。
    let src = with_defs(SIMPLE_STRUCT);
    let s = src.clone();
    assert!(run_ok(|| L09_mltt::run(&s, 0)), "L09 简单 struct 模式");
    let s = src.clone();
    assert!(run_ok(|| L10_typeclass::run(&s, 0)), "L10 简单 struct 模式");
    // 嵌套 Con 的 ill-typed 用例正确拒绝（不再因解析恢复而假 Ok）。
    let src = with_defs(WEAK02);
    let s = src.clone();
    assert!(run_err(|| L09_mltt::run(&s, 0)), "L09 weak02 应正确拒绝");
    let s = src.clone();
    assert!(run_err(|| L10_typeclass::run(&s, 0)), "L10 weak02 应正确拒绝");
}

#[test]
fn weak02_weak04_ill_typed_rejected_by_checking_layers() {
    for prog in [WEAK02, WEAK04] {
        let src = with_defs(prog);
        let s = src.clone();
        assert!(run_err(|| L08_product_type::run(&s, 0)), "L08");
        let s = src.clone();
        assert!(run_err(|| L09_mltt::run(&s, 0)), "L09");
        let s = src.clone();
        assert!(run_err(|| L10_typeclass::run(&s, 0)), "L10");
        let s = src.clone();
        assert!(run_err(|| L11_macro::run(&s, 0)), "L11");
        let s = src.clone();
        assert!(run_err(|| L12_canonical::run(&s, 0)), "L12");
        let s = src.clone();
        assert!(run_err(|| L13_namespace::run(&s, 0)), "L13");
    }
}

#[test]
fn weak03_cross_field_well_typed_accepted_with_quality_notes() {
    let src = with_defs(WEAK03);
    let s = src.clone();
    assert!(run_ok(|| L08_product_type::run(&s, 0)), "L08 具体值");
    let s = src.clone();
    assert!(run_ok(|| L09_mltt::run(&s, 0)), "L09 Ok 但输出卡住/未解");
    let s = src.clone();
    assert!(run_ok(|| L10_typeclass::run(&s, 0)), "L10 Ok 但输出卡住/未解");
    let s = src.clone();
    assert!(run_ok(|| L11_macro::run(&s, 0)), "L11 Ok 但输出卡住/未解");
    let s = src.clone();
    assert!(run_ok(|| L12_canonical::run(&s, 0)), "L12 Ok 但输出卡住/未解");
    let s = src.clone();
    assert!(run_ok(|| L13_namespace::run(&s, 0)), "L13 具体值");
}

#[test]
fn weak05_well_typed_accepted_from_l08() {
    // 第 18 轮（2026-11-15）fallback 修复后，L09–L12 的 weak05 也通过与 L08/L13
    // 一致的具体值路径（此前 L11/L12 误拒、L09/L10 输出卡住）。
    let src = with_defs(WEAK05);
    let s = src.clone();
    assert!(run_ok(|| L08_product_type::run(&s, 0)), "L08 接受");
    let s = src.clone();
    assert!(run_ok(|| L09_mltt::run(&s, 0)), "L09 接受");
    let s = src.clone();
    assert!(run_ok(|| L10_typeclass::run(&s, 0)), "L10 接受");
    let s = src.clone();
    assert!(run_ok(|| L11_macro::run(&s, 0)), "L11 接受");
    let s = src.clone();
    assert!(run_ok(|| L12_canonical::run(&s, 0)), "L12 接受");
    let s = src.clone();
    assert!(run_ok(|| L13_namespace::run(&s, 0)), "L13 接受");
}
