// ============================================================
// B1 栈安全化回归：深链 rename / quote 在默认 2 MB 栈下不得爆栈
//
// 背景（docs/inheritance/l13-B0-carrier-upgrade-plan.md §7）：L13 的
// eval 深链早已帧式化、quote 的单构造子 SumCase 链也早已迭代化，
// 但 rename 的 Sum/SumCase/Obj 仍是逐点递归。B1 把它们换成帧式
// 收集器（rename_deep），语义与逐点递归逐项等价，这里把「不爆栈」钉住。
//
// 判据不是性能，是能否在 default stack 下跑完：旧实现对 N=200_000
// 的 SumCase 链会在 rename 递归时打爆 2 MB 栈（调大栈才过得去）。
// ============================================================

use super::*;

const N_DEEP: usize = 20_000;

fn nat_sum_span() -> Span<SmolStr> {
    empty_span(SmolStr::new("Nat"))
}

fn succ_name() -> Span<SmolStr> {
    empty_span(SmolStr::new("succ"))
}

fn zero_name() -> Span<SmolStr> {
    empty_span(SmolStr::new("zero"))
}

/// succ^n zero 的 SumCase 链（每层 datas 单元素，正是 quote 的
/// 迭代快路径与 rename 帧式收集器要处理的形态）。
fn chain(n: usize) -> Rc<Val> {
    let nat: Rc<Val> = Rc::new(Val::Sum(
        nat_sum_span(),
        Rc::new(vec![]),
        Rc::new(vec![zero_name(), succ_name()]),
        false,
    ));
    let mut v: Rc<Val> = Val::SumCase {
        is_trait: false,
        typ: nat.clone(),
        index: 0,
        datas: Rc::new(vec![]),
    }
    .into();
    for _ in 0..n {
        v = Val::SumCase {
            is_trait: false,
            typ: nat.clone(),
            index: 1,
            datas: Rc::new(vec![(succ_name(), v, Icit::Expl)]),
        }
        .into();
    }
    v
}

fn pren_for_rename() -> super::unification::PartialRenaming {
    super::unification::PartialRenaming {
        occ: None,
        dom: Lvl(0),
        cod: Lvl(0),
        ren: Rc::new(rustc_hash::FxHashMap::default()),
    }
}

fn chain_depth(t: &Tm) -> usize {
    let mut depth = 0usize;
    let mut cur: &Tm = t;
    loop {
        match cur {
            Tm::SumCase { datas, .. } if !datas.is_empty() => {
                depth += 1;
                cur = &datas[0].1;
            }
            Tm::SumCase { .. } => {
                depth += 1;
                break;
            }
            _ => break,
        }
    }
    depth
}

/// rename 深链：帧式收集器在默认栈下跑完，且剥出的链深 = N_DEEP + 1。
#[test]
fn deep_sumcase_rename_does_not_overflow_default_stack() {
    let deep = std::mem::ManuallyDrop::new(chain(N_DEEP));
    let mut infer = Infer::new();
    let decl: Decl = Decl::default();
    let pren = pren_for_rename();
    let renamed = std::mem::ManuallyDrop::new(
        infer
            .rename(&decl, &pren, &deep)
            .expect("closed nat chain 的 rename 应当成功"),
    );
    assert_eq!(chain_depth(&renamed), N_DEEP + 1, "剥链深度应等于构造层数");
}

/// quote 深链：与 rename 同一形态，确保两条路径都在默认栈下成立。
#[test]
fn deep_sumcase_quote_does_not_overflow_default_stack() {
    let deep = std::mem::ManuallyDrop::new(chain(N_DEEP));
    let infer = Infer::new();
    let decl: Decl = Decl::default();
    let quoted = std::mem::ManuallyDrop::new(infer.quote(&decl, Lvl(0), &deep));
    assert_eq!(chain_depth(&quoted), N_DEEP + 1, "quote 的剥链深度应等于构造层数");
}

/// σ 链的 Drop 必须栈安全：派生 Drop 逐层递归释放 `SubEntry.next`，
/// 数万深的 σ 链在默认 2 MB 栈上直接 `STATUS_STACK_OVERFLOW`。
/// 本用例是红绿对照：移除 `impl Drop for Subst` 的迭代实现即爆栈。
#[test]
fn deep_subst_chain_drop_does_not_overflow_default_stack() {
    const N: usize = 100_000;
    let mut sub: Rc<Subst> = Rc::new(Subst::default());
    for i in 0..N {
        // 解值用最轻的（宇宙值），不参与链——只测链本身的释放
        sub = Subst::extend(&sub, Lvl(i as u32), Val::U(0).into());
    }
    assert_eq!(sub.lookup(Lvl(0)).is_some(), true, "链尾条目应可查");
    drop(sub);
}
