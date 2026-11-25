//! 结构相等判定（快路径专用）：不 force、不展开、不求值，忽略 span。
//!
//! **来源**：L07 `src/L07_sum_type/struct_eq.rs`（373 行，2026-09-18 迭代化，
//! `EQ_BUDGET = 20_000`）。L09 起参考版一直保留、L10+ 删掉；L13 从来就没有——
//! 这正是 docs/compare-l07-l13-shared/FINAL.md §4 #2 记录的语义分叉：
//! `unify` 的 `(Match, Match)` 自比较失去结构快路径后，只能逐分支重求值
//! 64 次然后判「不可信」，L07 能证的等式 L13 报不出。
//!
//! **与 L07 版的差异**（按 L13 的值表示重写，不是照抄）：
//! - L13 没有 `Val::VSub`（精化载体是 `update_cxt`，值层无 σ 包裹）⇒ 删掉
//!   VSub 臂及其「异实例回落」分支；
//! - L13 没有 `Val::Prim`（prim 挂 decl 条目）⇒ 换成 `Val::Call`、
//!   `Val::SumCase{is_trait,index,...}`、`Val::Nat(u64)` 三条新臂；
//! - L13 的 `Val::U(u32)` 带层级 ⇒ 必须比较层级（L07 是单元变体）；
//! - L13 的 `Pi` 是 `(Span, Icit, Rc<VTy>, Closure)`、`Sum` 是 4 元组带 `bool`、
//!   `SumCase` 是 `{is_trait, typ, index, datas}` ⇒ 逐臂对齐真实字段，比较
//!   `index` 而不是构造子名（与运行时的 by-index 分派一致）；
//! - `PatternDetail` 在 L13 是 `Any(Span, Option<Span>, Icit)` /
//!   `Con(u32, Span, Vec<..>, Option<SmolStr>)` ⇒ 直接沿用 `PartialEq`；
//! - `Tm` 多出 `Call` / `OpCall` / `AppPruning` 等形态。
//!
//! 预算与迭代化语义与 L07 完全一致（超限按「不相等」，只会把本可判等但求值
//! 发散的情形提前判等，回落路径保持原行为）。

use std::rc::Rc;

use super::{Closure, Env, Icit, InlineStack, PatternDetail, Spine, Tm, Val};

struct EqBudget(usize);

impl EqBudget {
    fn spend(&mut self) -> bool {
        if self.0 == 0 {
            return false;
        }
        self.0 -= 1;
        true
    }
}

/// 结构比较的**总步数**上限（L07 同值）。超限按「不相等」处理——快路径只
/// 负责把「本可判等但求值发散」的情形提前判等，判不了就回落慢路径。
const EQ_BUDGET: usize = 20_000;

pub fn tm_eq(a: &Tm, b: &Tm) -> bool {
    eq_run(EqTask::T(a, b))
}

pub fn env_eq(a: &Env, b: &Env) -> bool {
    eq_run(EqTask::Env(a, b))
}

pub fn val_eq(a: &Val, b: &Val) -> bool {
    // 同址：同一 Val 实例，免预算免递归（Sum/SumCase 的 Rc 槽位共享同一
    // 展开的场景常见——同源 decl 值的两份拷贝）。
    if std::ptr::eq(a, b) {
        return true;
    }
    eq_run(EqTask::V(a, b))
}

#[derive(Clone, Copy)]
enum EqTask<'a> {
    V(&'a Val, &'a Val),
    T(&'a Tm, &'a Tm),
    Env(&'a Env, &'a Env),
    Spine(&'a Spine, &'a Spine),
    Closure(&'a Closure, &'a Closure),
}
fn eq_run(first: EqTask<'_>) -> bool {
    let mut budget = EqBudget(EQ_BUDGET);
    // 主循环栈内联化（L07 2026-09-18 性能轮同款）：浅结构（match 自比较快路径的
    // 绝大多数调用）零堆分配；深/宽结构溢出转 Vec。
    let mut stack = InlineStack::<EqTask<'_>, 16>::with_first(first);
    while let Some(task) = stack.pop() {
        match task {
            EqTask::V(a, b) => {
                // 同址短路（不烧预算）。
                if std::ptr::eq(a, b) {
                    continue;
                }
                if !budget.spend() {
                    return false;
                }
                match (a, b) {
                    (Val::Flex(x, xs), Val::Flex(y, ys)) => {
                        if x != y {
                            return false;
                        }
                        stack.push(EqTask::Spine(xs, ys));
                    }
                    (Val::Rigid(x, xs), Val::Rigid(y, ys)) => {
                        if x != y {
                            return false;
                        }
                        stack.push(EqTask::Spine(xs, ys));
                    }
                    (Val::Decl(x, xs), Val::Decl(y, ys)) => {
                        // 名字比较含定义处 span：同一份 decl 展开的两份值 span 相同。
                        if x != y {
                            return false;
                        }
                        stack.push(EqTask::Spine(xs, ys));
                    }
                    (Val::Obj(x, xn, xs), Val::Obj(y, yn, ys)) => {
                        if xn != yn {
                            return false;
                        }
                        stack.push(EqTask::Spine(xs, ys));
                        stack.push(EqTask::V(x, y));
                    }
                    (Val::Lam(_, xi, xc), Val::Lam(_, yi, yc)) => {
                        if xi != yi {
                            return false;
                        }
                        stack.push(EqTask::Closure(xc, yc));
                    }
                    (Val::Pi(_, xi, xa, xc), Val::Pi(_, yi, ya, yc)) => {
                        if xi != yi {
                            return false;
                        }
                        stack.push(EqTask::Closure(xc, yc));
                        stack.push(EqTask::V(xa, ya));
                    }
                    // 宇宙带层级：L07 是单元变体恒等，L13 必须比层级。
                    (Val::U(x), Val::U(y)) => {
                        if x != y {
                            return false;
                        }
                    }
                    (Val::LiteralType, Val::LiteralType) => {}
                    (Val::LiteralIntro(x), Val::LiteralIntro(y)) => {
                        if x != y {
                            return false;
                        }
                    }
                    // 原生 Nat：立即数直接比数值（L07 没有这一变体，是 succ 链）。
                    (Val::Nat(x), Val::Nat(y)) => {
                        if x != y {
                            return false;
                        }
                    }
                    // 内联调用头：名字 + 实参 + 体内联值。
                    (Val::Call(xn, xa, xb), Val::Call(yn, ya, yb)) => {
                        if xn != yn || xa.len() != ya.len() {
                            return false;
                        }
                        for ((_, xi), (_, yi)) in xa.iter().zip(ya.iter()) {
                            if xi != yi {
                                return false;
                            }
                        }
                        stack.push(EqTask::V(xb, yb));
                        let xa_v: Vec<_> = xa.iter().collect();
                        let ya_v: Vec<_> = ya.iter().collect();
                        for i in (0..xa_v.len()).rev() {
                            stack.push(EqTask::V(&xa_v[i].0, &ya_v[i].0));
                        }
                    }
                    (Val::Sum(xn, xp, _, _), Val::Sum(yn, yp, _, _)) => {
                        if xn.data != yn.data || xp.len() != yp.len() {
                            return false;
                        }
                        for ((_, _, _, xi), (_, _, _, yi)) in xp.iter().zip(yp.iter()) {
                            if xi != yi {
                                return false;
                            }
                        }
                        for i in (0..xp.len()).rev() {
                            let (_, xv, xt, _) = &xp[i];
                            let (_, yv, yt, _) = &yp[i];
                            // Rc 槽位同实例短路（共享同源 decl 展开时免递归）。
                            if !Rc::ptr_eq(xt, yt) {
                                stack.push(EqTask::V(xt, yt));
                            }
                            if !Rc::ptr_eq(xv, yv) {
                                stack.push(EqTask::V(xv, yv));
                            }
                        }
                    }
                    (
                        Val::SumCase { is_trait: xti, typ: xt, index: xn, datas: xd },
                        Val::SumCase { is_trait: yti, typ: yt, index: yn, datas: yd },
                    ) => {
                        // 构造子按**下标**判等（与运行时分派同口径）；is_trait 区分
                        // trait 方法与普通构造子。
                        if xn != yn || xti != yti || xd.len() != yd.len() {
                            return false;
                        }
                        for ((_, _, xi), (_, _, yi)) in xd.iter().zip(yd.iter()) {
                            if xi != yi {
                                return false;
                            }
                        }
                        for i in (0..xd.len()).rev() {
                            let (_, xv, _) = &xd[i];
                            let (_, yv, _) = &yd[i];
                            if !Rc::ptr_eq(xv, yv) {
                                stack.push(EqTask::V(xv, yv));
                            }
                        }
                        if !Rc::ptr_eq(xt, yt) {
                            stack.push(EqTask::V(xt, yt));
                        }
                    }
                    (Val::Match(xs, xe, xc), Val::Match(ys, ye, yc)) => {
                        if xc.len() != yc.len() {
                            return false;
                        }
                        for ((p, _), (q, _)) in xc.iter().zip(yc.iter()) {
                            if p != q {
                                return false;
                            }
                        }
                        // 访问序（L07 旧递归）：scrutinee → env → 分支体。
                        for i in (0..xc.len()).rev() {
                            let (_, xb) = &xc[i];
                            let (_, yb) = &yc[i];
                            stack.push(EqTask::T(xb, yb));
                        }
                        stack.push(EqTask::Env(xe, ye));
                        stack.push(EqTask::V(xs, ys));
                    }
                    _ => return false,
                }
            }
            EqTask::T(a, b) => {
                if !budget.spend() {
                    return false;
                }
                match (a, b) {
                    (Tm::Var(x), Tm::Var(y)) => {
                        if x != y {
                            return false;
                        }
                    }
                    (Tm::Decl(x), Tm::Decl(y)) => {
                        if x != y {
                            return false;
                        }
                    }
                    (Tm::Obj(x, n), Tm::Obj(y, m)) => {
                        if n != m {
                            return false;
                        }
                        stack.push(EqTask::T(x, y));
                    }
                    (Tm::App(x, xu, i), Tm::App(y, yu, j)) => {
                        if i != j {
                            return false;
                        }
                        stack.push(EqTask::T(xu, yu));
                        stack.push(EqTask::T(x, y));
                    }
                    (Tm::Lam(_, i, x), Tm::Lam(_, j, y)) => {
                        if i != j {
                            return false;
                        }
                        stack.push(EqTask::T(x, y));
                    }
                    (Tm::U(x), Tm::U(y)) => {
                        if x != y {
                            return false;
                        }
                    }
                    (Tm::Pi(_, i, xa, xb), Tm::Pi(_, j, ya, yb)) => {
                        if i != j {
                            return false;
                        }
                        stack.push(EqTask::T(xb, yb));
                        stack.push(EqTask::T(xa, ya));
                    }
                    (Tm::Let(_, xa, xb, xc), Tm::Let(_, ya, yb, yc)) => {
                        stack.push(EqTask::T(xc, yc));
                        stack.push(EqTask::T(xb, yb));
                        stack.push(EqTask::T(xa, ya));
                    }
                    (Tm::Meta(x), Tm::Meta(y)) => {
                        if x != y {
                            return false;
                        }
                    }
                    (Tm::AppPruning(x, p), Tm::AppPruning(y, q)) => {
                        if p.len() != q.len() || !p.iter().zip(q.iter()).all(|(a, b)| a == b) {
                            return false;
                        }
                        stack.push(EqTask::T(x, y));
                    }
                    (Tm::LiteralType, Tm::LiteralType) => {}
                    (Tm::LiteralIntro(x), Tm::LiteralIntro(y)) => {
                        if x != y {
                            return false;
                        }
                    }
                    (Tm::Call(xn, xa, xb), Tm::Call(yn, ya, yb)) => {
                        if xn != yn || xa.len() != ya.len() {
                            return false;
                        }
                        for ((_, xi), (_, yi)) in xa.iter().zip(ya.iter()) {
                            if xi != yi {
                                return false;
                            }
                        }
                        stack.push(EqTask::T(xb, yb));
                        let xa_v: Vec<_> = xa.iter().collect();
                        let ya_v: Vec<_> = ya.iter().collect();
                        for i in (0..xa_v.len()).rev() {
                            stack.push(EqTask::T(&xa_v[i].0, &ya_v[i].0));
                        }
                    }
                    (
                        Tm::OpCall { name: xn, args: xa, body: xb, .. },
                        Tm::OpCall { name: yn, args: ya, body: yb, .. },
                    ) => {
                        if xn != yn || xa.len() != ya.len() {
                            return false;
                        }
                        for ((_, xi), (_, yi)) in xa.iter().zip(ya.iter()) {
                            if xi != yi {
                                return false;
                            }
                        }
                        stack.push(EqTask::T(xb, yb));
                        let xa_v: Vec<_> = xa.iter().collect();
                        let ya_v: Vec<_> = ya.iter().collect();
                        for i in (0..xa_v.len()).rev() {
                            stack.push(EqTask::T(&xa_v[i].0, &ya_v[i].0));
                        }
                    }
                    (Tm::Sum(xn, xp, _, _), Tm::Sum(yn, yp, _, _)) => {
                        if xn.data != yn.data || xp.len() != yp.len() {
                            return false;
                        }
                        for ((_, _, _, xi), (_, _, _, yi)) in xp.iter().zip(yp.iter()) {
                            if xi != yi {
                                return false;
                            }
                        }
                        for i in (0..xp.len()).rev() {
                            let (_, xv, xt, _) = &xp[i];
                            let (_, yv, yt, _) = &yp[i];
                            if !Rc::ptr_eq(xt, yt) {
                                stack.push(EqTask::T(xt, yt));
                            }
                            if !Rc::ptr_eq(xv, yv) {
                                stack.push(EqTask::T(xv, yv));
                            }
                        }
                    }
                    (
                        Tm::SumCase { is_trait: xti, typ: xt, index: xn, datas: xd },
                        Tm::SumCase { is_trait: yti, typ: yt, index: yn, datas: yd },
                    ) => {
                        if xn != yn || xti != yti || xd.len() != yd.len() {
                            return false;
                        }
                        for ((_, _, xi), (_, _, yi)) in xd.iter().zip(yd.iter()) {
                            if xi != yi {
                                return false;
                            }
                        }
                        for i in (0..xd.len()).rev() {
                            let (_, xv, _) = &xd[i];
                            let (_, yv, _) = &yd[i];
                            if !Rc::ptr_eq(xv, yv) {
                                stack.push(EqTask::T(xv, yv));
                            }
                        }
                        if !Rc::ptr_eq(xt, yt) {
                            stack.push(EqTask::T(xt, yt));
                        }
                    }
                    (Tm::Match(xs, xc), Tm::Match(ys, yc)) => {
                        if xc.len() != yc.len() {
                            return false;
                        }
                        for ((p, _), (q, _)) in xc.iter().zip(yc.iter()) {
                            if p != q {
                                return false;
                            }
                        }
                        for i in (0..xc.len()).rev() {
                            let (_, xb) = &xc[i];
                            let (_, yb) = &yc[i];
                            stack.push(EqTask::T(xb, yb));
                        }
                        stack.push(EqTask::T(xs, ys));
                    }
                    _ => return false,
                }
            }
            EqTask::Env(a, b) => {
                if a.len() != b.len() {
                    return false;
                }
                stack.extend(a.iter().zip(b.iter()).map(|(x, y)| EqTask::V(x, y)));
            }
            EqTask::Spine(a, b) => {
                if a.len() != b.len() {
                    return false;
                }
                for ((_, i), (_, j)) in a.iter().zip(b.iter()) {
                    if i != j {
                        return false;
                    }
                }
                stack.extend(
                    a.iter()
                        .zip(b.iter())
                        .map(|((x, _), (y, _))| EqTask::V(x, y)),
                );
            }
            EqTask::Closure(a, b) => {
                // 旧递归序：env 先、闭包体后。
                stack.push(EqTask::T(&a.1, &b.1));
                stack.push(EqTask::Env(&a.0, &b.0));
            }
        }
    }
    true
}
