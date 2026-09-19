//! 结构相等判定（快路径专用）：不 force、不展开、不求值，忽略 span。
//!
//! 用于 `unify` 对卡住 `Val::Match` 的自比较短路：同一个 decl 值在合一两侧
//! 各展开一份相同的卡住 match 时，逐分支重求值会把分支体再展开一层卡住
//! match（fresh rigid 层级随深度递增，永不收敛）；先做纯结构比较即可短路。
//! 新架构下精化不改写槽位，"同一组变量"的两份捕获 env 字面相等，这条
//! 快路径即覆盖绝大多数比较。预算封顶，超限按"不相等"处理——快路径只会
//! 把本可判等（但求值发散）的情形提前判等，回落路径保持原行为。
//!
//! 迭代实现（2026-09-18，README §7.6）：`succ^N zero` 型深值可由 eval 不烧
//! fuel 地构造（def 倍增链），递归版在预算（20k 层）烧尽**之前**就会先在
//! ~万级深度爆栈（常规栈 1–8 MB）。显式任务栈保持旧递归的两个可观测语义：
//! - **短路顺序**：子任务逆序压栈，pop 序 = 旧递归的访问序（`a && b` 里
//!   a 失败即整体 false，b 不再燃烧）；
//! - **燃烧面**：值/项任务各烧 1（≙ 旧 `val_eq_go`/`tm_eq_go` 入口），
//!   Env/Spine/Closure 展开不烧（同旧 `env_eq_go`/`spine_eq`/`closure_eq`
//!   无入口燃烧）。零成本的字段判定（icit / pat / 名字 / 长度）在压栈前
//!   完成，失败即 return——与旧闭包内 `xi == yi && …` 的短路一致。

use std::rc::Rc;

use super::{Closure, Env, InlineStack, Spine, Tm, Val};

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

const EQ_BUDGET: usize = 20_000;

pub fn tm_eq(a: &Tm, b: &Tm) -> bool {
    eq_run(EqTask::T(a, b))
}

pub fn env_eq(a: &Env, b: &Env) -> bool {
    eq_run(EqTask::Env(a, b))
}

pub fn val_eq(a: &Val, b: &Val) -> bool {
    // 同址：同一 Val 实例，免预算免递归（Sum/SumCase 的 Rc 槽位共享同一
    // 展开的场景常见——同源 decl 值两份拷贝）
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
    // 主循环栈内联化（2026-09-18 性能轮）：浅结构（match 自比较快路径的
    // 绝大多数调用）零堆分配，与旧递归剖面一致；深/宽结构溢出转 Vec
    let mut stack = InlineStack::<EqTask<'_>, 16>::with_first(first);
    while let Some(task) = stack.pop() {
        match task {
            EqTask::V(a, b) => {
                // 同址短路（不烧预算）：同 Rc 来源的两份引用
                if std::ptr::eq(a, b) {
                    continue;
                }
                if !budget.spend() {
                    return false;
                }
                match (a, b) {
                    // 精化包裹：仅同一替换实例（同 Rc）且内层结构相等才短路；异实例
                    // 一律回落慢路径（慢路径的 force 会推开 VSub，正确性不受影响）
                    (Val::VSub(x, xs), Val::VSub(y, ys)) => {
                        if !std::rc::Rc::ptr_eq(xs, ys) {
                            return false;
                        }
                        stack.push(EqTask::V(x, y));
                    }
                    (Val::VSub(..), _) | (_, Val::VSub(..)) => return false,
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
                    (Val::U, Val::U) | (Val::LiteralType, Val::LiteralType) => {}
                    (Val::LiteralIntro(x), Val::LiteralIntro(y)) => {
                        if x != y {
                            return false;
                        }
                    }
                    (Val::Prim(x, xs), Val::Prim(y, ys)) => {
                        if x != y {
                            return false;
                        }
                        stack.push(EqTask::Spine(xs, ys));
                    }
                    (Val::Sum(xn, xp, _), Val::Sum(yn, yp, _)) => {
                        if xn.data != yn.data || xp.len() != yp.len() {
                            return false;
                        }
                        for ((_, _, _, xi), (_, _, _, yi)) in xp.iter().zip(yp.iter()) {
                            if xi != yi {
                                return false;
                            }
                        }
                        for ((_, xv, xt, _), (_, yv, yt, _)) in xp.iter().zip(yp.iter()).rev() {
                            // Rc 槽位同实例短路（共享同源 decl 展开时免递归）
                            if !Rc::ptr_eq(xt, yt) {
                                stack.push(EqTask::V(xt, yt));
                            }
                            if !Rc::ptr_eq(xv, yv) {
                                stack.push(EqTask::V(xv, yv));
                            }
                        }
                    }
                    (
                        Val::SumCase {
                            typ: xt,
                            case_name: xn,
                            datas: xd,
                        },
                        Val::SumCase {
                            typ: yt,
                            case_name: yn,
                            datas: yd,
                        },
                    ) => {
                        if xn != yn || xd.len() != yd.len() {
                            return false;
                        }
                        for ((_, _, xi), (_, _, yi)) in xd.iter().zip(yd.iter()) {
                            if xi != yi {
                                return false;
                            }
                        }
                        for ((_, xv, _), (_, yv, _)) in xd.iter().zip(yd.iter()).rev() {
                            if !Rc::ptr_eq(xv, yv) {
                                stack.push(EqTask::V(xv, yv));
                            }
                        }
                        if !Rc::ptr_eq(xt, yt) {
                            stack.push(EqTask::V(xt, yt));
                        }
                    }
                    (Val::Match(xs, xe, xc, xp), Val::Match(ys, ye, yc, yp)) => {
                        if xc.len() != yc.len() || xp.len() != yp.len() {
                            return false;
                        }
                        for ((p, _), (q, _)) in xc.iter().zip(yc.iter()) {
                            if p != q {
                                return false;
                            }
                        }
                        for ((_, xi), (_, yi)) in xp.iter().zip(yp.iter()) {
                            if xi != yi {
                                return false;
                            }
                        }
                        // 访问序（旧递归）：scrutinee → env → 分支体 → pending
                        for ((_, xb), (_, yb)) in xc.iter().zip(yc.iter()).rev() {
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
                    (Tm::U, Tm::U) => {}
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
                    (Tm::Prim(x), Tm::Prim(y)) => {
                        if x != y {
                            return false;
                        }
                    }
                    (Tm::Sum(xn, xp, _), Tm::Sum(yn, yp, _)) => {
                        if xn.data != yn.data || xp.len() != yp.len() {
                            return false;
                        }
                        for ((_, _, _, xi), (_, _, _, yi)) in xp.iter().zip(yp.iter()) {
                            if xi != yi {
                                return false;
                            }
                        }
                        for ((_, xv, xt, _), (_, yv, yt, _)) in xp.iter().zip(yp.iter()).rev() {
                            stack.push(EqTask::T(xt, yt));
                            stack.push(EqTask::T(xv, yv));
                        }
                    }
                    (
                        Tm::SumCase {
                            typ: xt,
                            case_name: xn,
                            datas: xd,
                        },
                        Tm::SumCase {
                            typ: yt,
                            case_name: yn,
                            datas: yd,
                        },
                    ) => {
                        if xn != yn || xd.len() != yd.len() {
                            return false;
                        }
                        for ((_, _, xi), (_, _, yi)) in xd.iter().zip(yd.iter()) {
                            if xi != yi {
                                return false;
                            }
                        }
                        for ((_, xv, _), (_, yv, _)) in xd.iter().zip(yd.iter()).rev() {
                            stack.push(EqTask::T(xv, yv));
                        }
                        stack.push(EqTask::T(xt, yt));
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
                        for ((_, xb), (_, yb)) in xc.iter().zip(yc.iter()).rev() {
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
                // 旧递归序：env 先、闭包体后
                stack.push(EqTask::T(&a.1, &b.1));
                stack.push(EqTask::Env(&a.0, &b.0));
            }
        }
    }
    true
}
