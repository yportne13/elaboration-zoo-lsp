//! 结构相等判定（快路径专用）：不 force、不展开、不求值，忽略 span。
//!
//! 用于 `unify` 对卡住 `Val::Match` 的自比较短路：同一个 decl 值在合一两侧
//! 各展开一份相同的卡住 match 时，逐分支重求值会把分支体再展开一层卡住
//! match（fresh rigid 层级随深度递增，永不收敛）；先做纯结构比较即可短路。
//! 新架构下精化不改写槽位，"同一组变量"的两份捕获 env 字面相等，这条
//! 快路径即覆盖绝大多数比较。预算封顶，超限按"不相等"处理——快路径只会
//! 把本可判等（但求值发散）的情形提前判等，回落路径保持原行为。

use super::{Closure, Env, Icit, PatternDetail, Spine, Tm, Val};

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
    tm_eq_go(&mut EqBudget(EQ_BUDGET), a, b)
}

pub fn env_eq(a: &Env, b: &Env) -> bool {
    env_eq_go(&mut EqBudget(EQ_BUDGET), a, b)
}

pub fn val_eq(a: &Val, b: &Val) -> bool {
    val_eq_go(&mut EqBudget(EQ_BUDGET), a, b)
}

fn spine_eq(budget: &mut EqBudget, a: &Spine, b: &Spine) -> bool {
    a.len() == b.len()
        && a.iter()
            .zip(b.iter())
            .all(|((x, i), (y, j))| *i == *j && val_eq_go(budget, x, y))
}

fn tm_eq_go(budget: &mut EqBudget, a: &Tm, b: &Tm) -> bool {
    if !budget.spend() {
        return false;
    }
    match (a, b) {
        (Tm::Var(x), Tm::Var(y)) => x == y,
        (Tm::Decl(x), Tm::Decl(y)) => x == y,
        (Tm::Obj(x, n), Tm::Obj(y, m)) => n == m && tm_eq_go(budget, x, y),
        (Tm::App(x, xu, i), Tm::App(y, yu, j)) => {
            i == j && tm_eq_go(budget, x, y) && tm_eq_go(budget, xu, yu)
        }
        (Tm::Lam(_, i, x), Tm::Lam(_, j, y)) => i == j && tm_eq_go(budget, x, y),
        (Tm::U, Tm::U) => true,
        (Tm::Pi(_, i, xa, xb), Tm::Pi(_, j, ya, yb)) => {
            i == j && tm_eq_go(budget, xa, ya) && tm_eq_go(budget, xb, yb)
        }
        (Tm::Let(_, xa, xb, xc), Tm::Let(_, ya, yb, yc)) => {
            tm_eq_go(budget, xa, ya) && tm_eq_go(budget, xb, yb) && tm_eq_go(budget, xc, yc)
        }
        (Tm::Meta(x), Tm::Meta(y)) => x == y,
        (Tm::AppPruning(x, p), Tm::AppPruning(y, q)) => {
            p.len() == q.len() && p.iter().zip(q.iter()).all(|(a, b)| a == b) && tm_eq_go(budget, x, y)
        }
        (Tm::LiteralType, Tm::LiteralType) => true,
        (Tm::LiteralIntro(x), Tm::LiteralIntro(y)) => x == y,
        (Tm::Prim(x), Tm::Prim(y)) => x == y,
        (Tm::Sum(xn, xp, _), Tm::Sum(yn, yp, _)) => {
            xn.data == yn.data
                && xp.len() == yp.len()
                && xp.iter().zip(yp.iter()).all(
                    |((_, xv, xt, xi), (_, yv, yt, yi))| {
                        xi == yi && tm_eq_go(budget, xv, yv) && tm_eq_go(budget, xt, yt)
                    },
                )
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
            xn == yn
                && tm_eq_go(budget, xt, yt)
                && xd.len() == yd.len()
                && xd.iter().zip(yd.iter()).all(|((_, xv, xi), (_, yv, yi))| {
                    xi == yi && tm_eq_go(budget, xv, yv)
                })
        }
        (Tm::Match(xs, xc), Tm::Match(ys, yc)) => {
            tm_eq_go(budget, xs, ys)
                && xc.len() == yc.len()
                && xc
                    .iter()
                    .zip(yc.iter())
                    .all(|((p, xb), (q, yb))| p == q && tm_eq_go(budget, xb, yb))
        }
        _ => false,
    }
}

fn val_eq_go(budget: &mut EqBudget, a: &Val, b: &Val) -> bool {
    if !budget.spend() {
        return false;
    }
    match (a, b) {
        (Val::Flex(x, xs), Val::Flex(y, ys)) => x == y && spine_eq(budget, xs, ys),
        (Val::Rigid(x, xs), Val::Rigid(y, ys)) => x == y && spine_eq(budget, xs, ys),
        (Val::Decl(x, xs), Val::Decl(y, ys)) => x == y && spine_eq(budget, xs, ys),
        (Val::Obj(x, xn, xs), Val::Obj(y, yn, ys)) => {
            xn == yn && val_eq_go(budget, x, y) && spine_eq(budget, xs, ys)
        }
        (Val::Lam(_, xi, xc), Val::Lam(_, yi, yc)) => xi == yi && closure_eq(budget, xc, yc),
        (Val::Pi(_, xi, xa, xc), Val::Pi(_, yi, ya, yc)) => {
            xi == yi && val_eq_go(budget, xa, ya) && closure_eq(budget, xc, yc)
        }
        (Val::U, Val::U) => true,
        (Val::LiteralType, Val::LiteralType) => true,
        (Val::LiteralIntro(x), Val::LiteralIntro(y)) => x == y,
        (Val::Prim(x, xs), Val::Prim(y, ys)) => x == y && spine_eq(budget, xs, ys),
        (Val::Sum(xn, xp, _), Val::Sum(yn, yp, _)) => {
            xn.data == yn.data
                && xp.len() == yp.len()
                && xp.iter().zip(yp.iter()).all(
                    |((_, xv, xt, xi), (_, yv, yt, yi))| {
                        xi == yi && val_eq_go(budget, xv, yv) && val_eq_go(budget, xt, yt)
                    },
                )
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
            xn == yn
                && val_eq_go(budget, xt, yt)
                && xd.len() == yd.len()
                && xd.iter().zip(yd.iter()).all(|((_, xv, xi), (_, yv, yi))| {
                    xi == yi && val_eq_go(budget, xv, yv)
                })
        }
        (Val::Match(xs, xe, xc, xp), Val::Match(ys, ye, yc, yp)) => {
            val_eq_go(budget, xs, ys)
                && env_eq_go(budget, xe, ye)
                && xc.len() == yc.len()
                && xc
                    .iter()
                    .zip(yc.iter())
                    .all(|((p, xb), (q, yb))| p == q && tm_eq_go(budget, xb, yb))
                && xp.len() == yp.len()
                && xp.iter().zip(yp.iter()).all(|((xv, xi), (yv, yi))| {
                    xi == yi && val_eq_go(budget, xv, yv)
                })
        }
        _ => false,
    }
}

fn closure_eq(budget: &mut EqBudget, a: &Closure, b: &Closure) -> bool {
    env_eq_go(budget, &a.0, &b.0) && tm_eq_go(budget, &a.1, &b.1)
}

fn env_eq_go(budget: &mut EqBudget, a: &Env, b: &Env) -> bool {
    a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| val_eq_go(budget, x, y))
}

// Icit 在 spine 比较里按引用比较即可；这里显式引用类型避免未使用告警。
const _: fn(&Icit, &Icit) -> bool = |a, b| a == b;
const _: fn(&PatternDetail, &PatternDetail) -> bool = |a, b| a == b;
