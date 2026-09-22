//! struct_eq：结构相等快路径（不 force、不展开、不求值，budget 封顶）——
//! `EqBudget`/`struct_tm_eq`/`struct_val_eq`/`struct_env_eq`。原
//! bump_spine_iter.rs 的 "结构相等" 节，逐行搬运（2026-09-23 拆分）。

use super::parser::syntax::Icit;

use super::env::{Env, env_len};
use super::spine::Spine;
use super::syntax::{PrCons, Tm, V, v_clo_of, v_lvl_of, v_meta_of, v_pi_of, v_spine_of, v_tag, v_xcell_of, XCell};

// 结构相等（快路径专用）：不 force、不展开、不求值，忽略 span 名。
// budget 封顶（参考版 struct_eq 的 20_000 同口径），超限按"不相等"处理
// ——快路径只会把本可判等（但求值发散）的情形提前判等，回落路径保持
// 原行为。env 的解析需要 `defs`（平坦区域）与 `spine`（链实参收集）。
// --------------------------------------------------------------------------------

const EQ_BUDGET: usize = 20_000;

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

/// `AppPruning` 掩码链的槽位快照（头 = 最内层）。
fn pr_slots(p: &Option<&PrCons<'_>>) -> Vec<Option<Icit>> {
    let mut out = Vec::new();
    let mut cur = *p;
    while let Some(b) = cur {
        out.push(b.slot);
        cur = b.next;
    }
    out
}

pub(super) fn struct_tm_eq(a: &Tm<'_>, b: &Tm<'_>) -> bool {
    struct_tm_eq_go(&mut EqBudget(EQ_BUDGET), a, b)
}

pub(super) fn struct_val_eq(spine: &Spine, defs: &[V], a: V, b: V) -> bool {
    struct_val_eq_go(&mut EqBudget(EQ_BUDGET), spine, defs, a, b)
}

pub(super) fn struct_env_eq(spine: &Spine, defs: &[V], a: Env<'_>, b: Env<'_>) -> bool {
    struct_env_eq_go(&mut EqBudget(EQ_BUDGET), spine, defs, a, b)
}

fn struct_spine_eq_go(budget: &mut EqBudget, spine: &Spine, defs: &[V], h1: usize, h2: usize) -> bool {
    if spine.spine_len(h1) != spine.spine_len(h2) {
        return false;
    }
    let mut a1: Vec<(V, Icit)> = Vec::new();
    spine.collect_args(h1, &mut a1);
    let mut a2: Vec<(V, Icit)> = Vec::new();
    spine.collect_args(h2, &mut a2);
    // 头也要同（bit-equal 或同名 Decl/Prim/同 Obj 结构）
    if !struct_val_eq_go(budget, spine, defs, spine.spine_head(h1), spine.spine_head(h2)) {
        return false;
    }
    a1.iter()
        .zip(a2.iter())
        .all(|((x, i), (y, j))| i == j && struct_val_eq_go(budget, spine, defs, *x, *y))
}

fn struct_tm_eq_go(budget: &mut EqBudget, a: &Tm<'_>, b: &Tm<'_>) -> bool {
    if !budget.spend() {
        return false;
    }
    match (a, b) {
        (Tm::Var(x), Tm::Var(y)) => x == y,
        (Tm::Decl(x), Tm::Decl(y)) => x == y,
        (Tm::Prim(x), Tm::Prim(y)) => x == y,
        (Tm::Obj(x, n), Tm::Obj(y, m)) => n == m && struct_tm_eq_go(budget, x, y),
        (Tm::App(x, xu, i), Tm::App(y, yu, j)) => {
            i == j && struct_tm_eq_go(budget, x, y) && struct_tm_eq_go(budget, xu, yu)
        }
        (Tm::Lam(_, i, x), Tm::Lam(_, j, y)) => i == j && struct_tm_eq_go(budget, x, y),
        (Tm::U, Tm::U) => true,
        (Tm::Pi(_, i, xa, xb), Tm::Pi(_, j, ya, yb)) => {
            i == j && struct_tm_eq_go(budget, xa, ya) && struct_tm_eq_go(budget, xb, yb)
        }
        (Tm::Let(_, xa, xb, xc), Tm::Let(_, ya, yb, yc)) => {
            struct_tm_eq_go(budget, xa, ya)
                && struct_tm_eq_go(budget, xb, yb)
                && struct_tm_eq_go(budget, xc, yc)
        }
        (Tm::Meta(x), Tm::Meta(y)) => x == y,
        (Tm::AppPruning(x, p), Tm::AppPruning(y, q)) => {
            let (sp, sq) = (pr_slots(p), pr_slots(q));
            sp.len() == sq.len()
                && sp.iter().zip(sq.iter()).all(|(a, b)| a == b)
                && struct_tm_eq_go(budget, x, y)
        }
        (Tm::LiteralType, Tm::LiteralType) => true,
        (Tm::LiteralIntro(x), Tm::LiteralIntro(y)) => x == y,
        (Tm::Sum(xn, xp, _), Tm::Sum(yn, yp, _)) => {
            xn == yn
                && xp.len() == yp.len()
                && xp.iter().zip(yp.iter()).all(|(a, b)| {
                    a.icit == b.icit
                        && struct_tm_eq_go(budget, a.val, b.val)
                        && struct_tm_eq_go(budget, a.ty, b.ty)
                })
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
                && struct_tm_eq_go(budget, xt, yt)
                && xd.len() == yd.len()
                && xd.iter().zip(yd.iter()).all(|(a, b)| {
                    a.icit == b.icit && struct_tm_eq_go(budget, a.val, b.val)
                })
        }
        (Tm::Match(xs, xc), Tm::Match(ys, yc)) => {
            struct_tm_eq_go(budget, xs, ys)
                && xc.len() == yc.len()
                && xc
                    .iter()
                    .zip(yc.iter())
                    .all(|((p, xb), (q, yb))| p == q && struct_tm_eq_go(budget, xb, yb))
        }
        _ => false,
    }
}

fn struct_val_eq_go(budget: &mut EqBudget, spine: &Spine, defs: &[V], x: V, y: V) -> bool {
    if !budget.spend() {
        return false;
    }
    match (v_tag(x), v_tag(y)) {
        (0, 0) => v_lvl_of(x) == v_lvl_of(y),
        (5, 5) => v_meta_of(x) == v_meta_of(y),
        (3, 3) | (6, 6) => true,
        (1, 1) => {
            let c1 = v_clo_of(x);
            let c2 = v_clo_of(y);
            c1.icit == c2.icit
                && struct_env_eq_go(budget, spine, defs, c1.env, c2.env)
                && struct_tm_eq_go(budget, c1.body, c2.body)
        }
        (4, 4) => {
            let p1 = v_pi_of(x);
            let p2 = v_pi_of(y);
            p1.icit == p2.icit
                && struct_val_eq_go(budget, spine, defs, p1.dom, p2.dom)
                && struct_env_eq_go(budget, spine, defs, p1.env, p2.env)
                && struct_tm_eq_go(budget, p1.body, p2.body)
        }
        (2, 2) => struct_spine_eq_go(budget, spine, defs, v_spine_of(x), v_spine_of(y)),
        (7, 7) => match (v_xcell_of(x), v_xcell_of(y)) {
            // 精化包裹：仅同一替换实例（同 Rc）且内层结构相等才短路；异实例
            // 一律回落慢路径（慢路径的 force 会推开 VSub，正确性不受影响）
            (XCell::VSub { val: a, sub: sa }, XCell::VSub { val: b, sub: sb }) => {
                std::rc::Rc::ptr_eq(sa, sb) && struct_val_eq_go(budget, spine, defs, *a, *b)
            }
            (XCell::VSub { .. }, _) | (_, XCell::VSub { .. }) => false,
            (XCell::Lit(a), XCell::Lit(b)) => a == b,
            (XCell::Decl(a), XCell::Decl(b)) => a == b,
            (XCell::Prim(a), XCell::Prim(b)) => a == b,
            (XCell::Obj { val: a, name: an }, XCell::Obj { val: b, name: bn }) => {
                an == bn && struct_val_eq_go(budget, spine, defs, *a, *b)
            }
            (
                XCell::Sum {
                    name: xn,
                    params: xp,
                    ..
                },
                XCell::Sum {
                    name: yn,
                    params: yp,
                    ..
                },
            ) => {
                xn == yn
                    && xp.len() == yp.len()
                    && xp.iter().zip(yp.iter()).all(|(a, b)| {
                        a.icit == b.icit
                            && struct_val_eq_go(budget, spine, defs, a.val, b.val)
                            && struct_val_eq_go(budget, spine, defs, a.ty, b.ty)
                    })
            }
            (
                XCell::SumCase {
                    typ: xt,
                    case_name: xn,
                    datas: xd,
                },
                XCell::SumCase {
                    typ: yt,
                    case_name: yn,
                    datas: yd,
                },
            ) => {
                xn == yn
                    && struct_val_eq_go(budget, spine, defs, *xt, *yt)
                    && xd.len() == yd.len()
                    && xd.iter().zip(yd.iter()).all(|(a, b)| {
                        a.icit == b.icit && struct_val_eq_go(budget, spine, defs, a.val, b.val)
                    })
            }
            (
                XCell::Match {
                    scrutinee: xs,
                    env: xe,
                    cases: xc,
                    pending: xp,
                },
                XCell::Match {
                    scrutinee: ys,
                    env: ye,
                    cases: yc,
                    pending: yp,
                },
            ) => {
                struct_val_eq_go(budget, spine, defs, *xs, *ys)
                    && struct_env_eq_go(budget, spine, defs, *xe, *ye)
                    && xc.len() == yc.len()
                    && xc
                        .iter()
                        .zip(yc.iter())
                        .all(|((p, xb), (q, yb))| p == q && struct_tm_eq_go(budget, xb, yb))
                    && xp.len() == yp.len()
                    && xp.iter().zip(yp.iter()).all(|((xv, xi), (yv, yi))| {
                        xi == yi && struct_val_eq_go(budget, spine, defs, *xv, *yv)
                    })
            }
            _ => false,
        },
        _ => false,
    }
}

fn struct_env_eq_go(
    budget: &mut EqBudget,
    spine: &Spine,
    defs: &[V],
    a: Env<'_>,
    b: Env<'_>,
) -> bool {
    let la = env_len(a);
    if la != env_len(b) {
        return false;
    }
    // 单趟双链迭代（原 (0..la).all(env_nth) 对链段是 O(d²)）：槽序与
    // env_nth 一致——各自链段先走（头 = 最内层），链尽后平坦区按
    // `flat_base + flat_len - 1 - k` 倒序读。两侧链/平坦划分可以不同，
    // 各自独立切换即可（env_nth 同款优先序）。
    let mut na = a.binds;
    let mut nb = b.binds;
    let mut fa = a.flat_base + a.flat_len;
    let mut fb = b.flat_base + b.flat_len;
    for _ in 0..la {
        let va = match na {
            Some(e) => {
                let v = e.val;
                na = e.next;
                v
            }
            None => {
                fa -= 1;
                defs[fa as usize]
            }
        };
        let vb = match nb {
            Some(e) => {
                let v = e.val;
                nb = e.next;
                v
            }
            None => {
                fb -= 1;
                defs[fb as usize]
            }
        };
        if !struct_val_eq_go(budget, spine, defs, va, vb) {
            return false;
        }
    }
    true
}
