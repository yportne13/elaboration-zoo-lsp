//! 结构相等判定（快路径专用）：不 force、不展开、不求值，忽略 span。
//!
//! 用于 `unify` 对卡住 `Val::Match` 的自比较短路：同一个 decl 值在合一两侧
//! 各展开一份相同的卡住 match 时，逐分支重求值会把分支体再展开一层卡住
//! match（fresh rigid 层级随深度递增，永不收敛）；先做纯结构比较即可短路。
//! 预算封顶，超限按"不相等"处理——快路径只会把本可判等（但求值发散）的
//! 情形提前判等，回落路径保持原行为。

use super::{Closure, Env, Icit, Ix, PatternDetail, Spine, Tm, Val};

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
        (Tm::Prim, Tm::Prim) => true,
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
        (Val::Prim, Val::Prim) => true,
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
        (Val::Match(xs, xe, xc), Val::Match(ys, ye, yc)) => {
            val_eq_go(budget, xs, ys)
                && env_eq_go(budget, xe, ye)
                && xc.len() == yc.len()
                && xc
                    .iter()
                    .zip(yc.iter())
                    .all(|((p, xb), (q, yb))| p == q && tm_eq_go(budget, xb, yb))
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

/// 建立 env2 槽位 → env1 槽位 的按值对应：对 env2 的每个位置 j2，找 env1
/// 中第一个与 env2[j2] 结构相等的位置 j1。找不到对应记为 None（该槽位
/// 的值是另一侧独有的，如被精化的 scrutinee 槽）——只有分支体**实际引用**
/// 了无对应的槽位时重映射才失败。
///
/// 值相同则可互换：重映射后的引用无论落在哪个同值槽位，求值结果一致，
/// 因此贪婪首匹配不影响健全性。
fn build_pos_map(budget: &mut EqBudget, env1: &Env, env2: &Env) -> Vec<Option<u32>> {
    let mut map = Vec::with_capacity(env2.len());
    for v2 in env2.iter() {
        let mut found = None;
        for (j1, v1) in env1.iter().enumerate() {
            if val_eq_go(budget, v1, v2) {
                found = Some(j1 as u32);
                break;
            }
        }
        map.push(found);
    }
    map
}

/// 把分支体 b（自由索引相对 [嵌套 fresh(e), binder(bd), case binders(count),
/// captured(env2)] 的 Ix 空间）重映射到 env1 的槽位布局：captured 引用
/// 经 map 换算，本地槽（case binders / 嵌套 fresh / 局部 binder）两侧同构
/// 保持字面。引用落在 map 之外的槽位（其值只存在于 env2）时返回 None。
fn remap_body_go(
    budget: &mut EqBudget,
    b: &Tm,
    count: u32,
    map: &[Option<u32>],
    e: u32,
    bd: u32,
) -> Option<Tm> {
    if !budget.spend() {
        return None;
    }
    let dyn_top = bd + e + count;
    Some(match b {
        Tm::Var(ix) => {
            let k = ix.0;
            if k < dyn_top {
                Tm::Var(*ix)
            } else {
                let pos = (k - dyn_top) as usize;
                match map.get(pos) {
                    Some(Some(j1)) => Tm::Var(Ix(dyn_top + j1)),
                    // 引用了无对应的槽位（另一侧独有的值）→ 无法对齐
                    _ => return None,
                }
            }
        }
        Tm::App(f, a, i) => Tm::App(
            Box::new(remap_body_go(budget, f, count, map, e, bd)?),
            Box::new(remap_body_go(budget, a, count, map, e, bd)?),
            *i,
        ),
        Tm::Lam(x, i, body) => Tm::Lam(
            x.clone(),
            *i,
            Box::new(remap_body_go(budget, body, count, map, e, bd + 1)?),
        ),
        Tm::Pi(x, i, a, body) => Tm::Pi(
            x.clone(),
            *i,
            Box::new(remap_body_go(budget, a, count, map, e, bd)?),
            Box::new(remap_body_go(budget, body, count, map, e, bd + 1)?),
        ),
        Tm::Let(x, a, t, u) => Tm::Let(
            x.clone(),
            Box::new(remap_body_go(budget, a, count, map, e, bd)?),
            Box::new(remap_body_go(budget, t, count, map, e, bd)?),
            Box::new(remap_body_go(budget, u, count, map, e, bd + 1)?),
        ),
        Tm::Match(s, cases) => Tm::Match(
            Box::new(remap_body_go(budget, s, count, map, e, bd)?),
            cases
                .iter()
                .map(|(p, body)| {
                    Some((
                        p.clone(),
                        remap_body_go(budget, body, count, map, e + p.bind_count(), bd)?,
                    ))
                })
                .collect::<Option<Vec<_>>>()?,
        ),
        Tm::Sum(xn, xp, xc) => Tm::Sum(
            xn.clone(),
            xp.iter()
                .map(|(n, v, t, i)| {
                    Some((
                        n.clone(),
                        remap_body_go(budget, v, count, map, e, bd)?,
                        remap_body_go(budget, t, count, map, e, bd)?,
                        *i,
                    ))
                })
                .collect::<Option<Vec<_>>>()?,
            xc.clone(),
        ),
        Tm::SumCase {
            typ,
            case_name,
            datas,
        } => Tm::SumCase {
            typ: Box::new(remap_body_go(budget, typ, count, map, e, bd)?),
            case_name: case_name.clone(),
            datas: datas
                .iter()
                .map(|(n, v, i)| {
                    Some((
                        n.clone(),
                        remap_body_go(budget, v, count, map, e, bd)?,
                        *i,
                    ))
                })
                .collect::<Option<Vec<_>>>()?,
        },
        Tm::Obj(x, n) => Tm::Obj(
            Box::new(remap_body_go(budget, x, count, map, e, bd)?),
            n.clone(),
        ),
        Tm::AppPruning(t, pr) => Tm::AppPruning(
            Box::new(remap_body_go(budget, t, count, map, e, bd)?),
            pr.clone(),
        ),
        other => other.clone(),
    })
}

/// 尝试判定两侧 match 分支体在"按值对齐的槽位布局"下是否相等。
///
/// 两侧 match 的捕获 env 常是同一组变量的不同上下文副本（如 meta 解经
/// prune/rename 后比使用现场少/多槽位）：字面 tm_eq 失败，但按值建立槽位
/// 对应后把一侧分支体重映射到另一侧布局，字面比较即可判定语义相等。
/// 返回 None = 无法建立对齐或对齐后仍不等（回落到逐分支求值路径）。
pub fn bodies_eq_aligned(
    s1: &Val,
    s2: &Val,
    env1: &Env,
    env2: &Env,
    cases1: &[(PatternDetail, Tm)],
    cases2: &[(PatternDetail, Tm)],
) -> Option<bool> {
    let mut budget = EqBudget(EQ_BUDGET);
    if !val_eq_go(&mut budget, s1, s2) {
        return None;
    }
    // 方向一：把 env2 侧的分支体重映射到 env1 的布局
    {
        let map = build_pos_map(&mut budget, env1, env2);
        let mut ok = true;
        for ((p1, b1), (p2, b2)) in cases1.iter().zip(cases2.iter()) {
            if p1 != p2 {
                return None;
            }
            match remap_body_go(&mut budget, b2, p2.bind_count(), &map, 0, 0) {
                Some(b2r) => {
                    if !tm_eq_go(&mut budget, b1, &b2r) {
                        ok = false;
                        break;
                    }
                }
                None => {
                    ok = false;
                    break;
                }
            }
        }
        if ok {
            return Some(true);
        }
    }
    // 方向二：对称（把 env1 侧的分支体重映射到 env2 的布局）
    {
        let map = build_pos_map(&mut budget, env2, env1);
        let mut ok = true;
        for ((p1, b1), (p2, b2)) in cases1.iter().zip(cases2.iter()) {
            if p1 != p2 {
                return None;
            }
            match remap_body_go(&mut budget, b1, p1.bind_count(), &map, 0, 0) {
                Some(b1r) => {
                    if !tm_eq_go(&mut budget, &b1r, b2) {
                        ok = false;
                        break;
                    }
                }
                None => {
                    ok = false;
                    break;
                }
            }
        }
        if ok {
            return Some(true);
        }
    }
    None
}
