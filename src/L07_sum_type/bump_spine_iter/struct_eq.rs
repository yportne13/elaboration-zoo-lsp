//! struct_eq：结构相等快路径（不 force、不展开、不求值，budget 封顶）——
//! `SEqTask`/`seq_run`/`seq_step_t`/`EqBudget`。原 bump_spine_iter.rs
//! 的 "结构相等" 节，逐行搬运（2026-09-19 拆分）。

use super::parser::syntax::Icit;

use super::env::{env_len, Env};
use super::spine::Spine;
use super::subst::InlineStack;
use super::syntax::{
    pending_len, PrCons, Tm, V, XCell, v_clo_of, v_lvl_of, v_meta_of, v_pi_of, v_spine_of,
    v_tag, v_xcell_of,
};

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
    // 迭代实现（2026-09-18，README §7.6）：深 Tm 树（succ^N 的 quote 产物）
    // 按树深递归会在万级深度爆栈。Tm 树不含值引用——T-only 任务栈即可，
    // 燃烧面 = 每 T 任务烧 1（对齐旧 struct_tm_eq_go 入口）。
    let mut budget = EqBudget(EQ_BUDGET);
    let mut stack = InlineStack::<SEqTask<'_>, 16>::with_first(SEqTask::T(a, b));
    while let Some(t) = stack.pop() {
        let SEqTask::T(x, y) = t else { unreachable!() };
        if !seq_step_t(&mut stack, &mut budget, x, y) {
            return false;
        }
    }
    true
}

pub(super) fn struct_val_eq(spine: &Spine, defs: &[V], a: V, b: V) -> bool {
    seq_run(spine, defs, SEqTask::V(a, b))
}

pub(super) fn struct_env_eq(spine: &Spine, defs: &[V], a: Env<'_>, b: Env<'_>) -> bool {
    seq_run(spine, defs, SEqTask::Env(a, b))
}

#[derive(Clone, Copy)]
enum SEqTask<'a> {
    V(V, V),
    T(&'a Tm<'a>, &'a Tm<'a>),
    Spine(usize, usize),
    Env(Env<'a>, Env<'a>),
}

/// 一对 Tm 的展开（值主循环与 T-only 入口共用）：子任务压栈（逆序，pop 序
/// = 旧递归访问序），零成本判定失败返回 false。
fn seq_step_t<'a>(
    stack: &mut InlineStack<SEqTask<'a>, 16>,
    budget: &mut EqBudget,
    a: &'a Tm<'a>,
    b: &'a Tm<'a>,
) -> bool {
    if !budget.spend() {
        return false;
    }
    match (a, b) {
        (Tm::Var(x), Tm::Var(y)) => x == y,
        (Tm::Decl(x), Tm::Decl(y)) | (Tm::Prim(x), Tm::Prim(y)) => x == y,
        (Tm::Obj(x, n), Tm::Obj(y, m)) => {
            n == m && {
                stack.push(SEqTask::T(x, y));
                true
            }
        }
        (Tm::App(x, xu, i), Tm::App(y, yu, j)) => {
            i == j && {
                stack.push(SEqTask::T(xu, yu));
                stack.push(SEqTask::T(x, y));
                true
            }
        }
        (Tm::Lam(_, i, x), Tm::Lam(_, j, y)) => {
            i == j && {
                stack.push(SEqTask::T(x, y));
                true
            }
        }
        (Tm::U, Tm::U) => true,
        (Tm::Pi(_, i, xa, xb), Tm::Pi(_, j, ya, yb)) => {
            i == j && {
                stack.push(SEqTask::T(xb, yb));
                stack.push(SEqTask::T(xa, ya));
                true
            }
        }
        (Tm::Let(_, xa, xb, xc), Tm::Let(_, ya, yb, yc)) => {
            stack.push(SEqTask::T(xc, yc));
            stack.push(SEqTask::T(xb, yb));
            stack.push(SEqTask::T(xa, ya));
            true
        }
        (Tm::Meta(x), Tm::Meta(y)) => x == y,
        (Tm::AppPruning(x, p), Tm::AppPruning(y, q)) => {
            let (sp, sq) = (pr_slots(p), pr_slots(q));
            sp.len() == sq.len()
                && sp.iter().zip(sq.iter()).all(|(a, b)| a == b)
                && {
                    stack.push(SEqTask::T(x, y));
                    true
                }
        }
        (Tm::LiteralType, Tm::LiteralType) => true,
        (Tm::LiteralIntro(x), Tm::LiteralIntro(y)) => x == y,
        (Tm::Sum(xn, xp, _), Tm::Sum(yn, yp, _)) => {
            xn == yn
                && xp.len() == yp.len()
                && xp.iter().zip(yp.iter()).all(|(a, b)| a.icit == b.icit)
                && {
                    for (a, b) in xp.iter().zip(yp.iter()).rev() {
                        stack.push(SEqTask::T(a.ty, b.ty));
                        stack.push(SEqTask::T(a.val, b.val));
                    }
                    true
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
            xn == yn
                && xd.len() == yd.len()
                && xd.iter().zip(yd.iter()).all(|(a, b)| a.icit == b.icit)
                && {
                    for (a, b) in xd.iter().zip(yd.iter()).rev() {
                        stack.push(SEqTask::T(a.val, b.val));
                    }
                    stack.push(SEqTask::T(xt, yt));
                    true
                }
        }
        (Tm::Match(xs, xc), Tm::Match(ys, yc)) => {
            xc.len() == yc.len()
                && xc.iter().zip(yc.iter()).all(|((p, _), (q, _))| p == q)
                && {
                    for ((_, xb), (_, yb)) in xc.iter().zip(yc.iter()).rev() {
                        stack.push(SEqTask::T(xb, yb));
                    }
                    stack.push(SEqTask::T(xs, ys));
                    true
                }
        }
        _ => false,
    }
}

/// 结构比较主循环（迭代实现，2026-09-18 README §7.6）：与旧递归
/// （struct_val_eq_go / struct_env_eq_go / struct_spine_eq_go）同一遍历面、
/// 同一燃烧面（V/T 任务各烧 1；Env/Spine 展开不烧），子任务逆序压栈保持
/// 短路访问序。深值（succ^N 链）不再按值深度吃 native 栈。
fn seq_run(spine: &Spine, defs: &[V], first: SEqTask<'_>) -> bool {
    let mut budget = EqBudget(EQ_BUDGET);
    let mut stack = InlineStack::<SEqTask<'_>, 16>::with_first(first);
    let mut a1: Vec<(V, Icit)> = Vec::new();
    let mut a2: Vec<(V, Icit)> = Vec::new();
    let mut vbuf: Vec<(V, V)> = Vec::new();
    while let Some(t) = stack.pop() {
        match t {
            SEqTask::T(x, y) => {
                if !seq_step_t(&mut stack, &mut budget, x, y) {
                    return false;
                }
            }
            SEqTask::V(x, y) => {
                if !budget.spend() {
                    return false;
                }
                match (v_tag(x), v_tag(y)) {
                    (0, 0) => {
                        if v_lvl_of(x) != v_lvl_of(y) {
                            return false;
                        }
                    }
                    (5, 5) => {
                        if v_meta_of(x) != v_meta_of(y) {
                            return false;
                        }
                    }
                    (3, 3) | (6, 6) => {}
                    (1, 1) => {
                        let (c1, c2) = (v_clo_of(x), v_clo_of(y));
                        if c1.icit != c2.icit {
                            return false;
                        }
                        stack.push(SEqTask::T(c1.body, c2.body));
                        stack.push(SEqTask::Env(c1.env, c2.env));
                    }
                    (4, 4) => {
                        let (p1, p2) = (v_pi_of(x), v_pi_of(y));
                        if p1.icit != p2.icit {
                            return false;
                        }
                        stack.push(SEqTask::T(p1.body, p2.body));
                        stack.push(SEqTask::Env(p1.env, p2.env));
                        stack.push(SEqTask::V(p1.dom, p2.dom));
                    }
                    (2, 2) => stack.push(SEqTask::Spine(v_spine_of(x), v_spine_of(y))),
                    (7, 7) => match (v_xcell_of(x), v_xcell_of(y)) {
                        // 精化包裹：仅同一替换实例（同 Rc）且内层结构相等才短路；
                        // 异实例一律回落慢路径（慢路径的 force 会推开 VSub）
                        (XCell::VSub { val: a, sub: sa }, XCell::VSub { val: b, sub: sb }) => {
                            if !std::rc::Rc::ptr_eq(sa, sb) {
                                return false;
                            }
                            stack.push(SEqTask::V(*a, *b));
                        }
                        (XCell::VSub { .. }, _) | (_, XCell::VSub { .. }) => return false,
                        (XCell::Lit(a), XCell::Lit(b)) => {
                            if a != b {
                                return false;
                            }
                        }
                        (XCell::Decl(a), XCell::Decl(b)) => {
                            if a != b {
                                return false;
                            }
                        }
                        (XCell::Prim(a), XCell::Prim(b)) => {
                            if a != b {
                                return false;
                            }
                        }
                        (XCell::Obj { val: a, name: an }, XCell::Obj { val: b, name: bn }) => {
                            if an != bn {
                                return false;
                            }
                            stack.push(SEqTask::V(*a, *b));
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
                            if xn != yn || xp.len() != yp.len() {
                                return false;
                            }
                            for (a, b) in xp.iter().zip(yp.iter()) {
                                if a.icit != b.icit {
                                    return false;
                                }
                            }
                            for (a, b) in xp.iter().zip(yp.iter()).rev() {
                                stack.push(SEqTask::V(a.ty, b.ty));
                                stack.push(SEqTask::V(a.val, b.val));
                            }
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
                            if xn != yn || xd.len() != yd.len() {
                                return false;
                            }
                            for (a, b) in xd.iter().zip(yd.iter()) {
                                if a.icit != b.icit {
                                    return false;
                                }
                            }
                            for (a, b) in xd.iter().zip(yd.iter()).rev() {
                                stack.push(SEqTask::V(a.val, b.val));
                            }
                            stack.push(SEqTask::V(*xt, *yt));
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
                            if xc.len() != yc.len() || pending_len(*xp) != pending_len(*yp) {
                                return false;
                            }
                            for ((p, _), (q, _)) in xc.iter().zip(yc.iter()) {
                                if p != q {
                                    return false;
                                }
                            }
                            // pending 沿双链同步走（头 = 最新）：icit 逐对检查
                            //（纯等词，与序无关），值对随走随压——栈序与切片
                            // 版 `.rev()` 相同，LIFO 弹出恢复应用序
                            let (mut c1, mut c2) = (*xp, *yp);
                            while let (Some(x), Some(y)) = (c1, c2) {
                                if x.arg.1 != y.arg.1 {
                                    return false;
                                }
                                stack.push(SEqTask::V(x.arg.0, y.arg.0));
                                c1 = x.next;
                                c2 = y.next;
                            }
                            // 访问序（旧递归）：scrutinee → env → 分支体 → pending
                            for ((_, xb), (_, yb)) in xc.iter().zip(yc.iter()).rev() {
                                stack.push(SEqTask::T(xb, yb));
                            }
                            stack.push(SEqTask::Env(*xe, *ye));
                            stack.push(SEqTask::V(*xs, *ys));
                        }
                        _ => return false,
                    },
                    _ => return false,
                }
            }
            SEqTask::Spine(h1, h2) => {
                // 头也要同（bit-equal 或同名 Decl/Prim/同 Obj 结构）；
                // 展开不烧（对齐旧 struct_spine_eq_go）
                if spine.spine_len(h1) != spine.spine_len(h2) {
                    return false;
                }
                a1.clear();
                spine.collect_args(h1, &mut a1);
                a2.clear();
                spine.collect_args(h2, &mut a2);
                for ((_, i), (_, j)) in a1.iter().zip(a2.iter()) {
                    if i != j {
                        return false;
                    }
                }
                for ((x, _), (y, _)) in a1.iter().zip(a2.iter()).rev() {
                    stack.push(SEqTask::V(*x, *y));
                }
                stack.push(SEqTask::V(spine.spine_head(h1), spine.spine_head(h2)));
            }
            SEqTask::Env(a, b) => {
                // 单趟双链（槽序与 env_nth 一致）；展开不烧（对齐旧
                // struct_env_eq_go）。逆序压栈保持槽序短路。
                let la = env_len(a);
                if la != env_len(b) {
                    return false;
                }
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
                    vbuf.push((va, vb));
                }
                for (va, vb) in vbuf.drain(..).rev() {
                    stack.push(SEqTask::V(va, vb));
                }
            }
        }
    }
    true
}
