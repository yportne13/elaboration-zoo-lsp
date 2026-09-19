//! unify：工作表迭代合一（`UItem`/`unify_iter`）+ intersect/flex-flex
//! （`intersect_bump`/`flex_flex_bump`）+ 同头 lockstep + pm 特化臂。
//! 原 bump_spine_iter.rs 的 "unify" 节，逐行搬运（2026-09-19 拆分）。

use bumpalo::Bump;
use rustc_hash::FxHashMap;
use std::rc::Rc;

use super::parser::syntax::Icit;
use super::PatternDetail;

use super::env::{env_ext, Env};
use super::eval::{eval_iter, W};
use super::force::{force, vapp1, vapp_ok, val_mentions_lvl};
use super::machine::ConvScratch;
use super::prim::{DeclEntryF, Fuel, MutableMap};
use super::rename::{invert_bump, prune_meta_bump, solve_bump, solve_with_pren_bump, RenBuf};
use super::spine::{head_kind, is_flex, is_objheaded, xcell_head_name, HK_DECL, HK_OBJ, HK_PRIM, MetaEntry, Spine};
use super::struct_eq::{struct_env_eq, struct_tm_eq, struct_val_eq};
use super::subst::{simpl_decl, wrap_sub, SpecSolve, SubstV};
use super::syntax::{
    pending_len, pending_struct_eq, Tm, V, XCell, v_clo_of, v_lit_ty, v_lvl, v_lvl_of,
    v_meta_of,
    v_pi_of, v_spine_of, v_tag, v_xcell_of,
};

// unify（工作表迭代 + force 前置 + 模式求解 + intersect/flex-flex + L07 臂）
// --------------------------------------------------------------------------------

/// A/B 实验开关（unify 工作表的判等记忆化消融）：置 `L06_NO_CONV_MEMO=1`
/// 关闭（`=0` 不关闭）。
static NO_CONV_MEMO: std::sync::LazyLock<std::sync::atomic::AtomicBool> =
    std::sync::LazyLock::new(|| {
        std::sync::atomic::AtomicBool::new(std::env::var("L06_NO_CONV_MEMO").is_ok_and(|v| v != "0"))
    });

// （旧 `pm_solve_into` / `pm_solvable_contains` 已随事实表机制删除：解入
// `SpecSolve::acc`（`SubstV::extend`）+ 入口 `val_mentions_lvl` occurs 守卫，
// 可解集经 `SpecSolve.solvable` 穿参——见 `unify_iter` 的特化臂。）

/// unify 工作表条目：待比较子对、Π 余定义域的惰性比较屏障、判等记忆化
/// 屏障、或卡住 match 分支对的惰性求值屏障（简化 decl 表下重求值后压
/// `l+count` 层的体对）。
pub(super) enum UItem<'a> {
    /// 待比较子对（level 相同的一对值；弹出时先 force 双方再分派）。
    Pair(u32, V, V),
    /// Π 余定义域的惰性比较（排在 dom 对之下——dom 不等即失败，cod 的
    /// eval 整个省掉）。
    EvalCod2(&'a Tm<'a>, Env<'a>, &'a Tm<'a>, Env<'a>, u32),
    /// 判等记忆化屏障（LIFO；健壮性论证同 L03——solve 写一次、成功单调）。
    Store((u64, u64)),
    /// 卡住 match 的一个分支对：两侧体在"各自捕获 env + fresh rigid 槽"
    /// 下用简化 decl 表重求值，再压 `l + count` 层的体对。弹出时**先比
    /// 模式**（参考版逐分支交错：先 `p1 != p2` 失败、后体合一——Err 路径
    /// 上 scrutinee / 前序分支的 meta 副作用保留）。
    MatchBranch {
        p1: &'a PatternDetail,
        p2: &'a PatternDetail,
        b1: &'a Tm<'a>,
        e1: Env<'a>,
        b2: &'a Tm<'a>,
        e2: Env<'a>,
        declb: Rc<FxHashMap<String, DeclEntryF>>,
        l: u32,
        count: u32,
    },
    /// 卡住 match Match/Match 的分支数预检屏障：排在 scrutinee 对**之下**
    /// 弹出（参考版顺序：scrutinee 合一 → 分支数检查 → 逐分支）。旧实现
    /// 把全部结构预检前置，Err 路径上 scrutinee 合一的 meta 副作用被吞掉
    /// ——spec 合一经 `unify_indices` 映射 `Walk::Unreachable` 后编译
    /// 继续，副作用可观测（"unify 错误均致命"的论证不成立于 spec 路径）。
    MatchPrecheck {
        c1: &'a [(PatternDetail, &'a Tm<'a>)],
        c2: &'a [(PatternDetail, &'a Tm<'a>)],
    },
    /// pending 实参数长度屏障：全部分支比完后弹出（参考版在分支循环后
    /// 才查 `pending1.len() != pending2.len()`）。
    MatchPendingLen(usize, usize),
    /// pending 实参对：先比 icit 再压值对（参考版循环体顺序）。
    MatchPending {
        l: u32,
        u1: V,
        i1: Icit,
        u2: V,
        i2: Icit,
    },
}

/// `?m args ≡ ?m args'`（同头 flex）：上游 `intersect`。逐槽（内→外）
/// 都取到裸变量则产出掩码（槽位相等 → 其 icit、不等 → None）；有 None 即
/// 剪枝（`pruneMeta`），全相等即成立。长度不等直接失败（参考版
/// intersect_go 的 `_ => None` → unify_sp 长度失配分支：失配即败、零比较）。
/// 任一对含非变量 → 回落 `unify_sp` 逐实参比较。
#[allow(clippy::too_many_arguments)]
pub(super) fn intersect_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    stack: &mut Vec<UItem<'a>>,
    l: u32,
    m: u32,
    args1: &[(V, Icit)], // 内先（collect_args 的产出序）
    args2: &[(V, Icit)],
) -> bool {
    let n1 = args1.len();
    let n2 = args2.len();
    if n1 != n2 {
        return false; // 长度失配：直败零比较（连 force/压栈都省）
    }
    let common = n1;
    let mut pr: Vec<Option<Icit>> = Vec::with_capacity(common);
    let mut fallback = false;
    for k in 0..common {
        let f1 = force(
            bump, spine, defs, metas, decls, mmap, fuel, args1[k].0,
        );
        let f2 = force(
            bump, spine, defs, metas, decls, mmap, fuel, args2[k].0,
        );
        if v_tag(f1) == 0 && v_tag(f2) == 0 {
            pr.push(if v_lvl_of(f1) == v_lvl_of(f2) {
                Some(args1[k].1)
            } else {
                None
            });
        } else {
            fallback = true; // 上游 go 的 None：回落 unify_sp
            break;
        }
    }
    if !fallback {
        if pr.iter().any(|x| x.is_none()) {
            return prune_meta_bump(
                bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, &pr, m,
            )
            .is_some();
        }
        return true; // 两 spine 逐槽相等
    }
    // unify_sp 回落：前缀对压栈（内先压 → 弹出外先，对齐 unify_sp 的递归序）。
    // tag 7 不跳过：参考版对字面量实参照走 unify（恒败）、对 Decl/Prim 实参
    // 照走同名逐参——位相等的同单元也须分派（见 unify 的 tag 7 守卫）。
    // Obj 头的位相等链（tag 2 + hk=Obj）同样不免：参考版 intersect_go 只收
    // 裸 Rigid，其余一律回落 unify_sp，而 Obj/Obj 无 unify 臂恒败（与
    // unify_sp_lockstep 的跳过守卫同款）。
    for k in 0..common {
        let (a1, _) = args1[k];
        let (a2, _) = args2[k];
        if a1.0 != a2.0
            || v_tag(a1) == 7
            || (v_tag(a1) == 2 && spine.stack[v_spine_of(a1)].hk == HK_OBJ)
        {
            stack.push(UItem::Pair(l, a1, a2));
        }
    }
    true
}

/// 异头 flex-flex（上游 `flexFlex`）：**短 spine 一侧优先**反演求解；反演
/// 失败则用另一侧求解（rhs 是整条 flex 值）。第一次尝试可能已 solve 部分
/// meta 才失败，反向尝试前回滚（参考版 meta 快照同款）。
#[allow(clippy::too_many_arguments)]
pub(super) fn flex_flex_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    ren: &mut RenBuf,
    gamma: u32,
    m1: u32,
    args1: &[(V, Icit)],
    v1: V,
    m2: u32,
    args2: &[(V, Icit)],
    v2: V,
) -> bool {
    // 方向选择与参考版一致：`sp.len() <= sp_prime.len()` → (m, sp) 先
    let (fa, aa, va, fb, ab, vb) = if args1.len() <= args2.len() {
        (m1, args1, v1, m2, args2, v2)
    } else {
        (m2, args2, v2, m1, args1, v1)
    };
    let snap = metas.clone();
    match invert_bump(bump, spine, defs, metas, decls, mmap, fuel, ren, gamma, aa) {
        Some(mask) => {
            if solve_with_pren_bump(
                bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, ren,
                gamma, fa, aa.len() as u32, mask, va,
            ) {
                return true;
            }
        }
        None => {
            // 一侧非模式：落另一侧（solve = invert + solve_with_pren）
            match invert_bump(
                bump, spine, defs, metas, decls, mmap, fuel, ren, gamma, ab,
            ) {
                Some(mask) => {
                    if solve_with_pren_bump(
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, ren, gamma, fb, ab.len() as u32, mask, vb,
                    ) {
                        return true;
                    }
                }
                None => return false,
            }
        }
    }
    // 首选方向失败：回滚 meta 快照，反向再试一次
    *metas = snap;
    match invert_bump(bump, spine, defs, metas, decls, mmap, fuel, ren, gamma, ab) {
        Some(mask) => solve_with_pren_bump(
            bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, ren, gamma,
            fb, ab.len() as u32, mask, vb,
        ),
        None => false,
    }
}

/// 同头链（unify_sp）的实参 lockstep 比较：长度失配即败；实参 icit 不比
/// （类型已定，上游同款）。位相等的实参对免比（tag 7 与 Obj 头链除外——
/// 字面量恒败、Decl/Prim 走同名分派、Obj 无臂恒败）。
#[allow(clippy::too_many_arguments)]
fn unify_sp_lockstep<'a>(
    spine: &Spine,
    stack: &mut Vec<UItem<'a>>,
    l: u32,
    h1: usize,
    h2: usize,
) -> bool {
    if spine.spine_len(h1) != spine.spine_len(h2) {
        return false;
    }
    let mut i1 = h1;
    let mut i2 = h2;
    loop {
        let (f1, a1) = {
            let e = &spine.stack[i1];
            (e.f, e.a)
        };
        let (f2, a2) = {
            let e = &spine.stack[i2];
            (e.f, e.a)
        };
        // 位相等后缀：实参对免比（tag 7 除外）；函数部分对仍须入栈。
        // Obj 头的链（tag 2 + hk=Obj）同样不免——参考版恒败。
        let skip1 = a1.0 == a2.0 && v_tag(a1) != 7 && !(v_tag(a1) == 2 && spine.stack[v_spine_of(a1)].hk == HK_OBJ);
        if skip1 {
            if f1.0 != f2.0 {
                stack.push(UItem::Pair(l, f1, f2));
            }
            break;
        }
        if v_tag(a1) == 2 && v_tag(a2) == 2 {
            // 下钻门控：两侧的实参链顶层 f 与本层 f 同字（纯 ChainWrap 同头
            // 延续）；实参若是另一条中性链（Apply 惯例：`f` = partial 句柄
            // ≠ 头字）则停下，把子对交回完整分派。派发序与参考版 unify_sp
            // 同序：停钻时先压实参对、后压函数部分对。
            let cont = spine.stack[v_spine_of(a1)].f.0 == f1.0
                && spine.stack[v_spine_of(a2)].f.0 == f2.0;
            if cont {
                if f1.0 != f2.0 {
                    stack.push(UItem::Pair(l, f1, f2));
                }
                i1 = v_spine_of(a1);
                i2 = v_spine_of(a2);
                continue;
            }
        }
        stack.push(UItem::Pair(l, a1, a2));
        if f1.0 != f2.0 {
            stack.push(UItem::Pair(l, f1, f2));
        }
        break;
    }
    true
}

/// unification：结构比较 + 模式求解（含 intersect / flex-flex / 剪枝），
/// 工作表迭代。臂序与参考版 `Infer::unify` 逐项对应（顺序敏感处：pm 特化
/// 臂在 Flex/λ/η 臂之前；λ/η 在 Flex 求解之前；Flex 求解在
/// LiteralType/Prim/Sum/SumCase/Match 臂之前）：
/// U → Π（icit 相等）→ pm 特化（双侧）→ Decl/Decl 同名 → λ/η → 中性链
/// （双 flex = intersect/flex_flex、同头 lockstep、异头单 flex = solve）→
/// flex 求解 → LiteralType/宽松臂 → Prim/Prim → Sum/Sum → SumCase/SumCase
/// → Match/Match → Match 严格 η → 失配。
/// **位相等捷径与实参跳过对 tag 7 与 Obj 头链关闭**：参考版 unify 无
/// `(Lit, Lit)` / `(Obj, Obj)` 臂——同字面量也 Err，同单元 Obj 也 Err。
/// **模式特化与常规转换共用本合一器**：可解性经 `spec: Option<&mut
/// SpecSolve>` 显式穿参——`spec` 非空（模式走查 / 覆盖探测）时 bare rigid
/// 可解，解记入 `spec.acc`（显式替换，force 读点惰性展开）；`spec = None`
/// （分支体检查等常规转换）时不得解假设。工作表上排队的三类子项（unify_sp
/// lockstep / intersect 回落 / 宽松臂 / Match 分支对）弹出时在本入口统一
/// "置于当时 acc 之下"，与参考版把这些子方程递归回 unify 的穿参时点一致。
#[allow(clippy::too_many_arguments)]
pub(super) fn unify_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    mut stack: &mut Vec<UItem<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    ren: &mut RenBuf,
    conv: &mut ConvScratch,
    fuel: &Fuel,
    mut spec: Option<&mut SpecSolve<'_>>,
    l0: u32,
    t0: V,
    u0: V,
) -> bool {
    let memo_on = !NO_CONV_MEMO.load(std::sync::atomic::Ordering::Relaxed);
    // 草稿复用（Machine 常驻）：清空保容量，热路径零分配
    conv.memo.clear();
    conv.scratch1.clear();
    conv.scratch2.clear();
    let memo = &mut conv.memo;
    stack.clear();
    stack.push(UItem::Pair(l0, t0, u0));
    while let Some(item) = stack.pop() {
        let (l, t, u) = match item {
            UItem::Store(key) => {
                memo.insert(key);
                continue;
            }
            UItem::EvalCod2(b1, e1, b2, e2, l) => {
                let vt = {
                    let env = env_ext(bump, e1, v_lvl(l));
                    eval_iter(
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, env, b1,
                    )
                };
                let vu = {
                    let env = env_ext(bump, e2, v_lvl(l));
                    eval_iter(
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, env, b2,
                    )
                };
                stack.push(UItem::Pair(l + 1, vt, vu));
                continue;
            }
            UItem::MatchBranch {
                p1,
                p2,
                b1,
                e1,
                b2,
                e2,
                declb,
                l,
                count,
            } => {
                // 先比模式（参考版逐分支交错：p1 != p2 即败，前序副作用保留）
                if p1 != p2 {
                    return false;
                }
                // 分支体：两侧各自"捕获 env + fresh rigid 槽（count =
                // bind_count，lvl 从 l 起）"下用简化 decl 表重求值，再在
                // l+count 层比较（参考版 unify 的 Match/Match 全路径同款）
                let mut env1 = e1;
                let mut env2 = e2;
                for i in 0..count {
                    env1 = env_ext(bump, env1, v_lvl(l + i));
                    env2 = env_ext(bump, env2, v_lvl(l + i));
                }
                let v1 = eval_iter(
                    bump, spine, work, vals, icits, defs, metas, &declb, mmap, fuel, env1, b1,
                );
                let v2 = eval_iter(
                    bump, spine, work, vals, icits, defs, metas, &declb, mmap, fuel, env2, b2,
                );
                stack.push(UItem::Pair(l + count, v1, v2));
                continue;
            }
            UItem::MatchPrecheck { c1, c2 } => {
                // scrutinee 合一之后的分支数检查（参考版顺序）
                if c1.len() != c2.len() {
                    return false;
                }
                continue;
            }
            UItem::MatchPendingLen(n1, n2) => {
                // 全部分支比完后的 pending 长度检查（参考版顺序）
                if n1 != n2 {
                    return false;
                }
                continue;
            }
            UItem::MatchPending {
                l,
                u1,
                i1,
                u2,
                i2,
            } => {
                // 先比 icit 再压值对（参考版循环体顺序）
                if i1 != i2 {
                    return false;
                }
                stack.push(UItem::Pair(l, u1, u2));
                continue;
            }
            UItem::Pair(l, t, u) => (l, t, u),
        };
        // 递归深度防护：每个子对一次（参考版 unify 每次调用消耗 1）
        let f = fuel.get();
        if f == 0 {
            return false;
        }
        fuel.set(f - 1);
        // 位相等：同一值。tag 7 与 Obj 头链例外（见函数注释——参考版对
        // 字面量/Obj 无自反性，Decl/Prim 需同名分派）
        if t.0 == u.0 && v_tag(t) != 7 && !is_objheaded(spine, t) {
            continue;
        }
        if memo_on && memo.contains(&(t.0, u.0)) {
            continue; // 本轮已判等过的子对（命中连 force 都省——成功单调）
        }
        let mut t = force(
            bump, spine, defs, metas, decls, mmap, fuel, t,
        );
        let mut u = force(
            bump, spine, defs, metas, decls, mmap, fuel, u,
        );
        if t.0 == u.0 && v_tag(t) != 7 && !is_objheaded(spine, t) {
            continue; // force 展开后同值（同一解的两处引用）
        }
        // 特化模式：方程两侧置于**当前已积累的解**之下再解释（参考版
        // `unify` 入口的 wrap_sub(&s.acc, ·)，dpm-nbe `subst ɑ vs` 的惰性
        // 等价物）。每次递归入口按当时的 acc 重新包裹——先解出的方程对后
        // 到的子方程自动可见，解两次的情形按构造排除（已解变量不再以
        // bare rigid 出现）。acc 为空时零开销。
        if let Some(s) = spec.as_deref() {
            if !s.acc.is_empty() {
                let acc = s.acc.clone();
                let t2 = force(
                    bump, spine, defs, metas, decls, mmap, fuel, wrap_sub(bump, &acc, t),
                );
                let u2 = force(
                    bump, spine, defs, metas, decls, mmap, fuel, wrap_sub(bump, &acc, u),
                );
                t = t2;
                u = u2;
            }
        }

        // —— 宇宙（参考臂 1）——
        if v_tag(t) == 3 && v_tag(u) == 3 {
            continue;
        }
        // —— Π：icit 相等才比（参考臂 2）；icit 失配落到后续臂 ——
        if v_tag(t) == 4 && v_tag(u) == 4 {
            let p = v_pi_of(t);
            let q = v_pi_of(u);
            if p.icit == q.icit {
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                // 先比定义域，再惰性 eval 两侧余定义域
                stack.push(UItem::EvalCod2(p.body, p.env, q.body, q.env, l));
                stack.push(UItem::Pair(l, p.dom, q.dom));
                continue;
            }
        }
        // —— pm 特化臂（参考臂 4/5，**在 Flex/λ/η 之前**——顺序敏感；
        // dpm-nbe unify1 的 VVar 臂）：可解 rigid（spec 携带的模式槽集）
        // 与非 Flex 值相遇 ⇒ 解入 `spec.acc`（显式替换，force 读点惰性
        // 展开）。Flex 除外——交给 Flex 规则（meta := var）。occurs 环守卫
        // 失败 = 失败（对齐旧 pm_solve false ⇒ Err：调用侧判为分支不可
        // 达）。spec = None（常规转换）时守卫不成立，落空到后续臂——不得
        // 解假设，否则 `Eq x y` 会被"证成" `Eq y y`。调用侧"头部一侧在前"，
        // 双侧都可解时解的方向是"头部变量 := 构造子侧值"。
        if v_tag(t) == 0
            && matches!(
                spec.as_deref(),
                Some(s) if s.solvable.contains(&v_lvl_of(t))
            )
            && !is_flex(spine, u)
        {
            if val_mentions_lvl(spine, defs, u, v_lvl_of(t)) {
                return false;
            }
            let s = spec.as_deref_mut().unwrap();
            s.acc = SubstV::extend(&s.acc, v_lvl_of(t), u);
            continue;
        }
        if v_tag(u) == 0
            && matches!(
                spec.as_deref(),
                Some(s) if s.solvable.contains(&v_lvl_of(u))
            )
            && !is_flex(spine, t)
        {
            if val_mentions_lvl(spine, defs, t, v_lvl_of(u)) {
                return false;
            }
            let s = spec.as_deref_mut().unwrap();
            s.acc = SubstV::extend(&s.acc, v_lvl_of(u), t);
            continue;
        }
        // —— (0,0) 裸刚性对早退：同 level 的对已被位相等捷径剪掉
        // （force 前后各一次），到这里必是异 level、必不等——免去走完
        // 整个 cascade 的两次 flex_of scratch 往返（GADT 索引合一的常见
        // 失败形态）。语义与 L06 的 (0,0) 末臂同构；位置是 L07 新增——
        // 刚性对可被 pm 臂求解，pm 臂必须保持在前（L06 无 pm 臂；L08 已
        // 回补同款早退）——
        if v_tag(t) == 0 && v_tag(u) == 0 {
            return false;
        }
        // —— Decl/Decl 同名（参考臂 6）：同名比 spine（裸单元自反成立），
        // 异名落到后续臂（λ/η 等仍可命中）——
        if head_kind(spine, t) == HK_DECL && head_kind(spine, u) == HK_DECL {
            if xcell_head_name(spine, t) == xcell_head_name(spine, u) {
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                match (v_tag(t), v_tag(u)) {
                    (7, 7) => continue, // 双裸单元：unify_sp([][]) 自反成立
                    (2, 2) => {
                        if !unify_sp_lockstep(spine, &mut stack, l, v_spine_of(t), v_spine_of(u)) {
                            return false;
                        }
                        continue;
                    }
                    _ => return false, // 裸×带实参：长度失配（参考版 unify_sp 同败）
                }
            }
        }
        // —— λ / η（参考臂 9/10/11；在 Flex 求解之前：Flex vs λ 走 η）——
        if v_tag(t) == 1 && v_tag(u) == 1 {
            let c1 = v_clo_of(t);
            let c2 = v_clo_of(u);
            let vt = {
                let env = env_ext(bump, c1.env, v_lvl(l));
                eval_iter(
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, env, c1.body,
                )
            };
            let vu = {
                let env = env_ext(bump, c2.env, v_lvl(l));
                eval_iter(
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, env, c2.body,
                )
            };
            if memo_on {
                stack.push(UItem::Store((t.0, u.0)));
            }
            stack.push(UItem::Pair(l + 1, vt, vu));
            continue;
        }
        // η：中性一侧按 λ 一侧的 icit 应用（Decl/Prim/Obj 头的应用压链；
        // 卡住 match 吸收进 pending）。可应用性守卫 `vapp_ok`（参考版
        // `v_applicable` 同款）：不可应用一侧（字面量/U/Π/Sum/SumCase）
        // 不展开，落空后按合一失败返回
        if v_tag(u) == 1 && vapp_ok(t) {
            let c = v_clo_of(u);
            let vu = {
                let env = env_ext(bump, c.env, v_lvl(l));
                eval_iter(
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, env, c.body,
                )
            };
            let vt = vapp1(
                bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, t,
                v_lvl(l), c.icit,
            );
            if memo_on {
                stack.push(UItem::Store((t.0, u.0)));
            }
            stack.push(UItem::Pair(l + 1, vt, vu));
            continue;
        }
        if v_tag(t) == 1 && vapp_ok(u) {
            let c = v_clo_of(t);
            let vt = {
                let env = env_ext(bump, c.env, v_lvl(l));
                eval_iter(
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, env, c.body,
                )
            };
            let vu = vapp1(
                bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, u,
                v_lvl(l), c.icit,
            );
            if memo_on {
                stack.push(UItem::Store((t.0, u.0)));
            }
            stack.push(UItem::Pair(l + 1, vt, vu));
            continue;
        }
        // —— 中性链 vs 中性链（参考臂 3/6/7/8/12/13 的链形态全在此分派）——
        if v_tag(t) == 2 && v_tag(u) == 2 {
            let h1 = v_spine_of(t);
            let h2 = v_spine_of(u);
            let hd1 = spine.spine_head(h1);
            let hd2 = spine.spine_head(h2);
            let f1 = v_tag(hd1) == 5;
            let f2 = v_tag(hd2) == 5;
            if f1 && f2 {
                // 双 flex：同头 intersect、异头 flex_flex（参考臂 7/8）
                let mut a1 = std::mem::take(&mut conv.scratch1);
                a1.clear();
                spine.collect_args(h1, &mut a1);
                let mut a2 = std::mem::take(&mut conv.scratch2);
                a2.clear();
                spine.collect_args(h2, &mut a2);
                let m1 = v_meta_of(hd1);
                let m2 = v_meta_of(hd2);
                let ok = if m1 == m2 {
                    intersect_bump(
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, &mut stack, l, m1, &a1, &a2,
                    )
                } else {
                    flex_flex_bump(
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, ren, l, m1, &a1, u, m2, &a2, t,
                    )
                };
                conv.scratch1 = a1;
                conv.scratch2 = a2;
                if ok {
                    if memo_on {
                        memo.insert((t.0, u.0));
                    }
                    continue;
                }
                return false;
            }
            // 同头判定：位相等（同变量 / 同 meta / 同单元）或同名 Decl/Prim
            // 头（参考版比较 Span——名字全部来自 empty_span 构造，等价于名
            // 内容相等）。**Obj 头不进同头**：参考版无 (Obj, Obj) 臂。
            let same_head = (hd1.0 == hd2.0
                && !(v_tag(hd1) == 7 && matches!(v_xcell_of(hd1), XCell::Obj { .. })))
                || (v_tag(hd1) == 7
                    && v_tag(hd2) == 7
                    && matches!(
                        (v_xcell_of(hd1), v_xcell_of(hd2)),
                        (XCell::Decl(n1), XCell::Decl(n2)) if n1 == n2
                    ))
                || (v_tag(hd1) == 7
                    && v_tag(hd2) == 7
                    && matches!(
                        (v_xcell_of(hd1), v_xcell_of(hd2)),
                        (XCell::Prim(n1), XCell::Prim(n2)) if n1 == n2
                    ));
            if same_head {
                // 同头刚性/Decl/Prim：逐实参比较（lockstep，长度失配即败）
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                if !unify_sp_lockstep(spine, &mut stack, l, h1, h2) {
                    return false;
                }
                continue;
            }
            // 异头：一侧 flex 头（f1/f2 已排除双 flex）→ 该侧 solve（参考
            // 臂 12/13 的链形态）；双刚性/Decl/Prim 异头 → 失配。
            let (mv, h, rhs) = if f1 {
                (v_meta_of(hd1), h1, u)
            } else if f2 {
                (v_meta_of(hd2), h2, t)
            } else {
                return false;
            };
            let mut args = std::mem::take(&mut conv.scratch1);
            args.clear();
            spine.collect_args(h, &mut args);
            let solved = solve_bump(
                bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, ren, l,
                mv, &args, rhs,
            );
            conv.scratch1 = args;
            if solved {
                if memo_on {
                    memo.insert((t.0, u.0));
                }
                continue;
            }
            return false;
        }
        // —— 单侧（或双侧）裸 flex：solve（参考臂 7/8/12/13）。**在
        // LiteralType/Prim/Sum/SumCase/Match 臂之前**——flex vs 那些形态走
        // 求解而非失配 ——
        {
            let mut a1 = std::mem::take(&mut conv.scratch1);
            a1.clear();
            let ft = spine.flex_of(t, &mut a1);
            let mut a2 = std::mem::take(&mut conv.scratch2);
            a2.clear();
            let fu = spine.flex_of(u, &mut a2);
            match (ft, fu) {
                (Some(m1), Some(m2)) => {
                    let ok = if m1 == m2 {
                        intersect_bump(
                            bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel,
                            &mut stack, l, m1, &a1, &a2,
                        )
                    } else {
                        flex_flex_bump(
                            bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel,
                            ren, l, m1, &a1, u, m2, &a2, t,
                        )
                    };
                    conv.scratch1 = a1;
                    conv.scratch2 = a2;
                    if ok {
                        if memo_on {
                            memo.insert((t.0, u.0));
                        }
                        continue;
                    }
                    return false;
                }
                (Some(m), None) => {
                    let ok = solve_bump(
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, ren, l, m, &a1, u,
                    );
                    conv.scratch1 = a1;
                    conv.scratch2 = a2;
                    if ok {
                        if memo_on {
                            memo.insert((t.0, u.0));
                        }
                        continue;
                    }
                    return false;
                }
                (None, Some(m)) => {
                    let ok = solve_bump(
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, ren, l, m, &a2, t,
                    );
                    conv.scratch1 = a1;
                    conv.scratch2 = a2;
                    if ok {
                        if memo_on {
                            memo.insert((t.0, u.0));
                        }
                        continue;
                    }
                    return false;
                }
                (None, None) => {
                    conv.scratch1 = a1;
                    conv.scratch2 = a2;
                    // 非 flex：落到字面量 / Prim / Sum / SumCase / Match 臂
                }
            }
        }
        // —— (LiteralType, LiteralType)（参考臂 14）——
        if v_tag(t) == 6 && v_tag(u) == 6 {
            continue;
        }
        // —— 宽松臂（参考臂 15）：String 与卡住内建 / 卡住 Decl 的宽松合一
        // 只对 decl 表**未登记名**放行——string_to_global_type 对未知名返回
        // 以其名字的卡住 Decl（动态类型的逃逸舱口）；已登记名按登记类型把关
        // （U 型返回的 builtin 卡住值不再冒充 String）——
        if v_tag(t) == 6 || v_tag(u) == 6 {
            let other = if v_tag(t) == 6 { u } else { t };
            let oname: Option<&str> = match v_tag(other) {
                7 => match v_xcell_of(other) {
                    XCell::Decl(n) => Some(n),
                    XCell::Prim(n) => Some(n),
                    // 字面量值与 String 类型:刚性失配(参考版同)
                    _ => None,
                },
                2 => {
                    let hd = spine.spine_head(v_spine_of(other));
                    // 链头可能是裸 Rigid / Meta（打包立即数，不是指针）——
                    // 不看 tag 就 v_xcell_of 是野指针读；非卡住单元头按参考
                    // 版语义走宽松臂失败（`_ => Err`）。
                    match v_tag(hd) {
                        7 => match v_xcell_of(hd) {
                            XCell::Decl(n) => Some(n),
                            XCell::Prim(n) => Some(n),
                            _ => None,
                        },
                        _ => None,
                    }
                }
                _ => None,
            };
            match oname {
                Some(n) => match decls.get(n) {
                    None => continue, // 未登记名（可变全局等动态名）放行
                    Some(e) => {
                        stack.push(UItem::Pair(l, v_lit_ty(), e.ty));
                        continue;
                    }
                },
                None => return false, // (LitType, Lit) 等无宽松臂 → 失配
            }
        }
        // —— Prim/Prim（参考臂 16）：同名比实参 spine（异名失败）——不带
        // 实参的单元 Prim 会把 `x ++ y ≡ x ++ z` 判成相等 ——
        if head_kind(spine, t) == HK_PRIM && head_kind(spine, u) == HK_PRIM {
            if xcell_head_name(spine, t) != xcell_head_name(spine, u) {
                return false;
            }
            match (v_tag(t), v_tag(u)) {
                (7, 7) => continue, // 双裸单元：unify_sp([][]) 自反成立
                (2, 2) => {
                    if memo_on {
                        stack.push(UItem::Store((t.0, u.0)));
                    }
                    if !unify_sp_lockstep(spine, &mut stack, l, v_spine_of(t), v_spine_of(u)) {
                        return false;
                    }
                    continue;
                }
                _ => return false, // 裸×带实参：长度失配
            }
        }
        // —— Sum/Sum（参考臂 17）：同名即逐参数（含索引）合一；zip 语义
        // （参数数不等取 min——参考版同款）；异名落到 Match 臂 / 失配 ——
        if v_tag(t) == 7 && v_tag(u) == 7 {
            let (xt, xu) = (v_xcell_of(t), v_xcell_of(u));
            if let (
                XCell::Sum { name: n1, params: p1, .. },
                XCell::Sum { name: n2, params: p2, .. },
            ) = (xt, xu)
            {
                if n1 == n2 {
                    for (a, b) in p1.iter().zip(p2.iter()).rev() {
                        stack.push(UItem::Pair(l, a.val, b.val));
                    }
                    continue;
                }
                return false; // 异名 Sum：参考版无后续可命中臂 → Err
            }
            // —— SumCase/SumCase（参考臂 18）：同构造子才比；**只比
            // datas 的值**（typ 是 datas 的函数，比 typ 值会在索引槽互相
            // 引用上深递归——索引等式在外层 Sum-Sum 的参数 zip 里建立），
            // 但**比 typ 的 Sum 头名字**：跨 enum 重名构造子（E1.c / E2.c）
            // 是两个不同值，同 case_name 不足以判定身份（参考版 2026-09-18
            // 同步）——
            if let (
                XCell::SumCase { case_name: c1, datas: d1, typ: t1 },
                XCell::SumCase { case_name: c2, datas: d2, typ: t2 },
            ) = (xt, xu)
            {
                if c1 == c2 {
                    if let (
                        XCell::Sum { name: n1, .. },
                        XCell::Sum { name: n2, .. },
                    ) = (v_xcell_of(*t1), v_xcell_of(*t2))
                    {
                        if n1 != n2 {
                            return false; // 异 enum 头：跨实例构造子 → Err
                        }
                    }
                    for (a, b) in d1.iter().zip(d2.iter()).rev() {
                        stack.push(UItem::Pair(l, a.val, b.val));
                    }
                    continue;
                }
                return false; // 异 case：参考版无后续可命中臂 → Err
            }
            // —— Match/Match（参考臂 19）：先 struct_eq 快路径（不 force
            // 不展开的结构比较 + budget 封顶，超限按不等），再 scrutinee
            // 合一 + 逐分支（模式必须相同；各分支体在 fresh rigid 槽 env 下
            // 用**简化 decl 表** eval 再 unify，l+count 层）+ pending 逐对 ——
            if let (
                XCell::Match { scrutinee: s1, env: e1, cases: c1, pending: pd1 },
                XCell::Match { scrutinee: s2, env: e2, cases: c2, pending: pd2 },
            ) = (xt, xu)
            {
                // 快路径：scrutinee、捕获 env、模式与分支体、pending 全部
                // 结构相同 ⇒ 两个 match 值在所有实例化下行为一致，直接判
                // 等。逐分支重求值会把递归函数的分支体再展开一层卡住
                // match（fresh rigid 层级随深度递增，永不收敛）——同一
                // decl 值在合一两侧各展开一份时正是这种自比较，必须短路
                // （参考版 struct_eq 同款 + 同一 budget 口径）。
                if struct_val_eq(spine, defs, *s1, *s2)
                    && struct_env_eq(spine, defs, *e1, *e2)
                    && c1.len() == c2.len()
                    && c1
                        .iter()
                        .zip(c2.iter())
                        .all(|((p1, b1), (p2, b2))| p1 == p2 && struct_tm_eq(*b1, *b2))
                    && pending_len(*pd1) == pending_len(*pd2)
                    && pending_struct_eq(spine, defs, *pd1, *pd2)
                {
                    continue;
                }
                // 参考版比较序（unification.rs Match/Match 臂）逐点对齐：
                // scrutinee → 分支数检查 → 逐分支（模式检查 + 体合一）→
                // pending 长度 → 逐 pending（icit 检查 + 值合一）。栈 LIFO
                // 反序压栈；两侧都在解同一 meta 时先解方向会影响最终解与
                // fuel 消耗序，序必须一致。结构检查作为屏障任务**交错**在
                // 序中弹出而非前置——Err 路径上 scrutinee / 前序分支的
                // meta 副作用与参考版保持一致。
                let declb = simpl_decl(bump, decls);
                // pending 逐对压栈：沿链走（头 = 最新）即应用序的**逆序**，
                // LIFO 弹出恢复应用序——与切片版 `.rev()` 同栈序。长度不
                // 等时 zip 截断，由 MatchPendingLen 屏障拦截（参考版在分支
                // 循环后才查长度）。
                let (mut pc1, mut pc2) = (*pd1, *pd2);
                loop {
                    match (pc1, pc2) {
                        (Some(x), Some(y)) => {
                            stack.push(UItem::MatchPending {
                                l,
                                u1: x.arg.0,
                                i1: x.arg.1,
                                u2: y.arg.0,
                                i2: y.arg.1,
                            });
                            pc1 = x.next;
                            pc2 = y.next;
                        }
                        _ => break,
                    }
                }
                stack.push(UItem::MatchPendingLen(pending_len(*pd1), pending_len(*pd2)));
                for ((p1, b1), (p2, b2)) in c1.iter().zip(c2.iter()).rev() {
                    stack.push(UItem::MatchBranch {
                        p1: &p1,
                        p2: &p2,
                        b1: *b1,
                        e1: *e1,
                        b2: *b2,
                        e2: *e2,
                        declb: declb.clone(),
                        l,
                        count: p1.bind_count(),
                    });
                }
                stack.push(UItem::MatchPrecheck { c1, c2 });
                stack.push(UItem::Pair(l, *s1, *s2));
                continue;
            }
        }
        // —— 卡住的 match vs 其它（参考臂 20）：能归约的已在入口 force 消掉
        // （force 会在 scrutinee 上重试选分支），这里只接受严格 η——每个
        // 分支都是通配且分支体就是 scrutinee 本身。无条件接受会把 `f x` 证
        // 成 `x` ——
        let (ms, mcases, mpending, other) = match (v_tag(t), v_tag(u)) {
            (7, _) => match v_xcell_of(t) {
                XCell::Match {
                    scrutinee,
                    cases,
                    pending,
                    ..
                } => (*scrutinee, *cases, *pending, u),
                _ => return false, // 其余 (7,·) 形态失配（参考 `_` 臂）
            },
            (_, 7) => match v_xcell_of(u) {
                XCell::Match {
                    scrutinee,
                    cases,
                    pending,
                    ..
                } => (*scrutinee, *cases, *pending, t),
                _ => return false,
            },
            _ => return false,
        };
        // 带 pending 实参的卡住 match 不是 η 形态（分支体经实参应用后
        // 不再等于 scrutinee）
        if mpending.is_some() {
            return false;
        }
        let sf = force(
            bump, spine, defs, metas, decls, mmap, fuel, ms,
        );
        if v_tag(sf) == 0 && v_tag(other) == 0 && v_lvl_of(sf) == v_lvl_of(other) {
            let is_eta = !mcases.is_empty()
                && mcases.iter().all(|(pat, body)| {
                    matches!(pat, PatternDetail::Any(_) | PatternDetail::Bind(_))
                        && matches!(body, Tm::Var(0))
                });
            if is_eta {
                continue;
            }
        }
        return false;
    }
    true
}
