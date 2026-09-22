//! unify：工作表迭代合一（`UItem`/`unify_iter`）+ intersect/flex-flex
//! （`intersect_bump`/`flex_flex_bump`）+ 同头 lockstep + pm 特化臂。
//! 原 bump_spine_iter.rs 的 "unify" 节，逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;
use rustc_hash::FxHashMap;
use std::rc::Rc;

use super::parser::syntax::Icit;
use super::PatternDetail;

use super::env::{Env, env_ext};
use super::eval::{eval_iter, W};
use super::force::{force, val_mentions_lvl, vapp1, vapp_ok};
use super::machine::{CACHE_SHRINK_MIN_ENTRIES, ConvScratch, ReclaimOnClear, SPINE_SHRINK_MIN_ENTRIES};
use super::prim::{DeclEntryF, Fuel, MutableMap};
use super::rename::{invert_bump, prune_meta_bump, RenBuf, solve_bump, solve_with_pren_bump};
use super::spine::{head_kind, HK_DECL, HK_OBJ, HK_PRIM, is_flex, is_objheaded, MetaEntry, Spine, xcell_head_name};
use super::struct_eq::{struct_env_eq, struct_tm_eq, struct_val_eq};
use super::subst::{simpl_decl, SpecSolve, SubstV, wrap_sub};
use super::syntax::{Tm, V, v_clo_of, v_lit_ty, v_lvl, v_lvl_of, v_meta_of, v_pi_of, v_spine_of, v_tag, v_xcell_of, XCell};

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
    /// 下用简化 decl 表重求值，再压 `l + count` 层的体对。
    MatchBranch {
        b1: &'a Tm<'a>,
        e1: Env<'a>,
        b2: &'a Tm<'a>,
        e2: Env<'a>,
        declb: Rc<FxHashMap<String, DeclEntryF>>,
        l: u32,
        count: u32,
    },
    /// Match/Match 的结构展开屏障（弹出时执行）：scrutinee 对比完后到达
    /// ——cases 长度检查、简化 decl 表重建、分支对与 pending 对的展开
    /// （参考版 scrutinee unify 之后的余下步骤；此前实现把检查前置，
    /// 失败路径的 meta 求解副作用时序与参考版分叉，错误消息正文可能
    /// 不同——Err parity 升级为正文比对后按参考版时序归位）。
    MatchStruct {
        e1: Env<'a>,
        e2: Env<'a>,
        c1: &'a [(PatternDetail, &'a Tm<'a>)],
        c2: &'a [(PatternDetail, &'a Tm<'a>)],
        pd1: &'a [(V, Icit)],
        pd2: &'a [(V, Icit)],
        l: u32,
    },
    /// 分支 pattern 相等检查（参考版逐分支在分支体之前）。
    MatchPattern(&'a PatternDetail, &'a PatternDetail),
    /// pending 长度检查（参考版在分支体全部比完之后）。
    MatchPendingLen(usize, usize),
    /// pending 对的 icit 检查（参考版逐对在分支体之后）。
    MatchIcit(Icit, Icit),
}

/// `?m args ≡ ?m args'`（同头 flex）：上游 `intersect`。逐槽（内→外）
/// 都取到裸变量则产出掩码（槽位相等 → 其 icit、不等 → None）；有 None 即
/// 剪枝（`pruneMeta`），全相等即成立。长度不等直接失败（参考版
/// intersect_go 的 `_ => None` → unify_sp 长度失配分支：失配即败、零比较）。
/// 任一对含非变量 → 回落 `unify_sp` 逐实参比较。
#[allow(clippy::too_many_arguments)]
fn intersect_bump<'a>(
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
    for k in 0..common {
        let (a1, _) = args1[k];
        let (a2, _) = args2[k];
        if a1.0 != a2.0 || v_tag(a1) == 7 {
            stack.push(UItem::Pair(l, a1, a2));
        }
    }
    true
}

/// 异头 flex-flex（上游 `flexFlex`）：**短 spine 一侧优先**反演求解；反演
/// 失败则用另一侧求解（rhs 是整条 flex 值）。第一次尝试可能已 solve 部分
/// meta 才失败，反向尝试前回滚（参考版 meta 快照同款）。
#[allow(clippy::too_many_arguments)]
fn flex_flex_bump<'a>(
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
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel,
                        ren, gamma, fb, ab.len() as u32, mask, vb,
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
/// 字面量恒败、Decl/Prim 走同名分派、Obj 走 `(Obj, Obj)` 专臂）。
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
        // Obj 头的链（tag 2 + hk=Obj）同样不免——接收者锁在头单元里，
        // lockstep 看不见，须交回 (Obj, Obj) 专臂。
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
/// **位相等捷径与实参跳过对 tag 7 与 Obj 头链关闭**：`(Lit, Lit)` 参考版
/// 无自反臂——同字面量也 Err；`(Obj, Obj)` 走专门合同臂——同单元也须比
/// 接收者 + 实参，不做字面自反放行。
#[allow(clippy::too_many_arguments)]
pub(super) fn unify_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    stack: &mut Vec<UItem<'a>>,
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
    // 草稿复用（Machine 常驻）：清空保容量，热路径零分配；容量到过阈值的表
    // 在清空时归还缓冲（memo 见 `CACHE_SHRINK_MIN_ENTRIES`，工作表见
    // `SPINE_SHRINK_MIN_ENTRIES`），否则峰值容量随常驻 Machine 到进程结束。
    let _ = conv.memo.reclaim(CACHE_SHRINK_MIN_ENTRIES);
    let _ = conv.scratch1.reclaim(SPINE_SHRINK_MIN_ENTRIES);
    let _ = conv.scratch2.reclaim(SPINE_SHRINK_MIN_ENTRIES);
    let memo = &mut conv.memo;
    // UItem 工作栈由调用方常驻复用（入口已 clear）；失败早退会留下非空
    // 栈，靠下次入口 clear 兜住（Rc 随 clear 正确减计，引用无 Drop）
    debug_assert!(stack.is_empty());
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
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel,
                        env, b1,
                    )
                };
                let vu = {
                    let env = env_ext(bump, e2, v_lvl(l));
                    eval_iter(
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel,
                        env, b2,
                    )
                };
                stack.push(UItem::Pair(l + 1, vt, vu));
                continue;
            }
            UItem::MatchBranch {
                b1,
                e1,
                b2,
                e2,
                declb,
                l,
                count,
            } => {
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
                    bump, spine, work, vals, icits, defs, metas, &declb, mmap, fuel,
                    env1, b1,
                );
                let v2 = eval_iter(
                    bump, spine, work, vals, icits, defs, metas, &declb, mmap, fuel,
                    env2, b2,
                );
                stack.push(UItem::Pair(l + count, v1, v2));
                continue;
            }
            UItem::MatchStruct {
                e1,
                e2,
                c1,
                c2,
                pd1,
                pd2,
                l,
            } => {
                // scrutinee 已比完（参考版 :766 之后）：cases 长度检查 →
                // 简化 decl 表 → 展开分支与 pending（检查本身不烧 fuel，
                // 与参考版一致——fuel 只随子 unify 调用/Pair 消耗）
                if c1.len() != c2.len() {
                    return false;
                }
                let declb = Rc::new(simpl_decl(bump, decls));
                // 展开序 = 参考版执行序：逐分支 pattern 检查 → 分支体 →
                // pending 长度检查 → 逐 pending icit 检查 → 对。LIFO 按执行
                // 序的逆序压：pending（对 → icit，反序）→ pending 长度 →
                // 分支（体 → pattern，反序）
                for ((u1, _), (u2, _)) in pd1.iter().zip(pd2.iter()).rev() {
                    stack.push(UItem::Pair(l, *u1, *u2));
                }
                // icit 检查按公共前缀推入：pending 长度差分时上面的 zip 已
                // 截断对推入，此处若仍用 pd1.len() 索引 pd2 会越界 panic
                // （参考版是干净的 pendingLen Err）——差分判定保留给弹出侧
                // 的 MatchPendingLen（提前到这里会改变失败前的 meta 副作用
                // 时序，正是屏障重构要消除的分叉源）
                for i in (0..pd1.len().min(pd2.len())).rev() {
                    stack.push(UItem::MatchIcit(pd1[i].1, pd2[i].1));
                }
                stack.push(UItem::MatchPendingLen(pd1.len(), pd2.len()));
                for (i, ((p1, b1), (_, b2))) in
                    c1.iter().zip(c2.iter()).enumerate().rev()
                {
                    stack.push(UItem::MatchBranch {
                        b1: *b1,
                        e1,
                        b2: *b2,
                        e2,
                        declb: declb.clone(),
                        l,
                        count: p1.bind_count(),
                    });
                    stack.push(UItem::MatchPattern(p1, &c2[i].0));
                }
                continue;
            }
            UItem::MatchPattern(p1, p2) => {
                if p1 != p2 {
                    return false;
                }
                continue;
            }
            UItem::MatchPendingLen(n1, n2) => {
                if n1 != n2 {
                    return false;
                }
                continue;
            }
            UItem::MatchIcit(i1, i2) => {
                if i1 != i2 {
                    return false;
                }
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
        // 字面量无自反性、Obj 走专臂，Decl/Prim 需同名分派）
        if t.0 == u.0 && v_tag(t) != 7 && !is_objheaded(spine, t) {
            continue;
        }
        if memo_on && memo.contains(&(t.0, u.0)) {
            continue; // 本轮已判等过的子对（命中连 force 都省——成功单调）
        }
        let t = force(
            bump, spine, defs, metas, decls, mmap, fuel, t,
        );
        let u = force(
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
        let (t, u) = if let Some(s) = spec.as_deref() {
            if !s.acc.is_empty() {
                let acc = s.acc.clone();
                let t2 = force(
                    bump, spine, defs, metas, decls, mmap, fuel, wrap_sub(bump, &acc, t),
                );
                let u2 = force(
                    bump, spine, defs, metas, decls, mmap, fuel, wrap_sub(bump, &acc, u),
                );
                (t2, u2)
            } else {
                (t, u)
            }
        } else {
            (t, u)
        };

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
        // 失败形态）。语义与 L06 的 (0,0) 末臂同构；位置在 pm 臂之后——
        // 刚性对可被 pm 臂求解，pm 臂必须保持在前（L07 7811a99 同款回补）——
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
                        if !unify_sp_lockstep(spine, stack, l, v_spine_of(t), v_spine_of(u)) {
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
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel,
                    env, c1.body,
                )
            };
            let vu = {
                let env = env_ext(bump, c2.env, v_lvl(l));
                eval_iter(
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel,
                    env, c2.body,
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
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel,
                    env, c.body,
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
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel,
                    env, c.body,
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
        // —— (Obj, Obj) 合同（对位参考版新臂，评审修复）：字段名相同 ⇒
        // 比接收者，再比 spine 实参（裸×裸接收者对入栈即完；链×链加
        // lockstep；裸×链长度失配即败——与参考版 (Obj, Obj) 臂语义一致）。
        // 卡住投影的两种形态（裸 XCell 单元 / 带实参 spine 链）统一在此
        // 处理，接收者住在头单元里、lockstep 看不见，单独入栈。tag 预门控
        // （head_kind 只对 tag 7/2 可能给 HK_OBJ）把每 Pair 的固定税从
        // 两次 head_kind 降为位比较。——
        if (v_tag(t) == 7 || v_tag(t) == 2)
            && (v_tag(u) == 7 || v_tag(u) == 2)
            && head_kind(spine, t) == HK_OBJ
            && head_kind(spine, u) == HK_OBJ
        {
            let (hc1, hc2) = (
                if v_tag(t) == 7 { t } else { spine.spine_head(v_spine_of(t)) },
                if v_tag(u) == 7 { u } else { spine.spine_head(v_spine_of(u)) },
            );
            let (o1, n1, o2, n2) = match (v_xcell_of(hc1), v_xcell_of(hc2)) {
                (
                    XCell::Obj { val: a1, name: m1 },
                    XCell::Obj { val: a2, name: m2 },
                ) => (*a1, *m1, *a2, *m2),
                _ => return false, // 防御（head_kind 已保证 Obj 头）
            };
            if n1 != n2 {
                return false;
            }
            if memo_on {
                stack.push(UItem::Store((t.0, u.0)));
            }
            stack.push(UItem::Pair(l, o1, o2));
            match (v_tag(t), v_tag(u)) {
                (7, 7) => {}
                (2, 2) => {
                    if !unify_sp_lockstep(spine, stack, l, v_spine_of(t), v_spine_of(u)) {
                        return false;
                    }
                }
                _ => return false, // 裸×带实参：spine 长度失配
            }
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
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel,
                        stack, l, m1, &a1, &a2,
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
            // 同头判定：位相等（同变量 / 同 meta / 同单元）或同名 Decl/Prim
            // 头（参考版比较 Span——名字全部来自 empty_span 构造，等价于名
            // 内容相等）。Obj 头走上文 (Obj, Obj) 专臂，不进同头
            // （排除为防御性保留）。
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
                if !unify_sp_lockstep(spine, stack, l, h1, h2) {
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
                            stack, l, m1, &a1, &a2,
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
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel,
                        ren, l, m, &a1, u,
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
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel,
                        ren, l, m, &a2, t,
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
                    if !unify_sp_lockstep(spine, stack, l, v_spine_of(t), v_spine_of(u)) {
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
                    && pd1.len() == pd2.len()
                    && pd1
                        .iter()
                        .zip(pd2.iter())
                        .all(|((a, i), (b, j))| i == j && struct_val_eq(spine, defs, *a, *b))
                {
                    continue;
                }
                // 比较顺序与参考版逐项对齐（含失败路径的副作用时序）：
                // scrutinee 最先比；cases/pending 的长度与 pattern 检查在
                // scrutinee 之后由 MatchStruct 屏障执行（简化 decl 表的
                // 重建同样推迟到检查通过）。——
                stack.push(UItem::MatchStruct {
                    e1: *e1,
                    e2: *e2,
                    c1,
                    c2,
                    pd1,
                    pd2,
                    l,
                });
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
        if !mpending.is_empty() {
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
