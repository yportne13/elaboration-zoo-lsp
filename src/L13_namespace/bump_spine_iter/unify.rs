//! unify：工作表迭代合一（`UItem`/`unify_iter` + `NO_CONV_MEMO` 消融开关/
//! `ConvScratch` 草稿 + `declb_of` 存根表缓存）、intersect/flex-flex/同头
//! lockstep 助手与 Flex 侧求解拦截（`solve_flex_side_bump`）。原
//! bump_spine_iter.rs 的 "unify" 节（其标题之后的 `quote_nat_chain` 归
//! quote），逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;
use rustc_hash::FxHashSet;
use std::cell::RefCell;
use std::rc::Rc;

use super::parser::syntax::Icit;

use super::env::{env_ext, Env};
use super::eval::{eval_aux, eval_iter, W};
use super::force::{
    force, twin_stat_record, vapp1, ReclaimOnClear, CACHE_SHRINK_MIN_ENTRIES,
    META_JOURNAL, SPINE_SHRINK_MIN_ENTRIES, TWIN_DECLB_CACHE, TWIN_STAT_CONV,
};
use super::machine::{Cxt, Machine};
use super::prim::{DeclEntry, Decls, is_nat_sum_v, Mutable};
use super::quote::quote_iter;
use super::rename::{
    invert_bump, prune_meta_bump, solve_bump, solve_with_pren_bump, RenBuf, SolveRes,
};
use super::spine::{
    head_kind, meta_journal_discard, meta_journal_rollback, HK_DECL, HK_OBJ, HK_OTHER,
    MetaEntry, Spine,
};
use super::syntax::{
    Tm, V, XCell, v_clo_of, v_lvl, v_lvl_of, v_meta_of, v_pi_of, v_spine_of, v_tag, v_u_of,
    v_xcell, v_xcell_of,
};
use super::PatternDetail;


// unify（工作表迭代；L09 参考版臂序，无燃料、无 pm 臂、无 (Obj,Obj) 臂）
// --------------------------------------------------------------------------------

/// A/B 实验开关（unify 工作表的判等记忆化消融）：置 `L06_NO_CONV_MEMO=1`
/// 关闭（`=0` 不关闭）。
pub(super) static NO_CONV_MEMO: std::sync::LazyLock<std::sync::atomic::AtomicBool> =
    std::sync::LazyLock::new(|| {
        std::sync::atomic::AtomicBool::new(std::env::var("L06_NO_CONV_MEMO").is_ok_and(|v| v != "0"))
    });

/// unify 的跨调用草稿。
#[derive(Default)]
pub(super) struct ConvScratch {
    pub(super) memo: FxHashSet<(u64, u64)>,
    pub(super) scratch1: Vec<(V, Icit)>,
    pub(super) scratch2: Vec<(V, Icit)>,
}

/// unify 工作表条目：待比较子对、Π 余定义域的惰性比较屏障、判等记忆化
/// 屏障、或卡住 match 的惰性展开屏障（declb 存根表下重求值后压
/// `l+count` 层的体对）。
pub(super) enum UItem<'a> {
    /// 待比较子对（level 与 **fuel** 随对携带；弹出时先 force 双方再分派）。
    /// L13 的燃料语义：Decl 失配重 eval / Match 归约臂 `fuel-1`、SumCase
    /// 内层硬编码 100、其余臂透传（参考版 `unify(.., fuel)` 同款）。
    Pair(u32, V, V, u32),
    /// Π 余定义域的惰性比较（排在 dom 对之下——dom 不等即失败，cod 的
    /// eval 整个省掉）。
    EvalCod2(&'a Tm<'a>, Env<'a>, &'a Tm<'a>, Env<'a>, u32, u32),
    /// 判等记忆化屏障（LIFO；健壮性论证同 L03——solve 写一次、成功单调）。
    Store((u64, u64)),
    /// 卡住 match 的一个分支对：两侧体在"各自捕获 env + fresh rigid 槽"
    /// 下用 **declb 存根表**重求值，再压 `l + count` 层的体对。
    MatchBranch {
        b1: &'a Tm<'a>,
        e1: Env<'a>,
        b2: &'a Tm<'a>,
        e2: Env<'a>,
        declb: Rc<Decls<'a>>,
        l: u32,
        count: u32,
        fuel: u32,
    },
    /// Match/Match 的结构展开屏障（scrutinee 对比完后到达）：cases 长度
    /// 检查、分支对展开（参考版 scrutinee unify 之后的余下步骤，副作用
    /// 时序与参考版一致）。
    MatchStruct {
        e1: Env<'a>,
        e2: Env<'a>,
        c1: &'a [(PatternDetail, &'a Tm<'a>)],
        c2: &'a [(PatternDetail, &'a Tm<'a>)],
        declb: Rc<Decls<'a>>,
        l: u32,
        fuel: u32,
    },
    /// 分支 pattern 相等检查（参考版逐分支在分支体之前）。
    MatchPattern(&'a PatternDetail, &'a PatternDetail),
}

/// 从 decl 表构建 declb 存根表（**Sum 类型值保留**——否则 SumCase 的 typ
/// 变 Decl 卡 pretty，参考版 `simpl_decl` 逐字对应；prim 槽随行）。
///
/// 单条目缓存（参考版 `DECLB_CACHE` 同款移植，表见 [`TWIN_DECLB_CACHE`]）：
/// Match/Match unify、quote、rename 对同一 decl 表的重复重建整表免掉。
/// 轮界由 `force_memo_clear()` 清空（bump 句柄不跨轮）。
pub(super) fn declb_of<'a>(bump: &'a Bump, decl: &Decls<'a>) -> Rc<Decls<'a>> {
    let key = (decl as *const Decls<'a> as usize, decl.len());
    if let Some(hit) = TWIN_DECLB_CACHE.with(|c| {
        c.borrow().as_ref().and_then(|(a, l, d)| {
            (*a == key.0 && *l == key.1).then(|| d.clone())
        })
    }) {
        return hit;
    }
    let built: Rc<Decls<'a>> = Rc::new(
        decl.iter()
            .map(|(k, e)| {
                let name = bump.alloc_str(k.as_str());
                (
                    k.clone(),
                    DeclEntry {
                        span: e.span,
                        typ_pretty: e.typ_pretty.clone(),
                        typ_pretty_final: e.typ_pretty_final,
                        tm: bump.alloc(Tm::Decl(name)),
                        ty: e.ty,
                        val: if v_tag(e.val) == 7
                            && matches!(v_xcell_of(e.val), XCell::Sum { .. })
                        {
                            e.val
                        } else {
                            v_xcell(bump.alloc(XCell::Decl { name }))
                        },
                        vty: e.vty,
                        prim: e.prim,
                    },
                )
            })
            .collect(),
    );
    TWIN_DECLB_CACHE.with(|c| {
        // SAFETY：'static 仅是存放口径——条目全指向当轮 bump，跨轮前
        // `force_memo_clear()` 已把本表清空（与 unify_stack 的借出重写同
        // 纪律）；`Decls<'a>` 与 `Decls<'static>` 布局无关生命周期参数。
        *c.borrow_mut() = Some((
            key.0,
            key.1,
            unsafe { std::mem::transmute::<Rc<Decls<'a>>, Rc<Decls<'static>>>(built.clone()) },
        ));
    });
    built
}

/// `v_app` 可否安全应用到该值（参考版 `is_appliable`）：λ / Flex / Rigid /
/// Decl / Obj / Call / 卡住 Match（应用 splice）；Sum / SumCase / Nat / 字面
/// 量 / Π / U 不可——η 展开对它们会 panic，须落 `_` 失配。
#[inline]
fn is_appliable(_spine: &Spine, v: V) -> bool {
    match v_tag(v) {
        0 | 1 | 2 | 5 => true,
        7 => matches!(
            v_xcell_of(v),
            XCell::Obj { .. } | XCell::Decl { .. } | XCell::Call { .. } | XCell::Match { .. }
        ),
        _ => false,
    }
}

/// 值里是否（保守地）不含未解 meta（参考版 `val_has_no_flex`：Lam/Pi/
/// Match/Call 一律报"含 flex"——体可能嵌 `Tm::Meta`）。**不 force**（与参考
/// 版同款：解开的 meta 在值里仍是 Flex 形态直到被 force 展开）。
fn val_has_no_flex(spine: &Spine, v: V) -> bool {
    match v_tag(v) {
        5 | 1 | 4 => false,
        0 | 3 | 6 => true,
        2 => {
            let h = v_spine_of(v);
            // 逐槽读 spine（collect 免分配版）
            let mut cur = h;
            loop {
                let e = &spine.stack[cur];
                if !val_has_no_flex(spine, e.a) {
                    return false;
                }
                if v_tag(e.f) == 2 {
                    cur = v_spine_of(e.f);
                } else {
                    return val_has_no_flex(spine, e.f);
                }
            }
        }
        7 => match v_xcell_of(v) {
            XCell::Lit(_) | XCell::Nat(_) => true,
            XCell::Obj { val, .. } => val_has_no_flex(spine, *val),
            XCell::Sum { params, .. } => params
                .iter()
                .all(|p| val_has_no_flex(spine, p.val) && val_has_no_flex(spine, p.ty)),
            XCell::SumCase { typ, datas, .. } => {
                val_has_no_flex(spine, *typ)
                    && datas.iter().all(|d| val_has_no_flex(spine, d.val))
            }
            XCell::Decl { .. } => true,
            XCell::Call { .. } | XCell::Match { .. } => false,
        },
        _ => true,
    }
}

/// 值是否为 prim 挂载的 decl 应用（裸 Decl 单元或 Decl 头链；参考版
/// `is_prim_application`）：force 后仍是这种形态 → 重 eval 只是同一 prim
/// 对语义相同实参的重复执行，不可能取得进展——视为不透明叶直接失败。
fn is_prim_application<'a>(decl: &Decls<'a>, spine: &Spine, v: V) -> bool {
    let name: &str = match v_tag(v) {
        7 => match v_xcell_of(v) {
            XCell::Decl { name } => *name,
            _ => return false,
        },
        2 => {
            let h = v_spine_of(v);
            // 头也须是 Decl 单元（Rigid / Flex / Obj 头链 → false，O(1)
            // 读顶端槽种类，免整趟走底）
            if spine.stack[h].hk != HK_DECL {
                return false;
            }
            let hd = spine.spine_head(h);
            match v_xcell_of(hd) {
                XCell::Decl { name } => *name,
                _ => return false,
            }
        }
        _ => return false,
    };
    decl.get(name).is_some_and(|e| e.prim.is_some())
}

/// 链（或裸单元）是否卡住投影 Obj 头——unify 的位相等捷径对它关闭
/// （参考版无 `(Obj, Obj)` 臂，同单元也须走 `_` → Err）。
#[inline]
fn is_objheaded(spine: &Spine, v: V) -> bool {
    head_kind(spine, v) == HK_OBJ
}

/// `?m args ≡ ?m args'`（同头 flex）：上游 `intersect`。逐槽（内→外）
/// 都取到裸变量则产出掩码（槽位相等 → 其 icit、不等 → None）；有 None 即
/// 剪枝（`pruneMeta`），全相等即成立。长度不等直接失败。任一对含非变量
/// → 回落 `unify_sp` 逐实参比较。
#[allow(clippy::too_many_arguments)]
fn intersect_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decl: &Decls<'a>,
    mutable: &RefCell<Mutable>,
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
        let f1 = force(bump, spine, defs, metas, decl, mutable, args1[k].0);
        let f2 = force(bump, spine, defs, metas, decl, mutable, args2[k].0);
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
            return prune_meta_bump(bump, spine, work, vals, icits, defs, metas, decl, mutable, &pr, m)
                .is_some();
        }
        return true; // 两 spine 逐槽相等
    }
    // unify_sp 回落（参考版 `intersect` 的 None 臂：fuel 硬编码 100）：前缀
    // 对压栈（内先压 → 弹出外先，对齐 unify_sp 的递归序）。tag 7 不跳过：
    // 参考版对字面量实参照走 unify（恒败）——位相等的同单元也须分派。
    for k in 0..common {
        let (a1, _) = args1[k];
        let (a2, _) = args2[k];
        if a1.0 != a2.0 || v_tag(a1) == 7 {
            stack.push(UItem::Pair(l, a1, a2, 100));
        }
    }
    true
}

/// 异头 flex-flex（上游 `flexFlex`）：**短 spine 一侧优先**反演求解；反演
/// 失败则用另一侧求解（rhs 是整条 flex 值）——solve 含 L13 的 non-invertible
/// 常数解 fallback；该分支解后跑 trait 合成（参考版 `go` 的 Err 臂逐字）。
#[allow(clippy::too_many_arguments)]
fn flex_flex_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decl: &Decls<'a>,
    mutable: &RefCell<Mutable>,
    ren: &mut RenBuf,
    gamma: u32,
    m1: u32,
    args1: &[(V, Icit)],
    v1: V,
    m2: u32,
    args2: &[(V, Icit)],
    v2: V,
    cxt: &Cxt<'a>,
    mach_ptr: *mut Machine,
) -> bool {
    // 方向选择与参考版一致：`sp.len() < sp_prime.len()` → (m', sp') 先；
    // 相等/更长 → (m, sp) 先。调用点约定（L08 同款）：v1 = u（m1 侧的
    // rhs），v2 = t（m2 侧的 rhs）。
    let (fa, aa, va, fb, ab, vb) = if args1.len() < args2.len() {
        (m2, args2, v2, m1, args1, v1)
    } else {
        (m1, args1, v1, m2, args2, v2)
    };
    match invert_bump(bump, spine, defs, metas, decl, mutable, ren, aa) {
        Some(mask) => matches!(
            solve_with_pren_bump(
                bump, spine, work, vals, icits, defs, metas, decl, mutable, ren, fa,
                aa.len() as u32, gamma, mask, va,
            ),
            SolveRes::Ok
        ),
        None => {
            if !matches!(
                solve_bump(
                    bump, spine, work, vals, icits, defs, metas, decl, mutable, ren, gamma, fb, ab,
                    vb,
                ),
                SolveRes::Ok
            ) {
                return false;
            }
            unsafe { (&mut *mach_ptr).solve_multi_trait_ref(bump, cxt, fb, false).is_ok() }
        }
    }
}

/// 同头链（unify_sp）的实参 lockstep 比较：长度失配即败；实参 icit 不比
/// （类型已定，上游同款）。位相等的实参对免比（tag 7 与 Obj 头链除外——
/// 字面量恒败、卡住投影走 `_` → Err）。fuel 随对透传。
fn unify_sp_lockstep<'a>(
    spine: &Spine,
    stack: &mut Vec<UItem<'a>>,
    l: u32,
    h1: usize,
    h2: usize,
    fuel: u32,
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
        // Obj 头的链（tag 2 头 = Obj 单元）同样不免——参考版无 (Obj, Obj)
        // 臂，交回完整分派后走 `_` → Err。
        let skip1 = a1.0 == a2.0 && v_tag(a1) != 7 && !is_objheaded(spine, a1);
        if skip1 {
            if f1.0 != f2.0 {
                stack.push(UItem::Pair(l, f1, f2, fuel));
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
                    stack.push(UItem::Pair(l, f1, f2, fuel));
                }
                i1 = v_spine_of(a1);
                i2 = v_spine_of(a2);
                continue;
            }
        }
        stack.push(UItem::Pair(l, a1, a2, fuel));
        if f1.0 != f2.0 {
            stack.push(UItem::Pair(l, f1, f2, fuel));
        }
        break;
    }
    true
}

/// 裸 Rigid（tag 0）或 Rigid 头的链的层级；非此形态返回 None。
#[inline]
fn rigid_lvl(spine: &Spine, v: V) -> Option<u32> {
    match v_tag(v) {
        0 => Some(v_lvl_of(v)),
        2 => {
            let h = v_spine_of(v);
            if spine.stack[h].hk != HK_OTHER {
                return None; // flex / Decl / Obj 头：必非 Rigid，免走底
            }
            let hd = spine.spine_head(h);
            if v_tag(hd) == 0 {
                Some(v_lvl_of(hd))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// unification：结构比较 + meta 求解（含 intersect / flex-flex / 剪枝），
/// 工作表迭代。臂序与参考版 L13 `Infer::unify` 逐项对应（顺序敏感）：
/// Call/Call 同名 spine 快路径（无 Flex 免快照 / 有 Flex 三重快照回滚）→
/// Call 三条退化臂 → U → Π（icit 相等）→ Rigid/Rigid 同级 → 中性链分派
/// （flex×flex / Decl 同名 / 同头 lockstep）→ Decl 头拦截（对侧 Flex 先走
/// solve_flex_side；prim 不透明叶；fuel 重 eval）→ λ/η（**is_appliable
/// 守卫**）→ flex 求解（**Stuck → 约束挂账**）→ LiteralType → Sum/Sum →
/// SumCase（index 相等，内层 fuel=100）→ Nat/Nat + Nat 链 → Match/Match
/// （declb 存根表下重求值）→ 单侧 Match（归约 / Rigid eta-expansion 检查）
/// → Obj/Obj → 失配。**位相等捷径对 tag 7 与 Obj 头链关闭**（参考版对字
/// 面量无自反臂）。燃料：Decl 重 eval / Match 归约 `fuel-1`、SumCase 内层
/// 100、intersect 回落 100、其余透传。
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
    decl: &Decls<'a>,
    mutable: &RefCell<Mutable>,
    ren: &mut RenBuf,
    conv: &mut ConvScratch,
    constraints: &mut Vec<(V, V)>,
    l0: u32,
    t0: V,
    u0: V,
    fuel0: u32,
    cxt: &Cxt<'a>,
    mach_ptr: *mut Machine,
    trait_err: &mut Option<String>,
) -> bool {
    let memo_on = !NO_CONV_MEMO.load(std::sync::atomic::Ordering::Relaxed);
    // 草稿复用（Machine 常驻）：清空保容量，热路径零分配；容量到过阈值的表
    // 在清空时归还缓冲（memo 见 `CACHE_SHRINK_MIN_ENTRIES`，工作表见
    // `SPINE_SHRINK_MIN_ENTRIES`），否则峰值容量随常驻 Machine 到进程结束。
    twin_stat_record(&TWIN_STAT_CONV, conv.memo.reclaim(CACHE_SHRINK_MIN_ENTRIES));
    let _ = conv.scratch1.reclaim(SPINE_SHRINK_MIN_ENTRIES);
    let _ = conv.scratch2.reclaim(SPINE_SHRINK_MIN_ENTRIES);
    let memo = &mut conv.memo;
    // UItem 工作栈由调用方常驻复用（入口已 clear）；失败早退会留下非空
    // 栈，靠下次入口 clear 兜住（Rc 随 clear 正确减计，引用无 Drop）。
    // **不设** stack.is_empty() 断言：Call/Call spine 快路径的嵌套调用
    // （3657/3686）按设计以"首个对作入口、其余预载子栈"进入，入口非空
    // 是合法形态（实测 09-hierarchy 走到该路径）。
    stack.push(UItem::Pair(l0, t0, u0, fuel0));
    while let Some(item) = stack.pop() {
        let (l, t, u, fuel) = match item {
            UItem::Store(key) => {
                memo.insert(key);
                continue;
            }
            UItem::EvalCod2(b1, e1, b2, e2, l, fuel) => {
                let vt = {
                    let env = env_ext(bump, e1, v_lvl(l));
                    eval_iter(bump, spine, work, vals, icits, defs, metas, decl, mutable, env, b1)
                };
                let vu = {
                    let env = env_ext(bump, e2, v_lvl(l));
                    eval_iter(bump, spine, work, vals, icits, defs, metas, decl, mutable, env, b2)
                };
                stack.push(UItem::Pair(l + 1, vt, vu, fuel));
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
                fuel,
            } => {
                // 分支体：两侧各自"捕获 env + fresh rigid 槽（count =
                // bind_count，lvl 从 l 起）"下用 declb 存根表重求值，再在
                // l+count 层比较（参考版 unify 的 Match/Match 全路径同款）
                let mut env1 = e1;
                let mut env2 = e2;
                for i in 0..count {
                    env1 = env_ext(bump, env1, v_lvl(l + i));
                    env2 = env_ext(bump, env2, v_lvl(l + i));
                }
                let v1 = eval_iter(
                    bump, spine, work, vals, icits, defs, metas, &declb, mutable, env1, b1,
                );
                let v2 = eval_iter(
                    bump, spine, work, vals, icits, defs, metas, &declb, mutable, env2, b2,
                );
                stack.push(UItem::Pair(l + count, v1, v2, fuel));
                continue;
            }
            UItem::MatchStruct {
                e1,
                e2,
                c1,
                c2,
                declb,
                l,
                fuel,
            } => {
                // scrutinee 已比完（参考版 unify 的 Match/Match 臂 scrutinee
                // 递归之后）：cases 长度检查 → 逐分支（pattern → 分支体）。
                if c1.len() != c2.len() {
                    return false;
                }
                for (i, ((p1, b1), (_, b2))) in c1.iter().zip(c2.iter()).enumerate().rev() {
                    stack.push(UItem::MatchBranch {
                        b1: *b1,
                        e1,
                        b2: *b2,
                        e2,
                        declb: declb.clone(),
                        l,
                        count: p1.bind_count(),
                        fuel,
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
            UItem::Pair(l, t, u, fuel) => (l, t, u, fuel),
        };
        // 位相等：同一值。tag 7 与 Obj 头链例外（参考版对字面量无自反性、
        // 卡住投影走 (Obj,Obj) 臂）
        if t.0 == u.0 && v_tag(t) != 7 && !is_objheaded(spine, t) {
            continue;
        }
        if memo_on && memo.contains(&(t.0, u.0)) {
            continue; // 本轮已判等过的子对（命中连 force 都省——成功单调）
        }
        let t = force(bump, spine, defs, metas, decl, mutable, t);
        let u = force(bump, spine, defs, metas, decl, mutable, u);
        if t.0 == u.0 && v_tag(t) != 7 && !is_objheaded(spine, t) {
            continue; // force 展开后同值（同一解的两处引用）
        }

        // —— Call/Call 同名 spine 快路径（参考版前置快路径）：同名且实参
        // spine 可合一 → 相等（内联体是 name+args 的纯函数）。无 Flex 免快
        // 照；有 Flex 三重快照（meta / trait_metas / 约束）失败回滚——中途
        // 可能已解出 meta。失败落入体比较。——
        if v_tag(t) == 7
            && v_tag(u) == 7
            && matches!(v_xcell_of(t), XCell::Call { .. })
            && matches!(v_xcell_of(u), XCell::Call { .. })
        {
            let (n1, a1) = match v_xcell_of(t) {
                XCell::Call { name, args, .. } => (name, args),
                _ => unreachable!(),
            };
            let (n2, a2) = match v_xcell_of(u) {
                XCell::Call { name, args, .. } => (name, args),
                _ => unreachable!(),
            };
            if n1 == n2 {
                let has_flex = a1.iter().any(|&(a, _)| !val_has_no_flex(spine, a))
                    || a2.iter().any(|&(a, _)| !val_has_no_flex(spine, a));
                // 子 unify（实参对按参考 unify_sp 尾先比较序：自然序压、
                // 逆序弹；首个对作入口，其余留子栈）。有 Flex 时三重快照
                //（meta / trait_metas / 约束），失败回滚——中途可能已解出
                // meta。conv 用全新草稿（子调用会清 memo）。
                let ok = if !has_flex {
                    // 无 Flex：子 unify 只比较基值，不可能改求解状态——免快照
                    let mut conv_fresh = ConvScratch::default();
                    let mut sub: Vec<UItem<'a>> = Vec::new();
                    let mut terr: Option<String> = None;
                    let mut first = true;
                    let mut entry = (l, t, u);
                    for ((x, _), (y, _)) in a1.iter().zip(a2.iter()) {
                        if x.0 != y.0 || v_tag(*x) == 7 {
                            if first {
                                entry = (l, *x, *y);
                                first = false;
                            } else {
                                sub.push(UItem::Pair(l, *x, *y, fuel));
                            }
                        }
                    }
                    if first {
                        true // 全部位相等 → spine 相等
                    } else {
                        unify_iter(
                            bump, spine, work, &mut sub, vals, icits, defs, metas, decl, mutable,
                            ren, &mut conv_fresh, &mut Vec::new(), entry.0, entry.1, entry.2,
                            fuel, cxt, mach_ptr, &mut terr,
                        )
                    }
                } else {

                    // 探测回滚（META_JOURNAL，trait_wrap 同款）：旧实现整表
                    // clone metas（万条级 × 每次 Call/Call 带 Flex 比较一遍
                    // = trait 密集证明的主因之一）；journal 记就地写、截断
                    // 收 append。trait_metas 子 unify 期只 push，truncate 即
                    // 可。constraints 本就经局部 `cons` 账本、成功才并入，
                    // 旧代码的整表快照从未被读取（死克隆），一并移除。
                    let pre_meta_len = metas.len();
                    let pre_tm_len = unsafe { (*mach_ptr).trait_metas.len() };
                    META_JOURNAL.with(|j| j.borrow_mut().push(Vec::new()));
                    let mut conv_fresh = ConvScratch::default();
                    let mut sub: Vec<UItem<'a>> = Vec::new();
                    let mut terr: Option<String> = None;
                    let mut cons: Vec<(V, V)> = Vec::new();
                    let mut first = true;
                    let mut entry = (l, t, u);
                    for ((x, _), (y, _)) in a1.iter().zip(a2.iter()) {
                        if x.0 != y.0 || v_tag(*x) == 7 {
                            if first {
                                entry = (l, *x, *y);
                                first = false;
                            } else {
                                sub.push(UItem::Pair(l, *x, *y, fuel));
                            }
                        }
                    }
                    let ok = if first {
                        true
                    } else {
                        unify_iter(
                            bump, spine, work, &mut sub, vals, icits, defs, metas, decl, mutable,
                            ren, &mut conv_fresh, &mut cons, entry.0, entry.1, entry.2, fuel,
                            cxt, mach_ptr, &mut terr,
                        )
                    };
                    if ok {
                        constraints.extend(cons);
                        // 成功：探测期解出的 meta 全部保留，只出帧
                        meta_journal_discard();
                    } else {
                        // 回滚（mutable 的 prim 副作用不回滚——参考版同款）
                        meta_journal_rollback(metas, pre_meta_len);
                        unsafe { (*mach_ptr).trait_metas.truncate(pre_tm_len); }
                    }
                    ok
                };
                if ok {
                    if memo_on {
                        memo.insert((t.0, u.0));
                    }
                    continue;
                }
                // 失败：落入下方体比较（退化臂）
            }
        }

        // —— Call 三条退化臂（参考臂 0.5）：同名快路径失败或异名 → 体比较
        //——
        if v_tag(t) == 7 && v_tag(u) == 7 {
            if let (XCell::Call { body: b1, .. }, XCell::Call { body: b2, .. }) =
                (v_xcell_of(t), v_xcell_of(u))
            {
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                stack.push(UItem::Pair(l, *b1, *b2, fuel));
                continue;
            }
        }
        if v_tag(t) == 7 {
            if let XCell::Call { body: b1, .. } = v_xcell_of(t) {
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                stack.push(UItem::Pair(l, *b1, u, fuel));
                continue;
            }
        }
        if v_tag(u) == 7 {
            if let XCell::Call { body: b2, .. } = v_xcell_of(u) {
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                stack.push(UItem::Pair(l, t, *b2, fuel));
                continue;
            }
        }

        // —— 宇宙（参考臂 1）：层级相等才成立（无累积）——
        if v_tag(t) == 3 && v_tag(u) == 3 {
            if v_u_of(t) == v_u_of(u) {
                continue;
            }
            return false;
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
                stack.push(UItem::EvalCod2(p.body, p.env, q.body, q.env, l, fuel));
                stack.push(UItem::Pair(l, p.dom, q.dom, fuel));
                continue;
            }
        }
        // —— Rigid/Rigid（参考臂 3）：同级比实参 spine（裸×裸自反成立），
        // 异级落到后续臂 ——
        if v_tag(t) == 0 && v_tag(u) == 0 {
            if v_lvl_of(t) == v_lvl_of(u) {
                continue; // 双裸单元：unify_sp([][]) 自反成立
            }
        }
        // —— 中性链 vs 中性链（参考臂 3/4/5 的链形态全在此分派）——
        if v_tag(t) == 2 && v_tag(u) == 2 {
            let h1 = v_spine_of(t);
            let h2 = v_spine_of(u);
            let hd1 = spine.spine_head(h1);
            let hd2 = spine.spine_head(h2);
            let f1 = v_tag(hd1) == 5;
            let f2 = v_tag(hd2) == 5;
            if f1 && f2 {
                // 双 flex：同头 intersect、异头 flex_flex（参考臂 4/5）
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
                        bump, spine, work, vals, icits, defs, metas, decl, mutable, stack, l, m1, &a1,
                        &a2,
                    )
                } else {
                    flex_flex_bump(
                        bump, spine, work, vals, icits, defs, metas, decl, mutable, ren, l, m1, &a1, u,
                        m2, &a2, t, cxt, mach_ptr,
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
            // —— Decl 头链的同名判定：同名 lockstep 比实参；异名**不直接
            // 失配**——落入下方 (Decl,_) 拦截的 fuel 重 eval（参考臂序）——
            if v_tag(hd1) == 7 && v_tag(hd2) == 7 {
                if let (
                    XCell::Decl { name: n1 },
                    XCell::Decl { name: n2 },
                ) = (v_xcell_of(hd1), v_xcell_of(hd2))
                {
                    if n1 == n2 {
                        if memo_on {
                            stack.push(UItem::Store((t.0, u.0)));
                        }
                        if !unify_sp_lockstep(spine, stack, l, h1, h2, fuel) {
                            return false;
                        }
                        continue;
                    }
                    // 异名：跳出链分派，走 Decl 拦截
                }
            } else {
                // 同头判定：位相等（同变量 / 同 meta）；Obj 头交 (Obj,Obj) 臂
                if hd1.0 == hd2.0 && !is_objheaded(spine, hd1) {
                    if memo_on {
                        stack.push(UItem::Store((t.0, u.0)));
                    }
                    if !unify_sp_lockstep(spine, stack, l, h1, h2, fuel) {
                        return false;
                    }
                    continue;
                }
                // 异头：一侧 flex 头 → 该侧 solve（参考臂 9/10 的链形态，
                // solve_flex_side 语义：Stuck 挂账约束）
                if f1 || f2 {
                    let (mv, h, rhs) = if f1 {
                        (v_meta_of(hd1), h1, u)
                    } else {
                        (v_meta_of(hd2), h2, t)
                    };
                    let mut args = std::mem::take(&mut conv.scratch1);
                    args.clear();
                    spine.collect_args(h, &mut args);
                    let ok = solve_flex_side_bump(
                        bump, spine, work, vals, icits, defs, metas, decl, mutable, ren,
                        constraints, l, mv, &args, t, u, rhs, cxt, mach_ptr, trait_err,
                    );
                    conv.scratch1 = args;
                    if ok {
                        if memo_on {
                            memo.insert((t.0, u.0));
                        }
                        continue;
                    }
                    return false;
                }
                // 双刚性异级 / Obj 头组合 → 失配（(Obj,Obj) 由末段臂处理，
                // 走不到这里——两侧都是链且头异：异头 Obj 不可能同为 Obj 臂
                // 的输入形态之外）
                return false;
            }
        }
        // —— 裸 Rigid vs 链（同级）：参考臂 3 的 unify_sp——裸侧空 spine
        // 与链长失配即败；异级落后续臂 ——
        if v_tag(t) == 0 && v_tag(u) == 2 {
            if rigid_lvl(spine, u) == Some(v_lvl_of(t)) {
                return false; // 空 spine vs 非空链：长度失配
            }
        }
        if v_tag(t) == 2 && v_tag(u) == 0 {
            if rigid_lvl(spine, t) == Some(v_lvl_of(u)) {
                return false;
            }
        }
        // —— 裸 Decl/Decl 同名（参考臂 3.5，**须在下方 prim 拦截之前**）——
        // 参考版 `unification.rs` 的 `(Val::Decl(x,sp), Val::Decl(x',sp')) if
        // x == x'` 排在 `(Decl,_)` prim 不透明叶之前，且 `Val::Decl` 基座是
        // decl 表里共享的 `Rc`，两侧天然同指针；孪生的 `XCell::Decl` 只存名字、
        // 每次 `stuck_decl` 各自分配，链基座因此是两颗**地址不同**的裸 Decl
        // 存根——位相等捷径不命中，若落到 prim 拦截就会被 `is_prim_application`
        // 判成"不透明叶"直接失配（adder_proof：`n + succ m` 与 `succ (n + m)`
        // 都归约成 `succ (nat_add n m)`，比较到 `nat_add` 链基座时误报
        // `can't unify`）。裸 × 裸（空 spine）：同名即成立、异名失配——与参考版
        // 同序同位。
        if v_tag(t) == 7 && v_tag(u) == 7 {
            if let (XCell::Decl { name: n1 }, XCell::Decl { name: n2 }) =
                (v_xcell_of(t), v_xcell_of(u))
            {
                if n1 == n2 {
                    if memo_on {
                        memo.insert((t.0, u.0));
                    }
                    continue;
                }
                return false;
            }
        }
        // —— (Decl, _) / (_, Decl) 拦截（参考臂 3.6，在 η/flex 臂之前）：
        // 对侧是 Flex → 直接 solve_flex_side（None 返回的 prim 永不展开，
        // 烧燃料无意义）；prim 应用 = 不透明叶；否则 fuel>0 时 quote→eval
        // 重 eval（重读 decl 表——fake_bind 存根被真值覆盖后 force 仍卡在
        // 旧值，重 eval 才能看到真值）——
        if is_decl_val(spine, t) || is_decl_val(spine, u) {
            let (dv, ov, flip) = if is_decl_val(spine, t) { (t, u, false) } else { (u, t, true) };
            // 对侧 Flex → solve_flex_side
            let other_flex = match v_tag(ov) {
                5 => Some(v_meta_of(ov)),
                2 => {
                    let hd = spine.spine_head(v_spine_of(ov));
                    if v_tag(hd) == 5 {
                        Some(v_meta_of(hd))
                    } else {
                        None
                    }
                }
                _ => None,
            };
            if let Some(m) = other_flex {
                let mut args: Vec<(V, Icit)> = match v_tag(ov) {
                    5 => Vec::new(),
                    _ => {
                        let mut a = Vec::new();
                        spine.collect_args(v_spine_of(ov), &mut a);
                        a
                    }
                };
                let ok = solve_flex_side_bump(
                    bump, spine, work, vals, icits, defs, metas, decl, mutable, ren,
                    constraints, l, m, &args, t, u, dv, cxt, mach_ptr, trait_err,
                );
                if ok {
                    if memo_on {
                        memo.insert((t.0, u.0));
                    }
                    continue;
                }
                return false;
            }
            if is_prim_application(decl, spine, dv) {
                return false; // 不透明叶
            }
            if fuel == 0 {
                return false;
            }
            let q = quote_iter(
                bump,
                spine,
                &mut Vec::new(),
                &mut Vec::new(),
                work,
                vals,
                icits,
                defs,
                metas,
                decl,
                mutable,
                l,
                dv,
                None,
            );
            let dv2 = eval_iter(bump, spine, work, vals, icits, defs, metas, decl, mutable, cxt.env, q);
            let _ = flip;
            if is_decl_val(spine, t) {
                stack.push(UItem::Pair(l, dv2, u, fuel - 1));
            } else {
                stack.push(UItem::Pair(l, t, dv2, fuel - 1));
            }
            continue;
        }
        // —— λ / η（参考臂 6/7/8；在 flex 求解之前：Flex vs λ 走 η）。
        // η 的应用侧须 **is_appliable**（参考版守卫——对 Sum/SumCase/Nat/
        // 字面量应用会 panic，须落 `_` 失配）——
        if v_tag(t) == 1 && v_tag(u) == 1 {
            let c1 = v_clo_of(t);
            let c2 = v_clo_of(u);
            let vt = {
                let env = env_ext(bump, c1.env, v_lvl(l));
                eval_iter(bump, spine, work, vals, icits, defs, metas, decl, mutable, env, c1.body)
            };
            let vu = {
                let env = env_ext(bump, c2.env, v_lvl(l));
                eval_iter(bump, spine, work, vals, icits, defs, metas, decl, mutable, env, c2.body)
            };
            if memo_on {
                stack.push(UItem::Store((t.0, u.0)));
            }
            stack.push(UItem::Pair(l + 1, vt, vu, fuel));
            continue;
        }
        if v_tag(u) == 1 && is_appliable(spine, t) {
            let c = v_clo_of(u);
            let vu = {
                let env = env_ext(bump, c.env, v_lvl(l));
                eval_iter(bump, spine, work, vals, icits, defs, metas, decl, mutable, env, c.body)
            };
            let vt = vapp1(
                bump, spine, work, vals, icits, defs, metas, decl, mutable, false, t, v_lvl(l), c.icit,
            );
            if memo_on {
                stack.push(UItem::Store((t.0, u.0)));
            }
            stack.push(UItem::Pair(l + 1, vt, vu, fuel));
            continue;
        }
        if v_tag(t) == 1 && is_appliable(spine, u) {
            let c = v_clo_of(t);
            let vt = {
                let env = env_ext(bump, c.env, v_lvl(l));
                eval_iter(bump, spine, work, vals, icits, defs, metas, decl, mutable, env, c.body)
            };
            let vu = vapp1(
                bump, spine, work, vals, icits, defs, metas, decl, mutable, false, u, v_lvl(l), c.icit,
            );
            if memo_on {
                stack.push(UItem::Store((t.0, u.0)));
            }
            stack.push(UItem::Pair(l + 1, vt, vu, fuel));
            continue;
        }
        // —— flex 求解（参考臂 4/5/9/10 的裸形态；solve_flex_side 语义：
        // Stuck → 约束挂账后继续）——
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
                            bump, spine, work, vals, icits, defs, metas, decl, mutable, stack, l, m1,
                            &a1, &a2,
                        )
                    } else {
                        flex_flex_bump(
                            bump, spine, work, vals, icits, defs, metas, decl, mutable, ren, l, m1, &a1,
                            u, m2, &a2, t, cxt, mach_ptr,
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
                    let ok = solve_flex_side_bump(
                        bump, spine, work, vals, icits, defs, metas, decl, mutable, ren,
                        constraints, l, m, &a1, t, u, u, cxt, mach_ptr, trait_err,
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
                    let ok = solve_flex_side_bump(
                        bump, spine, work, vals, icits, defs, metas, decl, mutable, ren,
                        constraints, l, m, &a2, t, u, t, cxt, mach_ptr, trait_err,
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
                    // 非 flex：落到字面量 / Sum / SumCase / Match 臂
                }
            }
        }
        // —— (LiteralType, LiteralType)（参考臂 11）——
        if v_tag(t) == 6 && v_tag(u) == 6 {
            continue;
        }
        // —— Sum/Sum（参考臂 13）：同名即逐参数（含索引）值合一；zip 语义
        // （参数数不等取 min——参考版同款）；异名失配 ——
        if v_tag(t) == 7 && v_tag(u) == 7 {
            let (xt, xu) = (v_xcell_of(t), v_xcell_of(u));
            // —— Decl/Decl 同名（参考臂 3.5 裸形态）：空 spine 即成立；异名
            // 已在上方拦截臂处理（走不到这里）——
            if let (XCell::Decl { name: n1 }, XCell::Decl { name: n2 }) = (xt, xu) {
                if n1 == n2 {
                    continue;
                }
                return false;
            }
            if let (
                XCell::Sum {
                    name: n1,
                    params: p1,
                    ..
                },
                XCell::Sum {
                    name: n2,
                    params: p2,
                    ..
                },
            ) = (xt, xu)
            {
                if n1 == n2 {
                    for (a, b) in p1.iter().zip(p2.iter()).rev() {
                        stack.push(UItem::Pair(l, a.val, b.val, fuel));
                    }
                    continue;
                }
                return false; // 异名 Sum：参考版无后续可命中臂 → Err
            }
            // —— SumCase/SumCase（参考臂 14）：index 相等才比；typ 与 datas
            // 都比（内层硬编码 fuel 100——参考版同款）——
            if let (
                XCell::SumCase {
                    typ: ty1,
                    index: c1,
                    datas: d1,
                    ..
                },
                XCell::SumCase {
                    typ: ty2,
                    index: c2,
                    datas: d2,
                    ..
                },
            ) = (xt, xu)
            {
                if c1 == c2 {
                    // pop 序 = typ, d0, d1, ...（参考版执行序）
                    for (a, b) in d1.iter().zip(d2.iter()).rev() {
                        stack.push(UItem::Pair(l, a.val, b.val, 100));
                    }
                    stack.push(UItem::Pair(l, *ty1, *ty2, 100));
                    continue;
                }
                return false; // 异构造子：参考版无后续可命中臂 → Err
            }
            // —— Nat/Nat + Nat/SumCase 链（参考臂 15/15.5）：定义上相等
            // 当且仅当 k == 链长（仅 Nat sum 类型；unify_nat_chain 递归）——
            if let (XCell::Nat(k), XCell::Nat(j)) = (xt, xu) {
                if k == j {
                    continue;
                }
                return false;
            }
            if let (XCell::Nat(k), XCell::SumCase { typ, index, datas, .. }) = (xt, xu) {
                let tf = force(bump, spine, defs, metas, decl, mutable, *typ);
                if is_nat_sum_v(tf) {
                    match (*index, datas.len()) {
                        (0, 0) => {
                            if *k == 0 {
                                continue;
                            }
                            return false;
                        }
                        (1, 1) => {
                            if *k > 0 {
                                let prev = v_xcell(bump.alloc(XCell::Nat(k - 1)));
                                stack.push(UItem::Pair(l, prev, datas[0].val, fuel));
                                continue;
                            }
                            return false;
                        }
                        _ => return false,
                    }
                }
                return false;
            }
            if let (XCell::SumCase { typ, index, datas, .. }, XCell::Nat(k)) = (xt, xu) {
                let tf = force(bump, spine, defs, metas, decl, mutable, *typ);
                if is_nat_sum_v(tf) {
                    match (*index, datas.len()) {
                        (0, 0) => {
                            if *k == 0 {
                                continue;
                            }
                            return false;
                        }
                        (1, 1) => {
                            if *k > 0 {
                                let prev = v_xcell(bump.alloc(XCell::Nat(k - 1)));
                                stack.push(UItem::Pair(l, datas[0].val, prev, fuel));
                                continue;
                            }
                            return false;
                        }
                        _ => return false,
                    }
                }
                return false;
            }
            // —— Match/Match（参考臂 16）：scrutinee 最先合一（真实副作用
            // 时序），cases 长度与 pattern 检查及其后分支体的中性重求值由
            // MatchStruct 屏障执行 ——
            if let (
                XCell::Match {
                    scrutinee: s1,
                    env: e1,
                    cases: c1,
                },
                XCell::Match {
                    scrutinee: s2,
                    env: e2,
                    cases: c2,
                },
            ) = (xt, xu)
            {
                stack.push(UItem::MatchStruct {
                    e1: *e1,
                    e2: *e2,
                    c1,
                    c2,
                    declb: declb_of(bump, decl),
                    l,
                    fuel,
                });
                stack.push(UItem::Pair(l, *s1, *s2, fuel));
                continue;
            }
        }
        // —— 单侧 Match（参考末段臂）：force scrutinee → 构造子头则 eval_aux
        // 归约（fuel-1）再比；否则 Rigid/Rigid 空 spine 的 eta-expansion
        // 检查（全分支是 Any/Bind 且体是 Var(0) 才相等——soundness 修复）——
        {
            let mcell = if v_tag(t) == 7 && matches!(v_xcell_of(t), XCell::Match { .. }) {
                Some((t, u))
            } else if v_tag(u) == 7 && matches!(v_xcell_of(u), XCell::Match { .. }) {
                Some((u, t))
            } else {
                None
            };
            if let Some((mv, other)) = mcell {
                let (s, env_m, cases) = match v_xcell_of(mv) {
                    XCell::Match { scrutinee, env, cases } => (*scrutinee, *env, cases),
                    _ => unreachable!(),
                };
                let s2 = force(bump, spine, defs, metas, decl, mutable, s);
                let is_ctor = v_tag(s2) == 7
                    && matches!(v_xcell_of(s2), XCell::SumCase { .. } | XCell::Nat(_));
                if is_ctor {
                    if let Some((tm_b, env_b)) =
                        eval_aux(bump, spine, defs, metas, decl, mutable, s2, env_m, cases)
                    {
                        let reduced =
                            eval_iter(bump, spine, work, vals, icits, defs, metas, decl, mutable, env_b, tm_b);
                        if fuel > 0 {
                            stack.push(UItem::Pair(l, reduced, other, fuel - 1));
                            continue;
                        }
                    }
                }
                // eta-expansion 检查：scrutinee 与对侧都是裸 Rigid 同级
                if v_tag(s2) == 0 && v_tag(other) == 0 && v_lvl_of(s2) == v_lvl_of(other) {
                    let is_eta = !cases.is_empty()
                        && cases.iter().all(|(pat, body)| {
                            let binds_scrutinee = matches!(
                                pat,
                                PatternDetail::Any(..) | PatternDetail::Bind(_)
                            );
                            binds_scrutinee && matches!(body, Tm::Var(0))
                        });
                    if is_eta {
                        continue;
                    }
                }
                return false;
            }
        }
        // —— (Obj, Obj) 合同臂（参考臂 17）：字段名同 ⇒ 比接收者 + spine
        // 实参 ——
        if is_objheaded(spine, t) && is_objheaded(spine, u) {
            let (hc1, hc2) = (
                if v_tag(t) == 7 { t } else { spine.spine_head(v_spine_of(t)) },
                if v_tag(u) == 7 { u } else { spine.spine_head(v_spine_of(u)) },
            );
            let (o1, n1, o2, n2) = match (v_xcell_of(hc1), v_xcell_of(hc2)) {
                (
                    XCell::Obj { val: a1, name: m1 },
                    XCell::Obj { val: a2, name: m2 },
                ) => (*a1, *m1, *a2, *m2),
                _ => return false,
            };
            if n1 != n2 {
                return false;
            }
            if memo_on {
                stack.push(UItem::Store((t.0, u.0)));
            }
            stack.push(UItem::Pair(l, o1, o2, fuel));
            match (v_tag(t), v_tag(u)) {
                (7, 7) => {}
                (2, 2) => {
                    if !unify_sp_lockstep(spine, stack, l, v_spine_of(t), v_spine_of(u), fuel) {
                        return false;
                    }
                }
                _ => return false,
            }
            continue;
        }
        return false;
    }
    true
}

/// 值是否 Decl 头（裸 Decl 单元或 Decl 头链）——unify 的 (Decl,_) 拦截判据。
#[inline]
fn is_decl_val(spine: &Spine, v: V) -> bool {
    head_kind(spine, v) == HK_DECL
}

/// `solve_flex_side` 的快版（参考版 unification.rs:879）：solve 成功 /
/// **Stuck → 约束挂账后视为成功** / 其余失败；随后跑 trait 合成（失败 →
/// trait_err 上抛）。返回 false = unify 失败。
#[allow(clippy::too_many_arguments)]
fn solve_flex_side_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decl: &Decls<'a>,
    mutable: &RefCell<Mutable>,
    ren: &mut RenBuf,
    constraints: &mut Vec<(V, V)>,
    l: u32,
    m: u32,
    args: &[(V, Icit)],
    t: V,
    u: V,
    rhs: V,
    cxt: &Cxt<'a>,
    mach_ptr: *mut Machine,
    trait_err: &mut Option<String>,
) -> bool {
    match solve_bump(
        bump, spine, work, vals, icits, defs, metas, decl, mutable, ren, l, m, args, rhs,
    ) {
        SolveRes::Fail => return false,
        SolveRes::Stuck => constraints.push((t, u)),
        SolveRes::Ok => {}
    }
    let tr = unsafe { (&mut *mach_ptr).solve_multi_trait_ref(bump, cxt, m, false) };
    if let Err(e) = tr {
        *trait_err = Some(e);
        return false;
    }
    true
}
