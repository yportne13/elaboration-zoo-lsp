//! unify：工作表 unify（`UItem`/`unify_iter`；force 前置 + 判等记忆化 +
//! intersect/flex-flex + L06 字面量/Decl 臂）。原 bump_spine_iter.rs 的
//! "unify…" 一节，逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;
use rustc_hash::FxHashMap;
use smol_str::SmolStr;

use super::parser::syntax::Icit;

use super::env::{env_ext, Env};
use super::eval::{eval_iter, force, W};
use super::machine::{CACHE_SHRINK_MIN_ENTRIES, ConvScratch, ReclaimOnClear, SPINE_SHRINK_MIN_ENTRIES};
use super::prim::{decl_apply, v_applicable, DeclEntryF, MutableMap};
use super::rename::{invert_bump, prune_meta_bump, solve_bump, solve_with_pren_bump, RenBuf, RenameScratch};
use super::spine::{is_declheaded, MetaEntry, Spine};
use super::syntax::{Tm, V, XCell, v_clo_of, v_lit_ty, v_lvl, v_lvl_of, v_meta_of, v_pi_of, v_spine_of, v_tag, v_xcell_of};

// unify（工作表迭代 + force 前置 + 模式求解 + intersect/flex-flex + L06 字面量/Decl 臂）
// --------------------------------------------------------------------------------

/// A/B 实验开关（unify 工作表的判等记忆化消融）：置 `L06_NO_CONV_MEMO=1`
/// 关闭（`=0` 不关闭）。
pub(super) static NO_CONV_MEMO: std::sync::LazyLock<std::sync::atomic::AtomicBool> =
    std::sync::LazyLock::new(|| {
        std::sync::atomic::AtomicBool::new(std::env::var("L06_NO_CONV_MEMO").is_ok_and(|v| v != "0"))
    });

/// unify 工作表条目：待比较子对，或 Π 余定义域的惰性比较屏障，或判等
/// 记忆化屏障。
pub(super) enum UItem<'a> {
    /// 待比较子对（level 相同的一对值；弹出时先 force 双方再分派）。
    Pair(u32, V, V),
    /// Π 余定义域的惰性比较（排在 dom 对之下——dom 不等即失败，cod 的
    /// eval 整个省掉）。
    EvalCod2(&'a Tm<'a>, Env<'a>, &'a Tm<'a>, Env<'a>, u32),
    /// 判等记忆化屏障（LIFO；健壮性论证同 L03——solve 写一次、成功单调）。
    Store((u64, u64)),
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
    decls: &FxHashMap<SmolStr, DeclEntryF>,
    mmap: &MutableMap,
    stack: &mut Vec<UItem<'a>>,
    pool: &mut Vec<RenameScratch<'a>>,
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
            bump, spine, work, vals, icits, defs, metas, decls, mmap, args1[k].0,
        );
        let f2 = force(
            bump, spine, work, vals, icits, defs, metas, decls, mmap, args2[k].0,
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
                bump, spine, work, vals, icits, defs, metas, decls, mmap, pool, &pr, m,
            )
            .is_some();
        }
        return true; // 两 spine 逐槽相等
    }
    // unify_sp 回落：前缀对压栈（内先压 → 弹出外先，对齐 unify_sp 的递归序）。
    // tag 7 不跳过：参考版对字面量实参照走 unify（恒败）、对 Decl 实参照
    // 走同名逐参——位相等的同单元也须分派（见 unify 的 (7,7) 臂）。
    for k in 0..common {
        let (a1, _) = args1[k];
        let (a2, _) = args2[k];
        if a1.0 != a2.0 || v_tag(a1) == 7 {
            stack.push(UItem::Pair(l, a1, a2));
        }
    }
    true
}

/// 异头 flex-flex（上游 `flexFlex`）：较长 spine 一侧优先反演求解；反演
/// 失败则用另一侧求解（rhs 是整条 flex 值）。
#[allow(clippy::too_many_arguments)]
fn flex_flex_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decls: &FxHashMap<SmolStr, DeclEntryF>,
    mmap: &MutableMap,
    ren: &mut RenBuf,
    pool: &mut Vec<RenameScratch<'a>>,
    gamma: u32,
    m1: u32,
    args1: &[(V, Icit)],
    v1: V,
    m2: u32,
    args2: &[(V, Icit)],
    v2: V,
) -> bool {
    let (ma, argsa, vrhs, mb, argsb, vlhs) = if args1.len() < args2.len() {
        (m2, args2, v2, m1, args1, v1)
    } else {
        (m1, args1, v1, m2, args2, v2)
    };
    match invert_bump(bump, spine, work, vals, icits, defs, metas, decls, mmap, ren, gamma, argsa) {
        Some(mask) => solve_with_pren_bump(
            bump, spine, work, vals, icits, defs, metas, decls, mmap, ren, pool, gamma, ma,
            argsa.len() as u32, mask, vrhs,
        ),
        None => {
            // 一侧非模式：落另一侧（solve = invert + solve_with_pren）
            match invert_bump(bump, spine, work, vals, icits, defs, metas, decls, mmap, ren, gamma, argsb) {
                Some(mask) => solve_with_pren_bump(
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, ren, pool, gamma,
                    mb, argsb.len() as u32, mask, vlhs,
                ),
                None => false,
            }
        }
    }
}

/// unification：结构比较 + 模式求解（含 intersect / flex-flex / 剪枝），
/// 工作表迭代。分派与参考版逐项对应（顺序按 tag 互斥重排）：λ/η → U →
/// Π（icit 相等）→ 同头 rigid 逐实参 → 同头 flex = intersect → 异头
/// flex = flex_flex → 单侧 flex 求解 → L06 的 LiteralType/Decl 臂 →
/// 其余刚性失配。**位相等捷径与实参跳过对 tag 7 关闭**：参考版 unify
/// 无 `(Lit, Lit)` 臂——同字面量也 Err，同单元 Decl 需走同名逐参分派，
/// 位相等直接放行会错 Accept。
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
    decls: &FxHashMap<SmolStr, DeclEntryF>,
    mmap: &MutableMap,
    ren: &mut RenBuf,
    conv: &mut ConvScratch,
    pool: &mut Vec<RenameScratch<'a>>,
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
                    eval_iter(bump, spine, work, vals, icits, defs, metas, decls, mmap, env, b1)
                };
                let vu = {
                    let env = env_ext(bump, e2, v_lvl(l));
                    eval_iter(bump, spine, work, vals, icits, defs, metas, decls, mmap, env, b2)
                };
                stack.push(UItem::Pair(l + 1, vt, vu));
                continue;
            }
            UItem::Pair(l, t, u) => (l, t, u),
        };
        // 位相等：同一值。tag 7 例外（见函数注释——参考版 unify 对字面量
        // 无自反性，Decl 需同名分派）
        if t.0 == u.0 && v_tag(t) != 7 {
            continue;
        }
        if memo_on && memo.contains(&(t.0, u.0)) {
            continue; // 本轮已判等过的子对（命中连 force 都省——成功单调）
        }
        let t = force(bump, spine, work, vals, icits, defs, metas, decls, mmap, t);
        let u = force(bump, spine, work, vals, icits, defs, metas, decls, mmap, u);
        if t.0 == u.0 && v_tag(t) != 7 {
            continue; // force 展开后同值（同一解的两处引用）
        }
        match (v_tag(t), v_tag(u)) {
            // λ 情形（eta 含）：两边都应用到同一个新变量
            (1, 1) => {
                let c1 = v_clo_of(t);
                let c2 = v_clo_of(u);
                let vt = {
                    let env = env_ext(bump, c1.env, v_lvl(l));
                    eval_iter(bump, spine, work, vals, icits, defs, metas, decls, mmap, env, c1.body)
                };
                let vu = {
                    let env = env_ext(bump, c2.env, v_lvl(l));
                    eval_iter(bump, spine, work, vals, icits, defs, metas, decls, mmap, env, c2.body)
                };
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                stack.push(UItem::Pair(l + 1, vt, vu));
            }
            // η：中性一侧按 λ 一侧的 icit 应用（Decl 头的应用可能触发
            // builtin——走 decl_apply）。守卫 `v_applicable`（参考版同款）：
            // 只对可应用值做——st2g 把 def 的函数值当"动态类型"返回后，λ 值
            // 会以类型身份流入 unify，与字面量/U/Π 的比较直接判失败。
            (_, 1) if v_applicable(spine, t) => {
                let c = v_clo_of(u);
                let vu = {
                    let env = env_ext(bump, c.env, v_lvl(l));
                    eval_iter(bump, spine, work, vals, icits, defs, metas, decls, mmap, env, c.body)
                };
                let vt = if is_declheaded(spine, t) {
                    decl_apply(
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, t, v_lvl(l),
                        c.icit,
                    )
                } else {
                    spine.push(t, v_lvl(l), c.icit)
                };
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                stack.push(UItem::Pair(l + 1, vt, vu));
            }
            (1, _) if v_applicable(spine, u) => {
                let c = v_clo_of(t);
                let vt = {
                    let env = env_ext(bump, c.env, v_lvl(l));
                    eval_iter(bump, spine, work, vals, icits, defs, metas, decls, mmap, env, c.body)
                };
                let vu = if is_declheaded(spine, u) {
                    decl_apply(
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, u, v_lvl(l),
                        c.icit,
                    )
                } else {
                    spine.push(u, v_lvl(l), c.icit)
                };
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                stack.push(UItem::Pair(l + 1, vt, vu));
            }

            // 宇宙
            (3, 3) => {}

            // Π：icit 相等才比；先比定义域，再惰性 eval 两侧余定义域
            (4, 4) => {
                let p = v_pi_of(t);
                let q = v_pi_of(u);
                if p.icit != q.icit {
                    return false;
                }
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                stack.push(UItem::EvalCod2(p.body, p.env, q.body, q.env, l));
                stack.push(UItem::Pair(l, p.dom, q.dom));
            }

            // 变量
            (0, 0) => return false, // 位相等已剪同 level；异 level 必不等

            // 中性链 vs 中性链
            (2, 2) => {
                let h1 = v_spine_of(t);
                let h2 = v_spine_of(u);
                let hd1 = spine.spine_head(h1);
                let hd2 = spine.spine_head(h2);
                let f1 = v_tag(hd1) == 5;
                let f2 = v_tag(hd2) == 5;
                if f1 && f2 {
                    // 双 flex：同头 intersect、异头 flex_flex
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
                            bump, spine, work, vals, icits, defs, metas, decls, mmap, &mut stack,
                            pool, l, m1, &a1, &a2,
                        )
                    } else {
                        flex_flex_bump(
                            bump, spine, work, vals, icits, defs, metas, decls, mmap, ren, pool,
                            l, m1, &a1, u, m2, &a2, t,
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
                // 同头判定：位相等（同变量 / 同 meta / 同单元）或**同名
                // Decl 头**（参考版 `x == x_prime` 比较 Span——decl 值的名
                // 全部来自 empty_span 构造，等价于名内容相等）
                let same_head = hd1.0 == hd2.0
                    || (v_tag(hd1) == 7
                        && v_tag(hd2) == 7
                        && matches!(
                            (v_xcell_of(hd1), v_xcell_of(hd2)),
                            (XCell::Decl(n1), XCell::Decl(n2)) if n1 == n2
                        ));
                if same_head {
                    // 同头刚性/Decl：逐实参比较（应用序；收集是逆序，压栈
                    // 倒回）。实参 icit 不比（类型已定，上游同款）。
                    if memo_on {
                        stack.push(UItem::Store((t.0, u.0)));
                    }
                    // 受控内联环（L03-L05 同款门控）：沿 `.a` 同步下走，仅在
                    // 纯 ChainWrap 同头延续处（实参链顶层 `f` 与本层 `f`
                    // 同字）；实参若是另一条中性链（Apply 惯例：`f` =
                    // partial 句柄 ≠ 头字；`?6 a b` vs `?0 a a` 的实参正是
                    // 此类）则停下，把子对交回完整分派（异头 flex 走
                    // flex_flex、同头 flex 走 intersect）——盲下钻会跳过内层
                    // 头分派、误比其内层变量。派发序与参考版 unify_sp 同序：
                    // 停钻时先压实参对、后压函数部分对（函数部分在栈顶先
                    // 弹出）。
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
                        // 位相等后缀：实参对免比（tag 7 除外——字面量恒
                        // 败、Decl 走同名分派），函数部分对仍须入栈
                        if a1.0 == a2.0 && v_tag(a1) != 7 {
                            if f1.0 != f2.0 {
                                stack.push(UItem::Pair(l, f1, f2));
                            }
                            break;
                        }
                        if v_tag(a1) == 2 && v_tag(a2) == 2 {
                            // 下钻门控：两侧的实参链顶层 f 与本层 f 同字
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
                    continue;
                }
                // 异头：一侧 flex 头（f1/f2 已排除双 flex）→ 该侧 solve；
                // 双刚性异头 → 刚性失配。
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
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, ren, pool, l, mv,
                    &args, rhs,
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

            // 其余形态：一侧（或两侧）是裸/带链 flex → 求解；L06 的
            // LiteralType / LiteralIntro / Decl 组合在此分派
            _ => {
                // L06 臂（参考版 unify 的末段）：String 类型自反；String
                // 类型与卡住 Decl 互通（decl 仍表示 String/U 型值）；同名
                // Decl 逐实参（空 spine 自反成立）；(Lit, Lit) 恒败（含
                // 同单元——参考版无该臂）。
                match (v_tag(t), v_tag(u)) {
                    (6, 6) => continue,
                    (6, 7) | (7, 6) => {
                        let other = if v_tag(t) == 7 { t } else { u };
                        match v_xcell_of(other) {
                            // 字面量值与 String 类型:刚性失配(参考版同)
                            XCell::Lit(_) => return false,
                            XCell::Decl(n) => match decls.get(*n) {
                                // 未登记名(可变全局等动态名):宽松放行——
                                // get_global 族动态余定义域的逃逸舱口
                                None => continue,
                                // 已登记名按登记类型把关:非 String 型(如
                                // U 型 builtin 的卡住值)不再与 String 混过
                                // (与参考版一致)
                                Some(e) => stack.push(UItem::Pair(l, v_lit_ty(), e.va)),
                            },
                        }
                    }
                    // 裸单元对（带实参的 Decl 是 tag 2 链，在 (2,2) 的同名
                    // 分支走 lockstep 逐实参）：同名 Decl 空 spine 自反成立
                    (7, 7) => match (v_xcell_of(t), v_xcell_of(u)) {
                        (XCell::Lit(_), XCell::Lit(_)) => return false, // 参考版无该臂
                        (XCell::Decl(n1), XCell::Decl(n2)) => {
                            if n1 == n2 {
                                continue;
                            }
                            return false; // 异名 Decl
                        }
                        _ => return false, // Lit vs Decl
                    },
                    _ => {}
                }
                let mut a1 = std::mem::take(&mut conv.scratch1);
                a1.clear();
                let ft = spine.flex_of(t, &mut a1);
                let mut a2 = std::mem::take(&mut conv.scratch2);
                a2.clear();
                let fu = spine.flex_of(u, &mut a2);
                let ok = match (ft, fu) {
                    (Some(m1), Some(m2)) => {
                        if m1 == m2 {
                            intersect_bump(
                                bump, spine, work, vals, icits, defs, metas, decls, mmap,
                                &mut stack, pool, l, m1, &a1, &a2,
                            )
                        } else {
                            flex_flex_bump(
                                bump, spine, work, vals, icits, defs, metas, decls, mmap, ren,
                                pool, l, m1, &a1, u, m2, &a2, t,
                            )
                        }
                    }
                    (Some(m), None) => solve_bump(
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, ren, pool, l, m,
                        &a1, u,
                    ),
                    (None, Some(m)) => solve_bump(
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, ren, pool, l, m,
                        &a2, t,
                    ),
                    (None, None) => false, // 刚性失配 / 病态混杂
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
        }
    }
    true
}
