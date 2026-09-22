//! force：迭代 force 主循环与 `frcs`/`frcs_env`/`force_arg`，独立应用
//! （`vapp1`/`vapp_ok`/`project`）与 occurs 守卫 `val_mentions_lvl`。
//! 原 bump_spine_iter.rs 的 "force（迭代）" 节及其前的 v_app 族，逐行
//! 搬运（2026-09-23 拆分）。

use bumpalo::Bump;
use rustc_hash::FxHashMap;
use std::rc::Rc;

use super::parser::syntax::Icit;

use super::env::{CloCell, Env, env_ext, env_len, env_nth, EnvCons, PiCell};
use super::eval::{eval_aux, eval_iter, W};
use super::prim::{burn, DeclEntryF, Fuel, is_selfref_val, MutableMap, prim_reduce};
use super::spine::{HK_DECL, HK_OBJ, HK_PRIM, MetaEntry, Spine, xcell_head_name};
use super::subst::{SubstV, wrap_sub};
use super::syntax::{SumDataV, SumParamV, V, v_clo, v_clo_of, v_lvl, v_lvl_of, v_meta_of, v_pi, v_pi_of, v_spine_of, v_tag, v_xcell, v_xcell_of, XCell};

/// 独立应用（eval_iter 之外的 v_app：force 的解值/pending 应用、prim 的
/// `change_mutable`）。λ → β；卡住 match → pending 累积（值层保存，分支
/// 选中后逐个应用——项层 splice 会把实参自由变量引到错误上下文）；其余
/// → spine 压栈（Rigid/Flex/Decl/Prim/Obj 头的链）。参考版对 Π/U/字面量/
/// Sum/SumCase 的应用 panic（"impossible apply"）——快版照做（两版同时
/// 不可达 / 同时 panic，判定一致）。
#[allow(clippy::too_many_arguments)]
pub(super) fn vapp1<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    f: V,
    a: V,
    i: Icit,
) -> V {
    if v_tag(f) == 1 {
        let c = v_clo_of(f);
        let env = env_ext(bump, c.env, a);
        eval_iter(
            bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, env, c.body,
        )
    } else if v_tag(f) == 7 {
        match v_xcell_of(f) {
            XCell::Match {
                scrutinee,
                env,
                cases,
                pending,
            } => {
                // 卡住 match 吸收实参进 pending（新单元——bump 内不可变）
                let mut p: Vec<(V, Icit)> = Vec::with_capacity(pending.len() + 1);
                p.extend_from_slice(pending);
                p.push((a, i));
                v_xcell(bump.alloc(XCell::Match {
                    scrutinee: *scrutinee,
                    env: *env,
                    cases,
                    pending: bump.alloc_slice_fill_iter(p),
                }))
            }
            // Lit / Sum / SumCase 不可应用（参考版 panic）；Decl/Prim/Obj
            // 压栈成链
            XCell::Lit(_) | XCell::Sum { .. } | XCell::SumCase { .. } => {
                panic!("impossible apply")
            }
            // 精化包裹的值先推开再分发（eval(App) 等不经 force 的调用点
            // 会把 VSub 头送进来——如臂上下文里 Var 引用了被解槽；force
            // 顶层不再产出 VSub，递归必终止）
            XCell::VSub { .. } => {
                let ff = force(bump, spine, defs, metas, decls, mmap, fuel, f);
                return vapp1(
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, ff, a, i,
                );
            }
            _ => spine.push(f, a, i),
        }
    } else if v_tag(f) == 3 || v_tag(f) == 4 || v_tag(f) == 6 {
        // U / Π / LiteralType 不可应用（参考版 panic）
        panic!("impossible apply")
    } else {
        spine.push(f, a, i)
    }
}

/// η 展开的可应用性守卫（参考版 `unification::v_applicable` 的快版对应，
/// L06 同款）：只有 `vapp1` 能吃 η 新变量的形态——裸 Rigid(0)/未解
/// Flex(5)/链(2)，以及 Decl/Prim/Obj/Match/VSub 头的 tag 7 单元；字面量 /
/// Sum / SumCase 单元与 U(3)/Π(4)/LiteralType(6) 不可应用（`vapp1`
/// panic 集）。λ 与不可应用值相遇时 η 臂不展开，落空后按合一失败返回
/// （与参考版守卫同判；守卫为真时行为照旧）。frcs 的解析应用读点共用
/// 同一守卫（"解值带实参但头不可应用 ⇒ 卡回原值"）。
#[inline]
pub(super) fn vapp_ok(v: V) -> bool {
    match v_tag(v) {
        3 | 4 | 6 => false,
        7 => !matches!(
            v_xcell_of(v),
            XCell::Lit(_) | XCell::Sum { .. } | XCell::SumCase { .. }
        ),
        _ => true,
    }
}

/// `v.field` 的值级投影：Sum 取索引参数的值；SumCase 先查 typ 的参数（索引）
/// 再查构造子字段。其余（Rigid / Flex / Decl / 卡住的 Obj / 函数……）返回
/// None → 卡住成 `Obj`。（参考版 mod.rs `project` 同款。）
pub(super) fn project<'a>(v: V, name: &str) -> Option<V> {
    match v_tag(v) {
        7 => match v_xcell_of(v) {
            XCell::Sum { params, .. } => {
                params.iter().find(|p| p.name == name).map(|p| p.val)
            }
            XCell::SumCase { typ, datas, .. } => {
                let params = match v_xcell_of(*typ) {
                    XCell::Sum { params, .. } => params,
                    _ => return None,
                };
                params
                    .iter()
                    .find(|p| p.name == name)
                    .map(|p| p.val)
                    .or_else(|| datas.iter().find(|d| d.name == name).map(|d| d.val))
            }
            _ => None,
        },
        _ => None,
    }
}

/// 值树里是否出现某层级（浅层结构扫描；闭包跳过——那里的环由 force 的
/// fuel 兜底）。特化解的环守卫（`pm_solve`）用。（参考版
/// `val_mentions_lvl` 同款遍历面。）
pub(crate) fn val_mentions_lvl(spine: &Spine, defs: &[V], v: V, x: u32) -> bool {
    match v_tag(v) {
        // Rigid 裸头
        0 => v_lvl_of(v) == x,
        2 => {
            // 链形态也要查链头：Rigid 头链查头层级、Obj 头链查被投影者
            // （参考版 `Val::Rigid(y, sp) => *y == x || spine(sp, x)`、
            // `Val::Obj(o, _, sp) => val_mentions_lvl(o, x) || spine(sp, x)`）
            let h = v_spine_of(v);
            let hd = spine.spine_head(h);
            let head_hit = match v_tag(hd) {
                0 => v_lvl_of(hd) == x,
                7 => match v_xcell_of(hd) {
                    XCell::Obj { val, .. } => val_mentions_lvl(spine, defs, *val, x),
                    _ => false,
                },
                _ => false,
            };
            let mut args: Vec<(V, Icit)> = Vec::new();
            spine.collect_args(h, &mut args);
            head_hit || args.iter().any(|(a, _)| val_mentions_lvl(spine, defs, *a, x))
        }
        // Flex 裸头（链在 tag 2）
        5 => false,
        1 | 4 => false, // Lam/Pi 闭包跳过（参考版同）
        3 | 6 => false,
        7 => match v_xcell_of(v) {
            XCell::Lit(_) => false,
            XCell::Decl(_) | XCell::Prim(_) => false, // 空实参（链在 tag 2）
            // VSub：只扫解值自身的结构，**不扫 σ 的映射值**——σ 的其它条目
            // （如头部精化的构造子值）合法引用别的模式变量，扫进来会把无害
            // 的解误判成环。σ 槽位若真引用 x，解包后的结构里自会以裸
            // Rigid(x) 出现（对齐旧世界"occurs 只看解的裸值"的语义；更深
            // 的间接环仍由 force 的 fuel 兜底）。
            XCell::VSub { val, .. } => val_mentions_lvl(spine, defs, *val, x),
            XCell::Obj { val, .. } => val_mentions_lvl(spine, defs, *val, x),
            XCell::Sum { params, .. } => params
                .iter()
                .any(|p| val_mentions_lvl(spine, defs, p.val, x) || val_mentions_lvl(spine, defs, p.ty, x)),
            XCell::SumCase { typ, datas, .. } => {
                val_mentions_lvl(spine, defs, *typ, x)
                    || datas.iter().any(|d| val_mentions_lvl(spine, defs, d.val, x))
            }
            XCell::Match {
                scrutinee,
                env,
                pending,
                ..
            } => {
                // env 槽序与 env_nth 一致：链段（头 = 最内层）先走，平坦区
                // 倒序——单趟遍历替代 (0..env_len).any(env_nth) 的 O(d²)
                let env_hit = {
                    let mut hit = false;
                    let mut n = env.binds;
                    while let Some(e) = n {
                        if val_mentions_lvl(spine, defs, e.val, x) {
                            hit = true;
                            break;
                        }
                        n = e.next;
                    }
                    if !hit {
                        for k in 0..env.flat_len {
                            if val_mentions_lvl(
                                spine,
                                defs,
                                defs[(env.flat_base + env.flat_len - 1 - k) as usize],
                                x,
                            ) {
                                hit = true;
                                break;
                            }
                        }
                    }
                    hit
                };
                val_mentions_lvl(spine, defs, *scrutinee, x)
                    || env_hit
                    || pending.iter().any(|(u, _)| val_mentions_lvl(spine, defs, *u, x))
            }
        },
        _ => false,
    }
}
// force（迭代）
// --------------------------------------------------------------------------------

/// **force**：把值更新到 metacontext / 模式特化的当前状态。L07 增量（参考
/// 版 `Infer::force` 的迭代化——保序语义）：
/// - Flex 已解 → 展开应用（burn fuel）；
/// - VSub → frcs：把模式精化的解 σ 推进值的结构（入口不烧 fuel——真正的
///   精化传播只发生在被解变量的读点，见 [`frcs`]）；
/// - Match → force scrutinee；是 SumCase 且 burn → eval_aux 选分支：选中 →
///   值 = eval(分支体) 后逐个 v_app(pending)，再 force；否则原样卡住返回；
/// - Decl → 查表 unfold（burn，自引用占位直接按中性返回）；
/// - Prim → prim_reduce（15 个 builtin；字面量/元数检查不满足保持卡住；
///   空实参同样烧 1 fuel——与参考版逐 force 调用消耗对齐）；
/// - Obj → force 被投影者 → project 命中且 burn → 应用链上实参，否则卡回
///   Obj（参考版返回 forced 内层的新单元，快版同款重建）。
///
/// 内部的 eval_iter 调用用**本调用私有的草稿栈**：外层 eval/unify 循环的
/// work/vals 不能被清空（force 可能在它们循环体中途被调用，且经 eval_aux
/// 与本函数互递归）。L04-L06 的 force 借用调用方的栈，是因为那几章的
/// eval_iter 不回调 force——这个差异**不是**漏同步，别往那方向改。四个
/// `Vec::new()` 本身不分配，只有真正下钻时才增长，早退路径零成本。
#[allow(clippy::too_many_arguments)]
pub(super) fn force<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    v0: V,
) -> V {
    let mut v = v0;
    // 实参缓冲在本次 force 调用内的展开轮间复用（clear 保容量）
    let mut work: Vec<W<'a>> = Vec::new();
    let mut vals: Vec<V> = Vec::new();
    let mut icits: Vec<Icit> = Vec::new();
    let mut args: Vec<(V, Icit)> = Vec::new();
    loop {
        match v_tag(v) {
            5 => match &metas[v_meta_of(v) as usize] {
                MetaEntry::Solved(sol, _) if burn(fuel) => v = *sol,
                _ => return v,
            },
            2 => {
                let h = v_spine_of(v);
                let hd = spine.spine_head(h);
                if v_tag(hd) == 5 {
                    // flex 链：解应用到全部实参（应用序 = 收集序的逆序）；
                    // 每步都可能 β / 触发 prim / 吸收进 pending——参考版
                    // vAppSp 逐步 vApp 同款
                    match &metas[v_meta_of(hd) as usize] {
                        MetaEntry::Unsolved(_) => return v,
                        MetaEntry::Solved(sol, _) => {
                            if !burn(fuel) {
                                return v;
                            }
                            args.clear();
                            spine.collect_args(h, &mut args);
                            let mut t = *sol;
                            for &(a, i) in args.iter().rev() {
                                t = vapp1(
                                    bump, spine, &mut work, &mut vals, &mut icits, defs, metas,
                                    decls, mmap, fuel, t, a, i,
                                );
                            }
                            v = t;
                        }
                    }
                } else {
                    match spine.stack[h].hk {
                        HK_DECL => {
                            let name = xcell_head_name(spine, hd);
                            match decls.get(name) {
                                Some(e) if !is_selfref_val(e.val, name) && burn(fuel) => {
                                    args.clear();
                                    spine.collect_args(h, &mut args);
                                    let mut t = e.val;
                                    for &(a, i) in args.iter().rev() {
                                        t = vapp1(
                                            bump, spine, &mut work, &mut vals, &mut icits, defs,
                                            metas, decls, mmap, fuel, t, a, i,
                                        );
                                    }
                                    v = t;
                                }
                                _ => return v,
                            }
                        }
                        HK_PRIM => {
                            // 卡住的内建：实参按自然序交给 builtin 体归约；
                            // 元数不足 / 实参不合 / 缺名时保持卡住。参考版对
                            // 每次 force 调用烧 1 fuel（归约成功与否皆然）。
                            // 实参先逐个 force 再交给 prim_reduce（与参考版
                            // Val::Prim 分支对齐）：spine 槽可能存着未归约的
                            // 嵌套 prim，不 force 外层永远过不了字面量检查。
                            if !burn(fuel) {
                                return v;
                            }
                            let name = xcell_head_name(spine, hd);
                            args.clear();
                            spine.collect_args(h, &mut args);
                            for i in 0..args.len() {
                                let a = args[i].0;
                                args[i].0 =
                                    force(bump, spine, defs, metas, decls, mmap, fuel, a);
                            }
                            match prim_reduce(
                                bump, spine, &mut work, &mut vals, &mut icits, defs, metas,
                                decls, mmap, fuel, name, &args,
                            ) {
                                Some(r) => v = r,
                                None => return v,
                            }
                        }
                        HK_OBJ => {
                            // 卡住投影：先 force 被投影者，project 命中 →
                            // 应用链上实参；miss → 重建 forced 内层的卡住
                            // Obj（参考版 `Val::Obj(Box::new(v), name, sp)`）
                            let (inner, oname) = match v_xcell_of(hd) {
                                XCell::Obj { val, name } => (*val, *name),
                                _ => unreachable!("hk=Obj 的链头必是 Obj 单元"),
                            };
                            let v2 = force(
                                bump, spine, defs, metas, decls, mmap, fuel, inner,
                            );
                            match project(v2, oname) {
                                Some(p) if burn(fuel) => {
                                    args.clear();
                                    spine.collect_args(h, &mut args);
                                    let mut t = p;
                                    for &(a, i) in args.iter().rev() {
                                        // 命中路径须走 vapp1（参考版 vAppSp
                                        // 逐步 vApp 同款）：字段值可能是 Lam
                                        // 闭包（β）或卡住 Match（吸收 pending）
                                        // ——spine.push 只压中性槽，会搁浅
                                        t = vapp1(
                                            bump, spine, &mut work, &mut vals, &mut icits,
                                            defs, metas, decls, mmap, fuel, t, a,
                                            i,
                                        );
                                    }
                                    v = t;
                                }
                                _ => {
                                    args.clear();
                                    spine.collect_args(h, &mut args);
                                    let mut t =
                                        v_xcell(bump.alloc(XCell::Obj { val: v2, name: oname }));
                                    for &(a, i) in args.iter().rev() {
                                        t = spine.push(t, a, i);
                                    }
                                    return t;
                                }
                            }
                        }
                        _ => return v,
                    }
                }
            }
            // 裸 Rigid：精化的解只对被 VSub 包裹的值可见（显式替换读点），
            // 裸 rigid 不再查任何全局表——槽位引用是作用域事实
            0 => return v,
            7 => match v_xcell_of(v) {
                XCell::Lit(_) | XCell::Sum { .. } | XCell::SumCase { .. } => return v,
                // 显式替换（参考版 force 的 VSub 臂 / dpm-nbe `frc`）：入口
                // 不烧 fuel——frcs 的 Rigid 读点 lookup 命中时才烧 1，对齐
                // 旧 pm_defs 时代"force(Rigid) 查表展开烧 1"的燃烧剖面。
                // 组合 σ 的机械开销免费，fuel 耗尽的降级点在 lookup 命中处。
                XCell::VSub { val, sub } => {
                    v = frcs(bump, spine, defs, metas, decls, mmap, fuel, sub, *val);
                }
                XCell::Decl(n) => match decls.get(*n) {
                    Some(e) if !is_selfref_val(e.val, n) && burn(fuel) => {
                        v = e.val; // 空实参：直接继续 force 展开值
                    }
                    _ => return v,
                },
                XCell::Prim(_) => {
                    // 空实参：prim_reduce 元数检查必败；与参考版一致仍按
                    // force 调用消耗 1 fuel
                    if !burn(fuel) {
                        return v;
                    }
                    return v;
                }
                XCell::Obj { val, name } => {
                    let v2 = force(bump, spine, defs, metas, decls, mmap, fuel, *val);
                    match project(v2, name) {
                        Some(p) if burn(fuel) => v = p,
                        _ => {
                            // 内层未变则原样返回（L13 口径）：省一次 bump
                            // 分配，更保住**位相等**——unify 的 `t == u`
                            // 捷径与 memo 才不会因同形重建而失配
                            if v2.0 == val.0 {
                                return v;
                            }
                            return v_xcell(bump.alloc(XCell::Obj { val: v2, name }));
                        }
                    }
                }
                XCell::Match {
                    scrutinee,
                    env,
                    cases,
                    pending,
                } => {
                    // 卡住的 match：scrutinee 在创建之后才被特化/解出时，
                    // 这里重新尝试选分支（精化传播进"卡住 match 里面"）。
                    // 选中 → eval 分支体 → 值层逐个应用 pending → 继续
                    // force；否则原样卡住返回（pending 原样保留）。
                    let s2 = force(bump, spine, defs, metas, decls, mmap, fuel, *scrutinee);
                    let mut matched = false;
                    if v_tag(s2) == 7 && matches!(v_xcell_of(s2), XCell::SumCase { .. }) {
                        if burn(fuel) {
                            if let Some((body_tm, env2)) = eval_aux(
                                bump, spine, defs, metas, decls, mmap, fuel, s2, *env,
                                cases,
                            ) {
                                let mut vb = eval_iter(
                                    bump, spine, &mut work, &mut vals, &mut icits, defs, metas,
                                    decls, mmap, fuel, env2, body_tm,
                                );
                                for &(u, i) in *pending {
                                    vb = vapp1(
                                        bump, spine, &mut work, &mut vals, &mut icits, defs,
                                        metas, decls, mmap, fuel, vb, u, i,
                                    );
                                }
                                v = vb;
                                matched = true;
                            }
                        }
                    }
                    if !matched {
                        return v;
                    }
                }
            },
            _ => return v,
        }
    }
}

/// 把替换 `σ` 推进值 `v` 的结构（参考版 `Infer::frcs` / dpm-nbe `frcS` 的
/// 快版对应）。与 `force` 的分工：σ 是本次精化的局部解，只作用于**被包裹
/// 过**的值；头部与 scrutinee 推进、闭包 env 逐槽包裹（惰性，不进入闭包体
/// 重求值）；spine 槽与 Sum/SumCase 槽**只包裹不物化**（设计文档 §4 的槽位
/// 纪律——槽位引用是作用域事实，物化会破坏后续 solve 的 invert）。
///
/// fuel 剖面：入口与各包裹臂不烧 fuel；唯一的燃烧点是 Rigid 读点的
/// `lookup_hit` 命中（对齐旧 pm_defs 的 force(Rigid) 查表展开烧 1）；
/// fuel 耗尽按未解处理（返回裸 rigid，有界降级，防闭环无限推进）。
#[allow(clippy::too_many_arguments)]
fn frcs<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    sub: &Rc<SubstV>,
    v0: V,
) -> V {
    if sub.is_empty() {
        return force(bump, spine, defs, metas, decls, mmap, fuel, v0);
    }
    let mut work: Vec<W<'a>> = Vec::new();
    let mut vals: Vec<V> = Vec::new();
    let mut icits: Vec<Icit> = Vec::new();
    match v_tag(v0) {
        // 内层先应用、外层后应用：组合后一次推进（frcS (subst sb sb') v）
        7 => match v_xcell_of(v0) {
            XCell::VSub { val, sub: sub2 } => {
                let composed = SubstV::compose(sub, sub2);
                frcs(bump, spine, defs, metas, decls, mmap, fuel, &composed, *val)
            }
            // 中性头单元：包裹后交回 force 重走既有臂（meta 解 / decl 展开
            // / prim 归约 / 投影），保持"σ 之下的值 force 到同一 WHNF 形态"
            // 的旧语义。Sum/SumCase 槽位只**包裹**不推进。
            XCell::Sum { name, params, cases } => {
                let ps: Vec<SumParamV<'_>> = params
                    .iter()
                    .map(|p| SumParamV {
                        name: p.name,
                        val: wrap_sub(bump, sub, p.val),
                        ty: wrap_sub(bump, sub, p.ty),
                        icit: p.icit,
                    })
                    .collect();
                v_xcell(bump.alloc(XCell::Sum {
                    name,
                    params: bump.alloc_slice_fill_iter(ps),
                    cases,
                }))
            }
            XCell::SumCase {
                typ,
                case_name,
                datas,
            } => {
                let ds: Vec<SumDataV<'_>> = datas
                    .iter()
                    .map(|d| SumDataV {
                        name: d.name,
                        val: wrap_sub(bump, sub, d.val),
                        icit: d.icit,
                    })
                    .collect();
                v_xcell(bump.alloc(XCell::SumCase {
                    typ: wrap_sub(bump, sub, *typ),
                    case_name,
                    datas: bump.alloc_slice_fill_iter(ds),
                }))
            }
            XCell::Lit(_) => v0,
            XCell::Decl(_) | XCell::Prim(_) => {
                force(bump, spine, defs, metas, decls, mmap, fuel, v0)
            }
            XCell::Obj { val, name } => {
                let inner = frcs(bump, spine, defs, metas, decls, mmap, fuel, sub, *val);
                force(
                    bump,
                    spine,
                    defs,
                    metas,
                    decls,
                    mmap,
                    fuel,
                    v_xcell(bump.alloc(XCell::Obj { val: inner, name })),
                )
            }
            // scrutinee **推进**（重选分支需要解出的构造子值）；捕获 env 与
            // pending 只包裹。交回 force：scrutinee 若已是构造子值，force
            // 的 Match 臂按同一纪律重选分支
            XCell::Match {
                scrutinee,
                env,
                cases,
                pending,
            } => {
                let ps: Vec<(V, Icit)> = pending
                    .iter()
                    .map(|(u, i)| (wrap_sub(bump, sub, *u), *i))
                    .collect();
                let s2 = frcs(bump, spine, defs, metas, decls, mmap, fuel, sub, *scrutinee);
                let e2 = frcs_env(bump, defs, sub, *env);
                force(
                    bump,
                    spine,
                    defs,
                    metas,
                    decls,
                    mmap,
                    fuel,
                    v_xcell(bump.alloc(XCell::Match {
                        scrutinee: s2,
                        env: e2,
                        cases,
                        pending: bump.alloc_slice_fill_iter(ps),
                    })),
                )
            }
        },
        // 裸 Rigid 的读点：lookup 命中（真正的精化传播）烧 1 fuel——对齐旧
        // pm_defs 的 force(Rigid) 查表展开烧 1 剖面；fuel 耗尽按未解处理
        // （返回裸 rigid）。未命中零成本直通。
        0 => match SubstV::lookup_hit(bump, spine, defs, sub, v_lvl_of(v0)) {
            Some(hit) => {
                if !burn(fuel) {
                    return v0;
                }
                force(bump, spine, defs, metas, decls, mmap, fuel, hit)
            }
            None => v0,
        },
        // spine 链分派：Rigid 头 = 解析应用（对齐 dpm-nbe 的
        // `napp (lookupSub sb v) (frcS sb sp)`——解值按应用序经 vapp1 拼接，
        // λ ⇒ β、Match ⇒ pending、中性头 ⇒ 收链）；Flex/Decl/Prim/Obj 头
        // = 槽位只包裹，重建链后交回 force。
        2 => {
            let h = v_spine_of(v0);
            let hd = spine.spine_head(h);
            if v_tag(hd) == 0 {
                let x = v_lvl_of(hd);
                let mut head = match SubstV::lookup_hit(bump, spine, defs, sub, x) {
                    Some(hit) => {
                        if !burn(fuel) {
                            return v0;
                        }
                        force(bump, spine, defs, metas, decls, mmap, fuel, hit)
                    }
                    None => v_lvl(x),
                };
                // 解出值带实参但头不可应用（对非函数解变量做应用的
                // ill-typed 形态）时卡回原值，不进 vapp1（η 臂的 vapp_ok
                // 守卫同款加固；fuel 耗尽的裸 rigid 回退同型）
                if !vapp_ok(head) {
                    return v0;
                }
                let mut args: Vec<(V, Icit)> = Vec::new();
                spine.collect_args(h, &mut args);
                for &(u, i) in args.iter().rev() {
                    head = vapp1(
                        bump, spine, &mut work, &mut vals, &mut icits, defs, metas, decls, mmap,
                        fuel, head, wrap_sub(bump, sub, u), i,
                    );
                }
                head
            } else {
                // 槽位只包裹（VSub 值从不进 spine 的函数侧）；Obj 头先推进
                // 被投影者（tag 7 判定保证 v_xcell_of 安全）
                let base = if v_tag(hd) == 7 {
                    match v_xcell_of(hd) {
                        XCell::Obj { val, name } => v_xcell(bump.alloc(XCell::Obj {
                            val: frcs(bump, spine, defs, metas, decls, mmap, fuel, sub, *val),
                            name,
                        })),
                        _ => hd,
                    }
                } else {
                    hd
                };
                let mut args: Vec<(V, Icit)> = Vec::new();
                spine.collect_args(h, &mut args);
                let mut t = base;
                for &(u, i) in args.iter().rev() {
                    t = spine.push(t, wrap_sub(bump, sub, u), i);
                }
                force(bump, spine, defs, metas, decls, mmap, fuel, t)
            }
        }
        // 闭包 env 逐槽包裹（dpm-nbe `subst sb cl` 的惰性形态）；返回同型
        // 值，不再 force（参考版 Lam/Pi 臂直通）
        1 => {
            let c = v_clo_of(v0);
            v_clo(bump.alloc(CloCell {
                name: c.name,
                icit: c.icit,
                env: frcs_env(bump, defs, sub, c.env),
                body: c.body,
            }))
        }
        4 => {
            let p = v_pi_of(v0);
            v_pi(bump.alloc(PiCell {
                name: p.name,
                icit: p.icit,
                dom: frcs(bump, spine, defs, metas, decls, mmap, fuel, sub, p.dom),
                env: frcs_env(bump, defs, sub, p.env),
                body: p.body,
            }))
        }
        // 裸 flex：无槽位可包，交回 force 走既有解链（与参考版
        // force(Flex(m, wrap_sp(σ, []))) 等价）；U / LiteralType 原样
        5 => force(bump, spine, defs, metas, decls, mmap, fuel, v0),
        _ => v0,
    }
}

/// 闭包 env 逐槽包裹：全部槽换成"原槽值的 VSub 包裹"。包裹值不进 defs
/// 平坦区，整体退化为 binder 链表示（槽序与 `env_nth` 严格一致——链段
/// 在前、平坦区倒序）。
pub(super) fn frcs_env<'a>(bump: &'a Bump, defs: &[V], sub: &Rc<SubstV>, env: Env<'a>) -> Env<'a> {
    if sub.is_empty() {
        return env;
    }
    let n = env_len(env);
    let mut e: Option<&'a EnvCons<'a>> = None;
    for i in (0..n).rev() {
        let v = env_nth(defs, env, i);
        e = Some(bump.alloc(EnvCons {
            val: wrap_sub(bump, sub, v),
            next: e,
        }));
    }
    Env {
        flat_base: 0,
        flat_len: 0,
        binds: e,
    }
}

/// 合一器**参数视角**的 WHNF：与 force 相同，但不推开 VSub 精化包裹、不做
/// Match 重选。`invert` / `prune_vflex` 关心的是"元变量被应用在哪些槽位
/// 上"——槽位引用（裸 Rigid）本身就是作用域事实，分支内的精化等式不改变
/// 槽位的存在；在它们身上展开反而会把可逆 spine 变成含构造子值的不可逆
/// spine。（参考版 `Infer::force_arg` 同款守卫。）
///
/// 逐层解包 VSub（嵌套 match 的上下文被外层臂与内层臂各 subst_cxt 一次，
/// 单层解包会漏）后：裸 rigid 返回裸值（已解也不推开——invert 视角，对
/// 齐旧"pm_defs 不参与 invert"的行为）；带实参的 rigid 链 / Match 返回
/// **原值**（包裹原样保留）；其余形态全量 force 推开。
#[allow(clippy::too_many_arguments)]
pub(super) fn force_arg<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    v: V,
) -> V {
    let mut cur = v;
    loop {
        match v_tag(cur) {
            7 => match v_xcell_of(cur) {
                XCell::VSub { val, .. } => cur = *val,
                _ => break,
            },
            _ => break,
        }
    }
    match v_tag(cur) {
        // 解到底仍是裸 rigid ⇒ 槽位保留（返回裸值）
        0 => cur,
        // 带实参的 rigid 链 / 卡住 match：返回原值（含 VSub 包裹）
        2 if v_tag(spine.spine_head(v_spine_of(cur))) == 0 => v,
        7 if matches!(v_xcell_of(cur), XCell::Match { .. }) => v,
        _ => force(bump, spine, defs, metas, decls, mmap, fuel, v),
    }
}
