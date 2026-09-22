//! force：迭代 force（L11 参考版臂集：Flex 展开 / Obj 重建 / VSub 推进）、
//! 显式替换推进（`frcs`/`frcs_env`）、深读点（`force_deep`）、参数视角 WHNF
//! （`force_arg`）、occurs 守卫（`val_mentions_lvl`）、独立应用（`vapp1`/
//! `vapp_ok`/`project`）与精化展开燃料（`PM_FUEL`/`refuel`/`burn`）。原
//! bump_spine_iter.rs 的 "force" + "frcs" 两节 + val_mentions_lvl +
//! metacontext 节尾的 project/vapp/fuel 块（按内容归属），逐行搬运
//! （2026-09-23 拆分）。

use bumpalo::Bump;
use rustc_hash::FxHashMap;
use std::cell::RefCell;
use std::rc::Rc;
use smol_str::SmolStr;

use super::parser::syntax::Icit;

use super::env::{env_ext, env_len, env_nth, CloCell, Decls, Env, EnvCons, PiCell};
use super::eval::{eval_aux, eval_iter, W};
use super::spine::{MetaEntry, Spine, HK_FLEX};
use super::subst::{wrap_sub, SubstV};
use super::syntax::{
    SumDataV, SumParamV, V, XCell, v_clo, v_clo_of, v_lvl, v_lvl_of, v_meta_of, v_pi,
    v_pi_of, v_spine_of, v_tag, v_xcell, v_xcell_of,
};

/// occurs 环守卫（参考版 `val_mentions_lvl` 同款）：只扫**解值自身**的浅层
/// 结构，闭包体 / Match 分支体跳过；**不扫 Flex/Decl 的 spine**（spine 是
/// 作用域事实，合法含当前方程的 rigid；旧 update_cxt 无 occurs 守卫，扫
/// spine 会把 GADT 嵌套 match 的合法解误判成环）。真环由运行时结构兜底。
pub(super) fn val_mentions_lvl(spine: &Spine, defs: &[V], v: V, x: u32) -> bool {
    match v_tag(v) {
        0 => v_lvl_of(v) == x,
        3 | 5 | 6 => false,
        2 => {
            let h = spine.spine_head(v_spine_of(v));
            if val_mentions_lvl(spine, defs, h, x) {
                return true;
            }
            let mut args: Vec<(V, Icit)> = Vec::new();
            spine.collect_args(v_spine_of(v), &mut args);
            args.iter().any(|(a, _)| val_mentions_lvl(spine, defs, *a, x))
        }
        1 => {
            let n = env_len(v_clo_of(v).env);
            (0..n).any(|i| val_mentions_lvl(spine, defs, env_nth(defs, v_clo_of(v).env, i), x))
        }
        4 => {
            let p = v_pi_of(v);
            val_mentions_lvl(spine, defs, p.dom, x)
                || (0..env_len(p.env)).any(|i| val_mentions_lvl(spine, defs, env_nth(defs, p.env, i), x))
        }
        7 => match v_xcell_of(v) {
            XCell::Lit(_) | XCell::Decl { .. } | XCell::Prim { .. } => false,
            XCell::Obj { val, .. } => val_mentions_lvl(spine, defs, *val, x),
            XCell::Sum { params, .. } => params
                .iter()
                .any(|p| val_mentions_lvl(spine, defs, p.val, x) || val_mentions_lvl(spine, defs, p.ty, x)),
            XCell::SumCase { typ, datas, .. } => {
                val_mentions_lvl(spine, defs, *typ, x)
                    || datas.iter().any(|d| val_mentions_lvl(spine, defs, d.val, x))
            }
            XCell::Match { scrutinee, env, .. } => {
                val_mentions_lvl(spine, defs, *scrutinee, x)
                    || (0..env_len(*env)).any(|i| val_mentions_lvl(spine, defs, env_nth(defs, *env, i), x))
            }
            XCell::VSub { val, .. } => val_mentions_lvl(spine, defs, *val, x),
        },
        _ => false,
    }
}

/// `v.field` 的值级投影：Sum 取索引参数的值；SumCase 先查 typ 的参数（索引）
/// 再查构造子字段。其余返回 None。（参考版 eval 的 Tm::Obj 臂自带
/// unwrap-panic 语义，调用方处理；本函数只在命中时给出值。）
fn project<'a>(v: V, name: &str) -> Option<V> {
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

/// 独立应用（eval_iter 之外的 v_app：force 的解值展开等）。λ → β；其余
/// 形态逐项对齐参考版 v_app：Rigid/Flex（裸或链）、卡住声明 Decl 与卡住
/// 投影 Obj → spine 压栈；字面量 / Prim / U / Π / LiteralType / Sum /
/// SumCase / 卡住 match → panic（"impossible apply"，参考版同款——两版
/// 同时不可达 / 同时 panic，判定一致）。
#[allow(clippy::too_many_arguments)]
pub(super) fn vapp1<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decl: &Decls<'a>,
    mutable: &RefCell<FxHashMap<SmolStr, V>>,
    f: V,
    a: V,
    i: Icit,
) -> V {
    // 精化包裹的头先 force 推开再分发（eval 等不经 force 的调用点会把
    // VSub 头送进来——如臂上下文里 Var 引用了被解槽）
    if v_tag(f) == 7 {
        if let XCell::VSub { .. } = v_xcell_of(f) {
            let f2 = force(bump, spine, defs, metas, decl, mutable, f);
            return vapp1(bump, spine, work, vals, icits, defs, metas, decl, mutable, f2, a, i);
        }
    }
    if v_tag(f) == 1 {
        let c = v_clo_of(f);
        let env = env_ext(bump, c.env, a);
        eval_iter(bump, spine, work, vals, icits, defs, metas, decl, mutable, env, c.body)
    } else if v_tag(f) == 7 {
        match v_xcell_of(f) {
            XCell::Obj { .. } | XCell::Decl { .. } => spine.push(f, a, i),
            _ => panic!("impossible apply"),
        }
    } else if v_tag(f) == 3 || v_tag(f) == 4 || v_tag(f) == 6 {
        panic!("impossible apply")
    } else {
        spine.push(f, a, i)
    }
}

/// η 展开的可应用性守卫（参考版 `unification::v_applicable` 的快版对应）：
/// 只有 `vapp1` 不会 panic 的形态能吃 η 新变量。tag 7 仅 `Obj`/`Decl` 可
/// （`Lit`/`Prim`/`Sum`/`SumCase`/`Match` → panic）；tag 3(U)/4(Pi)/6(Lit)
/// 不可；其余（Rigid 0 / Clo 1 / 链 2 / Flex 5）可。防止 λ 值以类型身份
/// 流入 unify 时（`get_global "f"` 取到 `x => x` 的登记值）触发
/// `impossible apply`。
#[inline]
pub(super) fn vapp_ok(v: V) -> bool {
    match v_tag(v) {
        3 | 4 | 6 => false,
        7 => matches!(
            v_xcell_of(v),
            XCell::Obj { .. } | XCell::Decl { .. } | XCell::VSub { .. }
        ),
        _ => true,
    }
}

// 精化传播的展开燃料（线程局部：每个测试/运行线程独立，与参考版
// `Infer::unify_fuel` 的"每次运行新建"口径一致）。仅 frcs 的 lookup 命中
// 与 Match 重选燃烧；外部入口（unify_catch / check_pm / check_pm_final /
// nf / bench_nf）充值。
const UNIFY_FUEL: u32 = 4096;
thread_local! {
    static PM_FUEL: std::cell::Cell<u32> = const { std::cell::Cell::new(UNIFY_FUEL) };
}

pub(super) fn refuel() {
    PM_FUEL.with(|c| c.set(UNIFY_FUEL));
}

#[inline]
fn burn() -> bool {
    PM_FUEL.with(|c| {
        let f = c.get();
        if f == 0 {
            false
        } else {
            c.set(f - 1);
            true
        }
    })
}

/// fuel 是否已耗尽（探测侧的降级判定用，2026-09-18 评审修复 L07 同款）：
/// probe 的索引方程失败时区分"结构冲突"与"预算耗尽"——后者按可达处理
/// （保守要求覆盖），否则深负载下的非穷尽 match 会被静默接受。
pub(super) fn pm_fuel_exhausted() -> bool {
    PM_FUEL.with(|c| c.get() == 0)
}

// force（迭代；L11 参考版只有 Flex + Obj 两臂）
// --------------------------------------------------------------------------------

/// **force**：把值更新到 metacontext 的当前状态。参考版 `Infer::force`
/// 只有 Flex 臂（已解 → 展开应用；未解原样）与 Obj 臂（递归进内层重建）——
/// 无 pm 精化读点展开、无 Decl unfold（求值期替换 + 卡住存根，递归自然
/// 停在 `Val::Decl`）、无 Match 重选、无投影归约。无燃料（meta 解由
/// occurs check 保证无环，参考版同款裸递归）。
///
/// 内部的 eval_iter 调用用**本调用私有的草稿栈**：外层 eval/unify 循环的
/// work/vals 不能被清空（force 可能在它们循环体中途被调用，且经 eval_aux
/// 与本函数互递归）。L04-L06 的 force 借用调用方的栈，是因为那几章的
/// eval_iter 不回调 force——这个差异**不是**漏同步，别往那方向改。四个
/// `Vec::new()` 本身不分配，只有真正下钻时才增长，早退路径零成本。
pub(super) fn force<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decl: &Decls<'a>,
    mutable: &RefCell<FxHashMap<SmolStr, V>>,
    v0: V,
) -> V {
    let mut v = v0;
    let mut work: Vec<W<'a>> = Vec::new();
    let mut vals: Vec<V> = Vec::new();
    let mut icits: Vec<Icit> = Vec::new();
    let mut args: Vec<(V, Icit)> = Vec::new();
    loop {
        match v_tag(v) {
            5 => match &metas[v_meta_of(v) as usize] {
                MetaEntry::Solved(sol, _) => v = *sol,
                _ => return v,
            },
            2 => {
                let h = v_spine_of(v);
                if spine.stack[h].hk != HK_FLEX {
                    // Rigid / Obj / Decl 头的链：卡住（参考版 force 无对应臂）。
                    // O(1) 读顶端槽种类，省去非 flex 链的整趟走底
                    return v;
                }
                let hd = spine.spine_head(h);
                // flex 链：解应用到全部实参（应用序 = 收集序的逆序）；
                // 每步都可能 β（参考版 vAppSp 逐步 vApp 同款）
                match &metas[v_meta_of(hd) as usize] {
                    MetaEntry::Unsolved(_) => return v,
                    MetaEntry::Solved(sol, _) => {
                        args.clear();
                        spine.collect_args(h, &mut args);
                        let mut t = *sol;
                        for &(a, i) in args.iter().rev() {
                            t = vapp1(
                                bump, spine, &mut work, &mut vals, &mut icits, defs, metas, decl, mutable, t, a, i,
                            );
                        }
                        v = t;
                    }
                }
            }
            7 => match v_xcell_of(v) {
                // force 递归进卡住投影的内层并**重建** Obj（参考版 force
                // 的 Obj 臂：`Val::Obj(self.force(x), a, b)`，重建后即返回）。
                // 不能把新 Obj 赋回 v 继续循环：内层已是 force 的不动点，
                // 下一轮又落进本臂重建出同形值，死循环
                //（binder 下的嵌套投影 `l.a.x` 即触发）。
                XCell::Obj { val, name } => {
                    let v2 = force(bump, spine, defs, metas, decl, mutable, *val);
                    // 内层未变则原样返回（L13 口径）：省一次 bump 分配，
                    // 更保住**位相等**——unify 的 `t == u` 捷径与 memo 不会
                    // 因同形重建而失配
                    if v2.0 == val.0 {
                        return v;
                    }
                    return v_xcell(bump.alloc(XCell::Obj { val: v2, name }));
                }
                // 显式替换（参考版 force 的 VSub 臂 / dpm-nbe `frc`）：把
                // 模式精化的解推进值的结构。入口不烧燃料（本层无燃料池），
                // 真正的精化传播只发生在被解 rigid 的读点。
                XCell::VSub { val, sub } => {
                    return frcs(bump, spine, defs, metas, decl, mutable, sub, *val);
                }
                _ => return v,
            },
            _ => return v,
        }
    }
}

// frcs：把显式替换推进值结构（参考版 Infer::frcs / dpm-nbe frcS）
// --------------------------------------------------------------------------------

/// 把替换 `σ` 推进值 `v` 的结构（参考版 `Infer::frcs` 同构）。σ 只作用于
/// **被包裹过**的值；推进到中性头为止——spine 逐槽推进，闭包 env 逐槽包裹
/// （惰性）。槽位命中裸 rigid 且 σ 有解时经 `vapp1` 应用（λ ⇒ β；中性头 ⇒
/// 收链），对应 dpm-nbe `napp (lookupSub sb v) (frcS sb sp)`。
///
/// 本层无燃料池（模块注释：force 无燃料）：lookup 命中直接推进，不做有界
/// 降级——与快版 force 对 meta 解无条件展开的既有权衡一致。
fn frcs<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decl: &Decls<'a>,
    mutable: &RefCell<FxHashMap<SmolStr, V>>,
    sub: &Rc<SubstV>,
    v0: V,
) -> V {
    if sub.is_empty() {
        return force(bump, spine, defs, metas, decl, mutable, v0);
    }
    match v_tag(v0) {
        7 => match v_xcell_of(v0) {
            // 内层先应用、外层后应用：组合后一次推进（frcS (subst sb sb') v）
            XCell::VSub { val, sub: sub2 } => {
                let composed = SubstV::compose(sub, sub2);
                frcs(bump, spine, defs, metas, decl, mutable, &composed, *val)
            }
            // Sum/SumCase 槽位只**包裹**不推进（槽位引用是作用域事实；
            // 旧 force 不进入这些结构——与参考版 frcs 同）
            XCell::Sum {
                name,
                params,
                cases,
                is_trait,
            } => {
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
                    is_trait: *is_trait,
                }))
            }
            XCell::SumCase {
                typ,
                case_name,
                datas,
                is_trait,
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
                    is_trait: *is_trait,
                }))
            }
            // 字面量 / builtin 体 / 全局声明头：σ 无从推进（参考版 frcs 的
            // `_ => v.clone()`；Decl 无 spine 槽可包）
            XCell::Lit(_) | XCell::Decl { .. } | XCell::Prim { .. } => {
                force(bump, spine, defs, metas, decl, mutable, v0)
            }
            XCell::Obj { val, name } => {
                let inner = frcs(bump, spine, defs, metas, decl, mutable, sub, *val);
                force(
                    bump,
                    spine,
                    defs,
                    metas,
                    decl,
                    mutable,
                    v_xcell(bump.alloc(XCell::Obj { val: inner, name })),
                )
            }
            // scrutinee **推进**；捕获 env 只包裹。推进后若已是构造子值则
            // 按首匹配重选（旧 refresh 重求值卡住 match 槽值的等价物）。
            XCell::Match {
                scrutinee,
                env,
                cases,
            } => {
                let s2 = frcs(bump, spine, defs, metas, decl, mutable, sub, *scrutinee);
                let e2 = frcs_env(bump, defs, sub, *env);
                let s3 = force(bump, spine, defs, metas, decl, mutable, s2);
                // Match 重选：推进后已是构造子值即重选分支（参考版
                // `frcs` 的 Match 臂同款）；重选本身烧 1，耗尽则不重选、
                // 按卡住 match 原样重建（有界降级）。
                if v_tag(s3) == 7
                    && matches!(v_xcell_of(s3), XCell::SumCase { .. })
                    && burn()
                {
                    if let Some((body, env3)) =
                        eval_aux(bump, spine, defs, metas, decl, mutable, s3, e2, cases)
                    {
                        let mut w2: Vec<W<'a>> = Vec::new();
                        let mut v2: Vec<V> = Vec::new();
                        let mut i2: Vec<Icit> = Vec::new();
                        let bv = eval_iter(
                            bump, spine, &mut w2, &mut v2, &mut i2, defs, metas, decl, mutable,
                            env3, body,
                        );
                        return force(bump, spine, defs, metas, decl, mutable, bv);
                    }
                }
                force(
                    bump,
                    spine,
                    defs,
                    metas,
                    decl,
                    mutable,
                    v_xcell(bump.alloc(XCell::Match {
                        scrutinee: s3,
                        env: e2,
                        cases,
                    })),
                )
            }
        },
        // 裸 rigid 的读点：lookup 命中（真正的精化传播）烧 1 fuel；fuel
        // 耗尽按未解处理（返回裸 rigid）。未命中零成本直通。
        0 => match SubstV::lookup_hit(bump, spine, defs, sub, v_lvl_of(v0)) {
            Some(hit) => {
                if !burn() {
                    return v0;
                }
                force(bump, spine, defs, metas, decl, mutable, hit)
            }
            None => v0,
        },
        // spine 链分派：rigid 头 = 解析应用（对齐 dpm-nbe
        // `napp (lookupSub sb v) (frcS sb sp)`——解值按应用序经 vapp1 拼接，
        // λ ⇒ β）；Flex/Obj/Decl 头 = 槽位只包裹，重建链后交回 force。
        2 => {
            let h = v_spine_of(v0);
            let hd = spine.spine_head(h);
            if v_tag(hd) == 0 {
                let x = v_lvl_of(hd);
                let mut head = match SubstV::lookup_hit(bump, spine, defs, sub, x) {
                    Some(hit) => {
                        if !burn() {
                            return v0;
                        }
                        force(bump, spine, defs, metas, decl, mutable, hit)
                    }
                    None => v_lvl(x),
                };
                // 解出值带实参但头不可应用（ill-typed 形态）时卡回原值
                if !vapp_ok(head) {
                    return v0;
                }
                let mut args: Vec<(V, Icit)> = Vec::new();
                spine.collect_args(h, &mut args);
                let mut w2: Vec<W<'a>> = Vec::new();
                let mut v2: Vec<V> = Vec::new();
                let mut i2: Vec<Icit> = Vec::new();
                for &(u, i) in args.iter().rev() {
                    head = vapp1(
                        bump, spine, &mut w2, &mut v2, &mut i2, defs, metas, decl, mutable, head,
                        wrap_sub(bump, sub, u), i,
                    );
                }
                head
            } else {
                // 槽位只包裹；Obj 头先推进被投影者；VSub 头（防御）先 force
                // 材料化再收链
                let base = if v_tag(hd) == 7 {
                    match v_xcell_of(hd) {
                        XCell::Obj { val, name } => v_xcell(bump.alloc(XCell::Obj {
                            val: frcs(bump, spine, defs, metas, decl, mutable, sub, *val),
                            name,
                        })),
                        XCell::VSub { .. } => {
                            force(bump, spine, defs, metas, decl, mutable, hd)
                        }
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
                force(bump, spine, defs, metas, decl, mutable, t)
            }
        }
        // 闭包 env 逐槽包裹（返回同型值，不再 force）
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
                dom: frcs(bump, spine, defs, metas, decl, mutable, sub, p.dom),
                env: frcs_env(bump, defs, sub, p.env),
                body: p.body,
            }))
        }
        // 裸 flex：无槽位可包，交回 force 走既有解链；U/LiteralType 原样
        5 => force(bump, spine, defs, metas, decl, mutable, v0),
        _ => v0,
    }
}

/// 闭包 env 逐槽包裹：全部槽换成"原槽值的 VSub 包裹"。包裹值不进 defs
/// 平坦区，整体退化为 binder 链表示（槽序与 `env_nth` 严格一致）。
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

/// `to_typ` 等"结构消费者"的深读点（参考版 `Infer::force_deep` 同款）：force
/// 到 WHNF 后，Sum/SumCase 的槽位值也 force 推开（旧机制下这些槽位已被
/// update_cxt/refresh 物化）。只服务 trait 求解边界，不进 spine/闭包体。
pub(super) fn force_deep<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decl: &Decls<'a>,
    mutable: &RefCell<FxHashMap<SmolStr, V>>,
    v: V,
) -> V {
    let v = force(bump, spine, defs, metas, decl, mutable, v);
    match v_tag(v) {
        7 => match v_xcell_of(v) {
            XCell::Sum {
                name,
                params,
                cases,
                is_trait,
            } => {
                let ps: Vec<SumParamV<'_>> = params
                    .iter()
                    .map(|p| SumParamV {
                        name: p.name,
                        val: force_deep(bump, spine, defs, metas, decl, mutable, p.val),
                        ty: force_deep(bump, spine, defs, metas, decl, mutable, p.ty),
                        icit: p.icit,
                    })
                    .collect();
                v_xcell(bump.alloc(XCell::Sum {
                    name,
                    params: bump.alloc_slice_fill_iter(ps),
                    cases,
                    is_trait: *is_trait,
                }))
            }
            XCell::SumCase {
                typ,
                case_name,
                datas,
                is_trait,
            } => {
                let ds: Vec<SumDataV<'_>> = datas
                    .iter()
                    .map(|d| SumDataV {
                        name: d.name,
                        val: force_deep(bump, spine, defs, metas, decl, mutable, d.val),
                        icit: d.icit,
                    })
                    .collect();
                v_xcell(bump.alloc(XCell::SumCase {
                    typ: force_deep(bump, spine, defs, metas, decl, mutable, *typ),
                    case_name,
                    datas: bump.alloc_slice_fill_iter(ds),
                    is_trait: *is_trait,
                }))
            }
            _ => v,
        },
        _ => v,
    }
}

/// 合一器**参数视角**的 WHNF（参考版 `Infer::force_arg` 同款）：不推开
/// VSub 精化包裹、不做 Match 重选——invert/prune_vflex 关心的是"元变量被
/// 应用在哪些槽位上"，物化会把可逆 spine 变成含构造子值的不可逆 spine。
/// 逐层解包 VSub 后：裸 rigid 返回裸值；带实参的 rigid 链 / 卡住 match 返回
/// **原值**（包裹保留）；其余形态全量 force 推开。
#[allow(clippy::too_many_arguments)]
pub(super) fn force_arg<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decl: &Decls<'a>,
    mutable: &RefCell<FxHashMap<SmolStr, V>>,
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
        0 => cur,
        2 if v_tag(spine.spine_head(v_spine_of(cur))) == 0 => v,
        7 if matches!(v_xcell_of(cur), XCell::Match { .. }) => v,
        _ => force(bump, spine, defs, metas, decl, mutable, v),
    }
}

