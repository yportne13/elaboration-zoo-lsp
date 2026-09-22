//! force：迭代 force（`force`/`frcs`/`frcs_env`/`force_arg`；L09 参考版只有
//! Flex 臂）+ 展开燃料（`UNIFY_FUEL`/`refuel`/`burn`）+ 值层应用/投影
//! （`vapp1`/`vapp_ok`/`project`/`val_mentions_lvl`）。条目按原文件行序跨三处
//! 拼装（σ 回收节内的 val_mentions_lvl 与燃料块 + metacontext 节尾的
//! project/vapp + "force" 节），逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;
use std::rc::Rc;

use super::parser::syntax::Icit;

use super::env::{CloCell, Env, EnvCons, PiCell, env_ext, env_len, env_nth};
use super::eval::{W, eval_iter};
use super::spine::{HK_FLEX, MetaEntry, Spine};
use super::subst::{SubstV, wrap_sub};
use super::syntax::{SumDataV, SumParamV, V, XCell, v_clo, v_clo_of, v_lvl, v_lvl_of, v_meta_of, v_pi, v_pi_of, v_spine_of, v_tag, v_xcell, v_xcell_of};

/// 值树里是否出现某层级（特化解的环守卫；参考版 `val_mentions_lvl`
/// 同款遍历面，但 **Flex 头的实参视为不透明**）：可达性探测用 `Raw::Hole`
/// 实例化构造子绑定器，fresh meta 的 pruning 会把整组绑定器（含被解变量
/// 本身）收进 spine——`l := succ (?m … l …)` 是"meta 应用到变量"的合法
/// 形，不是结构性自引用（旧 `update_cxt` 无 occurs，把 spine 算进来会把
/// 可达构造子误判不可达）。结构性自引用（`x := succ x`）仍由 Rigid/
/// SumCase 等臂捕获；更深的间接环由 force 的 fuel 兜底。
pub(super) fn val_mentions_lvl(spine: &Spine, defs: &[V], v: V, x: u32) -> bool {
    match v_tag(v) {
        0 => v_lvl_of(v) == x,
        2 => {
            let h = v_spine_of(v);
            let hd = spine.spine_head(h);
            // Flex 头的链 = 参考版 `Val::Flex(m, sp)` 的打包形态：**整条
            // 视为不透明**（实参不扫，见函数注释——探测的 fresh meta 会把
            // 绑定器（含被解变量）收进 spine，不是结构性自引用）
            if v_tag(hd) == 5 {
                return false;
            }
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
        // Flex 头（裸 meta 立即数）：实参视为不透明（见函数注释）
        5 => false,
        1 | 4 => false, // Lam/Pi 闭包跳过（参考版同）
        3 | 6 => false,
        7 => match v_xcell_of(v) {
            XCell::Lit(_) | XCell::Prim => false,
            // VSub：只扫解值自身的结构，**不扫 σ 的映射值**
            XCell::VSub { val, .. } => val_mentions_lvl(spine, defs, *val, x),
            XCell::Obj { val, .. } => val_mentions_lvl(spine, defs, *val, x),
            XCell::Sum { params, .. } => params.iter().any(|p| {
                val_mentions_lvl(spine, defs, p.val, x)
                    || val_mentions_lvl(spine, defs, p.ty, x)
            }),
            XCell::SumCase { typ, datas, .. } => {
                val_mentions_lvl(spine, defs, *typ, x)
                    || datas.iter().any(|d| val_mentions_lvl(spine, defs, d.val, x))
            }
            XCell::Match {
                scrutinee, env, ..
            } => {
                let mut hit = val_mentions_lvl(spine, defs, *scrutinee, x);
                if !hit {
                    let mut n = env.binds;
                    while let Some(e) = n {
                        if val_mentions_lvl(spine, defs, e.val, x) {
                            hit = true;
                            break;
                        }
                        n = e.next;
                    }
                }
                if !hit {
                    'outer: for k in 0..env.flat_len {
                        if val_mentions_lvl(
                            spine,
                            defs,
                            defs[(env.flat_base + env.flat_len - 1 - k) as usize],
                            x,
                        ) {
                            hit = true;
                            break 'outer;
                        }
                    }
                }
                hit
            }
        },
        _ => false,
    }
}
/// 精化传播的展开燃料（线程局部：每个测试/运行线程独立，与参考版
/// `Infer::unify_fuel` 的"每次运行新建"口径一致）。仅 frcs 的 lookup 命中
/// 点燃烧；外部入口（unify_catch / nf / check_pm / 模式编译）充值。
const UNIFY_FUEL: u32 = 4096;
thread_local! {
    static PM_FUEL: std::cell::Cell<u32> = const { std::cell::Cell::new(UNIFY_FUEL) };
}

pub(super) fn refuel() {
    PM_FUEL.with(|c| c.set(UNIFY_FUEL));
}

/// 燃料池是否已耗尽（探测失败侧的观察口：fuel 耗尽的失败是预算问题而非
/// 结构冲突——probe_accessible 尾部据此把失败按"可达"处理，保守地要求
/// 覆盖。L07 2026-09-18 评审修复 2 的同步移植）。
pub(super) fn fuel_exhausted() -> bool {
    PM_FUEL.with(|c| c.get() == 0)
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
/// 形态逐项对齐参考版 v_app：Rigid/Flex（裸或链）与卡住投影 Obj → spine
/// 压栈；字面量 / Prim / U / Π / LiteralType / Sum / SumCase / 卡住 match
/// → panic（"impossible apply"，参考版同款——两版同时不可达 / 同时
/// panic，判定一致）。
pub(super) fn vapp1<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    globals: &[V],
    f: V,
    a: V,
    i: Icit,
) -> V {
    if v_tag(f) == 1 {
        let c = v_clo_of(f);
        let env = env_ext(bump, c.env, a);
        eval_iter(bump, spine, work, vals, icits, defs, metas, globals, env, c.body)
    } else if v_tag(f) == 7 {
        match v_xcell_of(f) {
            XCell::Obj { .. } => spine.push(f, a, i),
            // 精化包裹的值先推开再分发（eval(App) 等不经 force 的调用点会
            // 把 VSub 头送进来——如臂上下文里 Var 引用了被解槽；force 顶层
            // 不再产出 VSub，递归必终止）
            XCell::VSub { .. } => {
                let ff = force(bump, spine, defs, metas, globals, f);
                return vapp1(
                    bump, spine, work, vals, icits, defs, metas, globals, ff, a, i,
                );
            }
            _ => panic!("impossible apply"),
        }
    } else if v_tag(f) == 3 || v_tag(f) == 4 || v_tag(f) == 6 {
        panic!("impossible apply")
    } else {
        spine.push(f, a, i)
    }
}

/// η 展开的可应用性守卫（参考版 `unification::v_applicable` 的快版对应，

/// L11 同款）：只有 `vapp1` 不会 panic 的形态能吃 η 新变量。tag 7 仅
/// `Obj` 可（`Sum`/`SumCase`/`Prim` → panic）；tag 3(U)/4(Pi)/6(Lit) 不可；
/// 其余（Rigid 0 / Clo 1 / 链 2 / Flex 5）可。防止 λ 值以类型/值身份流入
/// unify 的 η 臂时触发 `impossible apply`（守卫失败落后续臂判败，与参考
/// 版守卫后落 `_` → Err 同判定）。

#[inline]
pub(super) fn vapp_ok(v: V) -> bool {
    match v_tag(v) {
        3 | 4 | 6 => false,
        7 => matches!(v_xcell_of(v), XCell::Obj { .. }),
        _ => true,
    }
}
// force（迭代；L09 参考版只有 Flex 臂）
// --------------------------------------------------------------------------------

/// **force**：把值更新到 metacontext 的当前状态。参考版 `Infer::force`
/// 只有一个 Flex 臂（已解 → 展开应用；未解原样）——无 pm 精化读点展开、
/// 无 decl unfold、无 Match 重选、无投影归约。无燃料（meta 解由 occurs
/// check 保证无环，参考版同款裸递归）。
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
    globals: &[V],
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
                    // Rigid / Obj 头的链：卡住（参考版 force 无对应臂）。
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
                                bump, spine, &mut work, &mut vals, &mut icits, defs, metas,
                                globals, t, a, i,
                            );
                        }
                        v = t;
                    }
                }
            }
            // 显式替换（dpm-nbe `frc`）：把模式精化的解推进值的结构。入口
            // 不烧 fuel——真正的精化传播只发生在被解变量的读点（frcs 的
            // Rigid 臂 lookup 命中时烧 1）。fuel 耗尽的降级点也在该处。
            7 => {
                if let XCell::VSub { val, sub } = v_xcell_of(v) {
                    return frcs(bump, spine, defs, metas, globals, sub, *val);
                }
                return v;
            }
            _ => return v,
        }
    }
}

/// 把替换 `σ` 推进值 `v` 的结构（dpm-nbe `frcS`；参考版 `Infer::frcs`
/// 的快版对应）。槽位纪律：σ 对 spine / Sum/SumCase 槽只**包裹**，绝不
/// 推进物化——槽位引用是作用域事实，物化会破坏后续 solve 的 invert。
#[allow(clippy::too_many_arguments)]
fn frcs<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    globals: &[V],
    sub: &Rc<SubstV>,
    v0: V,
) -> V {
    if sub.is_empty() {
        return force(bump, spine, defs, metas, globals, v0);
    }
    let mut work: Vec<W<'a>> = Vec::new();
    let mut vals: Vec<V> = Vec::new();
    let mut icits: Vec<Icit> = Vec::new();
    match v_tag(v0) {
        // 内层先应用、外层后应用：组合后一次推进（frcS (subst sb sb') v）
        7 => match v_xcell_of(v0) {
            XCell::VSub { val, sub: sub2 } => {
                let composed = SubstV::compose(sub, sub2);
                frcs(bump, spine, defs, metas, globals, &composed, *val)
            }
            // 中性头单元：包裹后交回 force 重走既有臂。Sum/SumCase 槽位只
            // **包裹**不推进。
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
            XCell::Prim => force(bump, spine, defs, metas, globals, v0),
            XCell::Obj { val, name } => {
                let inner = frcs(bump, spine, defs, metas, globals, sub, *val);
                force(
                    bump,
                    spine,
                    defs,
                    metas,
                    globals,
                    v_xcell(bump.alloc(XCell::Obj { val: inner, name })),
                )
            }
            // scrutinee **推进**（分支重选需要解出的构造子值——L09 的分支
            // 重选发生在 eval 的 Tm::Match 臂：scrutinee 经 force 推开 σ 后
            // 是构造子值即选分支）；捕获 env 只包裹。
            XCell::Match {
                scrutinee, env, cases,
            } => {
                let s2 = frcs(bump, spine, defs, metas, globals, sub, *scrutinee);
                let env2 = frcs_env(bump, defs, sub, env);
                force(
                    bump,
                    spine,
                    defs,
                    metas,
                    globals,
                    v_xcell(bump.alloc(XCell::Match {
                        scrutinee: s2,
                        env: env2,
                        cases,
                    })),
                )
            }
        },
        // 裸 Rigid 的读点：lookup 命中（真正的精化传播）烧 1 fuel；fuel
        // 耗尽按未解处理（返回裸 rigid）。未命中零成本直通。
        0 => match SubstV::lookup_hit(bump, spine, defs, sub, v_lvl_of(v0)) {
            Some(hit) => {
                if !burn() {
                    return v0;
                }
                force(bump, spine, defs, metas, globals, hit)
            }
            None => v0,
        },
        // spine 链分派：Rigid 头 = 解析应用（对齐 dpm-nbe 的
        // `napp (lookupSub sb v) (frcS sb sp)`）；Flex/Obj 头 = 槽位只包裹，
        // 重建链后交回 force。
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
                        force(bump, spine, defs, metas, globals, hit)
                    }
                    None => v_lvl(x),
                };
                if !vapp_ok(head) {
                    return v0;
                }
                let mut args: Vec<(V, Icit)> = Vec::new();
                spine.collect_args(h, &mut args);
                for &(u, i) in args.iter().rev() {
                    head = vapp1(
                        bump, spine, &mut work, &mut vals, &mut icits, defs, metas, globals, head,
                        wrap_sub(bump, sub, u), i,
                    );
                }
                head
            } else {
                // **先查 tag 再解引用**：hd 可以是裸 rigid/meta 立即数
                let base = if v_tag(hd) == 7 {
                    match v_xcell_of(hd) {
                        XCell::Obj { val, name } => v_xcell(bump.alloc(XCell::Obj {
                            val: frcs(bump, spine, defs, metas, globals, sub, *val),
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
                force(bump, spine, defs, metas, globals, t)
            }
        }
        // 闭包 env 逐槽包裹；返回同型值，不再 force
        1 => {
            let c = v_clo_of(v0);
            v_clo(bump.alloc(CloCell {
                name: c.name,
                icit: c.icit,
                env: frcs_env(bump, defs, sub, &c.env),
                body: c.body,
            }))
        }
        4 => {
            let p = v_pi_of(v0);
            v_pi(bump.alloc(PiCell {
                name: p.name,
                icit: p.icit,
                dom: frcs(bump, spine, defs, metas, globals, sub, p.dom),
                // 平坦 defs 环境（定义期 cxt 环境）保持原样：其槽位是
                // `defs` 共享区的借用，转链会改变 de Bruijn 索引可达面
                // （参考版 List 表示无此问题；实测转链后 t 的 Π 体求值错位）。
                // 链式环境（subst_cxt 之后）逐槽包裹以传播精化。
                env: if p.env.binds.is_none() && p.env.flat_len > 0 {
                    p.env
                } else {
                    frcs_env(bump, defs, sub, &p.env)
                },
                body: p.body,
            }))
        }
        // 裸 flex：交回 force 走既有解链；U / LiteralType 原样
        5 => force(bump, spine, defs, metas, globals, v0),
        _ => v0,
    }
}

/// 闭包 env 逐槽包裹。包裹值不进 defs 平坦区，整体退化为 binder 链表示
/// （槽序与 `env_nth` 严格一致）。
fn frcs_env<'a>(bump: &'a Bump, defs: &[V], sub: &Rc<SubstV>, env: &Env<'a>) -> Env<'a> {
    if sub.is_empty() {
        return *env;
    }
    let n = env_len(*env);
    let mut e: Option<&'a EnvCons<'a>> = None;
    for i in (0..n).rev() {
        let v = env_nth(defs, *env, i);
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

/// 合一器**参数视角**的 WHNF（参考版 `Infer::force_arg` 同款）：不推开
/// VSub 精化包裹、不做 Match 重选。逐层解包 VSub 后：裸 rigid 返回裸值；
/// 带实参的 rigid 链 / 卡住 match 返回**原值**（包裹原样保留）；其余形态
/// 全量 force。
pub(super) fn force_arg<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    globals: &[V],
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
        _ => force(bump, spine, defs, metas, globals, v),
    }
}
