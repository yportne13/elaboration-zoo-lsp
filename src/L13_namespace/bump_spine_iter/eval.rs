//! eval：双栈迭代 eval（`W`/`eval_iter`）+ 运行时分支选择（`eval_aux`，
//! 值层首匹配、SumCase 按构造子 index 制 + 原生 Nat O(1) 分派）。原
//! bump_spine_iter.rs 的 "运行时分支选择" 与 "eval" 两节，逐行搬运
//! （2026-09-23 拆分）；同轮去冗余（perf-l13-round-2026-09-22 §3.2.3）：
//! 子模式递归走单臂助手 `eval_aux_one`（不再每步 bump 构造 1 元臂表 +
//! 深克隆子模式）。大表 Con 臂索引（同节候选）经 A/B 证伪回退：逐调用
//! 重建索引本身要全表一遍触达，宽表超 L2 后反劣化（wide_enum k=11
//! +9%），且小收益不稳（k=9 两窗口 -8%/-0.7%）。

use bumpalo::Bump;
use std::cell::RefCell;

use super::parser::syntax::Icit;

use super::env::{env_ext, env_nth, EMPTY_ENV, CloCell, Env, PiCell};
use super::force::{force, vapp1};
use super::prim::{def_needs_replay, nat_step_value, Decls, Mutable};
use super::spine::{meta_val_of, MetaEntry, Spine};
use super::syntax::{
    PrCons, SumDataT, SumDataV, SumParamT, SumParamV, Tm, V, XCell, v_clo, v_clo_of,
    v_lit_ty, v_pi, v_tag, v_u, v_xcell, v_xcell_of,
};
use super::PatternDetail;


// 运行时分支选择（值层首匹配，无合一；L13 参考版 Compiler::eval_aux 同款：
// index 制 + 原生 Nat O(1) 分派）
// --------------------------------------------------------------------------------

/// 构造子头分类：Some((index, datas))；`Nat(k>0)` 的参数表按需 bump 构造
/// （`eval_aux` / [`eval_aux_one`] 共用）。
fn classify_head<'a>(bump: &'a Bump, v: V) -> Option<(u32, &'a [SumDataV<'a>])> {
    if v_tag(v) != 7 {
        return None;
    }
    match v_xcell_of(v) {
        XCell::SumCase { index, datas, .. } => Some((*index, datas)),
        XCell::Nat(k) if *k == 0 => Some((0, &[])),
        XCell::Nat(k) => {
            let inner = v_xcell(bump.alloc(XCell::Nat(k - 1)));
            let ds: &'a [SumDataV<'a>] =
                bump.alloc([SumDataV { name: "n", val: inner, icit: Icit::Expl }]);
            Some((1, ds))
        }
        _ => None,
    }
}

/// eval_aux 系的头部纪律：构造子头（SumCase / 原生 Nat）**不 force 直接
/// 分派**（深链 O(n²) 规避）；非构造子头先 force 再分类，仍非构造子 →
/// `u32::MAX`。force 的副作用（spine WHNF 回填等）无论后续臂形如何都保
/// 留——与参考版逐句一致。
#[allow(clippy::too_many_arguments)]
fn classify_force_head<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decl: &Decls<'a>,
    mutable: &RefCell<Mutable>,
    head: V,
) -> (u32, &'a [SumDataV<'a>]) {
    match classify_head(bump, head) {
        Some(x) => x,
        None => {
            let h2 = force(bump, spine, defs, metas, decl, mutable, head);
            classify_head(bump, h2).unwrap_or((u32::MAX, &[]))
        }
    }
}

/// 按模式首匹配（参考版 `Compiler::eval_aux` 逐句）：
/// - 构造子头（SumCase / 原生 Nat）**不 force 直接分派**（深链 O(n²) 规
///   避）；非构造子头先 force 再分类，仍非构造子 → index = `u32::MAX`。
/// - `Nat 0` → index 0（zero，无字段）；`Nat k>0` → index 1（succ，字段绑
///   `Nat(k-1)`——不建一元链）。
/// - 第一遍：Con 模式 index 相等 → datas 与子模式 zip（zip 截断）逐个递
///   归（**单臂助手** [`eval_aux_one`]，不再构造 1 元臂表，env 累积——
///   head 本身不 prepend）；子模式失配 → 试下臂。头 `u32::MAX`（非构造
///   子）直接跳过第一遍——Con 臂的 `constr_idx` 是 enum 内 case 序号，
///   恒 ≠ `u32::MAX`（参考版的 `u32::MAX` 精确匹假阳，见 L13-code-review
///   N7，实际不可达）。
/// - 第二遍（兜底）：首个 Any/Bind 模式命中，**原始 head**（非 force 后的
///   值）prepend 进 env——参考版 `cxt.prepend(heads.clone())` 同款。
#[allow(clippy::too_many_arguments)]
pub(super) fn eval_aux<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decl: &Decls<'a>,
    mutable: &RefCell<Mutable>,
    head: V,
    env: Env<'a>,
    cases: &'a [(PatternDetail, &'a Tm<'a>)],
) -> Option<(&'a Tm<'a>, Env<'a>)> {
    let (index, datas): (u32, &[SumDataV<'a>]) =
        classify_force_head(bump, spine, defs, metas, decl, mutable, head);
    // 第一遍：Con(index) 相等（子模式 zip 失配 → 试下一臂）。头非构造子
    // （u32::MAX）直接跳过——Con 臂的 constr_idx 恒 ≠ u32::MAX（见上）。
    if index != u32::MAX {
        for (pat, body) in cases.iter() {
            if let PatternDetail::Con(constr_idx, _, subs, _) = pat {
                if *constr_idx == index {
                    if let Some(hit) = try_con_arm(
                        bump, spine, defs, metas, decl, mutable, datas, env, subs, *body,
                    ) {
                        return Some(hit);
                    }
                }
            }
        }
    }
    // 第二遍：首个 Any/Bind（绑定原始 head）
    for (pat, body) in cases.iter() {
        match pat {
            PatternDetail::Any(..) | PatternDetail::Bind(_) => {
                return Some((body, env_ext(bump, env, head)))
            }
            PatternDetail::Con(..) => {}
        }
    }
    None
}

/// 单个 Con 臂的尝试：datas（头部字段值）与臂子模式 zip（zip 截断）逐个
/// 递归（每步走单臂助手 [`eval_aux_one`]，env 累积——head 本身不
/// prepend）；子模式失配 → None（= 试下一臂）。
#[allow(clippy::too_many_arguments)]
fn try_con_arm<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decl: &Decls<'a>,
    mutable: &RefCell<Mutable>,
    datas: &[SumDataV<'a>],
    env: Env<'a>,
    subs: &[PatternDetail],
    body: &'a Tm<'a>,
) -> Option<(&'a Tm<'a>, Env<'a>)> {
    let mut cur_body = body;
    let mut cur_env = env;
    for (d, sub) in datas.iter().zip(subs.iter()) {
        match eval_aux_one(bump, spine, defs, metas, decl, mutable, d.val, cur_env, sub, cur_body) {
            Some((b, e)) => {
                cur_body = b;
                cur_env = e;
            }
            None => return None,
        }
    }
    Some((cur_body, cur_env))
}

/// 单臂递归（`eval_aux` 递归"每步单臂表"的专用形态）：`pat` 命中 `head`
/// 时返回 (体, 扩展 env)，None = 试下一臂。语义与把
/// `[(pat.clone(), body)]` 喂给 [`eval_aux`] **逐点一致**，但省掉每
/// (字段, 子模式) 一次的臂表 bump 分配 + `PatternDetail` 深克隆：
/// - Con：同款头部纪律（classify/force 副作用保留），index 相等 →
///   datas 与子模式 zip 递归（失配 → None）；非构造子头（`u32::MAX`）
///   恒 miss。
/// - Any/Bind：命中，绑**原始 head**（非 force 后的值）。
#[allow(clippy::too_many_arguments)]
fn eval_aux_one<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decl: &Decls<'a>,
    mutable: &RefCell<Mutable>,
    head: V,
    env: Env<'a>,
    pat: &PatternDetail,
    body: &'a Tm<'a>,
) -> Option<(&'a Tm<'a>, Env<'a>)> {
    // 头部纪律与 eval_aux 相同：Any/Bind 下 force 副作用也保留（1 元
    // cases 递归同样会跑 classify/force）
    let (index, datas) = classify_force_head(bump, spine, defs, metas, decl, mutable, head);
    match pat {
        PatternDetail::Any(..) | PatternDetail::Bind(_) => Some((body, env_ext(bump, env, head))),
        PatternDetail::Con(constr_idx, _, subs, _) => {
            if *constr_idx != index {
                return None;
            }
            try_con_arm(bump, spine, defs, metas, decl, mutable, datas, env, subs, body)
        }
    }
}

// eval（双栈迭代 + 右链快速路径 + AppPruning 实参应用 + L09 变体）
// --------------------------------------------------------------------------------

/// eval 的 work 栈条目。
pub(super) enum W<'a> {
    Tm(&'a Tm<'a>, Env<'a>),
    /// 应用（icit 来自 `Tm::App`）：vals 顶两个（先函数后实参）。
    Apply(Icit),
    /// vals 顶上是实参；函数值已知是闭包，直接 β（icit 无关）。
    ApplyKnown(V),
    /// vals 顶上是 base 值，其下 `k` 个是待应用的链头（内层最上；每个链头
    /// 的 icit 在 `icits` 侧栈平行压弹）。
    ChainWrap(u32),
    /// vals 顶是 let 绑定的值：弹出压进环境，继续求值体。
    LetBody(&'a Tm<'a>, Env<'a>),
    /// vals 顶是 Π 定义域值：弹出配余定义域闭包，压 Π 值。
    PiBody(&'a str, Icit, &'a Tm<'a>, Env<'a>),
    /// vals 顶是 `vAppPruning` 的当前值；沿 (env, pr) 平行走完剩余槽位
    /// （外层先应用，icit 取自掩码；`None` 槽跳过）。
    AppPrun(Env<'a>, Option<&'a PrCons<'a>>),
    /// vals 顶是 `vAppPruning` 的当前值；本步把 `arg` 以 `icit` 应用上去。
    AppPrunOne(V, Icit),
    /// vals 顶是投影接收者的值：构造子头（Sum/SumCase）不 force 直接投影
    /// （miss panic，参考版 unwrap 同款；SumCase 的 typ 非 Sum 时降级卡住
    /// Obj）；其余头先 force，仍不可投影 → 卡住 Obj。
    ObjSel(&'a str),
    /// vals 顶自底向上是 (v0,t0,...,v_{n-1},t_{n-1})（求值序）：装配 Sum。
    SumAsm {
        name: &'a str,
        params: &'a [SumParamT<'a>],
        cases: &'a [&'a str],
        is_trait: bool,
    },
    /// vals 顶自底向上是 (typ, d0..d_{nd-1})：装配 SumCase（含原生 Nat 折叠
    /// ——`nat_step_value`）。
    SumCaseAsm {
        index: u32,
        datas: &'a [SumDataT<'a>],
        is_trait: bool,
    },
    /// vals 顶是 Call/OpCall 体的值：**卡 Match 才包 `Val::Call`**（实参项在
    /// 捕获 env 下求值；参考版 eval 的 Frame::Call 同款），否则原样。
    CallAsm {
        name: &'a str,
        args: &'a [(&'a Tm<'a>, Icit)],
        env: Env<'a>,
    },
    /// vals 顶是 scrutinee 的值：构造子头（SumCase/Nat）不 force 直接
    /// eval_aux 选分支；其余先 force；无臂命中 / 非构造子头 → 卡住 Match。
    MatchSel {
        cases: &'a [(PatternDetail, &'a Tm<'a>)],
        env: Env<'a>,
    },
}

/// 双栈迭代 eval（L06 版 + L11 变体：Decl 表查名、带类型的 Prim 五路
/// 分派、投影的 panic 语义、match 的编译期选择与卡住停等）。
#[allow(clippy::too_many_arguments)]
pub(super) fn eval_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decl: &Decls<'a>,
    mutable: &RefCell<Mutable>,
    env0: Env<'a>,
    tm0: &'a Tm<'a>,
) -> V {
    work.clear();
    vals.clear();
    icits.clear();
    work.push(W::Tm(tm0, env0));
    while let Some(w) = work.pop() {
        match w {
            W::Tm(Tm::Var(i), env) => {
                vals.push(env_nth(defs, env, *i));
            }
            // 全局声明：decl 表查名。**replay 路径**：无参 def 的 body 含全局
            // 副作用（`def_needs_replay`：REPLAY_GLOBAL_OPS 名单，builtin 排除）
            // 时清空 env 重放 body（参考版 eval 的 Tm::Decl 臂同款——副作用
            // 对当前 mutable 状态生效）；否则返回登记值。未登记 → 卡
            // `Decl(name, 空 spine)`（递归自引用存根 / 逃逸形态）。
            W::Tm(Tm::Decl(x), _) => match decl.get(*x) {
                Some(e) => {
                    if e.prim.is_none() && def_needs_replay(mutable, decl, x) {
                        work.push(W::Tm(e.tm, EMPTY_ENV));
                    } else {
                        vals.push(e.val);
                    }
                }
                None => vals.push(v_xcell(bump.alloc(XCell::Decl { name: x }))),
            },
            W::Tm(Tm::Lam(name, icit, body), env) => {
                let c = bump.alloc(CloCell {
                    name,
                    icit: *icit,
                    env,
                    body,
                });
                vals.push(v_clo(c));
            }
            W::Tm(Tm::U(l), _) => vals.push(v_u(*l)),
            W::Tm(Tm::LiteralType, _) => vals.push(v_lit_ty()),
            W::Tm(Tm::LiteralIntro(s), _) => vals.push(v_xcell(bump.alloc(XCell::Lit(s)))),
            // Call（含参考版 OpCall 的 eval 行为——两节点 eval 完全一致）：
            // 先求体，体值卡 Match 才在 CallAsm 里求实参并包 `Val::Call`
            // （参考版 eval 的 Frame::Call）
            W::Tm(Tm::Call(name, args, body), env) => {
                work.push(W::CallAsm { name, args, env });
                work.push(W::Tm(body, env));
            }
            W::Tm(Tm::Pi(name, icit, dom, cod), env) => {
                work.push(W::PiBody(name, *icit, cod, env));
                work.push(W::Tm(dom, env));
            }
            W::Tm(Tm::Let(_, _, t, u), env) => {
                work.push(W::LetBody(u, env));
                work.push(W::Tm(t, env));
            }
            W::Tm(Tm::Meta(m), _) => vals.push(meta_val_of(metas, *m)),
            W::Tm(Tm::AppPruning(head, pr), env) => {
                work.push(W::AppPrun(env, *pr));
                work.push(W::Tm(head, env));
            }
            // 投影：构造子头（Sum/SumCase）不 force 直接投影（miss panic）；
            // 其余头先 force，仍不可投影一律卡成 Obj（详见 W::ObjSel）。
            W::Tm(Tm::Obj(h, name), env) => {
                work.push(W::ObjSel(name));
                work.push(W::Tm(h, env));
            }
            // enum 本体：逐参数求值（值 + 类型）后装配
            W::Tm(Tm::Sum(name, params, cases, is_trait), env) => {
                work.push(W::SumAsm { name, params, cases, is_trait: *is_trait });
                for p in params.iter().rev() {
                    work.push(W::Tm(p.ty, env));
                    work.push(W::Tm(p.val, env));
                }
            }
            W::Tm(
                Tm::SumCase {
                    typ,
                    index,
                    datas,
                    is_trait,
                },
                env,
            ) => {
                work.push(W::SumCaseAsm { index: *index, datas, is_trait: *is_trait });
                for d in datas.iter().rev() {
                    work.push(W::Tm(d.val, env));
                }
                work.push(W::Tm(typ, env));
            }
            // match：求值 scrutinee → force → 选分支 / 卡住（参考版 eval 的
            // Tm::Match 臂：SumCase + eval_aux 命中给分支体（**None 即
            // panic**）；其它 neutral 卡 Match，无 pending）
            W::Tm(Tm::Match(s, cases), env) => {
                work.push(W::MatchSel { cases, env });
                work.push(W::Tm(s, env));
            }
            W::Tm(app @ Tm::App(..), env) => {
                // 右链下钻：头为非闭包变量时头值直接进 vals（icit 进侧栈）
                let mut tm = app;
                let mut heads: u32 = 0;
                loop {
                    let (f, a, i) = match tm {
                        Tm::App(f, a, i) => (f, a, i),
                        base => {
                            if heads > 0 {
                                work.push(W::ChainWrap(heads));
                            }
                            work.push(W::Tm(base, env));
                            break;
                        }
                    };
                    let i = *i;
                    match f {
                        Tm::Var(ix) => {
                            let vf = env_nth(defs, env, *ix);
                            if v_tag(vf) == 1 {
                                // β 岔路：函数值已在手上（闭包），ApplyKnown
                                // 直接管 β（icit 无关）；heads>0 时 ChainWrap
                                // 照旧收拢
                                if heads > 0 {
                                    work.push(W::ChainWrap(heads));
                                }
                                work.push(W::ApplyKnown(vf));
                                work.push(W::Tm(a, env));
                                break;
                            }
                            vals.push(vf);
                            icits.push(i);
                            heads += 1;
                            tm = a;
                        }
                        _ => {
                            // 复合函数头：通用三推（同样先收已收的头）
                            if heads > 0 {
                                work.push(W::ChainWrap(heads));
                            }
                            work.push(W::Apply(i));
                            work.push(W::Tm(a, env));
                            work.push(W::Tm(f, env));
                            break;
                        }
                    }
                }
            }
            W::Apply(i) => {
                let va = vals.pop().expect("eval 栈：Apply 缺实参");
                let vf = vals.pop().expect("eval 栈：Apply 缺函数");
                if v_tag(vf) == 1 {
                    // β 归约是尾调用：直接推入体，继续循环
                    let c = v_clo_of(vf);
                    let env = env_ext(bump, c.env, va);
                    work.push(W::Tm(c.body, env));
                } else {
                    let r = vapp1(
                        bump, spine, work, vals, icits, defs, metas, decl, mutable, true, vf, va, i,
                    );
                    vals.push(r);
                }
            }
            W::ApplyKnown(vf) => {
                let va = vals.pop().expect("eval 栈：ApplyKnown 缺实参");
                let c = v_clo_of(vf);
                let env = env_ext(bump, c.env, va);
                work.push(W::Tm(c.body, env));
            }
            W::ChainWrap(k) => {
                let mut v = vals.pop().expect("eval 栈：ChainWrap 缺 base");
                for _ in 0..k {
                    let vf = vals.pop().expect("eval 栈：ChainWrap 缺链头");
                    let i = icits.pop().expect("eval 栈：ChainWrap 缺 icit");
v = vapp1(
                        bump, spine, work, vals, icits, defs, metas, decl, mutable, true, vf, v, i,
                    );
                }
                vals.push(v);
            }
            W::LetBody(u, env) => {
                let vt = vals.pop().expect("eval 栈：LetBody 缺绑定值");
                work.push(W::Tm(u, env_ext(bump, env, vt)));
            }
            W::PiBody(name, icit, cod, env) => {
                let dom = vals.pop().expect("eval 栈：PiBody 缺定义域");
                let cell = bump.alloc(PiCell {
                    name,
                    icit,
                    dom,
                    env,
                    body: cod,
                });
                vals.push(v_pi(cell));
            }
            W::AppPrun(env, bds) => match bds {
                None => {
                    // 与 reference 的 (None, None) 对齐：掩码先行耗尽
                    debug_assert!(env.binds.is_none() && env.flat_len == 0);
                }
                Some(b) if env.binds.is_none() && b.slot.is_none() => {
                    // O(1) 跳段：binds 耗尽后剩余链只剩 define 槽。
                    assert!(env.flat_len >= b.none_run);
                    work.push(W::AppPrun(
                        Env {
                            flat_len: env.flat_len - b.none_run,
                            ..env
                        },
                        b.after_run,
                    ));
                }
                Some(b) => {
                    // 内层绑定 = 链头；链耗尽后走平坦 def 区域末端。先跑
                    // 余下槽位（外层），再应用本槽（内层最后应用）
                    let (arg, rest) = if let Some(e) = env.binds {
                        (
                            b.slot.map(|_| e.val),
                            Env {
                                binds: e.next,
                                ..env
                            },
                        )
                    } else if env.flat_len > 0 {
                        let v = defs[(env.flat_base + env.flat_len - 1) as usize];
                        (
                            b.slot.map(|_| v),
                            Env {
                                flat_len: env.flat_len - 1,
                                ..env
                            },
                        )
                    } else {
                        panic!("impossible") // env 与 pr 错位
                    };
                    match (arg, b.slot) {
                        (Some(a), Some(i)) => work.push(W::AppPrunOne(a, i)),
                        (None, Some(_)) => panic!("impossible"), // env 短于 pr
                        _ => {}
                    }
                    work.push(W::AppPrun(rest, b.next));
                }
            },
            W::AppPrunOne(arg, i) => {
                let v = vals.pop().expect("eval 栈：AppPrunOne 缺值");
                if v_tag(v) == 1 {
                    let c = v_clo_of(v);
                    let env = env_ext(bump, c.env, arg);
                    work.push(W::Tm(c.body, env));
                } else {
                    let r = vapp1(
                        bump, spine, work, vals, icits, defs, metas, decl, mutable, true, v, arg, i,
                    );
                    vals.push(r);
                }
            }
            W::ObjSel(name) => {
                let v = vals.pop().expect("eval 栈：ObjSel 缺接收者");
                // L13：构造子头（Sum/SumCase）不 force 直接投影；其余头先
                // force（参考版 Frame::Obj）。SumCase 的 typ 非 Sum（meta/
                // rigid 头）→ 降级卡住 Obj（eval 永不崩）；其余不可投影形
                // 态同样卡住 Obj。
                let is_ctor = v_tag(v) == 7
                    && matches!(
                        v_xcell_of(v),
                        XCell::Sum { .. } | XCell::SumCase { .. }
                    );
                let a = if is_ctor { v } else { force(bump, spine, defs, metas, decl, mutable, v) };
                match v_tag(a) {
                    7 => match v_xcell_of(a) {
                        XCell::Sum { params, .. } => {
                            match params.iter().find(|p| p.name == name) {
                                Some(p) => vals.push(p.val),
                                // 参考 unwrap：字段必在
                                None => panic!("impossible"),
                            }
                        }
                        XCell::SumCase { typ, datas, .. } => {
                            match v_xcell_of(*typ) {
                                XCell::Sum { params, .. } => {
                                    match params
                                        .iter()
                                        .find(|p| p.name == name)
                                        .map(|p| p.val)
                                        .or_else(|| {
                                            datas.iter().find(|d| d.name == name).map(|d| d.val)
                                        })
                                    {
                                        Some(p) => vals.push(p),
                                        None => panic!("impossible"),
                                    }
                                }
                                // typ 非 Sum：无字段表可投影 → 卡住 Obj
                                _ => vals.push(
                                    v_xcell(bump.alloc(XCell::Obj { val: a, name })),
                                ),
                            }
                        }
                        _ => vals.push(v_xcell(bump.alloc(XCell::Obj { val: a, name }))),
                    },
                    // Rigid（裸或链）/ Flex / 卡住 match / 字面量… → 卡住 Obj
                    _ => vals.push(v_xcell(bump.alloc(XCell::Obj { val: a, name }))),
                }
            }
            W::SumAsm { name, params, cases, is_trait } => {
                // vals 槽序 = v0, t0, v1, t1, ...（先压者在底）→ pop 序是
                // t_{n-1}, v_{n-1}, ...：按 params 逆序逐槽收进 ps，再整体
                // 反转回自然序——单缓冲，省掉 items 中转 + 二次下标拷贝
                let mut ps: Vec<SumParamV<'_>> = Vec::with_capacity(params.len());
                for p in params.iter().rev() {
                    let ty = vals.pop().expect("eval 栈：SumAsm 缺参数");
                    let val = vals.pop().expect("eval 栈：SumAsm 缺参数");
                    ps.push(SumParamV {
                        name: p.name,
                        val,
                        ty,
                        icit: p.icit,
                    });
                }
                ps.reverse();
                vals.push(v_xcell(bump.alloc(XCell::Sum {
                    name,
                    params: bump.alloc_slice_fill_iter(ps),
                    cases,
                    is_trait,
                })));
            }
            W::SumCaseAsm { index, datas, is_trait } => {
                // datas 字段在 vals 栈顶（typ 先压在底）：逆序 pop 落槽后
                // 反转，typ 最后 pop
                let mut ds: Vec<SumDataV<'_>> = Vec::with_capacity(datas.len());
                for d in datas.iter().rev() {
                    let val = vals.pop().expect("eval 栈：SumCaseAsm 缺字段");
                    ds.push(SumDataV {
                        name: d.name,
                        val,
                        icit: d.icit,
                    });
                }
                ds.reverse();
                let typ = vals.pop().expect("eval 栈：SumCaseAsm 缺 typ");
                // 原生 Nat 折叠：全具体构造步直接建 Nat(k)（`succ (Nat k)` →
                // `Nat (k+1)`、`zero` → `Nat 0`）；部分卡住链保持 SumCase
                match nat_step_value(typ, index, &ds) {
                    Some(n) => vals.push(v_xcell(bump.alloc(XCell::Nat(n)))),
                    None => vals.push(v_xcell(bump.alloc(XCell::SumCase {
                        typ,
                        index,
                        datas: bump.alloc_slice_fill_iter(ds),
                        is_trait,
                    }))),
                }
            }
            W::CallAsm { name, args, env } => {
                let body = vals.pop().expect("eval 栈：CallAsm 缺体值");
                if v_tag(body) == 7 && matches!(v_xcell_of(body), XCell::Match { .. }) {
                    // 实参项在捕获 env 下求值（独立草稿栈——eval_iter 入口
                    // 清空 work/vals/icits）
                    let mut argv: Vec<(V, Icit)> = Vec::with_capacity(args.len());
                    let mut w2: Vec<W<'a>> = Vec::new();
                    let mut v2: Vec<V> = Vec::new();
                    let mut i2: Vec<Icit> = Vec::new();
                    for (t, i) in args.iter() {
                        let av = eval_iter(
                            bump, spine, &mut w2, &mut v2, &mut i2, defs, metas, decl, mutable,
                            env, t,
                        );
                        argv.push((av, *i));
                    }
                    vals.push(v_xcell(bump.alloc(XCell::Call {
                        name,
                        args: bump.alloc_slice_copy(&argv),
                        body,
                    })));
                } else {
                    vals.push(body);
                }
            }
            W::MatchSel { cases, env } => {
                let sv = vals.pop().expect("eval 栈：MatchSel 缺 scrutinee");
                // L13：构造子头（SumCase / Nat）不 force 直接分派（深链
                // O(n²) 规避）；其余头先 force；无臂命中 / 非构造子头 →
                // 卡住 Match（无 pending）
                let is_ctor = v_tag(sv) == 7
                    && matches!(
                        v_xcell_of(sv),
                        XCell::SumCase { .. } | XCell::Nat(_)
                    );
                let s2 = if is_ctor { sv } else { force(bump, spine, defs, metas, decl, mutable, sv) };
                let dispatched = v_tag(s2) == 7
                    && matches!(
                        v_xcell_of(s2),
                        XCell::SumCase { .. } | XCell::Nat(_)
                    );
                if dispatched {
                    match eval_aux(bump, spine, defs, metas, decl, mutable, s2, env, cases) {
                        Some((body_tm, env2)) => {
                            // 分支选中：体在本 eval 循环里尾推
                            work.push(W::Tm(body_tm, env2));
                        }
                        None => vals.push(v_xcell(bump.alloc(XCell::Match {
                            scrutinee: s2,
                            env,
                            cases,
                        }))),
                    }
                } else {
                    vals.push(v_xcell(bump.alloc(XCell::Match {
                        scrutinee: s2,
                        env,
                        cases,
                    })));
                }
            }
        }
    }
    vals.pop().expect("eval 必须恰有一个根值")
}
