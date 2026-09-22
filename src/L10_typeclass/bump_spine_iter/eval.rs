//! eval：运行时分支选择（`eval_aux`/`eval_aux_case`，值层首匹配）与双栈
//! 迭代 eval（`W`/`eval_iter`：global 大下标、无名 Prim 的 env 双槽拼接、
//! 投影的 panic 语义、match 的编译期选择与卡住停等）。原 bump_spine_iter.rs
//! 的 "运行时分支选择" + "eval" 两节，逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;

use super::parser::syntax::Icit;
use super::PatternDetail;

use super::env::{env_ext, env_nth, CloCell, Env, PiCell};
use super::force::{force, vapp1};
use super::machine::GLOBAL_BASE;
use super::spine::{lit_of, meta_val_of, MetaEntry, Spine};
use super::syntax::{
    PrCons, SumDataT, SumDataV, SumParamT, SumParamV, Tm, V, XCell, v_clo, v_clo_of,
    v_lit_ty, v_pi, v_tag, v_u, v_xcell, v_xcell_of,
};

// 运行时分支选择（值层首匹配，无合一；L09 参考版 Compiler::eval_aux 同款）
// --------------------------------------------------------------------------------

/// 按模式首匹配。参考版语义逐句对齐：
/// - 入口 force(head)；force 后非 SumCase → 任何 Con 模式都按"不在类型构造
///   子表里"的变量模式命中（`$unknown$` + 空表）。
/// - force 后是 SumCase：typ 必须 force 成 Sum（**否则 panic**——参考版
///   `panic!("by now only can match a sum type")`）；Con 模式名不在 Sum 的
///   cases 里 → 按变量模式命中（prepend head）；名 == case_name → datas 与
///   子模式 zip（**zip 截断**）逐个递归（每步单臂表，env 累积——**head 本身
///   不 prepend**，参考版 Con 臂从 cxt 起步）；同名异构造子 → 试下一分支。
pub(super) fn eval_aux<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    globals: &[V],
    head: V,
    env: Env<'a>,
    cases: &'a [(PatternDetail, &'a Tm<'a>)],
) -> Option<(&'a Tm<'a>, Env<'a>)> {
    let head = force(bump, spine, defs, metas, globals, head);
    let (case_name, datas, ctor_names): (&str, &[SumDataV<'a>], &[&str]) = if v_tag(head) == 7 {
        match v_xcell_of(head) {
            XCell::SumCase { typ, case_name, datas, .. } => {
                let cases_list = match v_xcell_of(*typ) {
                    XCell::Sum { cases, .. } => *cases,
                    // 参考 panic：typ 不是 Sum（中性 global 下的重求值可达）
                    _ => panic!("by now only can match a sum type"),
                };
                (case_name, *datas, cases_list)
            }
            _ => ("$unknown$", &[], &[]),
        }
    } else {
        ("$unknown$", &[], &[])
    };
    for (pat, body) in cases.iter() {
        if let Some(r) = eval_aux_case(
            bump, spine, defs, metas, globals, head, case_name, datas, ctor_names, env, pat, *body,
        ) {
            return Some(r);
        }
    }
    None
}

/// 单 (模式, 分支体) 的匹配（`eval_aux` 的内层；返回 None = 试下一分支）。
/// 子模式的下钻走**完整 eval_aux**（对子值重新派生 case 信息——参考版
/// 递归同款，`[(pat.clone(), body)]` 单臂表也照克隆）。
#[allow(clippy::too_many_arguments)]
fn eval_aux_case<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    globals: &[V],
    head: V,
    case_name: &str,
    datas: &[SumDataV<'a>],
    ctor_names: &[&str],
    env: Env<'a>,
    pat: &PatternDetail,
    body: &'a Tm<'a>,
) -> Option<(&'a Tm<'a>, Env<'a>)> {
    match pat {
        PatternDetail::Any(_) | PatternDetail::Bind(_) => {
            Some((body, env_ext(bump, env, head)))
        }
        PatternDetail::Con(name, subs) => {
            let in_type = ctor_names.iter().any(|c| *c == name.data);
            if !in_type {
                // 不是该类型的构造子名 → 变量模式（保守兼容；参考版首臂）
                Some((body, env_ext(bump, env, head)))
            } else if case_name == name.data {
                // datas 与子模式按序 zip（zip 截断；参考版 try_fold 同款：
                // 每步单臂完整 eval_aux，body 原样传递，env 累积——head 不
                // prepend）
                let mut cur_body = body;
                let mut cur_env = env;
                for (d, sub) in datas.iter().zip(subs.iter()) {
                    let arms1: &'a [(PatternDetail, &'a Tm<'a>)] =
                        bump.alloc([(sub.clone(), cur_body)]);
                    match eval_aux(
                        bump, spine, defs, metas, globals, d.val, cur_env, arms1,
                    ) {
                        Some((b, e)) => {
                            cur_body = b;
                            cur_env = e;
                        }
                        None => return None, // 子模式失配：试下一分支
                    }
                }
                Some((cur_body, cur_env))
            } else {
                None // 同类型不同构造子 → 试下一分支
            }
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
    /// vals 顶是投影接收者的值（先 force）：Sum/SumCase 命中给投影值
    /// （**miss panic**，参考版 unwrap 同款）；其余形态一律卡成 Obj
    ///（参考版 `_` 臂——L09 才是仅 Rigid 卡、其余 panic）。
    ObjSel(&'a str),
    /// vals 顶自底向上是 (v0,t0,...,v_{n-1},t_{n-1})（求值序）：装配 Sum。
    SumAsm {
        name: &'a str,
        params: &'a [SumParamT<'a>],
        cases: &'a [&'a str],
        is_trait: bool,
    },
    /// vals 顶自底向上是 (typ, d0..d_{nd-1})：装配 SumCase。
    SumCaseAsm {
        case_name: &'a str,
        datas: &'a [SumDataT<'a>],
        is_trait: bool,
    },
    /// vals 顶是 scrutinee 的值：force 后是 SumCase → eval_aux 选分支
    /// （**None 即 panic**，参考版 unwrap 同款）；否则卡成 Match（无
    /// pending）。
    MatchSel {
        cases: &'a [(PatternDetail, &'a Tm<'a>)],
        env: Env<'a>,
    },
}

/// 双栈迭代 eval（L06 版 + L09 变体：global 大下标、无名 Prim 的 env 双槽
/// 拼接、投影的 panic 语义、match 的编译期选择与卡住停等）。
#[allow(clippy::too_many_arguments)]
pub(super) fn eval_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    globals: &[V],
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
                // 越过哨兵的下标查 global 表（参考版 eval 的 Var 臂：env 走
                // 完才落 global——env 槽数远小于哨兵，次序无观察面）
                if *i >= GLOBAL_BASE {
                    vals.push(globals[(*i - GLOBAL_BASE) as usize]);
                } else {
                    vals.push(env_nth(defs, env, *i));
                }
            }
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
            // builtin 体：env 前两槽全为字面量 → 拼接；否则卡住 `Prim`（无
            // spine——v_app 对它 panic，永无 Prim 头的链）。env 不足两槽时
            // env_nth 越界 panic（参考版 unwrap 同款崩溃）。
            W::Tm(Tm::Prim, env) => {
                // 槽值可能被精化 σ 包裹（subst_cxt 后的臂上下文）——先推开
                // 再判字面量拼接，对齐旧 refresh 重求值后的槽值形态
                let b = force(bump, spine, defs, metas, globals, env_nth(defs, env, 0));
                let a = force(bump, spine, defs, metas, globals, env_nth(defs, env, 1));
                match (lit_of(a), lit_of(b)) {
                    (Some(a), Some(b)) => {
                        let len = a.len() + b.len();
                        let ptr = bump
                            .alloc_layout(std::alloc::Layout::from_size_align(len, 1).unwrap())
                            .as_ptr();
                        // SAFETY: a/b 都是 &str（合法 UTF-8）；两段完整序列按
                        // 字节拼接仍是合法 UTF-8，不会引入跨边界截断的码点
                        let s = unsafe {
                            std::ptr::copy_nonoverlapping(a.as_ptr(), ptr, a.len());
                            std::ptr::copy_nonoverlapping(b.as_ptr(), ptr.add(a.len()), b.len());
                            std::str::from_utf8_unchecked(std::slice::from_raw_parts(ptr, len))
                        };
                        vals.push(v_xcell(bump.alloc(XCell::Lit(s))));
                    }
                    _ => vals.push(v_xcell(bump.alloc(XCell::Prim))),
                }
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
            // 投影：求值接收者后 force（参考版 eval 的 Tm::Obj 臂同）。
            // Sum/SumCase 命中给投影值（miss panic，参考版 unwrap 同款）；
            // 其余形态一律卡成 Obj（参考版 `_` 臂）。
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
                    case_name,
                    datas,
                    is_trait,
                },
                env,
            ) => {
                work.push(W::SumCaseAsm { case_name, datas, is_trait: *is_trait });
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
                            let vf = if *ix >= GLOBAL_BASE {
                                globals[(*ix - GLOBAL_BASE) as usize]
                            } else {
                                env_nth(defs, env, *ix)
                            };
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
                        bump, spine, work, vals, icits, defs, metas, globals, vf, va, i,
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
                        bump, spine, work, vals, icits, defs, metas, globals, vf, v, i,
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
                        bump, spine, work, vals, icits, defs, metas, globals, v, arg, i,
                    );
                    vals.push(r);
                }
            }
            W::ObjSel(name) => {
                let v = vals.pop().expect("eval 栈：ObjSel 缺接收者");
                // L10：接收者先 force（参考版 eval 的 Obj 臂同款）
                let v = force(bump, spine, defs, metas, globals, v);
                match v_tag(v) {
                    7 => match v_xcell_of(v) {
                        XCell::Sum { params, .. } => {
                            match params.iter().find(|p| p.name == name) {
                                Some(p) => vals.push(p.val),
                                // 参考 unwrap：字段必在
                                None => panic!("impossible"),
                            }
                        }
                        XCell::SumCase { typ, datas, .. } => {
                            // typ 必须是 Sum（否则 panic "impossible"）；
                            // 索引参数优先，字段在后
                            let sparams = match v_xcell_of(*typ) {
                                XCell::Sum { params, .. } => *params,
                                _ => panic!("impossible"),
                            };
                            match sparams
                                .iter()
                                .find(|p| p.name == name)
                                .map(|p| p.val)
                                .or_else(|| datas.iter().find(|d| d.name == name).map(|d| d.val))
                            {
                                Some(p) => vals.push(p),
                                None => panic!("impossible"),
                            }
                        }
                        // L10：其余形态（Flex / 卡住 match / 卡住投影 /
                        // 字面量…）卡成 Obj（参考版 `_` 臂同款）
                        _ => vals.push(v_xcell(bump.alloc(XCell::Obj { val: v, name }))),
                    },
                    // 裸 Rigid / Rigid 链 / Flex / 卡住 match / 字面量……
                    // 一律卡成 Obj（参考版 eval 的 Tm::Obj `_` 臂）
                    _ => vals.push(v_xcell(bump.alloc(XCell::Obj { val: v, name }))),
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
            W::SumCaseAsm { case_name, datas, is_trait } => {
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
                vals.push(v_xcell(bump.alloc(XCell::SumCase {
                    typ,
                    case_name,
                    datas: bump.alloc_slice_fill_iter(ds),
                    is_trait,
                })));
            }
            W::MatchSel { cases, env } => {
                let sv = vals.pop().expect("eval 栈：MatchSel 缺 scrutinee");
                let s2 = force(bump, spine, defs, metas, globals, sv);
                if v_tag(s2) == 7 && matches!(v_xcell_of(s2), XCell::SumCase { .. }) {
                    match eval_aux(bump, spine, defs, metas, globals, s2, env, cases) {
                        Some((body_tm, env2)) => {
                            // 分支选中：体在本 eval 循环里尾推
                            work.push(W::Tm(body_tm, env2));
                        }
                        // L10：无臂命中 → 卡住 Match（参考版 None => Match）
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
