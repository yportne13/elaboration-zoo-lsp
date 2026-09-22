//! eval：双栈迭代 eval（`W`/`eval_iter`）+ 运行时分支选择（`eval_aux`/
//! `eval_aux_case`，值层首匹配）。原 bump_spine_iter.rs 的 "运行时分支
//! 选择" 与 "eval" 两节，逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;
use rustc_hash::FxHashMap;

use super::parser::syntax::Icit;
use super::PatternDetail;

use super::env::{CloCell, Env, env_ext, env_len, env_nth, PiCell};
use super::force::{force, project, vapp1};
use super::prim::{DeclEntryF, Fuel, MutableMap};
use super::spine::{meta_val_of, MetaEntry, Spine};
use super::syntax::{PrCons, SumDataT, SumDataV, SumParamT, SumParamV, Tm, V, v_clo, v_clo_of, v_lit_ty, v_pi, v_tag, v_u, v_xcell, v_xcell_of, XCell};

// 运行时分支选择（值层首匹配，无合一）
// --------------------------------------------------------------------------------

/// 按模式首匹配。返回 (分支体, 扩展后的 env)。任何 head 都不会 panic——
/// 不命中就返回 None，由调用方停成卡住 Match。（参考版
/// `Compiler::eval_aux` 同款：Any/Bind → 命中；Con → head 是同名 SumCase
/// （ctor 名在 typ 的 Sum cases 里）→ 逐 datas×子模式递归；名字不在 typ
/// 的 ctor 表里 → 按变量模式命中（保守兼容）；同类型不同构造子 → 试下一
/// 分支。入口 force(head)。）
#[allow(clippy::too_many_arguments)]
pub(super) fn eval_aux<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    head: V,
    env: Env<'a>,
    cases: &'a [(PatternDetail, &'a Tm<'a>)],
) -> Option<(&'a Tm<'a>, Env<'a>)> {
    let head = force(bump, spine, defs, metas, decls, mmap, fuel, head);
    for (pat, body) in cases.iter() {
        if let Some(r) = eval_aux_case(
            bump, spine, defs, metas, decls, mmap, fuel, head, env, pat, *body,
        ) {
            return Some(r);
        }
    }
    None
}

/// 单 (模式, 分支体) 的匹配（`eval_aux` 的内层；返回 None = 试下一分支）。
#[allow(clippy::too_many_arguments)]
fn eval_aux_case<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    head: V,
    env: Env<'a>,
    pat: &PatternDetail,
    body: &'a Tm<'a>,
) -> Option<(&'a Tm<'a>, Env<'a>)> {
    match pat {
        PatternDetail::Any(_) | PatternDetail::Bind(_) => {
            Some((body, env_ext(bump, env, head)))
        }
        PatternDetail::Con(name, subs) => {
            let (case_name, typ, datas) = match v_tag(head) {
                7 => match v_xcell_of(head) {
                    XCell::SumCase {
                        typ,
                        case_name,
                        datas,
                    } => (*case_name, *typ, *datas),
                    _ => return None, // 非 SumCase：试下一分支
                },
                _ => return None,
            };
            let ctor_names = match v_xcell_of(typ) {
                XCell::Sum { cases, .. } => *cases,
                _ => return None, // typ 不是 Sum：试下一分支
            };
            let in_type = ctor_names.iter().any(|c| *c == name.data);
            if in_type && case_name == name.data {
                if subs.len() != datas.len() {
                    return None; // 子模式数失配：试下一分支（参考版 continue）
                }
                // datas 与子模式按声明序 zip，逐个下钻；先 prepend 被匹配值
                // 本身（head 槽，编译期 walk_con 入口同序绑定），再逐字段
                // prepend 子模式槽值（编译期字段槽在后）
                let mut cur_body = body;
                let mut cur_env = env_ext(bump, env, head);
                for (d, sub) in datas.iter().zip(subs.iter()) {
                    let df = force(bump, spine, defs, metas, decls, mmap, fuel, d.val);
                    match eval_aux_case(
                        bump, spine, defs, metas, decls, mmap, fuel, df, cur_env, sub,
                        cur_body,
                    ) {
                        Some((b, e)) => {
                            cur_body = b;
                            cur_env = e;
                        }
                        None => return None, // 子模式失配：试下一分支
                    }
                }
                Some((cur_body, cur_env))
            } else if !in_type {
                // 不是该类型的构造子名 → 变量模式（保守兼容）
                Some((body, env_ext(bump, env, head)))
            } else {
                None // 同类型不同构造子 → 试下一分支
            }
        }
    }
}

// eval（双栈迭代 + 右链快速路径 + AppPruning 实参应用 + decl 表 + L07 变体）
// --------------------------------------------------------------------------------

/// eval 的 work 栈条目。
pub(super) enum W<'a> {
    Tm(&'a Tm<'a>, Env<'a>),
    /// 应用（icit 来自 `Tm::App`）：vals 顶两个（先函数后实参）——β、
    /// pending 累积或入栈。
    Apply(Icit),
    /// vals 顶上是实参；函数值已知是闭包（β 岔路下降时已 `env_nth` 出来），
    /// 直接 β（icit 无关）。
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
    /// vals 顶是 `vAppPruning` 的当前值；本步把 `arg` 以 `icit` 应用上去
    /// （Clo → β；卡住 match → pending；其它 → spine.push）。
    AppPrunOne(V, Icit),
    /// vals 顶是投影接收者的值：project 命中给投影值，miss 卡成 Obj。
    ObjSel(&'a str),
    /// vals 顶自底向上是 (v0,t0,...,v_{n-1},t_{n-1})（求值序）：装配 Sum。
    SumAsm {
        name: &'a str,
        params: &'a [SumParamT<'a>],
        cases: &'a [&'a str],
    },
    /// vals 顶自底向上是 (typ, d0..d_{nd-1})：装配 SumCase。
    SumCaseAsm {
        case_name: &'a str,
        datas: &'a [SumDataT<'a>],
    },
    /// vals 顶是 scrutinee 的值：force 后是 SumCase → eval_aux 选分支
    /// （选中 → 尾推分支体）；否则卡成 Match（pending 空）。
    MatchSel {
        cases: &'a [(PatternDetail, &'a Tm<'a>)],
        env: Env<'a>,
    },
}

/// 双栈迭代 eval（L06 版 + L07 增量：decl 表 panic 语义、Prim 体、投影、
/// Sum/SumCase 装配、match 的编译期选择与卡住停等）。
#[allow(clippy::too_many_arguments)]
pub(super) fn eval_iter<'a>(
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
    env0: Env<'a>,
    tm0: &'a Tm<'a>,
) -> V {
    work.clear();
    vals.clear();
    icits.clear();
    work.push(W::Tm(tm0, env0));
    while let Some(w) = work.pop() {
        match w {
            W::Tm(Tm::Var(i), env) => vals.push(env_nth(defs, env, *i)),
            W::Tm(Tm::Lam(name, icit, body), env) => {
                let c = bump.alloc(CloCell {
                    name,
                    icit: *icit,
                    env,
                    body,
                });
                vals.push(v_clo(c));
            }
            W::Tm(Tm::U, _) => vals.push(v_u()),
            W::Tm(Tm::LiteralType, _) => vals.push(v_lit_ty()),
            W::Tm(Tm::LiteralIntro(s), _) => vals.push(v_xcell(bump.alloc(XCell::Lit(s)))),
            // 按名查 decl 表：命中给登记值；miss panic（"unbound global"，
            // 参考版 eval 的 Tm::Decl 臂同款——良型项不可达）
            W::Tm(Tm::Decl(name), _) => vals.push(match decls.get(*name) {
                Some(e) => e.val,
                None => panic!("unbound global {}", name),
            }),
            // builtin 体：实参 = env 全部槽（应用序 = 外层槽先应用）→ 链头
            // = 最后应用 = 最内槽。归约统一在 force（不在求值点按 env 触发
            // ——quote → eval 往返时项已改成 `Prim 实参` 的应用形态，按
            // 现场 env 触发会把无关的字面量拼进来；参考版注释同款论证）
            W::Tm(Tm::Prim(name), env) => {
                let n = env_len(env);
                let mut acc = v_xcell(bump.alloc(XCell::Prim(name)));
                let mut i = n;
                while i > 0 {
                    i -= 1;
                    acc = spine.push(acc, env_nth(defs, env, i), Icit::Expl);
                }
                vals.push(acc);
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
            // 投影：求值接收者（不 force——参考版同），project 命中给投影
            // 值，miss 卡成 `Obj`
            W::Tm(Tm::Obj(h, name), env) => {
                work.push(W::ObjSel(name));
                work.push(W::Tm(h, env));
            }
            // enum 本体：逐参数求值（值 + 类型）后装配
            W::Tm(Tm::Sum(name, params, cases), env) => {
                work.push(W::SumAsm { name, params, cases });
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
                },
                env,
            ) => {
                work.push(W::SumCaseAsm { case_name, datas });
                for d in datas.iter().rev() {
                    work.push(W::Tm(d.val, env));
                }
                work.push(W::Tm(typ, env));
            }
            // match：求值 scrutinee → force → 选分支 / 卡住（参考版 eval 的
            // Tm::Match 臂：SumCase + eval_aux 命中给分支体（eval_aux 是值
            // 层首匹配，无合一）；其它 neutral 卡 Match，pending 空）
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
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel,
                        vf, va, i,
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
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel,
                        vf, v, i,
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
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel,
                        v, arg, i,
                    );
                    vals.push(r);
                }
            }
            W::ObjSel(name) => {
                let v = vals.pop().expect("eval 栈：ObjSel 缺接收者");
                match project(v, name) {
                    Some(p) => vals.push(p),
                    None => vals.push(v_xcell(bump.alloc(XCell::Obj { val: v, name }))),
                }
            }
            W::SumAsm { name, params, cases } => {
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
                })));
            }
            W::SumCaseAsm { case_name, datas } => {
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
                })));
            }
            W::MatchSel { cases, env } => {
                let sv = vals.pop().expect("eval 栈：MatchSel 缺 scrutinee");
                let s2 = force(bump, spine, defs, metas, decls, mmap, fuel, sv);
                let mut stuck = true;
                if v_tag(s2) == 7 && matches!(v_xcell_of(s2), XCell::SumCase { .. }) {
                    // 不烧 fuel：参考版 eval(Tm::Match) 直呼 eval_aux，无
                    // burn（force 的 Match 重选臂才烧——见 force 的 Match 臂）。
                    if let Some((body_tm, env2)) = eval_aux(
                        bump, spine, defs, metas, decls, mmap, fuel, s2, env, cases,
                    ) {
                        // 分支选中：体在本 eval 循环里尾推（pending 空）
                        work.push(W::Tm(body_tm, env2));
                        stuck = false;
                    }
                }
                if stuck {
                    vals.push(v_xcell(bump.alloc(XCell::Match {
                        scrutinee: s2,
                        env,
                        cases,
                        pending: &[],
                    })));
                }
            }
        }
    }
    vals.pop().expect("eval 必须恰有一个根值")
}
