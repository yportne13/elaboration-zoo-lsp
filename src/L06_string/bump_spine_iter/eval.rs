//! eval：force（迭代）+ 双栈迭代 eval（`W`/`eval_iter`；右链快速路径 +
//! AppPruning 实参应用 + decl 表）。原 bump_spine_iter.rs 的 "force（迭代）"
//! 节（不足 200 行，按拆分纪律并入内容最近的 eval）与 "eval…" 一节，
//! 逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;
use rustc_hash::FxHashMap;
use smol_str::SmolStr;

use super::parser::syntax::Icit;

use super::env::{env_ext, env_nth, CloCell, Env, PiCell};
use super::prim::{decl_apply, vapp1, DeclEntryF, MutableMap};
use super::spine::{is_declheaded, meta_val_of, MetaEntry, Spine};
use super::syntax::{PrCons, Tm, V, XCell, v_clo, v_clo_of, v_lit_ty, v_meta_of, v_pi, v_spine_of, v_tag, v_u, v_xcell};

// force（迭代）
// --------------------------------------------------------------------------------

/// **force**：把值更新到 metacontext 的当前状态。已解 meta 立即数 → 替换
/// 为解；已解 flex spine → 沿 f 链收集实参（带 icit）、把解按应用序应用到
/// 实参上（应用可触发 β / builtin prim，经 `vapp1`），再继续。
pub(super) fn force<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<SmolStr, DeclEntryF>,
    mmap: &MutableMap,
    v0: V,
) -> V {
    let mut v = v0;
    // 实参缓冲在本次 force 调用内的已解链轮间复用（clear 保容量）
    let mut args: Vec<(V, Icit)> = Vec::new();
    loop {
        match v_tag(v) {
            5 => match &metas[v_meta_of(v) as usize] {
                MetaEntry::Solved(sol, _) => v = *sol,
                MetaEntry::Unsolved(_) => return v,
            },
            2 => {
                let h = v_spine_of(v);
                let hd = spine.spine_head(h);
                if v_tag(hd) != 5 {
                    return v; // 刚性/Decl 链
                }
                let m = v_meta_of(hd);
                match &metas[m as usize] {
                    MetaEntry::Unsolved(_) => return v,
                    MetaEntry::Solved(sol, _) => {
                        // 把解应用到全部实参（应用序 = 收集序的逆序）；
                        // 每步都可能 β（解是闭包）或触发 builtin（解是
                        // Decl 头的卡住链）——参考版 vAppSp 逐步 vApp 同款
                        args.clear();
                        spine.collect_args(h, &mut args);
                        let mut t = *sol;
                        for &(a, i) in args.iter().rev() {
                            t = vapp1(
                                bump, spine, work, vals, icits, defs, metas, decls, mmap, t, a, i,
                            );
                        }
                        v = t;
                    }
                }
            }
            _ => return v,
        }
    }
}

// eval（双栈迭代 + 右链快速路径 + AppPruning 实参应用 + decl 表）
// --------------------------------------------------------------------------------

/// eval 的 work 栈条目。
pub(super) enum W<'a> {
    Tm(&'a Tm<'a>, Env<'a>),
    /// 应用（icit 来自 `Tm::App`）：vals 顶两个（先函数后实参）——β、
    /// builtin 触发或入栈。
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
    /// （Clo → β；Decl 头 → prim；其它 → spine.push）。
    AppPrunOne(V, Icit),
}

/// 双栈迭代 eval（L05 版 + L06 增量：decl 表查找、字面量、Decl 头应用的
/// builtin 触发）。
#[allow(clippy::too_many_arguments)]
pub(super) fn eval_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<SmolStr, DeclEntryF>,
    mmap: &MutableMap,
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
            W::Tm(Tm::LiteralIntro(s), _) => {
                vals.push(v_xcell(bump.alloc(XCell::Lit(s))))
            }
            // 按名查 decl 表：命中给登记值（builtin 即卡住的头，应用时触发
            // prim）；miss 保持卡住（现造 Decl 单元，参考版同款每次新值）
            W::Tm(Tm::Decl(name), _) => vals.push(match decls.get(*name) {
                Some(e) => e.vt,
                None => v_xcell(bump.alloc(XCell::Decl(name))),
            }),
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
                } else if is_declheaded(spine, vf) {
                    let r = decl_apply(
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, vf, va, i,
                    );
                    vals.push(r);
                } else {
                    vals.push(spine.push(vf, va, i));
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
                    // 链头是 Decl 值（define 的卡住头）：应用即触发尝试
                    // （参考版 vApp 的 Decl 臂；通常 None 保持卡住）
                    v = if is_declheaded(spine, vf) {
                        decl_apply(
                            bump, spine, work, vals, icits, defs, metas, decls, mmap, vf, v, i,
                        )
                    } else {
                        spine.push(vf, v, i)
                    };
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
                } else if is_declheaded(spine, v) {
                    let r = decl_apply(
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, v, arg, i,
                    );
                    vals.push(r);
                } else {
                    vals.push(spine.push(v, arg, i));
                }
            }
        }
    }
    vals.pop().expect("eval 必须恰有一个根值")
}
