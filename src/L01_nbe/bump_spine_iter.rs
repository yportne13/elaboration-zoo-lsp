//! `bump_spine` 的迭代改造（`bump_spine_iter`）：**速度 + 深度兼得**。
//!
//! - **eval**：`bump_spine` 递归 eval 的双栈压平（`bump_iter` 之于
//!   `bump_tree` 的同一改造：work/vals 双栈，β 归约是尾循环）。
//! - **quote**：任务栈迭代（`bump_iter` 之于 `quote_bump` 的同一改造），
//!   但保留 `bump_spine` 的核心赢点——**流式右链**：连续右嵌套链的
//!   readback 在 [`QJob::ChainRun`] 里按下标顺序自底向上分配，不逐节点
//!   递归；链头变量相同时 `Idx` 节点共享。
//!
//! 语义与 `bump_spine` 完全一致（同一 spine 机制、同一连续性引理、同一
//! 穿插 fallback）；代价是任务栈的固定开销（对照 `bump_iter` ≈
//! `bump_tree` 的 1.2×）。求值/quote 深度均不受进程栈限——大 n 段
//! （`bench_cek_deep`）出赛。

use bumpalo::Bump;

use super::bump_arena::{self, Bt};
use super::bump_spine::{
    nth, v_clo, v_clo_of, v_lvl, v_lvl_of, v_spine_of, v_tag, CloCell, EnvCons, Spine, V,
};
use super::term::Term;

/// 双栈迭代 eval：与 `bump_spine::eval` 语义相同（先函数后实参）。
///
/// **右链快速路径**：`App(变量头, ·)` 连续嵌套（church 链的形状）不走
/// 通用三推（Apply + Tm(a) + Tm(f)）——头值在下降时直接 `nth` 出来压
/// vals，base 交给通用机器，随后 [`W::ChainWrap`] 把 n 个链头按内层优先
/// 一次 `spine.push` 收拢。整条链不占 work 栈、vals 弹压减半。头若是
/// 闭包（β 岔路）则该层退回通用三推，已收的头仍由 ChainWrap 收拢——
/// 语义与逐层 Apply 等价（spine 入栈次序逐一对齐）。
fn eval_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    env0: Option<&'a EnvCons<'a>>,
    tm0: &'a Bt<'a>,
) -> V {
    enum W<'a> {
        Tm(&'a Bt<'a>, Option<&'a EnvCons<'a>>),
        Apply,
        /// vals 顶上是 base 值，其下 `n` 个是待应用的链头（内层最上）。
        ChainWrap(u32),
    }
    let mut work: Vec<W<'a>> = vec![W::Tm(tm0, env0)];
    let mut vals: Vec<V> = Vec::new();
    while let Some(w) = work.pop() {
        match w {
            W::Tm(Bt::Idx(i), env) => vals.push(nth(env, *i)),
            W::Tm(Bt::Lam(body), env) => {
                let c = bump.alloc(CloCell { env, body });
                vals.push(v_clo(c))
            },
            W::Tm(app @ Bt::App(..), env) => {
                // 右链下钻：头为非闭包变量时头值直接进 vals
                let mut tm = app;
                let mut heads: u32 = 0;
                loop {
                    let (f, a) = match tm {
                        Bt::App(f, a) => (f, a),
                        base => {
                            work.push(W::ChainWrap(heads));
                            work.push(W::Tm(base, env));
                            break;
                        },
                    };
                    match f {
                        Bt::Idx(i) => {
                            let vf = nth(env, *i);
                            if v_tag(vf) == 1 {
                                // β 岔路：本层退回通用三推（ChainWrap 收拢已收的头）
                                work.push(W::ChainWrap(heads));
                                work.push(W::Apply);
                                work.push(W::Tm(a, env));
                                work.push(W::Tm(f, env));
                                break;
                            }
                            vals.push(vf);
                            heads += 1;
                            tm = a;
                        },
                        _ => {
                            // 复合函数头：通用三推（同样先收已收的头）
                            work.push(W::ChainWrap(heads));
                            work.push(W::Apply);
                            work.push(W::Tm(a, env));
                            work.push(W::Tm(f, env));
                            break;
                        },
                    }
                }
            },
            W::Apply => {
                let va = vals.pop().expect("eval 栈：Apply 缺实参");
                let vf = vals.pop().expect("eval 栈：Apply 缺函数");
                if v_tag(vf) == 1 {
                    // β 归约是尾调用：直接推入体，继续循环
                    let c = v_clo_of(vf);
                    let node = bump.alloc(EnvCons { val: va, next: c.env });
                    work.push(W::Tm(c.body, Some(node)));
                } else {
                    vals.push(spine.push(vf, va));
                }
            },
            W::ChainWrap(k) => {
                let mut v = vals.pop().expect("eval 栈：ChainWrap 缺 base");
                for _ in 0..k {
                    let vf = vals.pop().expect("eval 栈：ChainWrap 缺链头");
                    v = spine.push(vf, v);
                }
                vals.push(v);
            },
        }
    }
    vals.pop().expect("eval 必须恰有一个根值")
}

/// quote 任务。`ChainRun` 是流式右链的"断点续跑"：prev=None 表示 base
/// 刚在 done 栈顶（链从 next 起的 f 全走共享 Idx）；prev=Some 表示某个
/// 非平凡 f 刚引完在 done 栈顶，合掉一层后继续。
enum QJob<'a> {
    /// 引一个值。
    Q(V, usize),
    /// done 栈顶是体，包一层 Lam。
    Lam1,
    /// 先 eval（引出 Clo 的体）再引——对应递归版 quote 的 Clo 分支。
    EvalQ(&'a Bt<'a>, Option<&'a EnvCons<'a>>, usize),
    /// done 栈顶两个（先 f 后 a），合一个 App——二叉 fallback 用。
    App1,
    /// 流式右链：next..=end 逐层 App 自底向上；f 与 f0 同为同一变量时
    /// 用共享 idx_node，否则挂起（Q 引 f）后续跑。
    ChainRun {
        level: usize,
        next: usize,
        end: usize,
        f0: V,
        idx_node: Option<&'a Bt<'a>>,
        prev: Option<&'a Bt<'a>>,
    },
}

fn quote_iter<'a>(bump: &'a Bump, spine: &mut Spine, v0: V) -> &'a Bt<'a> {
    let mut tasks: Vec<QJob<'a>> = vec![QJob::Q(v0, 0)];
    let mut done: Vec<&'a Bt<'a>> = Vec::new();
    while let Some(job) = tasks.pop() {
        match job {
            QJob::Q(v, level) => match v_tag(v) {
                0 => done.push(bump.alloc(Bt::Idx(level - v_lvl_of(v) - 1))),
                1 => {
                    let c = v_clo_of(v);
                    let node = bump.alloc(EnvCons { val: v_lvl(level), next: c.env });
                    tasks.push(QJob::Lam1);
                    tasks.push(QJob::EvalQ(c.body, Some(node), level + 1));
                },
                _ => {
                    // 先拷出标量再继续（后续任务会 push spine，Vec 可能扩容）
                    let h = v_spine_of(v);
                    let (ef, ea, len, base) = {
                        let e = &spine.stack[h];
                        (e.f, e.a, e.len, e.base)
                    };
                    if len > 1 && base as usize + len as usize - 1 == h {
                        // 连续右链：先引 base，再 ChainRun 自底向上扫
                        let f0 = spine.stack[base as usize].f;
                        let idx_node = if v_tag(f0) == 0 {
                            Some(&*bump.alloc(Bt::Idx(level - v_lvl_of(f0) - 1)))
                        } else {
                            None
                        };
                        let base_v = spine.stack[base as usize].a;
                        tasks.push(QJob::ChainRun {
                            level,
                            next: base as usize,
                            end: h,
                            f0,
                            idx_node,
                            prev: None,
                        });
                        tasks.push(QJob::Q(base_v, level));
                    } else {
                        tasks.push(QJob::App1);
                        tasks.push(QJob::Q(ea, level));
                        tasks.push(QJob::Q(ef, level));
                    }
                },
            },
            QJob::Lam1 => {
                let body = done.pop().expect("quote 栈：Lam 缺体");
                done.push(bump.alloc(Bt::Lam(body)));
            },
            QJob::EvalQ(body, env, level) => {
                let v = eval_iter(bump, spine, env, body);
                tasks.push(QJob::Q(v, level));
            },
            QJob::App1 => {
                let a = done.pop().expect("quote 栈：App 缺实参");
                let f = done.pop().expect("quote 栈：App 缺函数");
                done.push(bump.alloc(Bt::App(f, a)));
            },
            QJob::ChainRun { level, next, end, f0, idx_node, prev } => {
                let mut prev = match prev {
                    Some(p) => {
                        // 恢复点：非平凡 f 刚引完在 done 栈顶，合掉一层
                        let f_node = done.pop().expect("quote 栈：链缺函数头");
                        bump.alloc(Bt::App(f_node, p))
                    },
                    None => done.pop().expect("quote 栈：链缺 base"),
                };
                let mut i = next;
                loop {
                    if i > end {
                        done.push(prev);
                        break;
                    }
                    let fi = spine.stack[i].f;
                    match idx_node {
                        Some(n) if fi.0 == f0.0 => {
                            prev = bump.alloc(Bt::App(n, prev));
                            i += 1;
                        },
                        _ => {
                            // 非平凡链头：挂起引 f，ChainRun 续跑
                            tasks.push(QJob::ChainRun {
                                level,
                                next: i + 1,
                                end,
                                f0,
                                idx_node,
                                prev: Some(prev),
                            });
                            tasks.push(QJob::Q(fi, level));
                            break;
                        },
                    }
                }
            },
        }
    }
    done.pop().expect("quote 必须恰有一个根")
}

/// 对已导入 bump 的项做 NBE（基准计时对象；import 在计时外）。
/// eval（双栈）与 quote（任务栈 + 流式链）都深度无上限。
pub(crate) fn normalize_imported<'a>(bump: &'a Bump, tm: &'a Bt<'a>) -> &'a Bt<'a> {
    let mut spine = Spine { stack: Vec::with_capacity(4096) };
    let v = eval_iter(bump, &mut spine, None, tm);
    quote_iter(bump, &mut spine, v)
}

/// 便捷入口：import + normalize 一步完成（计时含转换成本）。
pub(crate) fn normalize(t: Term) -> Term {
    let bump = Bump::new();
    let tm = bump_arena::import_iter(&bump, &t);
    bump_arena::export(normalize_imported(&bump, tm))
}

#[cfg(test)]
mod tests {
    use super::super::term::{self, Term};
    use super::normalize;

    #[test]
    fn church_pair_ok() {
        assert_eq!(normalize(term::church_pair(5)), term::church(10));
    }

    #[test]
    fn already_normal_right_chain() {
        // λf.λx. f (f x)：已正态，走流式右链路径，结果须逐字还原
        let input = {
            let mut t = Term::Idx(0);
            for _ in 0..4 {
                t = Term::App(Box::new(Term::Idx(1)), Box::new(t));
            }
            Term::Lam(Box::new(Term::Lam(Box::new(t))))
        };
        assert_eq!(normalize(input.clone()), input);
    }

    #[test]
    fn beta_under_binder() {
        // λg. (λx. x) g  →  λg. g
        let inner = Term::App(Box::new(Term::Lam(Box::new(Term::Idx(0)))), Box::new(Term::Idx(0)));
        let input = Term::Lam(Box::new(inner));
        assert_eq!(normalize(input), Term::Lam(Box::new(Term::Idx(0))));
    }

    #[test]
    fn interleaved_chains_fallback() {
        // λf.λg.λx. (λy. (f y) (g y)) (f x) → λf.λg.λx. (f (f x)) (g (f x))
        let idx = |i: usize| Term::Idx(i);
        let app = |f: Term, a: Term| Term::App(Box::new(f), Box::new(a));
        let lam = |b: Term| Term::Lam(Box::new(b));
        let inner = app(app(idx(3), idx(0)), app(idx(2), idx(0)));
        let input = lam(lam(lam(app(lam(inner), app(idx(2), idx(0))))));
        let expect = lam(lam(lam(app(
            app(idx(2), app(idx(2), idx(0))),
            app(idx(1), app(idx(2), idx(0))),
        ))));
        assert_eq!(normalize(input), expect);
    }

    #[test]
    fn chain_beta_fork() {
        // (λf.λx. f (f x)) (λu.u) → λx. x：右链下钻中头指向闭包 → β 岔路
        // （ChainWrap(0) + 通用三推），岔路后又续上链
        let idx = |i: usize| Term::Idx(i);
        let app = |f: Term, a: Term| Term::App(Box::new(f), Box::new(a));
        let lam = |b: Term| Term::Lam(Box::new(b));
        let id = lam(idx(0));
        let church2 = lam(lam(app(idx(1), app(idx(1), idx(0)))));
        let input = app(church2, id.clone());
        assert_eq!(normalize(input), id);
    }

    #[test]
    fn chain_mixed_heads() {
        // λf.λg.λx. f (g x)：连续右链但链头不同（f、g 都不是闭包）——
        // eval 快速路径收 2 头，quote 流式但 f 不共享
        let idx = |i: usize| Term::Idx(i);
        let app = |f: Term, a: Term| Term::App(Box::new(f), Box::new(a));
        let lam = |b: Term| Term::Lam(Box::new(b));
        let input = lam(lam(lam(app(idx(2), app(idx(1), idx(0))))));
        assert_eq!(normalize(input.clone()), input);
    }
}
