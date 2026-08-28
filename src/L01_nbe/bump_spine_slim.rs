//! `bump_spine_iter` 的瘦身改造（`bump_spine_slim`）：spine 条目 24B→16B，
//! **连续性判定从 push 期记账挪到 quote 期推断**。
//!
//! - 旧 [`Entry`]（`bump_spine`）带 `len`/`base` 两个记账字段：每次 `push`
//!   都要 load 前驱条目的 `len`/`base` 并继承（+1/透传）——纯为 quote 的
//!   流式右链检测服务。
//! - 事实：**`entry[i].a == v_spine(i-1)` 当且仅当链在 i 处连续**（`a` 指向
//!   紧前条目）。于是 quote 沿 `a` 下行一步即可判定，push 变纯双 store，
//!   条目从 24B 瘦到 16B（每缓存行 4 条 vs 2.67 条，eval/quote 两条遍历
//!   的缓存密度同步提高）。
//! - 语义与 `bump_spine_iter` 完全一致（同一右链快速路径、同一 fallback
//!   形状）；差别只在记账的位置。下行推断只多一次顺序向下 load（硬件
//!   预取友好），换 push 期每次 -1 load -1 store -加法。
//!
//! 另提供 [`Machine`]：spine 与 vals 两个无生命周期的大栈跨调用复用
//! （配合同一 `Bump` 的 `reset()`），即稳态近零分配口径（bench 的 `_ss` 行）。

use bumpalo::Bump;

use super::bump_arena::{self, Bt};
use super::bump_spine::{
    nth, v_clo, v_clo_of, v_lvl, v_lvl_of, v_spine, v_spine_of, v_tag, CloCell, EnvCons, V,
};
use super::term::Term;

/// spine 栈槽：一次中性应用。无记账字段——连续性由 `a` 指向推断。
pub(crate) struct Entry {
    pub(crate) f: V,
    pub(crate) a: V,
}

/// 求值机持有的扁平中性栈（只增不减，槽位下标即句柄）。
pub(crate) struct Spine {
    pub(crate) stack: Vec<Entry>,
}

impl Spine {
    /// 中性应用 `f a` 压栈，返回句柄值。纯双 store，无前驱读取。
    #[inline]
    pub(crate) fn push(&mut self, f: V, a: V) -> V {
        let idx = self.stack.len();
        self.stack.push(Entry { f, a });
        v_spine(idx)
    }
}

/// eval 的 work 栈条目。
enum W<'a> {
    Tm(&'a Bt<'a>, Option<&'a EnvCons<'a>>),
    Apply,
    /// vals 顶上是 base 值，其下 `n` 个是待应用的链头（内层最上）。
    ChainWrap(u32),
}

/// 双栈迭代 eval：与 `bump_spine_iter` 同语义（先函数后实参），含同一
/// 右链快速路径（链头直进 vals、`ChainWrap` 一次收拢）。
/// 栈由调用方提供（一次性口径传新建 Vec，稳态口径传 [`Machine`] 的）。
fn eval_with<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    env0: Option<&'a EnvCons<'a>>,
    tm0: &'a Bt<'a>,
) -> V {
    work.clear();
    vals.clear();
    work.push(W::Tm(tm0, env0));
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

/// quote 任务。`ChainRun` 是流式右链的"断点续跑"（与 `bump_spine_iter` 同）。
pub(crate) enum QJob<'a> {
    /// 引一个值。
    Q(V, usize),
    /// done 栈顶是体，包一层 Lam。
    Lam1,
    /// 先 eval（引出 Clo 的体）再引——对应递归版 quote 的 Clo 分支。
    EvalQ(&'a Bt<'a>, Option<&'a EnvCons<'a>>, usize),
    /// done 栈顶两个（先 f 后 a），合一个 App——单条目 fallback 用。
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

/// 任务栈 quote：流式右链 + 穿插 fallback。EvalQ 强制闭包体时**复用调用方
/// 的 work/vals 栈**（一次性口径为新建 Vec，稳态口径为 [`Machine`] 的）。
fn quote_with<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    tasks: &mut Vec<QJob<'a>>,
    done: &mut Vec<&'a Bt<'a>>,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    v0: V,
) -> &'a Bt<'a> {
    tasks.clear();
    done.clear();
    tasks.push(QJob::Q(v0, 0));
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
                    let (ef, ea) = {
                        let e = &spine.stack[h];
                        (e.f, e.a)
                    };
                    // 连续性推断：沿 a 下行，entry[i].a 指向 i-1 即链连续。
                    // 同步进行（无重入），读栈安全；下行是顺序访存，预取友好。
                    let mut base = h;
                    while base > 0 {
                        let a = spine.stack[base].a;
                        if v_tag(a) == 2 && v_spine_of(a) == base - 1 {
                            base -= 1;
                        } else {
                            break;
                        }
                    }
                    if h > base {
                        // 连续右链：先引 base，再 ChainRun 自底向上扫
                        let f0 = spine.stack[base].f;
                        let idx_node = if v_tag(f0) == 0 {
                            Some(&*bump.alloc(Bt::Idx(level - v_lvl_of(f0) - 1)))
                        } else {
                            None
                        };
                        let base_v = spine.stack[base].a;
                        tasks.push(QJob::ChainRun {
                            level,
                            next: base,
                            end: h,
                            f0,
                            idx_node,
                            prev: None,
                        });
                        tasks.push(QJob::Q(base_v, level));
                    } else {
                        // 单条目：二叉 fallback
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
                let v = eval_with(bump, spine, work, vals, env, body);
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

/// 稳态复用机：跨调用复用**无生命周期**的两个大栈——spine（每输出 App 一条，
/// 本负载 ~2n 条）与 vals（右链快速路径收链头，~n 个）。带生命周期的小栈
/// （work/tasks/done，本负载恒浅）每调用新建，避免 struct 持 `'a` 跨
/// `Bump::reset` 的借用冲突。配合同一 `Bump` 的 `reset()` 即稳态近零分配。
pub(crate) struct Machine {
    spine: Spine,
    vals: Vec<V>,
}

impl Machine {
    pub(crate) fn new() -> Self {
        Machine {
            spine: Spine { stack: Vec::with_capacity(4096) },
            vals: Vec::with_capacity(4096),
        }
    }

    /// eval（双栈）与 quote（任务栈 + 流式链）都深度无上限；spine/vals 跨
    /// 调用复用（clear 保容量）。调用方保证 `bump`/`tm` 同源（reset 后重 import）。
    pub(crate) fn normalize<'a>(&mut self, bump: &'a Bump, tm: &'a Bt<'a>) -> &'a Bt<'a> {
        self.spine.stack.clear();
        let v = eval_with(bump, &mut self.spine, &mut Vec::new(), &mut self.vals, None, tm);
        quote_with(
            bump,
            &mut self.spine,
            &mut Vec::new(),
            &mut Vec::new(),
            &mut Vec::new(),
            &mut self.vals,
            v,
        )
    }
}

/// 对已导入 bump 的项做 NBE（一次性口径：全部栈每次新建）。
pub(crate) fn normalize_imported<'a>(bump: &'a Bump, tm: &'a Bt<'a>) -> &'a Bt<'a> {
    let mut spine = Spine { stack: Vec::with_capacity(4096) };
    let v = eval_with(bump, &mut spine, &mut Vec::new(), &mut Vec::new(), None, tm);
    quote_with(
        bump,
        &mut spine,
        &mut Vec::new(),
        &mut Vec::new(),
        &mut Vec::new(),
        &mut Vec::new(),
        v,
    )
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
    use super::{bump_arena, normalize, Machine};
    use bumpalo::Bump;

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
        // λf.λg.λx. f (g x)：连续右链但链头不同（f、g 都不是闭包）
        let idx = |i: usize| Term::Idx(i);
        let app = |f: Term, a: Term| Term::App(Box::new(f), Box::new(a));
        let lam = |b: Term| Term::Lam(Box::new(b));
        let input = lam(lam(lam(app(idx(2), app(idx(1), idx(0))))));
        assert_eq!(normalize(input.clone()), input);
    }

    #[test]
    fn machine_steady_state_two_rounds() {
        // 稳态机连续两轮（同一 Bump，reset 后重 import）——检查栈清理正确
        let mut bump = Bump::with_capacity(1 << 16);
        let mut m = Machine::new();
        let r1 = {
            let tm = bump_arena::import(&bump, &term::church_pair(3));
            bump_arena::export(m.normalize(&bump, tm))
        };
        assert_eq!(r1, term::church(6));
        bump.reset();
        let r2 = {
            let tm = bump_arena::import(&bump, &term::church_pair(5));
            bump_arena::export(m.normalize(&bump, tm))
        };
        assert_eq!(r2, term::church(10));
    }
}
