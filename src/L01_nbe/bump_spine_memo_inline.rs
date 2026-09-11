//! `bump_spine_memo` 的**内联缓存槽**改造（`bump_spine_memo_inline`）：把
//! quote 记忆化从"全局 `FxHashMap<(值, level), 结果>`"改成**每个值 cell 自带
//! 一个 `(level, 结果)` 槽**，去掉哈希与查表的那一层间接。
//!
//! 动机来自 guest0x0/normalization-bench 的记忆化 NBE 四变体实测（`NBE_Memo.ml`
//! 的 v1–v4，README「memorized NBE」）：四者算法相同，只差缓存槽放在哪；耗时
//! 与"quote 时取一个值需要几次间接"完全吻合——槽内联进值分支的 v3（1 次间接）
//! 比放在旁路 record 的 v1（2–3 次）快得多，且相对无 memo 基线常数开销很小。
//! `bump_spine_memo` 是旁路哈希表版，本变体是 v3 式的内联槽版，两者算法完全
//! 一致，只差记忆化的取用方式——用于量出哈希税。
//!
//! 槽挂在两个堆 cell 上（tag 0 的 level 值是立即数，quote 本就 O(1)，不挂槽）：
//! [`CloCell`]（闭包）与 [`Entry`]（spine 槽）。语义与 `bump_spine_memo` 一致：
//! 键 = 值 × level，单槽、每次覆盖；唯一区别是命中/写入走 cell 字段而非哈希表。
//!
//! 代价：`CloCell` 16B→32B、`Entry` 24B→40B（多 16B 槽），bump 占用与遍历的
//! 缓存密度变差；收益是省掉每次 `Q` 的哈希 + 探测。哪个赢得看负载——这正是
//! 本变体要测的。

use std::cell::Cell;

use bumpalo::Bump;

use super::bump_arena::{self, Bt};
use super::bump_spine::{
    nth, v_lvl, v_lvl_of, v_spine, v_spine_of, v_tag, EnvCons, V,
};
use super::term::Term;

/// 闭包单元 + 内联记忆化槽。
pub(crate) struct CloCell<'a> {
    pub(crate) env: Option<&'a EnvCons<'a>>,
    pub(crate) body: &'a Bt<'a>,
    /// `(level, 该值在 level 下的 quote 结果)`；`None` = 未缓存。
    memo: Cell<Option<(usize, &'a Bt<'a>)>>,
}

// packed tag 用低 2 位（`v_clo` 写 `ptr | 1`），要求分配地址低 2 位为 0。
// `CloCell` 含引用字段，64 位对齐 8、wasm32 对齐 4，均 ≥4。
const _: () = assert!(std::mem::align_of::<CloCell<'static>>() >= 4);

/// spine 槽：一次中性应用 + 内联记忆化槽。`len`/`base` 记账同
/// `bump_spine::Entry`。
pub(crate) struct Entry<'a> {
    pub(crate) f: V,
    pub(crate) a: V,
    pub(crate) len: u32,
    pub(crate) base: u32,
    memo: Cell<Option<(usize, &'a Bt<'a>)>>,
}

/// 求值机持有的扁平中性栈（只增不减，槽位下标即句柄）。
pub(crate) struct Spine<'a> {
    pub(crate) stack: Vec<Entry<'a>>,
}

impl<'a> Spine<'a> {
    /// 中性应用 `f a` 压栈，返回句柄值。连续性记账同 `bump_spine::Spine::push`。
    #[inline]
    pub(crate) fn push(&mut self, f: V, a: V) -> V {
        let idx = self.stack.len();
        let (len, base) = if v_tag(a) == 2 {
            let prev = &self.stack[v_spine_of(a)];
            (prev.len + 1, prev.base)
        } else {
            (1, idx as u32)
        };
        self.stack.push(Entry { f, a, len, base, memo: Cell::new(None) });
        v_spine(idx)
    }
}

#[inline]
fn v_clo<'a>(p: &'a CloCell<'a>) -> V {
    V((p as *const _ as u64) | 1)
}

#[inline]
fn v_clo_of<'a>(v: V) -> &'a CloCell<'a> {
    // SAFETY: v 由 `v_clo` 构造（tag 1）；指针来自 `Bump::alloc(CloCell)`，
    // 对齐 ≥4（上方 const 断言钉住）⇒ 低 2 位为 0，`& !3` 精确还原指针。
    // `'a` 由调用方保证与分配它的 `Bump` 同寿。
    unsafe { &*((v.0 & !3) as *const CloCell) }
}

/// 双栈迭代 eval：与 `bump_spine_memo::eval_iter` 逐字相同（含右链快速路径）。
fn eval_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine<'a>,
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
                let c = bump.alloc(CloCell { env, body, memo: Cell::new(None) });
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

/// quote 任务。`MemoStore` 是写入内联槽的屏障（语义同 `bump_spine_memo` 的
/// `QJob::MemoStore`，只是落点是值 cell 的字段而非哈希表）。
enum QJob<'a> {
    /// 引一个值。
    Q(V, usize),
    /// done 栈顶是体，包一层 Lam。
    Lam1,
    /// 先 eval（引出 Clo 的体）再引。
    EvalQ(&'a Bt<'a>, Option<&'a EnvCons<'a>>, usize),
    /// done 栈顶两个（先 f 后 a），合一个 App——二叉 fallback 用。
    App1,
    /// 记忆化屏障：done 栈顶是刚完成的 `Q(v, level)` 结果，写入 v 的内联槽后
    /// 放回。派发 `Q` 时压在最深处，LIFO 保证 v 的整棵子任务先跑完。
    MemoStore(V, usize),
    /// 流式右链：next..=end 逐层 App 自底向上。
    ChainRun {
        level: usize,
        next: usize,
        end: usize,
        f0: V,
        idx_node: Option<&'a Bt<'a>>,
        prev: Option<&'a Bt<'a>>,
    },
}

/// 命中查询：返回该值在 `level` 下的缓存结果。tag 0（level 值）不查。
#[inline]
fn memo_get<'a>(spine: &Spine<'a>, v: V, level: usize) -> Option<&'a Bt<'a>> {
    match v_tag(v) {
        0 => None,
        1 => match v_clo_of(v).memo.get() {
            Some((l, t)) if l == level => Some(t),
            _ => None,
        },
        _ => match spine.stack[v_spine_of(v)].memo.get() {
            Some((l, t)) if l == level => Some(t),
            _ => None,
        },
    }
}

#[inline]
fn memo_set<'a>(spine: &Spine<'a>, v: V, level: usize, t: &'a Bt<'a>) {
    match v_tag(v) {
        1 => v_clo_of(v).memo.set(Some((level, t))),
        // tag 0 不走屏障；防御性忽略。
        0 => {},
        _ => spine.stack[v_spine_of(v)].memo.set(Some((level, t))),
    }
}

/// quote：`bump_spine_memo` 的任务栈 + 流式右链，记忆化走值 cell 的内联槽。
fn quote_iter<'a>(bump: &'a Bump, spine: &mut Spine<'a>, v0: V) -> &'a Bt<'a> {
    let mut tasks: Vec<QJob<'a>> = vec![QJob::Q(v0, 0)];
    let mut done: Vec<&'a Bt<'a>> = Vec::new();
    while let Some(job) = tasks.pop() {
        match job {
            QJob::Q(v, level) => {
                if let Some(t) = memo_get(spine, v, level) {
                    done.push(t);
                    continue;
                }
                match v_tag(v) {
                    0 => done.push(bump.alloc(Bt::Idx(level - v_lvl_of(v) - 1))),
                    1 => {
                        tasks.push(QJob::MemoStore(v, level));
                        let c = v_clo_of(v);
                        let node = bump.alloc(EnvCons { val: v_lvl(level), next: c.env });
                        tasks.push(QJob::Lam1);
                        tasks.push(QJob::EvalQ(c.body, Some(node), level + 1));
                    },
                    _ => {
                        tasks.push(QJob::MemoStore(v, level));
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
                }
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
            QJob::MemoStore(v, level) => {
                let t = done.pop().expect("quote 栈：MemoStore 缺结果");
                memo_set(spine, v, level, t);
                done.push(t);
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
pub(crate) fn normalize_imported<'a>(bump: &'a Bump, tm: &'a Bt<'a>) -> &'a Bt<'a> {
    let mut spine = Spine { stack: Vec::with_capacity(4096) };
    let v = eval_iter(bump, &mut spine, None, tm);
    quote_iter(bump, &mut spine, v)
}

/// 便捷入口：import + normalize 一步完成（计时含转换成本）。
#[allow(dead_code)] // 仅供单测：bench 走 normalize_imported
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
        let inner = Term::App(Box::new(Term::Lam(Box::new(Term::Idx(0)))), Box::new(Term::Idx(0)));
        let input = Term::Lam(Box::new(inner));
        assert_eq!(normalize(input), Term::Lam(Box::new(Term::Idx(0))));
    }

    #[test]
    fn interleaved_chains_fallback() {
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
        let idx = |i: usize| Term::Idx(i);
        let app = |f: Term, a: Term| Term::App(Box::new(f), Box::new(a));
        let lam = |b: Term| Term::Lam(Box::new(b));
        let input = lam(lam(lam(app(idx(2), app(idx(1), idx(0))))));
        assert_eq!(normalize(input.clone()), input);
    }

    #[test]
    fn dup_pair_ok() {
        assert_eq!(normalize(term::dup_pair(3)), term::dup_pair_expect(3));
    }

    #[test]
    fn dup_deep_ok() {
        assert_eq!(normalize(term::dup_deep(3)), term::dup_deep_expect(3));
    }

    #[test]
    fn dup_shared_subtree_is_same_pointer() {
        // 结果须为 DAG：两个复制分量共享同一子树指针（内联槽命中的直接证据）。
        use bumpalo::Bump;

        use super::bump_arena::{self, Bt};
        let bump = Bump::new();
        let tm = bump_arena::import_iter(&bump, &term::dup_pair(3));
        let res = super::normalize_imported(&bump, tm);
        let Bt::Lam(Bt::App(Bt::App(_, c1), c2)) = res else {
            panic!("形状应为 λf. f C C")
        };
        assert!(
            std::ptr::eq(*c1, *c2),
            "复制分量未共享子树：内联槽未生效或 level 不命中"
        );
    }

    #[test]
    fn guest_shapes_ok() {
        assert_eq!(normalize(term::church_mul_pair(5)), term::church(25));
        assert_eq!(normalize(term::parigot_add_pair(2)), term::parigot(4));
        assert_eq!(normalize(term::exponential(5)), term::exponential_expect(5));
    }
}
