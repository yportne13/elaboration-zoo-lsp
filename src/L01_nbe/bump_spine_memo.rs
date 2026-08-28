//! `bump_spine_iter` 的 **quote 记忆化**改造（`bump_spine_memo`）：call-by-need
//! 的 readback 对偶（Lean 式 whnf 缓存的 quote 版）。
//!
//! 动机：NbE 的 CBV 只急切到 WHNF（`Lam` 求值 = O(1) 闭包创建），经典
//! "丢弃参数"浪费几乎不存在；**真正的重复在 readback**——同一个闭包/中性
//! 句柄值经 λ-binder 复制（`(λx. pair x x) BIG`）后，quote 会对它**多次
//! 强制求值**（每次都是完整的 body 重走 + 结果树重建）。
//!
//! 机制：quote 任务栈新增 [`QJob::MemoStore`] 屏障——`Q(v, level)` 先查
//! memo（键 = 值的打包字 `v.0` × quote level，闭包指针与 spine 句柄都
//! 全局唯一；同一值在同一 level 的 quote 结果只依赖 `(v, level)`，spine
//! 栈只增不改、条目压栈后不变，故缓存可靠）。未命中则在派发原任务前把
//! `MemoStore` 压到最深处：LIFO 栈纪律保证 v 的整棵子任务都跑在它之上，
//! 它弹出时 done 栈顶恰是 v 的完整结果——取出、入表、放回。命中则直接
//! `done.push` 共享子树（结果从树变 DAG，与 ChainRun 的 `Idx` 节点共享
//! 同一性质）。
//!
//! 代价：每个 Clo/中性 `Q` 一次哈希查 + 一次哈希插。`church_pair` 负载
//! 里 `Q` 的调用次数只有 O(λ 层)（链节点走 ChainRun，不经过 Q），故
//! 开销趋近于零；dup 负载（`dup_pair`/`dup_deep`，见 bench）里把
//! 2×/4× 的重复强制压回 1×。

use bumpalo::Bump;
use rustc_hash::FxHashMap;

use super::bump_arena::{self, Bt};
use super::bump_spine::{
    nth, v_clo, v_clo_of, v_lvl, v_lvl_of, v_spine_of, v_tag, CloCell, EnvCons, Spine, V,
};
use super::term::Term;

/// 双栈迭代 eval：与 `bump_spine_iter::eval_iter` 逐字相同（含右链快速路径）。
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

/// quote 任务（`bump_spine_iter` 的 QJob + 记忆化屏障）。
enum QJob<'a> {
    /// 引一个值。
    Q(V, usize),
    /// done 栈顶是体，包一层 Lam。
    Lam1,
    /// 先 eval（引出 Clo 的体）再引——对应递归版 quote 的 Clo 分支。
    EvalQ(&'a Bt<'a>, Option<&'a EnvCons<'a>>, usize),
    /// done 栈顶两个（先 f 后 a），合一个 App——二叉 fallback 用。
    App1,
    /// 记忆化屏障：done 栈顶是刚完成的 `Q(v.0, level)` 结果，入表后放回。
    /// 派发 `Q` 时压在最深处，LIFO 保证 v 的整棵子任务先跑完。
    MemoStore(u64, usize),
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

/// quote：`bump_spine_iter` 的任务栈 + 流式右链，外加 (值, level) → 结果
/// 子树的 memo。tag 0（level 值）的 Q 是 O(1)，不走 memo。
fn quote_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    memo: &mut FxHashMap<(u64, usize), &'a Bt<'a>>,
    v0: V,
) -> &'a Bt<'a> {
    let mut tasks: Vec<QJob<'a>> = vec![QJob::Q(v0, 0)];
    let mut done: Vec<&'a Bt<'a>> = Vec::new();
    while let Some(job) = tasks.pop() {
        match job {
            QJob::Q(v, level) => match v_tag(v) {
                0 => done.push(bump.alloc(Bt::Idx(level - v_lvl_of(v) - 1))),
                1 => {
                    if let Some(t) = memo.get(&(v.0, level)) {
                        done.push(*t);
                        continue;
                    }
                    // 屏障压在最深处：v 的子任务全部跑完后它弹出并回填
                    tasks.push(QJob::MemoStore(v.0, level));
                    let c = v_clo_of(v);
                    let node = bump.alloc(EnvCons { val: v_lvl(level), next: c.env });
                    tasks.push(QJob::Lam1);
                    tasks.push(QJob::EvalQ(c.body, Some(node), level + 1));
                },
                _ => {
                    if let Some(t) = memo.get(&(v.0, level)) {
                        done.push(*t);
                        continue;
                    }
                    tasks.push(QJob::MemoStore(v.0, level));
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
            QJob::MemoStore(key, level) => {
                let t = done.pop().expect("quote 栈：MemoStore 缺结果");
                memo.insert((key, level), t);
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
    let mut memo: FxHashMap<(u64, usize), &'a Bt<'a>> = FxHashMap::default();
    let v = eval_iter(bump, &mut spine, None, tm);
    quote_iter(bump, &mut spine, &mut memo, v)
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
        // 复制强制负载：quote 两次强制同一闭包，memo 命中须给出共享 DAG
        assert_eq!(normalize(term::dup_pair(3)), term::dup_pair_expect(3));
    }

    #[test]
    fn dup_deep_ok() {
        assert_eq!(normalize(term::dup_deep(3)), term::dup_deep_expect(3));
    }

    #[test]
    fn dup_shared_subtree_is_same_pointer() {
        // 结果是 DAG：两个复制分量应共享同一子树指针（memo 命中的直接证据）。
        // 注意：在 &Bt 上做模式匹配，绑定是"指向父节点字段槽位的引用"，
        // 比较子节点须再解一层（`*c1` 才是真正的子节点指针）。
        use super::bump_arena::{self, Bt};
        use bumpalo::Bump;
        let bump = Bump::new();
        let tm = bump_arena::import_iter(&bump, &term::dup_pair(3));
        let res = super::normalize_imported(&bump, tm);
        // λf. f C C：根 Lam 的体是 App(App(Idx, C), C)——两处 C 指针相同
        let Bt::Lam(Bt::App(Bt::App(_, c1), c2)) = res else {
            panic!("形状应为 λf. f C C")
        };
        assert!(
            std::ptr::eq(*c1, *c2),
            "复制分量未共享子树：memo 未生效或键不命中"
        );
    }
}
