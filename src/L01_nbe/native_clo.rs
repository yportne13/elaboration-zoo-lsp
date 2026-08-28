//! 原生闭包 NBE（`native_clo`）：封轴实验——**β 步 = 一次原生间接调用**。
//!
//! import 后把项**编译**为一棵原生 Rust 闭包树（闭包本体 bump 分配、以
//! `&'a dyn Fn` 胖引用装进 [`Clo`]——引用层面的 unsize 强转是稳定功能；
//! `bumpalo::boxed::Box` 的 `CoerceUnsized` 是 nightly，绕开），每个项节点
//! 一个闭包，捕获已编译的子节点：
//!
//! ```text
//! Idx(i)  ↦ |spine, env| nth(env, i)
//! Lam(b)  ↦ |spine, env| v_clo(Clo{ f: &dyn(|spine', x| cb(spine', cons(x, env))) })
//! App(f,a)↦ |spine, env| apply(spine, cf(spine, env), ca(spine, env))
//! ```
//!
//! Lam 在**求值时**才创建捕获当前 env 的单参闭包——β 归约即调用它，
//! 不再解释遍历项、无 work/vals 双栈、无 Bt 判别分发。值（`V` 打包
//! 64 位）与中性 spine（16B 条目、quote 期连续性推断）复用
//! `bump_spine`/`bump_spine_slim` 的机制；quote 的 Clo 分支同样退化为
//! 一次原生调用（替代 `EvalQ` + 双栈 eval），其余与 `bump_spine_slim`
//! 逐字相同。
//!
//! 本变体隔离的轴：**项访问 = 原生闭包调用 vs 机器解释**（对照
//! `compiled` 的指令数组解释——被实测否决——与 `bump_spine_iter` 的
//! 指针树解释）。原生路线的固有代价：dyn 调用不可内联、每 β 三次 bump
//! 分配（闭包体 + Clo 单元 + EnvCons，解释版是两次）、eval 递归深度 =
//! 项深（原生栈帧，深度受限同递归变体）。基准里 compile 在计时外
//! （与各变体的 import 同口径）。

use bumpalo::Bump;

use super::bump_arena::{self, Bt};
use super::bump_spine::{nth, v_lvl, v_lvl_of, v_spine_of, v_tag, EnvCons, V};
use super::bump_spine_slim::{QJob, Spine};
use super::term::Term;

/// 闭包单元：装一个原生单参闭包的胖引用。包装层只为给 `V` 打包提供
/// thin 指针（`&dyn Fn` 本身是胖指针，塞不进 u64）。
pub(crate) struct Clo<'a> {
    pub(crate) f: &'a (dyn Fn(&mut Spine, V) -> V + 'a),
}

#[inline]
fn v_clo<'a>(p: &'a Clo<'a>) -> V {
    V((p as *const _ as u64) | 1)
}

#[inline]
fn v_clo_of<'a>(v: V) -> &'a Clo<'a> {
    unsafe { &*((v.0 & !3) as *const Clo) }
}

/// 编译后的项节点：`(&mut Spine, env) -> V`（spine 穿参数传递，闭包只
/// 捕获编译期数据——已编译子节点与环境）。
pub(crate) type Code<'a> = &'a (dyn Fn(&mut Spine, Option<&'a EnvCons<'a>>) -> V + 'a);

/// 应用一个值：闭包则 β（一次原生调用），否则中性压栈。
#[inline]
fn apply(spine: &mut Spine, vf: V, va: V) -> V {
    if v_tag(vf) == 1 {
        (v_clo_of(vf).f)(spine, va)
    } else {
        spine.push(vf, va)
    }
}

/// 把 bump 内的项编译为原生闭包树（递归，深度同 `import`）。
pub(crate) fn compile<'a>(bump: &'a Bump, t: &'a Bt<'a>) -> Code<'a> {
    match t {
        Bt::Idx(i) => {
            let i = *i;
            let f = move |_spine: &mut Spine, env: Option<&'a EnvCons<'a>>| nth(env, i);
            let code: Code<'a> = bump.alloc(f);
            code
        },
        Bt::Lam(body) => {
            let cb: Code<'a> = compile(bump, body);
            let f = move |_spine: &mut Spine, env: Option<&'a EnvCons<'a>>| {
                // 捕获当前 env 的单参闭包：这就是"求值时的 VLam"。
                // 闭包本体 bump 分配，&Closure→&dyn 的 unsize 强转在此完成。
                let g: &'a (dyn Fn(&mut Spine, V) -> V + 'a) = bump.alloc(
                    move |spine: &mut Spine, x: V| {
                        let node = bump.alloc(EnvCons { val: x, next: env });
                        cb(spine, Some(node))
                    },
                );
                let c = bump.alloc(Clo { f: g });
                v_clo(c)
            };
            let code: Code<'a> = bump.alloc(f);
            code
        },
        Bt::App(fl, al) => {
            let cf: Code<'a> = compile(bump, fl);
            let ca: Code<'a> = compile(bump, al);
            let f = move |spine: &mut Spine, env: Option<&'a EnvCons<'a>>| {
                // 先函数后实参，与解释版同序
                let vf = cf(spine, env);
                let va = ca(spine, env);
                apply(spine, vf, va)
            };
            let code: Code<'a> = bump.alloc(f);
            code
        },
    }
}

/// quote：与 `bump_spine_slim` 相同的任务栈 + 流式右链，唯 Clo 分支是
/// 一次原生调用（无 `EvalQ` 任务——闭包体由调用直接引出）。
fn quote_iter<'a>(bump: &'a Bump, spine: &mut Spine, v0: V) -> &'a Bt<'a> {
    let mut tasks: Vec<QJob<'a>> = vec![QJob::Q(v0, 0)];
    let mut done: Vec<&'a Bt<'a>> = Vec::new();
    while let Some(job) = tasks.pop() {
        match job {
            QJob::Q(v, level) => match v_tag(v) {
                0 => done.push(bump.alloc(Bt::Idx(level - v_lvl_of(v) - 1))),
                1 => {
                    let c = v_clo_of(v);
                    // β：一次原生调用替代 EvalQ + 双栈 eval
                    let body = (c.f)(spine, v_lvl(level));
                    tasks.push(QJob::Lam1);
                    tasks.push(QJob::Q(body, level + 1));
                },
                _ => {
                    let h = v_spine_of(v);
                    let (ef, ea) = {
                        let e = &spine.stack[h];
                        (e.f, e.a)
                    };
                    // 连续性推断：沿 a 下行，entry[i].a 指向 i-1 即链连续
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
            QJob::EvalQ(..) => unreachable!("native_clo 无 EvalQ：闭包体由原生调用引出"),
            QJob::App1 => {
                let a = done.pop().expect("quote 栈：App 缺实参");
                let f = done.pop().expect("quote 栈：App 缺函数");
                done.push(bump.alloc(Bt::App(f, a)));
            },
            QJob::ChainRun { level, next, end, f0, idx_node, prev } => {
                let mut prev = match prev {
                    Some(p) => {
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

/// 对已编译的项做 NBE（基准计时对象；compile 在计时外，与 import 同口径）。
pub(crate) fn normalize_compiled<'a>(bump: &'a Bump, code: Code<'a>) -> &'a Bt<'a> {
    let mut spine = Spine { stack: Vec::with_capacity(4096) };
    let v = code(&mut spine, None);
    quote_iter(bump, &mut spine, v)
}

/// 便捷入口：import + compile + normalize 一步完成（计时含转换成本）。
pub(crate) fn normalize(t: Term) -> Term {
    let bump = Bump::new();
    let tm = bump_arena::import_iter(&bump, &t);
    let code = compile(&bump, tm);
    bump_arena::export(normalize_compiled(&bump, code))
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
        // (λf.λx. f (f x)) (λu.u) → λx. x：链头指向闭包 → β 岔路
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
}
