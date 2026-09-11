//! CEK 机 + bump 全分配：求值深度无上限，同时保留 bump 的速度。
//!
//! 求值 = 显式 kont 栈的 CEK 机（深度不受进程栈限），值/环境/结果 =
//! bump 引用式（零 malloc）。quote 用任务栈迭代
//! （`super::bump_tree::quote_bump_iter`）——递归版会以结果树深度爆栈。
//! 实测：速度 ≈ 递归版 `bump_tree` 的 1.2×，深度与 `cek` 同级（n = 51 万
//! 线性可跑，见 readme）。

use bumpalo::Bump;

use super::bump_arena::{self, Bt, Bv, Env};
use super::term::Term;

/// continuation 栈条目。
enum Kont<'a> {
    /// 函数已求得，实参待求值（实参项 + 其求值环境）。
    Fun(&'a Bt<'a>, Option<&'a Env<'a>>),
    /// 实参已求得（值），等函数来应用。
    Arg(Bv<'a>),
}

/// eval env tm = …（递归定义，见 `cek.rs` 的转移规则注释）。
/// bump 版的差异：env 是 bump 内持久链表（`&Env`），值在 bump 内引用式。
fn eval<'a>(bump: &'a Bump, env0: Option<&'a Env<'a>>, tm0: &'a Bt<'a>) -> Bv<'a> {
    let mut env = env0;
    let mut tm: Option<&'a Bt<'a>> = Some(tm0);
    let mut val: Option<Bv<'a>> = None;
    let mut kont: Vec<Kont<'a>> = Vec::new();

    loop {
        if let Some(t) = tm.take() {
            match t {
                Bt::Idx(i) => val = Some(bump_arena::nth(env, *i).clone()),
                Bt::Lam(body) => val = Some(Bv::Clo(env, body)),
                Bt::App(f, a) => {
                    kont.push(Kont::Fun(a, env));
                    tm = Some(f);
                },
            }
            continue; // 转值状态
        }

        let v = val.take().expect("值状态必须持有值");
        match kont.pop() {
            Some(Kont::Fun(a, e)) => {
                env = e;
                tm = Some(a);
                kont.push(Kont::Arg(v));
            },
            Some(Kont::Arg(f)) => match f {
                Bv::Clo(e, body) => {
                    let node = bump.alloc(Env { val: v, next: e });
                    env = Some(node);
                    tm = Some(body);
                },
                // 中立项：一次分配 [Bv; 2]（相邻存放），拆引用
                f => {
                    let arr = bump.alloc([f, v]);
                    val = Some(Bv::App(&arr[0], &arr[1]));
                },
            },
            None => return v,
        }
    }
}

/// 对已导入 bump 的项做 NBE（基准计时对象；import 在计时外）。
/// eval（CEK 迭代）+ quote（任务栈迭代）都深度无上限。
pub(crate) fn normalize_imported<'a>(bump: &'a Bump, tm: &'a Bt<'a>) -> &'a Bt<'a> {
    super::bump_tree::quote_bump_iter(bump, eval(bump, None, tm))
}

/// 便捷入口：import + normalize 一步完成（计时含转换成本）。
#[allow(dead_code)] // 仅供单测：bench 走 normalize_imported
pub(crate) fn normalize(t: Term) -> Term {
    let bump = Bump::new();
    let tm = bump_arena::import(&bump, &t);
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
        // λf.λx. f (f (f (f x)))：已正态，归一化须逐字还原
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
        // λg. (λx. x) g → λg. g
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
        // (λf.λx. f (f x)) (λu.u) → λx. x
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
        // λf.λg.λx. f (g x)：连续右链、链头不同
        let idx = |i: usize| Term::Idx(i);
        let app = |f: Term, a: Term| Term::App(Box::new(f), Box::new(a));
        let lam = |b: Term| Term::Lam(Box::new(b));
        let input = lam(lam(lam(app(idx(2), app(idx(1), idx(0))))));
        assert_eq!(normalize(input.clone()), input);
    }
}