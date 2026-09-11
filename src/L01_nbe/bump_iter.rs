//! `bump_tree` 的迭代改造（双栈推土机）：递归 eval 压平为显式双栈，
//! 求值深度不受进程栈限，代码结构与 `bump_tree` 一一对应。
//!
//! bump_tree 的 eval 递归结构是"求 f → 求 a → apply"，β 归约是纯尾调用。
//! 压平为**双栈**：
//!
//! ```text
//! work 栈：Tm(&Bt, env)     待求值的项
//!         Apply            值栈顶两个值做一次应用（每个 App 推入一枚）
//! vals 栈：Bv              已求出的值（LIFO 与 work 的 Apply 配对）
//! ```
//!
//! 与 `cek_bump` 的通用 CEK kont 栈（`Fun`/`Arg` 两条）相比：栈条目种类
//! 更少、β 归约不再产生额外条目（归约 = 直接推入体的 `Tm`，天然循环）。
//! quote 复用 `super::bump_tree::quote_bump_iter`（任务栈）。

use bumpalo::Bump;

use super::bump_arena::{self, Bt, Bv, Env};
use super::term::Term;

/// 双栈迭代 eval：与 `bump_arena::eval` 语义相同（先函数后实参）。
/// 公开给 [`super::bump_tree::quote_bump_iter`]——quote 强制闭包体时必须用
/// 迭代版（递归版在深链上吃线性机器栈，是旧"51 万+ 栈消耗"悬案的元凶）。
pub(crate) fn eval<'a>(
    bump: &'a Bump,
    env0: Option<&'a Env<'a>>,
    tm0: &'a Bt<'a>,
) -> Bv<'a> {
    enum W<'a> {
        Tm(&'a Bt<'a>, Option<&'a Env<'a>>),
        Apply,
    }
    let mut work: Vec<W<'a>> = vec![W::Tm(tm0, env0)];
    let mut vals: Vec<Bv<'a>> = Vec::new();
    while let Some(w) = work.pop() {
        match w {
            W::Tm(tm, env) => match tm {
                Bt::Idx(i) => vals.push(bump_arena::nth(env, *i).clone()),
                Bt::Lam(body) => vals.push(Bv::Clo(env, body)),
                Bt::App(f, a) => {
                    work.push(W::Apply);
                    work.push(W::Tm(a, env));
                    work.push(W::Tm(f, env));
                },
            },
            W::Apply => {
                let va = vals.pop().expect("eval 栈：Apply 缺实参");
                let vf = vals.pop().expect("eval 栈：Apply 缺函数");
                match vf {
                    // β 归约是尾调用：直接推入体，继续循环（无额外栈条目）
                    Bv::Clo(e, body) => {
                        let node = bump.alloc(Env { val: va, next: e });
                        work.push(W::Tm(body, Some(node)));
                    },
                    // 中立项：一次分配 [Bv; 2]（相邻存放），拆引用后回值栈
                    f => {
                        let arr = bump.alloc([f, va]);
                        vals.push(Bv::App(&arr[0], &arr[1]));
                    },
                }
            },
        }
    }
    vals.pop().expect("eval 必须恰有一个根值")
}

/// 对已导入 bump 的项做 NBE（基准计时对象；import 在计时外）。
/// eval（双栈迭代）+ quote（任务栈迭代）都深度无上限。
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