//! 结果树也留在 bump 里（`bump_tree` 变体）：求值 + 结果生成全程零
//! Rust 堆分配（quote 不再 `Box::new`），需要 `Box<Term>` 时再 `export`
//! （基准把它放在计时外）。公共内核（`Bt`/`Env`/`Bv`/`eval`/`import`/
//! `export`）在 [`super::bump_arena`]。
//!
//! quote 保持递归：实测迭代版（显式任务栈）反而慢 30%——Vec 栈的边界
//! 检查与容量管理比机器栈帧贵。深度无上限的场景（`cek_bump`/`bump_iter`）
//! 用 `quote_bump_iter`。

use bumpalo::Bump;

use super::bump_arena::{self, Bt, Bv, Env};
use super::term::Term;

/// 对已导入 bump 的项做 NBE（基准计时对象；import 在计时外）。
pub(crate) fn normalize_imported<'a>(bump: &'a Bump, tm: &'a Bt<'a>) -> &'a Bt<'a> {
    // eval 只做 O(λ) 步（church_pair 直接出闭包），重活全在 quote 的 Clo 重入
    quote_bump(bump, 0, bump_arena::eval(bump, None, tm))
}

/// 便捷入口：import + normalize 一步完成（计时含转换成本）。
pub(crate) fn normalize(t: Term) -> Term {
    let bump = Bump::new();
    let tm = bump_arena::import(&bump, &t);
    bump_arena::export(normalize_imported(&bump, tm))
}

fn quote_bump<'a>(bump: &'a Bump, level: usize, value: Bv<'a>) -> &'a Bt<'a> {
    match value {
        Bv::Lvl(lvl) => bump.alloc(Bt::Idx(level - lvl - 1)),
        Bv::Clo(env, body) => {
            let node = bump.alloc(Env { val: Bv::Lvl(level), next: env });
            let body = quote_bump(bump, level + 1, bump_arena::eval(bump, Some(node), body));
            bump.alloc(Bt::Lam(body))
        },
        Bv::App(vf, va) => {
            let f = quote_bump(bump, level, vf.clone());
            let a = quote_bump(bump, level, va.clone());
            bump.alloc(Bt::App(f, a))
        },
    }
}

/// 迭代 quote：任务栈 + 已完成节点栈，后续遍历。App spine 两万层深也只走
/// 自己的栈，不占硬件栈——递归版（`quote_bump`）更快，深度无上限的场景
/// （`cek_bump`/`bump_iter`）用本函数。
pub(crate) fn quote_bump_iter<'a>(bump: &'a Bump, v0: Bv<'a>) -> &'a Bt<'a> {
    enum QJob<'a> {
        Q(Bv<'a>, usize),
        Lam1,
        App1,
        EvalThenQ(&'a Bt<'a>, Option<&'a Env<'a>>, usize),
    }
    let mut tasks: Vec<QJob<'a>> = vec![QJob::Q(v0, 0)];
    let mut done: Vec<&'a Bt<'a>> = Vec::new();
    while let Some(job) = tasks.pop() {
        match job {
            QJob::Q(Bv::Lvl(lvl), level) => {
                done.push(bump.alloc(Bt::Idx(level - lvl - 1)));
            },
            QJob::Q(Bv::Clo(env, body), level) => {
                let node = bump.alloc(Env { val: Bv::Lvl(level), next: env });
                tasks.push(QJob::Lam1);
                tasks.push(QJob::EvalThenQ(body, Some(node), level + 1));
            },
            QJob::Q(Bv::App(vf, va), level) => {
                tasks.push(QJob::App1);
                tasks.push(QJob::Q(va.clone(), level));
                tasks.push(QJob::Q(vf.clone(), level));
            },
            QJob::Lam1 => {
                let body = done.pop().expect("quote 栈：Lam 缺体");
                done.push(bump.alloc(Bt::Lam(body)));
            },
            QJob::App1 => {
                let a = done.pop().expect("quote 栈：App 缺实参");
                let f = done.pop().expect("quote 栈：App 缺函数");
                done.push(bump.alloc(Bt::App(f, a)));
            },
            QJob::EvalThenQ(body, env, level) => {
                let v = bump_arena::eval(bump, env, body);
                tasks.push(QJob::Q(v, level));
            },
        }
    }
    done.pop().expect("quote 必须恰有一个根")
}

