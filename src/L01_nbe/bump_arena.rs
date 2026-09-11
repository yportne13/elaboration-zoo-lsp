//! bumpalo 全 arena 版：**项、值、环境节点全部 bump 分配**（`bumpalo::Bump`），
//! 引用式数据结构——没有 `Rc` 计数、没有 `Box` 析构，分配只是指针推进，
//! 整块 `Bump` 在 normalize 结束时一起释放。
//!
//! ```text
//! Bt< 'a>  项（bump 内）：Idx / Lam(&Bt) / App(&Bt, &Bt)
//! Env<'a>  环境（bump 内持久链表）：{ val: Bv, next: Option<&Env> }
//! Bv< 'a>  值（bump 内）：Lvl / Clo(&Env, &Bt) / App(&Bv, &Bv)
//! ```
//!
//! 生命周期 `'a` 贯穿同一个 `Bump`；闭包捕获的环境就是 `&'a Env` 链表头。
//! 与下标式 `ListArena` 的取舍：引用省掉 `nth` 的查表间接，代价是闭包/值
//! 的 `Clone` 只是浅拷引用（这点和 `Rc` 一致）。
//!
//! 本文件同时是 bump 系变体的公共内核：`bump_tree`（结果也 bump）、
//! `cek_bump`（CEK 迭代）、`bump_iter`（双栈迭代）、`compiled`（指令数组）
//! 复用这里的 `Bt`/`Env`/`Bv`/`eval`/`import`/`export`；`env_slice`（切片
//! 环境）只复用 `Bt` 与 `import`/`export`，自带切片版值/环境/`eval`。

use bumpalo::Bump;

use super::Term;

/// bump 内分配的项。
pub(crate) enum Bt<'a> {
    Idx(usize),
    Lam(&'a Bt<'a>),
    App(&'a Bt<'a>, &'a Bt<'a>),
}

/// bump 内分配的环境节点（持久链表）。
pub(crate) struct Env<'a> {
    pub(crate) val: Bv<'a>,
    pub(crate) next: Option<&'a Env<'a>>,
}

/// bump 内分配的值。全指针字段——位拷贝即安全，`Copy` 让数组化环境
/// （`env_slice`）的切片操作免去 `clone()` 调用点。
#[derive(Clone, Copy)]
pub(crate) enum Bv<'a> {
    Lvl(usize),
    Clo(Option<&'a Env<'a>>, &'a Bt<'a>),
    App(&'a Bv<'a>, &'a Bv<'a>),
}

/// 把 `Box<Term>` 树导入 bump（基准里放在计时外，与其他变体的编码同口径）。
pub(crate) fn import<'a>(bump: &'a Bump, t: &Term) -> &'a Bt<'a> {
    match t {
        Term::Idx(i) => bump.alloc(Bt::Idx(*i)),
        Term::Lam(body) => bump.alloc(Bt::Lam(import(bump, body))),
        Term::App(f, a) => bump.alloc(Bt::App(import(bump, f), import(bump, a))),
    }
}

/// 迭代版 import：任务栈 + 已完成节点栈（与 `quote_bump_iter` 镜像）。
/// 递归版在树深百万级（大 n 的 cek_bump 场景）会爆栈，这里只走自己的栈。
pub(crate) fn import_iter<'a>(bump: &'a Bump, t: &Term) -> &'a Bt<'a> {
    enum J<'a> {
        Do(&'a Term),
        Lam2,
        App2,
    }
    let mut tasks: Vec<J<'_>> = vec![J::Do(t)];
    let mut done: Vec<&'a Bt<'a>> = Vec::new();
    while let Some(j) = tasks.pop() {
        match j {
            J::Do(Term::Idx(i)) => done.push(bump.alloc(Bt::Idx(*i))),
            J::Do(Term::Lam(b)) => {
                tasks.push(J::Lam2);
                tasks.push(J::Do(b));
            },
            J::Do(Term::App(f, a)) => {
                tasks.push(J::App2);
                tasks.push(J::Do(a));
                tasks.push(J::Do(f));
            },
            J::Lam2 => {
                let b = done.pop().expect("import 栈：Lam 缺体");
                done.push(bump.alloc(Bt::Lam(b)));
            },
            J::App2 => {
                let a = done.pop().expect("import 栈：App 缺实参");
                let f = done.pop().expect("import 栈：App 缺函数");
                done.push(bump.alloc(Bt::App(f, a)));
            },
        }
    }
    done.pop().expect("import 必须恰有一个根")
}

pub(crate) fn nth<'a>(env: Option<&'a Env<'a>>, idx: usize) -> &'a Bv<'a> {
    let mut e = env.expect("de Bruijn 越界：闭项不应查空环境");
    for _ in 0..idx {
        e = e.next.expect("de Bruijn 越界：闭项不应查越深");
    }
    &e.val
}

/// eval env tm =
///      match tm with
///      | Idx idx   -> List.nth env idx
///      | Lam tm'   -> VLam(env, tm')
///      | App(f, a) -> apply_val (eval env f) (eval env a)
pub(crate) fn eval<'a>(bump: &'a Bump, env: Option<&'a Env<'a>>, tm: &'a Bt<'a>) -> Bv<'a> {
    match tm {
        Bt::Idx(idx) => nth(env, *idx).clone(),
        Bt::Lam(body) => Bv::Clo(env, body),
        Bt::App(f, a) => {
            // 顺序求值（先函数后实参），与 naive 同序
            let vf = eval(bump, env, f);
            let va = eval(bump, env, a);
            apply_val(bump, vf, va)
        },
    }
}

/// apply_val vf va =
///      match vf with
///      | VLam(env, body) -> eval (va :: env) body
///      | _               -> VApp(vf, va)
fn apply_val<'a>(bump: &'a Bump, vf: Bv<'a>, va: Bv<'a>) -> Bv<'a> {
    match vf {
        Bv::Clo(env, body) => {
            let node = bump.alloc(Env { val: va, next: env });
            eval(bump, Some(node), body)
        },
        // 中立项的两个子值也要进 bump 才能被引用；一次分配 [Bv; 2]
        // （相邻存放，单次对齐/检查/推进）再拆引用
        _ => {
            let arr = bump.alloc([vf, va]);
            Bv::App(&arr[0], &arr[1])
        },
    }
}

/// quote level value =
///      match value with
///      | VLvl lvl        -> Idx(level - lvl - 1)
///      | VLam(env, body) -> Lam(quote (level + 1) @@ eval (VLvl level :: env) body)
///      | VApp(vf, va)    -> App(quote level vf, quote level va)
fn quote<'a>(bump: &'a Bump, level: usize, value: Bv<'a>) -> Term {
    match value {
        Bv::Lvl(lvl) => Term::Idx(level - lvl - 1),
        Bv::Clo(env, body) => {
            let node = bump.alloc(Env { val: Bv::Lvl(level), next: env });
            let body = eval(bump, Some(node), body);
            Term::Lam(Box::new(quote(bump, level + 1, body)))
        },
        Bv::App(vf, va) => Term::App(
            Box::new(quote(bump, level, vf.clone())),
            Box::new(quote(bump, level, va.clone())),
        ),
    }
}

/// 对已导入 bump 的项做 NBE（基准的计时对象，import 在计时外）。
/// `bump` 与 `tm` 必须同源（`import` 的产物）。
pub(crate) fn normalize_imported<'a>(bump: &'a Bump, tm: &'a Bt<'a>) -> Term {
    quote(bump, 0, eval(bump, None, tm))
}

/// 把 bump 内结果树转回 `Box<Term>`（递归；仅用于断言/消费侧，不计时）。
pub(crate) fn export(t: &Bt) -> Term {
    match t {
        Bt::Idx(i) => Term::Idx(*i),
        Bt::Lam(b) => Term::Lam(Box::new(export(b))),
        Bt::App(f, a) => Term::App(Box::new(export(f)), Box::new(export(a))),
    }
}

/// 便捷入口：import + normalize 一步完成（计时含转换成本）。
#[allow(dead_code)] // 仅供单测：bench 走 normalize_imported
pub(crate) fn normalize(t: Term) -> Term {
    let bump = Bump::new();
    let tm = import(&bump, &t);
    quote(&bump, 0, eval(&bump, None, tm))
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