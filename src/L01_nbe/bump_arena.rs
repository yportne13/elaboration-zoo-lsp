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

use bumpalo::Bump;

use super::Term;

/// bump 内分配的项。
pub(crate) enum Bt<'a> {
    Idx(usize),
    Lam(&'a Bt<'a>),
    App(&'a Bt<'a>, &'a Bt<'a>),
}

/// bump 内分配的环境节点（持久链表）。
struct Env<'a> {
    val: Bv<'a>,
    next: Option<&'a Env<'a>>,
}

/// bump 内分配的值。
#[derive(Clone)]
enum Bv<'a> {
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

fn nth<'a>(env: Option<&'a Env<'a>>, idx: usize) -> &'a Bv<'a> {
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
fn eval<'a>(bump: &'a Bump, env: Option<&'a Env<'a>>, tm: &'a Bt<'a>) -> Bv<'a> {
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
        // 中立项的两个子值也要进 bump 才能被引用
        _ => {
            let vf = bump.alloc(vf);
            let va = bump.alloc(va);
            Bv::App(vf, va)
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

/// 便捷入口：import + normalize 一步完成（计时含转换成本）。
pub(crate) fn normalize(t: Term) -> Term {
    let bump = Bump::new();
    let tm = import(&bump, &t);
    quote(&bump, 0, eval(&bump, None, tm))
}