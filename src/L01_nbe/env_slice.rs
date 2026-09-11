//! 环境改为 **bump 分配的数组切片**（`&'a [BvS<'a>]`）：`nth` 变成 O(1)
//! 下标访问，不再沿 `Env` 链表逐节点走。`prepend`（进体/apply 时）=
//! `alloc_slice_fill_copy` 复制旧环境 + 新值插头部——复制成本与当前环境
//! 深度成正比；教堂数负载的环境深度恒定（≤4），每步复制就是几个字。
//!
//! `BvS` 是 `Bv` 的切片版：`Clo` 的环境字段直接存切片（空环境 = `&[]`），
//! 且实现了 `Copy`（全指针字段），切片读写无 `clone()` 调用点。

use bumpalo::Bump;

use super::bump_arena::{self, Bt};
use super::term::Term;

/// 切片环境版的值（全指针字段，位拷贝即安全）。
#[derive(Clone, Copy)]
enum BvS<'a> {
    Lvl(usize),
    Clo(&'a [BvS<'a>], &'a Bt<'a>),
    App(&'a BvS<'a>, &'a BvS<'a>),
}

/// 环境扩展：`[v] ++ env`（复制旧环境，新值在头部）。
fn prepend<'a>(bump: &'a Bump, env: &'a [BvS<'a>], v: BvS<'a>) -> &'a [BvS<'a>] {
    let dst = bump.alloc_slice_fill_copy(env.len() + 1, BvS::Lvl(0)); // 占位
    dst[0] = v;
    dst[1..].copy_from_slice(env);
    dst
}

/// eval env tm =
///      match tm with
///      | Idx idx   -> List.nth env idx（此处为 O(1) 下标）
///      | Lam tm'   -> VLam(env, tm')
///      | App(f, a) -> apply_val (eval env f) (eval env a)
fn eval<'a>(bump: &'a Bump, env: &'a [BvS<'a>], tm: &'a Bt<'a>) -> BvS<'a> {
    match tm {
        Bt::Idx(idx) => env[*idx],
        Bt::Lam(body) => BvS::Clo(env, body),
        Bt::App(f, a) => {
            // 顺序求值（先函数后实参），与 bump_tree 同序
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
fn apply_val<'a>(bump: &'a Bump, vf: BvS<'a>, va: BvS<'a>) -> BvS<'a> {
    match vf {
        BvS::Clo(env, body) => eval(bump, prepend(bump, env, va), body),
        // 中立项：一次分配 [BvS; 2]（相邻存放）再拆引用
        _ => {
            let arr = bump.alloc([vf, va]);
            BvS::App(&arr[0], &arr[1])
        },
    }
}

/// quote level value =
///      match value with
///      | VLvl lvl        -> Idx(level - lvl - 1)
///      | VLam(env, body) -> Lam(quote (level + 1) @@ eval (VLvl level :: env) body)
///      | VApp(vf, va)    -> App(quote level vf, quote level va)
fn quote<'a>(bump: &'a Bump, level: usize, value: BvS<'a>) -> &'a Bt<'a> {
    match value {
        BvS::Lvl(lvl) => bump.alloc(Bt::Idx(level - lvl - 1)),
        BvS::Clo(env, body) => {
            let env2 = prepend(bump, env, BvS::Lvl(level));
            let body = quote(bump, level + 1, eval(bump, env2, body));
            bump.alloc(Bt::Lam(body))
        },
        BvS::App(vf, va) => {
            let f = quote(bump, level, *vf);
            let a = quote(bump, level, *va);
            bump.alloc(Bt::App(f, a))
        },
    }
}

/// 对已导入 bump 的项做 NBE（基准计时对象；import 在计时外）。
pub(crate) fn normalize_imported<'a>(bump: &'a Bump, tm: &'a Bt<'a>) -> &'a Bt<'a> {
    quote(bump, 0, eval(bump, &[], tm))
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