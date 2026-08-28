//! `naive` 的 arena 演进：环境从 `Rc` 持久链表换成 `ListArena`（下标式
//! typed-arena 持久链表，见 [`super::persistent_list`]）；项与值保持原样
//! （`Box<Term>` AST + enum + `Box`）。
//!
//! 与 `bytes_env_arena` 的唯一差别是**项未序列化**——两个变体对读，正好
//! 隔离"环境 arena 化的收益是否独立于项表示"。实测：收益差不多，arena
//! 环境在两种项表示上各带来 ~1.3×。

use std::num::NonZeroUsize;

use super::persistent_list::ListArena;
use super::Term;

#[derive(Debug, Clone)]
pub(crate) enum Value {
    Lvl(usize),
    Lam(NonZeroUsize, Term),
    App(Box<Value>, Box<Value>),
}

impl Default for Value {
    fn default() -> Self {
        Value::Lvl(0)
    }
}

/// eval env tm =
///      match tm with
///      | Idx idx   -> List.nth env idx
///      | Lam tm'   -> VLam(env, tm')
///      | App(f, a) -> apply_val (eval env f) (eval env a)
fn eval(env: NonZeroUsize, tm: Term, arena: &mut ListArena<Value>) -> Value {
    match tm {
        Term::Idx(idx) => arena.nth(env, idx).clone(),
        Term::Lam(tm) => Value::Lam(env, *tm),
        Term::App(f, a) => {
            // 顺序求值（先函数后实参），与 naive 同序
            let vf = eval(env, *f, arena);
            let va = eval(env, *a, arena);
            apply_val(vf, va, arena)
        },
    }
}

/// apply_val vf va =
///      match vf with
///      | VLam(env, body) -> eval (va :: env) body
///      | _               -> VApp(vf, va)
fn apply_val(vf: Value, va: Value, arena: &mut ListArena<Value>) -> Value {
    match vf {
        Value::Lam(env, body) => eval(arena.prepend(env, va), body, arena),
        _ => Value::App(Box::new(vf), Box::new(va)),
    }
}

/// quote level value =
///      match value with
///      | VLvl lvl        -> Idx(level - lvl - 1)
///      | VLam(env, body) -> Lam(quote (level + 1) @@ eval (VLvl level :: env) body)
///      | VApp(vf, va)    -> App(quote level vf, quote level va)
fn quote(level: usize, value: Value, arena: &mut ListArena<Value>) -> Term {
    match value {
        Value::Lvl(lvl) => Term::Idx(level - lvl - 1),
        Value::Lam(env, body) => {
            let lam_body = quote(level + 1, eval(arena.prepend(env, Value::Lvl(level)), body, arena), arena);
            Term::Lam(Box::new(lam_body))
        },
        Value::App(vf, va) => Term::App(
            Box::new(quote(level, *vf, arena)),
            Box::new(quote(level, *va, arena)),
        ),
    }
}

pub(crate) fn normalize(t: Term, arena: &mut ListArena<Value>) -> Term {
    quote(0, eval(unsafe { NonZeroUsize::new_unchecked(1) }, t, arena), arena)
}