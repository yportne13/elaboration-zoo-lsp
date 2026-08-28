//! 基线变体：`Box<Term>` AST + `crate::list::List` 环境 + 无 `Rc` 的值。
//!
//! 求值全程在树上递归，环境 `prepend` 每次分配一个 `Rc` 节点；
//! 值是 enum + `Box`（`App` 两个子节点各自装箱）。其余变体都在这条
//! 基线上替换一到两件东西。

use crate::list::List;
use super::Term;

#[derive(Debug, Clone)]
enum Value {
    Lvl(usize),
    Lam(List<Value>, Term),
    App(Box<Value>, Box<Value>),
}

/// eval env tm =
///      match tm with
///      | Idx idx   -> List.nth env idx
///      | Lam tm'   -> VLam(env, tm')
///      | App(f, a) -> apply_val (eval env f) (eval env a)
fn eval(env: List<Value>, tm: Term) -> Value {
    match tm {
        Term::Idx(idx) => env.iter().nth(idx).unwrap().clone(),
        Term::Lam(tm) => Value::Lam(env, *tm),
        Term::App(f, a) => apply_val(eval(env.clone(), *f), eval(env, *a)),
    }
}

/// apply_val vf va =
///      match vf with
///      | VLam(env, body) -> eval (va :: env) body
///      | _               -> VApp(vf, va)
fn apply_val(vf: Value, va: Value) -> Value {
    match vf {
        Value::Lam(env, body) => eval(env.prepend(va), body),
        _ => Value::App(Box::new(vf), Box::new(va)),
    }
}

/// quote level value =
///      match value with
///      | VLvl lvl        -> Idx(level - lvl - 1)
///      | VLam(env, body) -> Lam(quote (level + 1) @@ eval (VLvl level :: env) body)
///      | VApp(vf, va)    -> App(quote level vf, quote level va)
fn quote(level: usize, value: Value) -> Term {
    match value {
        Value::Lvl(lvl) => Term::Idx(level - lvl - 1),
        Value::Lam(env, body) => Term::Lam(
            Box::new(
                quote(
                    level + 1,
                    eval(env.prepend(Value::Lvl(level)), body)
                )
            )
        ),
        Value::App(vf, va) => Term::App(
            Box::new(quote(level, *vf)),
            Box::new(quote(level, *va))
        ),
    }
}

pub(crate) fn normalize(t: Term) -> Term {
    quote(0, eval(List::new(), t))
}