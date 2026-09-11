//! `naive` 的变体：值改为 `Rc` 骨架。
//!
//! 只有 `App(Rc<Value>, Rc<Value>)` 换成了引用计数——`App` 的 quote 走
//! `Rc` 浅拷、不再深拷贝子树，代价是每次 `Rc` 克隆多一次**非原子**计数
//! （`std::rc::Rc`）。注意 `Value::Lam(List<Value>, Term)` 的闭包体仍是
//! `Box<Term>` 树：quote 的 Lam 分支要 `body.clone()`（`eval` 按值取项），
//! 对体树深拷一次——并非所有路径都免深拷。

use std::rc::Rc;

use crate::list::List;
use super::Term;

#[derive(Debug, Clone)]
enum Value {
    Lvl(usize),
    Lam(List<Value>, Term),
    App(Rc<Value>, Rc<Value>),
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
        _ => Value::App(Rc::new(vf), Rc::new(va)),
    }
}

/// quote level value =
///      match value with
///      | VLvl lvl        -> Idx(level - lvl - 1)
///      | VLam(env, body) -> Lam(quote (level + 1) @@ eval (VLvl level :: env) body)
///      | VApp(vf, va)    -> App(quote level vf, quote level va)
fn quote(level: usize, value: Rc<Value>) -> Term {
    match value.as_ref() {
        Value::Lvl(lvl) => Term::Idx(level - lvl - 1),
        Value::Lam(env, body) => Term::Lam(
            Box::new(
                quote(
                    level + 1,
                    eval(env.prepend(Value::Lvl(level)), body.clone()).into()
                )
            )
        ),
        Value::App(vf, va) => Term::App(
            Box::new(quote(level, vf.clone())),
            Box::new(quote(level, va.clone()))
        ),
    }
}

pub(crate) fn normalize(t: Term) -> Term {
    quote(0, eval(List::new(), t).into())
}