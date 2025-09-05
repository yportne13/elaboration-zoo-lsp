use std::rc::Rc;

use crate::list::List;
use super::{Term, TermRc};


#[derive(Debug, Clone)]
enum Value {
    Lvl(usize),
    Lam(List<Value>, Rc<TermRc>),
    App(Rc<Value>, Rc<Value>),
}

/// eval env tm =
///      match tm with
///      | Idx idx   -> List.nth env idx
///      | Lam tm'   -> VLam(env, tm')
///      | App(f, a) -> apply_val (eval env f) (eval env a)
fn eval(env: List<Value>, tm: Rc<TermRc>) -> Value {
    /*println!(
        "eval: [{}] {:?}",
        env.iter().map(|x| format!("{:?}", x)).reduce(|a, b| a + ", " + &b).unwrap_or(String::new()),
        tm,
    );*/
    match tm.as_ref() {
        TermRc::Idx(idx) => env.iter().nth(*idx).unwrap().clone(),
        TermRc::Lam(tm) => Value::Lam(env, tm.clone()),
        TermRc::App(f, a) => apply_val(eval(env.clone(), f.clone()), eval(env, a.clone())),
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

pub fn normalize(t: TermRc) -> Term {
    quote(0, eval(List::new(), t.into()).into())
}
