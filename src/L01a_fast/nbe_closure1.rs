use std::rc::Rc;

use crate::{list::List};


#[derive(Debug, Clone)]
enum Value {
    Lvl(usize),
    Lam(List<Value>, Vec<u8>),
    App(Rc<Value>, Rc<Value>),
}

/// eval env tm =
///      match tm with
///      | Idx idx   -> List.nth env idx
///      | Lam tm'   -> VLam(env, tm')
///      | App(f, a) -> apply_val (eval env f) (eval env a)
fn eval(env: List<Value>, tm: &[u8]) -> (Value, &[u8]) {
    /*println!(
        "eval: [{}] {:?}",
        env.iter().map(|x| format!("{:?}", x)).reduce(|a, b| a + ", " + &b).unwrap_or(String::new()),
        tm,
    );*/
    //let tag = unsafe { *tm.get_unchecked(tm.len() - 1) };
    match tm {
        [0, a0, a1, a2, a3, a4, a5, a6, a7, tail @ ..] => {
            let idx = usize::from_le_bytes([*a0, *a1, *a2, *a3, *a4, *a5, *a6, *a7]);
            let value = env.iter().nth(idx).unwrap().clone();
            (value, tail)
        },
        [1, a0, a1, a2, a3, a4, a5, a6, a7, tail @ ..] => {
            let len = usize::from_le_bytes([*a0, *a1, *a2, *a3, *a4, *a5, *a6, *a7]);
            let (tm, tail) = tail.split_at(len);
            let value = Value::Lam(env, tm.to_vec());
            (value, tail)
        },
        [2, tail @ ..] => {
            // App case: this is tricky, we need to parse two terms from the combined bytes
            // This requires more context about how the terms were combined
            // For now, let's use a simplified approach
            // In practice, you'd want to parse this more carefully
            let (value1, remaining_tm) = eval(env.clone(), tail);
            let (value2, final_tm) = eval(env, remaining_tm);
            let result = apply_val(value1, value2);
            (result, final_tm)
        },
        _ => unsafe { std::hint::unreachable_unchecked() },
    }
}

/// apply_val vf va =
///      match vf with
///      | VLam(env, body) -> eval (va :: env) body
///      | _               -> VApp(vf, va)
fn apply_val(vf: Value, va: Value) -> Value {
    match vf {
        Value::Lam(env, body) => eval(env.prepend(va), &body).0,
        _ => Value::App(Rc::new(vf), Rc::new(va)),
    }
}

/// quote level value =
///      match value with
///      | VLvl lvl        -> Idx(level - lvl - 1)
///      | VLam(env, body) -> Lam(quote (level + 1) @@ eval (VLvl level :: env) body)
///      | VApp(vf, va)    -> App(quote level vf, quote level va)
fn quote(level: usize, value: Rc<Value>) -> Vec<u8> {
    let mut ret = Vec::with_capacity(9);
    quote_append(level, value, &mut ret);
    ret
}

fn quote_append(level: usize, value: Rc<Value>, ret: &mut Vec<u8>) {
    match value.as_ref() {
        Value::Lvl(lvl) => {
            ret.push(0);
            ret.extend_from_slice(&(level - lvl - 1).to_le_bytes());
        },
        Value::Lam(env, body) => {
            let t = quote(
                level + 1,
                eval(env.prepend(Value::Lvl(level)), body).0.into()
            );
            let len = t.len() as u64;
            ret.push(1);
            ret.extend_from_slice(&len.to_le_bytes());
            ret.extend(t);
        },
        Value::App(vf, va) => {
            ret.push(2);
            quote_append(level, vf.clone(), ret);
            quote_append(level, va.clone(), ret);
        },
    }
}

pub fn normalize(t: Vec<u8>) -> Vec<u8> {
    quote(0, eval(List::new(), &t).0.into())
}
