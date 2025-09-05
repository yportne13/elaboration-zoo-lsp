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
fn eval(env: List<Value>, mut tm: Vec<u8>) -> (Value, Vec<u8>) {
    /*println!(
        "eval: [{}] {:?}",
        env.iter().map(|x| format!("{:?}", x)).reduce(|a, b| a + ", " + &b).unwrap_or(String::new()),
        tm,
    );*/
    //let tag = unsafe { *tm.get_unchecked(tm.len() - 1) };
    let tag = unsafe {tm.pop().unwrap_unchecked()};
    
    match tag {
        0 => {
            // Idx case: read 8 bytes as usize
            let mut idx_bytes = [0u8; 8];
            let start = tm.len() - 8;
            idx_bytes.copy_from_slice(unsafe { tm.get_unchecked(start..start + 8) });
            tm.truncate(start);
            let idx = usize::from_le_bytes(idx_bytes);
            let value = env.iter().nth(idx).unwrap().clone();
            (value, tm)
        },
        1 => {
            // Lam case: read length (8 bytes) and extract term
            let mut len_bytes = [0u8; 8];
            let start = tm.len() - 8;
            len_bytes.copy_from_slice(unsafe { tm.get_unchecked(start..start + 8) });
            tm.truncate(start);
            let len = u64::from_le_bytes(len_bytes) as usize;
            let term_start = tm.len() - len;
            let term_bytes = tm.split_off(term_start);
            let value = Value::Lam(env, term_bytes);
            (value, tm)
        },
        2 => {
            // App case: this is tricky, we need to parse two terms from the combined bytes
            // This requires more context about how the terms were combined
            // For now, let's use a simplified approach
            // In practice, you'd want to parse this more carefully
            let (value2, remaining_tm) = eval(env.clone(), tm);
            let (value1, final_tm) = eval(env, remaining_tm);
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
        Value::Lam(env, body) => eval(env.prepend(va), body).0,
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
            ret.extend((level - lvl - 1).to_le_bytes());
            ret.push(0);
        },
        Value::Lam(env, body) => {
            let x = quote(
                level + 1,
                eval(env.prepend(Value::Lvl(level)), body.to_vec()).0.into(),
            );
            let len = x.len() as u64;
            ret.extend(x);
            ret.extend_from_slice(&len.to_le_bytes());
            ret.push(1);
        },
        Value::App(vf, va) => {
            quote_append(level, vf.clone(), ret);
            quote_append(level, va.clone(), ret);
            ret.push(2);
        },
    }
}

pub fn normalize(t: Vec<u8>) -> Vec<u8> {
    quote(0, eval(List::new(), t).0.into())
}
