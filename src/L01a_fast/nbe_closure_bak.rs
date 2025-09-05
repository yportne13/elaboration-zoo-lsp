use crate::{list::List};


#[derive(Debug, Clone)]
enum Value {
    Lvl(usize),
    Lam(List<Value>, Vec<u8>),
    App(Box<Value>, Box<Value>),
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
    let tag = tm.pop().unwrap();
    
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
            let term_bytes = tm[term_start..].to_vec();
            tm.truncate(term_start);
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

fn eval_uncheck(env: List<Value>, mut tm: Vec<u8>) -> Value {
    /*println!(
        "eval: [{}] {:?}",
        env.iter().map(|x| format!("{:?}", x)).reduce(|a, b| a + ", " + &b).unwrap_or(String::new()),
        tm,
    );*/
    //let tag = unsafe { *tm.get_unchecked(tm.len() - 1) };
    let tag = tm.pop().unwrap();
    
    match tag {
        0 => {
            // Idx case: read 8 bytes as usize
            let mut idx_bytes = [0u8; 8];
            let start = tm.len() - 8;
            idx_bytes.copy_from_slice(unsafe { tm.get_unchecked(start..start + 8) });
            let idx = usize::from_le_bytes(idx_bytes);
            let value = env.iter().nth(idx).unwrap().clone();
            value
        },
        1 => {
            // Lam case: read length (8 bytes) and extract term
            let mut len_bytes = [0u8; 8];
            let start = tm.len() - 8;
            len_bytes.copy_from_slice(unsafe { tm.get_unchecked(start..start + 8) });
            tm.truncate(start);
            let len = u64::from_le_bytes(len_bytes) as usize;
            let term_start = tm.len() - len;
            let term_bytes = tm[term_start..].to_vec();
            Value::Lam(env, term_bytes)
        },
        2 => {
            // App case: this is tricky, we need to parse two terms from the combined bytes
            // This requires more context about how the terms were combined
            // For now, let's use a simplified approach
            // In practice, you'd want to parse this more carefully
            let (value2, remaining_tm) = eval(env.clone(), tm);
            let value1 = eval_uncheck(env, remaining_tm);
            apply_val(value1, value2)
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
        Value::Lam(env, body) => eval_uncheck(env.prepend(va), body),
        _ => Value::App(Box::new(vf), Box::new(va)),
    }
}

/// quote level value =
///      match value with
///      | VLvl lvl        -> Idx(level - lvl - 1)
///      | VLam(env, body) -> Lam(quote (level + 1) @@ eval (VLvl level :: env) body)
///      | VApp(vf, va)    -> App(quote level vf, quote level va)
fn quote(level: usize, value: Value) -> Vec<u8> {
    match value {
        Value::Lvl(lvl) => {
            let mut ret = (level - lvl - 1).to_le_bytes().to_vec();
            ret.push(0);
            ret
        },
        Value::Lam(env, body) => {
            let mut ret = quote(
                level + 1,
                eval_uncheck(env.prepend(Value::Lvl(level)), body)
            );
            let len = ret.len() as u64;
            ret.extend_from_slice(&len.to_le_bytes());
            ret.push(1);
            ret
        },
        Value::App(vf, va) => {
            let mut ret = quote(level, *vf);
            ret.extend(quote(level, *va));
            ret.push(2);
            ret
        },
    }
}

pub fn normalize(t: Vec<u8>) -> Vec<u8> {
    quote(0, eval_uncheck(List::new(), t))
}
