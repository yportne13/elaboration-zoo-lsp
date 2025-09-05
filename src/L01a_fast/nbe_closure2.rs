use std::{num::NonZeroUsize, rc::Rc};

use crate::{L01a_fast::list_arena::ListArena};


#[derive(Debug, Clone)]
pub enum Value {
    Lvl(usize),
    Lam(NonZeroUsize, Vec<u8>),
    App(Rc<Value>, Rc<Value>),
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
fn eval<'a>(env: NonZeroUsize, tm: &'a [u8], arena: &mut ListArena<Value>) -> (Value, &'a [u8]) {
    /*println!(
        "eval: [{}] {:?}",
        env.iter().map(|x| format!("{:?}", x)).reduce(|a, b| a + ", " + &b).unwrap_or(String::new()),
        tm,
    );*/
    //let tag = unsafe { *tm.get_unchecked(tm.len() - 1) };
    match tm {
        [0, a0, a1, a2, a3, a4, a5, a6, a7, tail @ ..] => {
            let idx = usize::from_le_bytes([*a0, *a1, *a2, *a3, *a4, *a5, *a6, *a7]);
            let value = arena.nth(env, idx).clone();
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
            let (value1, remaining_tm) = eval(env, tail, arena);
            let (value2, final_tm) = eval(env, remaining_tm, arena);
            let result = apply_val(value1, value2, arena);
            (result, final_tm)
        },
        _ => unsafe { std::hint::unreachable_unchecked() },
    }
}

/// apply_val vf va =
///      match vf with
///      | VLam(env, body) -> eval (va :: env) body
///      | _               -> VApp(vf, va)
fn apply_val(vf: Value, va: Value, arena: &mut ListArena<Value>) -> Value {
    match vf {
        Value::Lam(env, body) => eval(
            arena.prepend(env, va),
            &body,//TODO:no need to get tail length and split right?
            arena
        ).0,
        _ => Value::App(Rc::new(vf), Rc::new(va)),
    }
}

/// quote level value =
///      match value with
///      | VLvl lvl        -> Idx(level - lvl - 1)
///      | VLam(env, body) -> Lam(quote (level + 1) @@ eval (VLvl level :: env) body)
///      | VApp(vf, va)    -> App(quote level vf, quote level va)
fn quote(level: usize, value: Rc<Value>, arena: &mut ListArena<Value>) -> Vec<u8> {
    let mut ret = Vec::with_capacity(9);
    quote_append(level, value, &mut ret, arena);
    ret
}

fn quote_append(level: usize, value: Rc<Value>, ret: &mut Vec<u8>, arena: &mut ListArena<Value>) {
    match value.as_ref() {
        Value::Lvl(lvl) => {
            ret.push(0);
            ret.extend_from_slice(&(level - lvl - 1).to_le_bytes());
        },
        Value::Lam(env, body) => {
            // 构造闭包体的值
            let (evaluated_body, _) = eval(arena.prepend(*env, Value::Lvl(level)), body, arena);

            // 写 tag 和占位长度
            let pos = ret.len();
            ret.push(1); // tag
            ret.extend_from_slice(&(0u64).to_le_bytes()); // 占位长度

            // 递归写入 body 到 ret 中
            quote_append(level + 1, evaluated_body.into(), ret, arena);

            // 回填长度
            let len = (ret.len() - pos - 9) as u64;
            //ret[pos + 1..pos + 9].copy_from_slice(&len.to_le_bytes());
            unsafe {
                (ret.as_mut_ptr().add(pos + 1) as *mut u64).write_unaligned(len.to_le());
            }
        },
        Value::App(vf, va) => {
            ret.push(2);
            quote_append(level, vf.clone(), ret, arena);
            quote_append(level, va.clone(), ret, arena);
        },
    }
}

pub fn normalize(t: Vec<u8>, arena: &mut ListArena<Value>) -> Vec<u8> {
    quote(0, eval(unsafe {NonZeroUsize::new_unchecked(1)}, &t, arena).0.into(), arena)
}
