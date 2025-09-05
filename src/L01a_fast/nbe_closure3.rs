use std::num::NonZeroUsize;

use super::list_arena::ListArena;


#[derive(Debug, Clone, Default)]
pub struct Value(Vec<u8>);

impl Value {
    fn lvl(l: usize) -> Self {
        Value({
            let mut ret = Vec::with_capacity(9);
            ret.push(0);
            ret.extend_from_slice(&l.to_le_bytes());
            ret
        })
    }
}

//enum Value {
//    Lvl(usize),
//    Lam(List<Value>, Vec<u8>),
//    App(Box<Value>, Box<Value>),
//}

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
            let mut value = Vec::with_capacity(25 + tm.len());
            value.push(1);
            value.extend(env.get().to_le_bytes());
            value.extend(tm.len().to_le_bytes());
            value.extend(tm);
            (Value(value), tail)
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
    match &vf.0[..] {
        [
            1, a0, a1, a2, a3, a4, a5, a6, a7,
            b0, b1, b2, b3, b4, b5, b6, b7,
            tail @ ..
        ] => eval(
            arena.prepend(unsafe { NonZeroUsize::new_unchecked(usize::from_le_bytes([*a0, *a1, *a2, *a3, *a4, *a5, *a6, *a7])) }, va),
            tail,//TODO:no need to get tail length and split right?
            arena
        ).0,
        [1, ..] => unsafe { std::hint::unreachable_unchecked() },
        _ => Value({
            let mut ret = Vec::with_capacity(1 + vf.0.len() + va.0.len());
            ret.push(2);
            ret.extend(vf.0);
            ret.extend(va.0);
            ret
        }),
    }
}

/// quote level value =
///      match value with
///      | VLvl lvl        -> Idx(level - lvl - 1)
///      | VLam(env, body) -> Lam(quote (level + 1) @@ eval (VLvl level :: env) body)
///      | VApp(vf, va)    -> App(quote level vf, quote level va)
fn quote<'a>(level: usize, value: &'a [u8], arena: &mut ListArena<Value>) -> (Vec<u8>, &'a [u8]) {
    let mut ret = Vec::with_capacity(9);
    let t = quote_append(level, value, &mut ret, arena);
    (ret, t)
}

fn quote_append<'a>(level: usize, value: &'a [u8], ret: &mut Vec<u8>, arena: &mut ListArena<Value>) -> &'a [u8] {
    match value {
        [0, a0, a1, a2, a3, a4, a5, a6, a7, tail @ ..] => {
            let lvl = usize::from_le_bytes([*a0, *a1, *a2, *a3, *a4, *a5, *a6, *a7]);
            ret.push(0);
            ret.extend_from_slice(&(level - lvl - 1).to_le_bytes());
            tail
        },
        [
            1, a0, a1, a2, a3, a4, a5, a6, a7,
            b0, b1, b2, b3, b4, b5, b6, b7,
            tail @ ..
        ] => {
            let env = unsafe { NonZeroUsize::new_unchecked(usize::from_le_bytes([*a0, *a1, *a2, *a3, *a4, *a5, *a6, *a7])) };
            let (body, tail) = tail.split_at(usize::from_le_bytes([*b0, *b1, *b2, *b3, *b4, *b5, *b6, *b7]));
            let t = quote(
                level + 1,
                &eval(arena.prepend(env, Value::lvl(level)), body, arena).0.0,
                arena,
            ).0;
            let len = t.len() as u64;
            ret.push(1);
            ret.extend_from_slice(&len.to_le_bytes());
            ret.extend(t);
            tail
        },
        [2, tail @ ..] => {
            ret.push(2);
            let tail = quote_append(level, tail, ret, arena);
            quote_append(level, tail, ret, arena)
        },
        _ => unsafe { std::hint::unreachable_unchecked() },
    }
}

pub fn normalize(t: Vec<u8>, arena: &mut ListArena<Value>) -> Vec<u8> {
    quote(0, &eval(unsafe {NonZeroUsize::new_unchecked(1)}, &t, arena).0.0, arena).0
}
