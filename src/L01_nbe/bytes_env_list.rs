//! 第一代字节码变体：项序列化为前缀编码（`to_vec2`），求值只切 `&[u8]`。
//!
//! 遍历时不再为每个子项分配 `Term` 节点——tag 在前 8 字节跟着索引或长度，
//! `Lam` 体用长度字段 `split_at` 直接切出；环境仍是 `crate::list::List`，
//! 闭包体以 `Vec<u8>` 形式随值拷贝。

use std::rc::Rc;

use crate::list::List;

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
            // App 是前缀编码里的连续两项，函数在前、实参在后
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

pub(crate) fn normalize(t: Vec<u8>) -> Vec<u8> {
    quote(0, eval(List::new(), &t).0.into())
}