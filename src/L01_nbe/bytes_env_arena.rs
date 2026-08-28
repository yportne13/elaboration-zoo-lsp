//! 环境换成 `ListArena`（见 [`super::persistent_list`]）：`prepend` 变成
//! 追加式下标，求值不再分配 `Rc` 节点，多次求值可复用同一 arena。
//!
//! 项仍是 `to_vec2` 前缀字节码；闭包体以 `Rc<Vec<u8>>` 存进值（`Lam` 的
//! 第二字段是环境链头）。L01a 时代的 readme 判定本变体最快——该结论
//! 现在由 `typort bench` 复核（见模块 readme）。

use std::{num::NonZeroUsize, rc::Rc};

use super::persistent_list::ListArena;

#[derive(Debug, Clone)]
pub(crate) enum Value {
    Lvl(usize),
    Lam(NonZeroUsize, Rc<Vec<u8>>),
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
    match tm {
        [0, a0, a1, a2, a3, a4, a5, a6, a7, tail @ ..] => {
            let idx = usize::from_le_bytes([*a0, *a1, *a2, *a3, *a4, *a5, *a6, *a7]);
            let value = arena.nth(env, idx).clone();
            (value, tail)
        },
        [1, a0, a1, a2, a3, a4, a5, a6, a7, tail @ ..] => {
            let len = usize::from_le_bytes([*a0, *a1, *a2, *a3, *a4, *a5, *a6, *a7]);
            let (tm, tail) = tail.split_at(len);
            let value = Value::Lam(env, tm.to_vec().into());
            (value, tail)
        },
        [2, tail @ ..] => {
            // App 是前缀编码里的连续两项，函数在前、实参在后
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
            &body,
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
    let mut ret = Vec::new();
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

pub(crate) fn normalize(t: Vec<u8>, arena: &mut ListArena<Value>) -> Vec<u8> {
    quote(0, eval(unsafe { NonZeroUsize::new_unchecked(1) }, &t, arena).0.into(), arena)
}