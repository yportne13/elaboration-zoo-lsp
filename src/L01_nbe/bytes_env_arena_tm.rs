//! `bytes_env_arena` 的变体：**项体也进共享 arena**（`to_vec3` 编码）。
//!
//! 前缀字节码里 `Lam` 不再内联体，只存 `arena_tm` 下标；`Value::Lam`
//! 的第二字段也从 `Rc<Vec<u8>>` 缩成一个 `usize`。闭包体完全不拷贝，
//! 代价是 eval/quote 要多走一次 `arena_tm.get_unchecked` 间接寻址。

use std::{num::NonZeroUsize, rc::Rc};

use super::persistent_list::ListArena;

#[derive(Debug, Clone)]
pub(crate) enum Value {
    Lvl(usize),
    Lam(NonZeroUsize, usize),
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
fn eval<'a>(
    env: NonZeroUsize,
    tm: &'a [u8],
    arena: &mut ListArena<Value>,
    arena_tm: &mut Vec<Rc<Vec<u8>>>,
) -> (Value, &'a [u8]) {
    match tm {
        [0, a0, a1, a2, a3, a4, a5, a6, a7, tail @ ..] => {
            let idx = usize::from_le_bytes([*a0, *a1, *a2, *a3, *a4, *a5, *a6, *a7]);
            let value = arena.nth(env, idx).clone();
            (value, tail)
        },
        [1, a0, a1, a2, a3, a4, a5, a6, a7, tail @ ..] => {
            let tm_idx = usize::from_le_bytes([*a0, *a1, *a2, *a3, *a4, *a5, *a6, *a7]);
            let value = Value::Lam(env, tm_idx);
            (value, tail)
        },
        [2, tail @ ..] => {
            // App 是前缀编码里的连续两项，函数在前、实参在后
            let (value1, remaining_tm) = eval(env, tail, arena, arena_tm);
            let (value2, final_tm) = eval(env, remaining_tm, arena, arena_tm);
            let result = apply_val(value1, value2, arena, arena_tm);
            (result, final_tm)
        },
        _ => unsafe { std::hint::unreachable_unchecked() },
    }
}

/// apply_val vf va =
///      match vf with
///      | VLam(env, body) -> eval (va :: env) body
///      | _               -> VApp(vf, va)
fn apply_val(vf: Value, va: Value, arena: &mut ListArena<Value>, arena_tm: &mut Vec<Rc<Vec<u8>>>) -> Value {
    match vf {
        Value::Lam(env, body) => {
            // 克隆 Rc 使借用独立于 arena_tm（eval 内部还要可变借用 arena_tm）
            let body_tm = unsafe { arena_tm.get_unchecked(body) }.clone();
            eval(arena.prepend(env, va), &body_tm, arena, arena_tm).0
        },
        _ => Value::App(Rc::new(vf), Rc::new(va)),
    }
}

/// quote level value =
///      match value with
///      | VLvl lvl        -> Idx(level - lvl - 1)
///      | VLam(env, body) -> Lam(quote (level + 1) @@ eval (VLvl level :: env) body)
///      | VApp(vf, va)    -> App(quote level vf, quote level va)
fn quote(
    level: usize,
    value: Rc<Value>,
    arena: &mut ListArena<Value>,
    arena_tm: &mut Vec<Rc<Vec<u8>>>,
) -> Vec<u8> {
    let mut ret = Vec::new();
    quote_append(level, value, &mut ret, arena, arena_tm);
    ret
}

fn quote_append(
    level: usize,
    value: Rc<Value>,
    ret: &mut Vec<u8>,
    arena: &mut ListArena<Value>,
    arena_tm: &mut Vec<Rc<Vec<u8>>>,
) {
    match value.as_ref() {
        Value::Lvl(lvl) => {
            ret.push(0);
            ret.extend_from_slice(&(level - lvl - 1).to_le_bytes());
        },
        Value::Lam(env, body) => {
            // 计算闭包体的值，再压进 arena_tm，字节流里只写下标
            let body_tm = unsafe { arena_tm.get_unchecked(*body) }.clone();
            let (evaluated_body, _) = eval(arena.prepend(*env, Value::Lvl(level)), &body_tm, arena, arena_tm);

            ret.push(1); // tag
            let tm = quote(level + 1, evaluated_body.into(), arena, arena_tm);
            ret.extend_from_slice(&arena_tm.len().to_le_bytes()); // 占位长度（= 新体下标）
            arena_tm.push(tm.into());
        },
        Value::App(vf, va) => {
            ret.push(2);
            quote_append(level, vf.clone(), ret, arena, arena_tm);
            quote_append(level, va.clone(), ret, arena, arena_tm);
        },
    }
}

pub(crate) fn normalize(
    t: Vec<u8>,
    arena: &mut ListArena<Value>,
    arena_tm: &mut Vec<Rc<Vec<u8>>>,
) -> Vec<u8> {
    quote(0, eval(unsafe { NonZeroUsize::new_unchecked(1) }, &t, arena, arena_tm).0.into(), arena, arena_tm)
}