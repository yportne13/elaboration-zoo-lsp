//! 值也压成**扁平字节**的变体：`Value(Vec<u8>)`，tag + 负载，与项的字节码
//! 同一套布局。彻底去掉 enum 判分派和 `Rc`，`apply_val`/`quote` 直接按
//! 字节前缀匹配；环境用 `ListArena`（`Lam` 的 env 与体长都内联在值里）。
//!
//! 代价：查表 `nth` 要 `clone()` 整段值、`App` 值是两个子值的字节拼接，
//! 每步都在整段 memcpy——空间换掉了引用的间接性（`prepend` 入表本身是
//! move，memcpy 发生在读取与拼接处）。

use std::num::NonZeroUsize;

use super::persistent_list::ListArena;

#[derive(Debug, Clone, Default)]
pub(crate) struct Value(Vec<u8>);

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
            let mut value = Vec::with_capacity(25 + tm.len());
            value.push(1);
            value.extend(env.get().to_le_bytes());
            value.extend(tm.len().to_le_bytes());
            value.extend(tm);
            (Value(value), tail)
        },
        [2, tail @ ..] => {
            // App 是前缀编码里的连续两项，函数在前、实参在后
            let (value1, remaining_tm) = eval(env, tail, arena);
            let (value2, final_tm) = eval(env, remaining_tm, arena);
            let result = apply_val(value1, value2, arena);
            (result, final_tm)
        },
        // SAFETY: `tm` 必须由 `Term::to_vec2` 产出（见 term.rs 的编码契约），
        // tag 只可能是 0/1/2 且字段长度自洽；畸形输入属调用方违约。
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
            // 长度字节在此处冗余：体就是其后整段（构造值时就地切好）
            _b0, _b1, _b2, _b3, _b4, _b5, _b6, _b7,
            tail @ ..
        ] => eval(
            arena.prepend(unsafe { NonZeroUsize::new_unchecked(usize::from_le_bytes([*a0, *a1, *a2, *a3, *a4, *a5, *a6, *a7])) }, va),
            tail,
            arena
        ).0,
        // SAFETY: Lam 值恒带完整的 env(8B)+len(8B)+体，长度由构造保证；
        // 长度字段截断（< 17B）属构造期不变量被破坏，非本分支可达状态。
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
            // SAFETY: `Value::Lam` 的 env 字段来自 `ListArena` 下标（`env.get()`
            // 或 `prepend` 返回值），`ListArena` 只追加不收缩且下标从 1 起，
            // 故非零。
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
        // SAFETY: 同 `eval`——值由本文件的构造路径产出，tag 只会是 0/1/2。
        _ => unsafe { std::hint::unreachable_unchecked() },
    }
}

pub(crate) fn normalize(t: Vec<u8>, arena: &mut ListArena<Value>) -> Vec<u8> {
    quote(0, &eval(ListArena::<Value>::empty(), &t, arena).0.0, arena).0
}