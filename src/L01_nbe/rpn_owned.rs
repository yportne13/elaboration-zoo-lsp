//! 后缀（RPN）编码 + 自持 `Vec<u8>` 项的变体：tag 在**末尾**（`to_vec`）。
//!
//! 求值从尾部 `pop` tag，与 `bytes_env_list` 的前缀解码正好镜像——
//! `Lam` 的长度和体都从尾部读/切。输入是自持 `Vec`，eval 就地消费；
//! 环境仍是 `crate::list::List`，闭包体以 `Vec<u8>` 随值拷贝。
//!
//! 这是唯一在**尾部**增删 tag 的编码：quote 时先写子值再回填长度、
//! 最后补 tag，输出无需预知体长。

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
fn eval(env: List<Value>, mut tm: Vec<u8>) -> (Value, Vec<u8>) {
    // 契约（见 term.rs `to_vec` 与模块头）：输入必须是后缀编码的非空字节流。
    // debug 构建下把「空输入/字段被截断」这类误用提前炸出来（release 零成本，
    // 取值为 UB——`pop`/`len-8` 都不为畸形输入提供分支）。
    debug_assert!(!tm.is_empty(), "rpn_owned::eval 输入不能为空（须为 to_vec 产物）");
    // SAFETY: 上面的 debug_assert 之外，契约保证输入由 `to_vec` 产出、非空，
    // 故 `pop` 必为 Some。
    let tag = unsafe { tm.pop().unwrap_unchecked() };

    match tag {
        0 => {
            // Idx case: read 8 bytes as usize
            let mut idx_bytes = [0u8; 8];
            debug_assert!(tm.len() >= 8, "rpn_owned::eval Idx 负载被截断");
            let start = tm.len() - 8;
            // SAFETY: 契约 + 上面的 debug_assert 保证 `start..start+8` 是已初始
            // 化的索引负载区间。
            idx_bytes.copy_from_slice(unsafe { tm.get_unchecked(start..start + 8) });
            tm.truncate(start);
            let idx = usize::from_le_bytes(idx_bytes);
            let value = env.iter().nth(idx).unwrap().clone();
            (value, tm)
        },
        1 => {
            // Lam case: read length (8 bytes) and extract term
            let mut len_bytes = [0u8; 8];
            debug_assert!(tm.len() >= 8, "rpn_owned::eval Lam 长度字段被截断");
            let start = tm.len() - 8;
            // SAFETY: 同 Idx——长度字段区间已初始化。
            len_bytes.copy_from_slice(unsafe { tm.get_unchecked(start..start + 8) });
            tm.truncate(start);
            let len = u64::from_le_bytes(len_bytes) as usize;
            debug_assert!(tm.len() >= len, "rpn_owned::eval Lam 体长度越界");
            let term_start = tm.len() - len;
            let term_bytes = tm.split_off(term_start);
            let value = Value::Lam(env, term_bytes);
            (value, tm)
        },
        2 => {
            // App case: parse from right to left (the argument comes first)
            let (value2, remaining_tm) = eval(env.clone(), tm);
            let (value1, final_tm) = eval(env, remaining_tm);
            let result = apply_val(value1, value2);
            (result, final_tm)
        },
        // SAFETY: 契约保证 tag 只会是 0/1/2；畸形输入属调用方违约。
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

pub(crate) fn normalize(t: Vec<u8>) -> Vec<u8> {
    quote(0, eval(List::new(), t).0.into())
}