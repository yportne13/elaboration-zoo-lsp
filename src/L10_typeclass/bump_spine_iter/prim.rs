//! prim：卡住 builtin 的归约体（`prim_reduce`）。由参考版
//! `Infer::prim_reduce` 的 L10 裁剪而来——本层唯一 builtin 是
//! `string_concat`。归约在 force 的 Prim 链头臂触发；元数不足 / 实参非
//! 字面量时返回 None 保持卡住（源码可达路径不 panic）。

use bumpalo::Bump;

use super::parser::syntax::Icit;
use super::spine::lit_of;
use super::syntax::{V, XCell, v_xcell};

/// 卡住内建的归约体。`args` 自然序（最先应用在前）；本层只认
/// `string_concat`：两个实参全为字面量时拼接，否则 None 保持卡住。
pub(super) fn prim_reduce<'a>(bump: &'a Bump, name: &str, args: &[(V, Icit)]) -> Option<V> {
    match name {
        "string_concat" => {
            if args.len() < 2 {
                return None;
            }
            match (lit_of(args[0].0), lit_of(args[1].0)) {
                (Some(a), Some(b)) => {
                    let len = a.len() + b.len();
                    let ptr = bump
                        .alloc_layout(std::alloc::Layout::from_size_align(len, 1).unwrap())
                        .as_ptr();
                    // SAFETY: a/b 都是 &str（合法 UTF-8）；两段完整序列按
                    // 字节拼接仍是合法 UTF-8，不会引入跨边界截断的码点
                    let s = unsafe {
                        std::ptr::copy_nonoverlapping(a.as_ptr(), ptr, a.len());
                        std::ptr::copy_nonoverlapping(b.as_ptr(), ptr.add(a.len()), b.len());
                        std::str::from_utf8_unchecked(std::slice::from_raw_parts(ptr, len))
                    };
                    Some(v_xcell(bump.alloc(XCell::Lit(s))))
                }
                _ => None,
            }
        }
        _ => None,
    }
}
