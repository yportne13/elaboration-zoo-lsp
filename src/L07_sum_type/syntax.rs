use smol_str::SmolStr;
use std::rc::Rc;

use crate::{list::List, parser_lib::Span};

use super::{Ty, parser::syntax::Icit};

pub type Pruning = List<Option<Icit>>;

/// 词法作用域的链式表示：`Bind` 是 λ/Π 引入的变量，`Define` 是 let 绑定的变量。
/// `close_ty` 把一个开放类型按 locals 重新封口（fresh_meta 存元变量类型时用）。
///
/// L13 参考版同款：子链用 `Rc` 而不是 `Box`。`Box` 版每次 `locals.clone()`
/// 都深拷整条链（O(深度)），n 个嵌套 binder ⇒ O(n²)；`Rc` 版 clone 是 O(1)，
/// 这是深作用域路径上剩余的最大平方项。
///
/// 字段类型是 `Rc`/`Rc<Tm>`：`Bind` 的 `a_quote`（绑定器类型作为 `Tm`）在
/// `Cxt::bind` 的热路径上被逐臂复制。它原本是裸 `Tm`，而一个宽 `Sum` 类型的
/// `Tm` 有 O(width) 个构造子名——width=128 的 enum 上，每个臂深拷一次
/// 就是 128 次 `Span<SmolStr>` 拷贝（实测占 `walk_con` 的 76%）。改成 `Rc`
/// 后 clone 是一次引用计数递增；`close_ty` 在消费点 `Rc::unwrap_or_clone`。
#[derive(Debug, Clone)]
pub enum Locals {
    Here,
    Define(Rc<Locals>, Span<SmolStr>, Rc<Ty>, Rc<Tm>),
    Bind(Rc<Locals>, Span<SmolStr>, Rc<Ty>),
}

use super::Tm;

pub fn close_ty(mcl: Locals, b: Ty) -> Ty {
    match mcl {
        Locals::Here => b,
        Locals::Bind(mcl, x, a) => {
            close_ty(mcl.as_ref().clone(), Tm::Pi(x, Icit::Expl, a, Rc::new(b)))
        }
        Locals::Define(mcl, x, a, t) => close_ty(
            mcl.as_ref().clone(),
            Tm::Let(x, Box::new(Rc::unwrap_or_clone(a)), Box::new(Rc::unwrap_or_clone(t)), Box::new(b)),
        ),
    }
}
