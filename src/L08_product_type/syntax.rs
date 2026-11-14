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
#[derive(Debug, Clone)]
pub enum Locals {
    Here,
    Define(Rc<Locals>, Span<String>, Ty, Tm),
    Bind(Rc<Locals>, Span<String>, Ty),
}

use super::Tm;

pub fn close_ty(mcl: Locals, b: Ty) -> Ty {
    match mcl {
        Locals::Here => b,
        Locals::Bind(mcl, x, a) => {
            close_ty(mcl.as_ref().clone(), Tm::Pi(x, Icit::Expl, Rc::new(a), Rc::new(b)))
        }
        Locals::Define(mcl, x, a, t) => close_ty(
            mcl.as_ref().clone(),
            Tm::Let(x, Box::new(a), Box::new(t), Box::new(b)),
        ),
    }
}
