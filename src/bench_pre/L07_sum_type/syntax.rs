use crate::{list::List, parser_lib::Span};

use super::{Ty, parser::syntax::Icit};

pub type Pruning = List<Option<Icit>>;

/// 词法作用域的链式表示：`Bind` 是 λ/Π 引入的变量，`Define` 是 let 绑定的变量。
/// `close_ty` 把一个开放类型按 locals 重新封口（fresh_meta 存元变量类型时用）。
#[derive(Debug, Clone)]
pub enum Locals {
    Here,
    Define(Box<Locals>, Span<String>, Ty, Tm),
    Bind(Box<Locals>, Span<String>, Ty),
}

use super::Tm;

pub fn close_ty(mcl: Locals, b: Ty) -> Ty {
    match mcl {
        Locals::Here => b,
        Locals::Bind(mcl, x, a) => close_ty(*mcl, Tm::Pi(x, Icit::Expl, Box::new(a), Box::new(b))),
        Locals::Define(mcl, x, a, t) => {
            close_ty(*mcl, Tm::Let(x, Box::new(a), Box::new(t), Box::new(b)))
        }
    }
}
