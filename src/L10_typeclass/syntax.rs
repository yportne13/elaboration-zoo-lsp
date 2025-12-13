use std::rc::Rc;

use crate::{list::List, parser_lib::Span};

use super::{Tm, Ty, parser::syntax::Icit};

pub type Pruning = List<Option<Icit>>;

#[derive(Debug, Clone)]
pub enum Locals {
    Here,
    Define(Box<Locals>, Span<String>, Rc<Ty>, Rc<Tm>),
    Bind(Box<Locals>, Span<String>, Rc<Ty>),
}

pub fn close_ty(mcl: Locals, b: Rc<Ty>) -> Rc<Ty> {
    match mcl {
        Locals::Here => b,
        Locals::Bind(mcl, x, a) => close_ty(*mcl, Tm::Pi(x, Icit::Expl, a, b).into()),
        Locals::Define(mcl, x, a, t) => {
            close_ty(*mcl, Tm::Let(x, a, t, b).into())
        }
    }
}
