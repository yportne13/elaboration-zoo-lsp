use crate::{list::List, parser_lib::Span};

use super::{parser::syntax::Icit, Tm, Ty};

pub type Pruning = List<Option<Icit>>;

#[derive(Debug, Clone)]
pub enum Locals {
    Here,
    Define(Box<Locals>, Span<String>, Ty, Tm),
    Bind(Box<Locals>, Span<String>, Ty),
}

pub fn close_ty(mcl: Locals, b: Ty) -> Ty {
    match mcl {
        Locals::Here => b,
        Locals::Bind(mcl, x, a) => {
            close_ty(*mcl, Tm::Pi(x, Icit::Expl, Box::new(a), Box::new(b)))
        }
        Locals::Define(mcl, x, a, t) => {
            close_ty(*mcl, Tm::Let(x, Box::new(a), Box::new(t), Box::new(b)))
        }
    }
}
