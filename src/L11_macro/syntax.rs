use std::rc::Rc;

use crate::{list::List, parser_lib::Span};

use super::{Tm, Ty, parser::syntax::Icit, Val, Infer, Lvl};

pub type Pruning = List<Option<Icit>>;

#[derive(Debug, Clone)]
pub enum Locals {
    Here,
    Define(Box<Locals>, Span<String>, Rc<Ty>, Rc<Tm>),
    Bind(Box<Locals>, Span<String>, Rc<Ty>),
}

impl Locals {
    pub fn update_by_cxt(self, infer: &Infer, lvl: Lvl, cxt: &List<Rc<Val>>) -> Self {
        match (self, cxt) {
            (Locals::Here, _) => Locals::Here,
            (Locals::Define(mcl, name, ty, tm), cxt) => {
                //Locals::Define(Box::new(mcl.update_by_cxt(infer, lvl, &cxt.tail())), name, ty, tm)
                match cxt.head() {
                    Some(v) => match v.as_ref() {
                        Val::Rigid(_, _) => Locals::Bind(Box::new(mcl.update_by_cxt(infer, lvl, &cxt.tail())), name, ty),
                        _ => Locals::Define(
                            Box::new(mcl.update_by_cxt(infer, lvl, &cxt.tail())),
                            name,
                            ty,
                            infer.quote(lvl, v),
                        )
                    },
                    _ => panic!("Internal error: unexpected value in context"),
                }
            }
            (Locals::Bind(mcl, name, ty), cxt) => {
                match cxt.head() {
                    Some(v) => match v.as_ref() {
                        Val::Rigid(_, _) => Locals::Bind(Box::new(mcl.update_by_cxt(infer, lvl, &cxt.tail())), name, ty),
                        _ => Locals::Define(
                            Box::new(mcl.update_by_cxt(infer, lvl, &cxt.tail())),
                            name,
                            ty,
                            infer.quote(lvl, v),
                        )
                    },
                    _ => panic!("Internal error: unexpected value in context"),
                }
            }
        }
    }
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
