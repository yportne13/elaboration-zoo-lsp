use std::collections::HashMap;

use super::{
    syntax::{Locals, Pruning},
    *,
};

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum NameOrigin {
    Inserted,
    Source,
}

type Types = List<(Span<String>, NameOrigin, Val)>;

#[derive(Debug, Clone)]
pub struct Cxt {
    pub env: Env, // Used for evaluation
    pub lvl: Lvl, // Used for unification
    pub locals: Locals,
    pub pruning: Pruning,
    pub src_names: HashMap<String, (Lvl, VTy)>,
}

impl Cxt {
    pub fn new() -> Self {
        Self::empty()
            .define(
                empty_span("String".to_owned()),
                Tm::LiteralType,
                Val::LiteralType,
                Tm::U(0),
                Val::U(0),
            )
            .define(
                empty_span("string_concat".to_owned()),
                Tm::Lam(
                    empty_span("x".to_owned()),
                    Icit::Expl,
                    Box::new(Tm::Lam(
                        empty_span("y".to_owned()),
                        Icit::Expl,
                        Box::new(Tm::Prim),
                    )),
                ),
                Val::Lam(
                    empty_span("x".to_owned()),
                    Icit::Expl,
                    Closure(
                        List::new().prepend(Val::LiteralType),
                        Box::new(Tm::Lam(
                            empty_span("y".to_owned()),
                            Icit::Expl,
                            Box::new(Tm::Prim),
                        )),
                    ),
                ),
                Tm::Pi(
                    empty_span("x".to_owned()),
                    Icit::Expl,
                    Box::new(Tm::Var(Ix(0))),
                    Box::new(Tm::Pi(
                        empty_span("y".to_owned()),
                        Icit::Expl,
                        Box::new(Tm::Var(Ix(1))),
                        Box::new(Tm::Var(Ix(2))),
                    )),
                ),
                Val::Pi(
                    empty_span("x".to_owned()),
                    Icit::Expl,
                    Box::new(Val::LiteralType),
                    Closure(
                        List::new().prepend(Val::LiteralType),
                        Box::new(Tm::Pi(
                            empty_span("y".to_owned()),
                            Icit::Expl,
                            Box::new(Tm::Var(Ix(1))),
                            Box::new(Tm::Var(Ix(2))),
                        )),
                    ),
                ),
            )
    }
    pub fn empty() -> Self {
        Cxt {
            env: List::new(),
            lvl: Lvl(0),
            locals: Locals::Here,
            pruning: List::new(),
            src_names: HashMap::new(),
        }
    }

    pub fn bind(&self, x: Span<String>, a_quote: Tm, a: Val) -> Self {
        //println!("{} {x:?} {a:?} at {}", "bind".bright_purple(), self.lvl.0);
        let mut src_names = self.src_names.clone();
        src_names.insert(x.data.clone(), (self.lvl, a));
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl)),
            lvl: self.lvl + 1,
            locals: Locals::Bind(Box::new(self.locals.clone()), x, a_quote),
            pruning: self.pruning.prepend(Some(Icit::Expl)),
            src_names,
        }
    }

    pub fn fake_bind(&self, x: Span<String>, a_quote: Tm, a: Val) -> Self {
        //println!("{} {x:?} {a:?} at {}", "bind".bright_purple(), self.lvl.0);
        let mut src_names = self.src_names.clone();
        src_names.insert(x.data.clone(), (self.lvl + 1919810, a));
        Cxt {
            env: self.env.clone(),
            lvl: self.lvl,
            locals: self.locals.clone(),
            pruning: self.pruning.clone(),
            src_names,
        }
    }

    pub fn new_binder(&self, x: Span<String>, a_quote: Tm) -> Self {
        //println!("{} {x:?} {a:?} at {}", "bind".bright_purple(), self.lvl.0);
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl)),
            lvl: self.lvl + 1,
            locals: Locals::Bind(Box::new(self.locals.clone()), x, a_quote),
            pruning: self.pruning.prepend(Some(Icit::Expl)),
            src_names: self.src_names.clone(),
        }
    }

    pub fn define(&self, x: Span<String>, t: Tm, vt: Val, a: Ty, va: VTy) -> Self {
        //println!("{} {}\n{t:?}\n{vt:?}\n{a:?}\n{va:?}", "define".bright_purple(), x.data);
        let mut src_names = self.src_names.clone();
        src_names.insert(x.data.clone(), (self.lvl, va));
        Cxt {
            env: self.env.prepend(vt),
            lvl: self.lvl + 1,
            locals: Locals::Define(Box::new(self.locals.clone()), x, a, t),
            pruning: self.pruning.prepend(None),
            src_names,
        }
    }
}
