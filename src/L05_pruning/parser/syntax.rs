use crate::parser_lib::Span;


#[derive(Clone, Debug, Copy, PartialEq)]
pub enum Icit {
    Impl,
    Expl,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Either {
    Name(Span<String>),
    Icit(Icit),
}

#[derive(Clone, Debug)]
pub enum Raw {
    Var(Span<String>),
    Lam(Span<String>, Either, Box<Raw>),
    App(Box<Raw>, Box<Raw>, Either),
    U,
    Pi(Span<String>, Icit, Box<Raw>, Box<Raw>),
    Let(Span<String>, Box<Raw>, Box<Raw>, Box<Raw>),
    Hole,
}
