use crate::{list::List, parser_lib::Span};

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

#[derive(Clone, Debug, PartialEq)]
pub enum Pattern {
    Any(Span<()>),
    Con(Span<String>, Vec<Pattern>),
}

impl Pattern {
    pub fn to_raw(&self) -> Raw {
        match self {
            Pattern::Any(_) => Raw::Hole,
            Pattern::Con(name, pats) => pats.iter()
                .fold(Raw::Var(name.clone()), |ret, p| Raw::App(
                    Box::new(ret),
                    Box::new(p.to_raw()),
                    Either::Icit(Icit::Expl),
                )),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Raw {
    Var(Span<String>),
    Obj(Box<Raw>, Span<String>),
    Lam(Span<String>, Either, Box<Raw>),
    App(Box<Raw>, Box<Raw>, Either),
    U(u32),
    Pi(Span<String>, Icit, Box<Raw>, Box<Raw>),
    Let(Span<String>, Box<Raw>, Box<Raw>, Box<Raw>),
    Hole,
    LiteralIntro(Span<String>),
    Match(Box<Raw>, Vec<(Pattern, Raw)>),
    Sum(Span<String>, Vec<(Span<String>, Icit, Raw)>, Vec<Span<String>>, u32),
    SumCase {
        typ: Box<Raw>,
        case_name: Span<String>,
        datas: Vec<(Span<String>, Raw, Icit)>,
    },
}

#[derive(Clone, Debug)]
pub enum Decl {
    Def {
        name: Span<String>,
        params: Vec<(Span<String>, Raw, Icit)>,
        ret_type: Raw,
        body: Raw,
    },
    Println(Raw),
    Enum {
        name: Span<String>,
        params: Vec<(Span<String>, Raw, Icit)>,
        cases: Vec<(Span<String>, Vec<(Span<String>, Raw, Icit)>, Option<Raw>)>,
    },
}
