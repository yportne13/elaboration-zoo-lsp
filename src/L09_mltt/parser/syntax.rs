use crate::{parser_lib::{Span, ToSpan}, L09_mltt::empty_span};

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

impl Raw {
    pub fn to_span(&self) -> Span<()> {
        match self {
            Raw::Var(span) => span.to_span(),
            Raw::Obj(raw, span) => raw.to_span() + span.to_span(),
            Raw::Lam(span, _, raw) => span.to_span() + raw.to_span(),
            Raw::App(raw, raw1, either) => raw.to_span() + match either {
                Either::Name(span) => span.to_span(),
                Either::Icit(_) => raw1.to_span(),
            },
            Raw::U(_) => empty_span(()),//TODO:
            Raw::Pi(span, _, _, raw1) => span.to_span() + raw1.to_span(),
            Raw::Let(span, _, _, raw2) => span.to_span() + raw2.to_span(),
            Raw::Hole => empty_span(()),//TODO:
            Raw::LiteralIntro(span) => span.to_span(),
            Raw::Match(raw, items) => items.last()
                .map(|x| raw.to_span() + x.1.to_span())
                .unwrap_or(raw.to_span()),
            Raw::Sum(span, params, items, _) => items.last()
                .map(|x| span.to_span() + x.to_span())
                .unwrap_or(params.last().map(|x| span.to_span() + x.2.to_span()).unwrap_or(span.to_span())),
            Raw::SumCase { typ, case_name, datas } => datas.last()
                .map(|x| case_name.to_span() + x.1.to_span())
                .unwrap_or(case_name.to_span()),
        }
    }
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
