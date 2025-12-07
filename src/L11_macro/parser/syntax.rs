use crate::{parser_lib::{Span, ToSpan}};

use super::empty_span;

#[derive(Clone, Debug, Copy, PartialEq, Eq, Hash)]
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
    Any(Span<()>, Icit),
    Con(Span<String>, Vec<Pattern>, Icit),
}

impl Pattern {
    pub fn to_impl(self) -> Self {
        match self {
            Pattern::Any(span, _) => Pattern::Any(span, Icit::Impl),
            Pattern::Con(name, pats, _) => Pattern::Con(name, pats, Icit::Impl),
        }
    }

    pub fn get_icit(&self) -> Icit {
        match self {
            Pattern::Any(_, icit) | Pattern::Con(_, _, icit) => *icit,
        }
    }
}

impl Pattern {
    pub fn to_raw(&self) -> Raw {
        match self {
            Pattern::Any(_, _) => Raw::Hole,
            Pattern::Con(name, pats, _) => pats.iter()
                .fold(Raw::Var(name.clone()), |ret, p| Raw::App(
                    Box::new(ret),
                    Box::new(p.to_raw()),
                    Either::Icit(p.get_icit()),
                )),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Raw {
    Var(Span<String>),
    Obj(Box<Raw>, Option<Span<String>>),
    Lam(Span<String>, Either, Box<Raw>),
    App(Box<Raw>, Box<Raw>, Either),
    U(u32),
    Pi(Span<String>, Icit, Box<Raw>, Box<Raw>),
    Let(Span<String>, Box<Raw>, Box<Raw>, Box<Raw>),
    Hole,
    LiteralIntro(Span<String>),
    Match(Box<Raw>, Vec<(Pattern, Raw)>),
    Sum(Span<String>, Vec<(Span<String>, Icit, Raw)>, Vec<Span<String>>, u32, bool),
    SumCase {
        is_trait: bool,
        typ: Box<Raw>,
        case_name: Span<String>,
        datas: Vec<(Span<String>, Raw, Icit)>,
    },
}

impl Raw {
    pub fn to_span(&self) -> Span<()> {
        match self {
            Raw::Var(span) => span.to_span(),
            Raw::Obj(raw, span) => match span {
                Some(span) => raw.to_span() + span.to_span(),
                None => raw.to_span(),
            },
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
            Raw::Sum(span, params, items, _, _) => items.last()
                .map(|x| span.to_span() + x.to_span())
                .unwrap_or(params.last().map(|x| span.to_span() + x.2.to_span()).unwrap_or(span.to_span())),
            Raw::SumCase { is_trait: _, typ, case_name, datas } => datas.last()
                .map(|x| case_name.to_span() + x.1.to_span())
                .unwrap_or(case_name.to_span()),
        }
    }
}

impl std::fmt::Display for Raw {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Raw::Var(name) => write!(f, "{}", name.data),
            Raw::Obj(expr, name) => write!(f, "{}.{:?}", expr, name),
            Raw::Lam(param, Either::Name(name), body) => write!(f, "([{}={}] => {})", name.data, param.data, body),
            Raw::Lam(param, Either::Icit(Icit::Impl), body) => write!(f, "([{}] => {})", param.data, body),
            Raw::Lam(param, Either::Icit(Icit::Expl), body) => write!(f, "({} => {})", param.data, body),
            Raw::App(func, arg, Either::Name(name)) => write!(f, "({} [{}={}])", func, name.data, arg),
            Raw::App(func, arg, Either::Icit(Icit::Impl)) => write!(f, "({} [{}])", func, arg),
            Raw::App(func, arg, Either::Icit(Icit::Expl)) => write!(f, "({} {})", func, arg),
            Raw::U(level) => write!(f, "U{}", level),
            Raw::Pi(param, Icit::Impl, domain, codomain) => write!(f, "([{} : {}] -> {})", param.data, domain, codomain),
            Raw::Pi(param, Icit::Expl, domain, codomain) => write!(f, "({} : {}) -> {}", param.data, domain, codomain),
            Raw::Let(name, typ, expr, body) => write!(f, "(let {} : {} = {};\n{})", name.data, typ, expr, body),
            Raw::Hole => write!(f, "_"),
            Raw::LiteralIntro(lit) => write!(f, "\"{}\"", lit.data),
            Raw::Match(expr, cases) => {
                write!(f, "(match {}", expr)?;
                for (pattern, result) in cases {
                    match pattern {
                        Pattern::Any(_, _) => write!(f, " _ => {}", result)?,
                        Pattern::Con(name, patterns, _) => {
                            if patterns.is_empty() {
                                write!(f, " {} => {}", name.data, result)?;
                            } else {
                                write!(f, " {}({}) => {}", name.data,
                                    patterns.iter().map(|p| {
                                        match p {
                                            Pattern::Any(_, _) => "_".to_string(),
                                            Pattern::Con(n, _, _) => n.data.clone(),
                                        }
                                    }).collect::<Vec<_>>().join(" "),
                                    result)?;
                            }
                        }
                    }
                }
                write!(f, ")")
            },
            Raw::Sum(name, variants, constructors, _, is_inductive) => {
                if *is_inductive {
                    write!(f, "(enum {}", name.data)?;
                } else {
                    write!(f, "(struct {}", name.data)?;
                }
                
                // 显示 variants
                for (variant_name, icit, variant_type) in variants {
                    match icit {
                        Icit::Impl => write!(f, " {{{} : {}}}", variant_name.data, variant_type)?,
                        Icit::Expl => write!(f, " ({} : {})", variant_name.data, variant_type)?,
                    }
                }
                
                // 显示 constructors
                for constructor in constructors {
                    write!(f, " {}", constructor.data)?;
                }
                
                write!(f, ")")
            },
            Raw::SumCase { is_trait: _, typ, case_name, datas } => {
                write!(f, "(case {} of {} ", typ, case_name.data)?;
                for (data_name, data_type, icit) in datas {
                    match icit {
                        Icit::Impl => write!(f, "{{{} : {}}} ", data_name.data, data_type)?,
                        Icit::Expl => write!(f, "({} : {}) ", data_name.data, data_type)?,
                    }
                }
                write!(f, ")")
            }
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
        is_trait: bool,
        name: Span<String>,
        params: Vec<(Span<String>, Raw, Icit)>,
        cases: Vec<(Span<String>, Vec<(Span<String>, Raw, Icit)>, Option<Raw>)>,
    },
    TraitDecl {
        name: Span<String>,
        params: Vec<(Span<String>, Raw, Icit)>,
        methods: Vec<(Span<String>, Vec<(Span<String>, Raw, Icit)>, Raw)>,
    },
    ImplDecl {
        name: Raw,
        params: Vec<(Span<String>, Raw, Icit)>,
        trait_name: Span<String>,
        trait_params: Vec<Raw>,
        methods: Vec<Decl>,
    },
}
