use smol_str::SmolStr;

use crate::{parser_lib::{Span, ToSpan}};

use super::empty_span;

#[derive(Clone, Debug, Copy, PartialEq, Eq, Hash)]
pub enum Icit {
    Impl,
    Expl,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Either {
    Name(Span<SmolStr>),
    Icit(Icit),
}

impl Either {
    pub fn to_icit(&self) -> Icit {
        match self {
            Either::Name(_) => Icit::Impl,
            Either::Icit(icit) => *icit,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Pattern {
    Any(Span<bool>, Either),
    Con(Span<SmolStr>, Vec<Pattern>, Either),
}

impl Pattern {
    pub fn to_impl(self) -> Self {
        match self {
            Pattern::Any(span, _) => Pattern::Any(span, Either::Icit(Icit::Impl)),
            Pattern::Con(name, pats, _) => Pattern::Con(name, pats, Either::Icit(Icit::Impl)),
        }
    }
    pub fn to_name(self, name: Span<SmolStr>) -> Self {
        match self {
            Pattern::Any(span, _) => Pattern::Any(span, Either::Name(name)),
            Pattern::Con(name1, pats, _) => Pattern::Con(name1, pats, Either::Name(name)),
        }
    }

    pub fn get_icit(&self) -> Either {
        match self {
            Pattern::Any(_, icit) | Pattern::Con(_, _, icit) => icit.clone(),
        }
    }
}

impl Pattern {
    pub fn to_raw(&self) -> Raw {
        match self {
            Pattern::Any(s, _) => Raw::Hole(s.to_span()),
            Pattern::Con(name, pats, _) => pats.iter()
                .fold(Raw::Var(name.clone()), |ret, p| Raw::App(
                    Box::new(ret),
                    Box::new(p.to_raw()),
                    p.get_icit(),
                )),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Raw {
    Var(Span<SmolStr>),
    Obj(Box<Raw>, Option<Span<SmolStr>>),
    Lam(Span<SmolStr>, Either, Box<Raw>),
    App(Box<Raw>, Box<Raw>, Either),
    U(u32),
    Pi(Span<SmolStr>, Icit, Box<Raw>, Box<Raw>),
    Let(Span<SmolStr>, Box<Raw>, Box<Raw>, Box<Raw>),
    Hole(Span<()>),
    LiteralIntro(Span<String>),
    Match(Box<Raw>, Vec<(Pattern, Raw)>),
    Sum(Span<SmolStr>, Vec<(Span<SmolStr>, Icit, Raw)>, Vec<Span<SmolStr>>, u32, bool),
    SumCase {
        is_trait: bool,
        typ: Box<Raw>,
        case_name: Span<SmolStr>,
        datas: Vec<(Span<SmolStr>, Raw, Icit)>,
    },
}

impl Raw {
    pub fn app(lhs: Raw, rhs: Raw) -> Self {
        Raw::App(Box::new(lhs), Box::new(rhs), Either::Icit(Icit::Expl))
    }
    pub fn app_impl(lhs: Raw, rhs: Raw) -> Self {
        Raw::App(Box::new(lhs), Box::new(rhs), Either::Icit(Icit::Impl))
    }
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
            Raw::Hole(span) => span.clone(),//TODO:
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
            Raw::Hole(_) => write!(f, "_"),
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
                                            Pattern::Any(_, _) => SmolStr::new("_"),
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
        name: Span<SmolStr>,
        params: Vec<(Span<SmolStr>, Raw, Icit)>,
        ret_type: Raw,
        body: Raw,
    },
    Println(Raw),
    Enum {
        is_trait: bool,
        name: Span<SmolStr>,
        params: Vec<(Span<SmolStr>, Raw, Icit)>,
        cases: Vec<(Span<SmolStr>, Vec<(Span<SmolStr>, Raw, Icit)>, Option<Raw>)>,
    },
    TraitDecl {
        name: Span<SmolStr>,
        params: Vec<(Span<SmolStr>, Raw, Icit)>,
        methods: Vec<(Span<SmolStr>, Vec<(Span<SmolStr>, Raw, Icit)>, Raw)>,
    },
    ImplDecl {
        name: Raw,
        params: Vec<(Span<SmolStr>, Raw, Icit)>,
        trait_name: Span<SmolStr>,
        trait_params: Vec<Raw>,
        methods: Vec<Decl>,
        need_create: bool,
    },
}
