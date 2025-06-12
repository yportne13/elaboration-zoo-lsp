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
    pub fn count_binders(&self) -> u32 {
        match self {
            Pattern::Any(_) => 1, // 假设 Any 绑定一个变量
            Pattern::Con(_, pats) => pats.iter().map(|p| p.count_binders()).sum(),
            // 如果有 Pattern::Var, 也是返回 1
        }
    }
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
    LiteralIntro(Span<String>),
    Match(Box<Raw>, Vec<(Pattern, Raw)>),
    Sum(Span<String>, Vec<Raw>, Vec<(Span<String>, Vec<Raw>)>),
    SumCase {
        sum_name: Span<String>,
        params: Vec<Raw>,
        cases: Vec<(Span<String>, Vec<Raw>)>,
        case_name: Span<String>,
        datas: Vec<Raw>,
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
        cases: Vec<(Span<String>, Vec<Raw>)>,
    },
}
