use smol_str::SmolStr;
use crate::parser_lib::Span;

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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Pattern {
    Any(Span<()>, Icit),
    Con(Span<SmolStr>, Vec<Pattern>, Icit),
}

impl Pattern {
    pub fn to_impl(self) -> Self {
        match self {
            Pattern::Any(span, _) => Pattern::Any(span, Icit::Impl),
            Pattern::Con(name, pats, _) => Pattern::Con(name, pats, Icit::Impl),
        }
    }

    /// 错误文案用的模式渲染：`Con` 递归成 `name(sub, ...)`，`Any` 成 `_`。
    ///
    /// 诊断里**不要**用 `{:?}`——它会泄漏内部表示（`Con("refl" @ 166,170, …)`），
    /// 对 IDE / 终端用户都不可读。
    pub fn pretty(&self) -> String {
        match self {
            Pattern::Any(..) => "_".to_owned(),
            Pattern::Con(name, subs, _) => {
                let mut s = name.data.to_string();
                if !subs.is_empty() {
                    s.push('(');
                    for (i, sub) in subs.iter().enumerate() {
                        if i > 0 {
                            s.push_str(", ");
                        }
                        s.push_str(&sub.pretty());
                    }
                    s.push(')');
                }
                s
            }
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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Raw {
    Var(Span<SmolStr>),
    Obj(Box<Raw>, Span<SmolStr>),
    Lam(Span<SmolStr>, Either, Box<Raw>),
    App(Box<Raw>, Box<Raw>, Either),
    U(u32),
    Pi(Span<SmolStr>, Icit, Box<Raw>, Box<Raw>),
    Let(Span<SmolStr>, Box<Raw>, Box<Raw>, Box<Raw>),
    Hole,
    LiteralIntro(Span<String>),
    Match(Box<Raw>, Vec<(Pattern, Raw)>),
    Sum(Span<SmolStr>, Vec<(Span<SmolStr>, Icit, Raw)>, Vec<Span<SmolStr>>, u32),
    SumCase {
        typ: Box<Raw>,
        case_name: Span<SmolStr>,
        datas: Vec<(Span<SmolStr>, Raw, Icit)>,
    },
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
        name: Span<SmolStr>,
        params: Vec<(Span<SmolStr>, Raw, Icit)>,
        cases: Vec<(Span<SmolStr>, Vec<(Span<SmolStr>, Raw, Icit)>, Option<Raw>)>,
    },
}

impl Decl {
    /// 声明名（调试用）
    pub fn name(&self) -> String {
        match self {
            Decl::Def { name, .. } | Decl::Enum { name, .. } => name.data.to_string(),
            Decl::Println(_) => "<println>".to_owned(),
        }
    }
}
