use lex::{TokenKind, TokenNode};
use syntax::{Decl, Either, Icit, Pattern, Raw};

use crate::parser_lib_resilient::*;

mod lex;
pub mod syntax;

use TokenKind::*;

use super::empty_span;

#[derive(Debug, Clone, Copy)]
pub enum BaseMsg {
    Expect(TokenKind),
    EmptyVec,
    ExpectRaw,
    ExpectAtom,
    ExpectDecl,
}

#[derive(Debug, Clone)]
pub enum ErrMsg {
    Base(BaseMsg),
    /// A parser-level error with a full user-facing message.
    Custom(String),
}

fn extract_base(m: ErrMsg) -> ErrMsg {
    match m {
        ErrMsg::Base(b) => ErrMsg::Base(b),
        ErrMsg::Custom(_) => m,
    }
}

use std::fmt;

impl fmt::Display for BaseMsg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BaseMsg::Expect(tk) => write!(f, "expected {}", tk),
            BaseMsg::EmptyVec   => write!(f, "expected at least one element"),
            BaseMsg::ExpectRaw  => write!(f, "expected expression"),
            BaseMsg::ExpectAtom => write!(f, "expected atom"),
            BaseMsg::ExpectDecl => write!(f, "expected declaration"),
        }
    }
}

impl fmt::Display for ErrMsg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrMsg::Base(msg) => fmt::Display::fmt(msg, f),
            ErrMsg::Custom(msg) => write!(f, "{}", msg),
        }
    }
}

#[derive(Debug, Clone)]
pub struct IError {
    pub msg: Span<ErrMsg>,
}

type IResult<'a, 'b, O> = Result<(&'b [TokenNode<'a>], O), IError>;

/// This lesson has no macros, so the parser state is just the error store.
/// NOTE: this layer's public contract (`Result<Vec<Decl>, String>` with the
/// two message forms below) is pinned by the blackbox suites, so the state's
/// collected errors are folded into the whole-parse failure instead of being
/// surfaced individually — same observable behavior as the pre-rewrite
/// Option-based parser.
pub type MacroState = Vec<IError>;

trait ParserExt<I: Copy, A, S> {
    fn many1(self) -> impl Parser<I, Vec<A>, S, IError>;
    fn many1_sep<P: Parser<I, X, S, IError>, X>(self, sep: P) -> impl Parser<I, Vec<A>, S, IError>;
}

impl<'a: 'b, 'b, A, T: Parser<&'b [TokenNode<'a>], A, MacroState, IError>> ParserExt<&'b [TokenNode<'a>], A, MacroState> for T {
    fn many1(self) -> impl Parser<&'b [TokenNode<'a>], Vec<A>, MacroState, IError> {
        move |input, state: &mut MacroState| match self.many0().parse(input, state) {
            Ok((i, v)) if v.is_empty() => Err(IError {
                msg: i.first()
                    .map(|x| x.to_span())
                    .unwrap_or(empty_span(()))
                    .map(|_| ErrMsg::Base(BaseMsg::EmptyVec))
            }),
            x => x,
        }
    }
    fn many1_sep<P, X>(self, sep: P) -> impl Parser<&'b [TokenNode<'a>], Vec<A>, MacroState, IError>
    where
        P: Parser<&'b [TokenNode<'a>], X, MacroState, IError>,
    {
        move |input, state: &mut MacroState| match self.many0_sep(sep).parse(input, state) {
            Ok((i, v)) if v.is_empty() => Err(IError {
                msg: i.first()
                    .map(|x| x.to_span())
                    .unwrap_or(empty_span(()))
                    .map(|_| ErrMsg::Base(BaseMsg::EmptyVec))
            }),
            x => x,
        }
    }
}

/// 解析 decl 序列。decl 流必须吃完全部 token：残留 token（`;` / 垃圾
/// token 曾把后续 decl 静默截断）一律报错，并带**首个残余 token**的内容
/// 与偏移——`;` 结尾这类最常见错误不再无从定位。任何解析失败都折叠为
/// 整体 `Err("parse error")`（契约被 l07 blackbox 钉死）。
pub fn parser(input: &str, id: u32) -> Result<Vec<Decl>, String> {
    match lex::lex(Span {
        data: input,
        start_offset: 0,
        end_offset: input.len() as u32,
        path_id: id,
    }) {
        Some((_, ret)) => {
            let mut err_collect: MacroState = vec![];
            match p_decl.many1_sep(kw(EndLine).many1()).parse(&ret, &mut err_collect) {
                Ok((rest, decls)) => {
                    if rest.is_empty() {
                        Ok(decls)
                    } else {
                        let t = &rest[0];
                        Err(format!(
                            "parse error: leftover token `{}` @ {},{}",
                            t.data.0, t.start_offset, t.end_offset
                        ))
                    }
                }
                Err(_e) => Err("parse error".to_owned()),
            }
        }
        None => Err("parse error".to_owned()),
    }
}

macro_rules! T {
    [def] => { $crate::L07_sum_type::parser::TokenKind::DefKeyword };
    [let] => { $crate::L07_sum_type::parser::TokenKind::LetKeyword };
    [U] => { $crate::L07_sum_type::parser::TokenKind::UKeyword };
    [_] => { $crate::L07_sum_type::parser::TokenKind::Hole };
    ['('] => { $crate::L07_sum_type::parser::TokenKind::LParen };
    [')'] => { $crate::L07_sum_type::parser::TokenKind::RParen };
    ['['] => { $crate::L07_sum_type::parser::TokenKind::LSquare };
    [']'] => { $crate::L07_sum_type::parser::TokenKind::RSquare };
    ['{'] => { $crate::L07_sum_type::parser::TokenKind::LCurly };
    ['}'] => { $crate::L07_sum_type::parser::TokenKind::RCurly };
    [.] => { $crate::L07_sum_type::parser::TokenKind::Dot };
    [,] => { $crate::L07_sum_type::parser::TokenKind::Comma };
    [=] => { $crate::L07_sum_type::parser::TokenKind::Eq };
    [;] => { $crate::L07_sum_type::parser::TokenKind::Semi };
    [:] => { $crate::L07_sum_type::parser::TokenKind::Colon };
    [->] => { $crate::L07_sum_type::parser::TokenKind::Arrow };
    [=>] => { $crate::L07_sum_type::parser::TokenKind::DoubleArrow };
    ['\\'] => { $crate::L07_sum_type::parser::TokenKind::Lambda };
    [:=] => { $crate::L07_sum_type::parser::TokenKind::AssignEq };
}

fn kw<'a: 'b, 'b>(p: TokenKind) -> impl Parser<&'b [TokenNode<'a>], Span<()>, MacroState, IError> {
    move |input: &'b [TokenNode<'a>], _: &mut MacroState| match input.first() {
        Some(x) => if x.data.1 == p {
            input
                .get(1..)
                .map(|i| (i, x.map(|_| ())))
                .ok_or_else(|| IError {
                    msg: x.map(|_| ErrMsg::Base(BaseMsg::Expect(p)))
                })
        } else {
            Err(IError {
                msg: x.map(|_| ErrMsg::Base(BaseMsg::Expect(p)))
            })
        },
        _ => Err(IError {
            msg: empty_span(ErrMsg::Base(BaseMsg::Expect(p)))
        }),
    }
}

fn string<'a: 'b, 'b>(p: TokenKind) -> impl Parser<&'b [TokenNode<'a>], Span<String>, MacroState, IError> {
    move |input: &'b [TokenNode<'a>], _: &mut MacroState| match input.first() {
        Some(x) => if x.data.1 == p {
            input
                .get(1..)
                .map(|i| (i, x.map(|s| s.0.to_owned())))
                .ok_or_else(|| IError {
                    msg: x.map(|_| ErrMsg::Base(BaseMsg::Expect(p)))
                })
        } else {
            Err(IError {
                msg: x.map(|_| ErrMsg::Base(BaseMsg::Expect(p)))
            })
        },
        _ => Err(IError {
            msg: empty_span(ErrMsg::Base(BaseMsg::Expect(p)))
        }),
    }
}

/// ( p )
fn paren<'a: 'b, 'b, P, O>(p: P) -> impl Parser<&'b [TokenNode<'a>], O, MacroState, IError>
where
    P: Parser<&'b [TokenNode<'a>], O, MacroState, IError>,
{
    (kw(LParen), kw(EndLine).option(), p, kw(EndLine).option(), kw(RParen)).map(|c| c.2)
}

/// [ p ]
fn square<'a: 'b, 'b, P, O>(p: P) -> impl Parser<&'b [TokenNode<'a>], O, MacroState, IError>
where
    P: Parser<&'b [TokenNode<'a>], O, MacroState, IError>,
{
    (kw(LSquare), kw(EndLine).option(), p, kw(EndLine).option(), kw(RSquare)).map(|c| c.2)
}

/// { p }
fn brace<'a: 'b, 'b, P, O>(p: P) -> impl Parser<&'b [TokenNode<'a>], O, MacroState, IError>
where
    P: Parser<&'b [TokenNode<'a>], O, MacroState, IError>,
{
    (
        kw(LCurly),
        kw(EndLine).option(),
        p,
        kw(EndLine).option(),
        kw(RCurly),
    )
        .map(|c| c.2)
}

fn p_atom1<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    string(Ident)
        .map(Raw::Var)
        .or(kw(UKeyword).map(|_| Raw::U))
        .or(kw(Hole).map(|_| Raw::Hole))
        .or(string(Str).map(|x| Raw::LiteralIntro(x.map(|s| unescape(&s)))))
        .or(paren(p_raw))
        .parse(input, state)
}

fn p_atom<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    (p_atom1, (kw(T![.]), string(Ident)).option())
        .map(|(x, t)| match t {
            Some((_, t)) => Raw::Obj(Box::new(x), t),
            None => x,
        })
        .parse(input, state)
        .map_err(|_e| {
            IError {
                msg: input
                    .first()
                    .map(|x| x.map(|_| ErrMsg::Base(BaseMsg::ExpectAtom)))
                    .unwrap_or(empty_span(ErrMsg::Base(BaseMsg::ExpectAtom))),
            }
        })
}

fn p_arg<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, (Either, Raw)> {
    let named_arg = square((string(Ident), kw(Eq), p_raw)).map(|(x, _, t)| (Either::Name(x), t));

    let implicit_arg = square(p_raw).map(|t| (Either::Icit(Icit::Impl), t));

    let explicit_arg = p_atom.map(|t| (Either::Icit(Icit::Expl), t));

    let arg_parser = named_arg.or(implicit_arg).or(explicit_arg);

    arg_parser.parse(input, state)
}

fn p_spine<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    let (input, head) = p_atom(input, state)?;
    let (input, args) = p_arg.many0().parse(input, state)?;

    let result = args.into_iter().fold(head, |acc, (icit, arg)| {
        Raw::App(Box::new(acc), Box::new(arg), icit)
    });

    Ok((input, result))
}

fn p_bind<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Span<String>> {
    string(Ident).or(string(Hole)).parse(input, state)
}

fn p_lam_binder<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut MacroState,
) -> IResult<'a, 'b, (Span<String>, Either)> {
    let explicit_binder = p_bind.map(|x| (x, Either::Icit(Icit::Expl)));
    let implicit_binder = square(p_bind).map(|x| (x, Either::Icit(Icit::Impl)));
    let named_binder =
        square((string(Ident), kw(Eq), p_bind)).map(|(x, _, y)| (y, Either::Name(x)));

    explicit_binder
        .or(implicit_binder)
        .or(named_binder)
        .parse(input, state)
}

fn p_lam<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    (p_lam_binder.many1(), kw(T![=>]), p_raw)
        .map(|(binder, _, ty)| {
            binder
                .into_iter()
                .rev()
                .fold(ty, |acc, x| Raw::Lam(x.0, x.1, Box::new(acc)))
        })
        .parse(input, state)
}

/// [x: A] or [x]
fn p_pi_impl_binder<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut MacroState,
) -> IResult<'a, 'b, Vec<(Span<String>, Raw, Icit)>> {
    square(
        (
            p_bind,
            (kw(Colon), p_raw).option().map(|x| match x {
                Some((_, x)) => x,
                None => Raw::Hole,
            }),
        )
            .map(|(xs, a)| (xs, a, Icit::Impl))
            .many0_sep(kw(T![,])),
    )
    .parse(input, state)
}

fn p_pi_binder<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut MacroState,
) -> IResult<'a, 'b, Vec<(Span<String>, Raw, Icit)>> {
    // 解析显式参数 (x : A)
    let explicit_binder = paren(
        (
            p_bind,
            kw(Colon).with(p_raw),
        )
            .map(|(xs, a)| (xs, a.1, Icit::Expl))
            .many0_sep(kw(T![,])),
    );

    p_pi_impl_binder.or(explicit_binder).parse(input, state)
}

fn p_pi<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    (p_pi_binder.many1(), kw(T![->]), p_raw)
        .map(|(binder, _, ty)| {
            binder
                .into_iter()
                .flat_map(|x| x.into_iter())
                .rev()
                .fold(ty, |acc, (binder, ty, icit)| {
                    Raw::Pi(binder, icit, Box::new(ty), Box::new(acc))
                })
        })
        .parse(input, state)
}

fn fun_or_spine<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    (p_spine, (kw(Arrow), p_raw).option())
        .map(|(sp, tail)| match tail {
            Some((kw, cod)) => Raw::Pi(
                kw.map(|_| "_".to_owned()),
                Icit::Expl,
                Box::new(sp),
                Box::new(cod),
            ),
            None => sp,
        })
        .parse(input, state)
}

fn p_let<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    (
        kw(LetKeyword),
        string(Ident),
        (kw(Colon), p_raw).map(|(_, x)| x).option(),
        kw(Eq),
        p_raw,
        kw(Semi),
        kw(EndLine).option(),
        p_raw,
    )
        .map(|(_, binder, ann, _, val, _, _, body)| {
            Raw::Let(
                binder,
                Box::new(ann.unwrap_or(Raw::Hole)),
                Box::new(val),
                Box::new(body),
            )
        })
        .parse(input, state)
}

fn p_pattern<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Pattern> {
    (
        string(Ident),
        paren(p_pattern.many0_sep(kw(T![,])))
            .or(square(p_pattern.map(|x| x.to_impl()).many0_sep(kw(T![,]))))
            .many0()
            .map(|x| x.concat()),
    )
        .map(|(x, t)| Pattern::Con(x, t, Icit::Expl))
        .or(kw(T![_]).map(|x| Pattern::Any(x, Icit::Expl)))
        .parse(input, state)
}

fn p_match<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    (
        kw(MatchKeyword),
        p_raw,
        brace(
            (kw(CaseKeyword), p_pattern, kw(T![=>]), kw(EndLine).option(), p_raw)
                .map(|(_, pattern, _, _, body)| (pattern, body))
                // 臂间允许连续空行：注释行经 preprocess 剥成空白后仍产生
                // EndLine，单 EndLine 分隔会把「臂间注释」打成语法错误
                .many0_sep(kw(EndLine).many1()),
        ),
    )
        .map(|(_, scrutinee, body)| Raw::Match(Box::new(scrutinee), body))
        .parse(input, state)
}

fn p_raw<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    p_lam
        .or(p_let)
        .or(p_pi)
        .or(fun_or_spine)
        .or(p_match)
        .parse(input, state)
        .map_err(|_e| IError {
            msg: input
                .first()
                .map(|x| x.map(|_| ErrMsg::Base(BaseMsg::ExpectRaw)))
                .unwrap_or(empty_span(ErrMsg::Base(BaseMsg::ExpectRaw)))
        })
}

fn p_def<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
    (
        kw(DefKeyword),
        string(Ident),
        p_pi_binder
            .many0()
            .map(|x| x.into_iter().flatten().collect::<Vec<_>>()),
        (kw(T![:]), p_raw).map(|(_, x)| x).option(),
        kw(T![=]),
        kw(EndLine).option(),
        p_raw,
    )
        .map(|(_, name, params, ret, _, _, body)| Decl::Def {
            name,
            params,
            ret_type: ret.unwrap_or(Raw::Hole),
            body,
        })
        .parse(input, state)
}

fn p_print<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
    (kw(PrintlnKeyword), p_raw)
        .map(|(_, x)| Decl::Println(x))
        .parse(input, state)
}

fn p_enum<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
    (
        kw(EnumKeyword),
        string(Ident),
        p_pi_binder
            .many0()
            .map(|x| x.into_iter().flatten().collect::<Vec<_>>()),
        brace(
            (
                string(Ident),
                p_pi_binder
                    .many0()
                    .map(|x| x.into_iter().flatten().collect::<Vec<_>>()),
                (kw(T![->]), p_raw).option().map(|x| x.map(|y| y.1)),
            )
                .many1_sep(kw(EndLine)),
        ),
    )
        .map(|(_, name, params, fields)| Decl::Enum {
            name,
            params,
            cases: fields,
        })
        .parse(input, state)
}

fn p_decl<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
    p_def.or(p_print).or(p_enum)
        .parse(input, state)
        .map_err(|e| IError {
            msg: e.msg.map(extract_base)
        })
}

#[test]
fn test_ok() {
    let input = r#"
enum Nat {
    zero
    succ(x: Nat)
}

def two = succ succ zero

def add(x: Nat, y: Nat): Nat =
    match x {
        case zero => y
        case succ(n) => succ add n y
    }

println add two two
"#;
    let decls = parser(input, 0).unwrap();
    assert!(!decls.is_empty());
}

#[test]
fn test_leftover_located() {
    // `;` 结尾 / 垃圾 token 报错带定位（同 l07 blackbox 契约）。
    let input = "enum Nat {\n    zero\n}\nprintln zero;\n";
    let err = parser(input, 0).unwrap_err();
    assert!(err.contains("parse error"), "err: {err}");
    assert!(err.contains("`;`"), "err should locate the token: {err}");
}

#[test]
fn test_whole_file_fail() {
    // 坏 decl 折叠为整体 `parse error`（契约被 blackbox 钉死）。
    let input = "enum Void {\n}\n";
    assert_eq!(parser(input, 0).unwrap_err(), "parse error");
}