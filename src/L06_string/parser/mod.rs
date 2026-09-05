use lex::{TokenKind, TokenNode};
use syntax::{Decl, Either, Icit, Raw};

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

/// 解析 decl 序列。decl 流必须吃完全部 token:`;` / 垃圾 token 曾把后续
/// decl 静默截断(测试因此空转过)——现在一律报错,并带**首个残余 token**
/// 的内容与偏移,`;` 结尾这类最常见错误不再无从定位。任何解析失败都折叠
/// 为整体 `Err("parse error")`(契约被 l06 blackbox 钉死)。
pub fn parser(input: &str, id: u32) -> Result<Vec<Decl>, String> {
    match lex::lex(Span {
        data: input,
        start_offset: 0,
        end_offset: input.len() as u32,
        path_id: id,
    }) {
        Some((_, ret)) => {
            let mut err_collect: MacroState = vec![];
            match p_decl.many1().parse(&ret, &mut err_collect) {
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
    [def] => { $crate::L06_string::parser::TokenKind::DefKeyword };
    [let] => { $crate::L06_string::parser::TokenKind::LetKeyword };
    [U] => { $crate::L06_string::parser::TokenKind::UKeyword };
    [_] => { $crate::L06_string::parser::TokenKind::Hole };
    ['('] => { $crate::L06_string::parser::TokenKind::LParen };
    [')'] => { $crate::L06_string::parser::TokenKind::RParen };
    ['['] => { $crate::L06_string::parser::TokenKind::LSquare };
    [']'] => { $crate::L06_string::parser::TokenKind::RSquare };
    ['{'] => { $crate::L06_string::parser::TokenKind::LCurly };
    ['}'] => { $crate::L06_string::parser::TokenKind::RCurly };
    [.] => { $crate::L06_string::parser::TokenKind::Dot };
    [,] => { $crate::L06_string::parser::TokenKind::Comma };
    [=] => { $crate::L06_string::parser::TokenKind::Eq };
    [;] => { $crate::L06_string::parser::TokenKind::Semi };
    [:] => { $crate::L06_string::parser::TokenKind::Colon };
    [->] => { $crate::L06_string::parser::TokenKind::Arrow };
    [=>] => { $crate::L06_string::parser::TokenKind::DoubleArrow };
    ['\\'] => { $crate::L06_string::parser::TokenKind::Lambda };
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
    (kw(LParen), p, kw(RParen)).map(|c| c.1)
}

/// [ p ]
fn square<'a: 'b, 'b, P, O>(p: P) -> impl Parser<&'b [TokenNode<'a>], O, MacroState, IError>
where
    P: Parser<&'b [TokenNode<'a>], O, MacroState, IError>,
{
    (kw(LSquare), p, kw(RSquare)).map(|c| c.1)
}

/// { p }
fn brace<'a: 'b, 'b, P, O>(p: P) -> impl Parser<&'b [TokenNode<'a>], O, MacroState, IError>
where
    P: Parser<&'b [TokenNode<'a>], O, MacroState, IError>,
{
    (kw(LCurly), p, kw(RCurly)).map(|c| c.1)
}

fn p_atom<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    string(Ident)
        .map(Raw::Var)
        .or(kw(UKeyword).map(|_| Raw::U))
        .or(kw(Hole).map(|_| Raw::Hole))
        .or(string(Str).map(|x| Raw::LiteralIntro(x.map(|s| unescape(&s)))))
        .or(paren(p_raw))
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
    let named_binder = square((string(Ident), kw(Eq), p_bind)).map(|(x, _, y)| (y, Either::Name(x)));

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

fn p_pi_binder<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut MacroState,
) -> IResult<'a, 'b, Vec<(Span<String>, Raw, Icit)>> {
    // 解析隐式参数 [x : A] 或 [x]
    let implicit_binder = square(
        (
            p_bind, // 解析一个或多个绑定变量 xs
            (kw(Colon), p_raw).option().map(|x| match x {
                Some((_, x)) => x,
                None => Raw::Hole,
            }),
        )
            .map(|(xs, a)| (xs, a, Icit::Impl))
            .many0_sep(kw(T![,])),
    ); // 返回 (xs, a, Impl)

    // 解析显式参数 (x : A)
    let explicit_binder = paren((
        p_bind,                // 解析一个或多个绑定变量 xs
        kw(Colon).with(p_raw), // 解析类型 A
    ).map(|(xs, a)| (xs, a.1, Icit::Expl)).many0_sep(kw(T![,]))); // 返回 (xs, a, Expl)

    // 组合所有可能的解析器
    implicit_binder.or(explicit_binder).parse(input, state)
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

//TODO:fun_or_spine
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
        p_raw,
    )
        .map(|(_, binder, ann, _, val, _, body)| {
            Raw::Let(
                binder,
                Box::new(ann.unwrap_or(Raw::Hole)),
                Box::new(val),
                Box::new(body),
            )
        })
        .parse(input, state)
}

fn p_raw<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    p_lam.or(p_let).or(p_pi).or(fun_or_spine)
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
        p_pi_binder.many0().map(|x| x.into_iter().flatten().collect::<Vec<_>>()),
        (kw(T![:]), p_raw).map(|(_, x)| x).option(),
        kw(T![=]),
        p_raw,
    )
        .map(|(_, name, params, ret, _, body)| {
            Decl::Def {
                name,
                params,
                ret_type: ret.unwrap_or(Raw::Hole),
                body,
            }
        })
        .parse(input, state)
}

fn p_print<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
    (kw(PrintlnKeyword), p_raw)
        .map(|(_, x)| Decl::Println(x))
        .parse(input, state)
}

fn p_decl<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
    p_def.or(p_print)
        .parse(input, state)
        .map_err(|e| IError {
            msg: e.msg.map(extract_base)
        })
}

#[test]
fn test() {
    let input = r#"
def Eq[A : U](x: A, y: A): U = (P : A -> U) -> P x -> P y
def refl[A : U, x: A]: Eq[A] x x = _ => px => px

def the(A : U)(x: A): A = x

def m(A : U)(B : U): U -> U -> U = _
def test = a => b => the (Eq (m a a) (x => y => y)) refl

def m : U -> U -> U -> U = _
def test = a => b => c => the (Eq (m a b c) (m c b a)) refl


def pr1 = f => x => f x
def pr2 = f => x => y => f x y
def pr3 = f => f U

def Nat : U
    = (N : U) -> (N -> N) -> N -> N
def mul : Nat -> Nat -> Nat
    = a => b => N => s => z => a _ (b _ s) z
def ten : Nat
    = N => s => z => s (s (s (s (s (s (s (s (s (s z)))))))))
def hundred = mul ten ten

println hundred

def mystr = "hello world"

println mystr

"#;
    let decls = parser(input, 0).unwrap();
    assert!(!decls.is_empty());
}

#[test]
fn test_leftover_located() {
    // `;` 结尾 / 垃圾 token 报错带定位（同 l06 blackbox 契约）。
    let input = "def x: U = U\nprintln x;\n";
    let err = parser(input, 0).unwrap_err();
    assert!(err.contains("parse error"), "err: {err}");
    assert!(err.contains("`;`"), "err should locate the token: {err}");
}

#[test]
fn test_whole_file_fail() {
    // 坏 decl 折叠为整体 `parse error`（契约被 blackbox 钉死）。
    let input = "def = 1\n";
    assert_eq!(parser(input, 0).unwrap_err(), "parse error");
}