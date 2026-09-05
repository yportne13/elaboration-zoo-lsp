use lex::{TokenKind, TokenNode};

use crate::parser_lib_resilient::*;
use smol_str::SmolStr;

mod lex;

use TokenKind::*;

/// 隐式/显式标记（上游 04 `Icit`）。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Icit {
    Impl,
    Expl,
}

/// lambda binder / 应用实参的命名引用（上游 `Either Name Icit`）：
/// `Name` = 命名隐式（`\{x = y}` binder、`t {x = u}` 实参——按 Pi binder
/// 名字定位插入点）；`Icit` = 位置隐式/显式。
#[derive(Clone, Debug, PartialEq)]
pub enum Either {
    Name(Span<SmolStr>),
    Icit(Icit),
}

/// L04（implicit args）的表面语法（上游 04-implicit-args `Presyntax.hs` 的
/// `Raw`）。与 L03 的差别：
/// - `Lam` binder / `App` 实参携带 [`Either`]，`Pi` 携带 [`Icit`]；
/// - 多了 `{x}`、`{x : A}`、`{x = e}` 形态（Pi binder 可省类型注解 → 洞）；
/// - `let` 的类型注解可省（→ 洞）；
/// - [`Raw::SrcPos`] 同 L03：`withPos` 给每个产生式包上源位置。
#[derive(Clone, Debug)]
pub enum Raw {
    Var(Span<SmolStr>),
    Lam(Span<SmolStr>, Either, Box<Raw>),
    App(Box<Raw>, Box<Raw>, Either),
    U,
    Pi(Span<SmolStr>, Icit, Box<Raw>, Box<Raw>),
    Let(Span<SmolStr>, Box<Raw>, Box<Raw>, Box<Raw>),
    Hole,
    SrcPos(Span<()>, Box<Raw>),
}

fn empty_span<T>(data: T) -> Span<T> {
    Span {
        data,
        start_offset: 0,
        end_offset: 0,
        path_id: 0,
    }
}

/// 解析单条表达式。失败返回 None（main_with 报 "parse error"）。
pub fn parser(input: &str, id: u32) -> Option<Raw> {
    match super::parser::lex::lex(Span {
        data: input,
        start_offset: 0,
        end_offset: input.len() as u32,
        path_id: id,
    }) {
        Some((_, ret)) => {
            let mut err_collect: MacroState = vec![];
            p_raw(&ret, &mut err_collect).ok().map(|(_, r)| r)
        }
        None => None,
    }
}

#[derive(Debug, Clone, Copy)]
pub enum BaseMsg {
    Expect(TokenKind),
    EmptyVec,
    ExpectRaw,
    ExpectAtom,
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

/// 本层无宏也无 decl 流，解析态就是错误收集器；公开 API 只返回
/// Option<Raw>，收集到的错误随整体失败折叠为 None。
pub type MacroState = Vec<IError>;

trait ParserExt<I: Copy, A, S> {
    fn many1(self) -> impl Parser<I, Vec<A>, S, IError>;
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

fn string<'a: 'b, 'b>(p: TokenKind) -> impl Parser<&'b [TokenNode<'a>], Span<SmolStr>, MacroState, IError> {
    move |input: &'b [TokenNode<'a>], _: &mut MacroState| match input.first() {
        Some(x) => if x.data.1 == p {
            input
                .get(1..)
                .map(|i| (i, x.map(|s| SmolStr::new(s.0))))
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

fn paren<'a: 'b, 'b, P, O>(p: P) -> impl Parser<&'b [TokenNode<'a>], O, MacroState, IError>
where
    P: Parser<&'b [TokenNode<'a>], O, MacroState, IError>,
{
    (kw(LParen), p, kw(RParen)).map(|c| c.1)
}

fn brace<'a: 'b, 'b, P, O>(p: P) -> impl Parser<&'b [TokenNode<'a>], O, MacroState, IError>
where
    P: Parser<&'b [TokenNode<'a>], O, MacroState, IError>,
{
    (kw(LCurly), p, kw(RCurly)).map(|c| c.1)
}

/// main.hs 的 `withPos`：包一层 `Raw::SrcPos`，位置取产生式第一个 token 的
/// 起点。
fn with_pos<'a: 'b, 'b, P>(p: P) -> impl Parser<&'b [TokenNode<'a>], Raw, MacroState, IError>
where
    P: Parser<&'b [TokenNode<'a>], Raw, MacroState, IError>,
{
    move |input: &'b [TokenNode<'a>], _state: &mut MacroState| {
        let first = *input.first().ok_or_else(|| IError {
            msg: empty_span(ErrMsg::Base(BaseMsg::ExpectRaw)),
        })?;
        let pos = Span {
            data: (),
            start_offset: first.start_offset,
            end_offset: first.end_offset,
            path_id: first.path_id,
        };
        let (rest, r) = p.parse(input, _state)?;
        Ok((rest, Raw::SrcPos(pos, Box::new(r))))
    }
}

fn p_atom<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    with_pos(
        string(Ident)
            .map(Raw::Var)
            .or(kw(UKeyword).map(|_| Raw::U))
            .or(kw(Hole).map(|_| Raw::Hole)),
    )
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

/// 实参（上游 `pArg`）：`{x = t}` 命名隐式 | `{t}` 隐式 | atom 显式。
/// 命名形态须先于隐式形态尝试（`{x = t}` 的 `x` 会先吃掉 `{`）。
fn p_arg<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, (Either, Raw)> {
    let named_arg = brace((string(Ident), kw(Eq), p_raw)).map(|(x, _, t)| (Either::Name(x), t));

    let implicit_arg = brace(p_raw).map(|t| (Either::Icit(Icit::Impl), t));

    let explicit_arg = p_atom.map(|t| (Either::Icit(Icit::Expl), t));

    named_arg.or(implicit_arg).or(explicit_arg).parse(input, state)
}

fn p_spine<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    let (input, head) = p_atom(input, state)?;
    let (input, args) = p_arg.many0().parse(input, state)?;

    let result = args.into_iter().fold(head, |acc, (icit, arg)| {
        Raw::App(Box::new(acc), Box::new(arg), icit)
    });
    Ok((input, result))
}

/// binder 位置：普通标识符或匿名 binder `_`。
fn p_bind<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Span<SmolStr>> {
    string(Ident).or(string(Hole)).parse(input, state)
}

/// lambda binder（上游 `pLamBinder`）：`x` | `{x}` | `{x = y}`
/// （`y` 是体内可见的本地名，`x` 是按名定位的引用）。
fn p_lam_binder<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut MacroState,
) -> IResult<'a, 'b, (Span<SmolStr>, Either)> {
    let explicit_binder = p_bind.map(|x| (x, Either::Icit(Icit::Expl)));
    let implicit_binder = brace(p_bind).map(|x| (x, Either::Icit(Icit::Impl)));
    let named_binder =
        brace((string(Ident), kw(Eq), p_bind)).map(|(x, _, y)| (y, Either::Name(x)));

    explicit_binder.or(implicit_binder).or(named_binder).parse(input, state)
}

fn p_lam<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    (kw(Lambda), p_lam_binder.many1(), kw(Dot), p_raw)
        .map(|(_, binder, _, ty)| {
            binder
                .into_iter()
                .rev()
                .fold(ty, |acc, x| Raw::Lam(x.0, x.1, Box::new(acc)))
        })
        .parse(input, state)
}

/// Pi binder（上游 `pPiBinder`）：`{xs}` / `{xs : A}`（类型可省 → 洞，隐式）
/// | `(xs : A)`（显式）。
fn p_pi_binder<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut MacroState,
) -> IResult<'a, 'b, (Vec<Span<SmolStr>>, Raw, Icit)> {
    let implicit_binder = brace((
        p_bind.many1(),
        (kw(Colon), p_raw)
            .option()
            .map(|x| match x {
                Some((_, x)) => x,
                None => Raw::Hole,
            }),
    ))
    .map(|(xs, a)| (xs, a, Icit::Impl));

    let explicit_binder = paren((p_bind.many1(), kw(Colon).with(p_raw)))
        .map(|(xs, a)| (xs, a.1, Icit::Expl));

    implicit_binder.or(explicit_binder).parse(input, state)
}

fn p_pi<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    let param = p_pi_binder.map(|(binder, ty, icit)| {
        binder
            .into_iter()
            .map(|b| (b, ty.clone(), icit))
            .collect::<Vec<_>>()
    });
    (param.many1(), kw(Arrow), p_raw)
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
            Some((kw, cod)) => {
                Raw::Pi(kw.map(|_| SmolStr::new("_")), Icit::Expl, Box::new(sp), Box::new(cod))
            }
            None => sp,
        })
        .parse(input, state)
}

/// `let x [: A]? = t; u`（注解可省 → 洞；上游 04 的 readme 示例用到省略态）。
fn p_let<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    (
        kw(LetKeyword),
        p_bind,
        (kw(Colon), p_raw).map(|(_, x)| x).option(),
        kw(Eq),
        p_raw,
        kw(Semi),
        p_raw,
    )
    .map(|(_, binder, ann, _, val, _, body)| {
        Raw::Let(binder, Box::new(ann.unwrap_or(Raw::Hole)), Box::new(val), Box::new(body))
    })
    .parse(input, state)
}

/// `pRaw = withPos (pLam <|> pLet <|> try pPi <|> funOrSpine)`。
fn p_raw<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    with_pos(p_lam.or(p_let).or(p_pi).or(fun_or_spine))
        .parse(input, state)
        .map_err(|_e| IError {
            msg: input
                .first()
                .map(|x| x.map(|_| ErrMsg::Base(BaseMsg::ExpectRaw)))
                .unwrap_or(empty_span(ErrMsg::Base(BaseMsg::ExpectRaw)))
        })
}

#[test]
fn test() {
    let input = r#"
let id : {A : U} -> A -> A = \x. x;
let argTest1 = const {U}{U} U;
let argTest2 = const {B = U} U;
let namedLam : {A B C} -> A -> B -> C -> A = \{B = B} a b c. a;
let insert2 = (\{A} x. the A x) U;
the (Eq (mul ten ten) hundred) refl
"#;
    println!("{:#?}", parser(input, 0).unwrap());
}

#[test]
fn test_parse_err_is_none() {
    // 语法失败 → None（main_with 输出 "parse error"，契约被 blackbox 钉死）。
    assert!(parser("let x : U =;", 0).is_none());
}