use lex::{TokenKind, TokenNode};

use crate::parser_lib_resilient::*;
use smol_str::SmolStr;

mod lex;

use TokenKind::*;

/// 解析单条表达式。失败返回 None（main_with 报 "parse error"）。
pub fn parser(input: &str, id: u32) -> Option<Raw> {
    match crate::L03_holes::parser::lex::lex(Span {
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

/// L03（holes）的表面语法（上游 03-holes `Main.hs` 的 `Raw`）。与 L02 的差别：
/// - 多了 [`Raw::Hole`]——`_` 作为原子项（也兼任 binder 位置的匿名 binder）；
/// - [`Raw::SrcPos`] 同 L02：`withPos` 给每个产生式包上源位置，check/infer
///   下降时更新 cxt 的 pos，报错时取最内层位置。
#[derive(Clone, Debug)]
pub enum Raw {
    Var(Span<SmolStr>),
    Lam(Span<SmolStr>, Box<Raw>),
    App(Box<Raw>, Box<Raw>),
    U,
    Pi(Span<SmolStr>, Box<Raw>, Box<Raw>),
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

/// main.hs 的 `withPos`：包一层 `Raw::SrcPos`，位置取产生式第一个 token 的起点
/// （lex 已跳过前导空白，与 megaparsec `getSourcePos` 在 `ws` 之后取位置的语义一致）。
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

/// binder 位置：普通标识符或匿名 binder `_`（`pBinder = pIdent <|> symbol "_"`）。
fn p_binder<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Span<SmolStr>> {
    string(Ident).or(string(Hole)).parse(input, state)
}

fn p_spine<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    p_atom
        .many1()
        .map(|atoms| {
            atoms
                .into_iter()
                .reduce(|acc, x| Raw::App(Box::new(acc), Box::new(x)))
                .unwrap()
        })
        .parse(input, state)
}

fn p_lam<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    (kw(Lambda), p_binder.many1(), kw(Dot), p_raw)
        .map(|(_, binder, _, ty)| {
            binder
                .into_iter()
                .rev()
                .fold(ty, |acc, x| Raw::Lam(x, Box::new(acc)))
        })
        .parse(input, state)
}

fn p_pi<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    let param = paren((p_binder.many1(), kw(Colon), p_raw)).map(|(binder, _, ty)| {
        binder
            .into_iter()
            .map(|b| (b, ty.clone()))
            .collect::<Vec<_>>()
    });
    (param.many1(), kw(Arrow), p_raw)
        .map(|(binder, _, ty)| {
            binder
                .into_iter()
                .flat_map(|x| x.into_iter())
                .rev()
                .fold(ty, |acc, (binder, ty)| {
                    Raw::Pi(binder, Box::new(ty), Box::new(acc))
                })
        })
        .parse(input, state)
}

//TODO:fun_or_spine
fn fun_or_spine<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    (p_spine, (kw(Arrow), p_raw).option())
        .map(|(sp, tail)| match tail {
            Some((kw, cod)) => Raw::Pi(kw.map(|_| SmolStr::new("_")), Box::new(sp), Box::new(cod)),
            None => sp,
        })
        .parse(input, state)
}

fn p_let<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    (
        kw(LetKeyword),
        p_binder,
        kw(Colon),
        p_raw,
        kw(Eq),
        p_raw,
        kw(Semi),
        p_raw,
    )
        .map(|(_, binder, _, ty, _, val, _, body)| {
            Raw::Let(binder, Box::new(ty), Box::new(val), Box::new(body))
        })
        .parse(input, state)
}

/// main.hs：`pRaw = withPos (pLam <|> pLet <|> try pPi <|> funOrSpine)`。
/// 组合子版 `or` 在纯函数 token 切片上天然带回溯（失败不消费输入），
/// `try` 的语义由尝试顺序实现。
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
let id : (A : _) -> A -> A
  = \A x. x;
let foo : U = _;
let bar : U -> U = \x. id _ x;
bar _"#;
    println!("{:#?}", parser(input, 0).unwrap());
}

#[test]
fn test_parse_err_is_none() {
    // 语法失败 → None（main_with 输出 "parse error"，契约被 blackbox 钉死）。
    assert!(parser("let x : U =;", 0).is_none());
}