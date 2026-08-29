use lex::{TokenKind, TokenNode};

use crate::parser_lib::*;
use smol_str::SmolStr;

mod lex;

use TokenKind::*;

pub fn parser(input: &str, id: u32) -> Option<Raw> {
    crate::L03_holes::parser::lex::lex(Span {
        data: input,
        start_offset: 0,
        end_offset: input.len() as u32,
        path_id: id,
    })
    .and_then(|(_, ret)| p_raw(&ret).map(|x| x.1))
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

fn kw<'a: 'b, 'b>(p: TokenKind) -> impl Parser<&'b [TokenNode<'a>], Span<()>> {
    move |input: &'b [TokenNode<'a>]| match input.first() {
        Some(x) if x.data.1 == p => input.get(1..).map(|i| (i, x.map(|_| ()))),
        _ => None,
    }
}

fn string<'a: 'b, 'b>(p: TokenKind) -> impl Parser<&'b [TokenNode<'a>], Span<SmolStr>> {
    move |input: &'b [TokenNode<'a>]| match input.first() {
        Some(x) if x.data.1 == p => input.get(1..).map(|i| (i, x.map(|s| SmolStr::new(s.0)))),
        _ => None,
    }
}

fn paren<'a: 'b, 'b, P, O>(p: P) -> impl Parser<&'b [TokenNode<'a>], O>
where
    P: Parser<&'b [TokenNode<'a>], O>,
{
    (kw(LParen), p, kw(RParen)).map(|c| c.1)
}

/// main.hs 的 `withPos`：包一层 `Raw::SrcPos`，位置取产生式第一个 token 的起点
/// （lex 已跳过前导空白，与 megaparsec `getSourcePos` 在 `ws` 之后取位置的语义一致）。
fn with_pos<'a: 'b, 'b, P>(p: P) -> impl Parser<&'b [TokenNode<'a>], Raw>
where
    P: Parser<&'b [TokenNode<'a>], Raw>,
{
    move |input: &'b [TokenNode<'a>]| {
        let first = input.first()?;
        let pos = Span {
            data: (),
            start_offset: first.start_offset,
            end_offset: first.end_offset,
            path_id: first.path_id,
        };
        let (rest, r) = p.parse(input)?;
        Some((rest, Raw::SrcPos(pos, Box::new(r))))
    }
}

fn p_atom<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], Raw)> {
    with_pos(
        string(Ident)
            .map(Raw::Var)
            .or(kw(UKeyword).map(|_| Raw::U))
            .or(kw(Hole).map(|_| Raw::Hole)),
    )
    .or(paren(p_raw))
    .parse(input)
}

/// binder 位置：普通标识符或匿名 binder `_`（`pBinder = pIdent <|> symbol "_"`）。
fn p_binder<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], Span<SmolStr>)> {
    string(Ident).or(string(Hole)).parse(input)
}

fn p_spine<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], Raw)> {
    p_atom
        .many1()
        .map(|atoms| {
            atoms
                .into_iter()
                .reduce(|acc, x| Raw::App(Box::new(acc), Box::new(x)))
                .unwrap()
        })
        .parse(input)
}

fn p_lam<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], Raw)> {
    (kw(Lambda), p_binder.many1(), kw(Dot), p_raw)
        .map(|(_, binder, _, ty)| {
            binder
                .into_iter()
                .rev()
                .fold(ty, |acc, x| Raw::Lam(x, Box::new(acc)))
        })
        .parse(input)
}

fn p_pi<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], Raw)> {
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
        .parse(input)
}

//TODO:fun_or_spine
fn fun_or_spine<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], Raw)> {
    (p_spine, (kw(Arrow), p_raw).option())
        .map(|(sp, tail)| match tail {
            Some((kw, cod)) => Raw::Pi(kw.map(|_| SmolStr::new("_")), Box::new(sp), Box::new(cod)),
            None => sp,
        })
        .parse(input)
}

fn p_let<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], Raw)> {
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
        .parse(input)
}

/// main.hs：`pRaw = withPos (pLam <|> pLet <|> try pPi <|> funOrSpine)`。
/// 组合子版 `or` 在纯函数 token 切片上天然带回溯（失败不消费输入），
/// `try` 的语义由尝试顺序实现。
fn p_raw<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], Raw)> {
    with_pos(p_lam.or(p_let).or(p_pi).or(fun_or_spine)).parse(input)
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
