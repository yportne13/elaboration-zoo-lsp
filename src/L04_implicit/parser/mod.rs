use lex::{TokenKind, TokenNode};

use crate::parser_lib::*;
use smol_str::SmolStr;

mod lex;

use TokenKind::*;

pub fn parser(input: &str, id: u32) -> Option<Raw> {
    crate::L04_implicit::parser::lex::lex(Span {
        data: input,
        start_offset: 0,
        end_offset: input.len() as u32,
        path_id: id,
    })
    .and_then(|(_, ret)| p_raw(&ret).map(|x| x.1))
}

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

fn brace<'a: 'b, 'b, P, O>(p: P) -> impl Parser<&'b [TokenNode<'a>], O>
where
    P: Parser<&'b [TokenNode<'a>], O>,
{
    (kw(LCurly), p, kw(RCurly)).map(|c| c.1)
}

/// main.hs 的 `withPos`：包一层 `Raw::SrcPos`，位置取产生式第一个 token 的
/// 起点。
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

/// 实参（上游 `pArg`）：`{x = t}` 命名隐式 | `{t}` 隐式 | atom 显式。
/// 命名形态须先于隐式形态尝试（`{x = t}` 的 `x` 会先吃掉 `{`）。
fn p_arg<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], (Either, Raw))> {
    let named_arg = brace((string(Ident), kw(Eq), p_raw)).map(|(x, _, t)| (Either::Name(x), t));

    let implicit_arg = brace(p_raw).map(|t| (Either::Icit(Icit::Impl), t));

    let explicit_arg = p_atom.map(|t| (Either::Icit(Icit::Expl), t));

    named_arg.or(implicit_arg).or(explicit_arg).parse(input)
}

fn p_spine<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], Raw)> {
    let (input, head) = p_atom(input)?;
    let (input, args) = p_arg.many0().parse(input)?;

    let result = args.into_iter().fold(head, |acc, (icit, arg)| {
        Raw::App(Box::new(acc), Box::new(arg), icit)
    });
    Some((input, result))
}

/// binder 位置：普通标识符或匿名 binder `_`。
fn p_bind<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], Span<SmolStr>)> {
    string(Ident).or(string(Hole)).parse(input)
}

/// lambda binder（上游 `pLamBinder`）：`x` | `{x}` | `{x = y}`
/// （`y` 是体内可见的本地名，`x` 是按名定位的引用）。
fn p_lam_binder<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
) -> Option<(&'b [TokenNode<'a>], (Span<SmolStr>, Either))> {
    let explicit_binder = p_bind.map(|x| (x, Either::Icit(Icit::Expl)));
    let implicit_binder = brace(p_bind).map(|x| (x, Either::Icit(Icit::Impl)));
    let named_binder =
        brace((string(Ident), kw(Eq), p_bind)).map(|(x, _, y)| (y, Either::Name(x)));

    explicit_binder.or(implicit_binder).or(named_binder).parse(input)
}

fn p_lam<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], Raw)> {
    (kw(Lambda), p_lam_binder.many1(), kw(Dot), p_raw)
        .map(|(_, binder, _, ty)| {
            binder
                .into_iter()
                .rev()
                .fold(ty, |acc, x| Raw::Lam(x.0, x.1, Box::new(acc)))
        })
        .parse(input)
}

/// Pi binder（上游 `pPiBinder`）：`{xs}` / `{xs : A}`（类型可省 → 洞，隐式）
/// | `(xs : A)`（显式）。
fn p_pi_binder<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
) -> Option<(&'b [TokenNode<'a>], (Vec<Span<SmolStr>>, Raw, Icit))> {
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

    implicit_binder.or(explicit_binder).parse(input)
}

fn p_pi<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], Raw)> {
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
        .parse(input)
}

fn fun_or_spine<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], Raw)> {
    (p_spine, (kw(Arrow), p_raw).option())
        .map(|(sp, tail)| match tail {
            Some((kw, cod)) => {
                Raw::Pi(kw.map(|_| SmolStr::new("_")), Icit::Expl, Box::new(sp), Box::new(cod))
            }
            None => sp,
        })
        .parse(input)
}

/// `let x [: A]? = t; u`（注解可省 → 洞；上游 04 的 readme 示例用到省略态）。
fn p_let<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], Raw)> {
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
    .parse(input)
}

/// `pRaw = withPos (pLam <|> pLet <|> try pPi <|> funOrSpine)`。
fn p_raw<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], Raw)> {
    with_pos(p_lam.or(p_let).or(p_pi).or(fun_or_spine)).parse(input)
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
