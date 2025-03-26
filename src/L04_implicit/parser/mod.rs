use lex::{TokenKind, TokenNode};
use syntax::{Either, Icit, Raw};

use crate::parser_lib::*;

mod lex;
pub mod syntax;

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

fn kw<'a: 'b, 'b>(p: TokenKind) -> impl Parser<&'b [TokenNode<'a>], Span<()>> {
    move |input: &'b [TokenNode<'a>]| match input.first() {
        Some(x) if x.data.1 == p => input.get(1..).map(|i| (i, x.map(|_| ()))),
        _ => None,
    }
}

fn string<'a: 'b, 'b>(p: TokenKind) -> impl Parser<&'b [TokenNode<'a>], Span<String>> {
    move |input: &'b [TokenNode<'a>]| match input.first() {
        Some(x) if x.data.1 == p => input.get(1..).map(|i| (i, x.map(|s| s.0.to_owned()))),
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

fn p_atom<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], Raw)> {
    string(Ident)
        .map(Raw::Var)
        .or(kw(UKeyword).map(|_| Raw::U))
        .or(kw(Hole).map(|_| Raw::Hole))
        .or(paren(p_raw))
        .parse(input)
}

fn p_arg<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], (Either, Raw))> {
    let named_arg = brace((
        string(Ident),
        kw(Eq),
        p_raw,
    ))
    .map(|(x, _, t)| (Either::Name(x), t));

    let implicit_arg = brace(p_raw)
        .map(|t| (Either::Icit(Icit::Impl), t));

    let explicit_arg = p_atom.map(|t| (Either::Icit(Icit::Expl), t));

    let arg_parser = named_arg.or(implicit_arg).or(explicit_arg);

    arg_parser.parse(input)
}

fn p_spine<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], Raw)> {
    let (input, head) = p_atom(input)?;
    let (input, args) = p_arg.many0().parse(input)?;

    let result = args.into_iter().fold(head, |acc, (icit, arg)| {
        Raw::App(Box::new(acc), Box::new(arg), icit)
    });

    Some((input, result))
}

fn p_bind<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], Span<String>)> {
    string(Ident).or(string(Hole)).parse(input)
}

fn p_lam_binder<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], (Span<String>, Either))> {
    let explicit_binder = p_bind.map(|x| (x, Either::Icit(Icit::Expl)));
    let implicit_binder = brace(p_bind).map(|x| (x, Either::Icit(Icit::Impl)));
    let named_binder = brace((
        string(Ident),
        kw(Eq),
        p_bind,
    ))
    .map(|(x, _, y)| (y, Either::Name(x)));

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

fn p_pi_binder<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], (Vec<Span<String>>, Raw, Icit))> {
    // 解析隐式参数 {x : A} 或 {x}
    let implicit_binder = brace((
        p_bind.many1(),               // 解析一个或多个绑定变量 xs
        (kw(Colon),p_raw).map(|(_, x)| x)     // 解析类型 A，可选
            .or(kw(Hole).map(|_| Raw::Hole)) // 如果没有类型，默认为 Hole
    ))
    .map(|(xs, a)| (xs, a, Icit::Impl)); // 返回 (xs, a, Impl)

    // 解析显式参数 (x : A)
    let explicit_binder = paren((
        p_bind.many1(),               // 解析一个或多个绑定变量 xs
        kw(Colon).with(p_raw)       // 解析类型 A
    ))
    .map(|(xs, a)| (xs, a.1, Icit::Expl)); // 返回 (xs, a, Expl)

    // 组合所有可能的解析器
    implicit_binder.or(explicit_binder).parse(input)
}

fn p_pi<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], Raw)> {
    let param = p_pi_binder.map(|(binder, ty, icit)| {
        binder
            .into_iter()
            .map(|b| (b, ty.clone(), icit.clone()))
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

//TODO:fun_or_spine
fn fun_or_spine<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], Raw)> {
    (p_spine, (kw(Arrow), p_raw).option())
        .map(|(sp, tail)| match tail {
            Some((kw, cod)) => Raw::Pi(kw.map(|_| "_".to_owned()), Icit::Expl, Box::new(sp), Box::new(cod)),
            None => sp,
        })
        .parse(input)
}

fn p_let<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], Raw)> {
    (
        kw(LetKeyword),
        string(Ident),
        (kw(Colon),p_raw).map(|(_, x)| x).option(),
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

fn p_raw<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], Raw)> {
    p_lam.or(p_let).or(p_pi).or(fun_or_spine).parse(input)
}

#[test]
fn test() {
    let input = r#"
let id : (A : _) -> A -> A
  = \A x. x;

let List : U -> U
  = \A. (L : _) -> (A -> L -> L) -> L -> L;

let nil : (A : _) -> List A
  = \A L cons nil. nil;

let cons : (A : _) -> A -> List A -> List A
  = \A x xs L cons nil. cons x (xs _ cons nil);

let Bool : U
  = (B : _) -> B -> B -> B;

let true : Bool
  = \B t f. t;

let false : Bool
  = \B t f. f;

let not : Bool -> Bool
  = \b B t f. b B f t;

let list1 : List Bool
  = cons _ (id _ true) (nil _);

let Eq : (A : _) -> A -> A -> U
  = \A x y. (P : A -> U) -> P x -> P y;

let refl : (A : _)(x : A) -> Eq A x x
  = \A x P px. px;

let list1 : List Bool
  = cons _ true (cons _ false (nil _));

let Nat  : U = (N : U) -> (N -> N) -> N -> N;
let five : Nat = \N s z. s (s (s (s (s z))));
let add  : Nat -> Nat -> Nat = \a b N s z. a N s (b N s z);
let mul  : Nat -> Nat -> Nat = \a b N s z. a N (b N s) z;

let ten      : Nat = add five five;
let hundred  : Nat = mul ten ten;
let thousand : Nat = mul ten hundred;

let eqTest : Eq _ hundred hundred = refl _ _;

U
"#;
    println!("{:#?}", parser(input, 0).unwrap());
}
