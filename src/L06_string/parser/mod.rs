use lex::{TokenKind, TokenNode};
use syntax::{Decl, Either, Icit, Raw};

use crate::parser_lib::*;

mod lex;
pub mod syntax;

use TokenKind::*;

pub fn parser(input: &str, id: u32) -> Option<Vec<Decl>> {
    super::parser::lex::lex(Span {
        data: input,
        start_offset: 0,
        end_offset: input.len() as u32,
        path_id: id,
    })
    .and_then(|(_, ret)| p_decl.many1().parse(&ret).map(|x| x.1))
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

fn square<'a: 'b, 'b, P, O>(p: P) -> impl Parser<&'b [TokenNode<'a>], O>
where
    P: Parser<&'b [TokenNode<'a>], O>,
{
    (kw(LSquare), p, kw(RSquare)).map(|c| c.1)
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
        .or(string(Str).map(Raw::LiteralIntro))
        .or(paren(p_raw))
        .parse(input)
}

fn p_arg<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], (Either, Raw))> {
    let named_arg = square((string(Ident), kw(Eq), p_raw)).map(|(x, _, t)| (Either::Name(x), t));

    let implicit_arg = square(p_raw).map(|t| (Either::Icit(Icit::Impl), t));

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

fn p_lam_binder<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
) -> Option<(&'b [TokenNode<'a>], (Span<String>, Either))> {
    let explicit_binder = p_bind.map(|x| (x, Either::Icit(Icit::Expl)));
    let implicit_binder = square(p_bind).map(|x| (x, Either::Icit(Icit::Impl)));
    let named_binder = square((string(Ident), kw(Eq), p_bind)).map(|(x, _, y)| (y, Either::Name(x)));

    explicit_binder
        .or(implicit_binder)
        .or(named_binder)
        .parse(input)
}

fn p_lam<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], Raw)> {
    (p_lam_binder.many1(), kw(T![=>]), p_raw)
        .map(|(binder, _, ty)| {
            binder
                .into_iter()
                .rev()
                .fold(ty, |acc, x| Raw::Lam(x.0, x.1, Box::new(acc)))
        })
        .parse(input)
}

fn p_pi_binder<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
) -> Option<(&'b [TokenNode<'a>], Vec<(Span<String>, Raw, Icit)>)> {
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
    implicit_binder.or(explicit_binder).parse(input)
}

fn p_pi<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], Raw)> {
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
        .parse(input)
}

//TODO:fun_or_spine
fn fun_or_spine<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], Raw)> {
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
        .parse(input)
}

fn p_let<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], Raw)> {
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
        .parse(input)
}

fn p_raw<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], Raw)> {
    p_lam.or(p_let).or(p_pi).or(fun_or_spine).parse(input)
}

fn p_def<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], Decl)> {
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
        .parse(input)
}

fn p_print<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], Decl)> {
    (kw(PrintlnKeyword), p_raw)
        .map(|(_, x)| Decl::Println(x))
        .parse(input)
}

fn p_decl<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<(&'b [TokenNode<'a>], Decl)> {
    p_def.or(p_print).parse(input)
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
    println!("{:#?}", parser(input, 0).unwrap());
}
