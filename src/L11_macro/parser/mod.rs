use lex::{TokenKind, TokenNode};
use syntax::{Decl, Either, Icit, Pattern, Raw};

use crate::parser_lib_resilient::*;

mod lex;
pub mod syntax;

use TokenKind::*;

use super::empty_span;

#[derive(Debug, Clone, Copy)]
pub enum ErrMsg {
    Expect(TokenKind),
    EmptyVec,
    ExpectRaw,
    ExpectAtom,
    ExpectDecl,
}

#[derive(Debug, Clone, Copy)]
pub struct IError {
    pub msg: Span<ErrMsg>,
}

type IResult<'a, 'b, O> = Result<(&'b [TokenNode<'a>], O), IError>;

trait ParserExt<I: Copy, A, S> {
    fn many1(self) -> impl Parser<I, Vec<A>, S, IError>;
    fn many1_sep<P: Parser<I, X, S, IError>, X>(self, sep: P) -> impl Parser<I, Vec<A>, S, IError>;
}

impl<'a: 'b, 'b, A, T: Parser<&'b [TokenNode<'a>], A, Vec<IError>, IError>> ParserExt<&'b [TokenNode<'a>], A, Vec<IError>> for T {
    fn many1(self) -> impl Parser<&'b [TokenNode<'a>], Vec<A>, Vec<IError>, IError> {
        move |input, state: &mut Vec<IError>| match self.many0().parse(input, state) {
            Ok((i, v)) if v.is_empty() => Err(IError {
                msg: i.first()
                    .map(|x| x.to_span())
                    .unwrap_or(empty_span(()))
                    .map(|_| ErrMsg::EmptyVec)
            }),
            x => x,
        }
    }
    fn many1_sep<P, X>(self, sep: P) -> impl Parser<&'b [TokenNode<'a>], Vec<A>, Vec<IError>, IError>
    where
        P: Parser<&'b [TokenNode<'a>], X, Vec<IError>, IError>,
    {
        move |input, state: &mut Vec<IError>| match self.many0_sep(sep).parse(input, state) {
            Ok((i, v)) if v.is_empty() => Err(IError {
                msg: i.first()
                    .map(|x| x.to_span())
                    .unwrap_or(empty_span(()))
                    .map(|_| ErrMsg::EmptyVec)
            }),
            x => x,
        }
    }
}

pub fn parser(input: &str, id: u32) -> Option<(Vec<Decl>, Vec<IError>)> {
    let mut err_collect = vec![];
    match super::parser::lex::lex(Span {
        data: input,
        start_offset: 0,
        end_offset: input.len() as u32,
        path_id: id,
    }) {
        Some((_, ret)) => {
            let ret = p_decl.many1_sep(kw(EndLine)).parse(&ret, &mut err_collect);
            match ret {
                Ok(ret) => if ret.0.is_empty() {
                    Some((ret.1, err_collect))
                } else {
                    err_collect.push(IError { msg: ret.0.first().unwrap().map(|_| ErrMsg::Expect(EndLine)) });
                    Some((ret.1, err_collect))
                }
                Err(e) => {
                    err_collect.push(e);
                    Some((vec![], err_collect))
                }
            }
        }
        None => None
    }
}

macro_rules! T {
    [def] => { $crate::L11_macro::parser::TokenKind::DefKeyword };
    [let] => { $crate::L11_macro::parser::TokenKind::LetKeyword };
    [Type] => { $crate::L11_macro::parser::TokenKind::TypeKeyword };
    [this] => { $crate::L11_macro::parser::TokenKind::ThisKeyword };
    [_] => { $crate::L11_macro::parser::TokenKind::Hole };
    ['('] => { $crate::L11_macro::parser::TokenKind::LParen };
    [')'] => { $crate::L11_macro::parser::TokenKind::RParen };
    ['['] => { $crate::L11_macro::parser::TokenKind::LSquare };
    [']'] => { $crate::L11_macro::parser::TokenKind::RSquare };
    ['{'] => { $crate::L11_macro::parser::TokenKind::LCurly };
    ['}'] => { $crate::L11_macro::parser::TokenKind::RCurly };
    [.] => { $crate::L11_macro::parser::TokenKind::Dot };
    [,] => { $crate::L11_macro::parser::TokenKind::Comma };
    [=] => { $crate::L11_macro::parser::TokenKind::Eq };
    [;] => { $crate::L11_macro::parser::TokenKind::Semi };
    [:] => { $crate::L11_macro::parser::TokenKind::Colon };
    [->] => { $crate::L11_macro::parser::TokenKind::Arrow };
    [=>] => { $crate::L11_macro::parser::TokenKind::DoubleArrow };
    ['\\'] => { $crate::L11_macro::parser::TokenKind::Lambda };
}

fn kw<'a: 'b, 'b>(p: TokenKind) -> impl Parser<&'b [TokenNode<'a>], Span<()>, Vec<IError>, IError> {
    move |input: &'b [TokenNode<'a>], _: &mut Vec<IError>| match input.first() {
        Some(x) => if x.data.1 == p {
            input
                .get(1..)
                .map(|i| (i, x.map(|_| ())))
                .ok_or_else(|| IError {
                    msg: x.map(|_| ErrMsg::Expect(p))
                })
        } else {
            Err(IError {
                msg: x.map(|_| ErrMsg::Expect(p))
            })
        },
        _ => Err(IError {
            msg: empty_span(ErrMsg::Expect(p))
        }),
    }
}

fn string<'a: 'b, 'b>(p: TokenKind) -> impl Parser<&'b [TokenNode<'a>], Span<String>, Vec<IError>, IError> {
    move |input: &'b [TokenNode<'a>], _: &mut Vec<IError>| match input.first() {
        Some(x) => if x.data.1 == p {
            input
                .get(1..)
                .map(|i| (i, x.map(|s| s.0.to_owned())))
                .ok_or_else(|| IError {
                    msg: x.map(|_| ErrMsg::Expect(p))
                })
        } else {
            Err(IError {
                msg: x.map(|_| ErrMsg::Expect(p))
            })
        },
        _ => Err(IError {
            msg: empty_span(ErrMsg::Expect(p))
        }),
    }
}

/// ( p )
fn paren<'a: 'b, 'b, P, O>(p: P) -> impl Parser<&'b [TokenNode<'a>], O, Vec<IError>, IError>
where
    P: Parser<&'b [TokenNode<'a>], O, Vec<IError>, IError>,
{
    (kw(LParen), p, kw(RParen)).map(|c| c.1)
}

/// ( p )
fn paren_cut<'a: 'b, 'b, P, O>(p: P) -> impl Parser<&'b [TokenNode<'a>], Option<O>, Vec<IError>, IError>
where
    P: Parser<&'b [TokenNode<'a>], O, Vec<IError>, IError>,
{
    Cut((kw(LParen), p, kw(RParen))).map(|c| c.1)
}

/// [ p ]
fn square<'a: 'b, 'b, P, O>(p: P) -> impl Parser<&'b [TokenNode<'a>], O, Vec<IError>, IError>
where
    P: Parser<&'b [TokenNode<'a>], O, Vec<IError>, IError>,
{
    (kw(LSquare), p, kw(RSquare)).map(|c| c.1)
}

/// [ p ]
fn square_cut<'a: 'b, 'b, P, O>(p: P) -> impl Parser<&'b [TokenNode<'a>], Option<O>, Vec<IError>, IError>
where
    P: Parser<&'b [TokenNode<'a>], O, Vec<IError>, IError>,
{
    Cut((kw(LSquare), p, kw(RSquare))).map(|c| c.1)
}

/// { p }
fn brace<'a: 'b, 'b, P, O>(p: P) -> impl Parser<&'b [TokenNode<'a>], Option<O>, Vec<IError>, IError>
where
    P: Parser<&'b [TokenNode<'a>], O, Vec<IError>, IError>,
{
    Cut((
        kw(LCurly),
        kw(EndLine).option(),
        p,
        kw(EndLine).option(),
        kw(RCurly),
    ))
        .map(|c| c.2)
}

fn p_atom1<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut Vec<IError>) -> IResult<'a, 'b, Raw> {
    string(Ident)
        .map(Raw::Var)
        .or(kw(ThisKeyword).map(|s| Raw::Var(s.map(|_| "this".to_string()))))
        .or(Cut((kw(TypeKeyword), string(Num))).map(|(_, num)| Raw::U(
            num.and_then(|x| x.data.parse::<u32>().ok()).unwrap_or(0)
        )))//TODO:do not unwrap
        .or(kw(Hole).map(|_| Raw::Hole))
        .or(string(Str).map(Raw::LiteralIntro))
        .or(string(Num).map(|x| {
            let num_span = x.map(|x| x.parse::<u64>().unwrap());
            let mut ret = Raw::Var(num_span.to_span().map(|_| "zero".to_owned()));
            let mut num = num_span.data;
            while num > 0 {
                ret = Raw::app(Raw::Var(num_span.to_span().map(|_| "succ".to_owned())), ret);
                num -= 1;
            }
            ret
        }))
        .or(paren_cut(p_raw).map(|x| x.unwrap_or(Raw::Hole)))
        .parse(input, state)
}

fn p_atom<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut Vec<IError>) -> IResult<'a, 'b, Raw> {
    (p_atom1, Cut((kw(T![.]), string(Ident))).many0())
        .map(|(x, t)| t.into_iter().fold(x, |x, t| {
            Raw::Obj(Box::new(x), t.1)
        }))
        .parse(input, state)
        .map_err(|e| IError { msg: e.msg.map(|_| ErrMsg::ExpectAtom) })
}

fn expr_bp<'a: 'b, 'b>(min_bp: u8) -> impl Parser<&'b [TokenNode<'a>], Raw, Vec<IError>, IError> {
    move |input: &'b [TokenNode<'a>], state: &mut Vec<IError>| {
        let (mut input, mut lhs) = p_atom/*.or(
            (string(Op), expr_bp())
        )*/.parse(input, state)?;

        while let Ok((input_t, op)) = string(Op).parse(input, state) {
            input = input_t;

            if let Some((l_bp, ())) = postfix_binding_power(&op) {
                if l_bp < min_bp {
                    break;
                }

                lhs = /*if op == '[' {
                    let rhs = expr_bp(lexer, 0);
                    assert_eq!(lexer.next(), Token::Op(']'));
                    S::Cons(op, vec![lhs, rhs])
                } else*/ {
                    Raw::app(lhs, Raw::Var(op))
                };
                continue;
            }

            if let Some((l_bp, r_bp)) = infix_binding_power(&op) {
                if l_bp < min_bp {
                    break;
                }

                lhs = if &op.data == "?" {
                    let mhs = match expr_bp(0).parse(input, state) {
                        Ok((input_t, mhs)) => {
                            input = input_t;
                            mhs
                        }
                        Err(e) => {
                            state.push(e);
                            Raw::Hole
                        }
                    };
                    match kw(T![:]).parse(input, state) {
                        Ok((input_t, _)) => {
                            input = input_t;
                        }
                        Err(e) => {
                            state.push(e);
                        }
                    }
                    let rhs = match expr_bp(r_bp).parse(input, state) {
                        Ok((input_t, rhs)) => {
                            input = input_t;
                            rhs
                        },
                        Err(e) => {
                            state.push(e);
                            Raw::Hole
                        }
                    };
                    Raw::app(Raw::app(Raw::app(Raw::Var(empty_span("mux".to_owned())), lhs), mhs), rhs)
                } else {
                    let rhs = match expr_bp(r_bp).parse(input, state) {
                        Ok((input_t, rhs)) => {
                            input = input_t;
                            rhs
                        },
                        Err(e) => {
                            state.push(e);
                            Raw::Hole
                        }
                    };
                    Raw::app(Raw::Obj(Box::new(lhs), Some(op)), rhs)
                };
                continue;
            }

            break;
        }

        Ok((input, lhs))
    }
}

fn expr<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut Vec<IError>) -> IResult<'a, 'b, Raw> {
    expr_bp(0).parse(input, state)
}

fn prefix_binding_power(op: &Span<String>) -> ((), u8) {
    match op.data.as_str() {
        "+" | "-" => ((), 19),
        "!" => ((), 30),
        _ => panic!("bad op: {:?}", op),
    }
}

fn postfix_binding_power(op: &Span<String>) -> Option<(u8, ())> {
    let res = match op.data.as_str() {
        "!" => (20, ()),
        "[" => (20, ()),
        _ => return None,
    };
    Some(res)
}

fn infix_binding_power(op: &Span<String>) -> Option<(u8, u8)> {
    let res = match op.data.as_str() {
        "=" => (2, 1),
        "?" => (4, 3),
        "+" | "-" => (15, 16),
        "*" | "/" | "%" => (17, 18),
        "." => (25, 26),
        "::" => (24, 23),
        x => if x.contains(':') {
            (22, 21)
        } else if x.contains(['*', '/', '%']){
            (17, 18)
        } else if x.contains(['+', '-']) {
            (15, 16)
        } else if x.contains(['=', '<', '>']) {
            (13, 14)
        } else if x.contains(['&', '|']) {
            (11, 12)
        } else if x.contains(['^']) {
            (9, 10)
        } else {
            return None
        },
    };
    Some(res)
}

fn p_arg<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut Vec<IError>) -> IResult<'a, 'b, Vec<(Either, Raw)>> {
    let named_impl_arg = square_cut(
        (string(Ident), Cut((kw(Eq), p_raw))).map(|(x, t)| (Either::Name(x), t.1.unwrap_or(Raw::Hole)))
            .or(p_raw.map(|t| (Either::Icit(Icit::Impl), t)))
            .many0_sep(kw(T![,]))
    ).map(|x| x.unwrap_or_default());

    let explicit_arg = expr.map(|t| vec![(Either::Icit(Icit::Expl), t)]);

    let arg_parser = named_impl_arg.or(explicit_arg);

    arg_parser.parse(input, state)
}

fn p_spine<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut Vec<IError>) -> IResult<'a, 'b, Raw> {
    let (input, head) = expr(input, state)?;
    let (input, args) = p_arg.many0().map(|x| x.concat()).parse(input, state)?;

    let result = args.into_iter().fold(head, |acc, (icit, arg)| {
        Raw::App(Box::new(acc), Box::new(arg), icit)
    });

    Ok((input, result))
}

fn p_bind<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut Vec<IError>) -> IResult<'a, 'b, Span<String>> {
    string(Ident).or(string(Hole)).parse(input, state)
}

fn p_lam_binder<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut Vec<IError>,
) -> IResult<'a, 'b, (Span<String>, Either)> {
    let explicit_binder = p_bind.map(|x| (x, Either::Icit(Icit::Expl)));
    let implicit_name_binder = square(
        (string(Ident), Cut((kw(Eq), p_bind))).map(|(x, (_, y))| (y.unwrap_or(empty_span("".to_owned())), Either::Name(x)))
            .or(p_bind.map(|x| (x, Either::Icit(Icit::Impl))))
    );

    explicit_binder
        .or(implicit_name_binder)
        .parse(input, state)
}

fn p_lam<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut Vec<IError>) -> IResult<'a, 'b, Raw> {
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
    state: &mut Vec<IError>,
) -> Result<(&'b [TokenNode<'a>], Vec<(Span<String>, Raw, Icit)>), IError> {
    square_cut(
        (
            p_bind, // 解析一个或多个绑定变量 xs
            (kw(Colon), p_raw).option().map(|x| match x {
                Some((_, x)) => x,
                None => Raw::Hole,
            }),
        )
            .map(|(xs, a)| (xs, a, Icit::Impl))
            .many0_sep(kw(T![,])),
    )
    .map(|x| x.unwrap_or_default())
    .parse(input, state)
}

fn p_pi_impl_binder_option<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut Vec<IError>
) -> IResult<'a, 'b, Vec<(Span<String>, Raw, Icit)>> {
    p_pi_impl_binder
        .option()
        .map(|x| x.unwrap_or_default())
        .parse(input, state)
}

/// (x: A)
fn p_pi_expl_binder<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut Vec<IError>,
) -> IResult<'a, 'b, Vec<(Span<String>, Raw, Icit)>> {
    paren(
        (
            p_bind,                // 解析一个或多个绑定变量 xs
            kw(Colon).with(p_raw), // 解析类型 A
        )
            .map(|(xs, a)| (xs, a.1, Icit::Expl))
            .many0_sep(kw(T![,])),
    )
    .parse(input, state) // 返回 (xs, a, Expl)
}

fn p_pi_binder<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut Vec<IError>,
) -> IResult<'a, 'b, Vec<(Span<String>, Raw, Icit)>> {
    // 组合所有可能的解析器
    p_pi_impl_binder.or(p_pi_expl_binder).parse(input, state)
}

fn p_pi<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut Vec<IError>) -> IResult<'a, 'b, Raw> {
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
fn fun_or_spine<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut Vec<IError>) -> IResult<'a, 'b, Raw> {
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

fn p_let<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut Vec<IError>) -> IResult<'a, 'b, Raw> {
    Cut((
        kw(LetKeyword),
        string(Ident),
        (kw(Colon), p_raw).map(|(_, x)| x).option(),
        kw(Eq),
        p_raw,
        kw(Semi),
        kw(EndLine).option(),
        p_raw,
    ))
        .map(|(_, binder, ann, _, val, _, _, body)| {
            Raw::Let(
                binder.unwrap_or(empty_span("".to_owned())),
                Box::new(ann.flatten().unwrap_or(Raw::Hole)),
                Box::new(val.unwrap_or(Raw::Hole)),
                Box::new(body.unwrap_or(Raw::Hole)),
            )
        })
        .parse(input, state)
}

fn p_pattern<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut Vec<IError>) -> IResult<'a, 'b, Pattern> {
    (
        string(Ident),
        paren_cut(p_pattern.many1_sep(kw(T![,]))).map(|x| x.unwrap_or_default())
            .or(square_cut(p_pattern.map(|x| x.to_impl()).many1_sep(kw(T![,]))).map(|x| x.unwrap_or_default()))
            .many0()
            .map(|x| x.concat()),
    )
        .map(|(x, t)| Pattern::Con(x, t, Icit::Expl))
        .or(kw(T![_]).map(|x| Pattern::Any(x.map(|_| true), Icit::Expl)))
        .parse(input, state)
}

fn p_match<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut Vec<IError>) -> IResult<'a, 'b, Raw> {
    Cut((
        kw(MatchKeyword),
        p_raw,
        brace(
            (kw(CaseKeyword), p_pattern, kw(T![=>]), kw(EndLine).option(), p_raw)
                .map(|(_, pattern, _, _, body)| (pattern, body))
                .many0_sep(kw(EndLine)),
        ),
    ))
        .map(|(_, scrutinee, body)| Raw::Match(
            Box::new(scrutinee.unwrap_or(Raw::Hole)),
            body.flatten().unwrap_or_default()
        ))
        .parse(input, state)
}

fn p_new<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut Vec<IError>) -> IResult<'a, 'b, Raw> {
    Cut((
        kw(NewKeyword),
        string(Ident),
        paren_cut(p_raw.many1_sep(kw(T![,]))),
    ))
        .map(|(_, scrutinee, args)| args.flatten().unwrap_or_default().into_iter()
            .fold(Raw::Var(scrutinee.map_or(empty_span("".to_owned()), |x| x.map(|x| format!("{x}.mk")))), |acc, x| 
                Raw::App(Box::new(acc), Box::new(x), Either::Icit(Icit::Expl))
            ))
        .parse(input, state)
}

fn p_raw<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut Vec<IError>) -> IResult<'a, 'b, Raw> {
    p_lam
        .or(p_let)
        .or(p_pi)
        .or(fun_or_spine)
        .or(p_match)
        .or(p_new)
        .parse(input, state)
        .map_err(|e| IError {
            msg: e.msg.map(|_| ErrMsg::ExpectRaw)
        })
}

fn p_def<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut Vec<IError>) -> IResult<'a, 'b, Decl> {
    Cut((
        kw(DefKeyword),
        string(Ident).or(string(Op)),
        p_pi_binder
            .many0()
            .map(|x| x.into_iter().flatten().collect::<Vec<_>>()),
        (kw(T![:]), p_raw).map(|(_, x)| x).option(),
        kw(T![=]),
        kw(EndLine).option(),
        p_raw,
    ))
        .map(|(_, name, params, ret, _, _, body)| Decl::Def {
            name: name.unwrap_or(empty_span("".to_owned())),
            params: params.unwrap_or_default(),
            ret_type: ret.flatten().unwrap_or(Raw::Hole),
            body: body.unwrap_or(Raw::Hole),
        })
        .parse(input, state)
}

fn p_print<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut Vec<IError>) -> IResult<'a, 'b, Decl> {
    Cut((kw(PrintlnKeyword), p_raw))
        .map(|(_, x)| Decl::Println(x.unwrap_or(Raw::Hole)))
        .parse(input, state)
}

fn p_enum<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut Vec<IError>) -> IResult<'a, 'b, Decl> {
    Cut((
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
                /*paren(p_raw.many0_sep(kw(T![,])))
                    .option()
                    .map(|x| x.unwrap_or_default()),*/
                (
                    kw(T![->]),
                    p_raw,
                )
                    .option()
                    .map(|x| x.map(|y| y.1))
            )
                .many1_sep(kw(EndLine)),
        ),
    ))
        .map(|(_, name, params, fields)| Decl::Enum {
            is_trait: false,
            name: name.unwrap_or(empty_span("".to_owned())),
            params: params.unwrap_or_default(),
            cases: fields.flatten().unwrap_or_default(),
        })
        .parse(input, state)
}

fn p_struct<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut Vec<IError>) -> IResult<'a, 'b, Decl> {
    Cut((
        kw(StructKeyword),
        string(Ident),
        p_pi_impl_binder.option().map(|x| x.unwrap_or_default()),
        brace(
            (string(Ident), kw(T![:]), p_raw)
                .map(|(name, _, ty)| (name, ty))
                .many0_sep(kw(EndLine)), // named fields
        ), /*.or(
               paren(p_raw.many1_sep(kw(T![,]))).map(|fields| {
                   // tuple-like struct with positional fields
                   let mut unnamed_fields = Vec::new();
                   for (idx, field) in fields.into_iter().enumerate() {
                       unnamed_fields.push((empty_span(format!("{idx}")), field));
                   }
                   unnamed_fields
               })
           )*/
    ))
        .map(|(_, name, params, fields)| Decl::Enum {
            is_trait: false,
            name: name.clone().unwrap_or(empty_span("".to_owned())),
            params: params.clone().unwrap_or_default(),
            cases: vec![
                (
                    name.clone().map(|x| x.map(|x| format!("{x}.mk"))).unwrap_or(empty_span("".to_owned())),
                    fields.clone().flatten().unwrap_or_default().into_iter().map(|x| (x.0, x.1, Icit::Expl)).collect(),
                    None,
                ),
            ]
        })
        .parse(input, state)
}

fn p_trait_def<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut Vec<IError>) -> IResult<'a, 'b, Decl> {
    let p_def_declare = (
        kw(DefKeyword),
        string(Ident).or(string(Op)),
        p_pi_binder
            .many0()
            .map(|x| x.into_iter().flatten().collect::<Vec<_>>()),
        (kw(T![:]), p_raw).map(|(_, x)| x),
    )
        .map(|(_, name, params, ret)| (name, params, ret));
    (
        kw(TraitKeyword),
        string(Ident),
        p_pi_impl_binder_option,
        brace(p_def_declare.many0_sep(kw(EndLine))),
    )
        .map(|(_, name, params, body)| Decl::TraitDecl {
            name,
            params,
            methods: body.unwrap_or_default(),
        })
        .parse(input, state)
}

fn p_impl<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut Vec<IError>) -> IResult<'a, 'b, Decl> {
    Cut((
        kw(ImplKeyword),
        p_pi_impl_binder_option,
        (
            string(Ident),
            square_cut(p_raw.many0_sep(kw(T![,]))).option().map(|x| x.flatten().unwrap_or_default()),
            Cut((
                kw(ForKeyword),
                p_raw,
            )),
        ).map(Ok).or(p_raw.map(Err)),
        //p_generic_params(),
        brace(p_def.many0_sep(kw(EndLine))),
    )).map(|x| match x.2 {
        Some(Ok((trait_name, trait_params, (_, name)))) => (x.1, trait_name, trait_params, name.unwrap_or(Raw::Hole), x.3, false),
        Some(Err(name)) => (
            x.1.clone(),
            x.0.map(|_| format!("$trait_name${}", name)),
            x.1.unwrap_or_default().into_iter().map(|x| Raw::Var(x.0)).collect(),
            name,
            x.3,
            true,
        ),
        None => (x.1, empty_span("".to_owned()), vec![], Raw::Hole, x.3, false)
    })
        .map(|(params, trait_name, trait_params, name, body, need_create)| Decl::ImplDecl {
            name,
            params: params.unwrap_or_default(),
            trait_name,
            trait_params,
            methods: body.flatten().unwrap_or_default(),
            need_create,
        })
        .parse(input, state)
}

fn p_decl<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut Vec<IError>) -> IResult<'a, 'b, Decl> {
    p_def.or(p_print).or(p_enum).or(p_struct).or(p_trait_def).or(p_impl)
        .parse(input, state)
        .map_err(|e| IError {
            msg: e.msg.map(|_| ErrMsg::ExpectDecl)
        })
}

#[test]
fn test() {
    let input = r#"
def Eq[A : Type0](x: A, y: A): Type0 = (P : A -> Type0) -> P x -> P y
def refl[A : Type0, x: A]: Eq[A] x x = _ => px => px

def the(A : Type0)(x: A): A = x

def pr1 = f => x => f x
def pr2 = f => x => y => f x y
def pr3 = f => f Type0

def Nat : Type0 =
    (N : Type0) -> (N -> N) -> N -> N
def mul : Nat -> Nat -> Nat =
    a => b => N => s => z => a _ (b _ s) z
def ten : Nat =
    N => s => z => s (s (s (s (s (s (s (s (s (s z)))))))))
def hundred = mul ten ten

println hundred

def mystr = "hello world"

def add_tail(x: String): String = string_concat x "!"

def mystr2 = add_tail mystr

println mystr2

enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

def two = succ succ zero

def t = let one = succ zero;
    succ one

def add(x: Nat, y: Nat): Nat =
    match x {
        case zero => y
        case succ(n) => succ add n y
    }

def four = add two two

println four

struct Point {
    x: Nat
    y: Nat
}

struct Span[T] {
    data: T
    start: Nat
    end: Nat
}

def get_x(p: Point): Nat = p.x

"#;
    println!("{:#?}", parser(input, 0).unwrap());
}

#[test]
fn test1() {
    let input = r#"
def t = match x {
    case zero => a.b :: c.
}
"#;
    println!("{:#?}", parser(input, 0).unwrap());
}
