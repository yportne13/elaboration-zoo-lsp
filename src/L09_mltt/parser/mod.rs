use lex::{TokenKind, TokenNode};
use syntax::{Decl, Either, Icit, Pattern, Raw};

use crate::parser_lib_resilient::*;

mod lex;
pub mod syntax;

use TokenKind::*;

use super::empty_span;

/// Skip to the next EndLine that is immediately followed by a top-level declaration
/// keyword (`def`, `struct`, `enum`, `println`).
///
/// Returns `Some(remaining)` when a sync point is found, or `None` when no sync
/// point exists in the remaining input — allowing the caller to distinguish
/// "found at position 0" (still recover) from "not found at all" (stop).
fn skip_until_decl<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<&'b [TokenNode<'a>]> {
    fn is_decl_kw(kind: TokenKind) -> bool {
        matches!(kind,
            DefKeyword | StructKeyword | EnumKeyword | PrintlnKeyword
        )
    }
    input.iter()
        .enumerate()
        .find(|(i, t)| {
            t.data.1 == EndLine
                && input.get(i + 1).map(|next| is_decl_kw(next.data.1)).unwrap_or(false)
        })
        .map(|(i, _)| &input[i..])
}

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
pub type MacroState = Vec<IError>;

trait ParserExt<I: Copy, A, S> {
    fn many1(self) -> impl Parser<I, Vec<A>, S, IError>;
    fn many1_sep<P: Parser<I, X, S, IError>, X>(self, sep: P) -> impl Parser<I, Vec<A>, S, IError>;
    fn many1_sep_skip<P: Parser<I, X, S, IError>, X, Skip: Fn(I) -> Option<I> + Copy>(self, sep: P, skip: Skip) -> impl Parser<I, Vec<A>, S, IError>;
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
    fn many1_sep_skip<P, X, Skip>(self, sep: P, skip: Skip) -> impl Parser<&'b [TokenNode<'a>], Vec<A>, MacroState, IError>
    where
        P: Parser<&'b [TokenNode<'a>], X, MacroState, IError>,
        Skip: Fn(&'b [TokenNode<'a>]) -> Option<&'b [TokenNode<'a>]> + Copy,
    {
        move |input: &'b [TokenNode<'a>], state: &mut MacroState| {
            let mut input = input;
            let mut result = Vec::new();
            loop {
                match self.parse(input, state) {
                    Ok((i, a)) => {
                        input = i;
                        result.push(a);
                    }
                    Err(_) if result.is_empty() => {
                        return Err(IError {
                            msg: input.first()
                                .map(|x| x.to_span())
                                .unwrap_or(empty_span(()))
                                .map(|_| ErrMsg::Base(BaseMsg::EmptyVec)),
                        });
                    }
                    Err(_) => break,
                }
                if let Ok((i, _)) = sep.parse(input, state) {
                    input = i;
                } else {
                    match skip(input) {
                        Some(at_sep) => {
                            state.push_error(IError {
                                msg: input.first()
                                    .map(|x| x.to_span())
                                    .unwrap_or(empty_span(()))
                                    .map(|_| ErrMsg::Base(BaseMsg::Expect(EndLine)))
                            });
                            match sep.parse(at_sep, state) {
                                Ok((i, _)) => input = i,
                                Err(_) => break,
                            }
                        }
                        None => break,
                    }
                }
            }
            Ok((input, result))
        }
    }
}

/// Parse a declaration file. Returns (declarations, parse errors); a failed
/// declaration is skipped to the next declaration keyword and reported, the
/// successfully parsed prefix is kept.
pub fn parser(input: &str, id: u32) -> Option<(Vec<Decl>, Vec<IError>)> {
    let mut err_collect: MacroState = vec![];
    match super::parser::lex::lex(Span {
        data: input,
        start_offset: 0,
        end_offset: input.len() as u32,
        path_id: id,
    }) {
        Some((_, ret)) => {
            let ret = p_decl
                .recover_with(
                    skip_until_decl,
                    // Placeholder for the lost declaration; an empty println is
                    // used because this lesson has no `Package` no-op.
                    || Decl::Println(Raw::Hole),
                )
                .many1_sep_skip(kw(EndLine), skip_until_decl).parse(&ret, &mut err_collect);
            match ret {
                Ok(ret) => {
                    if ret.0.is_empty() || ret.0.iter().all(|t| t.data.1 == TokenKind::Eof) {
                        Some((ret.1, err_collect))
                    } else {
                        err_collect.push(IError { msg: ret.0.first().unwrap().map(|_| ErrMsg::Base(BaseMsg::Expect(EndLine))) });
                        Some((ret.1, err_collect))
                    }
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
    [def] => { $crate::L09_mltt::parser::TokenKind::DefKeyword };
    [let] => { $crate::L09_mltt::parser::TokenKind::LetKeyword };
    [Type] => { $crate::L09_mltt::parser::TokenKind::TypeKeyword };
    [_] => { $crate::L09_mltt::parser::TokenKind::Hole };
    ['('] => { $crate::L09_mltt::parser::TokenKind::LParen };
    [')'] => { $crate::L09_mltt::parser::TokenKind::RParen };
    ['['] => { $crate::L09_mltt::parser::TokenKind::LSquare };
    [']'] => { $crate::L09_mltt::parser::TokenKind::RSquare };
    ['{'] => { $crate::L09_mltt::parser::TokenKind::LCurly };
    ['}'] => { $crate::L09_mltt::parser::TokenKind::RCurly };
    [.] => { $crate::L09_mltt::parser::TokenKind::Dot };
    [,] => { $crate::L09_mltt::parser::TokenKind::Comma };
    [=] => { $crate::L09_mltt::parser::TokenKind::Eq };
    [;] => { $crate::L09_mltt::parser::TokenKind::Semi };
    [:] => { $crate::L09_mltt::parser::TokenKind::Colon };
    [->] => { $crate::L09_mltt::parser::TokenKind::Arrow };
    [=>] => { $crate::L09_mltt::parser::TokenKind::DoubleArrow };
    ['\\'] => { $crate::L09_mltt::parser::TokenKind::Lambda };
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

/// ( p )
fn paren_cut<'a: 'b, 'b, P, O>(p: P) -> impl Parser<&'b [TokenNode<'a>], Result<O, Span<()>>, MacroState, IError>
where
    P: Parser<&'b [TokenNode<'a>], O, MacroState, IError>,
{
    Cut((kw(LParen), (kw(EndLine).option(), p), (kw(EndLine).option(), kw(RParen))))
        .map(|c| match c.1 {
            Some((_, result)) => Ok(result),
            None => Err(c.0),
        })
}

/// [ p ]
fn square<'a: 'b, 'b, P, O>(p: P) -> impl Parser<&'b [TokenNode<'a>], O, MacroState, IError>
where
    P: Parser<&'b [TokenNode<'a>], O, MacroState, IError>,
{
    (kw(LSquare), kw(EndLine).option(), p, kw(EndLine).option(), kw(RSquare)).map(|c| c.2)
}

/// [ p ]
fn square_cut<'a: 'b, 'b, P, O>(p: P) -> impl Parser<&'b [TokenNode<'a>], Result<O, Span<()>>, MacroState, IError>
where
    P: Parser<&'b [TokenNode<'a>], O, MacroState, IError>,
{
    Cut((kw(LSquare), (kw(EndLine).option(), p), (kw(EndLine).option(), kw(RSquare))))
        .map(|c| match c.1 {
            Some((_, result)) => Ok(result),
            None => Err(c.0),
        })
}

/// { p }
fn brace<'a: 'b, 'b, P, O>(p: P) -> impl Parser<&'b [TokenNode<'a>], Result<O, Span<()>>, MacroState, IError>
where
    P: Parser<&'b [TokenNode<'a>], O, MacroState, IError>,
{
    Cut((
        kw(LCurly),
        (kw(EndLine).option(), p),
        (kw(EndLine).option(), kw(RCurly)),
    ))
        .map(|c| match c.1 {
            Some((_, result)) => Ok(result),
            None => Err(c.0),
        })
}

fn p_atom1<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    string(Ident)
        .map(Raw::Var)
        .or(Cut((kw(TypeKeyword), string(Num))).map(|(_, num)| Raw::U(
            num.and_then(|x| x.data.parse::<u32>().ok()).unwrap_or(0)
        )))//TODO:do not unwrap
        .or(kw(Hole).map(|_| Raw::Hole))
        .or(string(Str).map(|x| Raw::LiteralIntro(x.map(|s| unescape(&s)))))
        .or(paren_cut(p_raw).map(|x| x.unwrap_or_else(|_| Raw::Hole)))
        .parse(input, state)
}

fn p_atom<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    let result = (p_atom1, Cut((kw(T![.]), string(Ident))).option())
        .map(|(x, t)| match t {
            // A single (optional) projection; a missing name after `.` (Cut
            // failure) falls back to an empty projection name — this lesson's
            // Raw::Obj always carries a name.
            Some((_, name)) => Raw::Obj(Box::new(x), name.unwrap_or_else(|| empty_span(String::new()))),
            None => x,
        })
        .parse(input, state);
    match result {
        Ok(ok) => Ok(ok),
        Err(_e) => Err(IError {
            msg: input
                .first()
                .map(|x| x.map(|_| ErrMsg::Base(BaseMsg::ExpectAtom)))
                .unwrap_or(empty_span(ErrMsg::Base(BaseMsg::ExpectAtom)))
        })
    }
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
    (p_lam_binder.many1(), Cut((kw(T![=>]), (kw(EndLine).option(), p_raw))))
        .map(|(binder, (_arrow, body))| {
            // body: Option<(Option<Span<()>>, Raw)> — a missing body after =>
            // becomes a hole and the error is already recorded by the Cut.
            let ty = body.map(|(_, raw)| raw).unwrap_or(Raw::Hole);
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
) -> Result<(&'b [TokenNode<'a>], Vec<(Span<String>, Raw, Icit)>), IError> {
    square_cut(
        (
            p_bind,
            (kw(Colon), p_raw).option(),
        )
            .map(|(xs, opt)| {
                let a = match opt {
                    Some((_, x)) => x,
                    None => Raw::Hole,
                };
                (xs, a, Icit::Impl)
            })
            .many0_sep((kw(T![,]), kw(EndLine).option())),
    )
    .parse(input, state)
    .and_then(|(i, result)| match result {
        Ok(v) => Ok((i, v)),
        Err(square_span) => Err(IError { msg: square_span.map(|_| ErrMsg::Base(BaseMsg::Expect(TokenKind::LSquare))) }),
    })
}

fn p_pi_impl_binder_option<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut MacroState
) -> IResult<'a, 'b, Vec<(Span<String>, Raw, Icit)>> {
    p_pi_impl_binder
        .option()
        .map(|x| x.unwrap_or_default())
        .parse(input, state)
}

/// (x: A)
fn p_pi_expl_binder<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut MacroState,
) -> IResult<'a, 'b, Vec<(Span<String>, Raw, Icit)>> {
    paren(
        (
            p_bind,                // 解析一个或多个绑定变量 xs
            kw(Colon).with(p_raw), // 解析类型 A
        )
            .map(|(xs, a)| (xs, a.1, Icit::Expl))
            .many0_sep((kw(T![,]), kw(EndLine).option())),
    )
    .parse(input, state) // 返回 (xs, a, Expl)
}

fn p_pi_binder<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut MacroState,
) -> IResult<'a, 'b, Vec<(Span<String>, Raw, Icit)>> {
    // 组合所有可能的解析器
    p_pi_impl_binder.or(p_pi_expl_binder).parse(input, state)
}

fn p_pi<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    (p_pi_binder.many1(), Cut((kw(T![->]), (kw(EndLine).option(), p_raw))))
        .map(|(binder, (_arrow, ty))| {
            // ty: Option<(Option<Span<()>>, Raw)>
            let ty = ty.map(|(_, raw)| raw).unwrap_or(Raw::Hole);
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
    // After `let` is matched, Cut commits the parser: any subsequent error
    // is pushed to the error store (state) and the element becomes `None`,
    // allowing the parser to continue and collect further errors.
    Cut((
        kw(LetKeyword),
        string(Ident),
        (kw(Colon), kw(EndLine).option(), p_raw).map(|(_, _, x)| x).option(),
        kw(Eq),
        // Allow newline after `=` before the value, like `def`
        (kw(EndLine).option(), p_raw),
        kw(Semi),
        kw(EndLine).many0(),
        p_raw,
    ))
        .map(|(let_kw, binder, ann, _, val, _, _, body)| {
            Raw::Let(
                binder.unwrap_or(let_kw.end_span().map(|_| String::new())),
                Box::new(ann.flatten().unwrap_or(Raw::Hole)),
                Box::new(val.map(|(_, raw)| raw).unwrap_or(Raw::Hole)),
                Box::new(body.unwrap_or(Raw::Hole)),
            )
        })
        .parse(input, state)
}

fn p_pattern<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Pattern> {
    (
        string(Ident),
        paren_cut(p_pattern.many0_sep(kw(T![,])))
            .map(|x| x.ok().unwrap_or_default())
            .or(square_cut(p_pattern.map(|x| x.to_impl()).many0_sep(kw(T![,]))).map(|x| x.ok().unwrap_or_default()))
            .many0()
            .map(|x| x.concat()),
    )
        .map(|(x, t)| Pattern::Con(x, t, Icit::Expl))
        .or(kw(T![_]).map(|x| Pattern::Any(x, Icit::Expl)))
        .parse(input, state)
}

fn p_match<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    Cut((
        kw(MatchKeyword),
        p_raw,
        brace(
            // Like p_lam: Cut only after => so that once => is matched the
            // parser commits. Body failure → Hole + error in state, arm is
            // still collected and many0_sep continues to the next arm.
            Cut((kw(CaseKeyword), p_pattern, Cut((kw(T![=>]), (kw(EndLine).option(), p_raw)))))
                .map(|(case_kw, pattern, body_outer)| {
                    let pattern = pattern.unwrap_or(Pattern::Any(
                        case_kw.end_span(),
                        Icit::Expl,
                    ));
                    // body_outer: Option<(arrow_span, Option<(EndLine, Raw)>)>
                    let body = body_outer.and_then(|(_, inner)| inner)
                        .map(|(_, raw)| raw)
                        .unwrap_or(Raw::Hole);
                    (pattern, body)
                })
                .many0_sep(kw(EndLine)),
        ),
    ))
        .map(|(_match_kw, scrutinee, body)| Raw::Match(
            Box::new(scrutinee.unwrap_or(Raw::Hole)),
            body.and_then(|r| r.ok()).unwrap_or_default()
        ))
        .parse(input, state)
}

fn p_new<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    Cut((
        kw(NewKeyword),
        string(Ident),
        paren_cut(p_raw.many0_sep(kw(T![,]))),
    ))
        .map(|(new_kw, scrutinee, args)| args.and_then(|r| r.ok()).unwrap_or_default().into_iter()
            .fold(Raw::Var(scrutinee.map_or(new_kw.to_span().map(|_| String::new()), |x| x.map(|x| format!("{x}.mk")))), |acc, x| 
                Raw::App(Box::new(acc), Box::new(x), Either::Icit(Icit::Expl))
            ))
        .parse(input, state)
}

fn p_raw<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    p_lam
        .or(p_let)
        .or(p_pi)
        .or(fun_or_spine)
        .or(p_match)
        .or(p_new)
        .parse(input, state)
        .map_err(|_e| IError {
            msg: input
                .first()
                .map(|x| x.map(|_| ErrMsg::Base(BaseMsg::ExpectRaw)))
                .unwrap_or(empty_span(ErrMsg::Base(BaseMsg::ExpectRaw)))
        })
}

fn p_def<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
    Cut((
        kw(DefKeyword),
        string(Ident),
        p_pi_binder
            .many0()
            .map(|x| x.into_iter().flatten().collect::<Vec<_>>()),
        (kw(T![:]), kw(EndLine).option(), p_raw).map(|(_, _, x)| x).option(),
        kw(T![=]),
        kw(EndLine).option(),
        p_raw,
    ))
        .map(|(def_kw, name, params, ret, _eq_kw, _, body)| Decl::Def {
            name: name.unwrap_or(def_kw.end_span().map(|_| String::new())),
            params: params.unwrap_or_default(),
            ret_type: ret.flatten().unwrap_or(Raw::Hole),
            body: body.unwrap_or(Raw::Hole),
        })
        .parse(input, state)
}

fn p_print<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
    Cut((kw(PrintlnKeyword), p_raw))
        .map(|(println_kw, x)| Decl::Println(x.unwrap_or(Raw::Hole)))
        .parse(input, state)
}

fn p_enum<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
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
        .map(|(enum_kw, name, params, fields)| Decl::Enum {
            name: name.unwrap_or(enum_kw.end_span().map(|_| String::new())),
            params: params.unwrap_or_default(),
            cases: fields.and_then(|r| r.ok()).unwrap_or_default(),
        })
        .parse(input, state)
}

fn p_struct<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
    Cut((
        kw(StructKeyword),
        string(Ident),
        p_pi_impl_binder.option().map(|x| x.unwrap_or_default()),
        brace(
            (string(Ident), kw(T![:]), p_raw)
                .map(|(name, _, ty)| (name, ty))
                .many0_sep(kw(EndLine)), // named fields
        ),
    ))
        .map(|(struct_kw, name, params, fields)| Decl::Enum {
            name: name.clone().unwrap_or(struct_kw.end_span().map(|_| String::new())),
            params: params.clone().unwrap_or_default(),
            cases: vec![
                (
                    name.clone().map(|x| x.map(|x| format!("{x}.mk"))).unwrap_or(struct_kw.end_span().map(|_| String::new())),
                    fields.clone().and_then(|r| r.ok()).unwrap_or_default().into_iter().map(|x| (x.0, x.1, Icit::Expl)).collect(),
                    None,
                ),
            ]
        })
        .parse(input, state)
}

fn p_decl<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
    p_def.or(p_print).or(p_enum).or(p_struct)
        .parse(input, state)
        .map_err(|e| IError {
            msg: e.msg.map(extract_base)
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
    let (decls, errs) = parser(input, 0).unwrap();
    assert!(errs.is_empty(), "unexpected parse errors: {:?}", errs);
    println!("{:#?}", decls);
}

#[test]
fn test_bad_decl_reported_prefix_kept() {
    // A declaration that fails to parse is reported; the successfully parsed
    // surrounding declarations survive (no silent drop, no total abort).
    let input = r#"def ok: Type0 = Type0
def = 1
def ok2: Type0 = Type0
"#;
    let (decls, errs) = parser(input, 0).unwrap();
    assert!(!errs.is_empty(), "the broken decl must be reported");
    let names: Vec<&str> = decls.iter().filter_map(|d| match d {
        Decl::Def { name, .. } => Some(name.data.as_str()),
        _ => None,
    }).collect();
    assert!(names.contains(&"ok") && names.contains(&"ok2"),
        "declarations before AND after the broken decl must survive, got {:?}", names);
}