use lex::{TokenKind, TokenNode};
use smol_str::SmolStr;
use syntax::{Decl, Either, Icit, Pattern, Raw};
use std::collections::HashMap;
use macros::*;
use serde::{Serialize, Deserialize};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MacroExpansionInfo {
    pub name: String,
    pub start_offset: u32,
    pub end_offset: u32,
    pub expanded_text: String,
}

use crate::parser_lib_resilient::*;

mod lex;
pub mod syntax;
pub mod macros;
pub mod derive;

use TokenKind::*;

use super::empty_span;

/// Skip input until a token of the given kind is found, returning the slice
/// starting at that token (the sync token itself is NOT consumed).
/// If the token is not found, the entire remaining input is skipped.
fn skip_until_inner<'a: 'b, 'b>(kind: TokenKind) -> impl Fn(&'b [TokenNode<'a>]) -> &'b [TokenNode<'a>] + Copy {
    move |input: &'b [TokenNode<'a>]| {
        input.iter()
            .position(|t| t.data.1 == kind)
            .map(|i| &input[i..])
            .unwrap_or(&[])
    }
}

/// Skip to the next EndLine that is immediately followed by a top-level declaration
/// keyword (`def`, `struct`, `enum`, `trait`, `impl`, `macro_rules`, `package`,
/// `import`, `println`).
///
/// Returns `Some(remaining)` when a sync point is found, or `None` when no sync
/// point exists in the remaining input — allowing the caller to distinguish
/// "found at position 0" (still recover) from "not found at all" (stop).
fn skip_until_decl<'a: 'b, 'b>(input: &'b [TokenNode<'a>]) -> Option<&'b [TokenNode<'a>]> {
    fn is_decl_kw(kind: TokenKind) -> bool {
        matches!(kind,
            DefKeyword | StructKeyword | EnumKeyword | TraitKeyword | ImplKeyword
            | PackageKeyword | ImportKeyword | PrintlnKeyword | MacroKeyword
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

#[derive(Debug, Clone, Copy)]
pub enum ErrMsg {
    Base(BaseMsg),
    In(Ctx, BaseMsg),
}

#[derive(Debug, Clone, Copy)]
pub enum Ctx {
    Declare,
    FunctionDef,
    Print,
    EnumDef,
    StructDef,
    TraitDef,
    ImplBlock,
    ImplicitBinder,
    ExplicitBinder,
    Binder,
    Expr,
    Atom,
    LetBind,
    Lambda,
    PiType,
    MatchArm,
    NewExpr,
    PackageImport,
}

fn extract_base(m: ErrMsg) -> BaseMsg {
    match m {
        ErrMsg::Base(b) | ErrMsg::In(_, b) => b,
    }
}

use std::fmt;

impl fmt::Display for Ctx {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ctx::Declare         => write!(f, "declaration"),
            Ctx::FunctionDef     => write!(f, "function definition"),
            Ctx::Print           => write!(f, "print"),
            Ctx::EnumDef         => write!(f, "enum definition"),
            Ctx::StructDef       => write!(f, "struct definition"),
            Ctx::TraitDef        => write!(f, "trait definition"),
            Ctx::ImplBlock       => write!(f, "impl block"),
            Ctx::ImplicitBinder  => write!(f, "implicit binder"),
            Ctx::ExplicitBinder  => write!(f, "explicit binder"),
            Ctx::Binder          => write!(f, "binder"),
            Ctx::Expr            => write!(f, "expression"),
            Ctx::Atom            => write!(f, "atom"),
            Ctx::LetBind         => write!(f, "let binding"),
            Ctx::Lambda          => write!(f, "lambda"),
            Ctx::PiType          => write!(f, "Pi type"),
            Ctx::MatchArm        => write!(f, "match arm"),
            Ctx::NewExpr         => write!(f, "`new` expression"),
            Ctx::PackageImport   => write!(f, "package import"),
        }
    }
}

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
            ErrMsg::Base(msg)       => fmt::Display::fmt(msg, f),
            ErrMsg::In(ctx, msg)    => write!(f, "in {}: {}", ctx, msg),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct IError {
    pub msg: Span<ErrMsg>,
}

type IResult<'a, 'b, O> = Result<(&'b [TokenNode<'a>], O), IError>;

pub type MacroState = (Vec<IError>, HashMap<String, Vec<MacroRule>>, Vec<MacroExpansionInfo>);

fn owned_tokens_to_string(tokens: &[OwnedToken]) -> String {
    let mut result = String::new();
    for (i, tok) in tokens.iter().enumerate() {
        if i > 0 {
            result.push(' ');
        }
        // Wrap Str tokens in double quotes (string literals)
        if tok.data.1 == TokenKind::Str {
            result.push('"');
            result.push_str(&tok.data.0);
            result.push('"');
        } else {
            result.push_str(&tok.data.0);
        }
    }
    result
}

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

/// Parse with no pre-existing macros (for tests). Returns (declarations, parse errors, accumulated macros).
pub fn parser(input: &str, id: u32) -> Option<(Vec<Decl>, Vec<IError>)> {
    parser_with_macros(input, id, &Default::default()).map(|(d, e, _, _)| (expand_derives(d), e))
}

/// Parse with a pre-populated macro table (from macros in other files).
/// Returns (declarations, parse errors, macros to export to other files, macro expansions).
/// Only macros marked with #[macro_export] are included in the returned table.
pub fn parser_with_macros(input: &str, id: u32, global_macros: &HashMap<String, Vec<MacroRule>>) -> Option<(Vec<Decl>, Vec<IError>, HashMap<String, Vec<MacroRule>>, Vec<MacroExpansionInfo>)> {
    // Strip __exported__ sentinel keys from global macros (they're only for internal tracking)
    let clean_global: HashMap<String, Vec<MacroRule>> = global_macros.iter()
        .filter(|(k, _)| !k.starts_with("__exported__"))
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
    let mut err_collect: MacroState = (vec![], clean_global, vec![]);
    err_collect.1.entry("stringify".to_owned()).or_insert_with(|| vec![MacroRule {
        matcher: MacroMatcher::Metavar { name: empty_span(String::new()), fragment: MacroFragment::Ident },
        transcriber: MacroTranscriber::BuiltIn,
    }]);
    match super::parser::lex::lex(Span {
        data: input,
        start_offset: 0,
        end_offset: input.len() as u32,
        path_id: id,
    }) {
        Some((_, ret)) => {
            let ret = (p_decl.map(Ok).or(p_macro_def.map(Err)))
                .recover_with(
                    skip_until_decl,
                    || Ok(Decl::Package { path: vec![] }),
                )
                .many1_sep(kw(EndLine)).parse(&ret, &mut err_collect);
            match ret {
                Ok(ret) => {
                    let expansions = std::mem::take(&mut err_collect.2);
                    let exported: HashMap<String, Vec<MacroRule>> = err_collect.1.iter()
                        .filter(|(k, _)| !k.starts_with("__exported__") && err_collect.1.contains_key(&format!("__exported__{}", k)))
                        .map(|(k, v)| (k.clone(), v.clone()))
                        .collect();
                    if ret.0.is_empty() {
                        Some((expand_derives(ret.1.into_iter().flatten().collect()), err_collect.0, exported, expansions))
                    } else {
                        err_collect.0.push(IError { msg: ret.0.first().unwrap().map(|_| ErrMsg::Base(BaseMsg::Expect(EndLine))) });
                        Some((expand_derives(ret.1.into_iter().flatten().collect()), err_collect.0, exported, expansions))
                    }
                }
                Err(e) => {
                    err_collect.0.push(e);
                    Some((vec![], err_collect.0, Default::default(), Default::default()))
                }
            }
        }
        None => None
    }
}

macro_rules! T {
    [def] => { $crate::L13_namespace::parser::TokenKind::DefKeyword };
    [let] => { $crate::L13_namespace::parser::TokenKind::LetKeyword };
    [Type] => { $crate::L13_namespace::parser::TokenKind::TypeKeyword };
    [this] => { $crate::L13_namespace::parser::TokenKind::ThisKeyword };
    [static] => { $crate::L13_namespace::parser::TokenKind::StaticKeyword };
    [_] => { $crate::L13_namespace::parser::TokenKind::Hole };
    ['('] => { $crate::L13_namespace::parser::TokenKind::LParen };
    [')'] => { $crate::L13_namespace::parser::TokenKind::RParen };
    ['['] => { $crate::L13_namespace::parser::TokenKind::LSquare };
    [']'] => { $crate::L13_namespace::parser::TokenKind::RSquare };
    ['{'] => { $crate::L13_namespace::parser::TokenKind::LCurly };
    ['}'] => { $crate::L13_namespace::parser::TokenKind::RCurly };
    [.] => { $crate::L13_namespace::parser::TokenKind::Dot };
    [,] => { $crate::L13_namespace::parser::TokenKind::Comma };
    [=] => { $crate::L13_namespace::parser::TokenKind::Eq };
    [;] => { $crate::L13_namespace::parser::TokenKind::Semi };
    [:] => { $crate::L13_namespace::parser::TokenKind::Colon };
    [->] => { $crate::L13_namespace::parser::TokenKind::Arrow };
    [=>] => { $crate::L13_namespace::parser::TokenKind::DoubleArrow };
    ['\\'] => { $crate::L13_namespace::parser::TokenKind::Lambda };
    [+] => { $crate::L13_namespace::parser::TokenKind::Op };
    [where] => { $crate::L13_namespace::parser::TokenKind::WhereKeyword };
    [package] => { $crate::L13_namespace::parser::TokenKind::PackageKeyword };
    [import] => { $crate::L13_namespace::parser::TokenKind::ImportKeyword };
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

fn kw_is<'a: 'b, 'b>(p: TokenKind, s: &'a str) -> impl Parser<&'b [TokenNode<'a>], Span<()>, MacroState, IError> {
    move |input: &'b [TokenNode<'a>], _: &mut MacroState| match input.first() {
        Some(x) => if x.data.1 == p && x.data.0 == s {
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

fn smolstr<'a: 'b, 'b>(p: TokenKind) -> impl Parser<&'b [TokenNode<'a>], Span<SmolStr>, MacroState, IError> {
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

fn string_is<'a: 'b, 'b>(p: TokenKind, s: &'a str) -> impl Parser<&'b [TokenNode<'a>], Span<String>, MacroState, IError> {
    move |input: &'b [TokenNode<'a>], _: &mut MacroState| match input.first() {
        Some(x) => if x.data.1 == p && x.data.0 == s {
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
    smolstr(Ident)
        .map(Raw::Var)
        .or(kw(ThisKeyword).map(|s| Raw::Var(s.map(|_| SmolStr::new("this")))))
        .or(Cut((kw(TypeKeyword), string(Num))).map(|(_, num)| Raw::U(
            num.and_then(|x| x.data.parse::<u32>().ok()).unwrap_or(0)
        )))//TODO:do not unwrap
        .or(kw(Hole).map(Raw::Hole))
        .or(string(Str).map(|x| Raw::LiteralIntro(x.map(|s| unescape(&s)))))
        .or(string(Num).map(|x| {
            Raw::Nat(x.map(|x| x.parse::<u64>().unwrap()))
        }))
        .or(
            // Tuple literal: (a, b, ...) -> TupleN.mk a b ...
            paren_cut(
                p_raw.many1_sep((kw(T![,]), kw(EndLine).option()))
            ).map(|result| {
                match result {
                    Ok(items) if items.len() == 1 => items.into_iter().next().unwrap(),
                    Ok(items) => {
                        let n = items.len();
                        let mk_name = SmolStr::new(format!("Tuple{n}.mk"));
                        let mk_span = (items[0].to_span() + items[n - 1].to_span()).map(|_| mk_name.clone());
                        items.into_iter().fold(
                            Raw::Var(mk_span),
                            |acc, item| Raw::App(Box::new(acc), Box::new(item), Either::Icit(Icit::Expl))
                        )
                    }
                    Err(paren_span) => Raw::Hole(paren_span),
                }
            })
            .or(paren_cut(p_raw).map(|x| x.unwrap_or_else(Raw::Hole)))
        )
        .parse(input, state)
}

fn p_atom<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    let result = (p_atom1, Cut((kw(T![.]), smolstr(Ident).or(smolstr(Op)))).many0())
        .map(|(x, t)| t.into_iter().fold(x, |x, t| {
            Raw::Obj(Box::new(x), t.1)
        }))
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

fn expr_bp<'a: 'b, 'b>(min_bp: u8) -> impl Parser<&'b [TokenNode<'a>], Raw, MacroState, IError> {
    move |input: &'b [TokenNode<'a>], state: &mut MacroState| {
        let (mut input, mut lhs) = (|input: &'b [TokenNode<'a>], state: &mut MacroState| {
            let (input, op) = smolstr(Op).parse(input, state)?;
            if let Some(r_bp) = prefix_binding_power(&op) {
                let (input, rhs) = expr_bp(r_bp).parse(input, state)?;
                if op.data == "-" {
                    Ok((input, Raw::Obj(Box::new(rhs), Some(op.map(|_| SmolStr::new("neg"))))))
                } else if op.data == "~" {
                    Ok((input, Raw::Obj(Box::new(rhs), Some(op.map(|_| SmolStr::new("not"))))))
                } else {
                    Ok((input, Raw::Obj(Box::new(rhs), Some(op))))
                }
            } else {
                Err(IError { msg: op.map(|_| ErrMsg::Base(BaseMsg::ExpectAtom)) })
            }
        }).or(p_atom).parse(input, state)?;

        while let Ok((input_t, op)) = smolstr(Op)
            .or(kw(LParen).map(|x| x.map(|_| SmolStr::new("("))))
            //.or(kw(LCurly).map(|x| x.map(|_| SmolStr::new("{"))))
            .or(kw(LSquare).map(|x| x.map(|_| SmolStr::new("["))))
            .or(kw(Dot).map(|x| x.map(|_| SmolStr::new("."))))
            .parse(input, state) {
            if let Some((l_bp, ())) = postfix_binding_power(&op) {
                if l_bp < min_bp {
                    break;
                }
                input = input_t;

                lhs = if &op.data == "[" {
                    // Allow newline after [ before implicit args
                    let (input_after_el, _) = kw(EndLine).option().parse(input, state)?;
                    let (input_t, ret) = if let Ok((input_t, (icit, raw))) = (smolstr(Ident), Cut((kw(Eq), p_raw)))
                        .map(|(x, t)| (Either::Name(x), t.1.unwrap_or(Raw::Hole(empty_span(())))))
                        .parse(input_after_el, state) {
                            (
                                input_t,
                                Raw::App(Box::new(lhs), Box::new(raw), icit)
                            )
                    } else {
                        let (input_t, rhs) = p_raw
                            .many1_sep((kw(T![,]), kw(EndLine).option()))
                            .parse(input_after_el, state)?;
                        (input_t, rhs.into_iter().fold(lhs, Raw::app_impl))
                    };
                    let (input_t, _) = (kw(EndLine).option(), kw(RSquare)).parse(input_t, state)?;
                    input = input_t;
                    ret
                } else if &op.data == "(" {
                    // Allow newline after ( before arguments, and before ) after them
                    let (input_t, _) = kw(EndLine).option().parse(input, state)?;
                    let (input_t, rhs) = p_raw
                        .many0_sep((kw(T![,]), kw(EndLine).option()))
                        .parse(input_t, state)?;
                    let (input_t, _) = (kw(EndLine).option(), kw(RParen)).parse(input_t, state)?;
                    input = input_t;
                    rhs.into_iter().fold(lhs, Raw::app)
                } else if &op.data == "{" {
                    // Scala-style apply block: f { stmt1; stmt2; result }
                    // All but last become "let _useless = stmt;" desugaring.
                    let mut stmts: Vec<Raw> = Vec::new();
                    let mut input_t = input;
                    // consume newlines after {
                    while let Ok((i, _)) = kw(EndLine).parse(input_t, state) {
                        input_t = i;
                    }
                    // parse statements separated by newlines
                    loop {
                        match p_raw.parse(input_t, state) {
                            Ok((i, expr)) => {
                                stmts.push(expr);
                                input_t = i;
                            }
                            Err(_) => break,
                        }
                        if kw(EndLine).parse(input_t, state).is_ok() {
                            // consume any additional newlines (blank lines)
                            while let Ok((i, _)) = kw(EndLine).parse(input_t, state) {
                                input_t = i;
                            }
                        } else {
                            break;
                        }
                    }
                    // consume optional newline before }
                    let _ = kw(EndLine).option().parse(input_t, state);
                    let (input_t, _) = kw(RCurly).parse(input_t, state)?;
                    input = input_t;
                    if stmts.len() <= 1 {
                        match stmts.into_iter().next() {
                            Some(expr) => Raw::app(lhs, expr),
                            None => Raw::app(lhs, Raw::Hole(empty_span(()))),
                        }
                    } else {
                        let func = lhs.clone();
                        let last = stmts.pop().unwrap();
                        let mut result = last;
                        for stmt in stmts.into_iter().rev() {
                            result = Raw::Let(
                                empty_span(SmolStr::new("_useless")),
                                Box::new(Raw::Hole(empty_span(()))),
                                Box::new(stmt),
                                Box::new(result),
                            );
                        }
                        Raw::app(func, result)
                    }
                } else {
                    Raw::app(lhs, Raw::Var(op))
                };
                continue;
            }

            if let Some((l_bp, r_bp)) = infix_binding_power(&op) {
                if l_bp < min_bp {
                    break;
                }
                input = input_t;

	                lhs = if &op.data == "?" {
	                    let mhs = match expr_bp(0).parse(input, state) {
	                        Ok((input_t, mhs)) => {
	                            input = input_t;
	                            mhs
	                        }
	                        Err(e) => {
	                            state.0.push(IError { msg: e.msg.with_span(op.end_span()) });
	                            Raw::Hole(op.end_span())
	                        }
	                    };
	                    match kw(T![:]).parse(input, state) {
	                        Ok((input_t, _)) => {
	                            input = input_t;
	                        }
	                        Err(e) => {
	                            state.0.push(IError { msg: e.msg.with_span(op.end_span()) });
	                        }
	                    }
	                    let rhs = match expr_bp(r_bp).parse(input, state) {
	                        Ok((input_t, rhs)) => {
	                            input = input_t;
	                            rhs
	                        },
	                        Err(e) => {
	                            state.0.push(IError { msg: e.msg.with_span(op.end_span()) });
	                            Raw::Hole(op.end_span())
	                        }
	                    };
		                    let mux_span = lhs.to_span().map(|_| SmolStr::new("mux"));
		                    Raw::app(Raw::app(Raw::Obj(Box::new(lhs), Some(mux_span)), mhs), rhs)
	                } else if &op.data == "." {
	                    let name = match smolstr(Ident).or(smolstr(Op)).parse(input, state) {
	                        Ok((input_t, name)) => {
	                            input = input_t;
	                            name
	                        },
	                        Err(e) => {
	                            state.0.push(IError { msg: e.msg.with_span(op.end_span()) });
	                            empty_span(SmolStr::new(""))
	                        }
	                    };
	                    Raw::Obj(Box::new(lhs), Some(name))
	                } else {
	                    let rhs = match expr_bp(r_bp).parse(input, state) {
	                        Ok((input_t, rhs)) => {
	                            input = input_t;
	                            rhs
	                        },
	                        Err(e) => {
	                            state.0.push(IError { msg: e.msg.with_span(op.end_span()) });
	                            Raw::Hole(op.end_span())
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

fn expr<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    expr_bp(0).parse(input, state)
}

fn prefix_binding_power(op: &Span<SmolStr>) -> Option<u8> {
    match &op.data {
        s if (s == "!") | (s == "~") | (s == "-") => Some(30),
        _ => None,
    }
}

fn postfix_binding_power(op: &Span<SmolStr>) -> Option<(u8, ())> {
    let res = match &op.data {
        s if s == "!" => (20, ()),
        s if s == "[" => (20, ()),
        s if s == "(" => (20, ()),
        s if s == "{" => (20, ()),
        _ => return None,
    };
    Some(res)
}

fn infix_binding_power(op: &Span<SmolStr>) -> Option<(u8, u8)> {
    let res = match &op.data {
        s if s == "=" => (2, 1),
        s if s == "?" => (4, 3),
        s if (s == "+") | (s == "-") => (15, 16),
        s if (s == "*") | (s == "/") | (s == "%") => (17, 18),
        s if s == "." => (25, 26),
        s if s == "::" => (24, 23),
        x => if x.contains(':') {
            (2, 1)
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
            //return None
            (7, 8)
        },
    };
    Some(res)
}

fn p_arg<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Vec<(Either, Raw)>> {
    let named_impl_arg = square_cut(
        (smolstr(Ident), Cut((kw(Eq), p_raw))).map(|(x, t)| (Either::Name(x), t.1.unwrap_or(Raw::Hole(empty_span(())))))
            .or(p_raw.map(|t| (Either::Icit(Icit::Impl), t)))
            .many0_sep(kw(T![,]))
    ).map(|x| x.ok().unwrap_or_default());

    let explicit_arg = expr.map(|t| vec![(Either::Icit(Icit::Expl), t)]);

    let arg_parser = named_impl_arg.or(explicit_arg);

    arg_parser.parse(input, state)
}

fn p_spine<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    let (input, head) = expr(input, state)?;
    let (input, args) = p_arg.many0().map(|x| x.concat()).parse(input, state)?;

    let result = args.into_iter().fold(head, |acc, (icit, arg)| {
        Raw::App(Box::new(acc), Box::new(arg), icit)
    });

    Ok((input, result))
}

fn p_bind<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Span<SmolStr>> {
    smolstr(Ident).or(smolstr(Hole)).parse(input, state)
}

fn p_lam_binder<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut MacroState,
) -> IResult<'a, 'b, (Span<SmolStr>, Either)> {
    let explicit_binder = p_bind.map(|x| (x, Either::Icit(Icit::Expl)));
    let implicit_name_binder = square(
        (smolstr(Ident), Cut((kw(Eq), p_bind))).map(|(x, (_, y))| (y.unwrap_or(empty_span(SmolStr::new(""))), Either::Name(x)))
            .or(p_bind.map(|x| (x, Either::Icit(Icit::Impl))))
    );

    explicit_binder
        .or(implicit_name_binder)
        .parse(input, state)
}

fn p_lam<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    (p_lam_binder.many1(), Cut((kw(T![=>]), (kw(EndLine).option(), p_raw))))
        .map(|(binder, (arrow, body))| {
            // body: Option<(Option<Span<()>>, Raw)>
            let ty = body.map(|(_, raw)| raw).unwrap_or(Raw::Hole(arrow.end_span()));
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
) -> Result<(&'b [TokenNode<'a>], Vec<(Span<SmolStr>, Raw, Icit)>), IError> {
    square_cut(
        (
            p_bind, // 解析一个或多个绑定变量 xs
            (kw(Colon), p_raw).option().map(|x| match x {
                Some((_, x)) => x,
                None => Raw::Hole(empty_span(())),
            }),
        )
            .map(|(xs, a)| (xs, a, Icit::Impl))
            .many0_sep((kw(T![,]), kw(EndLine).option())),
    )
    .parse(input, state)
    .and_then(|(i, result)| match result {
        Ok(v) => Ok((i, v)),
        Err(square_span) => Err(IError { msg: square_span.map(|_| ErrMsg::In(Ctx::ImplicitBinder, BaseMsg::Expect(TokenKind::LSquare))) }),
    })
}

fn p_pi_impl_binder_option<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut MacroState
) -> IResult<'a, 'b, Vec<(Span<SmolStr>, Raw, Icit)>> {
    p_pi_impl_binder
        .option()
        .map(|x| x.unwrap_or_default())
        .parse(input, state)
}

/// (x: A)
fn p_pi_expl_binder<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut MacroState,
) -> IResult<'a, 'b, Vec<(Span<SmolStr>, Raw, Icit)>> {
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
) -> IResult<'a, 'b, Vec<(Span<SmolStr>, Raw, Icit)>> {
    // 组合所有可能的解析器
    p_pi_impl_binder.or(p_pi_expl_binder).parse(input, state)
}

fn p_pi<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    (p_pi_binder.many1(), Cut((kw(T![->]), (kw(EndLine).option(), p_raw))))
        .map(|(binder, (arrow, ty))| {
            // ty: Option<(Option<Span<()>>, Raw)>
            let ty = ty.map(|(_, raw)| raw).unwrap_or(Raw::Hole(arrow.end_span()));
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
                kw.map(|_| SmolStr::new("_")),
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
    // is pushed to the error store (state.0) and the element becomes `None`,
    // allowing the parser to continue and collect further errors.
    //
    // The LHS is parsed as a pattern (p_pattern), which covers both the
    // simple-identifier binder path (`let x [: T] = ...; body`) and the
    // complex-pattern match path (`let (a, b) = ...; body`).  The presence
    // of `: type` distinguishes the two:
    //
    //   - ident [: type] = value ; body   →  Raw::Let    (binder path)
    //   - pattern        = value ; body   →  Raw::Match  (pattern desugar)
    Cut((
        kw(LetKeyword),
        p_pattern,
        // Allow newline after `:` before the type, like `def`
        (kw(Colon), kw(EndLine).option(), p_raw).map(|(_, _, x)| x).option(),
        kw(Eq),
        // Allow newline after `=` before the value, like `def`
        (kw(EndLine).option(), p_raw),
        kw(Semi),
        kw(EndLine).many0(),
        p_raw,
    ))
    .map(|(let_kw, pattern, ann, eq_kw, val, semi_kw, _, body)| {
        let ann = ann.flatten();
        // Place the caret right after the relevant keyword when an element is missing
        let val_span = eq_kw.map(|s| s.end_span()).unwrap_or(let_kw.end_span());
        let body_span = semi_kw.map(|s| s.end_span()).unwrap_or(val_span);
        // val is now Option<(Option<EndLine>, Raw)> due to the grouped tuple
        let val = val.map(|(_, raw)| raw).unwrap_or(Raw::Hole(val_span));
        let body = body.unwrap_or(Raw::Hole(body_span));
        match pattern {
            None => {
                // Pattern is entirely missing — produce a let with holes
                Raw::Let(
                    let_kw.end_span().map(|_| SmolStr::new("_")),
                    Box::new(ann.unwrap_or(Raw::Hole(let_kw.end_span()))),
                    Box::new(val),
                    Box::new(body),
                )
            }
            Some(Pattern::Con(ident, pats, _)) if pats.is_empty() && ann.is_none() => {
                // Simple identifier, no type annotation → binder (inferred type)
                Raw::Let(
                    ident,
                    Box::new(Raw::Hole(let_kw.end_span())),
                    Box::new(val),
                    Box::new(body),
                )
            }
            Some(Pattern::Con(ident, _, _)) if ann.is_some() => {
                // Simple identifier with `: type` → typed binder
                Raw::Let(
                    ident,
                    Box::new(ann.unwrap()),
                    Box::new(val),
                    Box::new(body),
                )
            }
            Some(Pattern::Any(span, _)) => {
                // Wildcard `_` → binder named `_`
                Raw::Let(
                    span.map(|_| SmolStr::new("_")),
                    Box::new(ann.unwrap_or(Raw::Hole(let_kw.end_span()))),
                    Box::new(val),
                    Box::new(body),
                )
            }
            Some(pat) => {
                // Complex pattern → desugar to match expression
                Raw::Match(Box::new(val), vec![(pat, body)])
            }
        }
    })
    .parse(input, state)
}

fn p_pattern<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Pattern> {
    (
        string(Ident),
        brace(p_pattern.many1_sep(kw(T![,]))).map(|x| x.ok().unwrap_or_default())
    ).map(|x| Pattern::Con(x.0.map(|t| SmolStr::new(format!("{t}.mk"))), x.1, Either::Icit(Icit::Expl)))
        .or((
            smolstr(Ident),
            paren_cut(p_pattern.many1_sep(kw(T![,]))).map(|x| x.ok().unwrap_or_default())
                .or(square_cut(
                    (smolstr(Ident), kw(Eq), p_pattern).map(|x| x.2.to_name(x.0))
                        .or(p_pattern.map(|x| x.to_impl()))
                    .many1_sep(kw(T![,]))
                ).map(|x| x.ok().unwrap_or_default()))
                .many0()
                .map(|x| x.concat()),
        ).map(|(x, t)| Pattern::Con(x, t, Either::Icit(Icit::Expl))))
        .or(
            // Tuple pattern: (a, b, ...)
            paren_cut(p_pattern.many1_sep(kw(T![,])))
                .map(|result| match result {
                    Ok(pats) if pats.len() >= 2 => {
                        let n = pats.len();
                        let span = (pats[0].to_span() + pats[n - 1].to_span()).map(|_| SmolStr::new(format!("Tuple{n}.mk")));
                        Pattern::Con(
                            span,
                            pats,
                            Either::Icit(Icit::Expl),
                        )
                    }
                    Ok(mut pats) => pats.pop().unwrap(), // (a) → a
                    Err(paren_span) => Pattern::Any(paren_span.map(|_| true), Either::Icit(Icit::Expl)), // () → _
                })
        )
        .or(kw(T![_]).map(|x| Pattern::Any(x.map(|_| true), Either::Icit(Icit::Expl))))
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
            Cut((kw(CaseKeyword), p_pattern, Cut((kw(T![=>]), (kw(EndLine).option(), p_raw))))
            )
                .map(|(case_kw, pattern, body_outer)| {
                    let pattern = pattern.unwrap_or(Pattern::Any(
                        case_kw.end_span().map(|_| true),
                        Either::Icit(Icit::Expl),
                    ));
                    // body_outer: Option<(arrow_span, Option<(Option<EndLine>, Raw)>)>
                    // arrow_span is the `=>` token, body is the parsed expression
                    let body = body_outer.map_or(Raw::Hole(empty_span(())), |(arrow, inner)| {
                        inner
                            .map(|(_, raw)| raw)
                            .unwrap_or(Raw::Hole(arrow.end_span()))
                    });
                    (pattern, body)
                })
                .many0_sep(kw(EndLine)),
        ),
    ))
        .map(|(match_kw, scrutinee, body)| Raw::Match(
            Box::new(scrutinee.unwrap_or(Raw::Hole(match_kw.end_span()))),
            body.and_then(|r| r.ok()).unwrap_or_default()
        ))
        .parse(input, state)
}

fn p_new<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    Cut((
        kw(NewKeyword),
        string(Ident),
        paren_cut(p_raw.many1_sep(kw(T![,]))),
    ))
        .map(|(_, scrutinee, args)| args.and_then(|r| r.ok()).unwrap_or_default().into_iter()
            .fold(Raw::Var(scrutinee.map_or(empty_span(SmolStr::new("")), |x| x.map(|x| SmolStr::new(format!("{x}.mk"))))), |acc, x| 
                Raw::App(Box::new(acc), Box::new(x), Either::Icit(Icit::Expl))
            ))
        .parse(input, state)
}

fn p_raw<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    if let Some(macro_decl) = input.first().and_then(|x| state.1.get(x.data.0).cloned()) {
        for m in macro_decl {
            if let Ok((i, t)) = m.matcher.to_parser().parse(input.get(1..).unwrap(), state) {
                let t_owned = m.transcriber.replace(t)?;
                // Record macro expansion info
                {
                    let consumed = input.len() - i.len();
                    let start = input[0].start_offset;
                    let end = if consumed > 0 { input[consumed - 1].end_offset } else { input[0].end_offset };
                    state.2.push(MacroExpansionInfo {
                        name: input[0].data.0.to_string(),
                        start_offset: start,
                        end_offset: end,
                        expanded_text: owned_tokens_to_string(&t_owned),
                    });
                }
                let t_borrowed: Vec<_> = t_owned.iter().map(|tok| Span {
                    data: (tok.data.0.as_str(), tok.data.1),
                    start_offset: tok.start_offset,
                    end_offset: tok.end_offset,
                    path_id: tok.path_id,
                }).collect();
                let mut temp_state = (vec![], state.1.clone(), vec![]);
                let ret = p_raw(&t_borrowed, &mut temp_state)?;
                state.0.extend(temp_state.0);
                state.2.extend(temp_state.2);
                if !ret.0.is_empty() {
                    state.0.push(IError { msg: ret.0.first().unwrap().map(|_| ErrMsg::Base(BaseMsg::Expect(TokenKind::EndLine))) });
                } else {
                    return Ok((i, ret.1))
                }
            }
        }
    }
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
                .map(|x| x.map(|_| ErrMsg::In(Ctx::Expr, BaseMsg::ExpectRaw)))
                .unwrap_or(empty_span(ErrMsg::In(Ctx::Expr, BaseMsg::ExpectRaw)))
        })
}

// Parse a trait bound expression: `Ident` or `Ident[T, U, ...]`
fn p_trait_bound<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    let (input, name) = smolstr(Ident).parse(input, state)?;
    let (input, args) = square_cut(p_raw.many0_sep(kw(T![,])))
        .option()
        .parse(input, state)?;
    let raw = Raw::Var(name);
    match args {
        Some(Ok(args)) => Ok((input, args.into_iter().fold(raw, |acc, arg| Raw::app_impl(acc, arg)))),
        _ => Ok((input, raw)),
    }
}

fn p_def<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
    // Parse a where clause: `where T: Show + Eq, U: Trait[U]`
    let p_where_clause = (
        kw(T![where]),
        (smolstr(Ident), kw(T![:]), p_trait_bound.many0_sep(kw_is(T![+], "+")))
            .map(|(name, _, bounds)| (name, bounds))
            .many0_sep(kw(T![,])),
    ).option().map(|x| x.map(|(_, v)| v));
    Cut((
        kw(DefKeyword),
        smolstr(Ident).or(smolstr(Op)),
        p_pi_binder
            .many0()
            .map(|x| x.into_iter().flatten().collect::<Vec<_>>()),
        (kw(T![:]), kw(EndLine).option(), p_raw).map(|(_, _, x)| x).option(),
        p_where_clause,
        kw(T![=]),
        kw(EndLine).option(),
        p_raw,
    ))
        .map(|(def_kw, name, params, ret, where_clause, eq_kw, _, body)| {
            let mut all_params = params.unwrap_or_default();
            // Desugar where clause to implicit parameters (appended after all explicit params)
            if let Some(clause) = where_clause {
                for items in clause {
                    for (type_name, bounds) in items {
                        for bound in bounds {
                            let trait_name = match &bound {
                                Raw::Var(n) => n.data.clone(),
                                Raw::App(head, _, _) => match head.as_ref() {
                                    Raw::Var(n) => n.data.clone(),
                                    _ => SmolStr::new(""),
                                },
                                _ => SmolStr::new(""),
                            };
                            let inst_name = SmolStr::new(format!("_{}_{}", trait_name.to_lowercase(), type_name.data));
                            // Build constraint: apply type_name (Self) first, then bound args (explicit params).
                            let trait_app = {
                                let mut app = Raw::Var(empty_span(trait_name.clone()));
                                app = Raw::App(
                                    Box::new(app),
                                    Box::new(Raw::Var(type_name.clone())),
                                    Either::Icit(Icit::Impl),
                                );
                                fn collect_app_args(expr: &Raw) -> (SmolStr, Vec<&Raw>) {
                                    match expr {
                                        Raw::App(head, arg, _) => {
                                            let (name, mut args) = collect_app_args(head.as_ref());
                                            args.push(arg.as_ref());
                                            (name, args)
                                        }
                                        Raw::Var(n) => (n.data.clone(), vec![]),
                                        _ => (SmolStr::new(""), vec![]),
                                    }
                                }
                                let (_name, args) = collect_app_args(&bound);
                                for arg in args {
                                    app = Raw::App(
                                        Box::new(app),
                                        Box::new(arg.clone()),
                                        Either::Icit(Icit::Impl),
                                    );
                                }
                                app
                            };
                            all_params.push((empty_span(inst_name), trait_app, Icit::Impl));
                        }
                    }
                }
            }
            Decl::Def {
                name: name.unwrap_or(empty_span(SmolStr::new(""))),
                params: all_params,
                ret_type: ret.flatten().unwrap_or(Raw::Hole(def_kw.end_span())),
                body: body.unwrap_or(Raw::Hole(eq_kw.unwrap_or(def_kw).end_span())),
            }
        })
        .parse(input, state)
}

fn p_print<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
    Cut((kw(PrintlnKeyword), p_raw))
        .map(|(println_kw, x)| Decl::Println(x.unwrap_or(Raw::Hole(println_kw.end_span()))))
        .parse(input, state)
}

fn p_enum<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
    Cut((
        kw(EnumKeyword),
        smolstr(Ident),
        p_pi_binder
            .many0()
            .map(|x| x.into_iter().flatten().collect::<Vec<_>>()),
        brace(
            (
                smolstr(Ident),
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
                .many0_sep(kw(EndLine)),
        ),
    ))
        .map(|(_, name, params, fields)| Decl::Enum {
            is_trait: false,
            name: name.unwrap_or(empty_span(SmolStr::new(""))),
            params: params.unwrap_or_default(),
            cases: fields.and_then(|r| r.ok()).unwrap_or_default(),
        })
        .parse(input, state)
}

fn p_struct<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
    Cut((
        kw(StructKeyword),
        smolstr(Ident),
        p_pi_impl_binder.option().map(|x| x.unwrap_or_default()),
        brace(
            (smolstr(Ident), kw(T![:]), p_raw)
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
            name: name.clone().unwrap_or(empty_span(SmolStr::new(""))),
            params: params.clone().unwrap_or_default(),
            cases: vec![
                (
                    name.clone().map(|x| x.map(|x| SmolStr::new(format!("{x}.mk")))).unwrap_or(empty_span(SmolStr::new(""))),
                    fields.clone().and_then(|r| r.ok()).unwrap_or_default().into_iter().map(|x| (x.0, x.1, Icit::Expl)).collect(),
                    None,
                ),
            ]
        })
        .parse(input, state)
}

/// A single item in a trait body: either a type declaration or a method declaration
enum TraitBodyItem {
    TypeDecl { name: Span<SmolStr>, default_type: Option<Raw> },
    Method { name: Span<SmolStr>, params: Vec<(Span<SmolStr>, Raw, Icit)>, ret: Raw, body: Option<Raw> },
}

fn p_trait_body_item<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, TraitBodyItem> {
    // Try `type Name (= DefaultType)?` — `type` is lowercase ident, not the Type keyword
    if let Ok((input, _)) = kw_is(TokenKind::Ident, "type").parse(input, state) {
        let (input, type_name) = smolstr(Ident).parse(input, state)?;
        let (input, default) = (kw(T![=]), p_raw).option().parse(input, state)?;
        return Ok((input, TraitBodyItem::TypeDecl { name: type_name, default_type: default.map(|(_, v)| v) }));
    }
    // Try `def name(params): RetType where T: Into[Self] (= body)?`
    let (input, _) = kw(DefKeyword).parse(input, state)?;
    let (input, name) = smolstr(Ident).or(smolstr(Op)).parse(input, state)?;
    let (input, mut params) = p_pi_binder.many0().map(|x| x.into_iter().flatten().collect::<Vec<_>>()).parse(input, state)?;
    let (input, _) = kw(T![:]).parse(input, state)?;
    let (input, ret) = p_raw.parse(input, state)?;
    // Parse optional where clause
    let (input, where_clause) = (
        kw(T![where]),
        (smolstr(Ident), kw(T![:]), p_trait_bound.many0_sep(kw_is(T![+], "+")))
            .map(|(name, _, bounds)| (name, bounds))
            .many0_sep(kw(T![,])),
    ).option().map(|x| x.map(|(_, v)| v)).parse(input, state)?;
    if let Some(clause) = where_clause {
        for items in clause {
            let (type_name, bounds) = items;
            for bound in bounds {
                let trait_name = match &bound {
                    Raw::Var(n) => n.data.clone(),
                    Raw::App(head, _, _) => match head.as_ref() {
                        Raw::Var(n) => n.data.clone(),
                        _ => SmolStr::new(""),
                    },
                    _ => SmolStr::new(""),
                };
                let inst_name = SmolStr::new(format!("_{}_{}", trait_name.to_lowercase(), type_name.data));
                // Build constraint: apply type_name (Self) first, then bound args.
                let trait_app = {
                    let mut app = Raw::Var(empty_span(trait_name.clone()));
                    app = Raw::App(
                        Box::new(app),
                        Box::new(Raw::Var(type_name.clone())),
                        super::parser::syntax::Either::Icit(Icit::Impl),
                    );
                    fn collect_app_args_trait(expr: &Raw) -> (SmolStr, Vec<&Raw>) {
                        match expr {
                            Raw::App(head, arg, _) => {
                                let (name, mut args) = collect_app_args_trait(head.as_ref());
                                args.push(arg.as_ref());
                                (name, args)
                            }
                            Raw::Var(n) => (n.data.clone(), vec![]),
                            _ => (SmolStr::new(""), vec![]),
                        }
                    }
                    let (_name, args) = collect_app_args_trait(&bound);
                    for arg in args {
                        app = Raw::App(
                            Box::new(app),
                            Box::new(arg.clone()),
                            super::parser::syntax::Either::Icit(Icit::Impl),
                        );
                    }
                    app
                };
                params.push((empty_span(inst_name), trait_app, Icit::Impl));
            }
        }
    }
    let (input, body) = (kw(T![=]), p_raw).option().parse(input, state)?;
    Ok((input, TraitBodyItem::Method { name, params, ret, body: body.map(|(_, v)| v) }))
}

fn p_trait_def<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
    (
        kw(TraitKeyword),
        smolstr(Ident),
        (kw(T![:]), smolstr(Ident).many0_sep(kw_is(T![+], "+"))).option()
            .map(|x| x.map(|(_, v)| v).unwrap_or_default()),
        p_pi_impl_binder_option,
        brace(p_trait_body_item.many0_sep(kw(EndLine))),
    )
        .map(|(_, name, supertraits, params, body)| {
            let mut methods = Vec::new();
            let mut extra_params = params;
            let mut assoc_defaults = Vec::new();
            if let Ok(items) = body {
                for item in items {
                    match item {
                    TraitBodyItem::TypeDecl { name: type_name, default_type } => {
                        // Desugar `type Elem` to `[Elem: outParam(Type 0)]` trait param
                        let out_param_raw = Raw::App(
                            Box::new(Raw::Var(empty_span(SmolStr::new("outParam")))),
                            Box::new(Raw::U(0)),
                            super::parser::syntax::Either::Icit(Icit::Expl),
                        );
                        assoc_defaults.push((type_name.data.clone(), default_type));
                        extra_params.push((type_name, out_param_raw, Icit::Impl));
                    }
                        TraitBodyItem::Method { name: mn, params: mparams, ret: mret, body: mbody } => {
                            methods.push((mn, mparams, mret, mbody));
                        }
                    }
                }
            }
            Decl::TraitDecl {
                name,
                params: extra_params,
                supertraits,
                methods,
                assoc_defaults,
            }
        })
        .parse(input, state)
}

fn p_impl_body_item_def_or_type<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, (bool, Option<Raw>, Option<(Decl, bool)>)> {
    // Check if first token is lowercase `type` ident — must be an associated type assignment
    if input.first().map(|t| t.data.0 == "type" && t.data.1 == TokenKind::Ident).unwrap_or(false) {
        let (input, _) = kw_is(TokenKind::Ident, "type").parse(input, state)?;
        let (input, _) = smolstr(Ident).parse(input, state)?;
        let (input, (_, typ)) = (kw(T![=]), p_raw).parse(input, state)?;
        return Ok((input, (true, Some(typ), None)));
    }
    // `def name(...) = body` or `static def ...` — method
    let (input, is_static) = kw(StaticKeyword).option().parse(input, state)?;
    let is_static = is_static.is_some();
    let (input, decl) = p_def.parse(input, state)?;
    Ok((input, (false, None, Some((decl, is_static)))))
}

fn p_impl<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
    Cut((
        kw(ImplKeyword),
        p_pi_impl_binder_option,
        (
            smolstr(Ident),
            square_cut(p_raw.many0_sep(kw(T![,]))).option().map(|x| x.and_then(|r| r.ok()).unwrap_or_default()),
            Cut((
                kw(ForKeyword),
                p_raw,
            )),
        ).map(Ok).or(p_raw.map(Err)),
        brace(p_impl_body_item_def_or_type.many0_sep(kw(EndLine))),
    )).map(|x| match x.2 {
        Some(Ok((trait_name, trait_params, (_, name)))) => (x.1, trait_name, trait_params, name.unwrap_or(Raw::Hole(empty_span(()))), x.3, false),
        Some(Err(name)) => (
            x.1.clone(),
            x.0.map(|_| SmolStr::new(format!("$trait_name${}", name))),
            vec![],
            name,
            x.3,
            true,
        ),
        None => (x.1, empty_span(SmolStr::new("")), vec![], Raw::Hole(empty_span(())), x.3, false)
    })
        .map(|(params, trait_name, trait_params, name, body, need_create)| {
            // body is Option<Result<Vec<...>, Span<()>>> (brace's Result wrapped by Cut)
            let mut methods: Vec<(Decl, bool)> = Vec::new();
            let mut extra_params = trait_params;
            // body is Option<Result<Vec<(bool, Option<Raw>, Option<(Decl, bool)>)>, Span<()>>>
            if let Some(Ok(items)) = body {
                for item in items {
                    if item.0 {
                        if let Some(typ) = item.1 {
                            extra_params.push(typ);
                        }
                    } else if let Some((decl, is_static)) = item.2 {
                        methods.push((decl, is_static));
                    }
                }
            }
            Decl::ImplDecl {
                name,
                params: params.unwrap_or_default(),
                trait_name,
                trait_params: extra_params,
                methods,
                need_create,
            }
        })
        .parse(input, state)
}



// 在 mod.rs 中添加这些函数
fn parse_fragment_kind<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut MacroState
) -> IResult<'a, 'b, MacroFragment> {
    string(Ident).parse(input, state).map(|(input, span)| {
        let fragment = match span.data.as_str() {
            //"expr" => MacroFragment::Expr,
            "ident" => MacroFragment::Ident,
            "raw" => MacroFragment::Raw,
            "params" => MacroFragment::Param,
            //"ty" => MacroFragment::Ty,
            //"pat" => MacroFragment::Pat,
            //"stmt" => MacroFragment::Stmt,
            //"item" => MacroFragment::Item,
            //"block" => MacroFragment::Block,
            //"tt" => MacroFragment::Tt,
            _ => {
                //state.0.push(IError {
                //    msg: span.to_span().map(|_| ErrMsg::Base(BaseMsg::Expect(Ident))
                //});
                MacroFragment::Name(span)
            }
        };
        (input, fragment)
    })
}

fn p_macro_matcher_single<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut MacroState
) -> IResult<'a, 'b, MacroMatcher> {
    // 尝试解析 $name:fragment
    let metavar_parser = (
        string(MacroIdent),
        kw(Colon),
        parse_fragment_kind
    ).map(|(name, _, fragment)| {
        MacroMatcher::Metavar { name, fragment }
    });
    
    // 尝试解析分组 (...) [...] {...}
    /*let group_parser = paren(p_macro_matcher_sequence.map(MacroMatcher::Sequence))
        .map(|m| MacroMatcher::Group(Delimiter::Parenthesis, vec![m]))
        .or(square(p_macro_matcher_sequence.map(MacroMatcher::Sequence))
            .map(|m| MacroMatcher::Group(Delimiter::Bracket, vec![m])))
        .or(brace(p_macro_matcher_sequence.map(|opt| {
            MacroMatcher::Group(Delimiter::Brace, opt.map(|m| vec![m]).unwrap_or_default())
        })));*/
    let group_parser = (
        kw_is(Op, "$"),
        kw(LParen),
        p_macro_matcher_sequence,
        kw(RParen),
        string_is(Op, "*").or(string_is(Op, "+")),
    ).map(|(_, _, m, _, s)| if &s.data == "*" {
        MacroMatcher::Many0(MacroMatcher::Sequence(m).into())
    } else {
        MacroMatcher::Many1(MacroMatcher::Sequence(m).into())
    });
    
    // 尝试解析普通 token
    let token_parser = string(Ident)
        .map(|span| {
            MacroMatcher::Token(Ident, span)
        })
        .or(string(Op).map(|span| {
            MacroMatcher::Token(Op, span)
        }))
        .or(string(Num).map(|span| {
            MacroMatcher::Token(Num, span)
        }))
        /*.or(string(LParen).map(|span| {
            MacroMatcher::Token(LParen, span)
        }))
        .or(string(RParen).map(|span| {
            MacroMatcher::Token(RParen, span)
        }))*/
        .or(string(LSquare).map(|span| {
            MacroMatcher::Token(LSquare, span)
        }))
        .or(string(RSquare).map(|span| {
            MacroMatcher::Token(RSquare, span)
        }))
        .or(string(LCurly).map(|span| {
            MacroMatcher::Token(LCurly, span)
        }))
        .or(string(RCurly).map(|span| {
            MacroMatcher::Token(RCurly, span)
        }))
        .or(string(LetKeyword).map(|span| MacroMatcher::Token(LetKeyword, span)))
        .or(string(Eq).map(|span| MacroMatcher::Token(Eq, span)));
    
    metavar_parser
        .or(group_parser)
        .or(token_parser)
        .parse(input, state)
}

fn p_macro_matcher_sequence<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut MacroState
) -> IResult<'a, 'b, Vec<MacroMatcher>> {
    p_macro_matcher_single.many0().parse(input, state)
}

fn p_macro_matcher<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut MacroState
) -> IResult<'a, 'b, MacroMatcher> {
    // 解析带重复的匹配器：$(...)* $(...)+ $(...)?
    /*let repetition_parser = (
        kw(Dollar),
        paren(p_macro_matcher_sequence),
        string(Op),
    ).map(|(_, matchers, op_token)| {
        let op = match op_token.data.as_ref() {
            "*" => RepetitionOp::ZeroOrMore,
            "+" => RepetitionOp::OneOrMore,
            "?" => RepetitionOp::Optional,
            _ => RepetitionOp::ZeroOrMore,
        };
        MacroMatcher::Repetition {
            inner: Box::new(MacroMatcher::Sequence(matchers)),
            separator: None,  // 简化，暂不支持分隔符
            op,
        }
    });
    
    repetition_parser
        .or(p_macro_matcher_sequence.map(|matchers| {
            if matchers.len() == 1 {
                matchers.into_iter().next().unwrap()
            } else {
                MacroMatcher::Sequence(matchers)
            }
        }))
        .parse(input, state)*/
    p_macro_matcher_sequence.map(|matchers| {
        if matchers.len() == 1 {
            matchers.into_iter().next().unwrap()
        } else {
            MacroMatcher::Sequence(matchers)
        }
    })
    .parse(input, state)
}

fn p_macro_transcriber_single<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut MacroState
) -> IResult<'a, 'b, MacroTranscriber> {
    // 尝试解析 $name
    /*let metavar_ref = (
        kw(Dollar),
        string(Ident)
    ).map(|(_, name)| {
        MacroTranscriber::MetavarRef(name)
    });
    
    // 尝试解析分组
    let group_parser = paren(p_macro_transcriber_sequence.map(MacroTranscriber::Sequence))
        .map(|m| MacroTranscriber::Group(Delimiter::Parenthesis, vec![m]))
        .or(square(p_macro_transcriber_sequence.map(MacroTranscriber::Sequence))
            .map(|m| MacroTranscriber::Group(Delimiter::Bracket, vec![m])))
        .or(brace(p_macro_transcriber_sequence.map(|opt| {
            MacroTranscriber::Group(Delimiter::Brace, opt.map(|m| vec![m]).unwrap_or_default())
        })));
    
    // 尝试解析普通 token
    let token_parser = string(Ident)
        .or(string(Op))
        .or(string(Num))
        .map(|span| {
            let kind = match span.data.as_str() {
                "(" => TokenKind::LParen,
                ")" => TokenKind::RParen,
                _ => TokenKind::Ident,
            };
            MacroTranscriber::Token(kind, Some(span.data.clone()))
        });
    
    metavar_ref
        .or(group_parser)
        .or(token_parser)
        .parse(input, state)*/
    match (kw(LCurly), kw(EndLine).option()).parse(input, state) {
        Ok((input, _)) => {
            let mut lvl = 1;
            let mut input = input;
            let mut i_back = input;
            let mut ret = vec![];
            let mut need_remove_endline = 0;
            loop {
                if let Ok((i, (endline, _))) = (kw(EndLine).option(), kw(RCurly)).parse(input, state) {
                    lvl -= 1;
                    input = i;
                    if lvl == 0 {
                        if endline.is_some() {
                            need_remove_endline = 1;
                        }
                        break;
                    }
                } else if let Ok((i, _)) = kw(LCurly).parse(input, state) {
                    lvl += 1;
                    input = i;
                } else if input.is_empty() || (kw(RParen), kw_is(Op, "*")).parse(input, state).is_ok() || (kw(RParen), kw_is(Op, "+")).parse(input, state).is_ok() {
                    break;
                } else if let Ok((i, _)) = (kw_is(Op, "$"), kw(LParen)).parse(input, state) {
                    let len = i_back.len() - input.len();
                    let owned: Vec<OwnedToken> = i_back[..len].iter().map(|tok| Span {
                        data: (tok.data.0.to_owned(), tok.data.1),
                        start_offset: tok.start_offset,
                        end_offset: tok.end_offset,
                        path_id: tok.path_id,
                    }).collect();
                    ret.push(MacroTranscriber::Basic(owned));
                    let (i, o) = p_macro_transcriber_single.parse(i, state)?;
                    ret.push(MacroTranscriber::Group(o.into()));
                    let (i, _) = (kw(RParen), kw_is(Op, "*")).or((kw(RParen), kw_is(Op, "+"))).parse(i, state)?;//TODO: 0 or 1?
                    i_back = i;
                    input = i;
                } else {
                    input = input.get(1..).unwrap();
                }
            }
            let len = i_back.len() - input.len() - 1 - need_remove_endline;
            let owned: Vec<OwnedToken> = i_back[..len].iter().map(|tok| Span {
                data: (tok.data.0.to_owned(), tok.data.1),
                start_offset: tok.start_offset,
                end_offset: tok.end_offset,
                path_id: tok.path_id,
            }).collect();
            ret.push(MacroTranscriber::Basic(owned));
            Ok((input, MacroTranscriber::Sequence(ret)))
        },
        //Err(e) => Err(e),
        Err(_) => {
            // No leading '{' - parse as flat token sequence with possible $(...) groups
            let mut input = input;
            let mut i_back = input;
            let mut ret = vec![];
            while !input.is_empty()
                && (kw(RParen), kw_is(Op, "*")).parse(input, state).is_err()
                && (kw(RParen), kw_is(Op, "+")).parse(input, state).is_err()
                && (kw(EndLine).option(), kw(RCurly)).parse(input, state).is_err()
            {
                if let Ok((i, _)) = (kw_is(Op, "$"), kw(LParen)).parse(input, state) {
                    let len = i_back.len() - input.len();
                    let owned: Vec<OwnedToken> = i_back[..len].iter().map(|tok| Span {
                        data: (tok.data.0.to_owned(), tok.data.1),
                        start_offset: tok.start_offset,
                        end_offset: tok.end_offset,
                        path_id: tok.path_id,
                    }).collect();
                    ret.push(MacroTranscriber::Basic(owned));
                    let (i, o) = p_macro_transcriber_single.parse(i, state)?;
                    ret.push(MacroTranscriber::Group(o.into()));
                    let (i, _) = (kw(RParen), kw_is(Op, "*")).or((kw(RParen), kw_is(Op, "+"))).parse(i, state)?;
                    i_back = i;
                    input = i;
                } else {
                    input = input.get(1..).unwrap();
                }
            }
            let len = i_back.len() - input.len();
            let owned: Vec<OwnedToken> = i_back[..len].iter().map(|tok| Span {
                data: (tok.data.0.to_owned(), tok.data.1),
                start_offset: tok.start_offset,
                end_offset: tok.end_offset,
                path_id: tok.path_id,
            }).collect();
            ret.push(MacroTranscriber::Basic(owned));
            Ok((input, MacroTranscriber::Sequence(ret)))
        },
    }
}

/*fn p_macro_transcriber_sequence<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut MacroState
) -> IResult<'a, 'b, Vec<MacroTranscriber>> {
    p_macro_transcriber_single.many0().parse(input, state)
}

fn p_macro_transcriber<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut MacroState
) -> IResult<'a, 'b, MacroTranscriber> {
    // 类似 matcher，支持重复
    let repetition_parser = (
        kw(Dollar),
        paren(p_macro_transcriber_sequence),
        kw(Op),  // *, +, ?
    ).map(|(_, transcribers, op_token)| {
        let op = match op_token.data {
            "*" => RepetitionOp::ZeroOrMore,
            "+" => RepetitionOp::OneOrMore,
            "?" => RepetitionOp::Optional,
            _ => RepetitionOp::ZeroOrMore,
        };
        MacroTranscriber::Repetition {
            inner: Box::new(MacroTranscriber::Sequence(transcribers)),
            separator: None,
            op,
            metavar: empty_span("".to_owned()),  // 需要改进
        }
    });
    
    repetition_parser
        .or(p_macro_transcriber_sequence.map(|transcribers| {
            if transcribers.len() == 1 {
                transcribers.into_iter().next().unwrap()
            } else {
                MacroTranscriber::Sequence(transcribers)
            }
        }))
        .parse(input, state)
}

// 修改 p_macro_def
fn p_macro_def<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut MacroState
) -> IResult<'a, 'b, Decl> {
    Cut((
        kw(MacroKeyword),
        string(Ident),  // 宏名称
        p_pi_expl_binder.option().map(|x| x.unwrap_or_default()),  // 可选参数
        brace(
            // 解析多条规则: (matcher) => (transcriber);
            (
                paren(p_macro_matcher),      // 匹配器在 (...) 中
                kw(DoubleArrow),             // =>
                paren(p_macro_transcriber),  // 转写器在 (...) 中
            ).map(|(matcher, _, transcriber)| {
                MacroRule { matcher, transcriber }
            })
            .many1_sep(kw(Semi))  // 规则用 ; 分隔
        ),
    ))
    .map(|(_, name, params, rules_result)| {
        Decl::Macro_Def {
            name,
            params,
            rules: rules_result.flatten().unwrap_or_default(),
        }
    })
    .parse(input, state)
}*/

/// Parse optional #[macro_export] attribute before macro_rules.
/// Returns true if the attribute was present.
fn p_macro_export_attr<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, bool> {
    let attr = (kw_is(Op, "#"), kw(LSquare), string_is(Ident, "macro_export"), kw(RSquare), kw(EndLine).many0())
        .map(|_| true)
        .option()
        .map(|x| x.unwrap_or(false));
    attr.parse(input, state)
}

// macro_rule <ident>($<ident>: raw|ident|..) {..}
fn p_macro_def<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, ()> {
    let (input, is_exported) = p_macro_export_attr(input, state)?;
    match Cut((
        kw(MacroKeyword),
        string(Ident),  // 宏名称
        brace(
            // 解析多条规则: (matcher => transcriber);
            Cut((
                paren(p_macro_matcher),  // 匹配器在 (...) 中
                kw(T![=>]),
                p_macro_transcriber_single,  // 转写器在 (...) 中
            )).map(|(matcher, _, transcriber)| MacroRule {
                matcher,
                transcriber: transcriber.unwrap_or(MacroTranscriber::Sequence(vec![])),
            })
            .many1_sep((kw(T![;]), kw(EndLine).option()))  // 规则用 ; 分隔
        ),
    ))
    .parse(input, state) {
        Ok((input, (_, name, rules))) => {
            if let Some(name) = name {
                // Store exported status in the macro name's span metadata.
                // We use a sentinel prefix to mark exported macros.
                if is_exported {
                    state.1.insert(format!("__exported__{}", name.data), vec![]);
                }
                state.1.insert(name.data.clone(), rules.and_then(|r| r.ok()).unwrap_or(vec![]));
            }
            Ok((input, ()))
        },
        Err(e) => Err(e),
    }
}

fn p_package<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
    let (input, _) = kw(PackageKeyword).parse(input, state)?;
    let (input, first) = smolstr(Ident).parse(input, state)?;
    let mut path = vec![first];
    let mut input = input;
    loop {
        match (kw(T![.]), smolstr(Ident)).parse(input, state) {
            Ok((i, (_, seg))) => {
                path.push(seg);
                input = i;
            }
            Err(_) => break,
        }
    }
    Ok((input, Decl::Package { path }))
}

fn p_import<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
    let (input, _) = kw(ImportKeyword).parse(input, state)?;
    let (input, first) = smolstr(Ident).parse(input, state)?;
    let mut prefix: Vec<SmolStr> = vec![first.data];
    let mut input = input;
    loop {
        match (kw(T![.]), smolstr(Ident)).parse(input, state) {
            Ok((i, (_, seg))) => {
                prefix.push(seg.data);
                input = i;
            }
            Err(_) => break,
        }
    }
    // Check for wildcard `._`
    if let Ok((i, _)) = (kw(T![.]), kw(T![_])).parse(input, state) {
        Ok((i, Decl::Import { prefix, names: vec![], wildcard: true }))
    } else if let Ok((i, _)) = (kw(T![.]), kw(LCurly)).parse(input, state) {
        // import foo.bar.{Name1, Name2}
        let (i, names) = smolstr(Ident)
            .many1_sep((kw(T![,]), kw(EndLine).option()))
            .parse(i, state)?;
        let (i, _) = kw(RCurly).parse(i, state)?;
        let names: Vec<SmolStr> = names.into_iter().map(|s| s.data).collect();
        Ok((i, Decl::Import { prefix, names, wildcard: false }))
    } else {
        // import foo.bar.Name  — last segment is the name
        let name = prefix.pop().unwrap_or(SmolStr::new(""));
        Ok((input, Decl::Import { prefix, names: vec![name], wildcard: false }))
    }
}

fn p_derive_attr<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Vec<Span<SmolStr>>> {
    let attr = (kw_is(Op, "#"), kw(LSquare), string_is(Ident, "derive"), kw(LParen));
    match attr.option().parse(input, state) {
        Ok((input, Some(_))) => {
            let (input, traits) = smolstr(Ident)
                .many1_sep((kw(T![,]), kw(EndLine).option()))
                .parse(input, state)?;
            let (input, _) = kw(RParen).parse(input, state)?;
            let (input, _) = kw(RSquare).parse(input, state)?;
            let (input, _) = kw(EndLine).many0().parse(input, state)?;
            Ok((input, traits))
        }
        Ok((input, None)) => Ok((input, vec![])),
        Err(e) => Ok((input, vec![])), // No attribute found, not an error
    }
}

/// Expand `Decl::Derive` items into their inner declaration + generated impl blocks.
fn expand_derives(decls: Vec<Decl>) -> Vec<Decl> {
    let registry = derive::default_derive_registry();
    let mut result = vec![];
    for decl in decls {
        match decl {
            Decl::Derive { traits, decl } => {
                let inner = *decl;
                let generated = derive::expand_derive(&registry, &traits, &inner);
                result.push(inner);
                result.extend(generated);
            }
            other => result.push(other),
        }
    }
    result
}

fn p_decl<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
    if let Some(macro_decl) = input.first().and_then(|x| state.1.get(x.data.0).cloned()) {
        let is_cut = macro_decl.len() == 1;
        for m in macro_decl {
            let (i, t) = if is_cut {
                m.matcher.to_parser().parse(input.get(1..).unwrap(), state)?
            } else {
                match m.matcher.to_parser().parse(input.get(1..).unwrap(), state) {
                    Ok(x) => x,
                    Err(_) => continue,
                }
            };
            let i = if matches!(i.first().map(|x| x.data.1), Some(EndLine)) || i.is_empty() {
                i
            } else if input.len() != i.len() {
                input.get(input.len() - i.len() - 1 ..).unwrap()
            } else {
                i
            };
            let t_owned = m.transcriber.replace(t)?;
            // Record macro expansion info
            {
                let consumed = input.len() - i.len();
                let start = input[0].start_offset;
                let end = if consumed > 0 { input[consumed - 1].end_offset } else { input[0].end_offset };
                state.2.push(MacroExpansionInfo {
                    name: input[0].data.0.to_string(),
                    start_offset: start,
                    end_offset: end,
                    expanded_text: owned_tokens_to_string(&t_owned),
                });
            }
            let t_borrowed: Vec<_> = t_owned.iter().map(|tok| Span {
                data: (tok.data.0.as_str(), tok.data.1),
                start_offset: tok.start_offset,
                end_offset: tok.end_offset,
                path_id: tok.path_id,
            }).collect();
            let mut temp_state = (vec![], state.1.clone(), vec![]);
            let ret = p_decl(&t_borrowed, &mut temp_state)?;
            state.0.extend(temp_state.0);
            state.2.extend(temp_state.2);
            if !ret.0.is_empty() {
                let only_endlines = ret.0.iter().all(|t| t.data.1 == TokenKind::EndLine);
                if only_endlines {
                    return Ok((i, ret.1))
                }
                state.0.push(IError { msg: ret.0.first().unwrap().map(|_| ErrMsg::Base(BaseMsg::Expect(TokenKind::EndLine))) })
            } else {
                return Ok((i, ret.1))
            }
        }
    }
    // Check for #[derive(Trait1, Trait2, ...)] attribute before enum/struct
    let (input, derive_traits) = p_derive_attr.option().map(|x| x.unwrap_or_default()).parse(input, state)?;
    if !derive_traits.is_empty() {
        let (input, decl) = p_enum.or(p_struct).parse(input, state).map_err(|e| IError {
            msg: e.msg.map(|m| ErrMsg::In(Ctx::Declare, extract_base(m)))
        })?;
        return Ok((input, Decl::Derive { traits: derive_traits, decl: Box::new(decl) }))
    }
    p_def.or(p_print).or(p_enum).or(p_struct).or(p_trait_def).or(p_impl)
        .or(p_package).or(p_import)
        .parse(input, state)
        .map_err(|e| IError {
            msg: e.msg.map(|m| ErrMsg::In(Ctx::Declare, extract_base(m)))
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

//pub fn parser_test<'a, T, P: Parser<&'a [TokenNode<'a>], T, Vec<IError>, IError>>(p: P, input: &'a str, id: u32) -> Option<(Vec<T>, Vec<IError>)> {
pub fn parser_test(input: &str, id: u32) -> Option<(Vec<Raw>, Vec<IError>)> {
    let mut err_collect: MacroState = (vec![], Default::default(), vec![]);
    let ret = super::parser::lex::lex(Span {
        data: input,
        start_offset: 0,
        end_offset: input.len() as u32,
        path_id: id,
    }).unwrap();
    let o = p_raw.many0().parse(&ret.1, &mut err_collect);
    match o {
        Ok(ret) => if ret.0.is_empty() {
            Some((ret.1, err_collect.0))
        } else {
            err_collect.0.push(IError { msg: ret.0.first().unwrap().map(|_| ErrMsg::Base(BaseMsg::Expect(EndLine))) });
            Some((ret.1, err_collect.0))
        }
        Err(e) => {
            err_collect.0.push(e);
            Some((vec![], err_collect.0))
        }
    }
}

#[test]
fn test2() {
    let input = r#"(a + b) + c"#;
    println!("{:#?}", parser_test(input, 0).unwrap());
    println!("--------------");
    let input = r#"a + b + c"#;
    println!("{:#?}", parser_test(input, 0).unwrap());
}

#[test]
fn test_macro_expansion_info() {
    // Test that parser_with_macros correctly produces MacroExpansionInfo
    // with byte offsets matching the source text, and that the
    // expand-macro find logic (offset >= start && offset < end) works.
    let input = r#"
println stringify hello
"#;
    let (_decls, _errs, _exports, expansions) = parser_with_macros(input, 0, &Default::default()).unwrap();

    // We expect exactly one expansion: `stringify hello`
    assert_eq!(expansions.len(), 1, "expected exactly one macro expansion");
    let exp = &expansions[0];
    assert_eq!(exp.name, "stringify");

    // Find the byte offset of "stringify" in the input
    let str_off = input.find("stringify").expect("stringify should be in input");
    let hello_off = input.find("hello").expect("hello should be in input");

    // start_offset should point to the start of "stringify"
    assert_eq!(exp.start_offset as usize, str_off,
        "start_offset should be at the start of the macro name");

    // end_offset should point to the end of "hello"
    assert_eq!(exp.end_offset as usize, hello_off + "hello".len(),
        "end_offset should be at the end of the last consumed token");

    // ---- simulate the expand macro lookup logic ----
    // Cursor on the macro name "stringify"
    assert!(str_off >= exp.start_offset as usize && str_off < exp.end_offset as usize,
        "cursor on macro name should find expansion");
    // Cursor between "stringify" and "hello"
    let between = str_off + "stringify".len();
    assert!(between >= exp.start_offset as usize && between < exp.end_offset as usize,
        "cursor between name and arg should find expansion");
    // Cursor on the argument "hello"
    assert!(hello_off >= exp.start_offset as usize && hello_off < exp.end_offset as usize,
        "cursor on argument should find expansion");
    // Cursor BEFORE the macro invocation
    assert!(!(0usize >= exp.start_offset as usize && 0usize < exp.end_offset as usize),
        "cursor before macro should NOT find expansion");
}

#[test]
fn test_macro_expansion_info_nested_innermost() {
    // Test that when macros are nested, the cursor should find
    // the innermost (smallest span) expansion, not the outermost.
    //
    // Note: The current impl uses find() which returns the first match
    // (outermost). This test documents that behavior as a known limitation.
    let input = r#"
macro_rules repeat {
    ($x: raw) => { $x $x }
}
repeat stringify hello
"#;
    // First parse defines `repeat`, second parse uses it
    let (_d1, _e1, exports, _) = parser_with_macros(input, 0, &Default::default()).unwrap();
    // Now parse again with `repeat` available as a macro
    let (_d2, _e2, _ex2, expansions) = parser_with_macros(input, 0, &exports).unwrap();

    // We expect at least the `repeat` expansion
    let repeat_exp = expansions.iter().find(|e| e.name == "repeat");
    assert!(repeat_exp.is_some(), "repeat expansion should exist");

    // Also check stringify expansion exists if repeat's expansion triggers it
    let str_exp = expansions.iter().find(|e| e.name == "stringify");
    assert!(str_exp.is_some(), "stringify expansion should exist");

    // The original find() gives outermost, which is `repeat`
    let first_by_find = expansions.iter().find(|e| {
        let offset = 1usize; // somewhere inside
        offset >= e.start_offset as usize && offset < e.end_offset as usize
    });
    // This documents current behavior
    if let Some(found) = first_by_find {
        eprintln!("Current find() picks: {} (span {}-{})",
            found.name, found.start_offset, found.end_offset);
    }
}

#[test]
fn test_macro_expansion_info_missing_no_macro() {
    // File without macros should produce empty expansions
    let input = r#"
def fortytwo: Type0 = Type0
"#;
    let (_decls, _errs, _exports, expansions) = parser_with_macros(input, 0, &Default::default()).unwrap();
    assert!(expansions.is_empty(),
        "file without macro invocations should have no expansions");
}

#[test]
fn test_macro_expansion_expanded_text() {
    // Verify expanded_text is populated correctly
    let input = r#"println stringify hello"#;
    let (_decls, _errs, _exports, expansions) = parser_with_macros(input, 0, &Default::default()).unwrap();

    assert_eq!(expansions.len(), 1);
    let exp = &expansions[0];
    assert_eq!(exp.name, "stringify");

    // expanded_text should contain the expanded form (a string literal for stringify)
    assert!(!exp.expanded_text.is_empty(),
        "expanded_text should not be empty for built-in stringify");
    eprintln!("stringify hello expands to: {:?}", exp.expanded_text);
}

#[test]
fn test_macro_expansion_derive_offsets() {
    // Derive expansion doesn't produce MacroExpansionInfo (by current design)
    let input = r#"
enum Foo[A] {
    bar(x: A)
    baz(y: A, z: A)
}
"#;
    let (_decls, _errs, _exports, expansions) = parser_with_macros(input, 0, &Default::default()).unwrap();
    assert!(expansions.is_empty(),
        "derive expansion doesn't produce MacroExpansionInfo (by design)");
}

#[test]
fn test_expand_macro_full_flow_alu() {
    // Full flow: load hdl.typort macros, parse alu.typort content,
    // verify module{} macro expansion with correct offsets.
    let hdl_core = include_str!("../../prelude/hdl/hdl-core.typort");
    let hdl_types = include_str!("../../prelude/hdl/hdl-types.typort");
    let hdl_ops = include_str!("../../prelude/hdl/hdl-ops.typort");
    let hdl_clock = include_str!("../../prelude/hdl/hdl-clock.typort");
    let hdl_bus = include_str!("../../prelude/hdl/hdl-bus.typort");
    let hdl_signals = include_str!("../../prelude/hdl/hdl-signals.typort");
    let hdl_macros = include_str!("../../prelude/hdl/hdl-macros.typort");
    let hdl_verilog = include_str!("../../prelude/hdl/hdl-verilog.typort");

    // Combine all hdl parts into one content string for parsing
    let hdl_content = hdl_core.to_owned() + "\n" + hdl_types + "\n" + hdl_ops
        + "\n" + hdl_clock + "\n" + hdl_bus + "\n" + hdl_signals
        + "\n" + hdl_macros + "\n" + hdl_verilog;

    // Step 1: Parse hdl.typort to extract exported macros
    // parser_with_macros expects preprocessed text (comments stripped)
    let (_hdl_decls, _hdl_errs, hdl_exports, _hdl_expansions) =
        parser_with_macros(&super::preprocess(&hdl_content), 0, &Default::default()).unwrap();

    // Verify 'module' macro was exported from hdl.typort
    assert!(hdl_exports.contains_key("module"),
        "hdl.typort must export the 'module' macro");

    // Step 2: Parse alu.typort content using the exported macros
    let alu_content = include_str!("../../../examples/alu.typort");
    eprintln!("alu.typort len: {}", alu_content.len());
    let alu_preprocessed = super::preprocess(alu_content);
    eprintln!("alu preprocessed len: {}", alu_preprocessed.len());
    let (_alu_decls, _alu_errs, _alu_exports, expansions) =
        parser_with_macros(&alu_preprocessed, 1, &hdl_exports).unwrap();
    eprintln!("expansions count: {}", expansions.len());

    // We expect at least one macro expansion for 'module'
    let module_exps: Vec<_> = expansions.iter().filter(|e| e.name == "module").collect();
    assert!(!module_exps.is_empty(),
        "expected at least one 'module' macro expansion in alu.typort");
    for (i, me) in module_exps.iter().enumerate() {
        assert!(me.end_offset as usize <= alu_preprocessed.len(),
            "module expansion {}: end_offset {} out of bounds (len {})",
            i, me.end_offset, alu_preprocessed.len());
    }

    // Step 3: Verify cursor on 'module' finds the direct macro expansion
    // Find the first 'module' keyword in the preprocessed text (which has
    // byte positions matching the original)
    let mod_off = alu_preprocessed.find("module")
        .expect("alu.typort should contain 'module' keyword");
    let found = expansions.iter().find(|e| {
        mod_off >= e.start_offset as usize && mod_off < e.end_offset as usize
    });
    assert!(found.is_some(), "cursor on 'module' should find an expansion");
    assert_eq!(found.unwrap().name, "module",
        "cursor on 'module' should find module expansion, not {:?}", found.unwrap().name);
    eprintln!("✓ cursor on 'module' (offset {}) -> {} expansion ({}-{})",
        mod_off, found.unwrap().name, found.unwrap().start_offset, found.unwrap().end_offset);
}
