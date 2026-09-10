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
    /// Whether the recorded `name` is an actual macro NAME token at the call
    /// site. Direct invocations (p_raw/p_decl) always are. Fragment-driven
    /// invocations (e.g. the `Expr` fragment used by `module`/`when` bodies)
    /// record the first call-site token as `name`, which is only a macro name
    /// when that token itself starts a nested macro call (like `when`); for a
    /// plain body statement (`sum := a +^ b`) the first token is user code and
    /// must not be treated as a macro name by goto-definition.
    pub name_token_is_macro: bool,
    /// Definition location of the macro rule that matched at this use site:
    /// byte offsets of the macro name token in the file that declared
    /// `macro_rules <name>`, plus that file's path_id. All `None` for macros
    /// without a textual definition (built-in `stringify`).
    pub def_start_offset: Option<u32>,
    pub def_end_offset: Option<u32>,
    pub def_path_id: Option<u32>,
}

use crate::parser_lib_resilient::*;

mod lex;
pub mod syntax;
pub mod macros;

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

#[derive(Debug, Clone)]
pub enum ErrMsg {
    Base(BaseMsg),
    /// A derive/expansion error with a full user-facing message
    /// (e.g. a malformed `impl IMasterSlave` direction spec).
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

pub type MacroState = (Vec<IError>, HashMap<String, Vec<MacroRule>>, Vec<MacroExpansionInfo>);

/// 宏展开重解析的递归深度上限：自递归宏（`macro_rules m { () => { m } }` +
/// `def x = m`）在展开后再次命中同名宏，若不加限制会无限递归直至栈溢出
/// （LSP 可在任意用户源码上触发）。合法宏/块嵌套深度远小于此值；超限推
/// 一条 IError 并停止展开（不再递归）。
const MAX_MACRO_EXPANSION_DEPTH: u32 = 256;

thread_local! {
    /// 当前线程的宏展开重解析深度（普通解析不计入）。
    static MACRO_DEPTH: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
}

/// RAII 深度守卫：`enter` 成功即计数 +1，`Drop`（含 panic 展开）时 -1。
struct MacroDepthGuard;

impl MacroDepthGuard {
    /// 进入下一层展开；已达上限返回 `None`（调用方推 IError 并退化）。
    fn enter() -> Option<Self> {
        MACRO_DEPTH.with(|d| {
            let n = d.get();
            if n >= MAX_MACRO_EXPANSION_DEPTH {
                None
            } else {
                d.set(n + 1);
                Some(MacroDepthGuard)
            }
        })
    }
}

impl Drop for MacroDepthGuard {
    fn drop(&mut self) {
        MACRO_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
    }
}

/// 展开超限错误（span 取宏调用首 token）。
fn macro_depth_error(input: &[TokenNode<'_>]) -> IError {
    IError {
        msg: input
            .first()
            .map(|x| x.to_span())
            .unwrap_or(empty_span(()))
            .map(|_| ErrMsg::Custom(format!(
                "macro expansion too deep (limit {})",
                MAX_MACRO_EXPANSION_DEPTH
            ))),
    }
}

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

/// Byte range in the expansion string -> the original owned token's source span.
struct ExpansionSpan {
    expansion_start: u32,
    expansion_end: u32,
    src_start: u32,
    src_end: u32,
    src_path_id: u32,
}

/// Like `owned_tokens_to_string`, but also records, for each token, the range it
/// occupies in the expansion string and the token's original source span. Used
/// to restore call-site spans after the expansion is re-lexed, so errors inside
/// a macro expansion point back into the user's source (not the expansion).
fn owned_tokens_to_string_mapped(tokens: &[OwnedToken]) -> (String, Vec<ExpansionSpan>) {
    let mut result = String::new();
    let mut map = Vec::with_capacity(tokens.len());
    for (i, tok) in tokens.iter().enumerate() {
        if i > 0 {
            result.push(' ');
        }
        let expansion_start = result.len() as u32;
        // Wrap Str tokens in double quotes (string literals)
        if tok.data.1 == TokenKind::Str {
            result.push('"');
            result.push_str(&tok.data.0);
            result.push('"');
        } else {
            result.push_str(&tok.data.0);
        }
        let expansion_end = result.len() as u32;
        map.push(ExpansionSpan {
            expansion_start,
            expansion_end,
            src_start: tok.start_offset,
            src_end: tok.end_offset,
            src_path_id: tok.path_id,
        });
    }
    (result, map)
}

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
                            // A macro expansion may have consumed the newline
                            // between two declarations (the literal-Token
                            // matcher skips one EndLine after a match, which
                            // when/switch-style macros rely on). When the
                            // remainder already starts with a declaration
                            // keyword, the expansion ate the separator — treat
                            // it as an implicit one and keep the current
                            // position (skip_until_decl would scan past this
                            // decl to the next EndLine+keyword and drop it).
                            let is_decl_start = input.first().map(|t| matches!(t.data.1,
                                TokenKind::DefKeyword
                                | TokenKind::EnumKeyword
                                | TokenKind::TraitKeyword
                                | TokenKind::ImplKeyword
                                | TokenKind::PackageKeyword
                                | TokenKind::ImportKeyword
                                | TokenKind::MacroKeyword
                                | TokenKind::PrintlnKeyword
                            )).unwrap_or(false);
                            if is_decl_start {
                                continue;
                            }
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

/// Parse with no pre-existing macros (for tests). Returns (declarations, parse errors).
pub fn parser(input: &str, id: u32) -> Option<(Vec<Decl>, Vec<IError>)> {
    parser_with_macros(input, id, &Default::default()).map(|(d, e, _, _)| (d, e))
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
        def_start_offset: None,
        def_end_offset: None,
        def_path_id: None,
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
                    // Placeholder for the lost declaration; the lesson has no
                    // `Package` no-op decl, so an empty println is used (parse
                    // errors are reported alongside, and only bad input hits
                    // this path).
                    || Ok(Decl::Println(Raw::Hole(empty_span(())))),
                )
                .many1_sep_skip(kw(EndLine), skip_until_decl).parse(&ret, &mut err_collect);
            match ret {
                Ok(ret) => {
                    let expansions = std::mem::take(&mut err_collect.2);
                    let exported: HashMap<String, Vec<MacroRule>> = err_collect.1.iter()
                        .filter(|(k, _)| !k.starts_with("__exported__") && err_collect.1.contains_key(&format!("__exported__{}", k)))
                        .map(|(k, v)| (k.clone(), v.clone()))
                        .collect();
                    if ret.0.is_empty() || ret.0.iter().all(|t| t.data.1 == TokenKind::Eof) {
                        Some((ret.1.into_iter().flatten().collect(), err_collect.0, exported, expansions))
                    } else {
                        err_collect.0.push(IError { msg: ret.0.first().unwrap().map(|_| ErrMsg::Base(BaseMsg::Expect(EndLine))) });
                        Some((ret.1.into_iter().flatten().collect(), err_collect.0, exported, expansions))
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
    [def] => { $crate::L12_canonical::parser::TokenKind::DefKeyword };
    [let] => { $crate::L12_canonical::parser::TokenKind::LetKeyword };
    [Type] => { $crate::L12_canonical::parser::TokenKind::TypeKeyword };
    [this] => { $crate::L12_canonical::parser::TokenKind::ThisKeyword };
    [_] => { $crate::L12_canonical::parser::TokenKind::Hole };
    ['('] => { $crate::L12_canonical::parser::TokenKind::LParen };
    [')'] => { $crate::L12_canonical::parser::TokenKind::RParen };
    ['['] => { $crate::L12_canonical::parser::TokenKind::LSquare };
    [']'] => { $crate::L12_canonical::parser::TokenKind::RSquare };
    ['{'] => { $crate::L12_canonical::parser::TokenKind::LCurly };
    ['}'] => { $crate::L12_canonical::parser::TokenKind::RCurly };
    [.] => { $crate::L12_canonical::parser::TokenKind::Dot };
    [,] => { $crate::L12_canonical::parser::TokenKind::Comma };
    [=] => { $crate::L12_canonical::parser::TokenKind::Eq };
    [;] => { $crate::L12_canonical::parser::TokenKind::Semi };
    [:] => { $crate::L12_canonical::parser::TokenKind::Colon };
    [->] => { $crate::L12_canonical::parser::TokenKind::Arrow };
    [=>] => { $crate::L12_canonical::parser::TokenKind::DoubleArrow };
    ['\\'] => { $crate::L12_canonical::parser::TokenKind::Lambda };
    [+] => { $crate::L12_canonical::parser::TokenKind::Op };
    [where] => { $crate::L12_canonical::parser::TokenKind::WhereKeyword };
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
        .or(|input: &'b [TokenNode<'a>], state: &mut MacroState| {
            // Characteristic of this lesson (canonical layer): no Nat literal —
            // numbers desugar to Church numeral chains over `zero`/`succ`.
            let (rest, x) = string(Num).parse(input, state)?;
            match x.data.parse::<u64>() {
                Ok(mut num) => {
                    let num_span = x.to_span();
                    let mut ret = Raw::Var(num_span.map(|_| SmolStr::new("zero")));
                    while num > 0 {
                        ret =
                            Raw::app(Raw::Var(num_span.map(|_| SmolStr::new("succ"))), ret);
                        num -= 1;
                    }
                    Ok((rest, ret))
                }
                Err(_) => {
                    // 整数超出 u64（如 `99999999999999999999999999`）：推一条
                    // 解析错误并退化为 `Raw::Hole`，不再 panic；与常规语法
                    // 错误同路径（双版共用本 parser）。
                    state.push_error(IError {
                        msg: x.to_span().map(|_| {
                            ErrMsg::Custom("integer literal does not fit in u64".to_owned())
                        }),
                    });
                    Ok((rest, Raw::Hole(x.to_span())))
                }
            }
        })
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
            // `{` as an application operator conflicts with `match x { ... }`
            // (the match scrutinee is parsed by expr_bp, which would steal the
            // `{` as an application argument list). Kept disabled, same as the
            // reference: the `else if "{"` branch below is dead code.
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
                        .map(|(x, t)| (Either::Name(x.clone()), t.1.unwrap_or(Raw::Hole(x.end_span()))))
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
                    // Dead code — the `{` operator is disabled above.
                    let (input_t, rhs) = p_raw
                        .many1_sep((kw(T![,]), kw(EndLine).option()))
                        .parse(input, state)?;
                    let (input_t, _) = kw(RCurly).parse(input_t, state)?;
                    input = input_t;
                    rhs.into_iter().fold(lhs, Raw::app)
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
                            op.end_span().map(|_| SmolStr::new(""))
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
        (smolstr(Ident), Cut((kw(Eq), p_raw))).map(|(x, t)| (Either::Name(x.clone()), t.1.unwrap_or(Raw::Hole(x.end_span()))))
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
        (smolstr(Ident), Cut((kw(Eq), p_bind))).map(|(x, (_, y))| (y.unwrap_or(x.to_span().map(|_| SmolStr::new(""))), Either::Name(x)))
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
            p_bind,
            (kw(Colon), p_raw).option(),
        )
            .map(|(xs, opt)| {
                let a = match opt {
                    Some((_, x)) => x,
                    None => Raw::Hole(xs.end_span()),
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
            // Body: `{ <Expr statements> }` braced statement block (same
            // machinery as braced def bodies — the LAST statement is the
            // arm's value) or a plain raw expression (p_block_body).
            Cut((kw(CaseKeyword), p_pattern, Cut((kw(T![=>]), p_block_body))))
                .map(|(case_kw, pattern, body_outer)| {
                    let pattern = pattern.unwrap_or(Pattern::Any(
                        case_kw.end_span().map(|_| true),
                        Either::Icit(Icit::Expl),
                    ));
                    // body_outer: Option<(arrow_span, Option<Raw>)>
                    // arrow_span is the `=>` token, body is the parsed expression
                    let body = body_outer.map_or(Raw::Hole(case_kw.end_span()), |(arrow, body)| {
                        body.unwrap_or(Raw::Hole(arrow.end_span()))
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
        paren_cut(p_raw.many0_sep(kw(T![,]))),
    ))
        .map(|(new_kw, scrutinee, args)| args.and_then(|r| r.ok()).unwrap_or_default().into_iter()
            .fold(Raw::Var(scrutinee.map_or(new_kw.to_span().map(|_| SmolStr::new("")), |x| x.map(|x| SmolStr::new(format!("{x}.mk"))))), |acc, x| 
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
                        name_token_is_macro: true,
                        def_start_offset: m.def_start_offset,
                        def_end_offset: m.def_end_offset,
                        def_path_id: m.def_path_id,
                    });
                }
                // Re-lex the expanded text instead of splicing the owned tokens
                // directly: owned tokens carry spans/path_ids from the macro
                // definition, and mixing them with call-site tokens made the
                // re-parse of the expansion fail (Expect(EndLine) at a literal
                // token's definition-site span). The EOF token is filtered so
                // the recursive p_raw sees a clean token stream.
                let (t_str, span_map) = owned_tokens_to_string_mapped(&t_owned);
                let invocation_start = input[0].start_offset;
                let invocation_end = if input.len() > i.len() { input[input.len() - i.len() - 1].end_offset } else { input[0].end_offset };
                let call_site_path = input[0].path_id;
                let t_borrowed: Vec<_> = match super::parser::lex::lex(Span {
                    data: &t_str,
                    start_offset: 0,
                    end_offset: t_str.len() as u32,
                    path_id: call_site_path,
                }) {
                    Some((_, lexed)) => lexed.into_iter().filter(|t| t.data.1 != TokenKind::Eof).map(|t| {
                        // Restore the original source span for each re-lexed
                        // token: metavar captures keep their call-site span;
                        // transcriber literals (definition-site path) map to the
                        // whole invocation so errors stay inside the macro call.
                        let orig = span_map.iter().find(|m| m.expansion_start <= t.start_offset && t.start_offset < m.expansion_end);
                        match orig {
                            Some(m) if m.src_path_id == call_site_path => Span {
                                data: (t.data.0, t.data.1),
                                start_offset: m.src_start,
                                end_offset: m.src_end,
                                path_id: m.src_path_id,
                            },
                            _ => Span {
                                data: (t.data.0, t.data.1),
                                start_offset: invocation_start,
                                end_offset: invocation_end,
                                path_id: call_site_path,
                            },
                        }
                    }).collect(),
                    None => t_owned.iter().map(|tok| Span {
                        data: (tok.data.0.as_str(), tok.data.1),
                        start_offset: tok.start_offset,
                        end_offset: tok.end_offset,
                        path_id: tok.path_id,
                    }).collect(),
                };
                let _guard = match MacroDepthGuard::enter() {
                    Some(g) => g,
                    // 展开深度超限：停止递归，返回错误（由上层 recover 记录）。
                    None => return Err(macro_depth_error(input)),
                };
                let mut temp_state = (vec![], state.1.clone(), vec![]);
                let ret = p_raw(&t_borrowed, &mut temp_state)?;
                state.0.extend(temp_state.0);
                state.2.extend(temp_state.2);
                if !ret.0.is_empty() {
                    state.0.push(IError { msg: ret.0.first().unwrap().map(|_| ErrMsg::Base(BaseMsg::Expect(TokenKind::EndLine))) });
                } else {
                    // The literal-Token matcher eats one EndLine after each
                    // matched token (see MacroMatcher::Token), so a rule
                    // ending in `}` consumes the newline that separates this
                    // invocation from the NEXT statement/declaration/match
                    // arm. Callers use that newline as a separator (p_let
                    // chains, the decl list, match-arm lists), and losing it
                    // surfaced as "expected newline"/"expected `}`" leftover
                    // errors — e.g. `def f(...): Unit = when c { ... }` as
                    // the second-to-last declaration. Give exactly one eaten
                    // trailing EndLine back (mirrors the decl-level macro
                    // dispatch's backoff in p_decl); a real last statement
                    // token (e.g. the `3` in `twice 3`) stays consumed.
                    let consumed = input.len() - i.len();
                    let i = if consumed > 0
                        && input[consumed - 1].data.1 == TokenKind::EndLine
                        && !matches!(i.first().map(|t| t.data.1), Some(TokenKind::EndLine))
                    {
                        input.get(consumed - 1..).unwrap()
                    } else {
                        i
                    };
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
                .map(|x| x.map(|_| ErrMsg::Base(BaseMsg::ExpectRaw)))
                .unwrap_or(empty_span(ErrMsg::Base(BaseMsg::ExpectRaw)))
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
        // Body: `{ <Expr statements> }` braced statement block (SpinalHDL
        // style, hardware statements allowed) or a plain raw expression.
        // NOTE: no `.option()` — the Cut tuple already wraps elements 2+
        // in Option (the parser recovers on failure).
        p_block_body,
    ))
        .map(|(def_kw, name, params, ret, where_clause, eq_kw, body)| {
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
                                let mut app = Raw::Var(bound.to_span().map(|_| trait_name.clone()));
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
                            all_params.push((type_name.to_span().map(|_| inst_name.clone()), trait_app, Icit::Impl));
                        }
                    }
                }
            }
            Decl::Def {
                name: name.unwrap_or(def_kw.end_span().map(|_| SmolStr::new(""))),
                params: all_params,
                ret_type: ret.flatten().unwrap_or(Raw::Hole(def_kw.end_span())),
                body: body.unwrap_or(Raw::Hole(eq_kw.unwrap_or(def_kw).end_span())),
            }
        })
        .parse(input, state)
}

// ============================================================
//  Braced statement blocks: `def f(): T = { <Expr statements> }`
//  and `match x { case p => { <Expr statements> } }`
// ============================================================
// Statement blocks are parsed statement-by-statement through the `Expr`
// macro's named fragment — the SAME machinery a `module` macro body uses —
// and the transcriptions are spliced into one let-chain expression:
//   - statements before the last are transcribed as-is (they are all
//     `let ...;`-shaped, so the chain continues across `;`)
//   - the LAST statement is the block's value:
//       - a plain expression keeps its original tokens
//         (def f(): Nat = { 1 + 1 }  →  body is `1 + 1`)
//       - a hardware declaration arm (`reg x = ...`, `let x = ...`, a port
//         declaration) is transcribed and the declared binder becomes the
//         value (`def mk(): UInt[8] = { reg x = UInt[8] }`  →  returns x)
//       - a control chain (`when`/`switch` — `_`-bound transcription) is
//         transcribed with `unit` as the value
// For a case arm the block value is the ARM's value (all arms of one match
// must still agree on a type). When no `Expr` rules are registered (plain
// inputs without the HDL prelude), `{`-blocks are rejected exactly as
// before the statement-block machinery existed.

/// Match one block statement against the `Expr` macro rules (first match
/// wins, like the `$body: Expr` fragment in the `module` macro). Returns
/// the transcription tokens, the statement's original tokens, and which
/// rule matched (the LAST rule is the raw-expression catch-all).
fn p_expr_block_stmt<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut MacroState,
) -> IResult<'a, 'b, (Vec<OwnedToken>, Vec<OwnedToken>, usize, usize)> {
    let err = || IError {
        msg: input
            .first()
            .map(|x| x.map(|_| ErrMsg::Base(BaseMsg::Expect(TokenKind::EndLine))))
            .unwrap_or(empty_span(ErrMsg::Base(BaseMsg::Expect(TokenKind::EndLine)))),
    };
    let rules = match state.1.get("Expr") {
        Some(r) => r.clone(),
        None => return Err(err()),
    };
    for (idx, m) in rules.iter().enumerate() {
        if let Ok((i, t)) = m.matcher.to_parser().parse(input, state) {
            let t_owned = m.transcriber.replace(t)?;
            let consumed = input.len() - i.len();
            let original: Vec<OwnedToken> = input[..consumed].iter().map(|tok| Span {
                data: (tok.data.0.to_owned(), tok.data.1),
                start_offset: tok.start_offset,
                end_offset: tok.end_offset,
                path_id: tok.path_id,
            }).collect();
            // Record the expansion for LSP hover/goto-definition (same as
            // the fragment-driven invocation path in macros.rs).
            if let Some(first) = input.first() {
                let (def_start, def_end, def_path) = state.1.get(first.data.0)
                    .and_then(|r| r.first())
                    .map(|r| (r.def_start_offset, r.def_end_offset, r.def_path_id))
                    .unwrap_or((m.def_start_offset, m.def_end_offset, m.def_path_id));
                let start = first.start_offset;
                let end = if consumed > 0 { input[consumed - 1].end_offset } else { first.end_offset };
                state.2.push(MacroExpansionInfo {
                    name: first.data.0.to_string(),
                    start_offset: start,
                    end_offset: end,
                    expanded_text: owned_tokens_to_string(&t_owned),
                    // The first call-site token starts a nested macro call
                    // (when/switch) or is user code (a declaration) — same
                    // rule as the module-body fragment.
                    name_token_is_macro: state.1.contains_key(first.data.0),
                    def_start_offset: def_start,
                    def_end_offset: def_end,
                    def_path_id: def_path,
                });
            }
            return Ok((i, (t_owned, original, idx, rules.len())));
        }
    }
    Err(err())
}

/// `{ <stmt>* }` — parse one braced statement block (input starts AFTER the
/// `{`); shared by def bodies and match case arms via p_block_body.
fn p_def_stmt_block<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut MacroState,
    lcurly: Span<()>,
) -> IResult<'a, 'b, Raw> {
    let mut body_tokens: Vec<OwnedToken> = vec![];
    let mut input = input;
    let mut rcurly_span: Option<Span<()>> = None;
    loop {
        let (i, _) = kw(EndLine).many0().parse(input, state)?;
        input = i;
        if let Ok((i, rc)) = kw(RCurly).parse(input, state) {
            rcurly_span = Some(rc);
            input = i;
            break;
        }
        // One statement, transcribed through the `Expr` fragment.
        let (rest, (transcription, mut original, rule_idx, num_rules)) = p_expr_block_stmt.parse(input, state)?;
        // Optional `;` / EndLine between statements (the transcription ends
        // with its own `;`, so a user-written one just needs skipping).
        let (rest, _) = kw(Semi).option().parse(rest, state)?;
        // Peek whether this is the last statement (end of block).
        let (rest2, _) = kw(EndLine).many0().parse(rest, state)?;
        if let Ok((rest3, rc)) = kw(RCurly).parse(rest2, state) {
            // Last statement → the block value (see the block header note).
            if rule_idx + 1 == num_rules {
                // Raw-expression catch-all: the statement IS the value.
                // Trim a trailing `;`/EndLine the user may have written.
                while matches!(original.last().map(|t| t.data.1), Some(TokenKind::Semi) | Some(TokenKind::EndLine)) {
                    original.pop();
                }
                body_tokens.extend(original);
            } else if transcription.len() >= 2
                && transcription[0].data.1 == TokenKind::LetKeyword
                && transcription[1].data.1 == TokenKind::Ident
            {
                // Hardware declaration arm: `let <binder> ...;` — the value
                // is the declared binder.
                if transcription[1].data.0 == "_" {
                    body_tokens.extend(transcription);
                    body_tokens.push(Span {
                        data: ("unit".to_string(), TokenKind::Ident),
                        start_offset: rc.start_offset,
                        end_offset: rc.end_offset,
                        path_id: rc.path_id,
                    });
                } else {
                    let binder = transcription[1].clone();
                    body_tokens.extend(transcription);
                    body_tokens.push(binder);
                }
            } else {
                // Control chain (`_`-bound transcription) → Unit value.
                body_tokens.extend(transcription);
                body_tokens.push(Span {
                    data: ("unit".to_string(), TokenKind::Ident),
                    start_offset: rc.start_offset,
                    end_offset: rc.end_offset,
                    path_id: rc.path_id,
                });
            }
            rcurly_span = Some(rc);
            input = rest3;
            break;
        }
        // Middle statement: splice the transcription into the let chain.
        body_tokens.extend(transcription);
        input = rest;
    }
    let rcurly = rcurly_span.unwrap_or(lcurly.end_span());
    if body_tokens.is_empty() {
        return Ok((input, Raw::Hole(lcurly)));
    }
    // Re-lex the spliced body and parse it as ONE expression (the let-chain
    // with the value tail) — mirroring p_raw's macro-expansion path so token
    // spans map back to the block / source.
    let (t_str, span_map) = owned_tokens_to_string_mapped(&body_tokens);
    let invocation_start = lcurly.start_offset;
    let invocation_end = rcurly.end_offset;
    let call_site_path = lcurly.path_id;
    let t_borrowed: Vec<TokenNode> = match lex::lex(Span {
        data: &t_str,
        start_offset: 0,
        end_offset: t_str.len() as u32,
        path_id: call_site_path,
    }) {
        Some((_, lexed)) => lexed.into_iter().filter(|t| t.data.1 != TokenKind::Eof).map(|t| {
            let orig = span_map.iter().find(|m| m.expansion_start <= t.start_offset && t.start_offset < m.expansion_end);
            match orig {
                Some(m) if m.src_path_id == call_site_path => Span {
                    data: (t.data.0, t.data.1),
                    start_offset: m.src_start,
                    end_offset: m.src_end,
                    path_id: m.src_path_id,
                },
                _ => Span {
                    data: (t.data.0, t.data.1),
                    start_offset: invocation_start,
                    end_offset: invocation_end,
                    path_id: call_site_path,
                },
            }
        }).collect(),
        None => {
            return Err(IError { msg: lcurly.map(|_| ErrMsg::Base(BaseMsg::ExpectRaw)) });
        }
    };
    let _guard = match MacroDepthGuard::enter() {
        Some(g) => g,
        None => return Err(macro_depth_error(input)),
    };
    let mut temp_state = (vec![], state.1.clone(), vec![]);
    let ret = p_raw(&t_borrowed, &mut temp_state)?;
    state.0.extend(temp_state.0);
    state.2.extend(temp_state.2);
    if !ret.0.is_empty() {
        return Err(IError {
            msg: ret.0.first().unwrap().map(|_| ErrMsg::Base(BaseMsg::ExpectRaw)),
        });
    }
    Ok((input, ret.1))
}

/// Body of a braced-statement-block context: `{ <Expr statements> }` when it
/// starts with `{` (p_raw cannot parse a leading `{`, so the two body forms
/// never overlap), otherwise the plain raw expression. Used by def bodies
/// (`def f(): T = { ... }` / `def f(): T = expr`) and match case arms
/// (`case p => { ... }` / `case p => expr`) — the LAST statement of a block
/// is the body's value (see p_def_stmt_block).
fn p_block_body<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    if let Ok((after_lcurly, (_, lcurly))) = (kw(EndLine).option(), kw(LCurly)).parse(input, state) {
        return p_def_stmt_block(after_lcurly, state, lcurly);
    }
    (kw(EndLine).option(), p_raw)
        .parse(input, state)
        .map(|(i, (_, x))| (i, x))
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
        .map(|(enum_kw, name, params, fields)| Decl::Enum {
            is_trait: false,
            name: name.unwrap_or(enum_kw.end_span().map(|_| SmolStr::new(""))),
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
        ),
    ))
        .map(|(struct_kw, name, params, fields)| Decl::Enum {
            is_trait: false,
            name: name.clone().unwrap_or(struct_kw.end_span().map(|_| SmolStr::new(""))),
            params: params.clone().unwrap_or_default(),
            cases: vec![
                (
                    name.clone().map(|x| x.map(|x| SmolStr::new(format!("{x}.mk")))).unwrap_or(struct_kw.end_span().map(|_| SmolStr::new(""))),
                    fields.clone().and_then(|r| r.ok()).unwrap_or_default().into_iter().map(|x| (x.0, x.1, Icit::Expl)).collect(),
                    None,
                ),
            ]
        })
        .parse(input, state)
}

/// Parse a `trait Name` body: method declarations without bodies
/// (`def eq(x: A): Bool`) — the shape these lessons' checkers consume.
fn p_trait_def<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
    let p_def_declare = (
        kw(DefKeyword),
        smolstr(Ident).or(smolstr(Op)),
        p_pi_binder
            .many0()
            .map(|x| x.into_iter().flatten().collect::<Vec<_>>()),
        (kw(T![:]), p_raw).map(|(_, x)| x),
    )
        .map(|(_, name, params, ret)| (name, params, ret));
    (
        kw(TraitKeyword),
        smolstr(Ident),
        p_pi_impl_binder_option,
        brace(p_def_declare.many0_sep(kw(EndLine))),
    )
        .map(|(_, name, params, body)| Decl::TraitDecl {
            name,
            params,
            methods: body.ok().unwrap_or_default(),
        })
        .parse(input, state)
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
        brace(p_def.many0_sep(kw(EndLine))),
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
        .map(|(params, trait_name, trait_params, name, body, need_create)| Decl::ImplDecl {
            name,
            params: params.unwrap_or_default(),
            trait_name,
            trait_params,
            methods: body.and_then(|r| r.ok()).unwrap_or_default(),
            need_create,
        })
        .parse(input, state)
}



// 在 mod.rs 中添加这些函数
/// Token index where the paren depth first returns to zero, counting from the
/// start of `input`. For `input[0] == '('` this is the matching `)`. The
/// macro-definition parser needs this to find where a matcher pattern (or a
/// `$(...)* ` group body) ends when the pattern itself contains literal
/// `(` `)` tokens — the Verilog-compat arms (`always @ ( posedge $clk )`,
/// `module top ( input a )`) are the first users.
fn paren_close_index(input: &[TokenNode]) -> Option<usize> {
    let mut depth = 0usize;
    for (i, t) in input.iter().enumerate() {
        match t.data.1 {
            TokenKind::LParen => depth += 1,
            TokenKind::RParen => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

fn err_expect(input: &[TokenNode], kind: TokenKind) -> IError {
    IError {
        msg: input
            .first()
            .map(|x| x.map(|_| ErrMsg::Base(BaseMsg::Expect(kind))))
            .unwrap_or_else(|| empty_span(ErrMsg::Base(BaseMsg::Expect(kind)))),
    }
}

/// `$( matcher-sequence ) op` — balanced-paren aware: the sequence ends at
/// the RParen matching the group's LParen, so the sequence may itself contain
/// literal `(` `)` tokens.
fn p_macro_group_matcher<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, MacroMatcher> {
    (kw_is(Op, "$"), kw(LParen)).parse(input, state)?;
    let close = paren_close_index(input).ok_or_else(|| err_expect(input, TokenKind::RParen))?;
    // input[0] is `$`, input[1] is the group's `(` — content starts at 2.
    let inner = &input[2..close];
    // Trim surrounding EndLine tokens (a pattern may wrap lines).
    let start = inner.iter().position(|t| t.data.1 != TokenKind::EndLine).unwrap_or(inner.len());
    let end = inner[start..].iter().rposition(|t| t.data.1 != TokenKind::EndLine).map(|p| start + p + 1).unwrap_or(start);
    let (rest, matchers) = p_macro_matcher_sequence.parse(&inner[start..end], state)?;
    if !rest.is_empty() {
        return Err(err_expect(rest, TokenKind::RParen));
    }
    let (after, (_, s)) = (kw(RParen), string_is(Op, "*").or(string_is(Op, "+")).or(string_is(Op, "?")))
        .parse(&input[close..], state)?;
    let seq: Box<MacroMatcher> = MacroMatcher::Sequence(matchers).into();
    let m = if s.data == "*" {
        MacroMatcher::Many0(seq)
    } else if s.data == "+" {
        MacroMatcher::Many1(seq)
    } else {
        MacroMatcher::Optional(seq)
    };
    Ok((after, m))
}

fn parse_fragment_kind<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut MacroState
) -> IResult<'a, 'b, MacroFragment> {
    string(Ident).parse(input, state).map(|(input, span)| {
        let fragment = match span.data.as_str() {
            "ident" => MacroFragment::Ident,
            "raw" => MacroFragment::Raw,
            "params" => MacroFragment::Param,
            _ => {
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
    
    // 尝试解析分组 $(...)* / $(...)+ / $(...)? — balanced-paren aware
    // (p_macro_group_matcher)，序列内可含字面 ( ) token。

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
        .or(string(ForKeyword).map(|span| MacroMatcher::Token(ForKeyword, span)))
        .or(string(Eq).map(|span| MacroMatcher::Token(Eq, span)))
        .or(string(Dot).map(|span| MacroMatcher::Token(Dot, span)))
        .or(string(ByKeyword).map(|span| MacroMatcher::Token(ByKeyword, span)))
        .or(string(Hole).map(|span| MacroMatcher::Token(Hole, span)))
        .or(string(Colon).map(|span| MacroMatcher::Token(Colon, span)))
        // Verilog-compat layer: patterns for `module (...)`, `always @(...)`,
        // `q <= d ;`, `.a(x), .b(y)` need these as literal tokens. The
        // matcher itself (MacroMatcher::Token) has always been generic over
        // (kind, text); only the pattern-side parser was limited. Additive —
        // existing macro patterns never contain these tokens.
        .or(string(LParen).map(|span| MacroMatcher::Token(LParen, span)))
        .or(string(RParen).map(|span| MacroMatcher::Token(RParen, span)))
        .or(string(Semi).map(|span| MacroMatcher::Token(Semi, span)))
        .or(string(Comma).map(|span| MacroMatcher::Token(Comma, span)))
        .or(string(CaseKeyword).map(|span| MacroMatcher::Token(CaseKeyword, span)))
        .or(string(MatchKeyword).map(|span| MacroMatcher::Token(MatchKeyword, span)));
    
    metavar_parser
        .or(p_macro_group_matcher)
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
    p_macro_matcher_sequence.map(|matchers| {
        if matchers.len() == 1 {
            matchers.into_iter().next().unwrap()
        } else {
            MacroMatcher::Sequence(matchers)
        }
    })
    .parse(input, state)
}

/// `( matcher-sequence )` for one macro arm — balanced-paren aware so the
/// sequence may contain literal `(` `)` tokens (Verilog-compat patterns).
fn p_macro_matcher_paren<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, MacroMatcher> {
    kw(LParen).parse(input, state)?;
    let close = paren_close_index(input).ok_or_else(|| err_expect(input, TokenKind::RParen))?;
    let inner = &input[1..close];
    // Trim surrounding EndLine tokens (the old `paren` wrapper allowed one
    // optional EndLine on each side; trimming all is a superset).
    let start = inner.iter().position(|t| t.data.1 != TokenKind::EndLine).unwrap_or(inner.len());
    let end = inner[start..].iter().rposition(|t| t.data.1 != TokenKind::EndLine).map(|p| start + p + 1).unwrap_or(start);
    let (rest, m) = p_macro_matcher.parse(&inner[start..end], state)?;
    if !rest.is_empty() {
        return Err(err_expect(rest, TokenKind::RParen));
    }
    Ok((&input[close + 1..], m))
}

fn p_macro_transcriber_single<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut MacroState
) -> IResult<'a, 'b, MacroTranscriber> {
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
                } else if input.is_empty() || (kw(RParen), kw_is(Op, "*")).parse(input, state).is_ok() || (kw(RParen), kw_is(Op, "+")).parse(input, state).is_ok() || (kw(RParen), kw_is(Op, "?")).parse(input, state).is_ok() {
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
                    let (i, _) = (kw(RParen), kw_is(Op, "*")).or((kw(RParen), kw_is(Op, "+"))).or((kw(RParen), kw_is(Op, "?"))).parse(i, state)?;// op: * + ?
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
        Err(_) => {
            // No leading '{' - parse as flat token sequence with possible $(...) groups
            let mut input = input;
            let mut i_back = input;
            let mut ret = vec![];
            while !input.is_empty()
                && (kw(RParen), kw_is(Op, "*")).parse(input, state).is_err()
                && (kw(RParen), kw_is(Op, "+")).parse(input, state).is_err()
                && (kw(RParen), kw_is(Op, "?")).parse(input, state).is_err()
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
                    let (i, _) = (kw(RParen), kw_is(Op, "*")).or((kw(RParen), kw_is(Op, "+"))).or((kw(RParen), kw_is(Op, "?"))).parse(i, state)?;
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
                p_macro_matcher_paren,  // 匹配器在平衡括号 (...) 中
                kw(T![=>]),
                p_macro_transcriber_single,  // 转写器在 (...) 中
            )).map(|(matcher, _, transcriber)| MacroRule {
                matcher,
                transcriber: transcriber.unwrap_or(MacroTranscriber::Sequence(vec![])),
                def_start_offset: None,
                def_end_offset: None,
                def_path_id: None,
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
                // Stamp the definition span (the `macro_rules <name>` name
                // token) onto every rule so use sites can resolve
                // goto-definition back to this declaration.
                let rules: Vec<MacroRule> = rules.and_then(|r| r.ok()).unwrap_or_default()
                    .into_iter()
                    .map(|rule| MacroRule {
                        def_start_offset: Some(name.start_offset),
                        def_end_offset: Some(name.end_offset),
                        def_path_id: Some(name.path_id),
                        ..rule
                    })
                    .collect();
                state.1.insert(name.data.clone(), rules);
            }
            Ok((input, ()))
        },
        Err(e) => Err(e),
    }
}

fn p_decl<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
    if let Some(macro_decl) = input.first().and_then(|x| state.1.get(x.data.0).cloned()) {
        let is_cut = macro_decl.len() == 1;
        for m in macro_decl {
            let (i, t) = if is_cut {
                match m.matcher.to_parser().parse(input.get(1..).unwrap(), state) {
                    Ok(x) => x,
                    Err(e) => {
                        state.0.push(e);
                        return Ok((input.get(1..).unwrap_or(&[]), Decl::Println(Raw::Hole(empty_span(())))))
                    }
                }
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
                    name_token_is_macro: true,
                    def_start_offset: m.def_start_offset,
                    def_end_offset: m.def_end_offset,
                    def_path_id: m.def_path_id,
                });
            }
            let t_borrowed: Vec<_> = t_owned.iter().map(|tok| Span {
                data: (tok.data.0.as_str(), tok.data.1),
                start_offset: tok.start_offset,
                end_offset: tok.end_offset,
                path_id: tok.path_id,
            }).collect();
            let _guard = match MacroDepthGuard::enter() {
                Some(g) => g,
                // 展开深度超限：停止递归，推 IError 后退化（is_cut → Hole，
                // 否则试下一条规则），与本函数现有 Err 分支同款。
                None => {
                    state.0.push(macro_depth_error(input));
                    if is_cut {
                        return Ok((i, Decl::Println(Raw::Hole(empty_span(())))))
                    } else {
                        continue;
                    }
                }
            };
            let mut temp_state = (vec![], state.1.clone(), vec![]);
            let ret = match p_decl(&t_borrowed, &mut temp_state) {
                Ok(r) => r,
                Err(e) => {
                    state.0.extend(temp_state.0);
                    state.2.extend(temp_state.2);
                    state.0.push(e);
                    if is_cut {
                        return Ok((i, Decl::Println(Raw::Hole(empty_span(())))))
                    } else {
                        continue;
                    }
                }
            };
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
    p_def.or(p_print).or(p_enum).or(p_struct).or(p_trait_def).or(p_impl)
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
        Ok(ret) => if ret.0.is_empty() || ret.0.iter().all(|t| t.data.1 == TokenKind::Eof) {
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
fn test3() {
    let input = r#"
macro_rules stringify {
    ($x: ident) => { $x }
}
"#;
    println!("{:#?}", parser(input, 0).unwrap());
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
fn test_macro_expansion_span_preservation() {
    // A raw metavar captured at the call site must keep its source span after
    // the expansion is re-lexed. Regression: expansion-relative offsets used
    // to leak into the Raw AST, so elaboration errors floated to wrong places.
    let input = r#"
macro_rules mwrap {
    ($x: raw) => { $x }
}
def f = mwrap 12345
"#;
    let processed = crate::L12_canonical::preprocess(input);
    let (decls, _errs, _exports, _expansions) = parser_with_macros(&processed, 7, &Default::default()).unwrap();
    let def = decls.iter()
        .find(|d| matches!(d, Decl::Def { name, .. } if name.data == "f"))
        .expect("expected def f");
    let body = match def {
        Decl::Def { body, .. } => body,
        _ => unreachable!(),
    };
    let num_off = processed.find("12345").expect("12345 should be in input");
    let span = body.to_span();
    assert_eq!(span.start_offset as usize, num_off,
        "expanded raw fragment must keep its call-site start offset");
    assert_eq!(span.end_offset as usize, num_off + "12345".len(),
        "expanded raw fragment must keep its call-site end offset");
}

#[test]
fn test_macro_expansion_span_preservation_multitoken() {
    // Multi-token raw capture: every token of the captured expression keeps
    // its source span, so the whole expanded expression covers its source
    // region instead of a 0-based slice of the expansion text.
    let input = r#"
macro_rules mwrap {
    ($x: raw) => { $x }
}
def g = mwrap a + b * c
"#;
    let processed = crate::L12_canonical::preprocess(input);
    let (decls, _errs, _exports, _expansions) = parser_with_macros(&processed, 7, &Default::default()).unwrap();
    let def = decls.iter()
        .find(|d| matches!(d, Decl::Def { name, .. } if name.data == "g"))
        .expect("expected def g");
    let body = match def {
        Decl::Def { body, .. } => body,
        _ => unreachable!(),
    };
    let a_off = processed.find("a + b * c").expect("expr should be in input");
    let end = a_off + "a + b * c".len();
    let span = body.to_span();
    assert!(span.start_offset as usize <= a_off && span.end_offset as usize >= end,
        "multitoken expanded raw must cover its source region, got {}..{} vs {}..{}",
        span.start_offset, span.end_offset, a_off, end);
}

#[test]
fn test_macro_expansion_info_def_span_local() {
    // A macro defined and used in the same file: the expansion info must
    // carry the definition span (the `macro_rules <name>` name token) and
    // the defining file's path_id, so the LSP can resolve goto-definition.
    let input = r#"
macro_rules mym {
    ($x: raw) => { $x $x }
}
mym stringify hello
"#;
    let id = 42u32;
    let (_decls, _errs, _exports, expansions) = parser_with_macros(input, id, &Default::default()).unwrap();
    let exp = expansions.iter().find(|e| e.name == "mym").expect("mym expansion should exist");

    // Definition span = the `mym` name token in `macro_rules mym {`
    let def_off = input.find("macro_rules mym").expect("def in input")
        + "macro_rules ".len();
    assert_eq!(exp.def_start_offset, Some(def_off as u32),
        "def_start_offset should point at the macro name token");
    assert_eq!(exp.def_end_offset, Some((def_off + "mym".len()) as u32),
        "def_end_offset should end at the macro name token");
    assert_eq!(exp.def_path_id, Some(id),
        "def_path_id should be the defining file's id");

    // The use-site span still covers the invocation in the source.
    let use_off = input.find("mym stringify").expect("use in input");
    assert_eq!(exp.start_offset as usize, use_off);
    assert_eq!(exp.end_offset as usize, use_off + "mym stringify hello".len());

    // Built-in `stringify` has no textual definition.
    let str_exp = expansions.iter().find(|e| e.name == "stringify").expect("stringify expansion");
    assert_eq!(str_exp.def_start_offset, None);
    assert_eq!(str_exp.def_end_offset, None);
    assert_eq!(str_exp.def_path_id, None);
}

#[test]
fn test_macro_expansion_info_def_span_cross_file() {
    // A macro exported from another file (id 7) and used in this file (id 42):
    // the use-site expansion must point back at the defining file, so the LSP
    // can resolve a cross-file goto (the prelude case).
    let def_input = r#"
#[macro_export]
macro_rules mym {
    ($x: raw) => { $x $x }
}
"#;
    let (_d, _e, exports, _) = parser_with_macros(def_input, 7, &Default::default()).unwrap();
    assert!(exports.contains_key("mym"), "macro should be exported");

    // Note: a use-only single-line file would make the top-level
    // many1_sep_skip fail with EmptyVec (pre-existing parser behavior), so
    // the use file carries a leading successful declaration like real files.
    let use_input = "println x
mym stringify hello
";
    let (_d2, _e2, _ex2, expansions) = parser_with_macros(use_input, 42, &exports).unwrap();
    let exp = expansions.iter().find(|e| e.name == "mym").expect("mym expansion should exist");
    let def_off = def_input.find("macro_rules mym").expect("def in input")
        + "macro_rules ".len();
    assert_eq!(exp.def_path_id, Some(7), "def must point at the exporting file");
    assert_eq!(exp.def_start_offset, Some(def_off as u32));
    assert_eq!(exp.def_end_offset, Some((def_off + "mym".len()) as u32));
}

#[test]
fn test_macro_expansion_info_def_span_multi_rule() {
    // Multi-rule macro (like `when`): whichever rule matches, the expansion
    // records the same definition span (the macro name token).
    let input = r#"
macro_rules pick {
    (a) => { println first };
    (b) => { println second }
}
pick b
"#;
    let (_decls, _errs, _exports, expansions) = parser_with_macros(input, 0, &Default::default()).unwrap();
    let exp = expansions.iter().find(|e| e.name == "pick").expect("pick expansion should exist");
    let def_off = input.find("macro_rules pick").expect("def in input")
        + "macro_rules ".len();
    assert_eq!(exp.def_start_offset, Some(def_off as u32),
        "matched rule should carry the macro_rules name token span");
    assert_eq!(exp.def_end_offset, Some((def_off + "pick".len()) as u32));
    assert_eq!(exp.def_path_id, Some(0));
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