use smol_str::SmolStr;
use lex::{TokenKind, TokenNode};
use syntax::{Decl, Either, Icit, Pattern, Raw};

use std::rc::Rc;
use rustc_hash::FxHashMap as HashMap;
use serde::{Serialize, Deserialize};

use crate::parser_lib_resilient::*;

use macros::*;

mod lex;
pub mod syntax;
mod macros;

use TokenKind::*;

use super::empty_span;

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

/// 错误进度 = 错误锚定的 token 源偏移。`or_far` 用它保留"最远失败"的备选
/// 错误，而不是 last-branch-wins 把正确位置吞掉（review R6：`p_decl` 的
/// `or` 链会把 `def` 在 `)` 处的错误换成 `enum` 分支在 `def` 处的错误）。
impl ErrorProgress for IError {
    fn parse_progress(&self) -> u32 {
        self.msg.start_offset
    }
}

type IResult<'a, 'b, O> = Result<(&'b [TokenNode<'a>], O), IError>;

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


// macro_rules 状态：错误流 + 宏规则表（Rc 快照）+ 展开记录（LSP）。
/// 累积宏表：整表包 `Rc`、每条规则表包 `Rc`。parse 期只在 `macro_rules`
/// 声明点经 `Rc::make_mut` 增量插入（此时表独占，O(1)）；展开期
/// `p_raw`/`p_decl` 递归用 `state.1.clone()` 传快照——Rc 克隆 O(1)，
/// 取代过去每次展开对整表（含规则匹配器/转写器树）的深克隆；入口
/// `state.1.get(..).cloned()` 同理降为规则表的 Rc 克隆。
pub type MacroState = (Vec<IError>, Rc<HashMap<String, Rc<Vec<MacroRule>>>>, Vec<MacroExpansionInfo>);

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

/// 把展开 token 序列化成文本（仅用于 `MacroExpansionInfo.expanded_text`
/// 的 LSP 记录；展开本身已改为 `splice_transcriber` 直接拼接 token，不再
/// 经过「序列化 → 重词法」往返）。与 `owned_tokens_to_string` 逐字节一致。
fn borrowed_tokens_to_string(tokens: &[TokenNode<'_>]) -> String {
    let mut result = String::new();
    for (i, tok) in tokens.iter().enumerate() {
        if i > 0 {
            result.push(' ');
        }
        // Wrap Str tokens in double quotes (string literals)
        if tok.data.1 == TokenKind::Str {
            result.push('"');
            result.push_str(tok.data.0);
            result.push('"');
        } else {
            result.push_str(tok.data.0);
        }
    }
    result
}

/// 相邻 EndLine 折叠 + 丢弃 Eof：整串重词法按构造具备的两个归一化行为
/// （lexer 的 endline matcher 是 many1——连续换行合一；Eof 不产出）。
/// 直接拼接据此对齐，保证与旧重词法路径的 token 流逐 token 一致。
fn splice_push<'t>(out: &mut Vec<TokenNode<'t>>, tok: TokenNode<'t>) {
    if tok.data.1 == TokenKind::Eof {
        return;
    }
    if tok.data.1 == TokenKind::EndLine
        && out.last().map_or(false, |p| p.data.1 == TokenKind::EndLine)
    {
        return;
    }
    out.push(tok);
}

/// 直接拼接展开 token（不落文本）：沿转写器树行走，
/// - 元变量捕获：按借用原样拼入（捕获 token 在匹配期就带调用点 span/path）；
/// - 模板字面量：span 改写为整个宏调用区间（调用点 path）——定义点 span
///   泄漏进报错文案是过去「直接拼接失败」的根因，按调用点改写即按构造
///   消除；下游消费 TokenNode 切片而非文本。
/// 语义与旧「`replace` 深拷贝 → 序列化 → 重词法 → span_map 回查」路径
/// 一致（Group 的逐迭代选表、BuiltIn 的 Str 化、EndLine 折叠/Eof 过滤），
/// 但免去捕获 token 的 String 深拷贝、整串序列化与二次词法。
fn splice_transcriber<'t>(
    trans: &'t MacroTranscriber,
    metavars: &[(&'t str, &'t [OwnedToken])],
    invocation_start: u32,
    invocation_end: u32,
    call_site_path: u32,
    out: &mut Vec<TokenNode<'t>>,
) -> Result<(), IError> {
    match trans {
        MacroTranscriber::Basic(toks) => {
            for tok in toks.iter() {
                if tok.data.1 == TokenKind::MacroIdent {
                    if let Some((_, cap)) = metavars.iter().find(|z| z.0 == tok.data.0) {
                        for t0 in cap.iter() {
                            splice_push(out, Span {
                                data: (t0.data.0.as_str(), t0.data.1),
                                start_offset: t0.start_offset,
                                end_offset: t0.end_offset,
                                path_id: t0.path_id,
                            });
                        }
                        continue;
                    }
                }
                splice_push(out, Span {
                    data: (tok.data.0.as_str(), tok.data.1),
                    start_offset: invocation_start,
                    end_offset: invocation_end,
                    path_id: call_site_path,
                });
            }
            Ok(())
        }
        MacroTranscriber::Sequence(parts) => {
            for p in parts.iter() {
                splice_transcriber(p, metavars, invocation_start, invocation_end, call_site_path, out)?;
            }
            Ok(())
        }
        MacroTranscriber::Group(x) => {
            let used = x.get_used_metavars();
            // 每个被引用的元变量名 → 该名下全部捕获（按 metavars 条目序）。
            let vars: Vec<(&'t str, Vec<&'t [OwnedToken]>)> = metavars.iter()
                .filter(|(name, _)| used.contains(*name))
                .map(|(name, toks)| (*name, vec![*toks]))
                .collect();
            let loop_num = vars.iter().map(|v| v.1.len()).max().unwrap_or(0);
            for i in 0..loop_num {
                let tables: Result<Vec<(&'t str, &'t [OwnedToken])>, IError> = vars.iter()
                    .map(|(name, slices)| {
                        if slices.len() == 1 {
                            Ok((*name, slices[0]))
                        } else if slices.len() == loop_num {
                            Ok((*name, slices[i]))
                        } else {
                            Err(IError { msg: empty_span(ErrMsg::Base(BaseMsg::Expect(TokenKind::RParen))) })
                        }
                    })
                    .collect();
                splice_transcriber(x, &tables?, invocation_start, invocation_end, call_site_path, out)?;
            }
            Ok(())
        }
        MacroTranscriber::BuiltIn => {
            for (_, toks) in metavars.iter() {
                for t0 in toks.iter() {
                    splice_push(out, Span {
                        data: (t0.data.0.as_str(), TokenKind::Str),
                        start_offset: t0.start_offset,
                        end_offset: t0.end_offset,
                        path_id: t0.path_id,
                    });
                }
            }
            Ok(())
        }
    }
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
        move |input, state: &mut MacroState| {
            // 先试第一个 item：失败时**保留底层错误**（含失败 token 的真实
            // span），不再像 `many0_sep` 那样吞掉错误、再在包装层用"剩余输
            // 入首 token"伪装成 EmptyVec——后者会把语法错误定位到失败 decl
            // 的起点（review R6）。
            let (mut input, first) = self.parse(input, state)?;
            let mut result = vec![first];
            loop {
                let (after_sep, _) = match sep.parse(input, state) {
                    Ok(x) => x,
                    Err(_) => break,
                };
                match self.parse(after_sep, state) {
                    Ok((i, a)) => {
                        input = i;
                        result.push(a);
                    }
                    // 与 `many0_sep` 旧语义一致：分隔符已消费、下一个 item
                    // 失败即正常结束（尾随换行/空行等），不报错。
                    Err(_) => {
                        input = after_sep;
                        break;
                    }
                }
            }
            Ok((input, result))
        }
    }
}

/// 解析 decl 序列。decl 流必须吃完全部 token：残留 token（`;` / 垃圾
/// token 曾把后续 decl 静默截断）一律报错，并带**首个残余 token**的内容
/// 与偏移——`;` 结尾这类最常见错误不再无从定位。任何解析失败都折叠为
/// 整体 `Err("parse error")`（契约被 l12 blackbox 钉死）。
pub fn parser(input: &str, id: u32) -> Result<Vec<Decl>, String> {
    parser_with_span(input, id).map_err(|(msg, _)| msg)
}

/// 解析错误（P10 第二步）：文案 + 可选位置。
///
/// 文案与 [`parser`] 的契约**逐字节一致**（`"parse error"` / 残余 token 那条），
/// 只有位置是新增的：IError 的 span（失败 token 处）或残余 token 的 span。
pub type ParseError = (String, Option<Span<()>>);

fn span_of(s: &Span<ErrMsg>) -> Option<Span<()>> {
    // 0,0 是"无位置"哨兵（空输入 / lexer 失败）；有偏移才返回
    if s.start_offset == 0 && s.end_offset == 0 {
        None
    } else {
        Some(Span {
            data: (),
            start_offset: s.start_offset,
            end_offset: s.end_offset,
            path_id: s.path_id,
        })
    }
}

/// 带位置的解析入口：[`parser`] 的契约 + 错误位置（供 LSP/诊断消费）。
pub fn parser_with_span(input: &str, id: u32) -> Result<Vec<Decl>, ParseError> {
    match lex::lex(Span {
        data: input,
        start_offset: 0,
        end_offset: input.len() as u32,
        path_id: id,
    }) {
        Some((_, ret)) => {
            // macro_rules 状态：错误流 + 规则表（内置 stringify）+ 展开记录。
            let mut err_collect: MacroState = (vec![], Default::default(), vec![]);
            Rc::make_mut(&mut err_collect.1)
                .entry("stringify".to_owned())
                .or_insert_with(|| {
                    Rc::new(vec![MacroRule {
                        matcher: MacroMatcher::Metavar {
                            name: empty_span(SmolStr::new("")),
                            fragment: MacroFragment::Ident,
                        },
                        transcriber: MacroTranscriber::BuiltIn,
                        def_start_offset: None,
                        def_end_offset: None,
                        def_path_id: None,
                    }])
                });
            match p_top.many1_sep(kw(EndLine).many1()).parse(&ret, &mut err_collect) {
                Ok((rest, opts)) => {
                    let decls: Vec<Decl> = opts.into_iter().flatten().collect();
                    if rest.is_empty() {
                        Ok(decls)
                    } else {
                        let t = &rest[0];
                        Err((
                            format!(
                                "parse error: leftover token `{}` @ {},{}",
                                t.data.0, t.start_offset, t.end_offset
                            ),
                            Some(t.to_span()),
                        ))
                    }
                }
                Err(e) => {
                    let span = span_of(&e.msg)
                        .or_else(|| err_collect.0.first().and_then(|c| span_of(&c.msg)));
                    Err(("parse error".to_owned(), span))
                }
            }
        }
        None => Err(("parse error".to_owned(), None)),
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
    [:=] => { $crate::L12_canonical::parser::TokenKind::AssignEq };
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

/// 名字词法：与 string 同匹配，产出 Span<SmolStr>。
fn smolstr<'a: 'b, 'b>(
    p: TokenKind,
) -> impl Parser<&'b [TokenNode<'a>], Span<SmolStr>, MacroState, IError> {
    move |input: &'b [TokenNode<'a>], _: &mut MacroState| match input.first() {
        Some(x) => {
            if x.data.1 == p {
                input
                    .get(1..)
                    .map(|i| (i, x.map(|s| SmolStr::new(s.0))))
                    .ok_or_else(|| IError {
                        msg: x.map(|_| ErrMsg::Base(BaseMsg::Expect(p))),
                    })
            } else {
                Err(IError {
                    msg: x.map(|_| ErrMsg::Base(BaseMsg::Expect(p))),
                })
            }
        }
        _ => Err(IError {
            msg: empty_span(ErrMsg::Base(BaseMsg::Expect(p))),
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

/// [ p ]
fn square<'a: 'b, 'b, P, O>(p: P) -> impl Parser<&'b [TokenNode<'a>], O, MacroState, IError>
where
    P: Parser<&'b [TokenNode<'a>], O, MacroState, IError>,
{
    (kw(LSquare), kw(EndLine).option(), p, kw(EndLine).option(), kw(RSquare)).map(|c| c.2)
}

/// [ p ]（Cut 版：内层失败记入诊断流并回退，供隐式实参表的软恢复）
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
fn brace<'a: 'b, 'b, P, O>(p: P) -> impl Parser<&'b [TokenNode<'a>], O, MacroState, IError>
where
    P: Parser<&'b [TokenNode<'a>], O, MacroState, IError>,
{
    (
        kw(LCurly),
        kw(EndLine).option(),
        p,
        kw(EndLine).option(),
        kw(RCurly),
    )
        .map(|c| c.2)
}

fn p_atom1<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    smolstr(Ident)
        .map(Raw::Var)
        .or(Cut((kw(TypeKeyword), string(Num))).map(|(_, num)| Raw::U(
            num.and_then(|x| x.data.parse::<u32>().ok()).unwrap_or(0),
        )))
        .or(kw(ThisKeyword).map(|s| Raw::Var(s.map(|_| SmolStr::new("this")))))
        .or(kw(Hole).map(|_| Raw::Hole))
        .or(smolstr(Str).map(|x| Raw::LiteralIntro(x.map(|s| unescape(&s)))))
        .or(paren(p_raw))
        .parse(input, state)
}

fn p_atom<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    // L08 积类型：原子 + 左结合多段投影链（`p.x.y`）；L07 只允许单段。
    (p_atom1, (kw(T![.]), smolstr(Ident)).many0())
        .map(|(x, t)| t.into_iter().fold(x, |acc, (_, f)| Raw::Obj(Box::new(acc), f)))
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

fn p_arg<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Vec<(Either, Raw)>> {
    // 方括号内逗号分隔的隐式实参表：`f[A, B]` ≡ `f[A][B]`（L11 起同款，2026-09-19 回移植）
    let named_impl_arg = square_cut(
        (smolstr(Ident), Cut((kw(Eq), p_raw))).map(|(x, t)| (Either::Name(x), t.1.unwrap_or(Raw::Hole)))
            .or(p_raw.map(|t| (Either::Icit(Icit::Impl), t)))
            .many0_sep(kw(T![,]))
    ).map(|x| x.ok().unwrap_or_default());

    let explicit_arg = p_atom.map(|t| vec![(Either::Icit(Icit::Expl), t)]);

    let arg_parser = named_impl_arg.or(explicit_arg);

    arg_parser.parse(input, state)
}

fn p_spine<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    let (input, head) = p_atom(input, state)?;
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
    let implicit_binder = square(p_bind).map(|x| (x, Either::Icit(Icit::Impl)));
    let named_binder =
        square((smolstr(Ident), kw(Eq), p_bind)).map(|(x, _, y)| (y, Either::Name(x)));

    explicit_binder
        .or(implicit_binder)
        .or(named_binder)
        .parse(input, state)
}

fn p_lam<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
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
    state: &mut MacroState,
) -> IResult<'a, 'b, Vec<(Span<SmolStr>, Raw, Icit)>> {
    square(
        (
            p_bind,
            (kw(Colon), p_raw).option().map(|x| match x {
                Some((_, x)) => x,
                None => Raw::Hole,
            }),
        )
            .map(|(xs, a)| (xs, a, Icit::Impl))
            .many0_sep(kw(T![,])),
    )
    .parse(input, state)
}

fn p_pi_binder<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut MacroState,
) -> IResult<'a, 'b, Vec<(Span<SmolStr>, Raw, Icit)>> {
    // 解析显式参数 (x : A)
    let explicit_binder = paren(
        (
            p_bind,
            kw(Colon).with(p_raw),
        )
            .map(|(xs, a)| (xs, a.1, Icit::Expl))
            .many0_sep(kw(T![,])),
    );

    p_pi_impl_binder.or(explicit_binder).parse(input, state)
}

fn p_pi<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
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
    (
        kw(LetKeyword),
        smolstr(Ident),
        (kw(Colon), p_raw).map(|(_, x)| x).option(),
        kw(Eq),
        p_raw,
        kw(Semi),
        kw(EndLine).option(),
        p_raw,
    )
        .map(|(_, binder, ann, _, val, _, _, body)| {
            Raw::Let(
                binder,
                Box::new(ann.unwrap_or(Raw::Hole)),
                Box::new(val),
                Box::new(body),
            )
        })
        .parse(input, state)
}

fn p_pattern<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Pattern> {
    (
        // struct 模式糖（与 L11/L12/L13 同款）：`Wrap { p1, p2 }` 脱糖成单构造子
        // enum 的 `Wrap.mk(p1, p2)` 模式。struct 在解析期就展开成单 case enum
        // （case 名即 `Name.mk`），所以这里只需在名字上补 `.mk` 后缀。
        smolstr(Ident),
        brace(p_pattern.many1_sep(kw(T![,]))),
    )
        .map(|(x, t)| Pattern::Con(x.map(|t| SmolStr::new(format!("{t}.mk"))), t, Icit::Expl))
        .or((
            smolstr(Ident),
            paren(p_pattern.many0_sep(kw(T![,])))
                .or(square(p_pattern.map(|x| x.to_impl()).many0_sep(kw(T![,]))))
                .many0()
                .map(|x| x.concat()),
        )
            .map(|(x, t)| Pattern::Con(x, t, Icit::Expl)))
        .or(kw(T![_]).map(|x| Pattern::Any(x, Icit::Expl)))
        .parse(input, state)
}

fn p_match<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    (
        kw(MatchKeyword),
        p_raw,
        brace(
            (kw(CaseKeyword), p_pattern, kw(T![=>]), kw(EndLine).option(), p_raw)
                .map(|(_, pattern, _, _, body)| (pattern, body))
                // 臂间允许连续空行：注释行经 preprocess 剥成空白后仍产生
                // EndLine，单 EndLine 分隔会把「臂间注释」打成语法错误
                .many0_sep(kw(EndLine).many1()),
        ),
    )
        .map(|(_, scrutinee, body)| Raw::Match(Box::new(scrutinee), body))
        .parse(input, state)
}

/// `new Name(a, b, ...)` —— L08 积类型构造语法糖：脱糖成限定构造子
/// `Name.mk` 的显式应用（`struct` 注册的构造子名就是 `{Name}.mk`）。
/// 结果可直接接 `.field` 投影后缀链（与原子同等待遇）；裸 spine 实参位
/// 仍不接 `new`（p_arg 不动）。
fn p_new<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    (
        kw(NewKeyword),
        smolstr(Ident),
        paren(p_raw.many0_sep(kw(T![,]))),
        (kw(T![.]), smolstr(Ident)).many0(),
    )
        .map(|(_, name, args, suffixes)| {
            let head = args.into_iter().fold(
                Raw::Var(name.map(|x| SmolStr::new(format!("{x}.mk")))),
                |acc, x| Raw::App(Box::new(acc), Box::new(x), Either::Icit(Icit::Expl)),
            );
            suffixes
                .into_iter()
                .fold(head, |acc, (_, f)| Raw::Obj(Box::new(acc), f))
        })
        .parse(input, state)
}

fn p_raw<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
    if let Some(macro_decl) = input.first().and_then(|x| state.1.get(x.data.0).cloned()) {
        for m in macro_decl.iter() {
            if let Ok((i, t)) = m.matcher.to_parser().parse(input.get(1..).unwrap(), state) {
                let invocation_start = input[0].start_offset;
                let invocation_end = if input.len() > i.len() { input[input.len() - i.len() - 1].end_offset } else { input[0].end_offset };
                let call_site_path = input[0].path_id;
                // 直接拼接展开 token（不再「序列化成串 → 整串重词法 →
                // span_map 回查」）：元变量捕获在匹配期就带调用点 span，按
                // 借用原样拼入；模板字面量的 span 改写为整个宏调用区间。
                // 过去直接拼接失败的根因是定义点 span 泄漏进报错文案——
                // span 按调用点改写即按构造消除；下游消费 TokenNode 切片
                // 而非文本。
                let captures: Vec<(&str, &[OwnedToken])> =
                    t.iter().map(|(name, toks)| (name.as_str(), toks.as_slice())).collect();
                let mut t_borrowed: Vec<TokenNode> = Vec::new();
                splice_transcriber(&m.transcriber, &captures, invocation_start, invocation_end, call_site_path, &mut t_borrowed)?;
                // Record macro expansion info（expanded_text 只服务 LSP
                // 记录，从拼接好的 token 借用序列化，单次分配、零深拷贝）。
                {
                    let consumed = input.len() - i.len();
                    let start = input[0].start_offset;
                    let end = if consumed > 0 { input[consumed - 1].end_offset } else { input[0].end_offset };
                    state.2.push(MacroExpansionInfo {
                        name: input[0].data.0.to_string(),
                        start_offset: start,
                        end_offset: end,
                        expanded_text: borrowed_tokens_to_string(&t_borrowed),
                        name_token_is_macro: true,
                        def_start_offset: m.def_start_offset,
                        def_end_offset: m.def_end_offset,
                        def_path_id: m.def_path_id,
                    });
                }
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
    p_raw_plain(input, state)
}

fn p_raw_plain<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Raw> {
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
    (
        kw(DefKeyword),
        smolstr(Ident),
        p_pi_binder
            .many0()
            .map(|x| x.into_iter().flatten().collect::<Vec<_>>()),
        (kw(T![:]), p_raw).map(|(_, x)| x).option(),
        kw(T![=]),
        kw(EndLine).option(),
        p_raw,
    )
        .map(|(_, name, params, ret, _, _, body)| Decl::Def {
            name,
            params,
            ret_type: ret.unwrap_or(Raw::Hole),
            body,
        })
        .parse(input, state)
}

fn p_print<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
    (kw(PrintlnKeyword), p_raw)
        .map(|(_, x)| Decl::Println(x))
        .parse(input, state)
}

fn p_enum<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
    (
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
                (kw(T![->]), p_raw).option().map(|x| x.map(|y| y.1)),
            )
                // case 间允许连续空行：注释行经 preprocess 剥成空白后仍产生
                // EndLine，单 EndLine 分隔会把「case 间注释」打成语法错误
                // （同 match 臂；L08 p_enum 同款，回合对齐）
                .many1_sep(kw(EndLine).many1()),
        ),
    )
        .map(|(_, name, params, fields)| Decl::Enum {
            name,
            params,
            cases: fields,
        })
        .parse(input, state)
}

/// `struct Name[A: U, ...] { field: Type ... }` —— L08 积类型语法糖：脱糖成
/// **单构造子 enum**，构造子名为 `{Name}.mk`，字段全部显式（Expl），参数走
/// 隐式方括号组（`[A]` / `[A: U]`）。字段可依赖参数与在前字段（依赖积 /
/// Sigma）。构造用 `new Name(e1, e2)` 或限定名 `Name.mk`；字段访问 `p.field`
/// 走 enum 投影（值级）与 `.mk` 构造子类型链剥层（类型级，见 elaboration）。
fn p_struct<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
    (
        kw(StructKeyword),
        smolstr(Ident),
        p_pi_impl_binder.option().map(|x| x.unwrap_or_default()),
        brace(
            (smolstr(Ident), kw(T![:]), p_raw)
                .map(|(name, _, ty)| (name, ty))
                // 字段按行分隔、无逗号；连续空行也容忍（注释行经 preprocess
                // 剥成空白后仍产生 EndLine，单 EndLine 分隔会把「字段间注释」
                // 打成语法错误）。
                .many0_sep(kw(EndLine).many1()),
        ),
    )
        .map(|(_, name, params, fields)| Decl::Enum {
            name: name.clone(),
            params,
            cases: vec![(
                name.map(|x| SmolStr::new(format!("{x}.mk"))),
                fields.into_iter().map(|(n, ty)| (n, ty, Icit::Expl)).collect(),
                None,
            )],
        })
        .parse(input, state)
}

/// `[p]` 隐式 binder 组（可缺省）：trait/impl 头部参数用。
fn p_pi_impl_binder_option<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut MacroState,
) -> IResult<'a, 'b, Vec<(Span<SmolStr>, Raw, Icit)>> {
    p_pi_impl_binder
        .option()
        .map(|x| x.unwrap_or_default())
        .parse(input, state)
}

/// trait 声明：`trait Name[params] { def m(x: A): B  ... }`（方法只有签名）。
fn p_trait_def<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
    let p_def_declare = (
        kw(DefKeyword),
        smolstr(Ident),
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
        .map(|(_, name, params, methods)| Decl::TraitDecl {
            name,
            params,
            methods,
        })
        .parse(input, state)
}

/// impl 声明：`impl Trait for T { ... }`（need_create=false）或
/// inherent `impl T { ... }`（need_create=true，先补建同名合成 trait）。
fn p_impl<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
    let for_form = (
        kw(ImplKeyword),
        p_pi_impl_binder_option,
        smolstr(Ident),
        square_cut(p_raw.many0_sep(kw(T![,])))
            .option()
            .map(|x| x.and_then(|r| r.ok()).unwrap_or_default()),
        kw(ForKeyword),
        p_raw,
        brace(p_def.many0_sep(kw(EndLine))),
    )
        .map(|(_, params, trait_name, trait_params, _, name, methods)| Decl::ImplDecl {
            name,
            params,
            trait_name,
            trait_params,
            methods,
            need_create: false,
        });
    let inherent = (
        kw(ImplKeyword),
        p_pi_impl_binder_option,
        p_raw,
        brace(p_def.many0_sep(kw(EndLine))),
    )
        .map(|(kw, params, name, methods)| {
            let synth = match &name {
                Raw::Var(n) => format!("$inherent${}", n.data),
                _ => "$inherent".to_string(),
            };
            Decl::ImplDecl {
                name,
                trait_params: params
                    .iter()
                    .map(|x| Raw::Var(x.0.clone()))
                    .collect(),
                params,
                trait_name: kw.map(|_| SmolStr::new(&synth)),
                methods,
                need_create: true,
            }
        });
    for_form.or(inherent).parse(input, state)
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
    smolstr(Ident).parse(input, state).map(|(input, span)| {
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
        smolstr(MacroIdent),
        kw(Colon),
        parse_fragment_kind
    ).map(|(name, _, fragment)| {
        MacroMatcher::Metavar { name, fragment }
    });
    
    // 尝试解析分组 $(...)* / $(...)+ / $(...)? — balanced-paren aware
    // (p_macro_group_matcher)，序列内可含字面 ( ) token。

    // 尝试解析普通 token
    let token_parser = smolstr(Ident)
        .map(|span| {
            MacroMatcher::Token(Ident, span)
        })
        .or(smolstr(Op).map(|span| {
            MacroMatcher::Token(Op, span)
        }))
        .or(smolstr(Num).map(|span| {
            MacroMatcher::Token(Num, span)
        }))
        .or(smolstr(LSquare).map(|span| {
            MacroMatcher::Token(LSquare, span)
        }))
        .or(smolstr(RSquare).map(|span| {
            MacroMatcher::Token(RSquare, span)
        }))
        .or(smolstr(LCurly).map(|span| {
            MacroMatcher::Token(LCurly, span)
        }))
        .or(smolstr(RCurly).map(|span| {
            MacroMatcher::Token(RCurly, span)
        }))
        .or(smolstr(LetKeyword).map(|span| MacroMatcher::Token(LetKeyword, span)))
        .or(smolstr(ForKeyword).map(|span| MacroMatcher::Token(ForKeyword, span)))
        .or(smolstr(Eq).map(|span| MacroMatcher::Token(Eq, span)))
        .or(smolstr(Dot).map(|span| MacroMatcher::Token(Dot, span)))
        .or(smolstr(Hole).map(|span| MacroMatcher::Token(Hole, span)))
        .or(smolstr(Colon).map(|span| MacroMatcher::Token(Colon, span)))
        // Verilog-compat layer: patterns for `module (...)`, `always @(...)`,
        // `q <= d ;`, `.a(x), .b(y)` need these as literal tokens. The
        // matcher itself (MacroMatcher::Token) has always been generic over
        // (kind, text); only the pattern-side parser was limited. Additive —
        // existing macro patterns never contain these tokens.
        .or(smolstr(LParen).map(|span| MacroMatcher::Token(LParen, span)))
        .or(smolstr(RParen).map(|span| MacroMatcher::Token(RParen, span)))
        .or(smolstr(Semi).map(|span| MacroMatcher::Token(Semi, span)))
        .or(smolstr(Comma).map(|span| MacroMatcher::Token(Comma, span)))
        .or(smolstr(CaseKeyword).map(|span| MacroMatcher::Token(CaseKeyword, span)))
        .or(smolstr(MatchKeyword).map(|span| MacroMatcher::Token(MatchKeyword, span)));
    
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
        smolstr(Ident),  // 宏名称
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
                    Rc::make_mut(&mut state.1).insert(format!("__exported__{}", name.data), Rc::new(Vec::new()));
                }
                // Stamp the definition span (the `macro_rules <name>` name
                // token) onto every rule so use sites can resolve
                // goto-definition back to this declaration.
                let rules: Vec<MacroRule> = rules
                    .unwrap_or_default()
                    .into_iter()
                    .map(|rule| MacroRule {
                        def_start_offset: Some(name.start_offset),
                        def_end_offset: Some(name.end_offset),
                        def_path_id: Some(name.path_id),
                        ..rule
                    })
                    .collect();
                Rc::make_mut(&mut state.1).insert(name.data.to_string(), Rc::new(rules));
            }
            Ok((input, ()))
        },
        Err(e) => Err(e),
    }
}

fn p_decl<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
    if let Some(macro_decl) = input.first().and_then(|x| state.1.get(x.data.0).cloned()) {
        let is_cut = macro_decl.len() == 1;
        for m in macro_decl.iter() {
            let (i, t) = if is_cut {
                match m.matcher.to_parser().parse(input.get(1..).unwrap(), state) {
                    Ok(x) => x,
                    Err(e) => {
                        state.0.push(e);
                        return Ok((input.get(1..).unwrap_or(&[]), Decl::Println(Raw::Hole)))
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
                        return Ok((i, Decl::Println(Raw::Hole)))
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
                        return Ok((i, Decl::Println(Raw::Hole)))
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
    p_decl_plain(input, state)
}

/// 顶层：macro_rules 声明在解析期登记（不产出 Decl），其余走 p_decl。
fn p_top<'a: 'b, 'b>(
    input: &'b [TokenNode<'a>],
    state: &mut MacroState,
) -> IResult<'a, 'b, Option<Decl>> {
    p_macro_def
        .map(|_| None::<Decl>)
        .or(p_decl.map(Some))
        .parse(input, state)
}

fn p_decl_plain<'a: 'b, 'b>(input: &'b [TokenNode<'a>], state: &mut MacroState) -> IResult<'a, 'b, Decl> {
    // 错误原样透传：外层按契约折叠为整体 `parse error`（Custom 文案不外泄）。
    // `or_far`（而非 `or`）保留最远失败分支的错误位置——否则 `p_enum` 在
    // `def` 首 token 的期望错误会覆盖 `p_def` 在真正失败 token（如 `)`）处
    // 的错误（review R6）。
    p_def
        .or_far(p_print)
        .or_far(p_enum)
        .or_far(p_struct)
        .or_far(p_trait_def)
        .or_far(p_impl)
        .parse(input, state)
}

#[test]
fn test_ok() {
    let input = r#"
enum Nat {
    zero
    succ(x: Nat)
}

def two = succ succ zero

def add(x: Nat, y: Nat): Nat =
    match x {
        case zero => y
        case succ(n) => succ add n y
    }

println add two two
"#;
    let decls = parser(input, 0).unwrap();
    assert!(!decls.is_empty());
}

#[test]
fn test_leftover_located() {
    // `;` 结尾 / 垃圾 token 报错带定位（同 l12 blackbox 契约）。
    let input = "enum Nat {\n    zero\n}\nprintln zero;\n";
    let err = parser(input, 0).unwrap_err();
    assert!(err.contains("parse error"), "err: {err}");
    assert!(err.contains("`;`"), "err should locate the token: {err}");
}

#[test]
fn test_whole_file_fail() {
    // 坏 decl 折叠为整体 `parse error`（契约被 blackbox 钉死）。
    let input = "enum Void {\n}\n";
    assert_eq!(parser(input, 0).unwrap_err(), "parse error");
}