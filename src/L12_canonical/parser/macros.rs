use crate::parser_lib::ToSpan;
use crate::{parser_lib::Span, parser_lib_resilient::Parser};

use super::lex::TokenKind;
use super::{TokenNode, IError, HashMap, ErrMsg, BaseMsg, extract_base, string, p_raw, p_pi_binder, empty_span, owned_tokens_to_string, ParserExt, kw, MacroState, MacroExpansionInfo};

pub type OwnedToken = Span<(String, TokenKind)>;
pub type OwnedTokenSlice = [Span<(String, TokenKind)>];

#[derive(Clone, Debug)]
pub enum MacroMatcher {
    // 普通 token 匹配
    Token(TokenKind, Span<String>),
    // 变量捕获：$name:fragment
    Metavar {
        name: Span<String>,
        fragment: MacroFragment,
    },
    Many0(Box<MacroMatcher>),
    Many1(Box<MacroMatcher>),
    // 可选匹配：$(...)? — attempts the inner matcher; on failure consumes nothing.
    Optional(Box<MacroMatcher>),
    // 重复匹配：$(...)* $(...)+ $(...)?
    /*Repetition {
        inner: Box<MacroMatcher>,
        separator: Option<TokenKind>,  // 如逗号
        op: RepetitionOp,  // *, +, ?
    },
    // 分组：(...) [...] {...}
    Group(Delimiter, Vec<MacroMatcher>),*/
    // 序列
    Sequence(Vec<MacroMatcher>),
}

impl MacroMatcher {
    pub fn to_parser<'a: 'b, 'b>(&self) -> impl Parser<&'b [TokenNode<'a>], Vec<(String, Vec<OwnedToken>)>, MacroState, IError> {
        move |input: &'b [TokenNode<'a>], state: &mut MacroState| {
            match self {
                MacroMatcher::Token(kind, span) => {
                    match input.first() {
                        Some(token) => {
                            if token.data.1 == *kind && token.data.0 == span.data {
                                kw(TokenKind::EndLine).option()
                                    .map(|_| vec![])
                                    .parse(input.get(1..).unwrap(), state)
                            } else {
                                Err(IError {
                                    msg: token.map(|x| ErrMsg::Base(BaseMsg::Expect(*kind))),
                                })
                            }
                        }
                        None => {
                            Err(IError {
                                msg: empty_span(ErrMsg::Base(BaseMsg::Expect(*kind))),
                            })
                        }
                    }
                }
                MacroMatcher::Metavar { name, fragment } => {
                    match fragment {
                        MacroFragment::Ident => string(TokenKind::Ident).parse(input, state)
                            .map(|(i, _)| (i, vec![(name.data.clone(), input.get(0..1).unwrap().iter().map(|t| Span {
                                data: (t.data.0.to_owned(), t.data.1),
                                start_offset: t.start_offset,
                                end_offset: t.end_offset,
                                path_id: t.path_id,
                            }).collect())])),
                        MacroFragment::Raw => p_raw(input, state)
                            .map(|(i, _)| (i, vec![(name.data.clone(), input.get(0..(input.len() - i.len())).unwrap().iter().map(|t| Span {
                                data: (t.data.0.to_owned(), t.data.1),
                                start_offset: t.start_offset,
                                end_offset: t.end_offset,
                                path_id: t.path_id,
                            }).collect())])),
                        MacroFragment::Param => p_pi_binder.many1().parse(input, state)
                            .map(|(i, _)| (i, vec![(name.data.clone(), input.get(0..(input.len() - i.len())).unwrap().iter().map(|t| Span {
                                data: (t.data.0.to_owned(), t.data.1),
                                start_offset: t.start_offset,
                                end_offset: t.end_offset,
                                path_id: t.path_id,
                            }).collect())])),
                        MacroFragment::Name(mname) => state.1.get(&mname.data).cloned().and_then(|x| x.iter()
                            .flat_map(|m| {
                                m.matcher.to_parser().parse(input, state)
                                    .and_then(|(i, t)| {
                                        let t = m.transcriber.replace(t)?;
                                        // Record the expansion for LSP
                                        // goto-definition. A call like `when
                                        // ...` inside a module body is handled
                                        // by the `Expr` fragment (which
                                        // expands through the Expr macro's
                                        // rules), so prefer the definition of
                                        // a macro whose name matches the
                                        // call-site token (`when`), falling
                                        // back to the rule that actually
                                        // matched (`Expr`).
                                        if let Some(first) = input.first() {
                                            let (def_start, def_end, def_path) = state.1.get(first.data.0)
                                                .and_then(|r| r.first())
                                                .map(|r| (r.def_start_offset, r.def_end_offset, r.def_path_id))
                                                .unwrap_or((m.def_start_offset, m.def_end_offset, m.def_path_id));
                                            let consumed = input.len() - i.len();
                                            let start = first.start_offset;
                                            let end = if consumed > 0 { input[consumed - 1].end_offset } else { first.end_offset };
                                            state.2.push(MacroExpansionInfo {
                                                name: first.data.0.to_string(),
                                                start_offset: start,
                                                end_offset: end,
                                                expanded_text: owned_tokens_to_string(&t),
                                                // The `name` is only the macro NAME token when the
                                                // first call-site token itself starts a nested macro
                                                // call (e.g. `when` inside a module body). For a plain
                                                // Expr statement (`sum := a +^ b`) the first token is
                                                // user code, not a macro name.
                                                name_token_is_macro: state.1.contains_key(first.data.0),
                                                def_start_offset: def_start,
                                                def_end_offset: def_end,
                                                def_path_id: def_path,
                                            });
                                        }
                                        Ok((i, vec![(name.data.clone(), t)]))
                                    })
                            }).next()).ok_or(IError {
                                msg: name.to_span().map(|_| ErrMsg::Base(BaseMsg::Expect(TokenKind::RParen))),//TODO: err msg
                            })
                    }
                },
                MacroMatcher::Sequence(macro_matchers) => {
                    let mut input = input;
                    let mut ret = vec![];
                    for x in  macro_matchers {
                        match x.to_parser().parse(input, state) {
                            Ok((i, t)) => {
                                input = i;
                                ret.extend(t);
                            },
                            Err(e) => return Err(e),
                        }
                    }
                    Ok((input, ret))
                },
                MacroMatcher::Many0(m) => {
                    // Skip leading EndLine tokens (e.g., newline after {)
                    let (input, _) = kw(TokenKind::EndLine).many0().parse(input, state)?;
                    // Zero-consumption guard: a repetition unit that matches
                    // without consuming tokens (e.g. an all-optional binder
                    // on unexpected input) would loop forever in many0_sep.
                    let mut rest = input;
                    let mut acc = vec![];
                    loop {
                        match m.to_parser().parse(rest, state) {
                            Ok((i, t)) if i.len() < rest.len() => {
                                acc.extend(t);
                                if let Ok((i2, _)) = kw(TokenKind::EndLine).option().parse(i, state) {
                                    rest = i2;
                                } else {
                                    break;
                                }
                            }
                            _ => break,
                        }
                    }
                    Ok((rest, acc))
                },
                MacroMatcher::Many1(m) => {
                    // Skip leading EndLine tokens
                    let (input, _) = kw(TokenKind::EndLine).many0().parse(input, state)?;
                    let first = m.to_parser().parse(input, state);
                    match first {
                        Err(e) => Err(e),
                        Ok((i, t)) if i.len() == input.len() => Err(IError {
                            // zero-consumption first unit cannot satisfy many1
                            msg: input.first().map(|x| x.map(|_| ErrMsg::Base(BaseMsg::Expect(TokenKind::Ident)))).unwrap_or_else(|| empty_span(ErrMsg::Base(BaseMsg::Expect(TokenKind::Ident)))),
                        }),
                        Ok((i, mut t)) => {
                            let mut rest = i;
                            loop {
                                match m.to_parser().parse(rest, state) {
                                    Ok((i2, t2)) if i2.len() < rest.len() => {
                                        t.extend(t2);
                                        if let Ok((i3, _)) = kw(TokenKind::EndLine).option().parse(i2, state) {
                                            rest = i3;
                                        } else {
                                            break;
                                        }
                                    }
                                    _ => break,
                                }
                            }
                            Ok((rest, t))
                        }
                    }
                },
                MacroMatcher::Optional(m) => {
                    // Skip leading EndLine tokens, like Many0/Many1
                    let (input, _) = kw(TokenKind::EndLine).many0().parse(input, state)?;
                    match m.to_parser().parse(input, state) {
                        Ok((rest, captures)) => Ok((rest, captures)),
                        // Optional: on failure consume nothing.
                        Err(_) => Ok((input, vec![])),
                    }
                },
            }
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum RepetitionOp {
    ZeroOrMore,  // *
    OneOrMore,   // +
    Optional,    // ?
}

#[derive(Clone, Debug)]
pub enum MacroFragment {
    Ident,
    Raw,
    Param,
    Name(Span<String>),
    //Expr,      // 表达式
    //Ident,     // 标识符
    //Ty,        // 类型
    //Pat,       // 模式
    //Stmt,      // 语句
    //Item,      // 项
    //Block,     // 代码块
    //Tt,        // 单个 TokenTree
    //Meta,      // 元信息（类似属性）
    //Literal,   // 字面量
    //Path,      // 路径
    //Vis,       // 可见性
    //Lifetime,  // 生命周期
}

#[derive(Clone, Debug)]
pub enum MacroTranscriber {
    // 普通 token 输出
    /*Token(TokenKind, Option<String>),  // TokenKind + 原始文本
    // 引用元变量：$name
    MetavarRef(Span<String>),
    // 重复转写：$(...)* 等
    Repetition {
        inner: Box<MacroTranscriber>,
        separator: Option<TokenKind>,
        op: RepetitionOp,
        metavar: Span<String>,  // 控制重复的元变量
    },
    // 分组
    Group(Delimiter, Vec<MacroTranscriber>),
    // 序列
    Sequence(Vec<MacroTranscriber>),*/
    Group(Box<MacroTranscriber>),
    Basic(Vec<OwnedToken>),
    Sequence(Vec<MacroTranscriber>),
    BuiltIn,//TODO: more builtin
}

impl MacroTranscriber {
    /// Produce owned tokens from owned metavars.
    pub fn replace(&self, metavars: Vec<(String, Vec<OwnedToken>)>) -> Result<Vec<OwnedToken>, IError> {
        match self {
            MacroTranscriber::Basic(x) => {
                let mut ret = vec![];
                for tok in x.iter() {
                    if tok.data.1 == TokenKind::MacroIdent {
                        if let Some(y) = metavars.iter().find(|z| z.0 == tok.data.0) {
                            ret.extend(y.1.clone());
                        } else {
                            ret.push(tok.clone());
                        }
                    } else {
                        ret.push(tok.clone());
                    }
                }
                //TODO:truncate head endline and tail endline
                Ok(ret)
            },
            MacroTranscriber::Sequence(x) => {
                let mut ret = vec![];
                for x in x.iter() {
                    ret.extend(x.replace(metavars.clone())?);
                }
                Ok(ret)
            },
            MacroTranscriber::Group(x) => {
                let vars = x.get_used_metavars();
                let vars = vars.into_iter()
                    .map(|x| {
                        let t = metavars.iter().filter(|y| y.0 == x).collect::<Vec<_>>();
                        (x, t)
                    })
                    .collect::<std::collections::HashMap<_, _>>();
                let mut ret = vec![];
                let loop_num = vars.iter()
                    .map(|x| x.1.len())
                    .max()
                    .unwrap_or(0);
                for i in 0..loop_num { 
                    let tables = vars.iter()
                        .map(|x| if x.1.len() == 1 {
                            Ok(x.1[0].clone())
                        } else if x.1.len() == loop_num {
                            Ok(x.1[i].clone())
                        } else {
                            Err(IError { msg: empty_span(ErrMsg::Base(BaseMsg::Expect(TokenKind::RParen))) })//TODO: err msg
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    ret.extend(x.replace(tables)?)
                }
                Ok(ret)
            },
            MacroTranscriber::BuiltIn => {
                Ok(metavars.into_iter()
                    .flat_map(|x| x.1.into_iter())
                    .map(|mut z| {
                        z.data.1 = TokenKind::Str;
                        z
                    })
                    .collect())
            },
        }
    }
    fn get_used_metavars(&self) -> std::collections::HashSet<String> {
        match self {
            MacroTranscriber::Basic(x) => {
                x.iter()
                    .filter(|x| x.data.1 == TokenKind::MacroIdent)
                    .map(|x| x.data.0.to_owned())
                    .collect()
            },
            MacroTranscriber::Sequence(x) => {
                x.iter()
                    .flat_map(|x| x.get_used_metavars().into_iter())
                    .collect()
            },
            MacroTranscriber::Group(x) => {
                x.get_used_metavars()
            },
            MacroTranscriber::BuiltIn => {
                Default::default()
            },
        }
    }
}

#[derive(Clone, Debug)]
pub struct MacroRule {
    pub matcher: MacroMatcher,   // 匹配模式
    pub transcriber: MacroTranscriber,  // 展开模板
    /// Source location of the macro definition: byte offsets of the macro
    /// name token in the file where `macro_rules <name>` was declared, plus
    /// that file's path_id. All `None` for rules without a textual
    /// definition (built-in macros such as `stringify`).
    pub def_start_offset: Option<u32>,
    pub def_end_offset: Option<u32>,
    pub def_path_id: Option<u32>,
}
