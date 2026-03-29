use crate::parser_lib::ToSpan;
use crate::{parser_lib::Span, parser_lib_resilient::Parser};

use super::lex::TokenKind;
use super::{TokenNode, IError, HashMap, ErrMsg, string, p_raw, p_pi_binder, empty_span, ParserExt, kw};

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
    pub fn to_parser<'a: 'b, 'b>(&self) -> impl Parser<&'b [TokenNode<'a>], Vec<(String, Vec<TokenNode<'a>>)>, (Vec<IError>, HashMap<String, Vec<MacroRule<'a, 'b>>>), IError> {
        move |input: &'b [TokenNode<'a>], state: &mut (Vec<IError>, HashMap<String, Vec<MacroRule<'a, 'b>>>)| {
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
                                    msg: token.map(|x| ErrMsg::Expect(*kind)),
                                })
                            }
                        }
                        None => {
                            Err(IError {
                                msg: empty_span(ErrMsg::Expect(*kind)),
                            })
                        }
                    }
                }
                MacroMatcher::Metavar { name, fragment } => {
                    match fragment {
                        MacroFragment::Ident => string(TokenKind::Ident).parse(input, state)
                            .map(|(i, _)| (i, vec![(name.data.clone(), input.get(0..1).unwrap().to_vec())])),
                        MacroFragment::Raw => p_raw(input, state)
                            .map(|(i, _)| (i, vec![(name.data.clone(), input.get(0..(input.len() - i.len())).unwrap().to_vec())])),
                        MacroFragment::Param => p_pi_binder.many1().parse(input, state)
                            .map(|(i, _)| (i, vec![(name.data.clone(), input.get(0..(input.len() - i.len())).unwrap().to_vec())])),
                        MacroFragment::Name(mname) => state.1.get(&mname.data).cloned().and_then(|x| x.iter()
                            .flat_map(|m| {
                                m.matcher.to_parser().parse(input, state)
                                    .and_then(|(i, t)| {
                                        let t = m.transcriber.replace(t)?;
                                        Ok((i, vec![(name.data.clone(), t)]))
                                    })
                            }).next()).ok_or(IError {
                                msg: name.to_span().map(|_| ErrMsg::Expect(TokenKind::RParen)),//TODO: err msg
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
                MacroMatcher::Many0(m) => m.to_parser()
                    .many0_sep(kw(TokenKind::EndLine).option())
                    .map(|x| x.concat())
                    .parse(input, state),
                MacroMatcher::Many1(m) => m.to_parser()
                    .many1_sep(kw(TokenKind::EndLine).option())
                    .map(|x| x.concat())
                    .parse(input, state),
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
pub enum MacroTranscriber<'a: 'b, 'b> {
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
    Group(Box<MacroTranscriber<'a, 'b>>),
    Basic(&'b [Span<(&'a str, TokenKind)>]),
    Sequence(Vec<MacroTranscriber<'a, 'b>>),
    BuiltIn,//TODO: more builtin
}

impl<'a: 'b, 'b> MacroTranscriber<'a, 'b> {
    pub fn replace(&self, metavars: Vec<(String, Vec<TokenNode<'a>>)>) -> Result<Vec<Span<(&'a str, TokenKind)>>, IError> {
        match self {
            MacroTranscriber::Basic(x) => {
                let mut ret = vec![];
                for x in x.iter() {
                    if x.data.1 == TokenKind::MacroIdent {
                        if let Some(y) = metavars.iter().find(|z| z.0 == x.data.0) {
                            ret.extend(y.1.clone());
                        } else {
                            ret.push(*x);
                        }
                    } else {
                        ret.push(*x);
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
                            Err(IError { msg: empty_span(ErrMsg::Expect(TokenKind::RParen)) })//TODO: err msg
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    ret.extend(x.replace(tables)?)
                }
                Ok(ret)
            },
            MacroTranscriber::BuiltIn => {
                Ok(metavars.into_iter()
                    .flat_map(|x| x.1.into_iter())
                    .map(|z| z.map(|(s, _)| (s, TokenKind::Str)))
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
pub struct MacroRule<'a: 'b, 'b> {
    pub matcher: MacroMatcher,   // 匹配模式
    pub transcriber: MacroTranscriber<'a, 'b>,  // 展开模板
}
