use crate::{parser_lib::Span, parser_lib_resilient::Parser};

use super::lex::TokenKind;
use super::{TokenNode, IError, HashMap, ErrMsg, string, p_raw, p_pi_binder, empty_span, ParserExt};

#[derive(Clone, Debug)]
pub enum TokenTree {
    Token(Span<(String, TokenKind)>),  // 单个 token
    Group(Delimiter, Vec<TokenTree>),  // (...) [...] {...}
}

#[derive(Clone, Copy, Debug)]
pub enum Delimiter {
    Parenthesis,  // ()
    Bracket,      // []
    Brace,        // {}
    None,         // 无分隔符（用于序列）
}

#[derive(Clone, Debug)]
pub enum MacroMatcher {
    // 普通 token 匹配
    Token(TokenKind, Span<String>),
    // 变量捕获：$name:fragment
    Metavar {
        name: Span<String>,
        fragment: MacroFragment,
    },
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
    pub fn to_parser<'a: 'b, 'b>(&self) -> impl Parser<&'b [TokenNode<'a>], Vec<(String, &'b [TokenNode<'a>])>, (Vec<IError>, HashMap<String, Vec<MacroRule<'a, 'b>>>), IError> {
        move |input: &'b [TokenNode<'a>], state: &mut (Vec<IError>, HashMap<String, Vec<MacroRule<'a, 'b>>>)| {
            match self {
                MacroMatcher::Token(kind, span) => {
                    match input.first() {
                        Some(token) => {
                            if token.data.1 == *kind && token.data.0 == span.data {
                                Ok((input.get(1..).unwrap(), vec![]))
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
                            .map(|(i, _)| (i, vec![(name.data.clone(), input.get(0..1).unwrap())])),
                        MacroFragment::Raw => p_raw(input, state)
                            .map(|(i, _)| (i, vec![(name.data.clone(), input.get(0..(input.len() - i.len())).unwrap())])),
                        MacroFragment::Param => p_pi_binder.many1().parse(input, state)
                            .map(|(i, _)| (i, vec![(name.data.clone(), input.get(0..(input.len() - i.len())).unwrap())])),
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
    Sequence(&'b [Span<(&'a str, TokenKind)>]),
    BuiltIn,//TODO: more builtin
}

impl<'a: 'b, 'b> MacroTranscriber<'a, 'b> {
    pub fn replace(&self, metavars: Vec<(String, &'b [TokenNode<'a>])>) -> Vec<Span<(&'a str, TokenKind)>> {
        match self {
            MacroTranscriber::Sequence(x) => {
                let mut ret = vec![];
                for x in x.iter() {
                    if x.data.1 == TokenKind::MacroIdent {
                        if let Some(y) = metavars.iter().find(|z| z.0 == x.data.0) {
                            ret.extend(y.1);
                        } else {
                            ret.push(*x);
                        }
                    } else {
                        ret.push(*x);
                    }
                }
                //TODO:truncate head endline and tail endline
                ret
            },
            MacroTranscriber::BuiltIn => {
                metavars.into_iter()
                    .flat_map(|x| x.1.iter())
                    .map(|z| z.map(|(s, _)| (s, TokenKind::Str)))
                    .collect()
            },
        }
    }
}

#[derive(Clone, Debug)]
pub struct MacroRule<'a: 'b, 'b> {
    pub matcher: MacroMatcher,   // 匹配模式
    pub transcriber: MacroTranscriber<'a, 'b>,  // 展开模板
}
