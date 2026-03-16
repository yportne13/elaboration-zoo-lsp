use crate::parser_lib::Span;

use super::lex::TokenKind;


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
    Sequence(&'b [Span<(&'a str, TokenKind)>])
}

#[derive(Clone, Debug)]
pub struct MacroRule<'a: 'b, 'b> {
    pub matcher: MacroMatcher,   // 匹配模式
    pub transcriber: MacroTranscriber<'a, 'b>,  // 展开模板
}
