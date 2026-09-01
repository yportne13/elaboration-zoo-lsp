use crate::parser_lib::*;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum TokenKind {
    LetKeyword,
    UKeyword, //Universe

    /// `_`：hole（atom 位置）或匿名 binder（binder 位置）
    Hole,
    LParen,
    RParen,
    /// `{`：隐式语法——`{x}`、`{x : A}`、`{x = e}`（binder/实参皆可）
    LCurly,
    /// `}`
    RCurly,
    Dot,
    Eq,
    /// ;
    Semi,
    /// :
    Colon,
    Arrow,
    Lambda,

    Ident,
    Num,
    Op,
    Str,

    ErrToken,

    Eof,
}

pub type Token<'a> = Span<(&'a str, TokenKind)>;

use TokenKind::*;

const KEYWORD: [(&str, TokenKind); 2] = [("let", LetKeyword), ("U", UKeyword)];

const OP: [(&str, TokenKind); 11] = [
    ("_", Hole),
    ("(", LParen),
    (")", RParen),
    ("{", LCurly),
    ("}", RCurly),
    (".", Dot),
    ("=", Eq),
    (";", Semi),
    (":", Colon),
    ("->", Arrow),
    ("\\", Lambda),
];

pub type TokenNode<'a> = Span<(&'a str, TokenKind)>;

fn ident(input: Span<&str>) -> Option<(Input<'_>, Token<'_>)> {
    // `;` 单独成 token（op 的字符区间盖住 ';'，须先切出来）
    if let Some((rest, semi)) = is(';').parse(input) {
        return Some((rest, semi.map(|t| (t, Semi))));
    }
    let (after_head, head) = pmatch(|c: char| c.is_alphabetic() || c == '_').parse(input)?;
    let (rest, ident_len) = match pmatch(|c: char| c.is_alphanumeric() || c == '_').parse(after_head) {
        Some((rest, tail)) => (rest, head.data.len() + tail.data.len()),
        None => (after_head, head.data.len()),
    };
    let ident = unsafe { input.data.get_unchecked(..ident_len) };

    // `λ` 在 main.hs 里是字符级匹配（pLam 的 `char 'λ'`），所以 `λx` 要拆成
    // Lambda + Ident("x")——ident 贪婪吞掉的 "λx" 在这里重新切分。
    if ident.starts_with('λ') {
        let n = 'λ'.len_utf8();
        let token = Span {
            data: (&input.data[..n], Lambda),
            start_offset: input.start_offset,
            end_offset: input.start_offset + n as u32,
            path_id: input.path_id,
        };
        let rest = Span {
            data: &input.data[n..],
            start_offset: input.start_offset + n as u32,
            end_offset: input.end_offset,
            path_id: input.path_id,
        };
        return Some((rest, token));
    }

    let kind = if let Some((_, k)) = KEYWORD.into_iter().find(|(k, _)| ident == *k) {
        k
    } else {
        Ident
    };
    Some((
        rest,
        Span {
            data: (ident, kind),
            start_offset: input.start_offset,
            end_offset: input.start_offset + ident_len as u32,
            path_id: input.path_id,
        },
    ))
}

fn brace(input: Span<&str>) -> Option<(Input<'_>, Token<'_>)> {
    let lparen = is('(').map(|x| x.map(|y| (y, LParen)));
    let rparen = is(')').map(|x| x.map(|y| (y, RParen)));
    let lcurly = is('{').map(|x| x.map(|y| (y, LCurly)));
    let rcurly = is('}').map(|x| x.map(|y| (y, RCurly)));
    lparen.or(rparen).or(lcurly).or(rcurly).parse(input)
}

fn op(input: Span<&str>) -> Option<(Input<'_>, Token<'_>)> {
    pmatch(|c: char| {
        ('!'..='\'').contains(&c)
            || ('*'..='/').contains(&c)
            || ((':'..='@').contains(&c) && c != ';')
            || c == '\\'
            || ('^'..='`').contains(&c)
            || c == '|'
            || c == '~'
    })
    .map(|x| {
        let token = if let Some((_, k)) = OP.into_iter().find(|(k, _)| x.data == *k) {
            k
        } else {
            Op
        };
        x.map(move |y| (y, token))
    })
    .parse(input)
}

/// 在 Span 前进 n 个字节（调用方保证 n ≤ data.len()）。
fn advance(input: Span<&str>, n: usize) -> Span<&str> {
    Span {
        data: &input.data[n..],
        start_offset: input.start_offset + n as u32,
        end_offset: input.end_offset,
        path_id: input.path_id,
    }
}

/// 空白与注释（同 L03 的 `ws`：行注释 `--`、块注释 `{- -}`）。
fn skip_trivia(mut input: Span<&str>) -> Span<&str> {
    loop {
        let start_len = input.data.len();
        let rest = input.data.trim_start_matches(|c: char| c.is_whitespace());
        input = advance(input, start_len - rest.len());
        if let Some(after) = input.data.strip_prefix("--") {
            input = advance(input, input.data.len() - after.len());
            let nl = input.data.find('\n').unwrap_or(input.data.len());
            input = advance(input, nl);
        } else if let Some(after) = input.data.strip_prefix("{-") {
            input = advance(input, input.data.len() - after.len());
            match input.data.find("-}") {
                Some(end) => input = advance(input, end + 2),
                None => input = advance(input, input.data.len()),
            }
        }
        if input.data.len() == start_len {
            break; // 本轮无进展：trivia 结束
        }
    }
    input
}

pub fn lex(input: Span<&str>) -> Option<(Input<'_>, Vec<Token<'_>>)> {
    let num = pmatch(|c: char| c.is_ascii_digit()).map(|x| x.map(|y| (y, Num)));
    let err_token = pmatch(|c: char| !c.is_ascii_whitespace()).map(|x| x.map(|y| (y, ErrToken)));
    fn ws<'a, A, P: Parser<Span<&'a str>, A>>(p: P) -> impl Parser<Span<&'a str>, A> {
        move |input: Span<&'a str>| {
            let input = skip_trivia(input);
            let (rest, a) = p.parse(input)?;
            Some((skip_trivia(rest), a))
        }
    }
    let input = skip_trivia(input);
    // `_` 与 `\` 单独成 token，且放在 op 之前（同 L03）：op 的字符类贪婪匹配
    // 会把 `\_.`、`_.` 吃成一个 Op token。
    let hole = is('_').map(|x| x.map(|y| (y, Hole)));
    let lambda = is('\\').map(|x| x.map(|y| (y, Lambda)));
    ws(brace.or(hole).or(lambda).or(op).or(num).or(ident))
        .or(ws(err_token))
        .many0()
        .parse(input)
}

#[test]
fn test() {
    let input = r#"
let id : {A : U} -> A -> A = \{A} x. x;
let argTest2 = const {B = U} U;
id _"#;
    let ret = lex(Span {
        data: input,
        start_offset: 0,
        end_offset: input.len() as u32,
        path_id: 0,
    })
    .unwrap();
    for x in ret.1 {
        println!("{} @ {} {:?}", x.data.0, x.start_offset, x.data.1)
    }
}
