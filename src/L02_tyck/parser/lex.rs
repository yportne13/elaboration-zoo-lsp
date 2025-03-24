use crate::parser_lib::*;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum TokenKind {
    LetKeyword,
    UKeyword,//Universe

    LParen,
    RParen,
    Eq,
    Semi,
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

const KEYWORD: [(&str, TokenKind); 2] = [
    ("let", LetKeyword),
    ("U", UKeyword),
];

const OP: [(&str, TokenKind); 7] = [
    ("(", LParen),
    (")", RParen),
    ("=", Eq),
    (";", Semi),
    (":", Colon),
    ("->", Arrow),
    ("\\\\", Lambda),
];

pub type TokenNode<'a> = Span<(&'a str, TokenKind)>;

fn ident(input: Span<&str>) -> Option<(Input<'_>, Token<'_>)> {
    pmatch(|c: char| c.is_alphabetic() || c == '_')
        .with(pmatch(|c: char| c.is_alphanumeric() || c == '_').option())
        .map(|(head, tail)| {
            let tail_len = tail.map(|t| t.len()).unwrap_or(0);
            let ident = unsafe {
                head.data
                    .get_unchecked(..head.len() as usize + tail_len as usize)
            };
            let kind = if let Some((_, k)) = KEYWORD.into_iter().find(|(k, _)| ident == *k) {
                k
            } else {
                Ident
            };
            Span {
                data: (ident, kind),
                start_offset: head.start_offset,
                end_offset: head.start_offset + head.len() + tail_len,
                path_id: head.path_id,
            }
        })
        .parse(input)
}

fn brace(input: Span<&str>) -> Option<(Input<'_>, Token<'_>)> {
    let lparen = is('(').map(|x| x.map(|y| (y, LParen)));
    let rparen = is(')').map(|x| x.map(|y| (y, RParen)));
    lparen
        .or(rparen)
        .parse(input)
}

fn op(input: Span<&str>) -> Option<(Input<'_>, Token<'_>)> {
    pmatch(|c: char| {
        ('!'..='\'').contains(&c)
            || ('*'..='/').contains(&c)
            || (':'..='@').contains(&c)
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

pub fn lex(input: Span<&str>) -> Option<(Input<'_>, Vec<Token<'_>>)> {
    let num = pmatch(|c: char| c.is_ascii_digit()).map(|x| x.map(|y| (y, Num)));
    //let endline = pmatch("\n").map(|x| x.map(|y| (y, EndLine)));
    let err_token = pmatch(|c: char| !c.is_ascii_whitespace()).map(|x| x.map(|y| (y, ErrToken)));
    fn ws<'a, A, P: Parser<Span<&'a str>, A>>(p: P) -> impl Parser<Span<&'a str>, A> {
        //let whitespace = pmatch(|c: char| c == ' ' || c == '\t' || c == '\r').option();
        let whitespace = pmatch(|c: char| c.is_whitespace()).option();
        p.with(whitespace).map(|(a, _)| a)
    }
    //let whitespace = pmatch(|c: char| c == ' ' || c == '\t' || c == '\r').option();
    let whitespace = pmatch(|c: char| c.is_whitespace()).option();
    whitespace
        .with(
            ws(brace.or(ident).or(num).or(op))
                //.or(ws(endline))
                .or(ws(err_token))
                .many0(),
        )
        .map(|(_, token)| token)
        .parse(input)
}

#[test]
fn test() {
    let input = r#"
  let id : (A : U) -> A -> A
       = \\A x. x;
  let foo : U = U;
  let bar : U = id id;
  id"#;
    let ret = lex(Span {
        data: input,
        start_offset: 0,
        end_offset: input.len() as u32,
        path_id: 0,
    })
    .unwrap();
    for x in ret.1 {
        println!("{}", x.data.0)
    }
}
