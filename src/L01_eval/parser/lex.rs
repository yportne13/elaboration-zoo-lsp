use crate::parser_lib::*;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum TokenKind {
    DefKeyword,
    ValKeyword,
    VarKeyword,
    IfKeyword,
    ElseKeyword,
    TrueKeyword,
    FalseKeyword,
    ForKeyword,
    WhileKeyword,
    ReturnKeyword,
    MatchKeyword,
    CaseKeyword,

    LParen,
    RParen,
    LSquare,
    RSquare,
    LCurly,
    RCurly,
    Eq,
    Semi,
    Comma,
    Colon,
    Dot,
    Arrow,
    DoubleArrow,
    Plus,
    Minus,
    Star,
    Slash,
    At,

    Ident,
    Num,
    Op,
    EndLine,
    Str,

    ErrToken,

    Eof,
}

pub type Token<'a> = Span<(&'a str, TokenKind)>;

use TokenKind::*;

const KEYWORD: [(&str, TokenKind); 12] = [
    ("def", DefKeyword),
    ("val", ValKeyword),
    ("var", VarKeyword),
    ("if", IfKeyword),
    ("else", ElseKeyword),
    ("match", MatchKeyword),
    ("case", CaseKeyword),
    ("true", TrueKeyword),
    ("false", FalseKeyword),
    ("for", ForKeyword),
    ("while", WhileKeyword),
    ("return", ReturnKeyword),
];

const OP: [(&str, TokenKind); 16] = [
    ("(", LParen),
    (")", RParen),
    ("{", LCurly),
    ("}", RCurly),
    ("=", Eq),
    (";", Semi),
    (",", Comma),
    (":", Colon),
    (".", Dot),
    ("->", Arrow),
    ("=>", DoubleArrow),
    ("+", Plus),
    ("-", Minus),
    ("*", Star),
    ("/", Slash),
    ("@", At),
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
    let lsquare = is('[').map(|x| x.map(|y| (y, LSquare)));
    let rsquare = is(']').map(|x| x.map(|y| (y, RSquare)));
    let lcurly = is('{').map(|x| x.map(|y| (y, LCurly)));
    let rcurly = is('}').map(|x| x.map(|y| (y, RCurly)));
    lparen
        .or(rparen)
        .or(lsquare)
        .or(rsquare)
        .or(lcurly)
        .or(rcurly)
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
    let endline = pmatch("\n").map(|x| x.map(|y| (y, EndLine)));
    let err_token = pmatch(|c: char| !c.is_ascii_whitespace()).map(|x| x.map(|y| (y, ErrToken)));
    fn ws<'a, A, P: Parser<Span<&'a str>, A>>(p: P) -> impl Parser<Span<&'a str>, A> {
        let whitespace = pmatch(|c: char| c == ' ' || c == '\t' || c == '\r').option();
        //let whitespace = pmatch(|c: char| c.is_whitespace()).option();
        p.with(whitespace).map(|(a, _)| a)
    }
    //let whitespace = pmatch(|c: char| c == ' ' || c == '\t' || c == '\r').option();
    let whitespace = pmatch(|c: char| c.is_whitespace()).option();
    whitespace
        .with(
            ws(brace.or(ident).or(num).or(op))
                .or(ws(endline))
                .or(ws(err_token))
                .many0(),
        )
        .map(|(_, token)| token)
        .parse(input)
}

#[test]
fn test() {
    let input = r#"let id = fun x -> x
let twice = fun f -> fun x -> f (f x)

let object1 = { x = 42; y = id }
let object2 = { x = 17; y = false }
let pick_an_object = fun b ->
  if b then object1 else object2

let rec produce = fun arg ->
  { head = arg; tail = produce (succ arg) }

let rec consume = fun strm ->
  add strm.head (consume strm.tail)

let codata = produce 42
let res = consume codata"#;
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
