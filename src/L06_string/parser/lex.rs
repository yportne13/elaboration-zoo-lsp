use crate::parser_lib::*;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum TokenKind {
    DefKeyword,
    LetKeyword,
    PrintlnKeyword,
    UKeyword, //Universe

    Hole,
    LParen,
    RParen,
    LSquare,
    RSquare,
    LCurly,
    RCurly,
    Dot,
    Eq,
    /// ;
    Semi,
    /// :
    Colon,
    Arrow,
    DoubleArrow,
    Lambda,
    Comma,

    Ident,
    Num,
    Op,
    Str,

    ErrToken,

    Eof,
}

pub type Token<'a> = Span<(&'a str, TokenKind)>;

use TokenKind::*;

const KEYWORD: [(&str, TokenKind); 4] = [
    ("def", DefKeyword),
    ("let", LetKeyword),
    ("println", PrintlnKeyword),
    ("U", UKeyword),
];

const OP: [(&str, TokenKind); 15] = [
    ("_", Hole),
    ("(", LParen),
    (")", RParen),
    ("[", LSquare),
    ("]", RSquare),
    ("{", LCurly),
    ("}", RCurly),
    (".", Dot),
    (",", Comma),
    ("=", Eq),
    (";", Semi),
    (":", Colon),
    ("->", Arrow),
    ("=>", DoubleArrow),
    ("\\", Lambda),
];

pub type TokenNode<'a> = Span<(&'a str, TokenKind)>;

fn string(input: Span<&str>) -> Option<(Input<'_>, Token<'_>)> {
    (is('"'), pmatch(|c: char| c != '"'), is('"'))
        .map(|(_, x, _)| x.map(|t| (t, Str)))
        .parse(input)
}

fn ident(input: Span<&str>) -> Option<(Input<'_>, Token<'_>)> {
    is(';')
        .map(|x| x.map(|t| (t, Semi)))
        .or(is('_').map(|x| x.map(|t| (t, Hole))))
        .or(pmatch(|c: char| c.is_alphabetic() || c == '_')
            .with(pmatch(|c: char| c.is_alphanumeric() || c == '_').option())
            .map(|(head, tail)| {
                let tail_len = tail.map(|t| t.len()).unwrap_or(0);
                let ident = unsafe {
                    input.data
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
            }))
        .parse(input)
}

fn brace(input: Span<&str>) -> Option<(Input<'_>, Token<'_>)> {
    let lparen = is('(').map(|x| x.map(|y| (y, LParen)));
    let rparen = is(')').map(|x| x.map(|y| (y, RParen)));
    let lsquare = is('[').map(|x| x.map(|y| (y, LSquare)));
    let rsquare = is(']').map(|x| x.map(|y| (y, RSquare)));
    let lcurly = is('{').map(|x| x.map(|y| (y, LCurly)));
    let rcurly = is('}').map(|x| x.map(|y| (y, RCurly)));
    lparen.or(rparen).or(lsquare).or(rsquare).or(lcurly).or(rcurly).parse(input)
}

fn op(input: Span<&str>) -> Option<(Input<'_>, Token<'_>)> {
    pmatch(|c: char| {
        ('!'..='\'').contains(&c)
            || ('*'..='/').contains(&c)
            || ((':'..='@').contains(&c) && c != ';')
            || c == '\\'
            || (('^'..='`').contains(&c) && c != '_')
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
            //ws(brace.or(ident).or(num).or(op))
            ws(string.or(brace).or(op).or(num).or(ident))
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
def Eq[A : U](x: A, y: A): U = (P : A -> U) -> P x -> P y
def refl[A : U, x: A]: Eq[A] x x = _ => px => px

def the(A : U)(x: A): A = x

def m(A : U)(B : U): U -> U -> U = _
def test = a => b => the (Eq (m a a) (x => y => y)) refl

def m : U -> U -> U -> U = _
def test = a => b => c => the (Eq (m a b c) (m c b a)) refl


def pr1 = f => x => f x
def pr2 = f => x => y => f x y
def pr3 = f => f U

def Nat : U
    = (N : U) -> (N -> N) -> N -> N
def mul : Nat -> Nat -> Nat
    = a => b => N => s => z => a _ (b _ s) z
def ten : Nat
    = N => s => z => s (s (s (s (s (s (s (s (s (s z)))))))))
def hundred = mul ten ten

println hundred

def mystr = "hello world"

println mystr

"#;
    let ret = lex(Span {
        data: input,
        start_offset: 0,
        end_offset: input.len() as u32,
        path_id: 0,
    })
    .unwrap();
    for x in ret.1 {
        println!("{} @ {}", x.data.0, x.start_offset)
    }
}
