use crate::parser_lib::*;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum TokenKind {
    LetKeyword,
    UKeyword, //Universe

    Hole,
    LParen,
    RParen,
    LCurly,
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
    is(';')
        .map(|x| x.map(|t| (t, Semi)))
        .or(pmatch(|c: char| c.is_alphabetic() || c == '_')
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
            }))
        .parse(input)
}

fn brace(input: Span<&str>) -> Option<(Input<'_>, Token<'_>)> {
    let lparen = is('(').map(|x| x.map(|y| (y, LParen)));
    let rparen = is(')').map(|x| x.map(|y| (y, RParen)));
    lparen.or(rparen).parse(input)
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
            ws(brace.or(op).or(num).or(ident))
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
let id : {A : U} -> A -> A = \x. x;

let const : {A B} -> A -> B -> A = \x y. x;

let group1 : {A B : U}(x y z : A) -> B -> B = \x y z b. b;
let group2 : {A B}(x y z : A) -> B -> B = \x y z b. b;

let the : (A : _) -> A -> A = \_ x. x;

let argTest1 = const {U}{U} U;

let argTest2 = const {B = U} U;  -- only give B, the second implicit arg

let id2 : {A} -> A -> A = \{A} x. x;

let namedLam  : {A B C} -> A -> B -> C -> A = \{B = B} a b c. a; -- second arg in scope as B
let namedLam2 : {A B C} -> A -> B -> C -> A = \{B = X} a b c. a; -- second arg in scope as X
let namedLam2 : {A B C} -> A -> B -> C -> A = \{C = X} a b c. a; -- third arg in scope as X


let insert : {A} -> A -> A = id;

let noinsert = \{A} x. the A x;

let insert2 = (\{A} x. the A x) U;  -- (\{A} x. the A x) {U} U


let Bool : U
    = (B : _) -> B -> B -> B;
let true : Bool
    = \B t f. t;
let false : Bool
    = \B t f. f;
let not : Bool -> Bool
    = \b B t f. b B f t;

let List : U -> U
    = \A. (L : _) -> (A -> L -> L) -> L -> L;
let nil : {A} -> List A
    = \L cons nil. nil;
let cons : {A} -> A -> List A -> List A
    = \x xs L cons nil. cons x (xs L cons nil);
let map : {A B} -> (A -> B) -> List A -> List B
    = \{A}{B} f xs L c n. xs L (\a. c (f a)) n;
let list1 : List Bool
    = cons true (cons false (cons true nil));

let comp : {A}{B : A -> U}{C : {a} -> B a -> U}
           (f : {a}(b : B a) -> C b)
           (g : (a : A) -> B a)
           (a : A)
           -> C (g a)
    = \f g a. f (g a);

let compExample = comp (cons true) (cons false) nil;

let Nat : U
    = (N : U) -> (N -> N) -> N -> N;
let mul : Nat -> Nat -> Nat
    = \a b N s z. a _ (b _ s) z;
let ten : Nat
    = \N s z. s (s (s (s (s (s (s (s (s (s z)))))))));
let hundred = mul ten ten;

let Eq : {A} -> A -> A -> U
    = \{A} x y. (P : A -> U) -> P x -> P y;
let refl : {A}{x : A} -> Eq x x
    = \_ px. px;

let sym : {A x y} → Eq {A} x y → Eq y x
  = λ {A}{x}{y} p. p (λ y. Eq y x) refl;

the (Eq (mul ten ten) hundred) refl

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
