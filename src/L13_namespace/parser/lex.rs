use crate::parser_lib::*;
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum TokenKind {
    DefKeyword,
    LetKeyword,
    PrintlnKeyword,
    EnumKeyword,
    StructKeyword,
    TypeKeyword, //Universe
    MatchKeyword,
    CaseKeyword,
    NewKeyword,
    TraitKeyword,
    ImplKeyword,
    ForKeyword,
    ThisKeyword,
    StaticKeyword,
    MacroKeyword,
    WhereKeyword,
    PackageKeyword,
    ImportKeyword,
    ClassKeyword,
    ByKeyword,

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
    MacroIdent,
    Num,
    Op,
    Str,

    EndLine,

    ErrToken,

    Eof,
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenKind::DefKeyword     => write!(f, "`def`"),
            TokenKind::LetKeyword     => write!(f, "`let`"),
            TokenKind::PrintlnKeyword => write!(f, "`println`"),
            TokenKind::EnumKeyword    => write!(f, "`enum`"),
            TokenKind::StructKeyword  => write!(f, "`struct`"),
            TokenKind::TypeKeyword    => write!(f, "`Type`"),
            TokenKind::MatchKeyword   => write!(f, "`match`"),
            TokenKind::CaseKeyword    => write!(f, "`case`"),
            TokenKind::NewKeyword     => write!(f, "`new`"),
            TokenKind::TraitKeyword   => write!(f, "`trait`"),
            TokenKind::ImplKeyword    => write!(f, "`impl`"),
            TokenKind::ForKeyword     => write!(f, "`for`"),
            TokenKind::ThisKeyword    => write!(f, "`this`"),
            TokenKind::StaticKeyword  => write!(f, "`static`"),
            TokenKind::MacroKeyword   => write!(f, "`macro_rules`"),
            TokenKind::WhereKeyword   => write!(f, "`where`"),
            TokenKind::PackageKeyword => write!(f, "`package`"),
            TokenKind::ImportKeyword  => write!(f, "`import`"),
            TokenKind::ClassKeyword   => write!(f, "`class`"),
            TokenKind::ByKeyword      => write!(f, "`by`"),
            TokenKind::Hole           => write!(f, "`_`"),
            TokenKind::LParen         => write!(f, "`(`"),
            TokenKind::RParen         => write!(f, "`)`"),
            TokenKind::LSquare        => write!(f, "`[`"),
            TokenKind::RSquare        => write!(f, "`]`"),
            TokenKind::LCurly         => write!(f, "`{{`"),
            TokenKind::RCurly         => write!(f, "`}}`"),
            TokenKind::Dot            => write!(f, "`.`"),
            TokenKind::Eq             => write!(f, "`=`"),
            TokenKind::Semi           => write!(f, "`;`"),
            TokenKind::Colon          => write!(f, "`:`"),
            TokenKind::Arrow          => write!(f, "`->`"),
            TokenKind::DoubleArrow    => write!(f, "`=>`"),
            TokenKind::Lambda         => write!(f, "`\\`"),
            TokenKind::Comma          => write!(f, "`,`"),
            TokenKind::Ident          => write!(f, "identifier"),
            TokenKind::MacroIdent     => write!(f, "macro identifier"),
            TokenKind::Num            => write!(f, "number"),
            TokenKind::Op             => write!(f, "operator"),
            TokenKind::Str            => write!(f, "string"),
            TokenKind::EndLine        => write!(f, "newline"),
            TokenKind::ErrToken       => write!(f, "unexpected token"),
            TokenKind::Eof            => write!(f, "end of file"),
        }
    }
}

pub type Token<'a> = Span<(&'a str, TokenKind)>;

use TokenKind::*;

const KEYWORD: [(&str, TokenKind); 20] = [
    ("package", PackageKeyword),
    ("import", ImportKeyword),
    ("def", DefKeyword),
    ("let", LetKeyword),
    ("println", PrintlnKeyword),
    ("enum", EnumKeyword),
    ("struct", StructKeyword),
    ("Type", TypeKeyword),
    ("match", MatchKeyword),
    ("case", CaseKeyword),
    ("new", NewKeyword),
    ("trait", TraitKeyword),
    ("impl", ImplKeyword),
    ("for", ForKeyword),
    ("this", ThisKeyword),
    ("static", StaticKeyword),
    ("macro_rules", MacroKeyword),
    ("where", WhereKeyword),
    ("class", ClassKeyword),
    ("by", ByKeyword),
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
    let data = input.data.strip_prefix('"')?;
    let bytes = data.as_bytes();
    let mut end = 0;
    while end < bytes.len() {
        if bytes[end] == b'"' {
            break;
        }
        if bytes[end] == b'\\' {
            end += 2;
        } else {
            end += 1;
        }
    }
    if end >= bytes.len() || bytes[end] != b'"' {
        return None;
    }
    let content = &data[..end];
    let remaining = &data[end + 1..];
    Some((
        Span {
            data: remaining,
            start_offset: input.start_offset + 2 + end as u32,
            end_offset: input.end_offset,
            path_id: input.path_id,
        },
        Span {
            data: (content, Str),
            start_offset: input.start_offset + 1,
            end_offset: input.start_offset + 1 + end as u32,
            path_id: input.path_id,
        },
    ))
}

fn ident(input: Span<&str>) -> Option<(Input<'_>, Token<'_>)> {
    is(';')
        .map(|x| x.map(|t| (t, Semi)))
        .or(pmatch(|c: char| c.is_alphabetic() || c == '_')
            .with(pmatch(|c: char| c.is_alphanumeric() || c == '_').option())
            .map(|(head, tail)| {
                let tail_len = tail.map(|t| t.len()).unwrap_or(0);
                let ident = unsafe {
                    input.data
                        .get_unchecked(..head.len() as usize + tail_len as usize)
                };
                let kind = if ident == "_" {
                    Hole
                } else if let Some((_, k)) = KEYWORD.into_iter().find(|(k, _)| ident == *k) {
                    k
                } else if ident == "until" {
                    // HDL range operator: `0 until 4` parses as infix
                    // `0.until(4)` (kind+text matcher in macro patterns
                    // compares this token exactly like any Op).
                    Op
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

fn macro_ident(input: Span<&str>) -> Option<(Input<'_>, Token<'_>)> {
    is('$')
        .with(pmatch(|c: char| c.is_alphabetic() || c == '_'))
        .with(pmatch(|c: char| c.is_alphanumeric() || c == '_').option())
        .map(|((head, tail0), tail)| {
            let tail_len = tail.map(|t| t.len()).unwrap_or(0);
            let ident = unsafe {
                input.data
                    .get_unchecked(..head.len() as usize + tail0.len() as usize + tail_len as usize)
            };
            Span {
                data: (ident, MacroIdent),
                start_offset: head.start_offset,
                end_offset: head.start_offset + head.len() + tail0.len() + tail_len,
                path_id: head.path_id,
            }
        })
        .parse(input)
}

fn brace(input: Span<&str>) -> Option<(Input<'_>, Token<'_>)> {
    let dot = is('.').map(|x| x.map(|y| (y, Dot)));
    let comma = is(',').map(|x| x.map(|y| (y, Comma)));
    let lparen = is('(').map(|x| x.map(|y| (y, LParen)));
    let rparen = is(')').map(|x| x.map(|y| (y, RParen)));
    let lsquare = is('[').map(|x| x.map(|y| (y, LSquare)));
    let rsquare = is(']').map(|x| x.map(|y| (y, RSquare)));
    let lcurly = is('{').map(|x| x.map(|y| (y, LCurly)));
    let rcurly = is('}').map(|x| x.map(|y| (y, RCurly)));
    dot
        .or(comma)
        .or(lparen)
        .or(rparen)
        .or(lsquare)
        .or(rsquare)
        .or(lcurly)
        .or(rcurly)
        .parse(input)
}

fn op(input: Span<&str>) -> Option<(Input<'_>, Token<'_>)> {
    // '.' is excluded from the operator character ranges so that it is never consumed
    // as part of an operator token — it's always lexed as a standalone Dot.
    pmatch(|c: char| {
        ('!'..='\'').contains(&c)
            || (('*'..='-').contains(&c) || c == '/')
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

/// EndLine token 文本的「下一行缩进列」：最后一个换行之后的水平空白
/// **字符数**。缩进列定义（见 `lex` 内 `endline` 的注释）：' ' / '\t' /
/// '\r' 各计 1 列，不做 tab 展开——只用于相对深浅比较（续行 vs 语句
/// 锚点），统一定宽不影响判定。非 EndLine 文本调用返回无意义值。
pub fn endline_indent(text: &str) -> u32 {
    text.rsplit('\n').next().map_or(0, |s| s.chars().count() as u32)
}

/// Q2（2026-10-02，续行断开修复）：EndLine token 的文本从「换行 run」
/// 扩为「换行 run + 紧随的水平空白（下一行前导缩进）」，end_offset 同
/// 步延伸到下一行第一个非空白字符之前。解析器用 `endline_indent(token
/// 文本)` 读出下一行缩进列，在 p_spine 实参循环里做缩进感知续行。
///
/// 旧实现里这段缩进由 `ws` 包装吞掉后丢弃（token 只到换行末尾），词法
/// 层完全不携带行布局信息。缩进列的口径：' ' / '\t' / '\r' 各计 1 列
/// （与 `ws` 的空白类一致），不做 tab 展开；CRLF 的 '\r' 在换行前被上
/// 一 token 的尾随 ws 吃掉，行首孤悬 '\r' 计 1 列。
///
/// 行为保持：换行 run 之间夹水平空白的折叠（旧 many1 of ws("\n") 把
/// "\n \n" 并成一个 EndLine）等价保留——循环直到水平空白后不再是换行
/// 为止；token 覆盖范围多吃了尾随缩进而已。
///
/// 一致性要求：宏展开/块拼接送 owned token 文本重拼字符串再 re-lex
/// （parser/mod.rs owned_tokens_to_string_mapped）——EndLine 文本带缩进
/// 后，拼接处在 EndLine 之后**不再补空格分隔**（见该函数），re-lex 逐
/// 列复原缩进；否则每次 re-lex 缩进 +1，同缩进守护（calc 步骤）会被
/// 差一错误击穿。
fn endline(input: Input<'_>) -> Option<(Input<'_>, Token<'_>)> {
    let mut rest = input;
    loop {
        let (r, _) = pmatch("\n").parse(rest)?;
        // 贪心水平空白（可空）：option 包装保证零匹配也成功
        let (r, _) = pmatch(|c: char| c == ' ' || c == '\t' || c == '\r')
            .option()
            .parse(r)?;
        rest = r;
        if !rest.data.starts_with('\n') {
            break;
        }
    }
    let len = input.data.len() - rest.data.len();
    Some((
        rest,
        Span {
            data: (&input.data[..len], EndLine),
            start_offset: input.start_offset,
            end_offset: input.start_offset + len as u32,
            path_id: input.path_id,
        },
    ))
}

pub fn lex(input: Span<&str>) -> Option<(Input<'_>, Vec<Token<'_>>)> {
    let num = pmatch(|c: char| c.is_ascii_digit()).map(|x| x.map(|y| (y, Num)));
    let err_token = pmatch(|c: char| !c.is_ascii_whitespace()).map(|x| x.map(|y| (y, ErrToken)));
    fn ws<'a, A, P: Parser<Span<&'a str>, A>>(p: P) -> impl Parser<Span<&'a str>, A> {
        let whitespace = pmatch(|c: char| c == ' ' || c == '\t' || c == '\r').option();
        //let whitespace = pmatch(|c: char| c.is_whitespace()).option();
        p.with(whitespace).map(|(a, _)| a)
    }
    //let whitespace = pmatch(|c: char| c == ' ' || c == '\t' || c == '\r').option();
    // 前导空白：**额外吞掉文件开头的 UTF-8 BOM**（U+FEFF）。`fs::read_to_string`
    // （`src/bin/cli.rs:705`）不剥 BOM，客户端也可能把它放进 `didOpen.text`；
    // 而 U+FEFF 不在 Unicode `White_Space` 属性里 ⇒ `is_whitespace()` 不匹配它
    // ⇒ BOM 落到 `err_token`（`!is_ascii_whitespace`）变成 `ErrToken`，顶层报一条
    // 伪解析错误并触发恢复。只扩前导这一处（token 循环内的 `ws()` 不含 BOM），
    // 所以文件中间的 U+FEFF 仍是 `ErrToken`（行为不变）。
    let whitespace = pmatch(|c: char| c.is_whitespace() || c == '\u{feff}').option();
    whitespace
        .with(
            //ws(brace.or(ident).or(num).or(op))
            ws(string.or(macro_ident).or(brace).or(op).or(num).or(ident))
                .or(ws(endline))
                .or(ws(err_token))
                .many0(),
        )
        .map(|(_, token)| {
            let mut token = token;
            token.push(Span {
                data: ("", Eof),
                start_offset: input.end_offset,
                end_offset: input.end_offset,
                path_id: input.path_id,
            });
            token
        })
        .parse(input)
}

#[test]
fn test() {
    let input = r#"
def Eq[A : Type0](x: A, y: A): Type0 = (P : A -> Type0) -> P x -> P y
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

enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(n: Nat)
}

def two = succ(succ(zero))

def add(x: Nat, y: Nat): Nat = {
    match x {
        case zero => y
        case succ(n) => succ(add(n, y))
    }
}

def four = add(two, two)

println four

struct SimplePoint(Nat, Nat)

struct Point {
    x: Nat,
    y: Nat,
}

struct Span[T] {
    data: T,
    start: Nat,
    end: Nat,
}

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
