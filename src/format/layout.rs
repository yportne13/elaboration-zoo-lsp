//! Whitespace-only layout engine for `textDocument/formatting`.
//!
//! Contract (see `docs/format-document-design.md`): the output is built by
//! walking the *original* token stream and choosing whitespace/indentation
//! between tokens. Token and comment text is copied verbatim and is never
//! reordered, added or dropped.
//!
//! Tokens come from the real L13 lexer (single tokenizer), run on
//! `preprocess(raw)` so `EndLine` semantics stay identical to the parser's.
//! Comments are recovered from the raw text by a *string-aware* scanner: the
//! existing `preprocess` is not string-aware (it splits on `//` even inside a
//! string literal), so it must never be trusted for comment text.

use super::FormatOptions;
use crate::L13_namespace::parser::lex::{self, TokenKind};
use crate::parser_lib::Span;
use TokenKind::*;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Eol {
    Lf,
    CrLf,
}

impl Eol {
    fn as_str(self) -> &'static str {
        match self {
            Eol::Lf => "\n",
            Eol::CrLf => "\r\n",
        }
    }
}

pub(crate) fn detect_eol(text: &str) -> Eol {
    if text.contains("\r\n") {
        Eol::CrLf
    } else {
        Eol::Lf
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct Comment {
    pub block: bool,
    pub start: u32,
    pub end: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct StrLit {
    pub start: u32,
    pub end: u32,
}

pub(crate) struct RawScan {
    pub comments: Vec<Comment>,
    pub strings: Vec<StrLit>,
}

/// String-aware scan of `raw` for comments and string literals.
/// Returns `None` on an unterminated string or block comment.
pub(crate) fn scan_raw(raw: &str) -> Option<RawScan> {
    let bytes = raw.as_bytes();
    let n = bytes.len();
    let mut i = 0usize;
    let mut comments = Vec::new();
    let mut strings = Vec::new();
    while i < n {
        match bytes[i] {
            b'"' => {
                let start = i;
                i += 1;
                let mut closed = false;
                while i < n {
                    match bytes[i] {
                        b'\\' => i += 2,
                        b'"' => {
                            i += 1;
                            closed = true;
                            break;
                        }
                        _ => i += 1,
                    }
                }
                if !closed {
                    return None;
                }
                strings.push(StrLit { start: start as u32, end: i as u32 });
            }
            b'/' if i + 1 < n && bytes[i + 1] == b'/' => {
                let start = i;
                i += 2;
                while i < n && bytes[i] != b'\n' && bytes[i] != b'\r' {
                    i += 1;
                }
                comments.push(Comment { block: false, start: start as u32, end: i as u32 });
            }
            b'/' if i + 1 < n && bytes[i + 1] == b'*' => {
                let start = i;
                i += 2;
                let mut closed = false;
                while i + 1 < n {
                    if bytes[i] == b'*' && bytes[i + 1] == b'/' {
                        i += 2;
                        closed = true;
                        break;
                    }
                    i += 1;
                }
                if !closed {
                    return None;
                }
                comments.push(Comment { block: true, start: start as u32, end: i as u32 });
            }
            _ => i += 1,
        }
    }
    Some(RawScan { comments, strings })
}

/// One non-trivia token with its byte span into the raw text.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Tok {
    pub kind: TokenKind,
    pub start: u32,
    pub end: u32,
}

/// Tokenize `raw` with the real L13 lexer. `EndLine`/`Eof` are dropped (line
/// structure is recovered from raw gaps between items); an `ErrToken` aborts,
/// because the formatter refuses to lay out text it cannot tokenize cleanly.
pub(crate) fn lex_tokens(raw: &str) -> Option<Vec<Tok>> {
    let pre = crate::L13_namespace::preprocess(raw);
    let end = pre.len() as u32;
    let (_, toks) = lex::lex(Span {
        data: pre.as_str(),
        start_offset: 0,
        end_offset: end,
        path_id: 0,
    })?;
    let mut out = Vec::with_capacity(toks.len());
    for t in toks {
        match t.data.1 {
            Eof | EndLine => {}
            ErrToken => return None,
            k => out.push(Tok { kind: k, start: t.start_offset, end: t.end_offset }),
        }
    }
    Some(out)
}

#[derive(Clone, Copy, Debug)]
enum ItemKind {
    Tok(TokenKind),
    Comment { block: bool },
}

#[derive(Clone, Copy, Debug)]
struct Item {
    start: u32,
    end: u32,
    kind: ItemKind,
}

fn merge_items(toks: &[Tok], comments: &[Comment]) -> Option<Vec<Item>> {
    let mut items: Vec<Item> = Vec::with_capacity(toks.len() + comments.len());
    for t in toks {
        items.push(Item { start: t.start, end: t.end, kind: ItemKind::Tok(t.kind) });
    }
    for c in comments {
        items.push(Item { start: c.start, end: c.end, kind: ItemKind::Comment { block: c.block } });
    }
    items.sort_by_key(|i| i.start);
    // Tokens and comments must be disjoint; if they overlap the token stream is
    // not trustworthy, so decline.
    let mut last = 0u32;
    for it in &items {
        if it.start < last {
            return None;
        }
        last = last.max(it.end);
    }
    Some(items)
}

fn is_opener(k: TokenKind) -> bool {
    matches!(k, LParen | LSquare | LCurly)
}

fn is_closer(k: TokenKind) -> bool {
    matches!(k, RParen | RSquare | RCurly)
}

fn is_op_like(k: TokenKind) -> bool {
    matches!(k, Op | Eq | Arrow | DoubleArrow | Lambda)
}

fn is_prefix_op(kind: TokenKind, text: &str) -> bool {
    kind == Op && matches!(text, "-" | "!" | "~")
}

fn is_operand(k: TokenKind) -> bool {
    matches!(k, Ident | Num | Str | Hole | MacroIdent | RParen | RSquare | RCurly)
}

/// A token at end-of-line that opens an unbraced continuation body, so the
/// following lines get one extra indent level until the continuation closes.
fn is_continuation_tok(k: TokenKind) -> bool {
    matches!(k, Eq | DoubleArrow | Arrow | WhereKeyword)
}

/// Top-level declaration starters; at bracket depth 0 they end any pending
/// continuation indent from the previous (unbraced) declaration.
fn is_decl_keyword(k: TokenKind) -> bool {
    matches!(
        k,
        DefKeyword
            | EnumKeyword
            | StructKeyword
            | TraitKeyword
            | ImplKeyword
            | ClassKeyword
            | PackageKeyword
            | ImportKeyword
            | PrintlnKeyword
            | MacroKeyword
    )
}

/// Whether a single space goes between two adjacent same-line tokens.
///
/// The `had_space` flag is the author's original gap (non-empty) between the
/// two tokens. It is used only where the surface grammar is genuinely ambiguous
/// — call `f(x)` vs grouping/application `f (x)`, indexing `x[i]` vs implicit
/// application `Vec[A]`, and inline vs compact braces `{ x }` / `{x}` — so the
/// formatter normalises spacing without erasing the author's intent.
fn space_between(prev: (TokenKind, &str), next: (TokenKind, &str), had_space: bool) -> bool {
    let (pk, _pt) = prev;
    let (nk, _nt) = next;
    match nk {
        RParen | RSquare => return false,
        LCurly | RCurly | LParen | LSquare => return had_space,
        Comma | Semi | Dot | Colon => return false,
        _ => {}
    }
    match pk {
        LParen | LSquare => return false,
        LCurly => return had_space,
        Dot => return false,
        Colon | Comma | Semi => return true,
        _ => {}
    }
    if is_op_like(pk) || is_op_like(nk) {
        return true;
    }
    true
}

struct Renderer<'o> {
    opts: &'o FormatOptions,
    eol: Eol,
    out: String,
    line: String,
    active: bool,
    line_has_content: bool,
    written_any: bool,
    pending_blanks: usize,
    depth: i32,
    line_prev: Option<(TokenKind, String)>,
    line_prev_was_prefix: bool,
    /// Whether an unbraced continuation body is open (see [`is_continuation_tok`]).
    cont_active: bool,
    /// Bracket depth at which the current continuation was opened; the extra
    /// indent applies while `depth >= cont_base_depth`.
    cont_base_depth: i32,
    /// First token emitted on the current line, used to recognise an HDL
    /// `module NAME[params]` header whose port list continues on later lines.
    line_first_tok: Option<(TokenKind, String)>,
    /// 0-based source line currently being consumed (advanced by newline gaps).
    src_line: usize,
    /// Source line that the line currently being built originated from.
    line_origin: usize,
    /// For each emitted output line, the source line it originated from.
    origins: Vec<usize>,
}

impl<'o> Renderer<'o> {
    fn new(opts: &'o FormatOptions, eol: Eol, cap: usize) -> Self {
        Self {
            opts,
            eol,
            out: String::with_capacity(cap),
            line: String::new(),
            active: false,
            line_has_content: false,
            written_any: false,
            pending_blanks: 0,
            depth: 0,
            line_prev: None,
            line_prev_was_prefix: false,
            cont_active: false,
            cont_base_depth: 0,
            line_first_tok: None,
            src_line: 0,
            line_origin: 0,
            origins: Vec::new(),
        }
    }

    fn ensure_line(&mut self) {
        if self.active {
            return;
        }
        if self.written_any {
            for _ in 0..self.pending_blanks {
                self.out.push_str(self.eol.as_str());
                // Blank lines belong to the source line of the content that
                // follows them; keeps `origins` aligned with output lines.
                self.origins.push(self.src_line);
            }
        }
        self.pending_blanks = 0;
        self.line.clear();
        let extra = if self.cont_active && self.depth >= self.cont_base_depth { 1 } else { 0 };
        let level = (self.depth + extra).max(0);
        if self.opts.use_tabs {
            for _ in 0..level {
                self.line.push('\t');
            }
        } else {
            for _ in 0..(level as usize * self.opts.indent_width) {
                self.line.push(' ');
            }
        }
        self.active = true;
        self.line_has_content = false;
        self.line_prev = None;
        self.line_prev_was_prefix = false;
        self.line_first_tok = None;
        self.line_origin = self.src_line;
    }

    fn push(&mut self, text: &str, space: bool) {
        self.ensure_line();
        if self.line_has_content && space {
            self.line.push(' ');
        }
        self.line.push_str(text);
        self.line_has_content = true;
    }

    fn flush(&mut self) {
        if self.active {
            self.out.push_str(&self.line);
            self.out.push_str(self.eol.as_str());
            self.written_any = true;
            self.active = false;
            self.line_has_content = false;
            // A single emitted line may itself contain newlines (a multi-line
            // string literal or block comment), in which case it maps to that
            // many output lines; keep `origins` one-entry-per-output-line.
            for _ in 0..=self.line.matches('\n').count() {
                self.origins.push(self.line_origin);
            }
            self.line.clear();
        }
    }

    fn newline_gap(&mut self, nl: usize) {
        self.flush();
        self.src_line += nl;
        if let Some((k, _)) = &self.line_prev {
            // A binary operator at end-of-line continues the expression; a
            // prefix operator (`-`/`!`/`~`) does not.
            let cont = is_continuation_tok(*k) || (*k == Op && !self.line_prev_was_prefix);
            if cont {
                self.cont_active = true;
                self.cont_base_depth = self.depth;
            }
        }
        // HDL `module NAME[params]` split across lines: the port list that
        // follows is part of the header, so keep it indented until the body
        // brace opens. (`line_prev` is the `]` of the parameter list.)
        if matches!(&self.line_first_tok, Some((Ident, t)) if t == "module")
            && matches!(&self.line_prev, Some((RSquare, _)))
        {
            self.cont_active = true;
            self.cont_base_depth = self.depth;
        }
        if nl >= 2 {
            self.cont_active = false;
        }
        self.pending_blanks = nl.saturating_sub(1).min(self.opts.max_blank_lines);
        self.line_prev = None;
        self.line_prev_was_prefix = false;
        self.line_first_tok = None;
    }
}

pub(crate) fn render(
    raw: &str,
    items: &[Item],
    opts: &FormatOptions,
    eol: Eol,
) -> Option<(String, Vec<usize>)> {
    let mut r = Renderer::new(opts, eol, raw.len() + raw.len() / 8 + 16);
    let mut prev_end = 0u32;
    for it in items {
        let start = it.start as usize;
        let end = it.end as usize;
        if start > raw.len() || end > raw.len() || start > end {
            return None;
        }
        let gap = &raw[prev_end as usize..start];
        let nl = gap.as_bytes().iter().filter(|&&b| b == b'\n').count();
        let had_space = !gap.is_empty();
        if nl > 0 {
            r.newline_gap(nl);
        }
        // The lexer's `Str` token span covers only the content between the
        // quotes; widen it so the literal is re-emitted with its quotes.
        let text: &str = match it.kind {
            ItemKind::Tok(Str) => {
                if start == 0 || end >= raw.len() {
                    return None;
                }
                &raw[start - 1..end + 1]
            }
            _ => &raw[start..end],
        };
        match it.kind {
            ItemKind::Tok(kind) => {
                if !r.active && r.depth == 0 && is_decl_keyword(kind) {
                    r.cont_active = false;
                }
                // A line-leading `{` closes a split module header: dedent it to
                // the construct's base so the body brace aligns with `module`.
                if !r.active && kind == LCurly {
                    r.cont_active = false;
                }
                if is_closer(kind) {
                    r.depth = (r.depth - 1).max(0);
                    if r.cont_active && r.depth < r.cont_base_depth {
                        r.cont_active = false;
                    }
                }
                let unary = is_prefix_op(kind, text)
                    && !r.line_prev.as_ref().map(|(k, _)| is_operand(*k)).unwrap_or(false);
                let space = if r.line_prev_was_prefix {
                    false
                } else {
                    match &r.line_prev {
                        Some((pk, pt)) => space_between((*pk, pt.as_str()), (kind, text), had_space),
                        None => r.line_has_content,
                    }
                };
                let was_first = !r.line_has_content;
                r.push(text, space);
                if was_first {
                    r.line_first_tok = Some((kind, text.to_string()));
                }
                if is_opener(kind) {
                    r.depth += 1;
                }
                r.line_prev = Some((kind, text.to_string()));
                r.line_prev_was_prefix = unary;
            }
            ItemKind::Comment { block } => {
                if block && text.contains('\n') {
                    // Multi-line block comment: preserve its body verbatim on
                    // its own lines (re-indent the first line only) so that
                    // ASCII art / internal alignment is not mangled.
                    r.flush();
                    r.ensure_line();
                    r.line.push_str(text);
                    r.line_has_content = true;
                    r.flush();
                    r.line_prev = None;
                    r.line_prev_was_prefix = false;
                } else {
                    let space = r.active && r.line_has_content;
                    r.push(text, space);
                    r.line_prev = None;
                    r.line_prev_was_prefix = false;
                }
            }
        }
        prev_end = it.end;
    }
    r.flush();
    Some((r.out, r.origins))
}

/// Layout `raw` into `(formatted_text, origins)`, where `origins[i]` is the
/// 0-based source line that output line `i` came from. `None` when the input
/// cannot be safely formatted (oversized, unterminated literal/comment,
/// untokenizable, or ambiguous string/comment overlap).
pub(crate) fn layout_parts(raw: &str, opts: &FormatOptions) -> Option<(String, Vec<usize>)> {
    if raw.len() > opts.max_bytes {
        return None;
    }
    let scan = scan_raw(raw)?;
    // `preprocess` is not string-aware: a string literal containing a comment
    // opener would make the token stream unreliable, so decline rather than
    // risk corrupting the literal.
    for s in &scan.strings {
        let lit = &raw[s.start as usize..s.end as usize];
        if lit.contains("//") || lit.contains("/*") {
            return None;
        }
    }
    let toks = lex_tokens(raw)?;
    let items = merge_items(&toks, &scan.comments)?;
    let eol = detect_eol(raw);
    render(raw, &items, opts, eol)
}

/// Layout `raw` into formatted text.
pub(crate) fn layout(raw: &str, opts: &FormatOptions) -> Option<String> {
    layout_parts(raw, opts).map(|(s, _)| s)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fmt(s: &str) -> String {
        layout(s, &FormatOptions::default()).expect("layout")
    }

    #[test]
    fn scan_ignores_comment_openers_in_strings() {
        let src = r#"let a = "http://x" // real"#;
        let s = scan_raw(src).unwrap();
        assert_eq!(s.strings.len(), 1);
        assert_eq!(s.comments.len(), 1);
        let c = s.comments[0];
        assert_eq!(&src[c.start as usize..c.end as usize], "// real");
    }

    #[test]
    fn scan_rejects_unterminated() {
        assert!(scan_raw("let a = /* oops").is_none());
        assert!(scan_raw("let a = \"oops").is_none());
    }

    #[test]
    fn basic_indent_and_spacing() {
        let src = "def add(x: Nat, y: Nat): Nat = {\nmatch x {\ncase zero => y\ncase succ(n) => succ(add(n, y))\n}\n}\n";
        assert_eq!(
            fmt(src),
            "def add(x: Nat, y: Nat): Nat = {\n    match x {\n        case zero => y\n        case succ(n) => succ(add(n, y))\n    }\n}\n"
        );
    }

    #[test]
    fn comment_preserved_and_indented() {
        assert_eq!(
            fmt("def f = {\n// hi\n1\n}\n"),
            "def f = {\n    // hi\n    1\n}\n"
        );
    }

    #[test]
    fn blank_lines_collapsed() {
        assert_eq!(
            fmt("def a = 1\n\n\n\ndef b = 2\n"),
            "def a = 1\n\ndef b = 2\n"
        );
    }

    #[test]
    fn trailing_whitespace_and_final_newline() {
        assert_eq!(fmt("def a = 1   \n\n\n"), "def a = 1\n");
    }

    #[test]
    fn preserves_call_vs_grouping_spacing() {
        assert_eq!(
            fmt("def a = succ(zero)\ndef b = the (Eq x y)\n"),
            "def a = succ(zero)\ndef b = the (Eq x y)\n"
        );
    }

    #[test]
    fn unary_vs_binary_minus() {
        assert_eq!(fmt("def a = -5\ndef b = x - 5\n"), "def a = -5\ndef b = x - 5\n");
    }

    #[test]
    fn unbraced_body_gets_continuation_indent() {
        let src = "def pow2(n: Nat): Nat =\nmatch n {\ncase zero => 1\ncase succ(m) => double(pow2(m))\n}\n";
        assert_eq!(
            fmt(src),
            "def pow2(n: Nat): Nat =\n    match n {\n        case zero => 1\n        case succ(m) => double(pow2(m))\n    }\n"
        );
    }

    #[test]
    fn binary_operator_at_eol_continues_expression() {
        assert_eq!(
            fmt("def f = a +\nb * c\n"),
            "def f = a +\n    b * c\n"
        );
        // A prefix operator at end of line does not open a continuation.
        assert_eq!(fmt("def f = !\nb\n"), "def f = !\nb\n");
    }

    #[test]
    fn split_module_header_keeps_ports_indented() {
        let src = "module myAdder[w: Nat]\ninput a = UInt[w]\ninput en = Bool\n{\nsum := a + b\n}\n";
        assert_eq!(
            fmt(src),
            "module myAdder[w: Nat]\n    input a = UInt[w]\n    input en = Bool\n{\n    sum := a + b\n}\n"
        );
    }

    #[test]
    fn continuation_does_not_leak_into_next_decl() {
        let src = "def f =\nmatch x {\ncase a => 1\n}\ndef g = 2\n";
        assert_eq!(
            fmt(src),
            "def f =\n    match x {\n        case a => 1\n    }\ndef g = 2\n"
        );
    }
}
