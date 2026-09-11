//! `textDocument/formatting` — a conservative, whitespace-only formatter.
//!
//! The design (see `docs/format-document-design.md`) keeps the formatter
//! independent of the desugaring parser: layout is derived from the real L13
//! token stream plus a string-aware comment scan, and every token/comment is
//! emitted verbatim. Before returning, [`format_document`] re-checks three
//! invariants and declines (`None`) if any fails:
//!
//!   1. [`token_signature`] — what the parser tokenizes must not change;
//!   2. [`comment_signature`] — comment text must not change;
//!   3. [`string_signature`] — string literal text must not change;
//!
//! plus idempotence (`format(format(x)) == format(x)`).

mod layout;

use crate::L13_namespace::parser::lex::TokenKind;

/// Layout options. Defaults follow the repository style (4-space indent, at
/// most one blank line between declarations).
#[derive(Clone, Copy, Debug)]
pub struct FormatOptions {
    pub indent_width: usize,
    pub use_tabs: bool,
    pub max_blank_lines: usize,
    /// Refuse to format documents larger than this many bytes (wasm frame guard).
    pub max_bytes: usize,
}

impl Default for FormatOptions {
    fn default() -> Self {
        Self {
            indent_width: 4,
            use_tabs: false,
            max_blank_lines: 1,
            max_bytes: 1 << 20,
        }
    }
}

/// Format `raw`, or return `None` when the document cannot be safely formatted.
pub fn format_document(raw: &str, opts: &FormatOptions) -> Option<String> {
    let out = layout::layout(raw, opts)?;
    if out == raw {
        return Some(out);
    }
    if token_signature(raw)? != token_signature(&out)? {
        return None;
    }
    if comment_signature(raw)? != comment_signature(&out)? {
        return None;
    }
    if string_signature(raw)? != string_signature(&out)? {
        return None;
    }
    if layout::layout(&out, opts)? != out {
        return None;
    }
    Some(out)
}

/// Whitespace-insensitive token sequence, as seen by the real parser pipeline.
/// A formatter must never change this.
pub fn token_signature(text: &str) -> Option<Vec<(TokenKind, String)>> {
    let toks = layout::lex_tokens(text)?;
    Some(
        toks.iter()
            .map(|t| (t.kind, text[t.start as usize..t.end as usize].to_string()))
            .collect(),
    )
}

/// Comment texts (exact, including `//` / `/* */` markers) in source order.
pub fn comment_signature(text: &str) -> Option<Vec<(bool, String)>> {
    let scan = layout::scan_raw(text)?;
    Some(
        scan.comments
            .iter()
            .map(|c| (c.block, text[c.start as usize..c.end as usize].to_string()))
            .collect(),
    )
}

/// String literal texts (exact, including quotes) in source order.
pub fn string_signature(text: &str) -> Option<Vec<String>> {
    let scan = layout::scan_raw(text)?;
    Some(
        scan.strings
            .iter()
            .map(|s| text[s.start as usize..s.end as usize].to_string())
            .collect(),
    )
}

/// Edit replacing a whole-line span of the source with formatted text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RangeEdit {
    /// Byte span in the original text that [`RangeEdit::new_text`] replaces.
    pub start_byte: usize,
    pub end_byte: usize,
    pub new_text: String,
}

/// Format whole source lines `[start_line, end_line]` (0-based, inclusive).
///
/// Line breaks and indentation are computed with the full document as context,
/// then only the output lines originating from the selected source lines are
/// returned. Returns `None` when the document cannot be safely formatted,
/// `Some(None)` when the range is already formatted, else `Some(Some(edit))`.
pub fn format_range(
    raw: &str,
    opts: &FormatOptions,
    start_line: usize,
    end_line: usize,
) -> Option<Option<RangeEdit>> {
    let (formatted, origins) = layout::layout_parts(raw, opts)?;

    // Byte offset at which each source line starts.
    let mut line_starts = vec![0usize];
    for (i, b) in raw.bytes().enumerate() {
        if b == b'\n' {
            line_starts.push(i + 1);
        }
    }
    let last = line_starts.len() - 1;
    let start_line = start_line.min(last);
    let end_line = end_line.min(last);
    if start_line > end_line {
        return Some(None);
    }

    let eol = match layout::detect_eol(raw) {
        layout::Eol::Lf => "\n",
        layout::Eol::CrLf => "\r\n",
    };
    let mut out_lines: Vec<&str> = formatted.split('\n').collect();
    if out_lines.last() == Some(&"") {
        out_lines.pop();
    }
    let out_lines: Vec<&str> = out_lines
        .into_iter()
        .map(|l| l.strip_suffix('\r').unwrap_or(l))
        .collect();
    // The renderer emits exactly one origin per output line; if that ever
    // disagrees, decline rather than produce a misaligned edit.
    if out_lines.len() != origins.len() {
        return None;
    }

    let selected: Vec<&str> = out_lines
        .iter()
        .zip(&origins)
        .filter(|(_, o)| **o >= start_line && **o <= end_line)
        .map(|(l, _)| *l)
        .collect();

    let mut new_text = String::new();
    for l in &selected {
        new_text.push_str(l);
        new_text.push_str(eol);
    }

    let start_byte = line_starts[start_line];
    let end_byte = if end_line + 1 < line_starts.len() {
        line_starts[end_line + 1]
    } else {
        raw.len()
    };
    if new_text == raw[start_byte..end_byte] {
        return Some(None);
    }
    Some(Some(RangeEdit { start_byte, end_byte, new_text }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::{Path, PathBuf};

    fn collect_typort(dir: &Path, out: &mut Vec<PathBuf>) {
        let Ok(rd) = std::fs::read_dir(dir) else {
            return;
        };
        for e in rd.flatten() {
            let p = e.path();
            if p.is_dir() {
                collect_typort(&p, out);
            } else if p.extension().map(|x| x == "typort").unwrap_or(false) {
                out.push(p);
            }
        }
    }

    /// The headline safety property, over the real example corpus: formatting
    /// must preserve the token stream, the comments, the string literals, and
    /// be idempotent.
    #[test]
    fn corpus_preserves_tokens_comments_strings_and_is_idempotent() {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples");
        let mut files = Vec::new();
        collect_typort(&root, &mut files);
        assert!(!files.is_empty(), "no .typort files under {}", root.display());

        let opts = FormatOptions::default();
        for f in &files {
            let src = std::fs::read_to_string(f).unwrap();
            let out = match format_document(&src, &opts) {
                Some(o) => o,
                None => panic!("declined to format {}", f.display()),
            };
            assert_eq!(token_signature(&src), token_signature(&out), "token stream changed: {}", f.display());
            assert_eq!(comment_signature(&src), comment_signature(&out), "comments changed: {}", f.display());
            assert_eq!(string_signature(&src), string_signature(&out), "strings changed: {}", f.display());
            assert_eq!(
                format_document(&out, &opts).as_deref(),
                Some(out.as_str()),
                "not idempotent: {}",
                f.display()
            );
        }
    }

    #[test]
    fn range_format_touches_only_selected_lines() {
        let src = "def a = 1\ndef b = {\nx\n}\ndef c = 2\n";
        let edit = format_range(src, &FormatOptions::default(), 1, 3)
            .expect("declined")
            .expect("expected a change");
        assert_eq!(edit.new_text, "def b = {\n    x\n}\n");
        assert_eq!(&src[edit.start_byte..edit.end_byte], "def b = {\nx\n}\n");
    }

    #[test]
    fn range_format_no_change_is_none() {
        let src = "def a = 1\ndef b = 2\n";
        assert!(format_range(src, &FormatOptions::default(), 0, 1)
            .expect("declined")
            .is_none());
    }

    /// Selecting every line must reproduce the full-document formatting: this
    /// exercises the output-line -> source-line origin mapping over the corpus.
    #[test]
    fn whole_file_range_matches_full_format() {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples");
        let mut files = Vec::new();
        collect_typort(&root, &mut files);
        let opts = FormatOptions::default();
        for f in &files {
            let src = std::fs::read_to_string(f).unwrap();
            let full = format_document(&src, &opts).unwrap_or_else(|| panic!("declined {}", f.display()));
            match format_range(&src, &opts, 0, usize::MAX) {
                Some(Some(e)) => assert_eq!(e.new_text, full, "range/full mismatch: {}", f.display()),
                Some(None) => assert_eq!(full, src, "range/full mismatch: {}", f.display()),
                None => panic!("range declined {}", f.display()),
            }
        }
    }

    #[test]
    fn declines_oversized_and_unterminated() {
        let opts = FormatOptions { max_bytes: 8, ..Default::default() };
        assert!(format_document("def averylongname = 1\n", &opts).is_none());
        assert!(format_document("def a = \"unterminated\n", &FormatOptions::default()).is_none());
        assert!(format_document("def a = /* unterminated\n", &FormatOptions::default()).is_none());
    }

    #[test]
    fn crlf_is_preserved() {
        let src = "def a = 1\r\ndef b = 2\r\n";
        let out = format_document(src, &FormatOptions::default()).unwrap();
        assert!(out.contains("\r\n"), "expected CRLF output, got {out:?}");
    }
}
