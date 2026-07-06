# Parser Error Reporting & Recovery — Upgrade Notes

## Motivation

Upgrade the L13 (Typort) parser's error reporting and recovery to be
more like chumsky.  This document tracks design decisions, remaining
ideas, and the gap between the current hand-written parser library
and a principled error-recovery system.

---

## Fixes Already Applied

### Delimiter wrappers eating declaration separators (Jul 2026)

**Problem.**  `paren_cut`, `square_cut` and `brace` used a separate
`kw(EndLine).option()` element *after* the inner content but *before*
the closing delimiter token.  When the closing delimiter was missing,
this `EndLine.option()` consumed the newline that separated
declarations, so the next `def`/`enum`/`struct` was treated as
misplaced content inside the malformed group rather than as a fresh
declaration.

Example input:
```typort
def foo: Nat = (1 + 2

def bar: Nat = 3
```

`def bar` was silently dropped; two errors (both at `def`) were
reported.

**Fix.**  Group the trailing `kw(EndLine).option()` together with
the closing delimiter into a *single* Cut element:

```rust
// Before (4 elements)
Cut((kw(LParen), kw(EndLine).option(), p, kw(EndLine).option(), kw(RParen)))

// After (3 elements) — trailing EndLine and RParen are one element
Cut((kw(LParen), kw(EndLine).option(), p, (kw(EndLine).option(), kw(RParen))))
```

When the grouped element fails, the Cut macro's terminating arm
returns `($input, None)` — the input **before** the element ran,
so the EndLine is never consumed.  The declaration separator is
preserved.

Likewise, group the **leading** `kw(EndLine).option()` (between
opening delimiter and content) with the inner parser for symmetry:

```rust
Cut((kw(LParen), (kw(EndLine).option(), p), (kw(EndLine).option(), kw(RParen))))
    .map(|c| c.1.map(|(_, result)| result))
```

Affected functions: `paren_cut`, `square_cut`, `brace`.

---

## Remaining Ideas (not yet implemented)

### 1. Nested-delimiter-aware `skip_until_decl`

The current `skip_until_decl` scans forward for `EndLine` followed by
a declaration keyword (`def`, `enum`, …).  It does **not** account for
delimiter nesting:

```
fn skip_until_decl(input) {
    input.iter()
        .enumerate()
        .find(|(i, t)| {
            t.data.1 == EndLine
                && input.get(i + 1).map(|next| is_decl_kw(next.data.1)).unwrap_or(false)
        })
        .map(|(i, _)| &input[i..])
}
```

A chumsky-style `nested_delimiters` recovery would track the nesting
depth of `()`, `[]`, `{}` while skipping:

```rust
fn skip_until_decl_nested(input) -> Option<&[TokenNode]> {
    let mut depth: i32 = 0;
    for (i, tok) in input.iter().enumerate() {
        match tok.data.1 {
            LParen | LSquare | LCurly => depth += 1,
            RParen | RSquare | RCurly => {
                depth -= 1;
                if depth < 0 {
                    // Closing bracket without matching open — sync point
                    return Some(&input[i..]);
                }
            }
            EndLine if depth == 0 => {
                // Outside any brackets — check for decl separator
                if input.get(i + 1)
                    .map(|next| matches!(next.data.1, DefKeyword | StructKeyword | …))
                    .unwrap_or(false)
                {
                    return Some(&input[i..]);
                }
            }
            _ => {}
        }
    }
    None
}
```

**Why this helps.**  When a `(` is never closed, the parser can skip
forward without being confused by `\n` inside the unclosed group.
It only treats `\n` as a declaration separator when `depth == 0`.

**Integration.**  `skip_until_decl_nested` is a drop-in replacement
for the `skip` parameter of `recover_with` — no other change needed.

### 1b. `skip_until_decl` should not match at the current position

`skip_until_decl` can return the **same** position as its input when
the very first token is `EndLine` followed by a declaration keyword.
This causes `recover_with` to return `Ok((input, fallback))` without
making progress, relying on the separator (`kw(EndLine)`) in
`many1_sep` to advance.  The error IS pushed to state, but the
"recovery" is spurious — the parser hadn't actually consumed
anything invalid.

Fix: skip position 0 when scanning:

```rust
fn skip_until_decl(input) {
    input.iter()
        .enumerate()
        .skip(1)  // don't match at the current position
        .find(|(i, t)| { ... })
        .map(|(i, _)| &input[i..])
}
```

### 2. Error merging for `.or()`

The current `.or()` combinator silently discards the first alternative's
error:

```rust
fn or<P>(self, rhs: P) -> impl Parser<I, A, S, E> {
    move |input, state| self.parse(input, state)
        .or_else(|_| rhs.parse(input, state))
}
```

chumsky's `or()`:
- Compares *farthest progress* offset — which branch consumed more
  input before failing?
- If both fail at the same offset, *merge* their `expected` sets.
- Results in errors like `expected ')' or ']' or keyword 'def'`
  instead of just `expected ')'`.

### 3. `found` tracking

Current errors only store *what was expected*, not *what was actually
found*.  chumsky's `Rich` stores both:

```rust
// Current
Expect(RParen)                         // "expected ')'"

// chumsky-style
expected ')' found `def`               // "expected ')', found `def`"
```

This requires storing the actual token (or its text) in the error.

### 4. Nested context stacking

`ErrMsg` currently has a single level of context:

```rust
enum ErrMsg {
    Base(BaseMsg),           // Expect(RParen)
    In(Ctx, BaseMsg),        // In(Expr, Expect(RParen))
}
```

The `extract_base` helper strips inner context when wrapping:
```rust
// In(Atom, In(Expr, Expect(RParen)))  →  In(Atom, Expect(RParen))
//                                      ← Ctx::Expr lost!
```

chumsky can stack multiple labels:
```
while parsing expression
while parsing atom
in definition of `foo`
  └─ expected ')'
```

To support stacking without losing `Copy`, the context stack could be a
small array or use `SmallVec` instead of `Box`.

### 5. Operator precedence in `infix_binding_power`

`infix_binding_power` has a catch-all fallback that gives `(7, 8)` to
any unrecognised operator (line 741).  This means `@` (lexed as `Op`)
gets a binding power and is treated as a real infix operator, producing
two identical `In(Atom, Expect(LParen))` errors instead of one.

**Fix:** change the fallback from `(7, 8)` to `return None` so that
unrecognised operators are ignored by the expression parser.

---

## Current Architecture vs chumsky — Comparison

| Aspect | Current (`parser_lib_resilient.rs`) | chumsky 0.9 |
|--------|--------------------------------------|--------------|
| Parser trait | `parse(&self, I, &mut S) -> Result<(I, A), E>` | `parse(&self, I) -> Result<(I, O), ParseError<I, E>>` |
| State | `&mut S` — fully generic | `&mut C` — constrained trait |
| Error type | Fully polymorphic `E` | `E: ParserError<I>` with merge/label/expect |
| Cut / recovery | `Cut<P>` + `recover_with` | `nested_delimiters` + `skip_then_retry_until` |
| Error merging | None (discards first err) | Automatic in `or()` |
| Context | Single level (`In(Ctx, BaseMsg)`) | Stackable `.context("…")` labels |
| Expected/found | Expected only | Both expected and found |
| Diagnostic output | `format!("{:?}")` (raw enum) | `Rich` with source snippets (via `codespan-reporting`) |
