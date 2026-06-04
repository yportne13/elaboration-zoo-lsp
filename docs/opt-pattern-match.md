# Pattern Match Optimization Notes

## Current State (2026-06-03)

`filter_accessible_constrs` fast-path added (e8bcbd9):
- Non-indexed sum types (Expr, Bool, Option) → skip GADT reachability analysis
- Indexed types (Vec[A](len: Nat)) → still do full unification-based check
- Benchmark: 7.18s → 4.91s (-32%)

## Future Optimizations

### ② Pre-compute constructor types at declaration time

**Problem:** `filter_accessible_constrs` calls `infer_expr` for each constructor to
re-derive its function signature (parameters, return type) every time the function
is called. This is redundant — the constructor's type structure is fixed at
declaration time.

**Idea:** Store a pre-computed signature for each constructor at declaration time:
- The constructor's Pi-type (parameter types)
- Which parameters are Expl vs Impl
- The constructor's return type (the Sum type it belongs to)

Then `filter_accessible_constrs` can skip `infer_expr` entirely and work with
pre-computed metadata directly.

**Trade-off:** More memory per constructor declaration. Only helps for indexed
types (non-indexed already fast-pathed). May be moderate benefit since `infer_expr`
on constructors is relatively cheap (just type lookup).

### ③ Structural equality instead of full unification

**Problem:** `filter_accessible_constrs` uses `check_pm` (full unification) to
determine if a constructor can inhabit the matched type. For GADT indices like
`Vec[A](len: Nat)`, the check is essentially structural:
- `nil` returns `Vec(A)(0)`, matched type is `Vec(A)(succ len)` → 0 ≠ succ len → NO
- `cons` returns `Vec(A)(succ n')`, matched type is `Vec(A)(succ len)` → unify n' ≈ len → YES

Full unification is overkill — we just need a **structural equality check** on
the index spine: does `0 === succ _`? No. Does `succ _ === succ _`? Yes, with
fresh sub-metavariables.

**Idea:** Replace `check_pm` with a lightweight structural comparison for the
index-level terms:
1. Extract the return type of the constructor (fully applied with holes)
2. Extract the type indices of the match target
3. Do a structural walk comparing corresponding indices:
   - Same head constructor → recurse into subterms
   - Different head constructors (0 vs succ) → unreachable
   - Metavariable / neutral → reachable (could be anything)

This avoids creating full `Infer` state, saves unification overhead, and
sidesteps side-effects on the meta store.

**Trade-off:** Only applies to simple GADT-like indexing. Full unification is
still needed for complex cases (type functions, overlapping indices). Would
need a fallback to `check_pm` when structural check can't decide.

---

## Implementation Priority

① Already done — lift call out of arm loop (e8bcbd9 + current changes).

② After ① — moderate gain, more code complexity.

③ After ① — potentially large gain, need careful design to handle edge cases.
