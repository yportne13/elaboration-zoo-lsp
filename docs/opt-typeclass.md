# Typeclass Resolution Optimization Notes

## Problem 1: Linear scan in assertion_table (SOLVED)

`find_assertion_entry` scanned `assertion_table` (a `Vec`) linearly with
`vals_eq_ground` structural comparison. Fixed by carrying `assertion_idx` through
`GeneratorNode` and `ConsumerNode`, eliminating the lookups in the goal-solved path.

## Problem 2: `clean()` discards all cached work

### Current behavior

`trait_wrap` in `elaboration.rs` calls `clean() + synth()` in two places:

```
Line 1102: Code completion for `t.data.is_empty()`
Line 1162: Method resolution filter per trait
```

Both use the pattern:

```rust
self.trait_solver.clean();
self.trait_solver
    .synth(Assertion { name: x.clone(), arguments: [typ_raw, wildcard, ...] })
    .is_some()
```

### Why it's wasteful

`synth()` is a full tabled resolution engine with assertion tables, generator stacks,
and a loop. But in these call sites, the wildcard `Flex(MetaVar(u32::MAX), [])`
matches the FIRST instance's pattern instantly, so `synth()` always returns after
one iteration. The entire table construction/teardown is purely overhead.

In effect, `synth()` is being used as a trivial membership test: "does this trait
have ANY instance whose Self type matches `typ_raw`?"

For `hdl-verilog.typort` with ~15 traits and ~40 instances, this means per method
lookup:
- ~15 × clone-all-instances per trait
- ~15 × table construction + generator push + cleanup

### Proposed fix

Add a lightweight `can_satisfy(&self, trait_name, typ_raw) -> bool` method to `Synth`
that directly checks instance patterns against `typ_raw` without building the
resolution table:

```rust
pub fn can_satisfy(&self, trait_name: &SmolStr, typ_raw: &Val) -> bool {
    let instances = match self.class_instances.get(trait_name) {
        Some(insts) => insts,
        None => return false,
    };
    let wildcard_val: Rc<Val> = Val::Flex(MetaVar(u32::MAX), List::new()).into();
    let out_params = self.trait_out_params.get(trait_name);

    for inst in instances {
        if inst.assertion.arguments.is_empty() { continue; }
        let mut subst = HashMap::new();
        let mut ok = true;
        for (i, i_arg) in inst.assertion.arguments.iter().enumerate() {
            let is_out = out_params
                .map(|op| op.get(i).copied().unwrap_or(false))
                .unwrap_or(false);
            let g_arg: &Val = if i == 0 && !is_out { typ_raw } else { &wildcard_val };
            if is_out && matches!(g_arg, Val::Flex(..)) { continue; }
            if !Self::val_match(g_arg, i_arg, &mut subst) {
                ok = false;
                break;
            }
        }
        if ok { return true; }
    }
    false
}
```

Replace `clean() + synth().is_some()` at both call sites with `can_satisfy()`.

### Not blocked by

`synth()` and `clean()` remain in place — they are used by L10/L11/L12 code paths
that still need the full resolution algorithm.

## Problem 3: No head-type index on instances

### Current state

`class_instances: HashMap<SmolStr, Vec<Instance>>` — instances are grouped only by
trait name. Finding instances for a specific Self type requires scanning all entries
in the `Vec`.

### Proposal

Add a secondary index: `HashMap<(SmolStr, SmolStr), Vec<usize>>` mapping
`(trait_name, self_type_head_constructor)` → indices into the instance Vec.
Use this for O(1) filtering before fallthrough `val_match`.

## Problem 4: `solve_trait` eagerly fully-elaborates every candidate instance

See separate analysis in discussion.

## Problem 5: `fresh_meta` eagerly calls `solve_trait`

When `fresh_meta` creates a meta with a trait type, it immediately attempts
instance resolution. This should be deferred to `solve_multi_trait` for
batched resolution after unification completes.
