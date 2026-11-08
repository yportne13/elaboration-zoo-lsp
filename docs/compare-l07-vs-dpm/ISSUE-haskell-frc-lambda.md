# 【Issue 草稿】Forcing a bare lambda diverges: normal forms containing λ cannot be printed, and function-typed conversions loop

> 仓库：`KonjacSource/dpm-nbe`（Haskell）· 版本：**已拉取最新 `4516cf5`（2026-10-31 fetch）复核，缺陷仍存在；该版本相对 `ed5fa07` 只改了 `src/Elab.hs` 一行，`src/Eval.hs` 未动**
> 状态：**未提交**（本机无法联网，见文末）。下面内容可直接粘贴到 GitHub New issue。

---

**Title**

`frc` on a bare lambda diverges — printing a normal form that is a λ, and conversion of function-typed terms, both loop forever

**Body**

### Summary

Forcing a value that is a lambda with an empty spine loops forever. Since both `quote` (printing) and `conv` (conversion) force their arguments, this means:

1. `nf`/printing never terminates for any program whose normal form contains a λ;
2. checking `refl` against `Id (A -> B) f g` never terminates (function-typed indices cannot be eliminated);
3. the repository's own examples hide this because every example ends in `; U`, so the normal form is never a λ.

The base code comes from elaboration-zoo, where the same shape exists; the Rust port `dpm-nbe-rs` documents and fixes it as deviation 1 in its `NOTES.md`, but this repository has no issue/commit for it.

### Environment

- `4516cf5` (latest, 2026-10-31 fetched; verified the hang still reproduces), GHC 9.10.2, `cabal`/stack per `stack.yaml` (lts-24.3)
- Verified by compiling `src/` (`Syntax`, `Subst`, `Eval`, `Context`, `Elab`, `Pretty`) against a `Text.Megaparsec` stub that only provides `SourcePos`/`initialPos` (the module is used only for source positions in these files), and constructing `Raw` directly so the behaviour does not depend on the parser. The same programs hang through the official CLI.

### Reproductions

All three hang (no output, CPU spinning). Use `timeout 10` to confirm.

**R1 — printing a λ (evaluation itself is fine)**

```sh
$ echo 'let pr : (Nat -> Nat) -> Nat -> Nat = \ f x . f x; pr' | timeout 10 cabal run dpm-nbe -- nf
# expected (after the fix):  λ f x . f x   :  (Nat -> Nat) -> Nat -> Nat
# actual:  hangs
```

`infer` returns in ~10 ms; only `nf` hangs, i.e. the loop is in `frc`/`quote`, not in elaboration.

**R2 — conversion of two lambdas (stronger: this is a typing gap)**

```sh
$ echo 'let f : Id (Nat -> Nat) (\ x . x) (\ x . x) = refl; f' | timeout 10 cabal run dpm-nbe -- nf
# expected:  refl  :  Id (Nat -> Nat) (λ x . x) (λ x . x)
# actual:  hangs
```

**R3 — same with a let-bound function**

```sh
$ echo 'let h : (n : Nat) -> Nat = \ n . n; let e : Id ((n : Nat) -> Nat) h h = refl; e' | timeout 10 cabal run dpm-nbe -- nf
# actual: hangs
```

**Control** — a normal form without λ works, so the evaluator/printer is otherwise fine:

```sh
$ echo 'let x : Nat = plus (suc zero) (suc zero); x' | cabal run dpm-nbe -- nf
succ (succ zero)
  :
Nat
```

### Root cause

`src/Eval.hs`:

```haskell
-- line 106
napp v sp = case frc v of
  v | len sp == 0 -> progress v                 -- (1) too late: v is already forced
  ...

-- line 82
frc = \case
  ...
  NLam ps n cl sp -> frc $ napp (VNe $ NLam ps n cl Sp) (frc sp)   -- (2) re-enters itself
```

Call chain for a bare lambda value (`sp = Sp`):

`frc (VNe (NLam … Sp))` → `frc (NLam … Sp)` → `frc (napp (VNe (NLam … Sp)) Sp)`
→ in `napp`, the scrutinee `frc v` is evaluated **before** the `len sp == 0` guard (the guard is a pattern-guard on the *result* of `case frc v of`, not a guard on the function), so we loop.

Because `quote` (`quoteNe`) and `conv` both start by forcing, printing and conversion inherit the loop.

### Proposed fix (minimal, verified)

A lambda with an empty spine is already in weak-head normal form:

```diff
 instance Force Ne Val where
   frc = \case
     NSub n sb       -> frcS sb n
     NVar v sp       -> VNe $ NVar v (frc sp)
-    NLam ps n cl sp -> frc $ napp (VNe $ NLam ps n cl Sp) (frc sp)
+    NLam ps n cl sp | len sp == 0 -> VNe $ NLam ps n cl sp
+                    | otherwise   -> frc $ napp (VNe $ NLam ps n cl Sp) (frc sp)
     NPlus u v       -> frc $ plus (frc u) (frc v)
```

With this patch applied to a copy of `src/` (original tree untouched) and recompiled, all of R1–R3 return immediately:

| program | before | after |
|---|---|---|
| R1 `pr` | hang | `λ f x . f x : (Nat -> Nat) -> Nat -> Nat` (12 ms) |
| R2 `f` | hang | `refl : Id (Nat → Nat) (λ x . x) (λ x . x)` |
| R3 `e` | hang | `refl : Id ((n : Nat) → Nat) (λ n . n) (λ n . n)` |
| control | ok | ok |

The fix is semantically transparent: `frc` only unfolds delayed substitutions/neutrals, and an `NLam` with an empty spine is already a value.

### Related (separate) defect exposed by the fix

After the fix, R4 reaches a second, independent hole — `Tm.Bot` has no case in `eval`:

```sh
$ echo 'let C : (A : U) -> Id Nat (suc zero) zero -> A = \ A (!); C' | cabal run dpm-nbe -- nf
# after the fix:  "eval: impossible" (CallStack)
# expected:      λ A (!) . ⊥  :  (A : U) -> Id Nat (suc zero) zero -> A
```

(Suggested in a separate issue: give `Bot` a value, as the Rust port does with `Val::Bot`.)

### Notes

- The derivative Rust port documents exactly this as deviation 1 (`dpm-nbe-rs/NOTES.md`): *"With an empty spine, `napp` forces its argument, which is again this lambda, so `frc` of a bare lambda value diverges … the original cannot even compare or print a lambda."* It fixes it with the same short-circuit.
- A second, closely related port deviation 3 is worth checking once the loop is gone: printing a **partially applied** lambda drops the arguments already applied in the original (the port saturates it with canonical arguments instead).

---

## 提交状态

- [ ] 未提交：本机 `git fetch`（ghfast 镜像）与直连 github.com 均超时，`gh` CLI 未安装，`web_fetch/web_search` 在本次会话中不可用（provider 配置报错）。
- 待办：联网后用 `gh issue create --repo KonjacSource/dpm-nbe --title ... --body-file <此文件>` 提交；若上游 HEAD 已变，把版本号改成最新 commit。
- 复核清单（提交前）：① 用官方 `cabal run` 复跑 R1–R3；② 确认上游是否已有同题 issue；③ 决定 R4（Bot）是否并入本 issue。
