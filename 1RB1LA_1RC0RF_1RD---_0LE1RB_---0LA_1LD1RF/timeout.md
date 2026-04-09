# Config whnf timeout: SOLVED ✓

## Solution that worked: `@[irreducible] toConfig` + split `mk_progress`

1. Mark `MacroConfig.toConfig` as `@[irreducible]` so Lean treats it as opaque
2. Add simp lemmas `MacroConfig.toConfig_M` and `MacroConfig.toConfig_M0` (proved by `rw [MacroConfig.toConfig]`)
3. Split `mk_progress` into `mk_progress_M` (taking explicit `L, c, R`) and `mk_progress_M0` (taking `L, R`), both returning progress proofs that avoid ever exposing the raw Config struct
4. Add `simp only [MacroConfig.toConfig_M]` / `simp only [MacroConfig.toConfig_M0]` as the first tactic in each branch of `macro_progress` to unfold the opaque `toConfig` once, after `cases cfg`
5. In `init_to_macro`, explicitly use `rw [MacroConfig.toConfig_M]` to unfold once

Result: **BUILD SUCCESS** with 5 sorries remaining (4 Mersenne + 1 last=2 compound). No more whnf timeouts.

Key insight: the `@[irreducible]` attribute stops the elaborator from eagerly unfolding `toConfig` when unifying types. Lean no longer tries to reduce complex Config structs to match against `(MacroConfig.M ...).toConfig` — instead it treats them as opaque and uses the simp lemmas explicitly when needed.

---

## Original problem statement (for reference)

## Problem statement

In `macro_progress`, we need to package `(k, htrans, hinv)` into `∃ k, 0 < k ∧ MacroProg (run sweeper c₀ k) ∧ (run sweeper c₀ k).state ≠ none` where:

- `htrans : run sweeper c₀ k = cfg'.toConfig`
- `cfg'.toConfig` reduces to `M_Config L' c' R'` or `M0_Config L' R'`
- For some cases (multi_bounce), the RHS contains complex list expressions: `M_Config (R_mid.reverse ++ (r'+1)::(a+4)::L') (last''+2) [1]`

Any operation that exposes the full Config struct to whnf times out:
- `htrans ▸ proof` — transfers proof along equation, triggers whnf
- `rw [htrans]` — rewrites goal, triggers whnf
- `congr_arg Config.state htrans` — applies `.state` to both sides, triggers whnf
- `refine ⟨_, htrans, _⟩` when `cfg'` is a metavariable — unification triggers whnf

Root cause: `M_Config L c R` unfolds to a Config struct whose `left` field contains `ones(c-1) ++ false :: runs L`. When L contains `R_mid.reverse ++ ...`, Lean's whnf tries to reduce `runs(R_mid.reverse ++ ...)` through the `runs` recursion, hitting the 200k heartbeat limit.

## Current state (machine.lean)

5+ sorries, 0 errors. The M_Config dispatch in macro_progress works fine (simple Configs). The M0 dispatch works for single-R cases. The multi_bounce sub-cases and the `mk_progress` helper's state-proof are sorry'd.

```
mk_progress: sorry on state ≠ none proof
multi_bounce_progress (last ≥ 3): sorry
multi_bounce_to_zero_progress (last = 1): sorry
macro_progress M0 multi_bounce last=2: sorry (compound needed)
invariant_sweep_and_shift Mersenne: sorry
invariant_zero_bounce_and_shift Mersenne: sorry
invariant_zero_two_solo Mersenne: sorry
invariant_zero_two Mersenne: sorry
```

## Solution ratings

### 1. Custom BusyLean tactic — Plausibility HIGH, Efficiency HIGH
A `close_macro_progress` tactic that builds the tuple via syntax manipulation, bypassing the elaborator's unification. Reusable across TMs.

**Pros**: clean long-term, reusable
**Cons**: metaprogramming learning curve
**Effort**: ~2-4 hours

### 2. Verified program via reflection — Plausibility LOW
Doesn't fit: the bottleneck is elaboration perf, not a decidable computation.

### 3. `@[irreducible] MacroConfig.toConfig` — Plausibility HIGH, Efficiency HIGH
Make `toConfig` opaque so Lean treats `(MacroConfig.M L c R).toConfig` as a black box. Combined with simp lemmas for the cases that actually need expansion.

**Pros**: one-line attribute change
**Cons**: breaks any proof that implicitly relied on `toConfig` unfolding
**Effort**: ~30 min to try

### 4. Pre-proven state lemmas + simp — Plausibility HIGH, Efficiency HIGH
```lean
@[simp] lemma M_Config_state (L c R) : (M_Config L c R).state = some stA := rfl
@[simp] lemma M0_Config_state (L R) : (M0_Config L R).state = some stA := rfl
```
Then `by rw [htrans]; simp` closes state goals without touching left/right.

**Pros**: zero metaprogramming
**Cons**: still needs `rw [htrans]` which may itself timeout
**Effort**: ~15 min to try

### 5. Black-box wrapper — Plausibility HIGH, Efficiency HIGH
Define an `@[irreducible]` predicate that packages the transition+invariant opaquely.

**Pros**: clean boundary
**Cons**: need helper lemmas for construction/destruction
**Effort**: ~1 hour

### 6. `@[irreducible]` on `M_Config`/`M0_Config` — Plausibility MEDIUM, Efficiency HIGH
Mark the raw Config constructors as irreducible. Prevents ALL unfolding.

**Pros**: strongest opacity
**Cons**: may break the macro transition THEOREMS which unfold M_Config/M0_Config to apply simp
**Risk**: HIGH — many existing proofs may break
**Effort**: ~1 hour + recovery from breakage

## Attempts and failures

### Attempt A: `htrans ▸ (by rw [MacroConfig.toConfig_state]; ...)`
Result: timeout on `▸` — rewrites goal, triggers full whnf.

### Attempt B: `congr_arg Config.state htrans`
Result: timeout — `congr_arg` elaborates `Config.state` applied to the Config equality, triggering struct reduction.

### Attempt C: `state_ne_of_M_Config` helper with `subst h`
Result: can't `subst` a non-variable (c₀ is `run sweeper ...`, not a free var).

### Attempt D: `state_ne_of_M_Config` with `rw [h]; simp [M_Config]`
Result: `rw [h]` triggers whnf on Config struct with complex list expressions.

### Attempt E: `@[reducible] MacroConfig.toConfig`
Result: worse — Lean tries harder to unfold, still times out elsewhere.

### Attempt F: `@[simp]` lemmas for `toConfig_M`/`toConfig_M0`
Result: `simp only [...] at htrans` changes htrans in one form, but then the `refine ⟨_, htrans, _⟩` elaboration still hits whnf when matching the tuple type.

### Attempt G: Explicit `cfg'` in call site with `have ht := ...`
Result: `ht` has type `... = M_Config ...` but the helper expects `... = (MacroConfig.M ...).toConfig`. Coercion triggers whnf. The ORIGINAL pattern `mk_progress K (.M ...) _ (transition) (inv)` worked because `cfg'` and `transition` were unified simultaneously.

## Next steps

1. **Try #3 (@[irreducible] on toConfig)** — lowest effort, may just work
2. If that fails: **try #4 (state simp lemmas) combined with explicit `.M` annotations** at call sites
3. If that fails: **escalate to #1 (custom tactic)**

## Configuration details

- Lean version: `leanprover-community/mathlib4`, toolchain `v4.29.0-rc8`
- Heartbeat limit: 200k (default); 400k didn't help for these specific cases
- File: `1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF/machine.lean`
- Split into `machine_base.lean` (stable, 1544 lines) and `machine.lean` (fast iteration, ~180 lines)

## What we know works

- Simple `mk_progress` calls with `.M0 [1] ((d+1)::R')` etc. (no list-reverse) compile fine
- The M_Config dispatch fully works
- The M0 single-element R dispatch fully works
- Only the multi_bounce sub-cases fail due to `R_mid.reverse ++ ...`

## Key observation

The timeout is strictly correlated with the presence of `R_mid.reverse ++ ...` in the MacroConfig output. Any operation touching this expression via the Config struct times out. Simple list operations like `(d+1) :: R'` or `[1, 1]` don't cause issues.

This suggests the problem is specifically `runs(R_mid.reverse ++ (r'+1)::(a+4)::L')` — the `runs` function recurses on the list, and with `R_mid.reverse ++ ...` it can't short-circuit.
