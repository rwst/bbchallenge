# Option C: Era-based progress predicate

## Core idea

Instead of a structural invariant on arbitrary `MacroConfig`s, define the progress predicate to match only configs that arise at **era boundaries**. An era is the period between two successive `era_complete` events, corresponding to one full sweep cycle plus bounces.

**Key insight**: era boundaries are the ONLY place where the orbit is "simple" — everything else is transient sweep/bounce steps. By restricting `P` to era-start configs, we avoid the complex intermediate states that cause the Mersenne cascade.

## Current orbit structure (from 10M-step simulation)

Era boundaries observed (M config after era_complete):

```
Era 0: M [] 6 []                           (step 24, sum=6)
Era 1: M [] 12 []                          (step 89, sum=12)
Era 2: M [6,11] 7 []                       (step 546, sum=24)
Era 3: M [7,2,18] 11 []                    (step 1852, sum=38)
Era 4: M [7,2,7,7] 23 []                   (step 2767, sum=46)
Era 5: M [7,2,41] 8 []                     (step 3908, sum=58)
Era 6: M [24,12] 30 []                     (step 5935, sum=66)
Era 7: M [24] 52 []                        (step 6732, sum=76)
Era 8: M [39,34] 23 []                     (step 19088, sum=96)
Era 9: M [13,8,19,39,15] 14 []             (step 28629, sum=108)
...
```

**Observation**: All era-start configs have `R = []`. This is because `era_complete` produces `M L (a+6) []`. The first macro step of the next era is a sweep (solo or right_empty) that creates R=[1].

## Revised predicate

```lean
def EraStart (c : Config 6) : Prop :=
  ∃ L c', c = M_Config L c' [] ∧ AllGe1 L ∧ c' ≥ 6
```

Or more precisely, after the first sweep:

```lean
def EraPlusSweep (c : Config 6) : Prop :=
  ∃ L c', c = M_Config L c' [1] ∧ AllGe1 L ∧ L ≠ [] ∧ c' ≥ 4
```

The second form has `L ≠ []` (from sweep_right_empty output `(a+1)::L'` or sweep_solo output `[1]`) and `c' ≥ 4` (from `a+4` where a is from `era_complete`'s `a+6`). This avoids the `L = []` edge cases entirely.

## Proof architecture

### Phase 1: Define `EraPlusSweep` and show initial config reaches it

```lean
-- Starting point: M [1] 4 [1] at step 43 (current)
-- This IS an EraPlusSweep state: L=[1]≠[], c=4≥4, R=[1]
theorem init_reaches_era : EraPlusSweep (run sweeper (initConfig 6) 43) := ...
```

### Phase 2: Show each EraPlusSweep reaches another EraPlusSweep

This is the main progress theorem, replacing `macro_progress`:

```lean
theorem era_progress (c : Config 6) (h : EraPlusSweep c) :
    ∃ k, 0 < k ∧ EraPlusSweep (run sweeper c k) ∧ (run sweeper c k).state ≠ none
```

### Phase 3: Wire into `sweeper_never_halts`

Same pattern as current:
```lean
nonhalt_of_progress sweeper EraPlusSweep era_progress
```

## Key sub-proofs needed

### Proof that EraPlusSweep → next EraPlusSweep

Given `M L c [1]` with `L ≠ [], AllGe1 L, c ≥ 4`, show there exists k > 0 such that after k steps, we reach another `M L' c' [1]` with same properties.

The path within one era:
1. Start: `M L c [1]` (cursor ≥ 4)
2. Sweep down until c=2 (even path) or c=3 then sweep+shift (odd path)
3. Eventually reach `M0 L' R'` with various R' structures
4. R' gets processed via bounces: zero_bounce, zero_two, multi_bounce
5. Eventually reach `M0 L'' [1]` (era complete trigger)
6. era_complete: `M L''.tail (L''.head+5) []` (with R=[])
7. First sweep: `M ((L''.head+1)::L''.tail') (L''.head+3) [1]`  — this is the NEW EraPlusSweep

**Problem**: Step 2-5 involve many macro transitions and intermediate configs. We need to show the orbit flows through all of them WITHOUT halting.

### Sub-lemma: "era progress" via explicit reduction

```lean
theorem era_step (L : List Nat) (c : Nat) (hL : L ≠ []) (hAll : AllGe1 L) (hc : c ≥ 4) :
    ∃ k L' c', 0 < k ∧
      run sweeper (M_Config L c [1]) k = M_Config L' c' [1] ∧
      L' ≠ [] ∧ AllGe1 L' ∧ c' ≥ 4
```

This is the heart of the proof. It would be proven by **induction on `c + sum(L) + sum(R)`** (strong induction) or by **direct computation** of the era's macro transitions.

**Challenge**: the number of macro steps in one era depends on `L` and `c`. For each specific `L`, `c`, we can compute it, but the general case requires reasoning about the dynamics.

## Feasibility assessment

### What's hard

The era's dynamics involve:
- Multiple sweep cycles (each decrementing c by 2, incrementing L.head and R.head)
- Shifts when c reaches 1 (for odd c starts)
- Bounces at R's zero-markers
- Multi-bounce through R's run sequence

Expressing this as a single Lean function or theorem is non-trivial.

### What's easier

- Each INDIVIDUAL macro step is already proven
- The `mk_progress_M`, `multi_bounce_progress`, etc. helpers chain them
- We don't need to prove for ALL configs, only era boundaries

### Key observation that helps

**The macro transitions within an era form a linear sequence**: each step is deterministic given the current config. There's no branching until we hit an `M0 L [1]`. So an era is a well-defined function `era : MacroConfig → MacroConfig`.

If we can **define this function in Lean** (recursively on the run-length structure), we can prove `era_step` by:
1. Showing the function terminates
2. Showing each step of the function corresponds to one proven macro transition
3. Showing the final result has the EraPlusSweep structure

## Concrete plan

### Step 1: Define `era` function at macro level
```lean
-- Process one era by macro transitions, returning the next M L c [1] config
def macroEra (L : List Nat) (c : Nat) : List Nat × Nat
```
This function recurses on L and c, simulating the orbit's macro-level dynamics. Must prove termination (via `c + sum L` as a measure, for example).

### Step 2: Prove `macroEra` corresponds to actual runs
```lean
theorem macroEra_spec (L c R) (hpre : ...) :
    let (L', c') := macroEra L c
    ∃ k > 0, run sweeper (M_Config L c [1]) k = M_Config L' c' [1]
```

### Step 3: Show EraPlusSweep properties are preserved
```lean
theorem macroEra_preserves (L c) (hpre) :
    let (L', c') := macroEra L c
    L' ≠ [] ∧ AllGe1 L' ∧ c' ≥ 4
```

### Step 4: Wire everything into `era_progress`
```lean
theorem era_progress (c : Config 6) (h : EraPlusSweep c) : ... :=
  obtain ⟨L, c', hc, hL, hAll, hc'⟩ := h
  subst hc
  let ⟨L', c'', hk_pos, hrun⟩ := macroEra_spec ...
  ...
```

### Step 5: Replace macro_progress with era_progress in sweeper_never_halts
```lean
theorem sweeper_never_halts (k : Nat) :
    (run sweeper (initConfig 6) k).state ≠ none := by
  suffices h43 : ∀ j, j < 43 → ... by
    by_cases hk : k < 43
    · exact h43 k hk
    · rw [show k = 43 + (k - 43) from by omega, run_add]
      exact nonhalt_of_progress sweeper EraPlusSweep era_progress
        (run sweeper (initConfig 6) 43) init_era_plus_sweep (k - 43)
  intro j hj; interval_cases j <;> simp [run, step, sweeper, initConfig]
```

## Effort estimate

- **Step 1** (define `macroEra`): 2-4 hours. Main work: identifying the recursion structure.
- **Step 2** (correctness): 4-8 hours. Inductive proof chaining macro transitions.
- **Step 3** (invariant preservation): 1-2 hours. Straightforward once `macroEra` is defined.
- **Step 4** (wiring): 1 hour.
- **Step 5** (replace macro_progress): 30 min.

**Total**: 8-15 hours. Significant but bounded.

## Risks

1. **Termination measure**: the `macroEra` function needs a decreasing measure on `L, c`. The era's duration depends on `c` and the number of runs, but may not be simply `c + sum L`. May need well-founded recursion with a custom measure.

2. **Multi-bounce complexity**: when R has multiple runs, the bounce cascade is complex. The existing `macro_multi_bounce_general` theorem handles this, but we need to invoke it correctly within `macroEra`.

3. **Cursor parity**: the era's structure depends on `c` parity. Odd c requires shifts, even c goes directly to M0. `macroEra` must branch on parity.

## Alternative simpler variant

Instead of defining `macroEra` explicitly, use an **inductive predicate** `EraReaches L c L' c'` that captures "after one era from (L, c), we reach (L', c')". Then prove by strong induction on the era's structure.

```lean
inductive EraReaches : List Nat → Nat → List Nat → Nat → Prop where
  | ... -- constructors for each macro transition
```

This is slightly less direct but avoids the termination proof.

## Decision

**Proceed with Option C** via:
1. Define `EraPlusSweep` predicate (~15 min)
2. Define `macroEra` using well-founded recursion OR inductive predicate (~4 hours)
3. Prove correctness via macro transition chaining (~6 hours)
4. Wire into `sweeper_never_halts` (~1 hour)

**Timeline**: 1-2 focused sessions.

**Fallback**: If `macroEra` becomes too complex, retreat to the existing `macro_progress` approach with 4 Mersenne sorries documented as axiomatic reachability assumptions.
