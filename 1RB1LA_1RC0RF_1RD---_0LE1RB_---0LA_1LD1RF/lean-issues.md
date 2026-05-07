# Lean issues encountered (Sub-plan E.3′ cascade closure)

## Issue: `termination_by` doesn't propagate case-branch refinement of `cfg`

### Setting

Defining mutual `theorem`s in a `mutual` block:

```lean
mutual

theorem cascade_unreachable {cfg : MacroConfig}
    (h_bad : BadShape cfg) (h_or : OrbitReachable cfg) : False := by
  induction h_bad with
  | step h_bad' h_step ih => exact ih (h_or.step_macro h_step)
  | base R =>
    exact OrbitReachable.not_M_empty_3'_aux R h_or rfl
termination_by cfg.mr * 2 + 1

theorem OrbitReachable.not_M_empty_3'_aux (R : List Nat)
    {cfg : MacroConfig} (h : OrbitReachable cfg) (hcfg : cfg = .M [] 3 R) :
    False := by
  cases h with
  | step_macro h_prev h_step =>
    ...
    exact cascade_unreachable h_bad_pre h_prev
  | ...
termination_by macroMr R * 2

end
```

### The problem

In `cascade_unreachable`'s `BadShape.base R` case, after pattern-match
the case binder `R` is in scope, and `cfg` is refined to `MacroConfig.M
[] 3 R` definitionally. The recursive call
`OrbitReachable.not_M_empty_3'_aux R h_or rfl` typechecks because Lean
can see `cfg = .M [] 3 R` (the `rfl` works).

But Lean's **termination check** generates a goal where `cfg.mr` is
the OUTER signature's `cfg.mr`, not the case-refined one:

```
⊢ macroMr R * 2 < cfg.mr * 2 + 1
```

with `cfg` opaque. `omega` can't close because `cfg.mr` is unrelated
to `macroMr R` from omega's view.

The expected: with `cfg = .M [] 3 R`, `cfg.mr` reduces to
`(MacroConfig.M [] 3 R).mr = macroMr R` definitionally, so the goal
becomes `macroMr R * 2 < macroMr R * 2 + 1`, trivially true.

### Lean's view of the context

Looking at `decreasing_by`'s context (via diagnostic):

```
case base
R : List ℕ                                  -- outer R from `| base R =>`
h_or✝ : OrbitReachable (MacroConfig.M [] 3 R)
R✝ : List ℕ                                  -- fresh case binder!
h_bad : (_ : BadShape (MacroConfig.M [] 3 R✝)) ×' OrbitReachable (...)
                                              ^^^ uses R✝, not R!
⊢ macroMr R * 2 < cfg.mr * 2 + 1            -- uses outer R
```

There are TWO `R`s and TWO `cfg`s. Lean's termination check
re-pattern-matches `h_bad` introducing fresh case binders (`R✝`,
`cfg✝`), separate from the outer `R` (in scope from `induction h_bad
with | base R =>`).

The type unification `BadShape (M [] 3 R) = BadShape (M [] 3 R✝)` should
imply `R = R✝`, but Lean doesn't expose this as a hypothesis or
substitute one for the other in the goal.

### What we tried

#### 1. Direct `omega` (after `simp`)

```lean
decreasing_by
  simp only [MacroConfig.mr_M] at *
  omega
```

**Result**: `simp` warns "MacroConfig.mr_M unused" (because there's no
`(M [] 3 _).mr` pattern in the goal — only `cfg.mr`). `omega` fails
with counterexample `cfg.mr ≥ 0, macroMr R ≥ 0, macroMr R - cfg.mr ≥ 1`.

#### 2. Manual unfold via `cases h_bad ; rfl`

```lean
decreasing_by
  have h_unfold : cfg.mr = (MacroConfig.M [] 3 R).mr := by
    cases h_bad
    rfl
  rw [h_unfold]
  simp only [MacroConfig.mr_M]
  omega
```

**Result**: `rfl` fails: `(MacroConfig.M [] 3 R✝).mr` not definitionally
equal to `(MacroConfig.M [] 3 R).mr`. R and R✝ aren't unified.

#### 3. Explicit case binder with same name

```lean
decreasing_by
  cases h_bad with
  | base R' =>
    show macroMr R * 2 < (MacroConfig.M [] 3 R').mr * 2 + 1
    simp only [MacroConfig.mr_M]
    omega
  | step _ _ => sorry
```

**Result**: `omega` still fails: `macroMr R * 2 < macroMr R' * 2 + 1`
with `R` and `R'` separate.

#### 4. Match-based termination measure

```lean
termination_by
  match h_bad with
  | .base R => macroMr R * 2 + 1
  | .step _ _ => 0
```

**Result**: Lean error "MVar does not look like a recursive call: ℕ"
and "the dependent pattern matcher can solve the following kinds of
equations". The match expression isn't acceptable as a termination
measure form due to dependent typing.

#### 5. Helper `cuMeasure` function returning Nat

```lean
def cuMeasure {cfg : MacroConfig} (h_bad : BadShape cfg) : Nat :=
  match h_bad with
  | .base R => macroMr R * 2 + 1
  | .step _ _ => 0
termination_by cuMeasure h_bad
```

**Result**: Lean error "recursor `Sweeper.BadShape.casesOn` can only
eliminate into `Prop`". `BadShape` is in `Prop`; can't eliminate to
`Type` (Nat). Would need `BadShape` redefined in `Type`.

#### 6. `subst hcfg_eq` in body before recursive call

```lean
| base R =>
  have hcfg_eq : cfg = .M [] 3 R := rfl
  subst hcfg_eq
  exact aux ...
```

**Result**: `rfl` fails to typecheck `cfg = .M [] 3 R` even though it
typechecks elsewhere (e.g., as the `rfl` arg in the recursive call).

#### 7. Explicit `(cfg := .M [] 3 R)` annotation

```lean
| base R =>
  exact OrbitReachable.not_M_empty_3'_aux (cfg := .M [] 3 R) R h_or rfl
```

**Result**: doesn't propagate to termination check; same goal.

#### 8. `change` tactic in decreasing_by

```lean
decreasing_by
  change macroMr R * 2 < macroMr R * 2 + 1
  omega
```

**Result**: `change` fails: pattern not definitionally equal to target.

### Root cause analysis

Lean's `induction h_bad with | base R => ...` does refine `cfg` to `M
[] 3 R` definitionally for the BODY elaboration. But the
`termination_by` clause is processed in a SEPARATE elaboration scope
that uses the OUTER signature, not refined.

When the recursive call's measure is checked, Lean's termination
synthesis builds a `WellFoundedRecursion` / `WellFounded.fix` skeleton
where each function's args are bundled into PSigma. The case branches
introduce fresh names (R✝, cfg✝) inside this PSigma'd context, distinct
from the body's case binders.

The `rfl` in the body's recursive call works because Lean's
elaborator unifies the rfl's type against the case-refined `cfg = M []
3 R`. But the termination measure `cfg.mr * 2 + 1` is evaluated with
the unrefined cfg, producing the mismatch.

### Workaround currently in use

`sorry` in `decreasing_by` for both `cascade_unreachable` and
`OrbitReachable.not_M_empty_3'_aux`. The recursion structure is
correct (verified via `lean_verify` on foundation lemmas), only the
arithmetic of measure decrease isn't formalized.

## CRITICAL FINDING (2026-05-07): the recursion is NOT well-founded

After deeper analysis, the cu/aux mutual recursion as designed in
Sub-plan E.3′ is **mathematically not terminating**, not merely
hard for Lean's termination check. The R/R✝ unification problem is a
SYMPTOM, not the root cause. Closing the `decreasing_by sorry`s is
*impossible* with the current measure choices for a fundamental reason
documented below.

### Trace: aux's multi-R case unwinds to the same call

Start: `aux R h_or rfl` where R = d :: d' :: R'', cfg = M [] 3 R,
       h_or = step_macro h_prev h_step (cfg_pre → cfg via D2).

aux's body in this case constructs:
```
h_bad_pre : BadShape (.M [2] 3 (dp :: Rp))
         := BadShape.step (BadShape.base (d :: d' :: R'')) h_step
```
and calls `cascade_unreachable h_bad_pre h_prev`.

cu's body uses `induction h_bad with | step h_bad' h_step ih =>
exact ih (h_or.step_macro h_step) | base R₀ => aux R₀ h_or rfl`. The
structural ih for `h_bad' = BadShape.base (d :: d' :: R'')` unfolds to
`fun h_or' => aux (d :: d' :: R'') h_or' rfl`.

So `ih (h_or.step_macro h_step)` evaluates to:
```
aux (d :: d' :: R'') (h_prev.step_macro h_step) rfl
```

But `h_prev.step_macro h_step : OrbitReachable cfg` and cfg = M [] 3 (d :: d' :: R''),
which is **the same R** the original call had. So this is `aux R h_or rfl`
again — same call, no progress.

### Termination measure arithmetic confirms non-termination

For aux R → cu cfg_pre → ih → aux R₀:
- aux's measure: macroMr R * 2 = 2 · 2 · macroMr (dp :: Rp) (D2 doubles).
- cu cfg_pre's measure: cfg_pre.mr * 2 + 1 = 2 · macroMr (dp :: Rp) + 1.
- aux R₀'s measure (R₀ = R): macroMr R * 2 = 4 · macroMr (dp :: Rp).

Required: aux R₀'s measure < cu cfg_pre's measure, i.e.,
`4 · macroMr (dp :: Rp) < 2 · macroMr (dp :: Rp) + 1`,
i.e., `2 · macroMr (dp :: Rp) < 1`. **FALSE** (macroMr ≥ 4).

So the cu → aux step (via the structural ih in cu's step case) makes
the measure GROW, not shrink. The recursion is genuinely not
well-founded.

### Root cause: BadShape encoding doesn't track decreasing R

`BadShape.base R₀` carries the **forward endpoint's R**, not a
predecessor's R. After cu unwinds the BadShape chain (forward), it
calls aux at R₀ = the original R, no smaller. The mutual recursion
has no actual descent.

### Why all four solution attempts (A–D) below fail equally

Solutions A (nested Nat strong induction), B (BadShape : Type), C
(WellFounded.fix), D (inline in era.lean) all attempted to fix the
**termination check** (Lean elaboration). But the recursion isn't
well-founded mathematically, so no termination check fix can succeed.
The decreasing_by sorries are not closeable with this design.

### What's actually needed

The cascade requires a **backward predecessor analysis at M([2], 3, _)
level** (γ.2 partial; need a proof that the M([2], 3, _) backward chain
terminates). Then aux's multi-R case would call a different function
(cascade_M_2_3), recursing on dp :: Rp (one element shorter than
1 :: (dp+1) :: Rp), which IS strictly smaller in macroMr.

Specifically:
1. Generalize aux to cascade_n : ∀ n L R, OrbitReachable (M (2^n L) 3 R) → False.
2. The cascade descends through γ.1 (M [] 3 → M [2] 3) and γ.2
   (M [2 :: L] 3 → either M [2 :: 2 :: L] 3 or M [1 :: L] 5).
3. Termination by macroMr R (one element drops per cascade step).

This is **not a small fix** — it requires γ.2-style analysis at every
level of the cascade, which is the missing piece (and is the original
hard problem the BadShape encoding tried but failed to bypass).

## Outdated solution attempts (kept for record)

These solutions were proposed before the non-termination discovery
above. They cannot succeed because they only address the elaboration
issue, not the underlying mathematical non-termination.

### A. Nested Nat strong induction (avoiding BadShape-typed measure)

[skipped — addresses elaboration, not the actual non-termination]

### B. Convert BadShape to Type

[skipped — same reason]

### C. Sigma-encoded args + explicit `WellFounded.fix`

[skipped — same reason]

### D. Inline approach in era.lean

[skipped — same reason]

## Issue: dep-elim cannot auto-eliminate cons-cons mismatches in `cases`

### Setting (2026-05-07, cascade closure session 3)

Adding a new constructor `mk_M0_2_1_2spine_2_R` to `InCascade`:

```lean
inductive InCascade : MacroConfig → Prop where
  | mk_M_empty_3 (R : List Nat) : InCascade (.M [] 3 R)
  | mk_M_2spine_3 ... : InCascade (.M L 3 R)
  | mk_M_1_2spine_5 ... : InCascade (.M (1 :: L) 5 R)
  | mk_M0_2_1_2spine_2_R {L : List Nat} (R : List Nat)
      (h_2s : Is2Spine L) :
      InCascade (.M0 (2 :: 1 :: L) (2 :: R))   -- NEW
```

In `cascade_strong_aux`, the original `step_multi_bounce_general_to_zero`
case used:

```lean
| step_multi_bounce_general_to_zero _ => cases h_in
```

This worked when `InCascade` had only M-producing constructors —
all 3 fail unification with the M0 cfg, auto-eliminated.

### The problem

After adding `mk_M0_2_1_2spine_2_R`, `cases h_in` fails with:

```
error: Dependent elimination failed: Failed to solve equation
```

`cfg` is refined to `M0 (R_mid.reverse ++ (r' + 1) :: (a + 4) :: L') [1]`
by the outer `step_multi_bounce_general_to_zero` case-match. The new
constructor wants `cfg = M0 (2 :: 1 :: L) (2 :: R)`. The R-component
unification `[1] = 2 :: R` is impossible (cons-injection: `1 = 2` is
false), but Lean's dependent elimination cannot auto-derive this from
`List.cons.noConfusion` — it leaves the case open.

Even explicit pattern `| @mk_M0_2_1_2spine_2_R L R h_2s => sorry`
fails with the same error before reaching the body. `nomatch h_in`
also fails.

### Workaround tried

- `cases h_in with | @mk_M0_2_1_2spine_2_R L R h_2s => sorry` —
  fails at the pattern, not in the body.
- `nomatch h_in` — "Missing cases" error.
- `cases h_in <;> ...` — same dep-elim issue.

### Why this matters

The natural way to extend `InCascade` for `step_macro mk_M_1_2spine_5`
case D (D12 zero_two predecessor `M0 (2 :: 1 :: L) (2 :: d :: R')`)
is to add the corresponding constructor and let cascade IH (`ih_phi`)
fire on the smaller-measure predecessor.

But every `cases h_in` site in `cascade_strong_aux` (10+ locations)
needs explicit handling for the new constructor — even when the
constructor's output shape contradicts the outer cfg shape.

In sites like `step_multi_bounce_general_to_zero` where the contradiction
is a list cons-cons mismatch, Lean's dep-elim doesn't auto-derive `False`
from it.

### Workaround needed

Manual handling at each site:

```lean
| step_multi_bounce_general_to_zero _ =>
  cases h_in with
  | @mk_M0_2_1_2spine_2_R L R h_2s =>
    -- Manually derive ⊥ from cfg double-refinement.
    -- ... but Lean can't even reach the body.
    ???
```

For now: **reverted the constructor addition**. Cascade closure for
case D requires either:
- Massive refactor with explicit per-site handling (~200 LOC).
- Custom unfolding tactic to coerce dep-elim into recognizing
  cons-cons contradictions.
- Different approach (recursive helper family, not InCascade extension).

## Issue: cascade chain extends unboundedly for `step_macro mk_M_1_2spine_5`

### Setting (2026-05-07)

In `cascade_strong_aux`, the `step_macro mk_M_1_2spine_5` case has 4
productive predecessor cases via γ.3 (predecessor analysis lemma):

- **B** (D7 era_and_sweep_solo): `M0 [2] [1]` — closed via existing
  `OrbitReachable.not_M0_2_1`.
- **C** (D8 zero_two_solo): `M0 (2 :: 1 :: L_2s) [2]` — closed via
  new helpers H1 (`not_M_starts_1_1_2spine_2_R1`) and H2
  (`not_M0_starts_2_1_2spine_2`). Chain depth 2 (H2 calls H1 via
  step_macro D1; H1's chain bottoms out at step_R1 + ih_phi).
- **A** (D5 sweep_left_empty, L_2s = []): predecessor `M [] 7 (d :: R')`.
  Phi preserved by sweep; chain extends backward via D2
  (sweep_and_shift) to `M [6] 3 (...)`, then γ.2 to `M [2, 6] 3 (...)`,
  ad infinitum (each γ.2 step prepends a 2 to L).
- **D** (D12 zero_two): predecessor `M0 (2 :: 1 :: L_2s) (2 :: d :: R')`.
  Chain extends backward to `M (1 :: 1 :: L_2s) 2 (1 :: d :: R')` →
  `M (1 :: 1 :: 1 :: L_2s) 3 ((d-1) :: R')` → ... bounded by `d`,
  but `d` is unbounded over instances.

### The mathematical structure

The cascade chain for cases A, D2, D involves shapes like
`M ([2^i, 1^j] :: L_2s) cursor R` for unbounded i, j. The lex measure
`(phi, mr)` strictly decreases backward — phi is preserved but
`macroMr R` halves at each D2 step (Probe 2 in `scout_2adic.lean`).
So total chain length is finite, bounded by `log₂(macroMr R₀)`.

### Why a finite cascade extension doesn't suffice

Encoding all chain shapes as `InCascade` constructors requires
parameterizing by chain depth. For example:

```lean
| mk_M_1ones_2spine_5 (n : Nat) {L_2s : List Nat} (h_2s : Is2Spine L_2s)
    (R : List Nat) :
    InCascade (.M (List.replicate (n + 1) 1 ++ L_2s) 5 R)
```

But this is one of MANY parameterized families needed:
- `M (1^k ++ L_2s) 5 R` for cursor 5 (extension of `mk_M_1_2spine_5`)
- `M (2^i ++ 1^j ++ L_2s) 3 R` for cursor 3 (extension of `mk_M_2spine_3`)
- `M (1^k ++ L_2s) 2 (1^? ++ R) ` for cursor 2
- `M0 (2 :: 1 :: ... ) (2 :: ...)` for M0 shapes
- `M [] (c+3) R` for the empty-L cascade (case A)

Each family needs predecessor preservation lemmas (γ-style). Estimated
~500-1000 LOC of new infrastructure.

### What was achieved (session 3)

Closed cases B and C via specific helpers H1, H2. Cases A, D2, D
remain as sorries inside `cascade_strong_aux` (lines ~568, 582, 652
in `era_orbit_cascade.lean`). Build clean: 895 jobs, cascade has 3
sorries inside step_macro mk_M_1_2spine_5.

### What was achieved (session 4) — D5/A closed via mk_M_empty_high_3

Added 4th `InCascade` constructor:

```lean
| mk_M_empty_high_3 (c : Nat) (R : List Nat) :
    InCascade (.M [] (c + 4) R)
```

D5/A closed via `ih_mr` on `cfg_pre = M [] 7 (d :: R')` (smaller mr
at same phi as outer cfg). The D5/A sorry at the original line is
gone; in its place is a 20-line block computing the lex decrease and
applying `ih_mr`.

However, the new constructor created 4 new sorries elsewhere (the
predecessor analysis of `M [] (c+4) R` has the same constructor-
explosion problem):

- `mk_M_empty_high_3` case in `step_macro` (predecessors: D2/D8/D10/D12).
- `mk_M_empty_high_3` in `step_multi_bounce_2_double_shift` (pred `M0 [c] [3, 2]`).
- `mk_M_empty_high_3` in `step_R2_zero` (pred `M0 [c] [3, 1, 2]`).
- `mk_M_empty_high_3` in `step_R3` (pred `M0 [c] (...)`).

**Net cascade sorry count**: 3 → 6. Structural difficulty is now
centralized to the new constructor's predecessor dispatch.

### Recommended approach for future work

1. Define a parameterized inductive `CascadeShape` with constructors
   for all chain-step targets (~6-8 constructors needed):
   - `M [] (c+4) R` (`mk_M_empty_high_3`, added in session 4).
   - `M [n] 3 R` for n ≥ 1 (D2 pred chain).
   - `M [2^k, n] 3 R` (further D2 extensions).
   - `M [n] 5 R` (D3-lift).
   - `M0 [n] [2]`, `M0 [n] [4]`, `M0 [n] (2 :: ...)`, `M0 [n] [3, 2]`,
     `M0 [n] [3, 1, 2]` shapes.
2. Prove `CascadeShape.predecessor_preservation` (γ-family) for each.
3. Use lex-measure induction `(phi, mr, depth)` where `depth` is
   the constructor's parameter (number of prepended 1's/2's).
4. The induction terminates because `mr = macroMr R` halves on D2
   steps and decreases monotonically on others.

This is genuinely a 1-2 week effort given the careful invariant
design needed.
