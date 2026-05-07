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
