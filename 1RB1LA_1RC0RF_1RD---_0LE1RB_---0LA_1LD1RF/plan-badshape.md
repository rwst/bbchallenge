# Plan: closing the residual `base R` sorry in `BadShape.not_OrbitReachable`

**Status**: drafted 2026-05-06; **Option A landed 2026-05-06**;
**Option γ scaffolding landed 2026-05-06** (`era_orbit_gamma.lean`,
333 L, axiom-clean, 0 sorries).

After landing Option A (structural induction on BadShape, not the
"well-founded on sizeOf" form initially conceived), the BadShape
framework collapses **17 sorries → 4 sorries** in `era_orbit.lean`:

- 3 unchanged (existing step_R1 sorries from prior work, unrelated).
- **1 new** (residual `base R` case in `BadShape.not_OrbitReachable`).

This document tracks the remaining `base R` sorry and the path forward.

## The current state (after Option A)

`era_orbit.lean` lines 487-499:

```lean
/-- **Cascade closure** (Sub-plan C-3, Option A, 2026-05-06): BadShape cfg
    implies cfg is not orbit-reachable. By structural induction on h_bad:
    - `step h_bad' h_step`: by IH, ¬ OrbitReachable cfg'. Forward
      extension via `h_or.step_macro h_step` produces OrbitReachable cfg',
      contradicting IH. ✓
    - `base R`: cfg = M([], 3, R). Need ¬ OrbitReachable cfg. The
      residual cascade-closure goal (sole `sorry`). -/
theorem BadShape.not_OrbitReachable {cfg : MacroConfig}
    (h_bad : BadShape cfg) : ¬ OrbitReachable cfg := by
  induction h_bad with
  | base R =>
    intro _
    sorry
  | step h_bad' h_step ih =>
    intro h_or
    exact ih (h_or.step_macro h_step)
```

Plus the corollaries:

```lean
theorem OrbitReachable.not_BadShape (h : OrbitReachable cfg)
    (h_bad : BadShape cfg) : False :=
  h_bad.not_OrbitReachable h

theorem OrbitReachable.not_M_empty_3_full (h : OrbitReachable cfg) :
    ∀ R, cfg ≠ .M [] 3 R := by
  intro R hcfg; apply h.not_BadShape; rw [hcfg]; exact BadShape.base R
```

When the residual `base R` case is closed, **all of these become fully
proved** (axiom-clean), and `era.lean`'s `not_M_empty_3` multi-R sorry
is closable via `not_M_empty_3_full`.

## What the residual sorry is

```
∀ R, OrbitReachable (.M [] 3 R) → False
```

i.e., **no orbit-reachable config has shape `M([], 3, R)`** for any R.

This is the original R1-closure goal. The BadShape framework offered
no shortcut for this: it consolidated 9 forward-cascade obligations
into one, but the irreducible cascade-closure work remains.

## Strategies for closing the `base R` case

By induction on the OrbitReachable derivation (`h : OrbitReachable cfg`
with `cfg = M([], 3, R)`), we case-split on the OrbitReachable
constructor that produced cfg:

| Constructor | Closure |
|-------------|---------|
| `init` | `M([1], 4, [1]) ≠ M([], 3, R)`: structural mismatch (cursor 4 ≠ 3 OR L=[1]≠[]). ✓ trivial. |
| `step_macro h_prev h_step` | predecessor analysis via phase2's `macroStep_M_empty_3_predecessor` gives `cfg_pre = M([2], 3, R'_pre)`. **Recursive call** to `BadShape.not_OrbitReachable` on `cfg_pre` with `BadShape.step (BadShape.base _) h_step` (the cascade). |
| `step_R1 h_pred ...` | predecessor `M([], 3, _)` ⟹ apply IH (recursive call same theorem) to derive contradiction. |
| `step_R3 _ _ _ _ h_safe _` | h_safe says `cfg ≠ M([], 3, R)`. Direct contradiction with `hcfg`. |
| `step_multi_bounce_*` | output L always non-empty (length ≥ 2). `cfg = M([], 3, R)` requires L=[]. Contradiction via shape mismatch. |
| `step_R2_zero`, `step_R2_succ` | output L starts with `(a+4)::...` or cursor `(a+4)` ≥ 5. Shape mismatch. |
| `step_multi_bounce_general_to_zero` | output is M0 — kind mismatch. |

Most cases close trivially. The hard ones are `step_macro` (cascade
recursion) and `step_R1` (IH application).

### Approach: standalone induction with cascade recursion

```lean
-- Place this inside BadShape.not_OrbitReachable's `base R` case.
intro h_or
-- Now: h_or : OrbitReachable (.M [] 3 R). Goal: False.
generalize hcfg : (.M [] 3 R : MacroConfig) = cfg at h_or
induction h_or with
| init =>
  -- M([1], 4, [1]) ≠ M([], 3, R). Structural.
  injection hcfg.symm with hL _ _
  exact List.cons_ne_nil _ _ hL
| step_macro h_prev h_step ih =>
  -- cfg = step_macro output = .M [] 3 R. Predecessor is M([2], 3, R'_pre).
  obtain ⟨d_pre, R_pre, hcfg_pre, _, _⟩ :=
    macroStep_M_empty_3_predecessor _ _ _ h_prev.macroInvariant (hcfg.symm ▸ h_step)
  -- Now h_prev : OrbitReachable cfg_pre with cfg_pre = M([2], 3, _).
  -- Need contradiction. Recursively call BadShape.not_OrbitReachable on cfg_pre
  -- with BadShape.step (BadShape.base R) h_step (a STEP-form BadShape).
  exact BadShape.not_OrbitReachable
    (BadShape.step (BadShape.base R) (hcfg.symm ▸ h_step)) (hcfg_pre ▸ h_prev)
| step_R1 h_pred ih =>
  -- pred = M([], 3, d::R') = also a base R1 shape. Use IH on h_pred.
  -- IH: cfg = .M [] 3 R → False, but pred ≠ original cfg. Need to instantiate IH.
  -- Specifically: pred IS M([], 3, d::R'); apply BadShape.not_OrbitReachable directly.
  exact BadShape.not_OrbitReachable (BadShape.base _) h_pred
| step_R3 _ _ _ _ h_safe _ _ =>
  exact h_safe R hcfg.symm
-- All other constructors: shape mismatch via injection on hcfg.
| step_multi_bounce_general _ _ =>
  injection hcfg.symm with hL _ _
  exact (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)) hL
| step_multi_bounce_general_to_zero _ _ =>
  exact MacroConfig.noConfusion hcfg.symm
| step_multi_bounce_2_and_shift _ _ =>
  injection hcfg.symm with _ _ hR
  injection hR with _ hR2
  exact List.cons_ne_nil _ _ hR2
| step_multi_bounce_2_double_shift _ _ =>
  injection hcfg.symm with _ hc
  -- hc: a + 4 = 3, where a comes from constructor's params. Need omega.
  sorry
-- ... continue for step_multi_bounce_3run_last_2, step_multi_bounce_last_2_general,
--     step_R2_zero, step_R2_succ.
```

**The crucial recursive call** in `step_macro`:

```lean
exact BadShape.not_OrbitReachable
    (BadShape.step (BadShape.base R) (hcfg.symm ▸ h_step)) (hcfg_pre ▸ h_prev)
```

This is the meat of the cascade closure. It calls back into
`BadShape.not_OrbitReachable` with:
- A *larger* BadShape (size 2: step containing base) than the original
  base case (size 1).
- A *smaller* OrbitReachable derivation (`h_prev` is sub-derivation of
  `h_or`).

### Termination concern

Lean's structural induction on `h_bad : BadShape cfg` doesn't directly
support this recursive call structure. We're inside the `base R` case,
calling the theorem on a different cfg with a `step` BadShape (size 2).
**This recursion does NOT decrease BadShape size** — it INCREASES.

The call structurally decreases on **OrbitReachable depth** (since
`h_prev` is a sub-derivation of `h_or`).

**This means** the induction we're doing inside the `base R` case is
on `h_or` (OrbitReachable), and the recursive call to
`BadShape.not_OrbitReachable` on the predecessor is NOT a recursive
call inside the original BadShape induction — it's a fresh top-level
call that Lean must accept via well-founded recursion on a combined
measure.

In Lean, this works **only if** we use:
- Mutual recursion between `BadShape.not_OrbitReachable` and a helper
  `not_orbit_M_empty_3` (or inline the recursion inside the induction
  block as a `let rec` or via `Acc.recursion`).
- An explicit termination measure: lex(OrbitReachable depth, BadShape
  size) or similar.

Alternatively, the cleanest closure uses **only the sub-derivation
recursion** (within `induction h_or`'s automatically-generated IH):

For step_macro case in `induction h_or`, the IH is:
`∀ R, cfg_pre = M([], 3, R) → False`.

But cfg_pre = M([2], 3, R'_pre), which is NOT M([], 3, R) form. So
IH doesn't directly apply. Hence the need for an EXTERNAL not_M_2_3
lemma (which itself needs the cascade).

### Why the cascade is hard

Each layer of the cascade introduces NEW shape patterns:

| Layer | Shape | Predecessors |
|-------|-------|--------------|
| 0 | M([], 3, R) | M([2], 3, _) |
| 1 | M([2], 3, R) | M([2,2], 3, _) OR M([1], 5, _) |
| 2a | M([2,2], 3, R) | M([2,2,2], 3, _) OR M([1,2], 5, _) |
| 2b | M([1], 5, R) | M([], 7, _), M([4,1], 3, _), M0([2], [1]), M0([2,1], [2]), M0([2,1], [2,d,R']), M0([1,1], [4]) |
| ... | ... | ... |

Phase2.lean has Layers 0-5 enumerated as predecessor lemmas
(`macroStep_M_empty_3_predecessor`, `macroStep_M_cons_2_3_predecessor`,
`macroStep_M_cons_1_5_predecessor`, etc.) but they aren't yet wired
into a top-level closure.

The cascade is bounded by Φ + structural arguments (sweep-family chain
length ≤ R.sum / 2; M0-side decreases Φ ≥ 2 per step), but the
formalization is ~500-1000 lines of intricate induction.

## Recommended path forward

**Three concrete options** for closing the residual sorry:

### Option α: complete the phase2 cascade

Extend phase2's predecessor lemmas through Layers 6-N (until cascade
terminates structurally OR via Φ < 6 exclusion). Wire into
`BadShape.not_OrbitReachable.base R` via mutual-recursion-style
induction.

**Effort**: ~500-800 lines.
**Status**: Layers 0-5 done in phase2.lean; ongoing.

### Option β: use F2 conjecture as a black-box

`conjectures.lean`'s `f2_max_era_step` characterizes the F2 family of
era-starts. If proven, it gives the orbit dynamics structure that
allows direct exclusion of `M([], 3, R)` shapes by Φ + era depth.

**Effort**: ~200 lines (assuming F2 conjecture is closed first).
**Risk**: F2 conjecture itself is unsorried with significant complexity.

### Option γ: integer-fueled forward simulation

For each OrbitReachable cfg, prove that within some FINITE number
of macroSteps, the trajectory terminates (macroStep returns none) OR
reaches a known orbit-reachable state. Use Φ + L_head + R_head as
fuel.

**Effort**: ~300-500 lines.
**Status**: scaffolding **landed 2026-05-06** in `era_orbit_gamma.lean`
(333 L, axiom-clean, 0 sorries). End-goal `base R` closure NOT yet
achieved — see "Option γ delivered" below.

#### Option γ delivered (2026-05-06)

`era_orbit_gamma.lean` provides foundational infrastructure but does
**not** close `BadShape.base R`. The investigation revealed why the
straightforward forward-fuel reading fails: macroStep on `M([], 3, R)`
returns `none` immediately (the R1 trigger is itself a macro-halt), so
forward simulation from the goal state has no traction. The natural
direction is therefore **backward predecessor enumeration**, which is
intrinsically unbounded.

**What γ DID provide:**

- **γ.1 (predecessor uniqueness)** `macroStep_M_empty_3_predecessor_form`:
  D2 (`sweep_and_shift`) is the **unique** macroStep producing
  `M([], 3, R)`; predecessor is `M([2], 3, d :: R')` with
  `R = 1 :: (d + 1) :: R'` and k = 19. Closes 10/12 dispatch disjuncts
  via shape mismatch; 2 require AllGe1 invariant on M0's L to rule out
  cursor=3 outputs from D8/D10/D12.
- **γ.2 (extension)** `macroStep_M_2list_3_predecessor_form`: predecessors
  of `M((2 :: L_out), 3, R)` are either D2 extension
  (`M (2 :: 2 :: L_out) 3 (d :: R')`) or D3 lift
  (`M (1 :: L_out) 5 (d :: R')`).
- **γ.3 (fuel)** `gammaFuel cfg := cfg.phi - 6` Nat-valued. Properties:
  `gammaFuel_init = 0`; `gammaFuel (M [] 3 R) = R.sum - 3`;
  non-decreasing under macroStep.
- **γ.4 (simulator)** `gammaSim fuel cfg : Option (Nat × MacroConfig)`:
  bounded Option-bind forward simulator. Lemmas: `gammaSim_zero`,
  `gammaSim_succ_halt`, `gammaSim_preserves_OrbitReachable`.
- **γ.5–γ.6**: γFuel-region characterisation + concrete OrbitReachable
  witness via gammaSim.

**Why γ does not close the residual sorry:**

The cascade backward from `M([], 3, R)` extends the L-spine indefinitely
via D2 chains, with predecessor Φ ≥ current Φ. No finite γFuel value
caps this enumeration. A genuine closure needs:

1. A measure that **strictly decreases** along D2 predecessors —
   neither Φ nor γFuel (= Φ − 6) qualifies.
2. OR a bound on D2-spine length via era-graded structure (matches
   plan-era-graded-not_R1.md's Sub-plan C territory).
3. OR the F2 conjecture as a black-box (Option β).

γ remains useful as the foundation for any of (1)/(2): the predecessor
uniqueness lemmas γ.1/γ.2 are loadbearing for whatever cascade lemma
ultimately closes the goal.

## What NOT to do

❌ **Per-constructor cascade** (the original "Option D" from the prior
plan): writing 9 separate cascade proofs, one per OrbitReachable
constructor. The BadShape framework already collapsed these, so
re-doing is redundant.

❌ **init's finite trace** as a standalone proof: with Option A, init
is no longer a separate case — it dissolves into the BadShape
induction. The `base R` case subsumes init's role.

## Cross-references

- `era_orbit.lean:487-503`: `BadShape.not_OrbitReachable` (residual
  base case sorry).
- `era_orbit.lean:505-507`: `OrbitReachable.not_BadShape` (corollary,
  axiom-clean modulo the base sorry).
- `era_orbit.lean:509-513`: `OrbitReachable.not_M_empty_3_full`
  (corollary, axiom-clean modulo the base sorry).
- `era.lean:471-549`: existing partial `OrbitReachable.not_M_empty_3`
  (unchanged; era.lean is upstream of era_orbit.lean and can't
  reference downstream lemmas).
- `phase2.lean:437-1346`: predecessor lemmas for Layers 0-5.
- `era_orbit_gamma.lean`: Option γ scaffolding (γ.1–γ.6).
  - `:39-100`: γ.1 D2-uniqueness predecessor lemma.
  - `:106-200`: γ.2 2-spine predecessor extension.
  - `:204-243`: γ.3 gammaFuel definition + properties.
  - `:247-297`: γ.4 gammaSim + preservation under OrbitReachable.
  - `:301-330`: γ.5 γFuel-region characterisation.
  - `:333`: γ.6 concrete witness.
- `plan-era-graded-not_R1.md`: original era-graded plan (Sub-plan C
  analysis section discusses why the cascade is intrinsically hard).
- `LOG.md` "Option A landed" entry + "Option γ scaffolding" entry
  (both 2026-05-06).

## Success criteria

After the residual sorry is closed:
- `BadShape.not_OrbitReachable`: 0 sorries.
- `OrbitReachable.not_BadShape`: 0 sorries (corollary).
- `OrbitReachable.not_M_empty_3_full`: 0 sorries (corollary).
- Build axiom set for `Sweeper.sweeper_never_halts`: depending on
  whether `era.lean`'s `not_M_empty_3` multi-R sorry is also closed
  via downstream wiring (or migrated to use `not_M_empty_3_full`):
  - `{propext, Classical.choice, Quot.sound}` (full closure).
  - Plus `reach_M_nil_3` if not yet wired upstream.

Wiring `not_M_empty_3_full` into `era.lean`'s upstream proof requires
either:
- Moving relevant phase2/era_orbit lemmas upstream (refactor).
- Restructuring `era.lean`'s `not_M_empty_3` to reference downstream
  via a forward-declaration trick (not idiomatic).
- Replacing the upstream version's invocation in `progress.lean`'s
  `orbit_progress` with a downstream-aware version (preferred).
