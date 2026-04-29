# Plan: closing the 3 reachability axioms

## Current status (2026-04-28)

`phase2.lean` (1379 lines, 46 axiom-clean lemmas):
- Master case-split (`macroStep_eq_some_cases`) + tactic macros
  (`ms_inj` / `ms_inj_all` / `ms_close`) provide clean per-shape backward
  analysis.
- Layers 0-4 complete, Layer 5 partial (5 of ~14 lemmas).
- `sweeper_never_halts` still depends on 3 reachability axioms (R1, R2,
  R3-narrow); empirically validated (F1+F2 simulator: 0 occurrences in
  51B raw steps).

## Strategies that have been ruled out

The following list is **definitive based on prior work + Phase A data**:

### Backward cascade (Phases 0-5 of this work)

The cascade closes ~30 shapes through Layer 5, but **branches ~3-4× per
layer**. Each layer opens 10-20 new shapes, none of which reduce to the
existing closure. Every branching shape satisfies `MacroInvariant`, so
that invariant alone cannot exclude them. Cascade depth is unbounded.

### Per-field invariant strengthening (legacy `era_plan.md`)

Multiple prior attempts:

- **C1Inv / SafeRight (step-level)**: bookkeeping for phase transitions
  explodes. Abandoned.
- **Mersenne-exclusion** (`L=[] → c ∉ {3,7,15,31,…}`): cascades into
  conditions on `L.head` at `c=1`, then `c=7`, then …  Infinite chain.
- **Compound-transition strengthening (Approach C)**: blocked because
  halting depends on the full `(L, c, R)` triple, not any single field.
  `M([], 5, [1])` halts but `M([], 11, [1])` does not; `M([], 7, R)`
  halts for every R but `M([], 4, [4,6,2])` does not. No simple
  per-field condition separates the two.
- **`RTailOkay` predicate** ("R ends in 1 when length ≥ 2"): preservation
  fails at `sweep_and_shift` on `M(L, 3, [1])` → `M(_, _, [1, 2])`.
- **macroEra refinement**: closed most cases but leaves the same 3
  transient shapes uncovered — the current 3 axioms.

**Phase A data confirms the same wall**:
- `M([], 5, _)` opened by Layer 5 `macroStep_M_cons_1_3_predecessor` is a
  Mersenne-family shape (cursor 5 is on the L=[] cascade chain).
- `M(2::1::L_out, 7, _)` opened by Layer 4f Producer 2 has 6 producers
  with structurally different shapes — same triple-dependence problem.
- All branching shapes are `MacroInvariant`-valid; the orbit avoids them
  empirically but no per-field condition separates them.

**Conclusion**: era-state / cascade-style invariants are unworkable for
this TM. Don't pursue Phase E.

## What might still work

### Option 1 — Forward simulation per axiom shape (Recommended)

The 3 axioms aren't statements about reachability — they're forward
dynamics:

> "Starting from R1 shape `M([], 3, d :: R)`, raw TM eventually reaches
> a non-halted MacroProg config in `k > 0` steps."

This is the same template as `macro_multi_bounce_last_2_general` (in
`machine.lean`), which closed **50% of the original R3** by direct raw
TM simulation through a specific transient shape.

Plan:

1. **R1 forward dynamics**: prove
   `∀ d R', ∃ k cfg', run sweeper (M [] 3 (d :: R')).toConfig k = cfg'.toConfig ∧ MacroInvariant cfg' ∧ ¬halted cfg'`.

   Approach: trace the raw TM by induction on the structure of `R'`
   (or on `d`). Each transition is small (a single `step` call); the
   total number of steps is determined by `R'`'s shape. The proof
   resembles existing macro-rule lemmas in `machine.lean`.

2. **R2 forward dynamics** (`reach_multi_bounce_last_2_mid_1`):
   `M0(a::L', [r'+3, 1, 2])`. Similar approach; the existing
   `macro_multi_bounce_2_double_shift` may compose.

3. **R3-narrow** (`reach_multi_bounce_last_2_long`):
   `M0(a::L', (r'+3) :: e :: f :: rest ++ [2])`. The recursive case;
   needs induction on `rest`'s length. The 50%-closed
   `macro_multi_bounce_last_2_general` shows the technique works for
   the easy half (last middle ≥ 2). The hard half (last middle = 1)
   would need a similar but more careful chain.

**Estimate**: 3-7 days per axiom. R3-narrow likely the hardest.

**Why this might work where other approaches haven't**: it's the same
technique that already works for ~25 macro rules in `machine.lean`. We
already know forward simulation is tractable when the chain length is
bounded by structural induction on R or L. The 3 axioms differ from
existing rules only in that nobody has formalized their step-counting
recurrences yet.

**Why it might still fail**: each axiom's chain length might depend on
multiple list components in a way that doesn't reduce by simple
structural induction. If `R'`'s elements interact non-trivially across
the chain (e.g., the Collatz-like cascade mentioned in `era_plan.md`'s
failure analysis), formalization could be intractable.

### Option 2 — 2-adic / algebraic invariant (Speculative)

The LucysMoonlight TM (`1RB0RD_…`) and Mxdys' ValidS work on related
TMs use number-theoretic functional invariants — a single
`Nat`-valued function that the orbit preserves. This sidesteps the
"halting depends on full triple" problem because the invariant isn't
a conjunction of per-field predicates.

For Sweeper, no such invariant has been identified. Designing one
would require:
- Empirical analysis of the orbit's L sequence as a function of era
  count (e.g., does it satisfy a linear recurrence? a 2-adic
  congruence?).
- Proving preservation through every macroStep dispatch.

**Estimate**: unknown. Could be 1 week (if the invariant is "obvious"
once spotted) or never (if no clean invariant exists for this TM).

### Option 3 — Accept axioms

The 3 axioms are:
- Empirically validated (51B raw steps, 0 occurrences).
- Stated as forward dynamics (`step_run` bypass), not orbit reachability,
  so soundness doesn't require showing the shapes are unreached.
- Already 50%-closed (R3-narrow via `macro_multi_bounce_last_2_general`).

The cascade work (Layers 0-5, 46 lemmas) remains as documentation of
which `macroStep` paths lead where; it's not wasted.

## Recommendation

**Start Option 1, R1 first.** R1 is the simplest of the 3 axioms (single
target shape `M([], 3, d::R)`, no recursive list tail). If the forward
simulation works for R1, the technique scales to R2 and R3-narrow.

Concrete steps:
1. Read `macro_multi_bounce_last_2_general` to understand the proof
   template.
2. Trace raw TM steps from `M([], 3, [d])` for small d; identify the
   recurrence.
3. Generalize the recurrence to `M([], 3, d::R)` for arbitrary R.
4. Replace `reach_M_nil_3` axiom invocation in `macro_progress` with
   the new forward lemma.

If R1 closes successfully, repeat for R2, R3-narrow. If it doesn't,
fall back to Option 3 (accept axioms) — Option 2 (2-adic) is a longer
research project that should only be undertaken with clear empirical
motivation for the candidate invariant.

## What's deprecated

- **Refactoring 1 (master case-split)** — DONE, see git history /
  `LOG.md`.
- **Refactoring 2/3 (helper lemmas, tactic helpers)** — done as part of
  Phase C.7.
- **Phase A (Layer 5 cascade extension)** — DONE, results in `LOG.md`.
  Confirms cascade is unbounded.
- **Phase B-D (mutual `OrbitReachable.not_*` block + wire-up)** —
  blocked on cascade not closing. Don't pursue.
- **Phase E (era-state invariant strengthening)** — explicitly ruled
  out by prior work and Phase A data. **DO NOT PURSUE.**
