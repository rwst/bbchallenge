# Strategy Analysis — Proving Nonhalt of TM 1RB---0RB0LA2RA_2LB2LA3RA4LB0LB

Date: 2026-04-17 (post-mortem of the current `machine.lean` attempt).

## Summary of the Current Attempt

The proof in `machine.lean` uses `nonhalt_of_progress` with a predicate
`IsCanonical` characterizing the `CycleStart` configuration family. The
bulk of the proof handles four cases of `canonical_progress`:

1. **Non-trivial ternary**: `cycle_nonzero` — one RInc/LInc cycle. Proved.
2. **Even overflow** (pad=0, tern all-zero): `overflow_cycle`. Proved.
3. **Odd overflow** (pad=1, tern all-zero): requires a case split on
   leading binary bits `k`:
   - `k=0`: `overflow_odd` proved (6d+9 steps).
   - `k=1`: `overflow_odd_k1` proved (6d+10 steps).
   - `k≥2`: not proved.
   - `bin = rep s3 dd` (all-s3): leads to HALT. Must prove unreachable.

### Why one sorry remains

To avoid handling k=1, k≥2, all-s3 individually, the attempt adds a
parity invariant to `IsCanonical`:

```
binOdd bin_cells = (ternOdd tern_cells == (pad == 1))
```

This forces `binOdd bin = false` at odd overflow (where `ternOdd = 0` and
`pad = 1`), eliminating all k ≥ 1 cases by contradiction. Only k=0 remains,
and it yields a clean output.

**The fatal issue**: The invariant is NOT preserved by `overflow_odd` itself.
Its output is `bin_rest`, and by simulation data in `macro.md`:

| era | V_entry | binOdd at odd overflow output |
|-----|---------|-------------------------------|
| 0   | 1       | true (matches invariant)      |
| 1   | 11      | false (breaks invariant)      |

After one era, the invariant is falsified. The proof stands only by carrying
forward a wrong hypothesis; the remaining sorry at line 1001 demands
`binOdd bin_rest = true` which cannot be derived.

### Root cause

The simulation table in `macro.wiki`/`macro.md` reveals:

    T_dig  B_val  binOdd  case
        3      1    true   k=1 (s3 leading)
        5     11    true   k=1
        7    130    false  k=0 (s2 leading)
        9   1425    true   k=1

The parity pattern {T, F, T, T, T, F, F, F, ...} is not periodic, not simply
mod-based, and not derivable from any single-argument mod invariant.

From `claude-said.txt`:
> The non-halting argument requires showing that the base-2 value never hits
> 2^n-1 at specific moments. This is inherently about the 2-adic properties
> of iterates of the map V → (V+3^d)/2 with growing d. No simple mod-based
> invariant captures this.

## Candidate Paths Forward

### Path A: Revert field 8, handle all four cases individually

**Plan**: Remove the parity invariant (field 8). Restore the original
4-sorry structure. Attack each case.

**Sub-goals**:
- A.1 Prove `overflow_odd_k` for general `k ≥ 2` (complex cascade in a
  single cleaned-up lemma). Estimate: 200-400 lines of step-by-step work.
- A.2 Prove that `bin = rep s3 dd` at odd overflow is unreachable.
  This is the crux — requires one of the sub-paths B/C/D/E below.
- A.3 Strengthen invariants in `IsCanonical` to force bin.length ≥ 2 so
  that k=1 output `bin_rest` remains nonempty (already works via field 7).

**Evaluation**: Cleanest, most modular. A.1 is labor; A.2 is where the
real difficulty lies.

### Path B: Computational bootstrap + asymptotic invariant

**Plan**: Verify the first N eras by `native_decide` (N ≈ 10-20). Prove a
structural invariant that holds from era N onward — typically
`bin.length ≥ f(era)` for some function `f` growing faster than the
all-s3 cascade could affect.

**Sub-goals**:
- B.1 Define an "era counter" derived from ternary length and pad.
- B.2 Prove `reaches_canonical_era_N` via native_decide (expensive:
  era 10 is ~10^7 steps, era 15 is ~10^10).
- B.3 From era N onward, prove `bin.length > some bound` ⇒ bin ≠ rep s3.

**Evaluation**: Feasible but brittle; `native_decide` cost grows fast.
Requires new infrastructure (era tracker).

### Path C: Diophantine / 2-adic approach

**Plan**: Track `binValue` (already defined) through the proof. Prove that
the sequence of values at odd overflow satisfies a Diophantine constraint
that rules out `V = 2^n - 1`.

**Sub-goals**:
- C.1 Prove conservation: within one era of `cycle_nonzero`, `binValue`
  transforms according to a specific linear recurrence (modulo wraps).
- C.2 Characterize the set of values reachable at odd overflow as
  `{V₀ + f(era history)}` for a concretely-described `f`.
- C.3 Prove `f(...) ≠ 2^n - 1` via a number-theoretic argument
  (e.g., Mihailescu's theorem rules out `2^n - 3^d = 1` for n,d ≥ 2,
  which handles one special case).

**Evaluation**: Mathematically deepest but most speculative. Likely
requires new mathlib imports (p-adic valuations, possibly Mihailescu).

### Path D: BusyCoq `progress_nonhalt_simple` via abstract state space

**Plan**: Use `progress_nonhalt_simple` from `bb2x5.lean` with a richer
abstract state `C` encoding the full trajectory (era number + internal state).
Define `f : C → Config` and `hnext : ∀ c, ∃ c', f c -[tr]->+ f c'`.

**Sub-goals**:
- D.1 Design `C` to reflect the era pair structure (big era + immediate
  odd overflow).
- D.2 Prove `hnext` by case analysis on era type, using existing
  `cycle_nonzero`, `overflow_cycle`, `overflow_odd*` theorems.
- D.3 The all-s3 problem still arises inside the odd overflow cases;
  requires path A, B, or C to close.

**Evaluation**: Cleaner proof architecture, but doesn't dissolve the
fundamental all-s3 obstruction.

### Path E: Direct simulation argument for all-s3

**Plan**: Prove the following directly without invariants:

> **Claim**: At any odd overflow (pad=1, tern=0), `bin ≠ rep s3 n` for any `n`.

**Sub-approach E.1**: Prove by induction on era count that every canonical
reached from `initConfig` has `bin.length > max s3-prefix length`, using
a length-growth lemma.

**Sub-approach E.2**: Prove that if `bin = rep s3 n` at odd overflow,
backward tracing gives a contradiction (the previous overflow could not
produce rep s3 n).

**Evaluation**: E.2 is most appealing — it pushes the problem to a single
"pre-image" calculation. Inverting `overflow_cycle` and `cycle_nonzero`
to characterize what kinds of bin lead to `bin = rep s3 n` may yield a
finite set of bad cases that can be ruled out computationally.

## Recommendation

**Short term (tractable)**: Path A (revert field 8) to recover a clean
4-sorry state, then tackle sorries 1-3 (even overflow length, k=1 length,
k=2 via new theorem). Leave the all-s3 sorry as the sole open problem.

**Long term (crux)**: Paths B, C, E are candidates for the all-s3 sorry.
My recommendation is to start with E.2 (backward tracing) because:
- It's most direct: no new invariants, no new asymptotics, no number theory.
- It leverages the existing transition theorems.
- It may collapse into a finite computational check.

If E.2 fails, escalate to Path B (computational bootstrap). Path C
should be a last resort — it's deep but speculative.

## What Basics.lean Contains

The companion file `Basics.lean` states lemmas that are directly
implied by `claude-said.txt` and can be proved with existing mathlib
(placeholders with sorry for the actual proofs). These serve as
building blocks for Paths B, C, E:

1. Binary/ternary value properties
2. `bin = rep s3 n ↔ binValue bin = 2^n - 1` (for valid binary)
3. 2-adic valuation / odd-ness of 2^n-1
4. The abstract iterate map `V → V + 3^d` and its parity behavior
5. Conservation statements relating successive eras

These are the "free" lemmas — already implied by current definitions,
just not yet stated. Proving them is bookkeeping, not breakthrough.
