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
- A.1 Prove `overflow_odd_k` for general `k ≥ 2` (complex cascade; see
  the dedicated "Plan for proving k≥2 dynamics" section below —
  simulation shows this is ~1000-step cascade that visits
  non-canonical intermediate states, so the original estimate of
  200-400 lines was too optimistic).
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
implied by `claude-said.txt` and can be proved with existing mathlib.
As of 2026-04-17 all but one lemma are proved (the remaining sorry is
the open problem itself). The proved lemmas:

1. Binary/ternary value properties (`binValue_rep_s3`, etc.)
2. `bin = rep s3 n ↔ binValue bin = 2^n - 1` (for valid binary)
3. 2-adic valuation / odd-ness of 2^n-1
4. The abstract iterate map `V → V + 3^d` and its parity behavior
5. Diophantine facts: `(2^n - 1) mod 2^m = 2^m - 1` for m ≤ n, etc.

## What BackwardTrace.lean Contains (Path E.2 infrastructure)

The file `BackwardTrace.lean` (2026-04-17) provides the structural
groundwork for Path E.2:

**Proved:**
- `halt_phase`: abstract "halting phase" — starting at `A,s3` with
  left = `rep s3 m ++ [s3, s1]`, the TM reaches `state = none` in
  `m + 3` steps.
- `all_s3_odd_overflow_halts`: the bad state
  `CycleStart (rep s3 n) (rep s2 (2*d)) 1` reaches `state = none`
  after exactly `6*d + 11 + n` further steps.
- `overflow_cycle_output_not_bad`: `overflow_cycle` never outputs
  all-zero ternary (its output ternary is `repPair s4 s2 d`,
  value `3^d - 1 ≠ 0`).
- `overflow_odd_k1_output_tern_not_all_zero`: `overflow_odd_k1`'s
  output ternary starts with `s0`, hence not all-`s2`.
- `bad_state_predecessor_forward`: the configuration
  `CycleStart (s2 :: rep s3 (n-1)) (s0 :: s2 :: rep s2 (2*(d-1))) 1`
  reaches the bad state in exactly 4 steps (via `cycle_d1_general`).

**Open (sorries in BackwardTrace.lean):**
- `cycle_nonzero_pred_bad_state` (uniqueness): the ONLY canonical
  predecessor of the bad state via any cycle_nonzero macro step is
  the configuration from `bad_state_predecessor_forward`. Proving this
  requires inverting the case disjunction inside `cycle_nonzero` —
  laborious but feasible.
- `all_s3_odd_overflow_unreachable_from_init`: the main open problem
  (bad state is never reachable from `initConfig`). Its proof, even
  modulo the uniqueness lemma above, still needs the 2-adic /
  Diophantine crux — i.e., Paths B or C remain necessary.

## What Dio.lean Contains (Path C.3 — precise Diophantine statement)

The file `Dio.lean` reduces the nonhalting claim to a **precise Diophantine
statement** about era-entry binary values.

### Derivation

At pad=1 era entry `(V_0, n_0, d)`, one runs `K = 3^d - 1` cycle_nonzero
steps. Each step: `V → V+1` or (when `V = 2^n - 1`) `V → 0, n → n+1`.
Writing `W` = number of wraps:

    n_end = n_0 + W
    V_end = (3^d - 1) + V_0 + 2^{n_0} - 2^{n_0+W}

The "bad" (all-s3) condition `V_end = 2^{n_end} - 1` reduces exactly to:

    V_0 + 2^{n_0} + 3^d = 2^{n_0+W+1}

i.e., **`V_0 + 2^{n_0} + 3^d` is a power of 2**.

### Formalized

**Proved** (`era_bad_iff_diophantine`, 2026-04-17):
```
IsBadEnd (eraEnd V n d).1 (eraEnd V n d).2 ↔ ∃ m, V + 2^n + 3^d = 2^m
```
This is a pure arithmetic fact — the reduction from TM dynamics to
a Diophantine equation is complete.

**Open** (`C3`, the main claim):
```
∀ V n d, IsReachableEraEntry V n d → ¬ ∃ m, V + 2^n + 3^d = 2^m
```

### Why C3 is hard

- **Simple parity fails**: `V` at era entries has no periodic mod-k behavior
  (empirical: T,F,T,T,T,F,F,F,... per `macro.md`).
- **Mihailescu / Catalan doesn't cover it**: Mihailescu resolves
  `2^m - 3^d = 1`. For C3 we need `2^m - 3^d = V + 2^n` to have no
  solution in *reachable* (V, n, d). The RHS ranges over a specific subset
  of `[2^n, 2^{n+1})`; Mihailescu handles only `V + 2^n = 1`.
- **Reachable set is recursive**: generated from `(V=2, n=2, d=4)` by the
  era→next-era transition (era end + odd overflow of k∈{0,1,≥2} + overflow_cycle).

### Consequence (`no_bad_end_if_C3`)

If C3 holds, combined with `BackwardTrace.all_s3_odd_overflow_halts` and
a backward-tracing analysis ruling out overflow_cycle / overflow_odd_*
as producers of the bad state, the nonhalt proof goes through.

## Revised recommendation (post-2026-04-17)

The mathematical task is now crisp: **prove C3**, i.e., show that for every
reachable era entry `(V, n, d)`, `V + 2^n + 3^d` is not a power of 2.

**Candidate paths** to close C3:

- **Path C-Mihailescu**: Leverage Mihailescu for small-V cases,
  combined with structural bounds on `(V, n, d)` triples.
- **Path B (computational bootstrap)**: Verify C3 for the first N eras by
  `native_decide` + `decide`. Then prove a structural property
  (e.g., a 2-adic invariant that eventually dominates) for i ≥ N.
- **Path "2-adic trajectory"**: Track the 2-adic valuation of
  `V + 2^n + 3^d` through the era transition. If `ν_2` has a controlled
  evolution, one may bound it away from `+∞` (i.e., from being a power
  of 2).
- **Path "lifting the exponent"**: Apply LTE / Zsygmondy-style
  theorems to rule out `2^m = V + 2^n + 3^d` for specific (V, n, d)
  structures.

**Short term (still recommended)**: Path A (revert field 8 in `machine.lean`,
handle overflow cases individually). This removes the false invariant.
With `Dio.lean` now providing the reduction, the proof structure becomes:
1. Handle k≥2 and all-s3 odd overflow cases.
2. Use `no_bad_end_if_C3` to conclude no bad state is reached.
3. Depend on `C3` as an axiomatic or (ideally) proved claim.

## Plan for proving k≥2 dynamics (and correcting k=1)

### Why this matters

The arithmetic `nextEra` function in `Dio.lean` closes the k=1 and k≥2
branches with closed-form formulas. **Neither is correct in general:**

- **k≥2 branch** (`V_end % 4 = 3`): the formula
  `V_new = (V_end - 1)/2, n_new = n_end - 1, d_new = d + 2` is a guess
  from macro.md's era 2. Simulation (below) disproves it.
- **k=1 branch** (`V_end % 4 = 1`): only the *single* macro-step
  `overflow_odd_k1` is proved in `machine.lean`, and its output leaves
  pad=1 with `tern = 1` (nonzero). The "next era entry" requires an
  additional `cycle_nonzero` step (bringing tern to 0) and then a
  further odd overflow (whose case is determined by the new V). The
  `nextEra` k=1 branch collapses this multi-step composition into a
  single formula, which is only valid when that follow-up overflow
  happens to be trivial — not in general.

Simulation for k≥2:

| Starting config | `nextEra`'s prediction | Actual first canonical (simulation) |
|-----------------|-------------------------|-----------------------------------|
| V=2851, n=12, d=8 (era 2 end from init) | V=1426, n=11, d=10 | V=1426, n=11, d=10 ✓ |
| V=11, n=4, d=2 (standalone test) | V=6, n=3, d=4 | V=56, n=6, d=7 ✗ |

The k≥2 formula coincidentally matches era 2 of the init trajectory
but fails for other k=2 configurations. From `V=11, n=4, d=2` the TM
takes 1152 steps, visits no intermediate canonical at pad=0, and
produces `(V=56, n=6, d=7)`.

**Every conclusion in `Probabilistic.lean` beyond era 2 is therefore
spurious as a statement about the TM.** The Dio arithmetic results
are still true **about the arithmetic sequence** defined by `nextEra`,
but that sequence has diverged from the TM's real trajectory from era
3 onward (the first era where a non-k=0 branch is invoked).

Rigorous status of `nextEra`:
- k=0 branch: faithful to the TM (backed by `overflow_odd`).
- k=1 branch: heuristic, may diverge when a chained overflow is needed.
- k≥2 branch: heuristic, disproved in general.

### Plan: Phase 1 — exhaustive simulation

**1.1** Use `sim.py` (or a dedicated Python/OCaml simulator) to run the
TM from many starting configurations with leading `rep s3 (k+1) ++ s2`
and record the resulting first canonical. Vary `k ∈ {2, 3, 4}`,
`d ∈ {2, 3, ...}`, and `bin_rest` over small values.

**1.2** Tabulate:
- step count `S(k, d, bin_rest)` from era end to first canonical
- output `(V_new, n_new, d_new, pad_new)`
- intermediate "non-canonical" structures encountered (ternary with
  `s0 s0` pairs, `s4 s4` pairs, etc.)

**1.3** Form a hypothesis about the macro-level transition. The known
k=2 structure "cascade produces k+1 consecutive s0 cells in ternary"
(per `macro.md`) is the starting point. The cascade must eventually
normalize these non-canonical cells into valid ternary pairs.

### Phase 2 — decompose the k≥2 dynamics into sub-macro-steps

From `machine.lean`, we already have these sub-macro-steps:
- `odd_overflow_cascade`: 6d+9 steps. Handles the initial bounce and
  leftward sweep through all-zero ternary and pad.
- `carry_step`: propagates carry through leading s3 bits.
- `carry_stop`: stops carry at a s2 bit.
- `overflow_carry`: propagates carry through all-s3 binary + terminator.

The k≥2 case will require NEW sub-macro-steps. Candidates:
- **`consume_s3_chain`** (k steps): after cascade, consume k leading
  s3 bits via A,s3→0LA writing s0 cells on the right.
- **`split_cascade`**: the head reads `s2` (the k-th bit that was not
  s3); A,s2→0RB enters state B on the first `s0` cell.
- **`normalize_s0_block`**: complex cascade that converts `s0 s0 s0 ...`
  (invalid ternary) into valid ternary pairs. This is the hardest.

### Phase 3 — formalize each sub-step

For each sub-macro-step:
1. Write the starting and ending `Config` as explicit structures.
2. Prove the `tmRun` equation using `tm_step` and the composed-step
   pattern (like `odd_overflow_cascade`).
3. Each sub-step theorem should be of the form:
   ```
   theorem <name> (params : …) (hyps : …) :
       run tm <input_config> <step_count_formula> = <output_config>
   ```

### Phase 4 — compose into `overflow_odd_k`

The target theorem:
```
theorem overflow_odd_k (k d : Nat) (bin_rest : List Sym)
    (hk : k ≥ 2)
    (hvalid : ∀ s ∈ bin_rest, s = s2 ∨ s = s3) :
    ∃ (S : Nat) (bin_new : List Sym) (d_new : Nat) (pad_new : Nat),
      0 < S ∧
      tmRun (CycleStart (rep s3 k ++ s2 :: bin_rest) (rep s2 (2*d)) 1) S =
        CycleStart bin_new <tern_new> pad_new ∧
      -- + consistency predicates on bin_new, d_new, pad_new
```

### Phase 5 — extract the value-level transition

Once `overflow_odd_k` is proved, compute the arithmetic image
`(V_end, n_end, d, pad) → (V_new, n_new, d_new, pad_new)` as a
Lean-level function. This replaces the incorrect `nextEra`'s k≥2
branch in `Dio.lean`.

### Phase 6 — refactor downstream files

- Update `Dio.lean`: replace the heuristic k=1 and k≥2 branches in
  `nextEra` with the proven arithmetic transitions from Phase 5
  (including the chained-overflow composition for k=1).
- Re-verify the `∀ i < 21, eraHasBadV i = false` check in
  `Probabilistic.lean` with the corrected `nextEra`.
- Potentially prove `arith_reachable_iff_TM` (the bridging conjecture
  in `Dio.lean`).

### Effort estimate

- Phase 1 (simulation): 4–8 hours of Python work.
- Phase 2 (decomposition): highly dependent on Phase 1 findings;
  expect 2–4 sub-macro-steps of varying complexity.
- Phase 3 (formalization): 200–600 lines of Lean per sub-step;
  total maybe 800–1500 lines.
- Phase 4–5 (composition & arithmetic): 200–300 lines.
- Phase 6 (downstream): mostly mechanical, 100 lines.

**Total estimate**: 1500–2500 lines of Lean, 2–4 weeks of focused work,
assuming the decomposition in Phase 2 yields tractable sub-steps.

### Key risk

If the k≥2 cascade doesn't decompose cleanly into a small number of
sub-macro-steps — e.g., if `normalize_s0_block` itself requires a
non-terminating-looking inductive structure — then this plan is
infeasible and we'd need Path B (computational bootstrap) for the
first N eras, then prove a NEW structural invariant that handles
k≥2 without explicit dynamics.

### Parallel work

Even while k≥2 remains unproved, Phase 1 (simulation) immediately
produces a **correct but un-axiomatized** `nextEra` for the k≥2
branch. Using this in `Dio.lean` / `Probabilistic.lean` as a
*computationally-tested hypothesis* (rather than an arithmetic
formula based on incorrect intuition) gives rigorous *computational*
results matching the TM's actual trajectory — even before Phase 2–6
are done.
