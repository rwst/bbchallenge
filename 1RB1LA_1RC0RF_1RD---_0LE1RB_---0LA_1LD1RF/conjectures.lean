/-
Empirical conjectures from era-sim experiments.

Statements that have been verified by the Rust `era-sim` tool over a wide
numerical range but are not yet proved. Each conjecture is stated as a
`theorem` with `sorry` and includes the empirical evidence that supports
it (range checked, tool used, generating script).

The conventions here mirror `era.lean`:
- Era-start shape is `M(L, c, [1])`.
- One full era is `Sweeper.macroEra fuel` from era-start to next era-start
  (the next macroStep that fires `era_and_sweep` or `era_and_sweep_solo`).
-/

import era

namespace Sweeper

open BusyLean

-- ============================================================
-- F2 family: synthetic era starts `M [1] c [1]` with c even
-- ============================================================
--
-- Define `f2_start k := M [1] (2^(k+1) - 4) [1]` for k ≥ 2.
-- This corresponds to era-sim's family F2 at parameter `n = 2^k - 3`,
-- since c = 2n + 2 = 2(2^k - 3) + 2 = 2^(k+1) - 4.
--
-- For k = 2 this is the actual TM initial state `M [1] 4 [1]`.
-- For k ≥ 3 the start state is synthetic (off the reachable orbit a priori).
--
-- Empirical observation (era-sim, /tmp/F2_max_verify.tsv):
-- starting from `f2_start k`, exactly one era completes after
-- `2^(k+1) - k - 2` macro steps, ending at `M [1] (2^(k+1) + 2(k-1)) [1]`.
-- Verified for k = 2..28 with zero exceptions (n up to 2.68 × 10^8).
--
-- Significance: a(2^k - 3) is the *maximum* of the F2 recurrence on the
-- dyadic block [2^(k-1), 2^k - 1] (also empirical, all checked blocks).
-- The clean closed form is the strongest 2-adic structural signal yet
-- observed in the F2 dynamics; it is a candidate building block for
-- closing R1 via the algebraic-invariant route (`plan-sim-era.md` Plan 5).

/-- **F2 max-formula conjecture.** Starting from the era-boundary shape
    `M [1] (2^(k+1) - 4) [1]` (i.e. F2 family at `n = 2^k - 3`), one full
    era completes in exactly `2^(k+1) - k - 2` macro steps and produces
    the next era-start `M [1] (2^(k+1) + 2(k-1)) [1]`.

    Both sides have `L = [1]` and `R = [1]`; only the cursor `c` changes
    (from `2^(k+1) - 4` to `2^(k+1) + 2(k-1)`).

    Empirical verification: `era-sim --scan C` for `n = 2^k - 3`,
    k = 2..28 (n up to 2.68 × 10^8 raw TM steps ~ 10^15). Zero
    counterexamples; per-row data in `/tmp/F2_max_verify.tsv`.

    Sketch of a proof strategy: induction on k. Base case k=2 is the
    era-0 fact already proved as `orbit_reachable_era0_end`
    (`progress.lean`), which witnesses
    `(macroEra 4 (.M [1] 4 [1])).2 = .M [1] 10 [1]`. Inductive step
    requires showing the era trace from `M [1] (2^(k+2) - 4) [1]`
    decomposes as: (i) `2^k` sweeps to `M [2^k] 2 [2^k]`, (ii) one
    sweep_to_zero to `M0 [2^k + 1] [2^k + 1]`, (iii) a chain of
    zero_bounce / sweep / sweep_to_zero / zero_bounce_to_zero rules
    that mirrors the `f2_start k` trace shifted by 2^k, then
    (iv) era_and_sweep_solo. The doubling structure of the bridge
    matches `era_findings.md` §"R3 doubling-chain" (k-1 = chain_len). -/
theorem f2_max_era_step (k : Nat) (hk : k ≥ 2) :
    (Sweeper.macroEra (2^(k+1) - k - 2) (.M [1] (2^(k+1) - 4) [1])).2
      = .M [1] (2^(k+1) + 2 * (k - 1)) [1] := by
  sorry

/-- Concrete sanity check: the k = 2 instance of `f2_max_era_step` is the
    era-0 transition. This is provable by `rfl` (and matches the existing
    `orbit_reachable_era0_end` witness in `progress.lean`). -/
theorem f2_max_era_step_k2 :
    (Sweeper.macroEra 4 (.M [1] 4 [1])).2 = .M [1] 10 [1] := rfl

end Sweeper
