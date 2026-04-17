import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum
import machine

/-!
# Dio — the Diophantine statement of Path C.3

This file derives and states the precise mathematical claim that, once
proved, would close the nonhalting proof of TM
`1RB---0RB0LA2RA_2LB2LA3RA4LB0LB` via Path C.

## Background (from `strategy.md` and `macro.md`)

The TM's canonical trajectory consists of macro-steps:
- `cycle_nonzero` (ternary nonzero): one "digit" step, increments binary by 1
  with possible wrap.
- `overflow_cycle` (ternary all-zero, pad=0): enters a pad=1 era with
  ternary re-initialized to `3^d - 1`.
- `overflow_odd_*` (pad=1, ternary all-zero): exits the pad=1 era.

The "bad state" is a canonical with pad=1, ternary all-zero, binary all-s3
(`rep s3 n`). By `BackwardTrace.all_s3_odd_overflow_halts`, this state
reaches `state = none` in finitely many steps — i.e., the TM halts.
The nonhalting proof therefore requires the bad state to be unreachable.

## Derivation (k=0 wrap accounting)

Let `(V_0, n_0, d)` be an era entry: `V_0 < 2^{n_0}` is the binary value,
`n_0` the binary length, `d` the ternary pair count. The era runs for
`K = 3^d - 1` `cycle_nonzero` steps, each applying `V → V+1` (no wrap)
or `V → 0, n → n+1` (wrap, when `V = 2^n - 1`).

**Claim (computed in §`era_step` below)**: after `K` steps, the state is
`(V_end, n_end)` where, writing `W` = number of wraps during the era:

    n_end = n_0 + W
    V_end = 3^d + V_0 + 2^{n_0} - 1 - 2^{n_0+W}

where `W` is the unique natural number satisfying
`f(W) ≤ K < f(W+1)` with `f(w) = (2^w - 1) · 2^{n_0} - V_0`.

**Bad condition** (`V_end = 2^{n_end} - 1`):

    2^{n_0+W} - 1 = 3^d + V_0 + 2^{n_0} - 1 - 2^{n_0+W}
    2^{n_0+W+1} = V_0 + 2^{n_0} + 3^d

So the bad state at the end of an era `(V_0, n_0, d)` occurs **iff**
`V_0 + 2^{n_0} + 3^d` is a power of 2.

## The Diophantine statement (C.3)

The nonhalting proof via Path C reduces to:

> **C.3 (Diophantine claim)**: For every reachable pad=1 era entry
> `(V_0, n_0, d)` of the TM's trajectory from `initConfig`,
>     V_0 + 2^{n_0} + 3^d   is *not* a power of 2.

Equivalently: `2^m - 3^d = V_0 + 2^{n_0}` has no solution in `m` for any
reachable `(V_0, n_0, d)`. Note `2^{n_0} ≤ V_0 + 2^{n_0} < 2^{n_0+1}`,
so this constrains `2^m - 3^d` to lie in a specific window
`[2^{n_0}, 2^{n_0+1})`.

The set of reachable era entries is generated recursively from
`E_0 = (V_0 = 2, n_0 = 2, d = 4)` by the era→next-era transition
(which involves multiple odd-overflow sub-cases). Closing C.3 requires
analyzing this recursive set and ruling out all power-of-2 sums.

## What this file provides

1. `wraps V n d`: the number of wraps during an era (Nat-level).
2. `eraEnd V n d`: the pair `(V_end, n_end)`.
3. `era_bad_iff_diophantine`: equivalence between
   "era ends in bad state" and "V + 2^n + 3^d is a power of 2" (provable).
4. `IsReachableEraEntry`: predicate asserting the era entry is reached by
   the TM's trajectory (using full TM dynamics).
5. `C3`: the main Diophantine claim. **Open.**
-/

set_option autoImplicit false

open BB2x5

namespace TM5.Dio

-- ============================================================
-- §1. Value-level era dynamics
-- ============================================================

/-- Position of the `w`-th wrap during an era started at `(V, n)`.
    `f(0) = 0`, `f(1) = 2^n - V`, and generally `f(w+1) = f(w) + 2^{n+w}`.
    Closed form: `f(w) = (2^w - 1) · 2^n - V` (for `w ≥ 0`; for `w = 0`, empty). -/
def wrapPos (V n w : Nat) : Nat := (2^w - 1) * 2^n - V

/-- The number of wraps during `K` cycle_nonzero steps starting from `(V, n)`.
    Uniquely defined as the max `w` with `wrapPos V n w ≤ K`. We compute it
    as `Nat.log 2 (V + 2^n + K) - n`, which gives the correct value since
    `wrapPos V n w ≤ K ↔ 2^{n+w} ≤ V + 2^n + K` (by rearranging). -/
def wraps (V n K : Nat) : Nat := Nat.log 2 (V + 2^n + K) - n

/-- The era-end state `(V_end, n_end)` after `K = 3^d - 1` cycle_nonzero
    steps starting from `(V, n)`.

    By the derivation in the header:
      n_end = n + W
      V_end = K + V + 2^n - 2^{n+W}
    where `W = wraps V n K`. -/
def eraEnd (V n d : Nat) : Nat × Nat :=
  let K := 3^d - 1
  let W := wraps V n K
  (K + V + 2^n - 2^(n + W), n + W)

/-- The era end state is "bad" iff `V_end = 2^{n_end} - 1`. -/
def IsBadEnd (V_end n_end : Nat) : Prop := V_end = 2^n_end - 1

-- ============================================================
-- §2. The core equivalence (provable)
-- ============================================================

/-- **Core derivation**: For era entry `(V, n, d)` with `V < 2^n`, `n ≥ 1`,
    `d ≥ 1`, the era ends in a bad state (all-s3 binary) iff
    `V + 2^n + 3^d` is a power of 2.

    This is the mathematically-precise statement of the Diophantine condition
    — it's provable from the `wraps`/`eraEnd` definitions and Nat.log
    arithmetic.

    Proof sketch:
    - Let `W = wraps V n K` with `K = 3^d - 1`. By definition,
      `2^{n+W} ≤ V + 2^n + K = V + 2^n + 3^d - 1 < 2^{n+W+1}`.
    - Plug into `eraEnd`:
        `V_end = K + V + 2^n - 2^{n+W}`
        `n_end = n + W`
      Then `V_end = 2^{n_end} - 1 ↔ 2·2^{n+W} = V + 2^n + 3^d`, i.e.,
      `V + 2^n + 3^d = 2^{n+W+1}`, i.e., it's a power of 2.
-/
theorem era_bad_iff_diophantine (V n d : Nat)
    (hV : V < 2^n) (hn : n ≥ 1) (_hd : d ≥ 1) :
    IsBadEnd (eraEnd V n d).1 (eraEnd V n d).2 ↔
    ∃ m, V + 2^n + 3^d = 2^m := by
  -- Constant facts
  have h3d : 3^d ≥ 1 := Nat.one_le_pow _ _ (by omega)
  have h2n : 2^n ≥ 2 := by
    calc 2 = 2^1 := (pow_one 2).symm
      _ ≤ 2^n := Nat.pow_le_pow_right (by omega) hn
  have hpos : V + 2^n + (3^d - 1) ≥ 2^n := by omega
  -- Let M = n + W = Nat.log 2 (V + 2^n + (3^d - 1)) (via our definition of `wraps`)
  have hlog_eq : n + (Nat.log 2 (V + 2^n + (3^d - 1)) - n) = Nat.log 2 (V + 2^n + (3^d - 1)) := by
    have := Nat.le_log_of_pow_le (b := 2) (by decide) hpos
    omega
  -- Evaluate eraEnd
  have h_end : eraEnd V n d = (3^d - 1 + V + 2^n - 2^(Nat.log 2 (V + 2^n + (3^d - 1))),
                                Nat.log 2 (V + 2^n + (3^d - 1))) := by
    unfold eraEnd wraps
    dsimp only
    rw [hlog_eq]
  rw [h_end]
  -- Shortcut: let L = Nat.log 2 (V + 2^n + (3^d - 1)), P = 2^L
  set L := Nat.log 2 (V + 2^n + (3^d - 1)) with hL_def
  have hP_pos : 2^L ≥ 1 := Nat.one_le_pow _ _ (by omega)
  have hP_le : 2^L ≤ V + 2^n + (3^d - 1) := Nat.pow_log_le_self 2 (by omega)
  have hP_lt : V + 2^n + (3^d - 1) < 2 * 2^L := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by decide) (V + 2^n + (3^d - 1))
    rw [pow_succ, Nat.mul_comm] at h
    exact h
  simp only [IsBadEnd]
  constructor
  · -- 3^d - 1 + V + 2^n - 2^L = 2^L - 1 → ∃ m, V + 2^n + 3^d = 2^m
    intro h_eq
    refine ⟨L + 1, ?_⟩
    rw [pow_succ]
    -- Goal: V + 2^n + 3^d = 2^L * 2
    omega
  · -- ∃ m, V + 2^n + 3^d = 2^m → 3^d - 1 + V + 2^n - 2^L = 2^L - 1
    intro ⟨m, hm⟩
    -- Derive m ≥ 1
    have h_m_ge_1 : m ≥ 1 := by
      rcases m with _ | m'
      · simp at hm; omega
      · omega
    -- 2^m = 2 * 2^(m-1)
    have h_2m_split : (2 : Nat)^m = 2 * 2^(m-1) := by
      conv_lhs => rw [show m = (m-1) + 1 from by omega]
      rw [pow_succ]; omega
    have h_2m1_pos : (2 : Nat)^(m-1) ≥ 1 := Nat.one_le_pow _ _ (by omega)
    -- Show L = m - 1, hence 2^L = 2^(m-1)
    have hL_eq : L = m - 1 := by
      rw [hL_def]
      apply Nat.log_eq_of_pow_le_of_lt_pow
      · -- 2^(m-1) ≤ V + 2^n + (3^d - 1): use hm to rewrite
        omega
      · -- V + 2^n + (3^d - 1) < 2^((m-1)+1) = 2^m
        rw [show m - 1 + 1 = m from by omega]
        omega
    rw [hL_eq]
    -- Goal: 3^d - 1 + V + 2^n - 2^(m-1) = 2^(m-1) - 1
    omega

-- ============================================================
-- §3a. The arithmetic era recurrence (purely number-theoretic)
-- ============================================================

/-!
We give a purely-arithmetic definition of "next era entry", independent
of the TM's step function. This makes C.3 a pure Diophantine/number-theoretic
statement over an arithmetically-defined sequence.

The transition from era entry `(V, n, d)` to the next is governed by
three TM-level cases, only ONE of which is formalized:

1. Compute `(V_end, n_end) := eraEnd V n d` (the pad=1 era end).
2. **Halting branch**: if `V_end = 2^{n_end} - 1` (all-s3 binary), the
   trajectory halts ("bad" state).
3. **k=0 branch** (`V_end` even): **proved** as `machine.overflow_odd`
   (6d+9 steps). The odd overflow maps `V_end → V_end/2, n_end → n_end - 1`,
   leaving pad=0 with tern=0. Then `overflow_cycle` increments (or wraps).
4. **k=1 branch** (`V_end ≡ 1 mod 4`, not all-s3): the single-macro-step
   `machine.overflow_odd_k1` is proved, but its output is pad=1 with
   `tern=1` (non-zero). Reaching the next pad=1 era entry requires an
   *additional* cycle_nonzero step (dropping tern to 0) and then another
   odd overflow whose case depends on the new V. The net transition is
   therefore a multi-step composition, not a single formula.
5. **k≥2 branch** (`V_end ≡ 3 mod 4`, not all-s3): **no macro-step theorem
   exists** in `machine.lean`. Simulation of `(V=11, n=4, d=2, pad=1)`
   (a concrete k=2 test case) shows the TM takes 1152 steps before
   reaching any canonical and arrives at `(V=56, n=6, d=7)` —
   inconsistent with any simple closed-form formula on `V_end`.

The `nextEra` function below models branches (3)–(5) with closed-form
approximations. The k=0 branch matches `overflow_odd` exactly. The k=1
and k≥2 branches are **heuristic approximations** that coincidentally
match some eras of the init trajectory (e.g., era 2 → era 3 under the
k≥2 branch matches macro.md) but are NOT universally correct. See
`strategy.md` for the plan to replace them with a proven transition.

The arithmetic claims in `Probabilistic.lean` and the `C3` theorem
below are statements about the sequence `eraSeq` generated by this
(partly heuristic) `nextEra`. They only correspond to the TM's actual
trajectory when every era along the way uses the k=0 branch; this
holds rigorously for eras 0, 1, and 2 of the init trajectory, and is
open thereafter.
-/

/-- One arithmetic "era step": given an era entry `(V, n, d)`,
    compute the next era entry, or `none` if the trajectory halts
    (bad state) at this era.

    - The k=0 branch (`V_end % 2 = 0`) is backed by `machine.overflow_odd`.
    - The k=1 branch (`V_end % 4 = 1`) is a heuristic approximation;
      the true net transition is a composition of `overflow_odd_k1`,
      one `cycle_nonzero`, and a second odd overflow whose case depends
      on intermediate data.
    - The k≥2 branch (`V_end % 4 = 3`) is a heuristic approximation
      disproved in general by simulation (see `strategy.md`).
-/
def nextEra (V n d : Nat) : Option (Nat × Nat × Nat) :=
  let end_pair := eraEnd V n d
  let V_end := end_pair.1
  let n_end := end_pair.2
  if V_end = 2^n_end - 1 then none  -- halting
  else
    -- Post-odd-overflow state at pad=0 with some (V_mid, n_mid):
    let V_mid : Nat :=
      if V_end % 2 = 0 then V_end / 2                     -- k=0 (rigorous)
      else if V_end % 4 = 1 then (V_end - 1) / 4          -- k=1 (heuristic)
      else (V_end - 1) / 2                                 -- k≥2 (heuristic, disproved in general)
    let n_mid : Nat :=
      if V_end % 2 = 0 then n_end - 1
      else if V_end % 4 = 1 then n_end - 2
      else n_end - 1                                       -- k≥2
    let d_mid := d + 2
    -- Then overflow_cycle: V_mid → V_mid + 1 with possible wrap at V_mid = 2^n_mid - 1.
    if V_mid = 2^n_mid - 1 then
      some (0, n_mid + 1, d_mid)
    else
      some (V_mid + 1, n_mid, d_mid)

/-- The initial era entry after the TM's startup (step 117 corresponds to
    `CycleStart [s3, s2] (rep s2 8) 0`; the first overflow_cycle applied
    yields `(V=2, n=2, d=4)` at pad=1). -/
def E0 : Nat × Nat × Nat := (2, 2, 4)

/-- The arithmetic era-entry sequence: `eraSeq 0 = some E0`,
    `eraSeq (i+1) = nextEra(eraSeq i)`. Yields `none` once the trajectory
    would halt at the bad state. -/
def eraSeq : Nat → Option (Nat × Nat × Nat)
  | 0 => some E0
  | i + 1 =>
    match eraSeq i with
    | none => none
    | some (V, n, d) => nextEra V n d

/-- Arithmetic reachability: `(V, n, d)` is reachable iff it appears in the
    arithmetic era-entry sequence. Purely number-theoretic. -/
def ArithReachable (V n d : Nat) : Prop :=
  ∃ i, eraSeq i = some (V, n, d)

-- ============================================================
-- §3b. TM-level reachability (for comparison / bridging)
-- ============================================================

/-- A pad=1 era entry of the TM: after `overflow_cycle`, the TM is at
    `CycleStart bin (repPair s4 s2 d) 1` with valid binary `bin` of length `n`
    encoding value `V`. -/
def IsEraEntry (V n d : Nat) (bin : List Sym) : Prop :=
  (∀ s ∈ bin, s = s2 ∨ s = s3) ∧
  bin.length = n ∧
  TM5.binValue bin = V ∧
  bin ≠ [] ∧
  d ≥ 1

/-- An era entry is *reachable* from `initConfig` via the TM's dynamics. -/
def IsReachableEraEntry (V n d : Nat) : Prop :=
  ∃ (bin : List Sym) (k : Nat),
    IsEraEntry V n d bin ∧
    run tm initConfig k = CycleStart bin (repPair s4 s2 d) 1

/-- **Bridging conjecture**: the arithmetic era-sequence matches the TM's
    actual reachable era entries. I.e., `ArithReachable V n d` holds for
    `(V, n, d)` iff the TM actually reaches that era entry.

    **Currently false as stated** because the k=1 and k≥2 branches of
    `nextEra` do not faithfully model the TM. A corrected `nextEra`
    (implementing the true multi-step composition for k=1 and the TBD
    dynamics for k≥2) would be needed before this bridge can hold.
    The forward direction `ArithReachable → IsReachableEraEntry` would
    then hold by construction; the backward direction would require
    proving the TM's trajectory only passes through era entries of the
    claimed form (no side branches). Both directions depend on
    formalizing k≥2 dynamics. -/
theorem arith_reachable_iff_TM (V n d : Nat) :
    ArithReachable V n d ↔ IsReachableEraEntry V n d := by
  sorry

-- ============================================================
-- §4. The main Diophantine claim (OPEN)
-- ============================================================

/-- **C.3 (pure number-theoretic statement)**:

    For every era entry `(V, n, d)` in the arithmetic sequence `eraSeq`
    starting at `E0 = (2, 2, 4)`, `V + 2^n + 3^d` is NOT a power of 2.

    This is a pure Diophantine claim: it depends only on
    - the arithmetic functions `wraps`, `eraEnd`, `nextEra`, `eraSeq`;
    - the power-of-2 predicate.

    No reference to the TM's `step`, `run`, or `Config`.

    Combined with `era_bad_iff_diophantine`, this means no era in the
    arithmetic sequence ever produces the "bad" end-state
    `V_end = 2^{n_end} - 1`. Combined with `arith_reachable_iff_TM` (the
    bridging conjecture) and `BackwardTrace.all_s3_odd_overflow_halts`,
    it closes the nonhalting proof. -/
theorem C3 (V n d : Nat) (h : ArithReachable V n d) :
    ¬ ∃ m, V + 2^n + 3^d = 2^m := by
  sorry

/-! ### Why C.3 is nontrivial

- `claude-said.txt` notes that no *simple* mod-based invariant captures
  this (the parity of `V` at era entries is not periodic; the mod-4,
  mod-8 patterns all fail empirically).

- The set of arithmetically-reachable `(V, n, d)` is generated by a
  nonlinear recurrence (era → odd overflow → overflow_cycle → next era)
  that resists closed-form analysis.

- The Diophantine equation `V + 2^n + 3^d = 2^m` (for fixed `d, n`) has
  up to one solution in `V` (if `2^m - 3^d` lies in `[2^n, 2^{n+1})`).
  So C.3 amounts to: for each reachable `(n_i, d_i)`, the *specific*
  `V_i` avoids this one "bad" value.

- Mihailescu's theorem (Catalan): `2^m - 3^d = 1` has only `(m, d) = (2, 1)`.
  This handles `V + 2^n = 1`, i.e., `V = 0, n = 0` — but that's not a
  reachable era entry. So Mihailescu alone is insufficient.

### Approaches

- **Path B (computational bootstrap)**: verify the first N era entries
  by `native_decide`, then derive a structural invariant for i ≥ N.
- **Path C (pure 2-adic / Diophantine)**: analyze the recurrence's
  2-adic behavior.
- **Hybrid**: use computation to exclude low-m cases, then Mihailescu
  or similar for high-m cases.
-/

-- ============================================================
-- §5. Connection to the nonhalting proof
-- ============================================================

/-- If C.3 holds, then no era reaches the bad state. Combined with
    `BackwardTrace.all_s3_odd_overflow_halts`, this gives nonhalting for all
    eras that *do* end at a canonical (i.e., don't hit k≥2 or all-s3
    pathological cases).

    This theorem records the final reduction; it is a direct consequence
    of `C3` and `era_bad_iff_diophantine`. -/
theorem no_bad_end_if_C3 (V n d : Nat)
    (hV : V < 2^n) (hn : n ≥ 1) (_hd : d ≥ 1)
    (h_reach : ArithReachable V n d) :
    ¬ IsBadEnd (eraEnd V n d).1 (eraEnd V n d).2 := by
  rw [era_bad_iff_diophantine V n d hV hn _hd]
  exact C3 V n d h_reach

end TM5.Dio
