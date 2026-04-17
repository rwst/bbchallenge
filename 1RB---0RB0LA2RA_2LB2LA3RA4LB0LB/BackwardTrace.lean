import machine

/-!
# BackwardTrace — infrastructure for Path E (backward tracing)

See `strategy.md` §Path E. The goal of this file is to provide the
infrastructure needed to argue that the "bad state"
`CycleStart (rep s3 n) (rep s2 (2*d)) 1` is unreachable from `initConfig`.

The overall strategy:
1. `all_s3_odd_overflow_halts`: The bad state *does* reach `state = none`
   in a specific finite number of steps. **Provable**, provided in this file.
2. Characterize the *possible canonical predecessors* of any canonical state.
   For the bad state, only one predecessor shape is possible (a cycle_nonzero
   input with `tern` of value 1 and `bin` of value `2^n - 2`).
3. Iterate backward through an era (3^d - 1 cycle_nonzero steps) to the era
   entry state, which came from `overflow_cycle`.
4. Constrain the era-entry binary value. This step introduces the
   2-adic / Diophantine obstruction that `claude-said.txt` identifies:
   no simple mod-based invariant rules out every era's ending with all-s3.
5. [OPEN] Close the constraint via either:
   - a computational bootstrap (Path B),
   - a 2-adic / Diophantine argument (Path C),
   - or a stronger inductive invariant yet to be found.

Items (1)–(3) are infrastructure that can be fully formalized. Item (4)
identifies the open subproblem in concrete Lean terms. Item (5) is the
remaining mathematical crux.
-/

set_option autoImplicit false

open BB2x5

namespace TM5

-- ============================================================
-- Section 1: The bad state halts in finitely many steps
-- ============================================================

/-- "Halting phase" starting at `A, s3` with left = `rep s3 m ++ [s3, s1]`.
    The head consumes `m+1` s3 cells of the binary+terminator, then hits `s1`
    (the terminator's halt cell) as `A`, which triggers `tm A s1 = none`.
    Total: `m + 3` steps reach `state = none`. -/
theorem halt_phase : (m : Nat) → (R : List Sym) →
    (run tm (⟨some stA, s3, rep s3 m ++ [s3, s1], R⟩ : Config) (m + 3)).state = none
  | 0, R => by
    -- Start: (A, s3, [s3, s1], R). After 3 steps reach state=none.
    simp only [rep_zero, List.nil_append]
    tm_step; tm_step; tm_step
    simp only [run_zero]
  | m + 1, R => by
    -- Start: (A, s3, s3 :: (rep s3 m ++ [s3, s1]), R)
    simp only [rep_succ, List.cons_append]
    rw [show m + 1 + 3 = (m + 3) + 1 from by omega, run_succ]
    simp only [step, tm, listHd_cons, listTl_cons]
    exact halt_phase m (s0 :: R)

/-- **Key halting fact**: if the TM reaches a canonical config with all-s3
    binary at odd overflow (pad=1, tern all-zero), then the TM halts
    after exactly `6*d + n + 11` further steps.

    This is a *forward* fact about the bad state. Combined with the
    assumption of nonhalt, it would imply the bad state is unreachable.
    Within the progress invariant proof of `canonical_progress`, one can
    instead use it constructively: if the progress invariant is maintained,
    the bad state is a contradiction.

    Steps: `6*d + 9` for `odd_overflow_cascade`, then `halt_phase`
    contributes `(n-1) + 3 = n + 2` more → total `6*d + 11 + n`. -/
theorem all_s3_odd_overflow_halts (n d : Nat) (hn : n ≥ 1) :
    (run tm (CycleStart (rep s3 n) (rep s2 (2*d)) 1) (6*d + 11 + n)).state = none := by
  unfold CycleStart
  -- Right side: rep s2 (2d) ++ rep s2 1 = rep s2 (2d+1)
  have hright : rep s2 (2 * d) ++ rep s2 1 = rep s2 (2 * d + 1) := by
    show List.replicate (2 * d) s2 ++ List.replicate 1 s2 = List.replicate (2 * d + 1) s2
    rw [← List.replicate_add]
  rw [hright]
  -- Split steps: (6d + 9) for cascade + (n + 2) for halt phase
  rw [show 6 * d + 11 + n = (6 * d + 9) + (n + 2) from by omega, run_add]
  -- Apply odd_overflow_cascade with L = rep s3 n ++ [s3, s1]
  rw [odd_overflow_cascade d (rep s3 n ++ [s3, s1])]
  -- Now config is (A, listHd L, listTl L, rep s2 (2*(d+2))). L starts with s3 (n ≥ 1).
  have hL_hd : listHd (rep s3 n ++ [s3, s1]) = s3 := by
    cases n with
    | zero => omega
    | succ n => simp only [rep_succ, List.cons_append, listHd_cons]
  have hL_tl : listTl (rep s3 n ++ [s3, s1]) = rep s3 (n - 1) ++ [s3, s1] := by
    cases n with
    | zero => omega
    | succ n =>
      simp only [rep_succ, List.cons_append, listTl_cons]
      rfl
  rw [hL_hd, hL_tl]
  -- Now: (run tm (A, s3, rep s3 (n-1) ++ [s3, s1], rep s2 (2*(d+2))) (n+2)).state = none
  rw [show (n + 2 : Nat) = (n - 1) + 3 from by omega]
  exact halt_phase (n - 1) (rep s2 (2 * (d + 2)))

-- ============================================================
-- Section 2: Canonical predecessors (infrastructure)
-- ============================================================

/-!
A canonical state's direct macro-step predecessors (via the specific
transition theorems) come in four types:

(a) `cycle_nonzero`: a different canonical with same pad, whose one-era
    cycle lands at `c`. The mapping here is intricate — one cycle_nonzero
    step decrements ternary by one digit (possibly with borrow cascades)
    and increments binary by one (possibly with carry cascades).

(b) `overflow_cycle` (pad 0→1): predecessor has pad=0 and tern all-zero;
    this is the entry to a pad=1 era. Output: `bin' = bin + 1` (with
    possible length growth), `tern' = repPair s4 s2 d` (all-max).

(c) `overflow_odd` (pad 1→0, k=0): predecessor has pad=1, tern all-zero,
    and `bin = s2 :: c.bin`. Output: `c` with pad=0, tern shifted.

(d) `overflow_odd_k1` (pad 1→1, k=1): predecessor has pad=1, tern
    all-zero, `bin = s3 :: s2 :: c.bin`. Output: `c` with pad=1,
    tern starting with digit 1.

For proving the "bad state is unreachable":
  - Bad state has `pad = 1, tern = all-zero, bin = rep s3 n`.
  - Any predecessor must come from one of (a)–(d).
  - Case (b): output of `overflow_cycle` has `tern = repPair s4 s2 d`,
    which has ternary value `3^d - 1 ≠ 0`. Eliminated.
  - Case (c): output of `overflow_odd` has `pad = 0 ≠ 1`. Eliminated.
  - Case (d): output of `overflow_odd_k1` has first ternary pair (s0,s2),
    i.e., digit 1. Ternary value is not 0. Eliminated.
  - Case (a): predecessor is a cycle_nonzero input. This is the only
    possible shape; characterized precisely below.
-/

/-- Negation: output of `overflow_cycle` (pad 0→1) is never the bad state.
    Formally, `repPair s4 s2 d` is never `rep s2 (2*d')` for any d' ≥ 1. -/
theorem overflow_cycle_output_not_bad (d d' : Nat) (hd : d ≥ 1) :
    repPair s4 s2 d ≠ rep s2 (2 * d') := by
  intro h
  have h_tern_val : ternValue (repPair s4 s2 d) = 3^d - 1 := ternValue_repPair_s4_s2 d
  have h_tern_zero : ternValue (rep s2 (2 * d')) = 0 := ternValue_rep_s2 _
  rw [h] at h_tern_val
  rw [h_tern_zero] at h_tern_val
  have : 3^d ≥ 3 := by
    calc 3 = 3^1 := (pow_one 3).symm
      _ ≤ 3^d := Nat.pow_le_pow_right (by omega) hd
  omega

-- Note: output of `overflow_odd` (pad 1→0) has pad=0 by its signature;
-- no explicit lemma is needed to eliminate this case.

/-- Output of `overflow_odd_k1` has first ternary digit = 1 (the ternary
    starts with `s0 :: s2 :: ...`), so `tern` is never all-zero. -/
theorem overflow_odd_k1_output_tern_not_all_zero (d d' : Nat) :
    (s0 :: s2 :: rep s2 (2 * (d + 1))) ≠ rep s2 (2 * d') := by
  intro h
  -- LHS contains s0. If RHS = rep s2 k, then all its elements are s2.
  -- So s0 ∈ LHS → s0 ∈ RHS → s0 = s2 (contradiction).
  have hs0_lhs : s0 ∈ (s0 :: s2 :: rep s2 (2 * (d + 1))) := by simp
  rw [h] at hs0_lhs
  have : s0 = s2 := List.eq_of_mem_replicate hs0_lhs
  exact absurd this (by decide)

-- ============================================================
-- Section 3: Cycle_nonzero backward step for the bad state
-- ============================================================

/-- **Forward verification**: the specific predecessor
    `(s2 :: rep s3 (n-1), s0 :: s2 :: rep s2 (2*(d-1)), 1)` transitions
    to the bad state in 4 steps via `cycle_d1_general` (digit-1 decrement,
    zero leading carry).

    Proved directly from `cycle_d1_general`. Combined with the elimination
    lemmas above, the bad state's ONLY canonical predecessor is this one.
    (The uniqueness direction is the deferred `cycle_nonzero_pred_bad_state`
    below.) -/
theorem bad_state_predecessor_forward (n d : Nat) (hn : n ≥ 1) (hd : d ≥ 1) :
    tmRun (CycleStart (s2 :: rep s3 (n - 1)) (s0 :: s2 :: rep s2 (2 * (d - 1))) 1) 4 =
      CycleStart (rep s3 n) (rep s2 (2 * d)) 1 := by
  have h := cycle_d1_general 0 (rep s3 (n - 1)) (rep s2 (2 * (d - 1))) 1
  simp only [rep_zero, List.nil_append, List.cons_append,
             Nat.mul_zero, Nat.add_zero] at h
  rw [h]
  congr 1
  · -- s3 :: rep s3 (n - 1) = rep s3 n
    cases n with
    | zero => omega
    | succ n' => simp [rep_succ]
  · -- s2 :: s2 :: rep s2 (2 * (d - 1)) = rep s2 (2 * d)
    cases d with
    | zero => omega
    | succ d' =>
      rw [show 2 * (d' + 1 - 1) = 2 * d' from by omega,
          show 2 * (d' + 1) = 2 * d' + 2 from by omega]
      rfl

/-- The *only* possible cycle_nonzero predecessor of the bad state
    `CycleStart (rep s3 n) (rep s2 (2*d)) 1` has binary `s2 :: rep s3 (n-1)`
    and ternary `s0 :: s2 :: rep s2 (2*(d-1))` (ternary value 1).
    (Uniqueness direction — backward characterization.)

    This characterization is "one simple cycle decrements tern by 1 and
    increments bin by 1". A full proof requires inverting the disjunction
    inside `cycle_nonzero` (carry_stop vs overflow_carry, each ternary
    digit case). Stated here as a structural claim; proof deferred. -/
theorem cycle_nonzero_pred_bad_state
    (n d : Nat) (_hn : n ≥ 1) (_hd : d ≥ 1) :
    -- Claim: any predecessor (bin_pre, tern_pre, 1) of the bad state via
    -- cycle_nonzero has bin_pre = s2 :: rep s3 (n-1) and
    -- tern_pre = s0 :: s2 :: rep s2 (2*(d-1)).
    ∀ bin_pre tern_pre steps, 0 < steps →
      tmRun (CycleStart bin_pre tern_pre 1) steps =
        CycleStart (rep s3 n) (rep s2 (2 * d)) 1 →
      (∀ s ∈ bin_pre, s = s2 ∨ s = s3) →
      ValidTern tern_pre →
      (∃ x ∈ tern_pre, x ≠ s2) →  -- cycle_nonzero requires non-all-zero ternary input
      bin_pre = s2 :: rep s3 (n - 1) ∧
      tern_pre = s0 :: s2 :: rep s2 (2 * (d - 1)) := by
  sorry

-- ============================================================
-- Section 4: Era-entry constraint (OPEN)
-- ============================================================

/-!
Era-entry constraint: if the bad state at the end of a pad=1 era exists,
the corresponding era-entry state (output of `overflow_cycle`) has
`bin'` such that iterating `cycle_nonzero` (3^d - 1) times produces
`rep s3 n`. Since each cycle_nonzero step `bin → bin + 1 (possibly with wrap)`,
this is a Diophantine condition on `bin'`, `d`, `n`.

Specifically (simplified): `binValue(bin') + 3^d - 1 ≡ 2^n - 1 (mod ???)`
where the modulus depends on the wrap schedule within the era — this is
precisely the 2-adic obstruction from `claude-said.txt`.

Closing the constraint requires one of Paths B, C (see `strategy.md`).
-/

-- ============================================================
-- Section 5: Main backward-tracing theorem (open)
-- ============================================================

/-- **The open problem (E.2)**: the "bad state"
    `CycleStart (rep s3 n) (rep s2 (2*d)) 1` is unreachable from `initConfig`
    for any `n ≥ 1`, `d ≥ 1`.

    Proof sketch (all provable sub-claims reduce to the 2-adic crux):
    1. Suppose for contradiction `run tm initConfig k = bad_state` for some k.
    2. By `cycle_nonzero_pred_bad_state`, trace back 3^d - 1 steps through
       cycle_nonzero to the era entry.
    3. By `overflow_cycle` backward: the era entry came from a pad=0 state
       with tern all-zero and bin such that applying overflow_cycle yields
       the era entry's bin.
    4. By induction, the previous pad=1 era also has the same structure,
       giving an earlier era-entry condition.
    5. Traced all the way back to the initial canonical
       `CycleStart [s3, s2] (rep s2 8) 0`, the chain of era-entry conditions
       must be consistent. Show by *2-adic analysis* (Path C) or
       *computational bootstrap* (Path B) that this chain is infeasible
       for any specific (n, d). -/
theorem all_s3_odd_overflow_unreachable_from_init
    (n d : Nat) (_hn : n ≥ 1) (_hd : d ≥ 1) (k : Nat) :
    run tm initConfig k ≠ CycleStart (rep s3 n) (rep s2 (2 * d)) 1 := by
  sorry

end TM5
