/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import BusyLean.Defs
import BusyLean.RunLemmas

/-!
# BusyLean: Non-halting Infrastructure

Lemmas for proving that a Turing machine does not halt, via progress invariants.

The main theorem `nonhalt_of_progress` says: if every configuration satisfying
a predicate `P` can advance to another `P`-configuration with non-halted state,
then the machine never halts from any `P`-configuration.
-/

namespace BusyLean

variable {n : Nat}

-- ============================================================
-- Halting monotonicity
-- ============================================================

/-- Once halted, the state stays `none` after any number of steps. -/
theorem run_state_none {n : Nat} (tm : TM n) (c : Config n) (m : Nat) (h : c.state = none) :
    (run tm c m).state = none := by
  have hh : c.halted := h
  rw [run_halted tm c hh]; exact h

/-- If the machine is alive at step `k`, it was alive at all earlier steps `m ≤ k`. -/
theorem run_alive_of_later (tm : TM n) (c : Config n) (m k : Nat)
    (hmk : m ≤ k) (hk : (run tm c k).state ≠ none) :
    (run tm c m).state ≠ none :=
  fun hm => hk (by rw [show k = m + (k - m) from by omega, run_add]; exact run_state_none tm _ _ hm)

-- ============================================================
-- Progress invariant → non-halting
-- ============================================================

/-- Any configuration satisfying a progress invariant must be alive.
    (If it were halted, `run` would keep it halted, contradicting progress.) -/
private theorem P_alive (tm : TM n) (P : Config n → Prop)
    (hprog : ∀ c, P c → ∃ k, 0 < k ∧ P (run tm c k) ∧ (run tm c k).state ≠ none)
    (c : Config n) (hc : P c) : c.state ≠ none :=
  let ⟨_, _, _, hk_state⟩ := hprog c hc
  run_alive_of_later tm c 0 _ (Nat.zero_le _) hk_state

/-- **Non-halting by progress invariant.**

If `P` is a predicate on configurations such that every `P`-configuration
can advance at least one step to another `P`-configuration with non-halted state,
then any `P`-configuration never halts.

This is the Lean equivalent of BusyCoq's `progress_nonhalt'`.

Usage: define `P` as the disjunction of all loop states in your abstract model,
prove that each state transitions to another with positive step count, then apply. -/
theorem nonhalt_of_progress (tm : TM n) (P : Config n → Prop)
    (hprog : ∀ c, P c → ∃ k, 0 < k ∧ P (run tm c k) ∧ (run tm c k).state ≠ none)
    (c : Config n) (hc : P c) : ∀ m, (run tm c m).state ≠ none := by
  intro m
  induction m using Nat.strongRecOn generalizing c with
  | _ m ihm =>
    match m with
    | 0 => exact P_alive tm P hprog c hc
    | m' + 1 =>
      obtain ⟨k, hk_pos, hk_P, hk_state⟩ := hprog c hc
      by_cases hge : m' + 1 ≤ k
      · exact run_alive_of_later tm c (m' + 1) k hge hk_state
      · have hlt : k < m' + 1 := Nat.lt_of_not_le hge
        rw [show m' + 1 = k + (m' + 1 - k) from by omega, run_add]
        exact ihm (m' + 1 - k) (by omega) (run tm c k) hk_P

/-- Corollary: a machine starting from `c` does not halt if there is a progress
    invariant `P` with `P c`. -/
theorem not_halts_of_progress (tm : TM n) (P : Config n → Prop)
    (hprog : ∀ c, P c → ∃ k, 0 < k ∧ P (run tm c k) ∧ (run tm c k).state ≠ none)
    (c : Config n) (hc : P c) : ∀ m, ¬ (run tm c m).halted :=
  fun m h => nonhalt_of_progress tm P hprog c hc m h

end BusyLean
