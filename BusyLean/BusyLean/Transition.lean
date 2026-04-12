/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Inspired by Busybeaver.Transition (https://github.com/mfornet/busybeaver)
Original authors: mfornet et al.
Adapted to BusyLean zipper tape model.
-/
import BusyLean.Defs
import BusyLean.RunLemmas

/-!
# BusyLean: Halting Transition Analysis

Lemmas connecting halting to transition table entries. The key result
`halted_of_step` says: if `step tm c` is halted but `c` is not, then
`c.state = some q` and `tm.tr q c.head = none` for some `q`.

This enables proving non-halting by showing all halting transitions
are unreachable.
-/

namespace BusyLean

variable {n : Nat}

/-- If stepping produces a halted config from a non-halted one, then the
    current state/symbol pair maps to `none` in the transition table. -/
theorem halted_of_step (tm : TM n) (c : Config n)
    (hc : ¬ c.halted) (hs : (step tm c).halted) :
    ∃ q : Fin n, c.state = some q ∧ tm.tr q c.head = none := by
  simp [Config.halted] at hc
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hc
  refine ⟨q, hq, ?_⟩
  simp [Config.halted] at hs
  -- hs : (step tm c).state = none, hq : c.state = some q
  -- step with state = some q looks up tm.tr q c.head
  revert hs
  simp [hq]
  cases h : tm.tr q c.head with
  | none => intro; rfl
  | some val =>
    obtain ⟨q', w, d⟩ := val
    cases d <;> simp

/-- A transition is reachable from config `C` if some future config has that
    state and head symbol. -/
def transReachable (tm : TM n) (q : Fin n) (s : Sym) (C : Config n) : Prop :=
  ∃ k : Nat, (run tm C k).state = some q ∧ (run tm C k).head = s

/-- If all halting transitions are unreachable from a non-halted config `C`,
    then the TM never halts from `C`. -/
theorem nonhalt_of_unreachable (tm : TM n) (C : Config n) (hC : ¬ C.halted)
    (h : ∀ q : Fin n, ∀ s : Sym, tm.tr q s = none → ¬ transReachable tm q s C) :
    ∀ m : Nat, ¬ (run tm C m).halted := by
  intro m hm
  induction m with
  | zero => exact hC (by simpa [run] using hm)
  | succ m ih =>
    by_cases hm' : (run tm C m).halted
    · -- Already halted at step m, contradiction with ih
      exact ih hm'
    · -- Not halted at step m, halted at step m+1
      -- run tm C (m+1) = run tm (step tm C) m, but we need step tm (run tm C m)
      have key : run tm C (m + 1) = step tm (run tm C m) := by
        rw [show m + 1 = m + 1 from rfl, run_add]; rfl
      rw [key] at hm
      obtain ⟨q, hq, htr⟩ := halted_of_step tm (run tm C m) hm' hm
      exact h q (run tm C m).head htr ⟨m, hq, rfl⟩

end BusyLean
