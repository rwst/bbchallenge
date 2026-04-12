/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Inspired by Busybeaver.ClosedSet (https://github.com/mfornet/busybeaver)
Original authors: mfornet et al.
Adapted to BusyLean zipper tape model.
-/
import BusyLean.Defs
import BusyLean.RunLemmas
import BusyLean.Nonhalt
import BusyLean.Multistep

/-!
# BusyLean: Closed Set Non-halting Framework

A closed set proof shows that the TM can always make progress from any
configuration in a set `P`, and that the initial config reaches `P`.
This implies non-halting.

## Usage

```lean
theorem tm_nonhalt : ∀ m, ¬ (run tm (initConfig 6) m).halted := by
  apply ClosedSet.nonHalting (P := fun c => ...)
  · -- closed: every P-config progresses to another P-config
    intro ⟨c, hc⟩
    ...
  · -- enters: init reaches a P-config
    exact ⟨⟨someConfig, proof_it_satisfies_P⟩, ⟨k, proof_of_run⟩⟩
```

Or use the `closed_set` tactic:
```lean
theorem tm_nonhalt : ∀ m, ¬ (run tm (initConfig 6) m).halted := by
  closed_set (fun c => ...)
```
-/

namespace BusyLean

variable {n : Nat} {tm : TM n}

/-- A closed set for TM `tm` with predicate `P` and initial config `I`.
    - `closed`: every config satisfying `P` can progress (1+ steps) to another
      `P`-config that is not halted.
    - `enters`: `I` eventually reaches (0+ steps) a config satisfying `P`. -/
structure ClosedSet (tm : TM n) (P : Config n → Prop) (I : Config n) where
  closed : ∀ (A : { c // P c }), ∃ (B : { c // P c }), A.val -[tm]->+ B.val
  enters : ∃ (B : { c // P c }), I -[tm]->* B.val

/-- A closed set implies non-halting from the initial config. -/
theorem ClosedSet.nonHalting {P : Config n → Prop} {I : Config n}
    (cs : ClosedSet tm P I) : ∀ m : Nat, ¬ (run tm I m).halted := by
  -- Extract the progress invariant from ClosedSet
  have hprog : ∀ c : Config n, P c →
      ∃ k : Nat, 0 < k ∧ P (run tm c k) ∧ (run tm c k).state ≠ none := by
    intro c hc
    obtain ⟨⟨B, hB⟩, k, hk, hrun, hnothalted⟩ := cs.closed ⟨c, hc⟩
    simp [Multistep] at hrun
    exact ⟨k, hk, hrun ▸ hB, hrun ▸ hnothalted⟩
  -- Get the entering config
  obtain ⟨⟨B, hB⟩, k, hIB⟩ := cs.enters
  simp [Multistep] at hIB
  -- Use nonhalt_of_progress on B, then transfer to I
  have hB_nonhalt := not_halts_of_progress tm P hprog B hB
  intro m
  by_cases hle : m < k
  · -- Before reaching B: if halted at m < k, then halted at k too
    intro hm
    have hk_eq : k = m + (k - m) := by omega
    have : (run tm I k).halted := by
      rw [hk_eq, run_add, run_halted tm _ hm]
      exact hm
    rw [hIB] at this
    exact hB_nonhalt 0 this
  · -- After reaching B
    have hle' : k ≤ m := Nat.not_lt.mp hle
    have hm_eq : m = k + (m - k) := by omega
    rw [hm_eq, run_add, hIB]
    exact hB_nonhalt (m - k)

/-- `closed_set P` tactic: replaces a non-halting goal with ClosedSet subgoals. -/
scoped macro "closed_set" P:term : tactic =>
  `(tactic| (
    apply ClosedSet.nonHalting (P := $P)
    constructor))

end BusyLean
