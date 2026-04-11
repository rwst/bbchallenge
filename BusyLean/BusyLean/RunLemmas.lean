/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import BusyLean.Defs

/-!
# BusyLean: Execution Lemmas

Key lemmas about `step` and `run` that are used in every BB proof.
-/

namespace BusyLean

variable {n : Nat} (tm : TM n)

/-- Running 0 steps is the identity. -/
@[simp]
theorem run_zero (c : Config n) : run tm c 0 = c := rfl

/-- Running k+1 steps = step then run k. -/
theorem run_succ (c : Config n) (k : Nat) :
    run tm c (k + 1) = run tm (step tm c) k := rfl

/-- Compositionality: running a+b steps = run a then run b. -/
theorem run_add (c : Config n) (a b : Nat) :
    run tm c (a + b) = run tm (run tm c a) b := by
  induction a generalizing c with
  | zero => simp [run]
  | succ a ih =>
    -- Goal: run tm c (a + 1 + b) = run tm (run tm c (a + 1)) b
    -- a + 1 + b = (a + b) + 1 and run tm c (k+1) = run tm (step tm c) k
    have h1 : a + 1 + b = (a + b) + 1 := by omega
    have h2 : run tm c (a + 1 + b) = run tm (step tm c) (a + b) := by
      rw [h1]; rfl
    have h3 : run tm c (a + 1) = run tm (step tm c) a := rfl
    rw [h2, h3]
    exact ih (step tm c)

/-- Stepping a halted configuration is identity. -/
@[simp]
theorem step_halted (c : Config n) (h : c.halted) :
    step tm c = c := by
  simp [step, Config.halted] at *
  simp [h]

/-- Running a halted configuration any number of steps is identity. -/
theorem run_halted (c : Config n) (h : c.halted) (k : Nat) :
    run tm c k = c := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    rw [run_succ, step_halted tm c h]
    exact ih c h

/-- Running 1 step is just `step`. -/
@[simp]
theorem run_one (c : Config n) : run tm c 1 = step tm c := rfl

-- ============================================================
-- Right-tape locality: appending cells past a non-empty right
-- commutes with `step` and `run`.
-- ============================================================

/-- **Step locality.** If the right strip is non-empty, extending it
with an arbitrary tail `T` commutes with a single TM step. This lets
us lift concrete-prefix proofs to "any tail" proofs. -/
theorem step_right_append (c : Config n) (T : List Sym) (h : c.right ≠ []) :
    step tm { c with right := c.right ++ T } =
    { step tm c with right := (step tm c).right ++ T } := by
  obtain ⟨st, L, hd, R⟩ := c
  obtain ⟨r, rs, rfl⟩ : ∃ r rs, R = r :: rs := by
    cases R with
    | nil => exact absurd rfl h
    | cons r rs => exact ⟨r, rs, rfl⟩
  -- Goal: step tm {state:=st, left:=L, head:=hd, right:=(r::rs) ++ T} = …
  -- Case analysis on state and transition table.
  rcases hst : st with _ | q
  · rfl
  rcases htr : tm.tr q hd with _ | ⟨q', w, d⟩
  · simp only [step, hst, htr, List.cons_append]
  rcases d
  · -- Dir.L
    simp only [step, hst, htr, List.cons_append]
  · -- Dir.R
    simp only [step, hst, htr, List.cons_append, listTail, listHead]

/-- **Run locality.** If the right strip stays non-empty for the first
`k` steps, extending it with `T` commutes with `run tm · k`. -/
theorem run_right_append (c : Config n) (T : List Sym) (k : Nat)
    (h : ∀ m, m < k → (run tm c m).right ≠ []) :
    run tm { c with right := c.right ++ T } k =
    { run tm c k with right := (run tm c k).right ++ T } := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    -- Peel one step:  run tm c' (k+1) = run tm (step tm c') k
    rw [run_succ]
    -- LHS after step: step tm {c with right := c.right ++ T}
    have h0 : c.right ≠ [] := h 0 (Nat.zero_lt_succ k)
    rw [step_right_append tm c T h0]
    -- Now apply IH with config := step tm c
    have h' : ∀ m, m < k → (run tm (step tm c) m).right ≠ [] := by
      intro m hm
      have : (run tm c (m + 1)).right ≠ [] := h (m + 1) (by omega)
      rw [run_succ] at this
      exact this
    rw [ih (step tm c) h']
    -- Simplify: run tm (step tm c) k = run tm c (k+1)
    rw [← run_succ]

end BusyLean
