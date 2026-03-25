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

end BusyLean
