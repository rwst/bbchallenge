/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Inspired by Busybeaver.Reachability (https://github.com/mfornet/busybeaver)
Original authors: mfornet et al.
Adapted to BusyLean zipper tape model.
-/
import BusyLean.Defs
import BusyLean.RunLemmas

/-!
# BusyLean: Multistep Relations

Relational characterization of TM execution, complementing the functional `run`.
Provides `Multistep` (exactly n steps via `run`), `Progress` (1+ steps to a non-halted
config), and `EvStep` (0+ steps).

Note: BusyLean's `step` is total (identity on halted configs), so `Multistep` via `run`
does not imply the config was alive. The `Progress` relation adds `¬ B.halted` to ensure
genuine forward motion, which is what `ClosedSet` needs.
-/

namespace BusyLean

variable {n : Nat} {tm : TM n}
variable {A B C : Config n}
variable {j k m : Nat}

/-! ### Multistep: exactly k steps via `run` -/

/-- `Multistep tm k A B` means `run tm A k = B`. -/
def Multistep (tm : TM n) (k : Nat) (A B : Config n) : Prop :=
  run tm A k = B

scoped notation:50 A " -[" tm "]{" k "}-> " B => Multistep tm k A B

instance Multistep.instDecidable (tm : TM n) (k : Nat) (A B : Config n) :
    Decidable (A -[tm]{k}-> B) :=
  inferInstanceAs (Decidable (run tm A k = B))

@[refl]
theorem Multistep.refl : A -[tm]{0}-> A := rfl

theorem Multistep.single (h : step tm A = B) : A -[tm]{1}-> B := by
  simp [Multistep, run]; exact h

theorem Multistep.trans (h1 : A -[tm]{j}-> B) (h2 : B -[tm]{k}-> C) :
    A -[tm]{j + k}-> C := by
  simp [Multistep] at *; rw [run_add, h1, h2]

theorem Multistep.split (h : A -[tm]{j + k}-> C) :
    ∃ B, (A -[tm]{j}-> B) ∧ (B -[tm]{k}-> C) :=
  ⟨run tm A j, rfl, by simp [Multistep] at *; rw [run_add] at h; exact h⟩

theorem Multistep.deterministic (h1 : A -[tm]{k}-> B) (h2 : A -[tm]{k}-> C) :
    B = C := by
  simp [Multistep] at *; rw [← h1, ← h2]

theorem Multistep.to_run (h : A -[tm]{k}-> B) : run tm A k = B := h

theorem Multistep.from_run (h : run tm A k = B) : A -[tm]{k}-> B := h

/-- If A reaches B in j steps and C in j+k steps, then B reaches C in k steps. -/
theorem Multistep.split_add (h1 : A -[tm]{j}-> B) (h2 : A -[tm]{j + k}-> C) :
    B -[tm]{k}-> C := by
  obtain ⟨B', hB', hBC⟩ := h2.split
  have : B = B' := h1.deterministic hB'
  subst this; exact hBC

/-! ### Progress: one or more steps to a non-halted config -/

/-- `Progress tm A B` means A reaches B in 1+ steps and B is not halted. -/
def Progress (tm : TM n) (A B : Config n) : Prop :=
  ∃ k : Nat, 0 < k ∧ Multistep tm k A B ∧ ¬ B.halted

scoped notation:50 A " -[" tm "]->+ " B => Progress tm A B

theorem Progress.mk (hk : 0 < k) (h : A -[tm]{k}-> B) (hB : ¬ B.halted) :
    A -[tm]->+ B :=
  ⟨k, hk, h, hB⟩

/-! ### EvStep: zero or more steps -/

/-- `EvStep tm A B` means A reaches B in 0 or more steps. -/
def EvStep (tm : TM n) (A B : Config n) : Prop :=
  ∃ k : Nat, Multistep tm k A B

scoped notation:50 A " -[" tm "]->* " B => EvStep tm A B

@[refl]
theorem EvStep.refl : A -[tm]->* A := ⟨0, rfl⟩

theorem EvStep.from_multistep (h : A -[tm]{k}-> B) : A -[tm]->* B := ⟨k, h⟩

theorem EvStep.trans (h1 : A -[tm]->* B) (h2 : B -[tm]->* C) : A -[tm]->* C := by
  obtain ⟨j, hAB⟩ := h1
  obtain ⟨k, hBC⟩ := h2
  exact ⟨j + k, hAB.trans hBC⟩

end BusyLean
