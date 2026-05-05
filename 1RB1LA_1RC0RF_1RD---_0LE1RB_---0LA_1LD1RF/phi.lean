/-
Tape-mass invariant `Φ := sum(L) + sum(R) + c` on `MacroConfig`.

Per the plan in `LOG.md` (2026-05-05), Φ is per-rule monotone non-decreasing
across every macro rule (sweeps and Shift conserve it; M0-cursor rules pump
it +2; EraDone pumps it +4).

The cursor `c` is treated as 0 for the M0 (transient zero-cursor) variant,
matching the rule-level deltas computed analytically.

Layout:
  • Stage 1: `MacroConfig.phi` definition + `phi_M` / `phi_M0` simp lemmas.
  • Stage 2: 18 per-rule Φ-delta lemmas mirroring `macro.txt`. Each states
    the input/output Φ-relation as an explicit arithmetic identity. These
    are mechanical (`simp; omega`) consequences of the elementary
    transformation each rule implements; they do not require the rule's
    raw-step proof.
-/

import machine

namespace Sweeper

open BusyLean

-- ============================================================
-- Stage 1: definition + simp lemmas
-- ============================================================

/-- Tape-mass invariant on `MacroConfig`. The M0 case has no explicit
    cursor, so we treat its cursor as 0. -/
def MacroConfig.phi : MacroConfig → Nat
  | .M  L c R => L.sum + R.sum + c
  | .M0 L R   => L.sum + R.sum

@[simp] lemma MacroConfig.phi_M (L : List Nat) (c : Nat) (R : List Nat) :
    (MacroConfig.M L c R).phi = L.sum + R.sum + c := rfl

@[simp] lemma MacroConfig.phi_M0 (L R : List Nat) :
    (MacroConfig.M0 L R).phi = L.sum + R.sum := rfl

-- ============================================================
-- Stage 2: per-rule Φ-delta lemmas (18 elementary rules)
-- ============================================================
-- Each lemma states `(out).phi = (in).phi + Δ` for one macro rule,
-- where Δ ∈ {0, 2, 4} per the analysis in LOG.md.

-- Sweep family (4 rules) — ΔΦ = 0

/-- `Sweep`: M(a∷L, c+3, d∷R) → M((a+1)∷L, c+1, (d+1)∷R). -/
lemma phi_macro_sweep (a c d : Nat) (L R : List Nat) :
    (MacroConfig.M ((a + 1) :: L) (c + 1) ((d + 1) :: R)).phi =
    (MacroConfig.M (a :: L) (c + 3) (d :: R)).phi := by
  simp only [MacroConfig.phi_M, List.sum_cons]; omega

/-- `SweepL`: M([], c+3, d∷R) → M([1], c+1, (d+1)∷R). -/
lemma phi_macro_sweep_left_empty (c d : Nat) (R : List Nat) :
    (MacroConfig.M [1] (c + 1) ((d + 1) :: R)).phi =
    (MacroConfig.M [] (c + 3) (d :: R)).phi := by
  simp only [MacroConfig.phi_M, List.sum_cons, List.sum_nil]; omega

/-- `SweepR`: M(a∷L, c+3, []) → M((a+1)∷L, c+1, [1]). -/
lemma phi_macro_sweep_right_empty (a c : Nat) (L : List Nat) :
    (MacroConfig.M ((a + 1) :: L) (c + 1) [1]).phi =
    (MacroConfig.M (a :: L) (c + 3) []).phi := by
  simp only [MacroConfig.phi_M, List.sum_cons, List.sum_nil]; omega

/-- `SweepS`: M([], c+3, []) → M([1], c+1, [1]). -/
lemma phi_macro_sweep_solo (c : Nat) :
    (MacroConfig.M [1] (c + 1) [1]).phi =
    (MacroConfig.M [] (c + 3) []).phi := by
  simp only [MacroConfig.phi_M, List.sum_singleton, List.sum_nil]; omega

-- SweepE family (4 rules) — ΔΦ = 0 (terminal: M with c=2 → M0 with c=0)

/-- `SweepE`: M(a∷L, 2, d∷R) → M0((a+1)∷L, (d+1)∷R). -/
lemma phi_macro_sweep_to_zero (a d : Nat) (L R : List Nat) :
    (MacroConfig.M0 ((a + 1) :: L) ((d + 1) :: R)).phi =
    (MacroConfig.M (a :: L) 2 (d :: R)).phi := by
  simp only [MacroConfig.phi_M, MacroConfig.phi_M0, List.sum_cons]; omega

/-- `SweepLE`: M([], 2, d∷R) → M0([1], (d+1)∷R). -/
lemma phi_macro_sweep_to_zero_left_empty (d : Nat) (R : List Nat) :
    (MacroConfig.M0 [1] ((d + 1) :: R)).phi =
    (MacroConfig.M [] 2 (d :: R)).phi := by
  simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
             List.sum_cons, List.sum_nil]; omega

/-- `SweepRE`: M(a∷L, 2, []) → M0((a+1)∷L, [1]). -/
lemma phi_macro_sweep_to_zero_right_empty (a : Nat) (L : List Nat) :
    (MacroConfig.M0 ((a + 1) :: L) [1]).phi =
    (MacroConfig.M (a :: L) 2 []).phi := by
  simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
             List.sum_cons, List.sum_nil]; omega

/-- `SweepSE`: M([], 2, []) → M0([1], [1]). -/
lemma phi_macro_sweep_solo_to_zero :
    (MacroConfig.M0 [1] [1]).phi =
    (MacroConfig.M [] 2 []).phi := by
  simp only [MacroConfig.phi_M, MacroConfig.phi_M0, List.sum_cons, List.sum_nil]; omega

-- Shift — ΔΦ = 0

/-- `Shift`: M((a+1)∷L, 1, d∷R) → M(L, a+1, 1∷d∷R). -/
lemma phi_macro_shift (a d : Nat) (L R : List Nat) :
    (MacroConfig.M L (a + 1) (1 :: d :: R)).phi =
    (MacroConfig.M ((a + 1) :: L) 1 (d :: R)).phi := by
  simp only [MacroConfig.phi_M, List.sum_cons]; omega

-- EraDone — ΔΦ = +4

/-- `EraDone`: M0((a+1)∷L, [1]) → M(L, a+6, []). -/
lemma phi_macro_era_complete (a : Nat) (L : List Nat) :
    (MacroConfig.M L (a + 6) []).phi =
    (MacroConfig.M0 ((a + 1) :: L) [1]).phi + 4 := by
  simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
             List.sum_cons, List.sum_nil]; omega

-- Bounce family — ΔΦ = +2

/-- `Bounce`: M0(a∷L, [z+4]) → M((a+4)∷L, z+1, [1]). -/
lemma phi_macro_zero_bounce (a z : Nat) (L : List Nat) :
    (MacroConfig.M ((a + 4) :: L) (z + 1) [1]).phi =
    (MacroConfig.M0 (a :: L) [z + 4]).phi + 2 := by
  simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
             List.sum_cons, List.sum_nil]; omega

/-- `BounceE`: M0(a∷L, [3]) → M0((a+4)∷L, [1]). -/
lemma phi_macro_zero_bounce_to_zero (a : Nat) (L : List Nat) :
    (MacroConfig.M0 ((a + 4) :: L) [1]).phi =
    (MacroConfig.M0 (a :: L) [3]).phi + 2 := by
  simp only [MacroConfig.phi_M0, List.sum_cons, List.sum_nil]; omega

-- Two family — ΔΦ = +2

/-- `Two`: M0(a∷L, 2∷d∷R) → M(L, a+3, (d+1)∷R). -/
lemma phi_macro_zero_two (a d : Nat) (L R : List Nat) :
    (MacroConfig.M L (a + 3) ((d + 1) :: R)).phi =
    (MacroConfig.M0 (a :: L) (2 :: d :: R)).phi + 2 := by
  simp only [MacroConfig.phi_M, MacroConfig.phi_M0, List.sum_cons]; omega

/-- `TwoS`: M0(a∷L, [2]) → M(L, a+3, [1]). -/
lemma phi_macro_zero_two_solo (a : Nat) (L : List Nat) :
    (MacroConfig.M L (a + 3) [1]).phi =
    (MacroConfig.M0 (a :: L) [2]).phi + 2 := by
  simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
             List.sum_cons, List.sum_nil]; omega

-- Multi2 family — ΔΦ = +2

/-- `Multi2`: M0(a∷L, [r+3, rₙ+2]) → M((r+1)∷(a+4)∷L, rₙ+1, [1]). -/
lemma phi_macro_multi_bounce_2 (a r rₙ : Nat) (L : List Nat) :
    (MacroConfig.M ((r + 1) :: (a + 4) :: L) (rₙ + 1) [1]).phi =
    (MacroConfig.M0 (a :: L) [r + 3, rₙ + 2]).phi + 2 := by
  simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
             List.sum_cons, List.sum_nil]; omega

/-- `Multi2E`: M0(a∷L, [r+3, 1]) → M0((r+1)∷(a+4)∷L, [1]). -/
lemma phi_macro_multi_bounce_2_to_zero (a r : Nat) (L : List Nat) :
    (MacroConfig.M0 ((r + 1) :: (a + 4) :: L) [1]).phi =
    (MacroConfig.M0 (a :: L) [r + 3, 1]).phi + 2 := by
  simp only [MacroConfig.phi_M0, List.sum_cons, List.sum_nil]; omega

-- MultiN family — ΔΦ = +2

/-- `MultiN`: M0(a∷L, (r+3)∷R_mid++[rₙ+2])
    → M(R_mid.reverse ++ (r+1)∷(a+4)∷L, rₙ+1, [1]). -/
lemma phi_macro_multi_bounce_general (a r rₙ : Nat) (L R_mid : List Nat) :
    (MacroConfig.M (R_mid.reverse ++ (r + 1) :: (a + 4) :: L) (rₙ + 1) [1]).phi =
    (MacroConfig.M0 (a :: L) ((r + 3) :: R_mid ++ [rₙ + 2])).phi + 2 := by
  simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
             List.sum_append, List.sum_cons, List.sum_nil,
             List.sum_reverse]
  omega

/-- `MultiNE`: M0(a∷L, (r+3)∷R_mid++[1])
    → M0(R_mid.reverse ++ (r+1)∷(a+4)∷L, [1]). -/
lemma phi_macro_multi_bounce_general_to_zero (a r : Nat) (L R_mid : List Nat) :
    (MacroConfig.M0 (R_mid.reverse ++ (r + 1) :: (a + 4) :: L) [1]).phi =
    (MacroConfig.M0 (a :: L) ((r + 3) :: R_mid ++ [1])).phi + 2 := by
  simp only [MacroConfig.phi_M0,
             List.sum_append, List.sum_cons, List.sum_nil,
             List.sum_reverse]
  omega

end Sweeper
