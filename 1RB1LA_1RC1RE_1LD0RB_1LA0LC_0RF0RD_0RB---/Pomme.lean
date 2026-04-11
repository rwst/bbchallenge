import Ellison
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Pomme's proof that `2·3^i + i + 5` has a large odd part

This file follows Pomme (Nov 28, 2025), `previous-work/Pomme2.pdf`, but
replaces the original Baker 1966-68 approach with the sharper
**Baker–Wüstholz (1993)** route defined in `Ellison.lean`. The main
consequence is that the threshold drops from `i ≥ 2^{2100}` to
`i ≥ 2^{60}`, making a verified small-`i` simulator feasible.

The target is the number-theoretic closure inequality needed to prove
non-halting of the Turing machine
`1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---` (a BB(6) holdout), as
identified by mxdys:
```
∀ i ≥ 50,    (2·3^i + i + 5) / 2^{v₂(2·3^i + i + 5)}  ≥  2·i + 14.    (*)
```

## Structure of the proof

1. The sequence `N i := 2·3^i + i + 5`. The easy case is `i` even
   (where `N i` is odd, so `v₂ = 0` and `(*)` is trivial).

2. `pomme_thm1`: for `i ≥ pommeThreshold`, `2^k ∤ N i` whenever
   `3^i/(2·i) ≤ 2^k`. This uses `direct_pillai_bound_small` (from
   `Ellison.lean`) for the hard case `c ≤ 4·i`, and the elementary
   `pomme_case_c_large` for the easy case `c > 4·i`.

3. `pomme_cor3`: for `i ≥ pommeThreshold`, the odd part of `N i`
   exceeds `2·i + 14`.

4. `pomme_small_range` (axiom): discharges `50 ≤ i < pommeThreshold`
   via a verified dense simulator (to be formalized).

5. `pomme_main`: combines (3) and (4).
-/

namespace Pomme

open Real

/-! ## The sequence `N i := 2·3^i + i + 5` -/

/-- Pomme's sequence `N i := 2·3^i + i + 5`. -/
def N (i : ℕ) : ℕ := 2 * 3 ^ i + i + 5

@[simp] lemma N_def (i : ℕ) : N i = 2 * 3 ^ i + i + 5 := rfl

lemma N_pos (i : ℕ) : 0 < N i := by
  unfold N; positivity

/-- Parity of `N`: `N i` is odd exactly when `i` is even. -/
lemma N_odd_iff_even (i : ℕ) : Odd (N i) ↔ Even i := by
  simp only [N, Nat.odd_iff, Nat.even_iff]
  have h : 2 * 3 ^ i % 2 = 0 := Nat.mul_mod_right 2 _
  omega

/-- The easy half of `(*)` (even-`i` case): `v₂(N i) = 0` and
`N i ≥ 2·i + 14` trivially. -/
lemma pomme_even_case
    (i : ℕ) (hi_even : Even i) (hi_ge : 2 ≤ i) :
    padicValNat 2 (N i) = 0 ∧ 2 * i + 14 ≤ N i := by
  refine ⟨?_, ?_⟩
  · rw [padicValNat.eq_zero_iff]
    refine Or.inr (Or.inr ?_)
    rintro ⟨m, hm⟩
    have hOdd : Odd (N i) := (N_odd_iff_even i).mpr hi_even
    rw [Nat.odd_iff] at hOdd
    omega
  · have h : i + 9 ≤ 2 * 3 ^ i := by
      clear hi_even
      induction i, hi_ge using Nat.le_induction with
      | base => decide
      | succ k _ ih =>
        have hpos : 1 ≤ 3 ^ k := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
        calc k + 1 + 9 = k + 9 + 1 := by ring
          _ ≤ 2 * 3 ^ k + 1 := by omega
          _ ≤ 2 * 3 ^ (k + 1) := by
              rw [pow_succ]
              nlinarith
    unfold N
    omega


/-! ## Pomme's Theorem 1

The threshold `pommeThreshold := 2^60` is defined at top level in
`Ellison.lean`. -/

/-- Reformulation: `2^k` does not divide `N i` follows from the condition
that for every positive integer `c`, the gap `|2·3^i − c·2^k|` exceeds
`i + 5`. -/
lemma pomme_not_dvd_of_gap
    (i k : ℕ)
    (h : ∀ c : ℕ, 0 < c → ((i : ℝ) + 5) < |((2 * 3 ^ i : ℤ) - (c : ℤ) * 2 ^ k)|) :
    ¬ (2 ^ k ∣ N i) := by
  rintro ⟨c, hc⟩
  have hc_pos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with rfl | hp
    · rw [mul_zero] at hc
      exact absurd hc (N_pos i).ne'
    · exact hp
  specialize h c hc_pos
  have hN_int : (2 * (3 : ℤ) ^ i + (i : ℤ) + 5) = (c : ℤ) * 2 ^ k := by
    have h1 : (N i : ℤ) = ((2 ^ k * c : ℕ) : ℤ) := by exact_mod_cast hc
    unfold N at h1
    push_cast at h1
    linarith
  have h_diff : (2 * (3 : ℤ) ^ i - (c : ℤ) * 2 ^ k) = -((i : ℤ) + 5) := by linarith
  have h_abs_eq : |((2 * 3 ^ i : ℤ) - (c : ℤ) * 2 ^ k)| = (i : ℤ) + 5 := by
    rw [h_diff, abs_neg, abs_of_nonneg]; positivity
  rw [show ((|((2 * 3 ^ i : ℤ) - (c : ℤ) * 2 ^ k)| : ℤ) : ℝ) = ((i : ℝ) + 5) by
        rw [h_abs_eq]; push_cast; rfl] at h
  exact lt_irrefl _ h

/-- **Case 1 (c large).** If `c > 4·i` and `2^k ≥ 3^i / (2·i) > i + 5`, then
`|2·3^i − c·2^k| = c·2^k − 2·3^i ≥ 2^k > i + 5`. -/
lemma pomme_case_c_large
    (i k c : ℕ) (hi_pos : 0 < i)
    (hk : ((3 : ℝ) ^ i) / (2 * i) ≤ (2 : ℝ) ^ k)
    (hi_large : ((i : ℝ) + 5) < ((3 : ℝ) ^ i) / (2 * i))
    (hc_big : 4 * i < c) :
    ((i : ℝ) + 5) < |((2 * 3 ^ i : ℤ) - (c : ℤ) * 2 ^ k)| := by
  have hi_ne : (i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hi_pos.ne'
  have h2k_lb : ((i : ℝ) + 5) < (2 : ℝ) ^ k := hi_large.trans_le hk
  have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have h4i : 2 * (3 : ℝ) ^ i ≤ (4 * (i : ℝ)) * (2 : ℝ) ^ k := by
    have heq : (4 * (i : ℝ)) * ((3 : ℝ) ^ i / (2 * (i : ℝ))) = 2 * (3 : ℝ) ^ i := by
      field_simp; ring
    have h1 : (4 * (i : ℝ)) * ((3 : ℝ) ^ i / (2 * (i : ℝ))) ≤ (4 * (i : ℝ)) * (2 : ℝ) ^ k := by
      have h4i_nn : (0 : ℝ) ≤ 4 * (i : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left hk h4i_nn
    linarith
  have hc_ge : ((4 * (i : ℝ)) + 1) ≤ (c : ℝ) := by
    have : (4 * i + 1 : ℕ) ≤ c := hc_big
    have := (Nat.cast_le (α := ℝ)).mpr this
    push_cast at this
    linarith
  have h_big : 2 * (3 : ℝ) ^ i + ((i : ℝ) + 5) < (c : ℝ) * (2 : ℝ) ^ k := by
    have hstep : ((4 * (i : ℝ)) + 1) * (2 : ℝ) ^ k ≤ (c : ℝ) * (2 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right hc_ge (le_of_lt h2k_pos)
    nlinarith [hstep, h4i, h2k_lb]
  have h_sign : ((2 * 3 ^ i : ℤ) - (c : ℤ) * 2 ^ k) ≤ 0 := by
    have h_lt_R : (2 : ℝ) * (3 : ℝ) ^ i < (c : ℝ) * (2 : ℝ) ^ k := by linarith
    have h_lt_Z : (2 * (3 : ℤ) ^ i : ℤ) < ((c : ℤ) * 2 ^ k : ℤ) := by
      have := h_lt_R
      exact_mod_cast this
    linarith
  rw [abs_of_nonpos h_sign]
  have h_eq_R : (((-(((2 * 3 ^ i : ℤ)) - (c : ℤ) * 2 ^ k) : ℤ)) : ℝ)
              = (c : ℝ) * (2 : ℝ) ^ k - 2 * (3 : ℝ) ^ i := by
    push_cast; ring
  rw [h_eq_R]
  linarith

/-- Helper: `2·i² + 10·i < 3^i` for all `i ≥ 8`. By induction. -/
lemma two_i_sq_plus_ten_i_lt_three_pow (i : ℕ) (hi : 8 ≤ i) :
    2 * i ^ 2 + 10 * i < 3 ^ i := by
  induction i, hi using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have h3 : 3 ^ (k + 1) = 3 * 3 ^ k := by rw [pow_succ]; ring
    have hksq : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
    rw [h3, hksq]
    nlinarith [ih, hk, sq_nonneg k]

/-- Elementary lemma used by `pomme_thm1`: for `i ≥ pommeThreshold`, we have
`i + 5 < 3^i / (2·i)`. -/
lemma pomme_ip5_lt_ratio
    (i : ℕ) (hi : pommeThreshold ≤ i) :
    ((i : ℝ) + 5) < ((3 : ℝ) ^ i) / (2 * i) := by
  have hi8 : 8 ≤ i := le_trans pommeThreshold_ge_eight hi
  have hi_pos : 0 < i := by omega
  have hi_R_pos : (0 : ℝ) < (i : ℝ) := Nat.cast_pos.mpr hi_pos
  have h2i_pos : (0 : ℝ) < 2 * (i : ℝ) := by linarith
  have h_nat := two_i_sq_plus_ten_i_lt_three_pow i hi8
  have h_R : (2 * (i : ℝ) ^ 2 + 10 * (i : ℝ)) < ((3 : ℝ) ^ i) := by
    have := h_nat
    have : ((2 * i ^ 2 + 10 * i : ℕ) : ℝ) < ((3 ^ i : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this
    linarith
  rw [lt_div_iff₀ h2i_pos]
  have heq : ((i : ℝ) + 5) * (2 * (i : ℝ)) = 2 * (i : ℝ) ^ 2 + 10 * (i : ℝ) := by ring
  linarith [h_R, heq]

/-- **Pomme's Theorem 1** (refined via Baker–Wüstholz). For `i ≥ pommeThreshold`
and any `k` with `3^i / (2·i) ≤ 2^k`, `2^k` does not divide `N i`. -/
theorem pomme_thm1
    (i k : ℕ) (hi : pommeThreshold ≤ i)
    (hk : ((3 : ℝ) ^ i) / (2 * i) ≤ (2 : ℝ) ^ k) :
    ¬ (2 ^ k ∣ N i) := by
  have hi_pos : 0 < i := lt_of_lt_of_le pommeThreshold_pos hi
  have hi_large : ((i : ℝ) + 5) < ((3 : ℝ) ^ i) / (2 * i) := pomme_ip5_lt_ratio i hi
  apply pomme_not_dvd_of_gap
  intro c hc_pos
  by_cases h : c ≤ 4 * i
  · exact direct_pillai_bound_small i k c hi hc_pos h hk
  · push_neg at h
    exact pomme_case_c_large i k c hi_pos hk hi_large h

/-! ## Pomme's Corollary 3 and the final inequality -/

/-- **Pomme's Corollary 3**. For `i ≥ pommeThreshold`, the odd part of
`N i` exceeds `2·i + 14`. -/
theorem pomme_cor3
    (i : ℕ) (hi : pommeThreshold ≤ i) :
    2 * i + 14 ≤ N i / 2 ^ padicValNat 2 (N i) := by
  have hi_pos : 0 < i := lt_of_lt_of_le pommeThreshold_pos hi
  have hi7 : 7 ≤ i := by
    have h1 : (7 : ℕ) ≤ 8 := by decide
    exact le_trans (le_trans h1 pommeThreshold_ge_eight) hi
  set v := padicValNat 2 (N i) with hv_def
  have h_dvd : 2 ^ v ∣ N i := pow_padicValNat_dvd
  have h2v_pos : 0 < (2 : ℕ) ^ v := pow_pos (by norm_num) v
  have h_lt : ((2 : ℝ) ^ v) < ((3 : ℝ) ^ i) / (2 * i) := by
    by_contra h_ge
    push_neg at h_ge
    exact pomme_thm1 i v hi h_ge h_dvd
  have hi_R_pos : (0 : ℝ) < (i : ℝ) := Nat.cast_pos.mpr hi_pos
  have h2i_pos : (0 : ℝ) < 2 * (i : ℝ) := by linarith
  have h1 : (2 : ℝ) ^ v * (2 * (i : ℝ)) < (3 : ℝ) ^ i := by
    rw [lt_div_iff₀ h2i_pos] at h_lt
    linarith
  have h2 : (4 * (i : ℝ)) * (2 : ℝ) ^ v < 2 * (3 : ℝ) ^ i := by nlinarith [h1]
  have hi7_R : (7 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi7
  have h3 : ((2 * (i : ℝ)) + 14) * (2 : ℝ) ^ v ≤ (4 * (i : ℝ)) * (2 : ℝ) ^ v := by
    have h2v_nn : (0 : ℝ) ≤ (2 : ℝ) ^ v := by positivity
    nlinarith [h2v_nn, hi7_R]
  have hN_lb : 2 * (3 : ℝ) ^ i ≤ (N i : ℝ) := by
    unfold N; push_cast; linarith [hi_R_pos]
  have h_final_N : (2 * i + 14) * 2 ^ v ≤ N i := by
    have key : (2 * (i : ℝ) + 14) * (2 : ℝ) ^ v ≤ (N i : ℝ) := by
      linarith [h3, h2, hN_lb]
    have cast_eq : (((2 * i + 14) * 2 ^ v : ℕ) : ℝ) = (2 * (i : ℝ) + 14) * (2 : ℝ) ^ v := by
      push_cast; ring
    have : (((2 * i + 14) * 2 ^ v : ℕ) : ℝ) ≤ ((N i : ℕ) : ℝ) := by
      rw [cast_eq]; exact key
    exact_mod_cast this
  exact (Nat.le_div_iff_mul_le h2v_pos).mpr h_final_N

/-! ### Small-`i` range

The direct Baker–Wüstholz bound covers `i ≥ pommeThreshold = 2^60`. The
range `50 ≤ i < 2^60 ≈ 1.15·10^{18}` has to be handled by a dense
simulator. (Down from `50 ≤ i < 2^{2100}` in the old approach —
computationally feasible in CPU-hours with GMP.) -/

/-- Dense simulator verification for the small-`i` range `50 ≤ i < 2^{60}`.
To be discharged later by a verified computation. -/
axiom pomme_small_range
    (i : ℕ) (hi_lo : 50 ≤ i) (hi_hi : i < pommeThreshold) :
    2 * i + 14 ≤ N i / 2 ^ padicValNat 2 (N i)

/-- **Main theorem**: the TM-closure inequality `(*)` for all `i ≥ 50`. -/
theorem pomme_main (i : ℕ) (hi : 50 ≤ i) :
    2 * i + 14 ≤ N i / 2 ^ padicValNat 2 (N i) := by
  by_cases h : i < pommeThreshold
  · exact pomme_small_range i hi h
  · push_neg at h
    exact pomme_cor3 i h

end Pomme
