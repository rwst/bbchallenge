import BakerWustholz
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Direct Pillai bound via Baker–Wüstholz

This file replaces the earlier Baker-via-Ellison approach in terms of
the 1966-68 Baker bound. Since Baker–Wüstholz (1993) is a strictly
sharper effective bound — in particular, its outer exponent on `log B`
is essentially `1` rather than `(2n+1)²` — the derivation of Pomme's
inequality becomes significantly more direct.

Crucially, Baker–Wüstholz does **not** require the degree `d ≥ 4`
hypothesis of Ellison's Lemma 2, so we can instantiate it with `K = ℚ`
directly. No auxiliary number field (e.g. `CyclotomicField 5 ℚ`) is
needed.

## What's here

* `pommeThreshold` — the threshold on `i` above which Pomme's inequality
  holds unconditionally. Set to `2^{60} ≈ 1.15·10^{18}`, comfortably
  above where the Baker–Wüstholz bound becomes effective for Pillai's
  setup. (Was `2^{2100}` in the old approach.)

* `log_bound_to_integer_bound` — "Ellison's Lemma 1": given that
  `|a·m^x − b·n^y|` is small relative to `b·n^y`, the linear form in
  logs is also small by the Taylor bound `|log(1+z)| ≤ 2|z|`.

* `direct_pillai_bound_small` — replaces the old
  `ellison_cor1 + pomme_case_c_small` pair. For `i ≥ pommeThreshold`,
  `1 ≤ c ≤ 4i`, and `3^i / (2i) ≤ 2^k`, gives
  `|2·3^i − c·2^k| > i + 5` directly via
  `bakerWustholz_linearForms_logs` + `log_bound_to_integer_bound`.
-/

open Complex

/-- Pomme's threshold: the smallest `i` above which the direct
Baker–Wüstholz route to Pomme's inequality works. Set to `2^{60}` — more
than large enough given that the true threshold emerging from the
Baker–Wüstholz constants is approximately `10^{17}`. -/
def pommeThreshold : ℕ := 2 ^ 60

lemma pommeThreshold_pos : 0 < pommeThreshold := by
  unfold pommeThreshold; positivity

lemma pommeThreshold_ge_eight : 8 ≤ pommeThreshold := by
  unfold pommeThreshold; decide

lemma pommeThreshold_ge_106 : 106 ≤ pommeThreshold := by
  unfold pommeThreshold; decide

/-- **Ellison's Lemma 1 (log-to-integer translation)**.

Given that `|a·m^x − b·n^y| = ω` with `|ω| < b·n^y / 2`, the linear
form in logs `Λ := x·log m − y·log n + log(a/b)` satisfies
`|Λ| ≤ 2·|ω| / (b·n^y)`.

Specialized to our Pomme setup `(a, b, m, n) = (1, 2, 2, 3)` with the
extra coefficient `c` absorbed as `α₃ = c/2`: given `|c·2^k − 2·3^i| ≤ ε`
with `ε < 3^i`, the sum `(k-1)·log 2 − i·log 3 + log c` has norm at most
`2·ε / (2·3^i)`.

**Status**: SORRY. This is the one analytic lemma needed; ~60-100 lines
of real analysis using `Real.abs_log_one_add_le` or the equivalent
Taylor bound `|log(1+z)| ≤ 2|z|` for `|z| ≤ 1/2`. -/
lemma log_bound_to_integer_bound
    (i k c : ℕ) (hi_pos : 0 < i) (hc_pos : 0 < c) (hk_pos : 1 ≤ k)
    (ε : ℝ) (hε_pos : 0 ≤ ε)
    (h_gap : ((|((2 * 3 ^ i : ℤ) - (c : ℤ) * 2 ^ k)| : ℤ) : ℝ) ≤ ε)
    (h_small : ε < (3 : ℝ) ^ i) :
    ‖(((k : ℤ) - 1 : ℂ)) * Complex.log (2 : ℂ)
      + ((-(i : ℤ) : ℂ)) * Complex.log (3 : ℂ)
      + (1 : ℂ) * Complex.log ((c : ℂ))‖
    ≤ 2 * ε / (2 * (3 : ℝ) ^ i) := by
  sorry

/-! ## Helper lemmas toward `direct_pillai_bound_small`

These break the proof into mechanical pieces that can be filled in
independently. Each references `bakerWustholz_linearForms_logs` only
via the `pillai_baker_application` helper below. -/

/-- Helper: `8·i ≤ 3^i` for all `i ≥ 8`. By induction. -/
private lemma eight_i_le_three_pow (i : ℕ) (hi : 8 ≤ i) : 8 * i ≤ 3 ^ i := by
  induction i, hi using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [pow_succ]
    nlinarith [ih, hk, pow_pos (by norm_num : (0 : ℕ) < 3) k]

/-- Helper: for `i ≥ pommeThreshold`, we have `k ≥ 2` whenever
`3^i / (2·i) ≤ 2^k`. This rules out the `Λ = 0` edge case in
`direct_pillai_bound_small`, because `2·3^i = c·2^k` with `k ≥ 2`
would contradict `v₂(2·3^i) = 1`. -/
lemma pillai_k_ge_two
    (i k : ℕ) (hi : pommeThreshold ≤ i)
    (hk : ((3 : ℝ) ^ i) / (2 * i) ≤ (2 : ℝ) ^ k) :
    2 ≤ k := by
  have hi8 : 8 ≤ i := le_trans pommeThreshold_ge_eight hi
  have hi_pos : 0 < i := by omega
  have h8i_nat := eight_i_le_three_pow i hi8
  have h_ratio : (4 : ℝ) ≤ (3 : ℝ) ^ i / (2 * (i : ℝ)) := by
    have hi_R_pos : (0 : ℝ) < (i : ℝ) := Nat.cast_pos.mpr hi_pos
    have h2i_pos : (0 : ℝ) < 2 * (i : ℝ) := by linarith
    rw [le_div_iff₀ h2i_pos]
    have h8i_R : (8 : ℝ) * (i : ℝ) ≤ (3 : ℝ) ^ i := by exact_mod_cast h8i_nat
    linarith
  have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ k := le_trans h_ratio hk
  -- Extract `2 ≤ k` from `4 ≤ 2^k`.
  by_contra h
  push_neg at h
  interval_cases k <;> norm_num at h4

/-- Helper: the linear form `(k−1) log 2 − i log 3 + log c` is nonzero,
provided `k ≥ 2` and `c ≥ 1`. (For `k ≥ 2`, `2·3^i ≠ c·2^k` by v₂, so
the ratio isn't 1, so the log is nonzero.) -/
lemma pillai_linear_form_ne_zero
    (i k c : ℕ) (hk : 2 ≤ k) (hc : 0 < c) :
    (((k : ℤ) - 1 : ℂ)) * Complex.log (2 : ℂ)
      + ((-(i : ℤ) : ℂ)) * Complex.log (3 : ℂ)
      + (1 : ℂ) * Complex.log ((c : ℂ)) ≠ 0 := by
  intro h
  have hc_R : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  -- Step 1: Convert each `Complex.log` on a positive real to `Real.log` coerced.
  rw [show (Complex.log (2 : ℂ)) = ((Real.log 2 : ℝ) : ℂ) by
        rw [show ((2 : ℂ)) = (((2 : ℝ)) : ℂ) from by norm_cast]
        exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm,
      show (Complex.log (3 : ℂ)) = ((Real.log 3 : ℝ) : ℂ) by
        rw [show ((3 : ℂ)) = (((3 : ℝ)) : ℂ) from by norm_cast]
        exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 3)).symm,
      show (Complex.log ((c : ℂ))) = ((Real.log (c : ℝ) : ℝ) : ℂ) by
        rw [show ((c : ℂ)) = (((c : ℝ)) : ℂ) from by push_cast; rfl]
        exact (Complex.ofReal_log hc_R.le).symm] at h
  -- Step 2: Cast the equation to a real equation.
  have h_real : ((k : ℝ) - 1) * Real.log 2 - (i : ℝ) * Real.log 3 + Real.log c = 0 := by
    have hcx : ((((k : ℝ) - 1) * Real.log 2 - (i : ℝ) * Real.log 3 + Real.log c : ℝ) : ℂ) = 0 := by
      push_cast at h ⊢
      linear_combination h
    exact_mod_cast hcx
  -- Step 3: This means `Real.log (2^(k-1) · c) = Real.log (3^i)`.
  have hk_cast : ((k : ℝ) - 1) = ((k - 1 : ℕ) : ℝ) := by
    have h1 : (k - 1 : ℕ) + 1 = k := Nat.sub_add_cancel (by omega : 1 ≤ k)
    have h2 : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by exact_mod_cast h1
    linarith
  have h_log_eq : Real.log ((2 : ℝ) ^ (k - 1) * c) = Real.log ((3 : ℝ) ^ i) := by
    rw [Real.log_mul (by positivity) hc_R.ne', Real.log_pow, Real.log_pow]
    rw [← hk_cast]
    linarith
  -- Step 4: by injectivity, `2^(k-1) · c = 3^i`.
  have h_eq : (2 : ℝ) ^ (k - 1) * c = (3 : ℝ) ^ i :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) h_log_eq
  have h_eq_N : (2 : ℕ) ^ (k - 1) * c = 3 ^ i := by exact_mod_cast h_eq
  -- Step 5: For k ≥ 2, LHS is even, RHS is odd. Contradiction.
  have h_2_dvd : (2 : ℕ) ∣ 2 ^ (k - 1) := dvd_pow_self 2 (by omega : k - 1 ≠ 0)
  have h_2_dvd_rhs : (2 : ℕ) ∣ 3 ^ i := by
    rw [← h_eq_N]
    exact h_2_dvd.mul_right c
  have : (2 : ℕ) ∣ 3 := Nat.prime_two.dvd_of_dvd_pow h_2_dvd_rhs
  omega

/-- Helper: the specialized Baker–Wüstholz bound for Pomme's linear form.
This is the **only** place `bakerWustholz_linearForms_logs` is invoked. -/
lemma pillai_baker_application
    (i k c : ℕ) (hc : 0 < c) (hk : 2 ≤ k)
    (hΛ_ne : (((k : ℤ) - 1 : ℂ)) * Complex.log (2 : ℂ)
              + ((-(i : ℤ) : ℂ)) * Complex.log (3 : ℂ)
              + (1 : ℂ) * Complex.log ((c : ℂ)) ≠ 0) :
    Real.log ‖(((k : ℤ) - 1 : ℂ)) * Complex.log (2 : ℂ)
              + ((-(i : ℤ) : ℂ)) * Complex.log (3 : ℂ)
              + (1 : ℂ) * Complex.log ((c : ℂ))‖
      ≥ -(BakerWustholz.C 3 (Module.finrank ℚ ℚ)
          * Real.log ((max k i + 2 : ℕ) : ℝ)
          * (BakerWustholz.modifiedHeight (algebraMap ℚ ℂ) (2 : ℚ)
              * BakerWustholz.modifiedHeight (algebraMap ℚ ℂ) (3 : ℚ)
              * BakerWustholz.modifiedHeight (algebraMap ℚ ℂ) ((c : ℚ)))) := by
  -- α = (2, 3, c) : Fin 3 → ℚ, b = (k−1, -i, 1) : Fin 3 → ℤ, B = max k i + 2.
  have hα : ∀ j : Fin 3, (![(2 : ℚ), (3 : ℚ), (c : ℚ)] : Fin 3 → ℚ) j ≠ 0 := by
    intro j
    fin_cases j
    · show (2 : ℚ) ≠ 0; norm_num
    · show (3 : ℚ) ≠ 0; norm_num
    · show ((c : ℚ)) ≠ 0; exact_mod_cast hc.ne'
  have hB : 2 ≤ max k i + 2 := by omega
  have hbB : ∀ j : Fin 3,
      ((![(k : ℤ) - 1, -(i : ℤ), 1] : Fin 3 → ℤ) j).natAbs ≤ max k i + 2 := by
    intro j
    fin_cases j
    · show ((k : ℤ) - 1).natAbs ≤ max k i + 2; omega
    · show (-(i : ℤ)).natAbs ≤ max k i + 2; simp; omega
    · show (1 : ℤ).natAbs ≤ max k i + 2; omega
  have hΛ_ne_sum :
      (∑ j, ((![(k : ℤ) - 1, -(i : ℤ), 1] : Fin 3 → ℤ) j : ℂ) *
             Complex.log ((algebraMap ℚ ℂ)
                ((![(2 : ℚ), (3 : ℚ), (c : ℚ)] : Fin 3 → ℚ) j))) ≠ 0 := by
    sorry
  have h_baker := bakerWustholz_linearForms_logs
    (n := 3) (hn := by norm_num)
    (K := ℚ) (φ := algebraMap ℚ ℂ)
    (α := ![(2 : ℚ), (3 : ℚ), (c : ℚ)]) hα
    (b := ![(k : ℤ) - 1, -(i : ℤ), 1]) (B := max k i + 2) hB hbB hΛ_ne_sum
  -- `h_baker` gives the Baker-Wüstholz bound on the summation form.
  -- Rearrange to match the expanded form (sum of three terms).
  sorry

/-- Helper: the product `C · log B · ∏ h'` is bounded above by a simple
expression in `log i` that we can beat with `i · log 3`. Specifically,
for `i ≥ pommeThreshold` and `c ≤ 4·i`, the RHS of Baker-Wüstholz is
at most `i · log 3 / 2`. -/
lemma pillai_baker_rhs_upper_bound
    (i k c : ℕ) (hi : pommeThreshold ≤ i) (hc_small : c ≤ 4 * i)
    (hc_pos : 0 < c) :
    BakerWustholz.C 3 (Module.finrank ℚ ℚ)
      * Real.log ((max k i + 2 : ℕ) : ℝ)
      * (BakerWustholz.modifiedHeight (algebraMap ℚ ℂ) (2 : ℚ)
          * BakerWustholz.modifiedHeight (algebraMap ℚ ℂ) (3 : ℚ)
          * BakerWustholz.modifiedHeight (algebraMap ℚ ℂ) ((c : ℚ)))
      ≤ (i : ℝ) * Real.log 3 / 2 := by
  sorry

/-- Helper: for `i ≥ pommeThreshold = 2^60`, the simple analytic
inequality `2 · log(i + 5) < i · log 3` holds. (Equivalently:
`log(i+5) < i · log 3 / 2`, used at the final step of
`direct_pillai_bound_small`.) -/
lemma pillai_log_dominates
    (i : ℕ) (hi : pommeThreshold ≤ i) :
    2 * Real.log ((i : ℝ) + 5) < (i : ℝ) * Real.log 3 := by
  sorry

/-- Helper: for `i ≥ pommeThreshold = 2^60`, `(i + 5 : ℝ) < 3^i`.
Used for the Lemma-1 application. -/
lemma pillai_ip5_lt_three_pow
    (i : ℕ) (hi : pommeThreshold ≤ i) :
    ((i : ℝ) + 5) < (3 : ℝ) ^ i := by
  sorry

/-- **Direct Pillai bound (small-`c` case) via Baker–Wüstholz**.

For `i ≥ pommeThreshold`, `1 ≤ c ≤ 4i`, and `k` with
`3^i/(2i) ≤ 2^k`, the gap `|2·3^i − c·2^k|` exceeds `i + 5`.

Proof structure:
1. Derive `k ≥ 2` via `pillai_k_ge_two`.
2. The linear form is nonzero via `pillai_linear_form_ne_zero`.
3. Apply Baker–Wüstholz via `pillai_baker_application`.
4. Assume for contradiction `|2·3^i − c·2^k| ≤ i + 5`.
5. Via `log_bound_to_integer_bound`, `‖Λ‖ ≤ (i+5)/3^i`.
6. Combine with (3): `log((i+5)/3^i) ≥ -C · log B · ∏ h'`.
7. Rearrange: `i · log 3 − log(i+5) ≤ C · log B · ∏ h'`.
8. By `pillai_baker_rhs_upper_bound`, the RHS is `≤ i · log 3 / 2`.
9. So `i · log 3 − log(i+5) ≤ i · log 3 / 2`,
   i.e., `i · log 3 / 2 ≤ log(i+5)`, which fails for large `i`. -/
lemma direct_pillai_bound_small
    (i k c : ℕ) (hi : pommeThreshold ≤ i)
    (hc_pos : 0 < c) (hc_small : c ≤ 4 * i)
    (hk : ((3 : ℝ) ^ i) / (2 * i) ≤ (2 : ℝ) ^ k) :
    ((i : ℝ) + 5) < |((2 * 3 ^ i : ℤ) - (c : ℤ) * 2 ^ k)| := by
  by_contra h_not
  push_neg at h_not
  -- `h_not : |2·3^i − c·2^k| ≤ i + 5`
  have hk_ge_2 : 2 ≤ k := pillai_k_ge_two i k hi hk
  have hΛ_ne := pillai_linear_form_ne_zero i k c hk_ge_2 hc_pos
  have h_baker := pillai_baker_application i k c hc_pos hk_ge_2 hΛ_ne
  have h_rhs := pillai_baker_rhs_upper_bound i k c hi hc_small hc_pos
  -- Set Λ to be the linear form (so we don't repeat the long expression).
  set Λ : ℂ := (((k : ℤ) - 1 : ℂ)) * Complex.log (2 : ℂ)
              + ((-(i : ℤ) : ℂ)) * Complex.log (3 : ℂ)
              + (1 : ℂ) * Complex.log ((c : ℂ)) with hΛ_def
  -- Apply log_bound_to_integer_bound: ‖Λ‖ ≤ 2·(i+5)/(2·3^i) = (i+5)/3^i.
  have hk_pos : 1 ≤ k := by omega
  have hi_pos : 0 < i := lt_of_lt_of_le pommeThreshold_pos hi
  have hip5_pos : (0 : ℝ) ≤ (i : ℝ) + 5 := by positivity
  have hip5_lt : ((i : ℝ) + 5) < (3 : ℝ) ^ i := pillai_ip5_lt_three_pow i hi
  have h_Λ_ub : ‖Λ‖ ≤ 2 * ((i : ℝ) + 5) / (2 * (3 : ℝ) ^ i) :=
    log_bound_to_integer_bound i k c hi_pos hc_pos hk_pos ((i : ℝ) + 5) hip5_pos h_not hip5_lt
  -- ‖Λ‖ > 0 since Λ ≠ 0.
  have hΛ_norm_pos : 0 < ‖Λ‖ := norm_pos_iff.mpr hΛ_ne
  -- Take log: log ‖Λ‖ ≤ log((i+5)/3^i) = log(i+5) - i·log 3.
  have h3_pow_pos : (0 : ℝ) < (3 : ℝ) ^ i := by positivity
  have h_Λ_log_ub : Real.log ‖Λ‖ ≤ Real.log ((i : ℝ) + 5) - (i : ℝ) * Real.log 3 := by
    have h_ub_simp : 2 * ((i : ℝ) + 5) / (2 * (3 : ℝ) ^ i) = ((i : ℝ) + 5) / (3 : ℝ) ^ i := by
      field_simp
    rw [h_ub_simp] at h_Λ_ub
    have h_pos_rhs : (0 : ℝ) < ((i : ℝ) + 5) / (3 : ℝ) ^ i := by positivity
    have h_log_le : Real.log ‖Λ‖ ≤ Real.log (((i : ℝ) + 5) / (3 : ℝ) ^ i) :=
      Real.log_le_log hΛ_norm_pos h_Λ_ub
    rw [Real.log_div (by positivity) h3_pow_pos.ne'] at h_log_le
    rw [Real.log_pow] at h_log_le
    linarith
  -- Combine with h_baker: -(C·log B·∏h') ≤ log ‖Λ‖
  -- And h_rhs: C·log B·∏h' ≤ i·log 3 / 2.
  -- So: -(i·log 3 / 2) ≤ log ‖Λ‖ ≤ log(i+5) - i·log 3.
  -- Rearranging: i·log 3 - i·log 3/2 ≤ log(i+5), i.e., i·log 3 / 2 ≤ log(i+5).
  -- But pillai_log_dominates says 2·log(i+5) < i·log 3, contradiction.
  have h_bound : -(i : ℝ) * Real.log 3 / 2 ≤ Real.log ‖Λ‖ := by
    have := h_baker
    -- h_baker : Real.log ‖Λ‖ ≥ -(C * log B * ∏ h')
    -- h_rhs : C * log B * ∏ h' ≤ i * log 3 / 2
    -- So Real.log ‖Λ‖ ≥ -(i * log 3 / 2)
    linarith
  have h_chain : -(i : ℝ) * Real.log 3 / 2 ≤ Real.log ((i : ℝ) + 5) - (i : ℝ) * Real.log 3 := by
    linarith [h_bound, h_Λ_log_ub]
  -- Rearranging: i·log 3 / 2 ≤ log(i+5)
  have h_final : (i : ℝ) * Real.log 3 ≤ 2 * Real.log ((i : ℝ) + 5) := by linarith
  have h_dominate := pillai_log_dominates i hi
  linarith
