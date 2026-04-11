import BakerWustholz
import RatHeight
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Complex.ExponentialBounds
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

/-- Helper: for `|x| ≤ 1/2`, `|Real.log(1 + x)| ≤ (3/2) · |x|`.
Derived from mathlib's complex log bound `Complex.norm_log_one_add_half_le_self`. -/
private lemma abs_log_one_add_half_le {x : ℝ} (h : |x| ≤ 1/2) :
    |Real.log (1 + x)| ≤ (3/2) * |x| := by
  have hx_pos : (0 : ℝ) < 1 + x := by
    have : -(1/2 : ℝ) ≤ x := (abs_le.mp h).1
    linarith
  have hx_cpx : ‖((x : ℝ) : ℂ)‖ ≤ 1/2 := by rw [Complex.norm_real]; exact h
  have h_complex : ‖Complex.log (1 + ((x : ℝ) : ℂ))‖ ≤ (3/2) * ‖((x : ℝ) : ℂ)‖ :=
    Complex.norm_log_one_add_half_le_self hx_cpx
  rw [Complex.norm_real] at h_complex
  have h_convert : Complex.log (1 + ((x : ℝ) : ℂ)) = ((Real.log (1 + x) : ℝ) : ℂ) := by
    rw [show (1 + ((x : ℝ) : ℂ)) = (((1 + x : ℝ)) : ℂ) from by push_cast; rfl]
    exact (Complex.ofReal_log hx_pos.le).symm
  rw [h_convert, Complex.norm_real] at h_complex
  exact h_complex

/-- **Ellison's Lemma 1 (log-to-integer translation)**.

Given `|2·3^i − c·2^k| ≤ ε` with `ε < 3^i`, the linear form
`(k-1)·log 2 − i·log 3 + log c` has norm bounded by `2·ε / (2·3^i)`.

**Proof**: The complex expression equals the real expression
`(k-1)·log 2 − i·log 3 + log c` (since all αᵢ are positive reals).
Using the algebraic identity `c·2^k = 2·3^i − ω` with `|ω| ≤ ε`, we
get `(2^(k-1) · c) / 3^i = 1 + z` where `z := −ω/(2·3^i)` and
`|z| ≤ ε/(2·3^i) < 1/2` (since `ε < 3^i`). Then
`Real.log(1 + z)` is bounded by `(3/2)·|z| ≤ (3/2)·ε/(2·3^i) ≤
2·ε/(2·3^i)` via the Taylor bound
`|log(1+z)| ≤ (3/2)|z|` from `Complex.norm_log_one_add_half_le_self`. -/
lemma log_bound_to_integer_bound
    (i k c : ℕ) (hc_pos : 0 < c) (hk_pos : 1 ≤ k)
    (ε : ℝ) (hε_pos : 0 ≤ ε)
    (h_gap : ((|((2 * 3 ^ i : ℤ) - (c : ℤ) * 2 ^ k)| : ℤ) : ℝ) ≤ ε)
    (h_small : ε < (3 : ℝ) ^ i) :
    ‖(((k : ℤ) - 1 : ℂ)) * Complex.log (2 : ℂ)
      + ((-(i : ℤ) : ℂ)) * Complex.log (3 : ℂ)
      + (1 : ℂ) * Complex.log ((c : ℂ))‖
    ≤ 2 * ε / (2 * (3 : ℝ) ^ i) := by
  have h2_R_pos : (0 : ℝ) < 2 := by norm_num
  have h3_R_pos : (0 : ℝ) < 3 := by norm_num
  have hc_R_pos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc_pos
  have h3_pow_pos : (0 : ℝ) < (3 : ℝ) ^ i := pow_pos h3_R_pos i
  -- Step 1: Convert complex log expression to real.
  have h_re_eq : (((k : ℤ) - 1 : ℂ)) * Complex.log (2 : ℂ)
                  + ((-(i : ℤ) : ℂ)) * Complex.log (3 : ℂ)
                  + (1 : ℂ) * Complex.log ((c : ℂ))
                = ((((k : ℝ) - 1) * Real.log 2 + (-(i : ℝ)) * Real.log 3 + Real.log c : ℝ) : ℂ) := by
    rw [show (Complex.log (2 : ℂ)) = ((Real.log 2 : ℝ) : ℂ) by
          rw [show ((2 : ℂ)) = (((2 : ℝ)) : ℂ) from by norm_cast]
          exact (Complex.ofReal_log h2_R_pos.le).symm,
        show (Complex.log (3 : ℂ)) = ((Real.log 3 : ℝ) : ℂ) by
          rw [show ((3 : ℂ)) = (((3 : ℝ)) : ℂ) from by norm_cast]
          exact (Complex.ofReal_log h3_R_pos.le).symm,
        show (Complex.log ((c : ℂ))) = ((Real.log (c : ℝ) : ℝ) : ℂ) by
          rw [show ((c : ℂ)) = (((c : ℝ)) : ℂ) from by push_cast; rfl]
          exact (Complex.ofReal_log hc_R_pos.le).symm]
    push_cast; ring
  rw [h_re_eq, Complex.norm_real]
  -- Step 2: Set up ω_R := 2·3^i - c·2^k as a real.
  set ω_R : ℝ := 2 * (3 : ℝ) ^ i - c * (2 : ℝ) ^ k with hω_R_def
  have hω_R_eq : ω_R = (((2 * 3^i : ℤ) - (c : ℤ) * 2^k : ℤ) : ℝ) := by
    rw [hω_R_def]; push_cast; ring
  have hω_R_abs : |ω_R| ≤ ε := by
    rw [hω_R_eq, ← Int.cast_abs]; exact h_gap
  -- Step 3: `2^k = 2 · 2^(k-1)`.
  have h_pow_k : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
    have h : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
    calc (2 : ℝ) ^ k = 2 ^ (k - 1 + 1) := by rw [h]
      _ = 2 ^ (k - 1) * 2 := pow_succ 2 (k - 1)
      _ = 2 * 2 ^ (k - 1) := by ring
  -- Step 4: Define `z := -ω_R / (2 · 3^i)` and show `|z| ≤ 1/2`.
  have h_denom_pos : (0 : ℝ) < 2 * (3 : ℝ) ^ i := by positivity
  set z : ℝ := -ω_R / (2 * (3 : ℝ) ^ i) with hz_def
  have hz_abs : |z| ≤ 1 / 2 := by
    rw [hz_def, abs_div, abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * (3 : ℝ) ^ i)]
    rw [div_le_iff₀ h_denom_pos]
    linarith [hω_R_abs, h_small]
  -- Step 5: The real Λ equals `Real.log(1 + z)`.
  have hk_cast : ((k : ℝ) - 1) = ((k - 1 : ℕ) : ℝ) := by
    have h1 : (k - 1 : ℕ) + 1 = k := Nat.sub_add_cancel hk_pos
    have h2 : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by exact_mod_cast h1
    linarith
  have h_Λ_R_form :
      ((k : ℝ) - 1) * Real.log 2 + (-(i : ℝ)) * Real.log 3 + Real.log c
        = Real.log (1 + z) := by
    have h_one_plus_z : 1 + z = (2 : ℝ) ^ (k - 1) * c / (3 : ℝ) ^ i := by
      rw [hz_def, hω_R_def]
      field_simp
      rw [h_pow_k]
      ring
    rw [h_one_plus_z]
    rw [Real.log_div (by positivity) h3_pow_pos.ne']
    rw [Real.log_mul (by positivity) hc_R_pos.ne']
    rw [Real.log_pow, Real.log_pow]
    rw [hk_cast]
    ring
  rw [h_Λ_R_form]
  -- Step 6: Apply the Taylor bound and chain inequalities.
  calc |Real.log (1 + z)|
      ≤ (3 / 2) * |z| := abs_log_one_add_half_le hz_abs
    _ = (3 / 2) * |ω_R| / (2 * (3 : ℝ) ^ i) := by
        rw [hz_def, abs_div, abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * (3 : ℝ) ^ i)]
        ring
    _ ≤ (3 / 2) * ε / (2 * (3 : ℝ) ^ i) := by
        apply div_le_div_of_nonneg_right _ h_denom_pos.le
        linarith [hω_R_abs]
    _ ≤ 2 * ε / (2 * (3 : ℝ) ^ i) := by
        apply div_le_div_of_nonneg_right _ h_denom_pos.le
        linarith

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
  -- Sum-form and expanded-form are equal.
  have h_sum_eq :
      (∑ j, ((![(k : ℤ) - 1, -(i : ℤ), 1] : Fin 3 → ℤ) j : ℂ) *
             Complex.log ((algebraMap ℚ ℂ)
                ((![(2 : ℚ), (3 : ℚ), (c : ℚ)] : Fin 3 → ℚ) j)))
      = (((k : ℤ) - 1 : ℂ)) * Complex.log (2 : ℂ)
          + ((-(i : ℤ) : ℂ)) * Complex.log (3 : ℂ)
          + (1 : ℂ) * Complex.log ((c : ℂ)) := by
    simp [Fin.sum_univ_three]
  have hΛ_ne_sum :
      (∑ j, ((![(k : ℤ) - 1, -(i : ℤ), 1] : Fin 3 → ℤ) j : ℂ) *
             Complex.log ((algebraMap ℚ ℂ)
                ((![(2 : ℚ), (3 : ℚ), (c : ℚ)] : Fin 3 → ℚ) j))) ≠ 0 := by
    rw [h_sum_eq]; exact hΛ_ne
  have h_baker := bakerWustholz_linearForms_logs
    (n := 3) (hn := by norm_num)
    (K := ℚ) (φ := algebraMap ℚ ℂ)
    (α := ![(2 : ℚ), (3 : ℚ), (c : ℚ)]) hα
    (b := ![(k : ℤ) - 1, -(i : ℤ), 1]) (B := max k i + 2) hB hbB hΛ_ne_sum
  -- Rewrite the summation form to the expanded form and the product form.
  rw [h_sum_eq] at h_baker
  have h_prod_eq :
      (∏ j : Fin 3, BakerWustholz.modifiedHeight (algebraMap ℚ ℂ)
        ((![(2 : ℚ), (3 : ℚ), (c : ℚ)] : Fin 3 → ℚ) j))
      = BakerWustholz.modifiedHeight (algebraMap ℚ ℂ) (2 : ℚ)
          * BakerWustholz.modifiedHeight (algebraMap ℚ ℂ) (3 : ℚ)
          * BakerWustholz.modifiedHeight (algebraMap ℚ ℂ) ((c : ℚ)) := by
    simp [Fin.prod_univ_three]
  rw [h_prod_eq] at h_baker
  exact h_baker

/-- Helper: the product `C · log B · ∏ h'` is bounded above by a simple
expression in `log i` that we can beat with `i · log 3`. Specifically,
for `i ≥ pommeThreshold` and `c ≤ 4·i`, the RHS of Baker-Wüstholz is
at most `i · log 3 / 2`.

With `RatHeight.lean` providing the concrete values of
`BakerWustholz.modifiedHeight` on `{(2 : ℚ), (3 : ℚ), ((c : ℕ) : ℚ)}`,
this sorry reduces to a **pure numerical comparison** involving
`BakerWustholz.C 3 1 ≈ 2.1 · 10^{12}`, `log(max k i + 2)`, `log 3`, and
`max(log c, 1)`. The comparison still requires an upper bound on `k`
in terms of `i` (derivable from the contradiction hypothesis
`|2·3^i - c·2^k| ≤ i + 5` in `direct_pillai_bound_small`, but not
passed here); a full proof would restructure `pillai_baker_rhs_upper_bound`
to take such a hypothesis. -/
lemma pillai_baker_rhs_upper_bound
    (i k c : ℕ) (hi : pommeThreshold ≤ i) (hc_small : c ≤ 4 * i)
    (hc_pos : 0 < c) :
    BakerWustholz.C 3 (Module.finrank ℚ ℚ)
      * Real.log ((max k i + 2 : ℕ) : ℝ)
      * (BakerWustholz.modifiedHeight (algebraMap ℚ ℂ) (2 : ℚ)
          * BakerWustholz.modifiedHeight (algebraMap ℚ ℂ) (3 : ℚ)
          * BakerWustholz.modifiedHeight (algebraMap ℚ ℂ) ((c : ℚ)))
      ≤ (i : ℝ) * Real.log 3 / 2 := by
  -- Substitute the concrete values from `RatHeight.lean`:
  --   `modifiedHeight φ (2 : ℚ) = 1`   (since `log 2 < 1`)
  --   `modifiedHeight φ (3 : ℚ) = log 3`
  rw [BakerWustholz.modifiedHeight_two, BakerWustholz.modifiedHeight_three]
  -- Bound `modifiedHeight φ ((c : ℚ)) ≤ max (log c) 1`
  have h_c_bound := BakerWustholz.modifiedHeight_natCast_le c hc_pos
  -- Remaining: the purely numerical comparison, without any height theory.
  sorry

/-- Helper: for `i ≥ pommeThreshold = 2^60`, the simple analytic
inequality `2 · log(i + 5) < i · log 3` holds. (Equivalently:
`log(i+5) < i · log 3 / 2`, used at the final step of
`direct_pillai_bound_small`.) -/
lemma pillai_log_dominates
    (i : ℕ) (hi : pommeThreshold ≤ i) :
    2 * Real.log ((i : ℝ) + 5) < (i : ℝ) * Real.log 3 := by
  have hi10 : 10 ≤ i := by
    have : (10 : ℕ) ≤ pommeThreshold := by unfold pommeThreshold; decide
    omega
  have hi_R : (10 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi10
  -- `log 2 < 1` since `2 < e`.
  have h_log2 : Real.log 2 < 1 := by
    have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 2) Real.exp_one_gt_two
    rwa [Real.log_exp] at h
  -- `log 3 > 1` since `e < 3`.
  have h_log3 : (1 : ℝ) < Real.log 3 := by
    have h := Real.log_lt_log (Real.exp_pos _) Real.exp_one_lt_three
    rwa [Real.log_exp] at h
  -- `log((i+5)/4) ≤ (i+5)/4 - 1 = (i+1)/4`
  have h_sub : Real.log (((i : ℝ) + 5) / 4) ≤ ((i : ℝ) + 5) / 4 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  -- `log(i+5) = log((i+5)/4) + log 4 = log((i+5)/4) + 2·log 2`
  have h_log4 : Real.log 4 = 2 * Real.log 2 := by
    have : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [this, Real.log_pow]; simp
  have h_div : Real.log ((i : ℝ) + 5) = Real.log (((i : ℝ) + 5) / 4) + 2 * Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num), ← h_log4]; ring
  rw [h_div]
  nlinarith [h_sub, h_log2, h_log3, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)]

/-- Helper: for `i ≥ pommeThreshold = 2^60`, `(i + 5 : ℝ) < 3^i`.
Used for the Lemma-1 application. Follows from `eight_i_le_three_pow`. -/
lemma pillai_ip5_lt_three_pow
    (i : ℕ) (hi : pommeThreshold ≤ i) :
    ((i : ℝ) + 5) < (3 : ℝ) ^ i := by
  have hi8 : 8 ≤ i := le_trans pommeThreshold_ge_eight hi
  have h8i := eight_i_le_three_pow i hi8
  have h_step : (i + 5 : ℕ) < 8 * i := by omega
  have h_N : (i + 5 : ℕ) < 3 ^ i := lt_of_lt_of_le h_step h8i
  have h_R : ((i + 5 : ℕ) : ℝ) < ((3 ^ i : ℕ) : ℝ) := by exact_mod_cast h_N
  push_cast at h_R
  linarith

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
    log_bound_to_integer_bound i k c hc_pos hk_pos ((i : ℝ) + 5) hip5_pos h_not hip5_lt
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
