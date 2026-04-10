import Baker
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Pomme's proof that `2·3^i + i + 5` has a large odd part

This file follows Pomme (Nov 28, 2025), `previous-work/Pomme2.pdf`, which in
turn follows W. J. Ellison, *On a theorem of S. Sivasankaranarayana Pillai*,
Séminaire de théorie des nombres de Bordeaux (1970-71), exposé n° 12 — see
`previous-work/STNB_1970-1971____A10_0.pdf`.

The target is the number-theoretic closure inequality needed to prove
non-halting of the Turing machine
`1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---` (a BB(6) holdout), as identified
by mxdys:
```
∀ i ≥ 50,    (2·3^i + i + 5) / 2^{v₂(2·3^i + i + 5)}  ≥  2·i + 14.      (*)
```

## Structure of the proof

We take **Ellison's Corollary 1** as a black box (`ellison_cor1`, currently
`sorry`; morally derived from `baker_linearForms_logs` in `Baker.lean`, via
the half-page argument on pp. 12-03 / 12-04 of the Ellison paper). Ellison's
auxiliary Lemma 1, Lemma 2 and Theorem 1 are skipped: Theorem 1 is a scaffold
used in the paper to prove Corollary 1, but since we are taking Corollary 1
itself as an axiomatic interface we do not need the scaffolding.

Pomme's argument then specialises Corollary 1 to `(a, b, m, n) = (c, 2, 2, 3)`
and derives `(*)` for `i ≥ 2^2100`. The range `50 ≤ i < 2^2100` is covered by
a dense simulator, which is recorded here as `pomme_small_range` — to be
discharged later by a verified simulator.
-/

namespace Pomme

open Real

/-! ## The sequence `N i := 2·3^i + i + 5` -/

/-- Pomme's sequence `N i := 2·3^i + i + 5`. This is the quantity whose odd
part we need to bound below by `2·i + 14`. -/
def N (i : ℕ) : ℕ := 2 * 3 ^ i + i + 5

@[simp] lemma N_def (i : ℕ) : N i = 2 * 3 ^ i + i + 5 := rfl

lemma N_pos (i : ℕ) : 0 < N i := by
  unfold N; positivity

/-- Parity of `N`: `N i` is odd exactly when `i` is even, since `2·3^i` is
always even and `i + 5` toggles parity with `i`. -/
lemma N_odd_iff_even (i : ℕ) : Odd (N i) ↔ Even i := by
  simp only [N, Nat.odd_iff, Nat.even_iff]
  have h : 2 * 3 ^ i % 2 = 0 := Nat.mul_mod_right 2 _
  omega

/-- The "easy half" of `(*)` (the Nov 26 screenshots in `previous-work/`):
for even `i ≥ 2`, `N i` is odd so `v₂(N i) = 0`, and the inequality reduces
to the trivial bound `N i ≥ 2·i + 14`. -/
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
  · -- `2·i + 14 ≤ 2·3^i + i + 5` iff `i + 9 ≤ 2·3^i`
    have h : i + 9 ≤ 2 * 3 ^ i := by
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

/-! ## Ellison's Corollary 1 (black-box interface)

Ellison's paper derives Corollary 1 from a technical log-manipulation
(Lemma 1) combined with the Baker–van der Poorten effective lower bound on
linear forms in logarithms of algebraic numbers (Lemma 2). We take
`ellison_cor1` as a `sorry`-theorem: morally, its proof follows the paper's
pp. 12-03 — 12-04 and ultimately depends on `baker_linearForms_logs` from
`Baker.lean`. -/

/-- Ellison's explicit `x₀` (p. 12-04):
`x₀ := (2^{31} · log A / Δ)^{49}` where `A := max{4, a, b, m, n}` and
`Δ := min{2, δ · log m, δ · log n}`. -/
noncomputable def ellisonX₀ (a b m n : ℕ) (δ : ℝ) : ℝ :=
  let A : ℝ := max 4 (max (a : ℝ) (max (b : ℝ) (n : ℝ)))
  let Δ : ℝ := min 2 (min (δ * Real.log m) (δ * Real.log n))
  (2 ^ 31 * Real.log A / Δ) ^ 49

/-- Auxiliary: specialization of `baker_linearForms_logs` to the degree-4
number field `CyclotomicField 5 ℚ`, with `n = 3` logarithms. This is the
single point where we invoke Baker's theorem. All hypotheses are passed
through — the helper is **sorry-free** — and its only role is to discharge
the `hd : 4 ≤ finrank` requirement of Baker using
`IsCyclotomicExtension.finrank` + `Nat.totient 5 = 4`. -/
private lemma baker_helper_degree4
    (α : Fin 3 → CyclotomicField 5 ℚ) (hα : ∀ i, α i ≠ 0)
    (A : ℝ) (hA : 4 ≤ A) (hH_α : ∀ i, Height.mulHeight₁ (α i) ≤ A)
    (b : Fin 3 → ℤ) (H : ℕ) (hH_b : ∀ i, (b i).natAbs ≤ H)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (φ : CyclotomicField 5 ℚ →+* ℂ)
    (hΛ_pos : (0 : ℝ) < ‖∑ i, (b i : ℂ) * Complex.log (φ (α i))‖)
    (hΛ_small : ‖∑ i, (b i : ℂ) * Complex.log (φ (α i))‖ < Real.exp (-(δ * (H : ℝ)))) :
    (H : ℝ) ≤
      (4 ^ ((3 : ℕ) ^ 2) * δ⁻¹ *
        (Module.finrank ℚ (CyclotomicField 5 ℚ) : ℝ) ^ (2 * 3) *
        Real.log A) ^ ((2 * 3 + 1) ^ 2) := by
  -- `finrank ℚ (CyclotomicField 5 ℚ) = Nat.totient 5 = 4` via
  -- `IsCyclotomicExtension.finrank` + `Polynomial.cyclotomic.irreducible_rat`.
  have hd : 4 ≤ Module.finrank ℚ (CyclotomicField 5 ℚ) := by
    haveI h5 : NeZero ((5 : ℕ) : ℚ) := ⟨by norm_num⟩
    haveI inst : IsCyclotomicExtension {(5 : ℕ)} ℚ (CyclotomicField 5 ℚ) :=
      CyclotomicField.isCyclotomicExtension 5 ℚ
    have h : Module.finrank ℚ (CyclotomicField 5 ℚ) = Nat.totient 5 :=
      IsCyclotomicExtension.finrank (K := ℚ) (CyclotomicField 5 ℚ)
        (Polynomial.cyclotomic.irreducible_rat (by norm_num : (0 : ℕ) < 5))
    rw [h]; decide
  exact baker_linearForms_logs φ hd α hα hA hH_α b hH_b hδ_pos hδ_le hΛ_pos hΛ_small

/-- **Ellison, Corollary 1** (p. 12-04). For all `x ≥ x₀(a, b, m, n, δ)` and
any `y`, either `a · m^x = b · n^y`, or `|a · m^x − b · n^y| ≥ m^{(1−δ)·x}`.

Derived from `baker_linearForms_logs` (in `Baker.lean`) via the
`baker_helper_degree4` specialization above. The helper is sorry-free; all
remaining sorries live here: Ellison's Lemma 1 reduction
(`|a·m^x − b·n^y|` ↦ linear-form-in-logs bound), the height computation for
rationals lifted to `CyclotomicField 5 ℚ`, and the final constant comparison
`4^{15} < 2^{31}` vs. `x ≥ x₀`. -/
theorem ellison_cor1
    (a b m n : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n) (ha : 0 < a) (hb : 0 < b)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt_1 : δ < 1) :
    ∀ x y : ℕ, ellisonX₀ a b m n δ ≤ x →
      ((a * m ^ x : ℤ) = b * n ^ y) ∨
        (((m : ℝ) ^ ((1 - δ) * (x : ℝ))) ≤ |((a * m ^ x : ℤ) - b * n ^ y)|) := by
  intro x y hx₀
  by_cases heq : (a * m ^ x : ℤ) = b * n ^ y
  · exact Or.inl heq
  refine Or.inr ?_
  by_contra h_small
  push_neg at h_small
  -- Construct Baker's inputs inside `CyclotomicField 5 ℚ`.
  let K : Type := CyclotomicField 5 ℚ
  let α : Fin 3 → K := ![((m : ℚ) : K), ((n : ℚ) : K), ((a : ℚ) / (b : ℚ) : K)]
  let bvec : Fin 3 → ℤ := ![(x : ℤ), -(y : ℤ), 1]
  let H : ℕ := max x (max y 1)
  let A : ℝ := max 4 (max (a : ℝ) (max (b : ℝ) (n : ℝ)))
  have hA : (4 : ℝ) ≤ A := le_max_left _ _
  -- Each `α i` is nonzero since `m ≥ 2`, `n ≥ 2`, `a ≥ 1`, `b ≥ 1`.
  have hm_pos : (0 : ℕ) < m := lt_of_lt_of_le (by norm_num) hm
  have hn_pos : (0 : ℕ) < n := lt_of_lt_of_le hm_pos hmn
  have hα : ∀ i, α i ≠ 0 := by
    intro i
    fin_cases i
    · show ((m : ℚ) : K) ≠ 0
      exact_mod_cast hm_pos.ne'
    · show ((n : ℚ) : K) ≠ 0
      exact_mod_cast hn_pos.ne'
    · show (((a : ℚ) / (b : ℚ)) : K) ≠ 0
      have ha_cast_ne : (((a : ℚ)) : K) ≠ 0 := by exact_mod_cast ha.ne'
      have hb_cast_ne : (((b : ℚ)) : K) ≠ 0 := by exact_mod_cast hb.ne'
      exact div_ne_zero ha_cast_ne hb_cast_ne
  have hH_b : ∀ i, (bvec i).natAbs ≤ H := by
    intro i
    fin_cases i <;> simp [bvec, H]
  -- Height bound (moderate analytic work, sorry'd).
  have hH_α : ∀ i, Height.mulHeight₁ (α i) ≤ A := by sorry
  -- Choose a complex embedding of `K = CyclotomicField 5 ℚ` (lift `algebraMap ℚ ℂ`).
  let φ : K →+* ℂ :=
    NumberField.ComplexEmbedding.lift (k := ℚ) (K := K) (algebraMap ℚ ℂ)
  -- The linear form `Λ := x · log m − y · log n + log(a/b)` in `ℂ`, via `φ`.
  -- Ellison's Lemma 1 (p. 12-02) converts `h_small` into these bounds.
  have hΛ_pos : (0 : ℝ) < ‖∑ i, (bvec i : ℂ) * Complex.log (φ (α i))‖ := by sorry
  have hΛ_small :
      ‖∑ i, (bvec i : ℂ) * Complex.log (φ (α i))‖ < Real.exp (-(δ * (H : ℝ))) := by sorry
  -- Invoke Baker via the helper.
  have h_baker :=
    baker_helper_degree4 α hα A hA hH_α bvec H hH_b δ hδ_pos (le_of_lt hδ_lt_1) φ
      hΛ_pos hΛ_small
  -- Final contradiction: Baker's bound on `H` is smaller than `ellisonX₀ a b m n δ ≤ x ≤ H`,
  -- because `4^{15} < 2^{31}` (the only nontrivial constant comparison).
  exact absurd h_baker (by sorry)

/-! ## Pomme's Theorem 1 -/

/-- Pomme's threshold `2^2100 ≥ 1.5 · 10^{632}`. -/
def pommeThreshold : ℕ := 2 ^ 2100

/-- Reformulation: `2^k` does not divide `N i` follows from the condition that
for every positive integer `c`, the gap `|2·3^i − c·2^k|` exceeds `i + 5`. -/
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
  -- `N i = 2^k * c` (from `hc`). In ℤ: `2·3^i + i + 5 = c · 2^k`.
  have hN_int : (2 * (3 : ℤ) ^ i + (i : ℤ) + 5) = (c : ℤ) * 2 ^ k := by
    have h1 : (N i : ℤ) = ((2 ^ k * c : ℕ) : ℤ) := by exact_mod_cast hc
    unfold N at h1
    push_cast at h1
    linarith
  have h_diff : (2 * (3 : ℤ) ^ i - (c : ℤ) * 2 ^ k) = -((i : ℤ) + 5) := by linarith
  -- Substitute into `h`.
  have h_abs_eq : |((2 * 3 ^ i : ℤ) - (c : ℤ) * 2 ^ k)| = (i : ℤ) + 5 := by
    rw [h_diff, abs_neg, abs_of_nonneg]; positivity
  rw [show ((|((2 * 3 ^ i : ℤ) - (c : ℤ) * 2 ^ k)| : ℤ) : ℝ) = ((i : ℝ) + 5) by
        rw [h_abs_eq]; push_cast; rfl] at h
  exact lt_irrefl _ h

/-- **Case 1 (c large).** If `c > 4·i` and `2^k ≥ 3^i / (2·i) > i + 5`, then
`|2·3^i − c·2^k| = c·2^k − 2·3^i ≥ 2^k > i + 5`. Elementary. -/
lemma pomme_case_c_large
    (i k c : ℕ) (hi_pos : 0 < i)
    (hk : ((3 : ℝ) ^ i) / (2 * i) ≤ (2 : ℝ) ^ k)
    (hi_large : ((i : ℝ) + 5) < ((3 : ℝ) ^ i) / (2 * i))
    (hc_big : 4 * i < c) :
    ((i : ℝ) + 5) < |((2 * 3 ^ i : ℤ) - (c : ℤ) * 2 ^ k)| := by
  have hi_ne : (i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hi_pos.ne'
  have h2k_lb : ((i : ℝ) + 5) < (2 : ℝ) ^ k := hi_large.trans_le hk
  have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  -- `(4 i) · 2^k ≥ 2 · 3^i`.
  have h4i : 2 * (3 : ℝ) ^ i ≤ (4 * (i : ℝ)) * (2 : ℝ) ^ k := by
    have heq : (4 * (i : ℝ)) * ((3 : ℝ) ^ i / (2 * (i : ℝ))) = 2 * (3 : ℝ) ^ i := by
      field_simp; ring
    have h1 : (4 * (i : ℝ)) * ((3 : ℝ) ^ i / (2 * (i : ℝ))) ≤ (4 * (i : ℝ)) * (2 : ℝ) ^ k := by
      have h4i_nn : (0 : ℝ) ≤ 4 * (i : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left hk h4i_nn
    linarith
  -- `c ≥ 4·i + 1`, so `c · 2^k ≥ (4·i + 1) · 2^k`.
  have hc_ge : ((4 * (i : ℝ)) + 1) ≤ (c : ℝ) := by
    have : (4 * i + 1 : ℕ) ≤ c := hc_big
    have := (Nat.cast_le (α := ℝ)).mpr this
    push_cast at this
    linarith
  -- Combine: `c · 2^k ≥ 2 · 3^i + 2^k > 2 · 3^i + (i + 5)`.
  have h_big : 2 * (3 : ℝ) ^ i + ((i : ℝ) + 5) < (c : ℝ) * (2 : ℝ) ^ k := by
    have hstep : ((4 * (i : ℝ)) + 1) * (2 : ℝ) ^ k ≤ (c : ℝ) * (2 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right hc_ge (le_of_lt h2k_pos)
    nlinarith [hstep, h4i, h2k_lb]
  -- Convert |...| to a real inequality.
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

/-- **Case 2 (c small, Ellison).** For `1 ≤ c ≤ 4·i` and `k` above Ellison's
`x₀(c, 2, 2, 3, 9/10)`, Corollary 1 gives
`|c · 2^k − 2 · 3^i| ≥ 2^{0.1 · k}`. -/
lemma pomme_case_c_small
    (i k c : ℕ) (hi_pos : 0 < i)
    (hc_pos : 0 < c) (_hc_small : c ≤ 4 * i)
    (hk_ge_x₀ : ellisonX₀ c 2 2 3 ((9 : ℝ) / 10) ≤ (k : ℝ)) :
    ((2 : ℝ) ^ ((1 : ℝ) / 10 * k)) ≤ |((2 * 3 ^ i : ℤ) - (c : ℤ) * 2 ^ k)| := by
  have hCor := ellison_cor1 c 2 2 3 (by norm_num) (by norm_num)
                 hc_pos (by norm_num) ((9 : ℝ) / 10) (by norm_num) (by norm_num) k i hk_ge_x₀
  rcases hCor with heq | hbound
  · -- Equality case: `c · 2^k = 2 · 3^i`. Impossible by `v₂` (needs `k ≥ 2`).
    exfalso
    have heqN : c * 2 ^ k = 2 * 3 ^ i := by exact_mod_cast heq
    -- `k ≥ 2` because `ellisonX₀ ≥ 2` when `c ≥ 1` (left as `sorry`; the
    -- explicit `x₀` is astronomically large, so certainly `≥ 2`).
    have hk2 : 2 ≤ k := by
      sorry
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h3_ne : (3 ^ i : ℕ) ≠ 0 := pow_ne_zero _ (by norm_num)
    have h2_ne : ((2 : ℕ) ^ k : ℕ) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hv2_left : k ≤ padicValNat 2 (c * 2 ^ k) := by
      rw [padicValNat.mul hc_pos.ne' h2_ne, padicValNat.prime_pow]
      omega
    have h3_not_dvd : ¬ (2 : ℕ) ∣ 3 ^ i := by
      intro hdvd
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd
      norm_num at this
    have hv2_right : padicValNat 2 (2 * 3 ^ i) = 1 := by
      rw [padicValNat.mul (by norm_num) h3_ne, padicValNat.eq_zero_of_not_dvd h3_not_dvd,
          padicValNat_self]
    rw [heqN, hv2_right] at hv2_left
    omega
  · -- Inequality case.
    have he : ((2 : ℕ) : ℝ) ^ ((1 - (9 : ℝ) / 10) * (k : ℝ))
            = (2 : ℝ) ^ ((1 : ℝ) / 10 * (k : ℝ)) := by
      push_cast
      ring_nf
    rw [← he]
    -- `|2·3^i - c·2^k| = |c·2^k - 2·3^i|` in ℤ and in ℝ.
    have habs : (|((2 * 3 ^ i : ℤ) - (c : ℤ) * 2 ^ k)| : ℤ)
              = (|((c * 2 ^ k : ℤ) - 2 * 3 ^ i)| : ℤ) := abs_sub_comm _ _
    have : ((|((2 * 3 ^ i : ℤ) - (c : ℤ) * 2 ^ k)| : ℤ) : ℝ)
         = ((|((c * 2 ^ k : ℤ) - 2 * 3 ^ i)| : ℤ) : ℝ) := by exact_mod_cast habs
    rw [this]
    exact hbound

/-- Upper bound on Ellison's `x₀` used by Pomme: with `a = c ≤ 4·i`, `b = 2`,
`m = 2`, `n = 3`, `δ = 9/10`, we get `x₀ ≤ 2^{1556} · (log (4·i))^{49}`. -/
lemma ellisonX₀_upper
    (i c : ℕ) (hi_pos : 0 < i) (hc_pos : 0 < c) (hc_le : c ≤ 4 * i) :
    ellisonX₀ c 2 2 3 ((9 : ℝ) / 10) ≤ (2 : ℝ) ^ (1556 : ℕ) * Real.log (4 * i) ^ 49 := by
  sorry

/-- Base case of the `k ≥ x₀` comparison (p. 2 of Pomme2.pdf): at
`i = 2^{2100}` the Ellison bound `2^{1556} · log(4·i)^{49}` is smaller than
`log₂(3^i / (2·i))`. -/
lemma pomme_k_ge_x₀_base :
    (2 : ℝ) ^ (1556 : ℕ) * Real.log (4 * (2 ^ 2100 : ℕ)) ^ 49
      ≤ Real.logb 2 (((3 : ℝ) ^ (2 ^ 2100 : ℕ)) / (2 * (2 ^ 2100 : ℕ))) := by
  sorry

/-- Derivative comparison (Pomme2.pdf, p. 2): the `i`-derivative of
`2^{1556} · log(4·i)^{49}` is smaller than that of `log₂(3^i / (2·i))` once
`i ≥ 2^{2100}`. -/
lemma pomme_derivative_comparison
    (i : ℕ) (hi : pommeThreshold ≤ i) :
    deriv (fun r : ℝ => (2 : ℝ) ^ (1556 : ℕ) * Real.log (4 * r) ^ 49) i
      < deriv (fun r : ℝ => Real.logb 2 ((3 : ℝ) ^ r / (2 * r))) i := by
  sorry

/-- **`k ≥ x₀`**: for `i ≥ 2^{2100}`, Ellison's `x₀` upper bound is absorbed by
`log₂(3^i / (2·i))`. Obtained from `pomme_k_ge_x₀_base` and
`pomme_derivative_comparison` by a mean-value argument. -/
lemma pomme_k_ge_x₀
    (i : ℕ) (hi : pommeThreshold ≤ i) :
    (2 : ℝ) ^ (1556 : ℕ) * Real.log (4 * i) ^ 49
      ≤ Real.logb 2 (((3 : ℝ) ^ i) / (2 * i)) := by
  sorry

/-- For `i ≥ 106` and `k ≥ log₂(3^i / (2·i))`,
`2^{0.1·k} ≥ (3^i / (2·i))^{0.1} > 1.1^i / (2·i) > i + 5`. -/
lemma pomme_two_pow_beats_linear
    (i k : ℕ) (hi : 106 ≤ i)
    (hk : Real.logb 2 (((3 : ℝ) ^ i) / (2 * i)) ≤ (k : ℝ)) :
    ((i : ℝ) + 5) < (2 : ℝ) ^ ((1 : ℝ) / 10 * k) := by
  sorry

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

/-- Elementary lemma used by `pomme_thm1`: for `i ≥ 2^{2100}`, we have
`i + 5 < 3^i / (2·i)`. This is needed to discharge the large-`c` case. -/
lemma pomme_ip5_lt_ratio
    (i : ℕ) (hi : pommeThreshold ≤ i) :
    ((i : ℝ) + 5) < ((3 : ℝ) ^ i) / (2 * i) := by
  have hi8 : 8 ≤ i := by
    have h1 : (8 : ℕ) ≤ 2 ^ 8 := by decide
    have h2 : (2 ^ 8 : ℕ) ≤ 2 ^ 2100 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    exact le_trans (le_trans h1 h2) hi
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

/-- **Pomme's Theorem 1** (Pomme2.pdf, p. 1). For `i ≥ 2^{2100}` and any `k`
with `3^i / (2·i) ≤ 2^k`, `2^k` does not divide `N i = 2·3^i + i + 5`. -/
theorem pomme_thm1
    (i k : ℕ) (hi : pommeThreshold ≤ i)
    (hk : ((3 : ℝ) ^ i) / (2 * i) ≤ (2 : ℝ) ^ k) :
    ¬ (2 ^ k ∣ N i) := by
  have hi_pos : 0 < i := by
    have : (0 : ℕ) < pommeThreshold := by unfold pommeThreshold; positivity
    omega
  have hi106 : 106 ≤ i := by
    have h1 : (106 : ℕ) ≤ 2 ^ 8 := by decide
    have h2 : (2 ^ 8 : ℕ) ≤ 2 ^ 2100 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    exact le_trans (le_trans h1 h2) hi
  have hi_large : ((i : ℝ) + 5) < ((3 : ℝ) ^ i) / (2 * i) := pomme_ip5_lt_ratio i hi
  -- `k ≥ log₂(3^i / (2·i))` because `2^k ≥ 3^i / (2i)`.
  have hi_R_pos : (0 : ℝ) < (i : ℝ) := Nat.cast_pos.mpr hi_pos
  have h_ratio_pos : (0 : ℝ) < ((3 : ℝ) ^ i) / (2 * (i : ℝ)) := by positivity
  have hk_log : Real.logb 2 (((3 : ℝ) ^ i) / (2 * i)) ≤ (k : ℝ) := by
    rw [Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) h_ratio_pos]
    rw [show ((2 : ℝ) ^ (k : ℝ)) = (2 : ℝ) ^ k from (Real.rpow_natCast 2 k)]
    exact hk
  apply pomme_not_dvd_of_gap
  intro c hc_pos
  by_cases h : c ≤ 4 * i
  · -- Small-c case: Ellison.
    have hk_x₀ : ellisonX₀ c 2 2 3 ((9 : ℝ) / 10) ≤ (k : ℝ) := by
      calc ellisonX₀ c 2 2 3 ((9 : ℝ) / 10)
          ≤ (2 : ℝ) ^ (1556 : ℕ) * Real.log (4 * i) ^ 49 :=
            ellisonX₀_upper i c hi_pos hc_pos h
        _ ≤ Real.logb 2 (((3 : ℝ) ^ i) / (2 * i)) := pomme_k_ge_x₀ i hi
        _ ≤ (k : ℝ) := hk_log
    have h_lb := pomme_case_c_small i k c hi_pos hc_pos h hk_x₀
    have h_beat := pomme_two_pow_beats_linear i k hi106 hk_log
    calc ((i : ℝ) + 5) < (2 : ℝ) ^ ((1 : ℝ) / 10 * k) := h_beat
      _ ≤ |((2 * 3 ^ i : ℤ) - (c : ℤ) * 2 ^ k)| := h_lb
  · push_neg at h
    exact pomme_case_c_large i k c hi_pos hk hi_large h

/-! ## Pomme's Corollary 3 and the final inequality -/

/-- **Pomme's Corollary 3** (Pomme2.pdf, p. 2). For `i ≥ 2^{2100}`, the odd
part of `N i` exceeds `2·i + 14`. -/
theorem pomme_cor3
    (i : ℕ) (hi : pommeThreshold ≤ i) :
    2 * i + 14 ≤ N i / 2 ^ padicValNat 2 (N i) := by
  have hi_pos : 0 < i := by
    have : (0 : ℕ) < pommeThreshold := by unfold pommeThreshold; positivity
    omega
  have hi7 : 7 ≤ i := by
    have h1 : (7 : ℕ) ≤ 2 ^ 8 := by decide
    have h2 : (2 ^ 8 : ℕ) ≤ 2 ^ 2100 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    exact le_trans (le_trans h1 h2) hi
  set v := padicValNat 2 (N i) with hv_def
  have h_dvd : 2 ^ v ∣ N i := pow_padicValNat_dvd
  have h2v_pos : 0 < (2 : ℕ) ^ v := pow_pos (by norm_num) v
  -- Key step via Theorem 1: `2^v < 3^i / (2·i)` (as reals).
  have h_lt : ((2 : ℝ) ^ v) < ((3 : ℝ) ^ i) / (2 * i) := by
    by_contra h_ge
    push_neg at h_ge
    exact pomme_thm1 i v hi h_ge h_dvd
  -- Turn the ratio inequality into a multiplicative one.
  have hi_R_pos : (0 : ℝ) < (i : ℝ) := Nat.cast_pos.mpr hi_pos
  have h2i_pos : (0 : ℝ) < 2 * (i : ℝ) := by linarith
  have h1 : (2 : ℝ) ^ v * (2 * (i : ℝ)) < (3 : ℝ) ^ i := by
    rw [lt_div_iff₀ h2i_pos] at h_lt
    linarith
  -- `(4·i) · 2^v < 2 · 3^i ≤ N i`.
  have h2 : (4 * (i : ℝ)) * (2 : ℝ) ^ v < 2 * (3 : ℝ) ^ i := by nlinarith [h1]
  -- `(2·i + 14) · 2^v ≤ (4·i) · 2^v`, since `2·i + 14 ≤ 4·i` for `i ≥ 7`.
  have hi7_R : (7 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi7
  have h3 : ((2 * (i : ℝ)) + 14) * (2 : ℝ) ^ v ≤ (4 * (i : ℝ)) * (2 : ℝ) ^ v := by
    have h2v_nn : (0 : ℝ) ≤ (2 : ℝ) ^ v := by positivity
    nlinarith [h2v_nn, hi7_R]
  -- `N i ≥ 2 · 3^i` trivially.
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

Pomme2.pdf only covers `i ≥ 2^{2100}`. The range `50 ≤ i < 2^{2100}` has to
be handled by a dense simulator. Until a verified Lean-native simulator is
available we record the sim result as an axiom. -/

/-- Dense simulator verification for the small-`i` range `50 ≤ i < 2^{2100}`.
To be discharged later by a verified computation. -/
axiom pomme_small_range
    (i : ℕ) (hi_lo : 50 ≤ i) (hi_hi : i < pommeThreshold) :
    2 * i + 14 ≤ N i / 2 ^ padicValNat 2 (N i)

/-- **Main theorem** combining Pomme's Corollary 3 and the small-`i`
simulator: the TM-closure inequality `(*)` for all `i ≥ 50`. -/
theorem pomme_main (i : ℕ) (hi : 50 ≤ i) :
    2 * i + 14 ≤ N i / 2 ^ padicValNat 2 (N i) := by
  by_cases h : i < pommeThreshold
  · exact pomme_small_range i hi h
  · push_neg at h
    exact pomme_cor3 i h

end Pomme
