import Baker
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-! ## Ellison's Corollary 1

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
  -- `φ` fixes ℚ: its value on any `(q : K)` (for `q : ℚ`) is `(q : ℂ)`.
  have hφ_rat : ∀ q : ℚ, φ ((q : K)) = (q : ℂ) := by
    intro q
    show NumberField.ComplexEmbedding.lift K (algebraMap ℚ ℂ) (algebraMap ℚ K q) = _
    rw [NumberField.ComplexEmbedding.lift_algebraMap_apply]
    rfl
  have hφ0 : φ (α 0) = (m : ℂ) := by
    show φ ((m : K)) = _
    rw [show ((m : K)) = (((m : ℚ)) : K) from by push_cast; rfl, hφ_rat]
    push_cast; rfl
  have hφ1 : φ (α 1) = (n : ℂ) := by
    show φ ((n : K)) = _
    rw [show ((n : K)) = (((n : ℚ)) : K) from by push_cast; rfl, hφ_rat]
    push_cast; rfl
  have hφ2 : φ (α 2) = ((a : ℂ) / (b : ℂ)) := by
    show φ ((((a : ℚ)) : K) / (((b : ℚ)) : K)) = _
    rw [map_div₀, hφ_rat, hφ_rat]
    push_cast; rfl
  -- Each value is a positive real.
  have hm_R_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
  have hn_R_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have ha_R_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hb_R_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have habR_pos : (0 : ℝ) < (a : ℝ) / b := div_pos ha_R_pos hb_R_pos
  -- Real-valued linear form: `Λ_R := x · log m − y · log n + log(a/b)`.
  set Λ_R : ℝ := (x : ℝ) * Real.log m - (y : ℝ) * Real.log n + Real.log ((a : ℝ) / b) with hΛ_R_def
  -- The complex log sum equals the real linear form coerced to ℂ.
  -- Each `φ (α i)` is a positive real, so `Complex.log` reduces to `Real.log`
  -- and the sum becomes `x·log m − y·log n + log(a/b) = Λ_R`.
  have hsum_eq :
      (∑ i, (bvec i : ℂ) * Complex.log (φ (α i))) = (Λ_R : ℂ) := by
    sorry
  -- Ellison's Lemma 1 (p. 12-02): from `h_small`, derive smallness of the log sum.
  -- Chain: |Λ_R| ≤ 2·|a·m^x − b·n^y|/(b·n^y) ≤ 2·m^{(1−δ)x}/(b·n^y) < exp(−δH).
  have hΛ_small : ‖∑ i, (bvec i : ℂ) * Complex.log (φ (α i))‖ < Real.exp (-(δ * (H : ℝ))) := by
    sorry
  -- Positivity: follows from `Λ_R ≠ 0`, which holds because `a·m^x ≠ b·n^y`.
  have hΛ_R_ne_zero : Λ_R ≠ 0 := by
    intro hzero
    rw [hΛ_R_def] at hzero
    -- `x log m − y log n + log(a/b) = 0` ⇒ `log(a·m^x) = log(b·n^y)` ⇒ `a·m^x = b·n^y`.
    have hax_pos : (0 : ℝ) < (a : ℝ) * (m : ℝ) ^ x := by positivity
    have hby_pos : (0 : ℝ) < (b : ℝ) * (n : ℝ) ^ y := by positivity
    have h_log_eq : Real.log ((a : ℝ) * m ^ x) = Real.log ((b : ℝ) * n ^ y) := by
      rw [Real.log_mul ha_R_pos.ne' (by positivity : ((m : ℝ)) ^ x ≠ 0),
          Real.log_mul hb_R_pos.ne' (by positivity : ((n : ℝ)) ^ y ≠ 0),
          Real.log_pow, Real.log_pow,
          Real.log_div ha_R_pos.ne' hb_R_pos.ne'] at *
      linarith
    have h_am_bn : (a : ℝ) * m ^ x = (b : ℝ) * n ^ y :=
      Real.log_injOn_pos (Set.mem_Ioi.mpr hax_pos) (Set.mem_Ioi.mpr hby_pos) h_log_eq
    apply heq
    have h_int : ((a * m ^ x : ℤ) : ℝ) = ((b * n ^ y : ℤ) : ℝ) := by push_cast; exact h_am_bn
    exact_mod_cast h_int
  have hΛ_pos : (0 : ℝ) < ‖∑ i, (bvec i : ℂ) * Complex.log (φ (α i))‖ := by
    rw [hsum_eq]
    simp only [Complex.norm_real]
    exact abs_pos.mpr hΛ_R_ne_zero
  -- Invoke Baker via the helper.
  have h_baker :=
    baker_helper_degree4 α hα A hA hH_α bvec H hH_b δ hδ_pos (le_of_lt hδ_lt_1) φ
      hΛ_pos hΛ_small
  -- Final contradiction: Baker's bound on `H` is smaller than `ellisonX₀ a b m n δ ≤ x ≤ H`,
  -- because `4^{15} < 2^{31}` (the only nontrivial constant comparison).
  exact absurd h_baker (by sorry)
