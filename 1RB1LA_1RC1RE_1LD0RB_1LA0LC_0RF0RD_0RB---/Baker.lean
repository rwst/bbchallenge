import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Baker's theorem on linear forms in logarithms (axiomatized)

Reference: A. Baker, *Linear forms in the logarithms of algebraic numbers*,
Mathematika (1966–68); quoted as Lemma 2 of
W. J. Ellison, *On a theorem of S. Sivasankaranarayana Pillai*,
Séminaire de théorie des nombres de Bordeaux (1970-71), exposé n° 12, p. 12-03.

This file states the effective form of Baker's theorem as an axiom, so that
downstream developments (Ellison's Corollary 1 — Pillai-type lower bounds on
`|a · m^x − b · n^y|` — and the proof in `Pomme2.pdf` of the Turing machine
holdout `1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---`) can proceed without
depending on a formal proof of Baker, which is not currently in mathlib.
-/

open Complex

/-- **Baker's theorem on linear forms in logarithms**, effective form.

Let `α₁, …, αₙ` be nonzero elements of a number field `K` of degree `d ≥ 4`
embedded into `ℂ` via `φ`. Suppose each `αᵢ` has classical (= normalized Weil)
height at most `A ≥ 4`; since mathlib's `Height.mulHeight₁` is the
**un-normalized** product-over-places height, this is expressed as the
hypothesis `mulHeight₁ (αᵢ) ≤ A ^ d`. (For a rational `q = a/b` lifted to `K`,
this gives `(max |a| b) ^ d`, as expected.) Let `log (φ (αᵢ))` denote the
principal value of the complex logarithm. Let `0 < δ ≤ 1`. If there exist
rational integers `b₁, …, bₙ`, of absolute value at most `H`, such that the
linear form `Λ := ∑ bᵢ · log (φ (αᵢ))` satisfies `0 < |Λ| < exp (−δ · H)`, then
`H ≤ (4 ^ (n²) · δ⁻¹ · d ^ (2n) · log A) ^ ((2n + 1)²)`
(exactly Ellison's Lemma 2 bound, with `A` now meaning the classical Weil
height). -/
axiom baker_linearForms_logs
    {n : ℕ}
    {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ)
    (hd : 4 ≤ Module.finrank ℚ K)
    (α : Fin n → K) (hα : ∀ i, α i ≠ 0)
    {A : ℝ} (hA : 4 ≤ A)
    (hH_α : ∀ i, Height.mulHeight₁ (α i) ≤ A ^ Module.finrank ℚ K)
    (b : Fin n → ℤ) {H : ℕ} (hH_b : ∀ i, (b i).natAbs ≤ H)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (hΛ_pos   : 0 < ‖∑ i, (b i : ℂ) * Complex.log (φ (α i))‖)
    (hΛ_small :     ‖∑ i, (b i : ℂ) * Complex.log (φ (α i))‖
                  < Real.exp (-(δ * (H : ℝ)))) :
    (H : ℝ) ≤
      (4 ^ (n ^ 2) * δ⁻¹ *
        (Module.finrank ℚ K : ℝ) ^ (2 * n) * Real.log A) ^ ((2 * n + 1) ^ 2)
