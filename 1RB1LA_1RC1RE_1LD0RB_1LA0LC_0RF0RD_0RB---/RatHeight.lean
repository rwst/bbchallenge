import BakerWustholz
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean

/-!
# Weil height of rational numbers (sorried helper file)

This file is a **provisional replacement** for a target mathlib PR that
would bridge Ostrowski's theorem (already in
`Mathlib.NumberTheory.Ostrowski`) to the `NumberField.FinitePlace`
infrastructure used by `Mathlib.NumberTheory.Height.NumberField` — see
`plan-Baker-Wustholz.md` for the PR sketch.

Concretely, mathlib (as of this project's pin) has:

* `Rat.infinitePlace : InfinitePlace ℚ` and `instance : Unique (InfinitePlace ℚ)`
  in `Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean`, plus
  `Rat.infinitePlace_apply v x = |x|`.
* The general product-over-places formula `NumberField.Height.mulHeight₁_eq`
  for any number field `K`.
* `Rat.AbsoluteValue.equiv_real_or_padic` (Ostrowski) in
  `Mathlib/NumberTheory/Ostrowski.lean`.

But **no** `FinitePlace ℚ` enumeration, no
`Rat.finitePlaceEquivPrime`, no closed-form height on `ℚ`. This file
provides the height formula directly as sorried theorems, so that
`Ellison.lean` can discharge `pillai_baker_rhs_upper_bound` without
waiting on the mathlib PR.

## Content

* `Rat.mulHeight₁_eq` — multiplicative Weil height of `q : ℚ` equals
  `max(|q.num|, q.den)`.
* `Rat.logHeight₁_eq` — log variant.
* Specializations to `BakerWustholz.modifiedHeight` at `(2 : ℚ)`,
  `(3 : ℚ)`, and `((c : ℕ) : ℚ)`, with numerical bounds used by
  `pillai_baker_rhs_upper_bound`.

## Removal plan

Once the mathlib PR lands (see `plan-Baker-Wustholz.md` for the outline),
this file can be deleted and the downstream `pillai_baker_rhs_upper_bound`
reverted to use the mathlib-standard names. The axiom chain of
`pomme_main` will automatically drop the `sorryAx` corresponding to the
lemmas below.
-/

open Real Complex

namespace Rat

/-- **Weil height of a rational number** (mathlib gap, classical formula).

For `q ∈ ℚ`, the multiplicative Weil height `Height.mulHeight₁ q` equals
`max(|q.num|, q.den)` (in lowest terms), the classical "naive height"
of the coprime numerator-denominator representation.

**Proof (for the mathlib PR)**: unfold `NumberField.Height.mulHeight₁_eq`
for `K = ℚ`. The archimedean contribution is `max(|q|, 1)`, where `|q|`
is the standard absolute value, via `Rat.infinitePlace_apply`. The finite
contribution `∏ᶠ v : FinitePlace ℚ, max(v q, 1)` equals `q.den`, via a
prime-by-prime computation of `p`-adic valuations (which requires
`Rat.finitePlaceEquivPrimes` or an equivalent bridge to
`Rat.AbsoluteValue.padic`). Combining: `mulHeight₁ q = max(|num|, den)`. -/
theorem mulHeight₁_eq (q : ℚ) :
    Height.mulHeight₁ q = (max q.num.natAbs q.den : ℝ) := by
  sorry

/-- **Logarithmic Weil height of a rational number.** Follows from
`Rat.mulHeight₁_eq` by taking logs. -/
theorem logHeight₁_eq (q : ℚ) :
    Height.logHeight₁ q = Real.log (max q.num.natAbs q.den : ℝ) := by
  sorry

/-- Specialization: `logHeight₁ ((n : ℕ) : ℚ) = log n` for `1 ≤ n`. -/
theorem logHeight₁_natCast (n : ℕ) (hn : 1 ≤ n) :
    Height.logHeight₁ ((n : ℚ)) = Real.log n := by
  rw [Height.logHeight₁_eq_log_mulHeight₁]
  congr 1
  rw [NumberField.mulHeight₁_eq]
  have hfin : ∀ v : NumberField.FinitePlace ℚ, max ((v ((n : ℚ)) : ℝ)) 1 = 1 := by
    intro v
    have hv : IsNonarchimedean (v.1 : AbsoluteValue ℚ ℝ) := NumberField.FinitePlace.add_le v
    have h1 : (v.1 : AbsoluteValue ℚ ℝ) ((n : ℚ)) ≤ 1 :=
      IsNonarchimedean.apply_natCast_le_one_of_isNonarchimedean hv
    show max (v ((n : ℚ))) 1 = 1
    rw [NumberField.FinitePlace.coe_apply]
    exact max_eq_right h1
  rw [show (∏ᶠ v : NumberField.FinitePlace ℚ, max ((v ((n : ℚ)) : ℝ)) 1) = 1 from by
        simp [hfin]]
  rw [mul_one, Fintype.prod_unique]
  have hmult : (default : NumberField.InfinitePlace ℚ).mult = 1 := by
    have hsub : (default : NumberField.InfinitePlace ℚ) = Rat.infinitePlace :=
      Subsingleton.elim _ _
    rw [hsub, NumberField.InfinitePlace.mult, if_pos Rat.isReal_infinitePlace]
  rw [hmult, pow_one, Rat.infinitePlace_apply]
  push_cast
  rw [show |(n : ℝ)| = n from abs_of_nonneg (Nat.cast_nonneg n),
      max_eq_left (by exact_mod_cast hn : (1 : ℝ) ≤ n)]

/-- Specialization: `logHeight₁ (2 : ℚ) = log 2`. -/
@[simp] theorem logHeight₁_two : Height.logHeight₁ (2 : ℚ) = Real.log 2 := by
  have := logHeight₁_natCast 2 (by norm_num)
  simpa using this

/-- Specialization: `logHeight₁ (3 : ℚ) = log 3`. -/
@[simp] theorem logHeight₁_three : Height.logHeight₁ (3 : ℚ) = Real.log 3 := by
  have := logHeight₁_natCast 3 (by norm_num)
  simpa using this

end Rat

/-! ## Specializations to `BakerWustholz.modifiedHeight`

The modified height `max(h, |log α|/d, 1/d)` has simpler form for
`K = ℚ` (where `d = finrank ℚ ℚ = 1`). These lemmas compute (or bound)
its value at the rational arguments used in `pillai_baker_application`. -/

namespace BakerWustholz

/-- For `q : ℚ`, the `modifiedHeight` simplifies because `finrank ℚ ℚ = 1`. -/
theorem modifiedHeight_rat_eq (q : ℚ) :
    BakerWustholz.modifiedHeight (algebraMap ℚ ℂ) q
      = max (Height.logHeight₁ q)
          (max ‖Complex.log ((algebraMap ℚ ℂ) q)‖ 1) := by
  simp [BakerWustholz.modifiedHeight, Module.finrank_self]

/-- **`modifiedHeight φ (2 : ℚ) = 1`** (since `log 2 < 1`). -/
@[simp] theorem modifiedHeight_two :
    BakerWustholz.modifiedHeight (algebraMap ℚ ℂ) (2 : ℚ) = 1 := by
  rw [modifiedHeight_rat_eq, Rat.logHeight₁_two]
  have hφ : (algebraMap ℚ ℂ) (2 : ℚ) = (2 : ℂ) := by norm_cast
  rw [hφ]
  have hlog : Complex.log (2 : ℂ) = ((Real.log 2 : ℝ) : ℂ) := by
    have := (Complex.ofReal_log (by norm_num : (0:ℝ) ≤ 2)).symm
    push_cast at this
    exact this
  rw [hlog, Complex.norm_real,
      Real.norm_of_nonneg (Real.log_nonneg (by norm_num))]
  have hlt : Real.log 2 < 1 :=
    lt_of_lt_of_le Real.log_two_lt_d9 (by norm_num)
  rw [max_eq_right hlt.le, max_eq_right hlt.le]

/-- **`modifiedHeight φ (3 : ℚ) = log 3`** (since `log 3 > 1`). -/
@[simp] theorem modifiedHeight_three :
    BakerWustholz.modifiedHeight (algebraMap ℚ ℂ) (3 : ℚ) = Real.log 3 := by
  rw [modifiedHeight_rat_eq, Rat.logHeight₁_three]
  have hφ : (algebraMap ℚ ℂ) (3 : ℚ) = (3 : ℂ) := by norm_cast
  rw [hφ]
  have hlog : Complex.log (3 : ℂ) = ((Real.log 3 : ℝ) : ℂ) := by
    have := (Complex.ofReal_log (by norm_num : (0:ℝ) ≤ 3)).symm
    push_cast at this
    exact this
  rw [hlog, Complex.norm_real,
      Real.norm_of_nonneg (Real.log_nonneg (by norm_num))]
  have hgt : 1 < Real.log 3 := by
    have h1 : Real.log (Real.exp 1) < Real.log 3 :=
      Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
    rwa [Real.log_exp] at h1
  rw [max_eq_left hgt.le, max_self]

/-- **Upper bound on `modifiedHeight φ ((c : ℚ))`** for `c : ℕ` with `c ≥ 1`:
`max(log c, 1)`. This is tight for `c ≥ 3` (where `log c > 1`) and
`c ∈ {1, 2}` (where it equals `1`). -/
theorem modifiedHeight_natCast_le (c : ℕ) (hc : 0 < c) :
    BakerWustholz.modifiedHeight (algebraMap ℚ ℂ) ((c : ℚ))
      ≤ max (Real.log c) 1 := by
  rw [modifiedHeight_rat_eq, Rat.logHeight₁_natCast c hc]
  have hφ : (algebraMap ℚ ℂ) ((c : ℚ)) = (c : ℂ) := by norm_cast
  rw [hφ]
  have hcpos : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hlog : Complex.log ((c : ℂ)) = ((Real.log c : ℝ) : ℂ) := by
    have h := (Complex.ofReal_log hcpos).symm
    -- h : Complex.log ((c : ℝ) : ℂ) = ((Real.log c : ℝ) : ℂ)
    rw [show ((c : ℂ) : ℂ) = ((c : ℝ) : ℂ) from by push_cast; rfl]
    exact_mod_cast h
  rw [hlog, Complex.norm_real,
      Real.norm_of_nonneg (Real.log_nonneg (by exact_mod_cast hc))]
  -- Goal: max (log c) (max (log c) 1) ≤ max (log c) 1
  rw [← max_assoc, max_self]

end BakerWustholz
