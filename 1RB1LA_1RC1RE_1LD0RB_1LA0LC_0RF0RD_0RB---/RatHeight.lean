import BakerWustholz
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

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

/-- Specialization: `logHeight₁ (2 : ℚ) = log 2`. -/
@[simp] theorem logHeight₁_two : Height.logHeight₁ (2 : ℚ) = Real.log 2 := by
  sorry

/-- Specialization: `logHeight₁ (3 : ℚ) = log 3`. -/
@[simp] theorem logHeight₁_three : Height.logHeight₁ (3 : ℚ) = Real.log 3 := by
  sorry

/-- Specialization: `logHeight₁ ((n : ℕ) : ℚ) = log n` for `1 ≤ n`. -/
theorem logHeight₁_natCast (n : ℕ) (hn : 1 ≤ n) :
    Height.logHeight₁ ((n : ℚ)) = Real.log n := by
  sorry

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
  sorry

/-- **`modifiedHeight φ (2 : ℚ) = 1`** (since `log 2 < 1`). -/
@[simp] theorem modifiedHeight_two :
    BakerWustholz.modifiedHeight (algebraMap ℚ ℂ) (2 : ℚ) = 1 := by
  sorry

/-- **`modifiedHeight φ (3 : ℚ) = log 3`** (since `log 3 > 1`). -/
@[simp] theorem modifiedHeight_three :
    BakerWustholz.modifiedHeight (algebraMap ℚ ℂ) (3 : ℚ) = Real.log 3 := by
  sorry

/-- **Upper bound on `modifiedHeight φ ((c : ℚ))`** for `c : ℕ` with `c ≥ 1`:
`max(log c, 1)`. This is tight for `c ≥ 3` (where `log c > 1`) and
`c ∈ {1, 2}` (where it equals `1`). -/
theorem modifiedHeight_natCast_le (c : ℕ) (hc : 0 < c) :
    BakerWustholz.modifiedHeight (algebraMap ℚ ℂ) ((c : ℚ))
      ≤ max (Real.log c) 1 := by
  sorry

end BakerWustholz
