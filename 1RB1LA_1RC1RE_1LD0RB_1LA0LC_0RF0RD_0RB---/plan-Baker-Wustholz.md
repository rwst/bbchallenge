# Plan: Prove Pomme's theorem via Baker–Wüstholz (1993)

## Context

The current proof in `Ellison.lean` / `Pomme.lean` axiomatizes **Baker's
original 1966-68 form** (as quoted in Ellison's 1970-71 paper, Lemma 2):

```
H ≤ (4^{n²} · δ⁻¹ · d^{2n} · log A)^{(2n+1)²}
```

with outer exponent `(2n+1)² = 49` for `n = 3`. Because this exponent is so
large, Pomme's theorem inherits an **astronomical threshold** `i ≥ 2^{2100}`
(≈10^{632}), and the proof requires an intricate derivative-extension
argument to carry the bound from a base point up to arbitrary `i`.

**Baker–Wüstholz (1993)** is a strictly sharper effective bound on linear
forms in logs: the outer exponent on `log B` is essentially **1**, not
`(2n+1)²`. The cost is a more complex explicit constant involving the
modified height `h'(α) := max(h(α), π/d, 1/d)` and numerics like
`C(n,d) = 18 · (n+1)! · n^{n+1} · (32d)^{n+2} · log(2nd)`.

This document plans a reformulation of Pomme's theorem that uses
Baker–Wüstholz as the axiomatic input, expected to lower the threshold
and collapse several layers of the current proof.

## Answers to the three questions

### 1. Will it require a verified program for computation?

**Yes, still required, but over a vastly smaller range.** For Pomme's
setup `(n, d) = (3, 4)`, the Baker–Wüstholz constant is
`C(3, 4) = 18 · 4! · 3^4 · 128^5 · log 24 ≈ 3.8 · 10^{12}`. Plugging this
into the natural specialization and running the same kind of threshold
derivation as Pomme yields a threshold on `i` of roughly **`10^{15}`**,
compared to `2^{2100} ≈ 10^{632}` in the current approach.

A dense simulator covering `50 ≤ i < 10^{15}` is feasible in a few
CPU-hours with GMP and the "i += 2^k jump" heuristic, and the result can
(in principle) be reflected into Lean as an interval-based check — e.g.,
by partitioning the interval into chunks and running `native_decide` on
each, or by using a `decide`-friendly encoding with a verified checker.
Covering up to `10^{632}` is physically impossible. The net effect is
that the "small-i axiom" (`pomme_small_range`) remains, but it becomes
something one could plausibly eliminate later, whereas with the
Ellison-form Baker it is permanent.

### 2. Will it likely make the chain shorter?

**Yes, moderately.** The current sorry landscape in the Pomme side:

| Sorry | Fate under Baker–Wüstholz |
|---|---|
| `ellisonX₀_upper` | **Gone.** No `x₀` formula in the Ellison style. |
| `pomme_k_ge_x₀_base` | **Gone.** No base case needed. |
| `pomme_derivative_comparison` | **Gone.** No derivative extension. |
| `pomme_k_ge_x₀` | **Gone.** No MVT argument. |
| `pomme_two_pow_beats_linear` | **Simpler.** Just `3^i · B^{-C·Π h'} > i + 5`, direct. |
| `pomme_case_c_small` internal `2 ≤ k` | Still needed but easier. |

On the Ellison side:

| Sorry | Fate under Baker–Wüstholz |
|---|---|
| `hH_α` (heights of rationals in K) | **Same work.** Still need `mulHeight₁ q ≤ A^d`. |
| `hΛ_small` (Ellison Lemma 1 = log Taylor bound) | **Same.** Still the core analytic lemma. |
| Final `absurd` (constant comparison) | **Gone.** Replaced by direct threshold check. |

Net: ~7 Pomme-side calculus/numerical sorries collapse to ~2, Ellison
side stays about the same. Total active proof length drops by an
estimated 30–40%.

### 3. Will it likely make the chain simpler?

**Yes, structurally.** The conceptual dependency chain becomes linear:

```
  Baker–Wüstholz  (axiom, more complex statement)
        ↓
  Log-to-integer translation  (one lemma, Lemma-1 style)
        ↓
  Direct bound |c·2^k − 2·3^i| ≥ 3^i · B^{-C · Π h'(αᵢ)}
        ↓
  Pomme's Cor 3  (plug in, elementary)
        ↓
  pomme_main  (combine with small-i simulator)
```

The current chain has two extra levels:

```
  Baker (Ellison's form)
        ↓
  Ellison's Lemma 1  (analytic)          ┐
        ↓                                │ Baker–Wüstholz absorbs all of this
  Ellison's Theorem 1 (skipped/sorry'd)  │
        ↓                                │
  Ellison's Cor 1                        ┘
        ↓
  Pomme Thm 1: requires derivative extension from i = 2^{2100}
        ↓
  Pomme Cor 3
        ↓
  pomme_main
```

Notably, the **derivative trick disappears**: it's currently needed
because the Ellison-form bound is just barely tight, and only the
derivative comparison shows it stays tight across the whole range.
Baker–Wüstholz is tight enough out of the box.

**Downside**: the axiom statement is more intricate. It involves the
modified logarithmic height `h'(α) = max(h(α), π/d, 1/d)` and the
explicit constant `C(n,d)`. This is a one-time cost in the axiom file,
not spread across the proof.

## The axiom statement

```lean
-- BakerWustholz.lean
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Analysis.SpecialFunctions.Complex.Log

open Complex

/-- **Baker–Wüstholz theorem on linear forms in logarithms** (Baker–Wüstholz
1993, *A refinement of the Baker–Feldman theorem*).

Let `α₁, …, αₙ` (`n ≥ 1`) be nonzero elements of a number field `K` of
degree `d ≥ 1`, embedded in `ℂ` via `φ`. Let `b₁, …, bₙ` be rational
integers, not all zero, with `B := max(|bᵢ|, 2)`. If the linear form
`Λ := ∑ bᵢ · log (φ (αᵢ))` is nonzero, then
```
  `log |Λ| ≥ − C(n, d) · log B · ∏ᵢ h'(αᵢ)`
```
where
- `h(α) := Height.logHeight₁ α / d` is the **normalized logarithmic Weil
  height** (field-independent);
- `h'(α) := max(h(α), π/d, 1/d)` is the **modified height**;
- `C(n,d) := 18 · (n+1)! · n^{n+1} · (32d)^{n+2} · log(2nd)` is the
  Baker–Wüstholz constant.

Equivalently (exponentiating),
```
  `|Λ| ≥ B^{−C(n,d) · ∏ᵢ h'(αᵢ)}`.
```
-/
axiom bakerWustholz_linearForms_logs
    {n : ℕ} (hn : 0 < n)
    {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ)
    (α : Fin n → K) (hα : ∀ i, α i ≠ 0)
    (b : Fin n → ℤ)
    (hΛ_ne_zero : (∑ i, (b i : ℂ) * Complex.log (φ (α i))) ≠ 0) :
    let d : ℕ := Module.finrank ℚ K
    let B : ℝ := max ((Finset.univ.image (fun i ↦ (b i).natAbs)).sup' ⟨0, by
      simp [Finset.univ_nonempty_iff, hn]⟩ id : ℕ) 2
    let hMod : Fin n → ℝ := fun i ↦
      max (Height.logHeight₁ (α i) / d) (max (Real.pi / d) (1 / d))
    let C : ℝ := 18 * (n + 1).factorial * (n : ℝ) ^ (n + 1) *
      (32 * d : ℝ) ^ (n + 2) * Real.log (2 * n * d)
    Real.log ‖∑ i, (b i : ℂ) * Complex.log (φ (α i))‖
      ≥ -(C * Real.log B * ∏ i, hMod i)
```

Notes on the statement:
- Uses mathlib's `Height.logHeight₁` (un-normalized, scales as `d · h`);
  we divide by `d` to recover the classical normalized `h`.
- `B` is clamped to 2 so that `log B > 0` (Baker–Wüstholz requires `B ≥ 2`
  to make the bound well-defined).
- The `0 < n` hypothesis is needed for the sup' over `Fin n`.
- Takes the **complex log** (principal value) via a chosen embedding
  `φ : K → ℂ`, consistent with our existing `Baker.lean` convention.

## Specialization to Pillai

For Pomme's use, we instantiate with:
- `K := CyclotomicField 5 ℚ`  (degree `d = 4`)
- `n := 3`
- `α := ![(2 : K), (3 : K), ((c : K) / 2)]`  (or equivalently `![2, 3, c/2]`)
- `b := ![(k − 1 : ℤ), −i, 1]` from rewriting `log((c·2^k)/(2·3^i))`
- `B ≈ max(k − 1, i, 2)`

Heights:
- `h(2) = log 2 ≈ 0.693`; `h'(2) = max(log 2, π/4, 1/4) = π/4 ≈ 0.785`.
- `h(3) = log 3 ≈ 1.099`; `h'(3) = log 3`.
- `h(c/2) ≤ log(max(c, 2)) ≤ log(4i)` for `c ≤ 4i`.
- Product `∏ h'(αᵢ) ≤ (π/4) · log 3 · log(4i) ≈ 0.863 · log(4i)`.

Constant:
- `C(3, 4) = 18 · 24 · 81 · 128^5 · log 24 ≈ 3.8 · 10^{12}`.

Resulting bound:
- `log|Λ| ≥ −C · log(max(k, i, 2)) · 0.863 · log(4i)`
- Since `k ≈ i · log₂ 3 + O(log i) = O(i)`, `log(max(k,i)) = O(log i)`.
- So `log|Λ| ≥ −C' · (log i)^2` for some `C' ≈ 3.3 · 10^{12}`.
- `|Λ| ≥ exp(−C' · (log i)^2) = i^{−C' · log i}`.

Via Lemma-1-style translation:
- `|c·2^k − 2·3^i| ≥ 2·3^i · |Λ| / 2 ≥ 3^i · i^{−C' · log i}`
  (the factor `1/2` comes from the Taylor bound).
- We want this `> i + 5`.
- Equivalently, `i · log 3 > log(i + 5) + C' · (log i)^2`.
- For `i ≥ 10^{15}`, LHS ≈ `1.099 i ≈ 10^{15}`, RHS ≈ `C' · (log 10^{15})^2 ≈ 3.3·10^{12} · 1194 ≈ 4·10^{15}`.

Hmm, that's too tight. Let me redo with `i ≥ 10^{16}`: LHS ≈ `1.1·10^{16}`,
RHS ≈ `3.3·10^{12} · (16 · log 10)^2 ≈ 3.3·10^{12} · 1355 ≈ 4.5·10^{15}`.
Still close. At `i = 10^{17}`: LHS ≈ `1.1·10^{17}`, RHS ≈ `5·10^{15}`.
Now LHS >> RHS. **So the Baker–Wüstholz threshold for Pomme is
approximately `i ≥ 10^{17}`**, not `10^{15}` as I first guessed. Still
a massive reduction from `10^{632}`.

## File plan

### New files

- **`BakerWustholz.lean`** (~70 lines) — axiomatize Baker–Wüstholz with
  the statement above. Uses mathlib's `Height.logHeight₁` plus
  `NumberField`, `Complex.log`. Documents the specific form and
  references the original 1993 paper.

### Modified files

- **`Ellison.lean`** — renamed/restructured as `BakerWustholzHelpers.lean`
  (or kept with Ellison's name for continuity):
  - Delete `ellisonX₀`, `baker_helper_degree4`, `ellison_cor1`.
  - Add `bakerWustholz_helper_degree4` — specialization to
    `CyclotomicField 5 ℚ` with `n = 3` logarithms.
  - Add `log_bound_to_integer_bound` (Lemma-1-style translation):
    given `|a·m^x − b·n^y| = c` and appropriate size conditions, derive
    `|Λ| ≤ 2c / (b·n^y)`. **This is the only analytic lemma needed.**
  - Add `direct_pillai_bound` (replaces `ellison_cor1`): for
    `i ≥ threshold`, `|c·2^k − 2·3^i| > i + 5` directly from
    `bakerWustholz_helper_degree4` + `log_bound_to_integer_bound`.
  - Retained Pomme helpers: `N`, `N_odd_iff_even`, `pomme_even_case`,
    `pomme_not_dvd_of_gap`, `pomme_case_c_large`, etc.

- **`Pomme.lean`**:
  - Delete `ellisonX₀_upper`, `pomme_k_ge_x₀_base`,
    `pomme_derivative_comparison`, `pomme_k_ge_x₀`,
    `pomme_two_pow_beats_linear`.
  - Simplify `pomme_thm1` to directly invoke `direct_pillai_bound`.
  - Update `pommeThreshold` to the new (smaller) value
    (e.g. `10^{17}`, or whatever the actual bound works out to).
  - Keep `pomme_small_range` axiom (still needed; just over a smaller
    interval now).
  - Keep `pomme_cor3`, `pomme_main` unchanged.

### Unchanged files

- `Pomme.Nat` helpers (`two_i_sq_plus_ten_i_lt_three_pow`, etc.).

## Step-by-step implementation

1. **Write `BakerWustholz.lean`** with the axiom statement. Test
   compiles. (~30 min of Lean typing + mathlib search for
   `logHeight₁`, `Finset.sup'`, etc.)

2. **Duplicate `Ellison.lean` → `Ellison.lean.old`**, start fresh.
   Reuse the existing sorry-free parts (`N`, `N_odd_iff_even`,
   `pomme_even_case`, `pomme_not_dvd_of_gap`, `pomme_case_c_large`,
   `hsum_eq`, `hΛ_R_ne_zero`, `hΛ_pos`, the number-field plumbing:
   `hφ_rat`, `hφ0`, `hφ1`, `hφ2`, `hα`, `hH_b`).

3. **Prove `bakerWustholz_helper_degree4`**, sorry-free, mirroring
   `baker_helper_degree4`. Should be ~20 lines — discharges
   `0 < 3`, `hd = Nat.totient 5 = 4`, and passes through.

4. **Prove `log_bound_to_integer_bound`** (Lemma 1). This is the only
   analytic work needed. Mathlib provides `Real.abs_log_one_add_le`
   and `Complex.log_one_add_of_norm_lt_half`. ~40–60 lines.

5. **Prove `direct_pillai_bound`**: combine steps 3 and 4, pick the
   threshold concretely.
   - Apply `bakerWustholz_helper_degree4`.
   - Apply `log_bound_to_integer_bound`.
   - Do the arithmetic: `3^i · i^{−C'·log i} > i + 5` for
     `i ≥ threshold`.
   - The threshold emerges from the numerical constants.
   - Use an explicit threshold like `2^{60}` or `10^{17}` chosen to
     leave comfortable slack.

6. **Update `Pomme.lean`**:
   - Replace `pommeThreshold := 2^{2100}` with the new value.
   - Delete the five dead calculus lemmas.
   - Rewrite `pomme_thm1` to call `direct_pillai_bound` instead of
     `ellison_cor1 + pomme_case_c_small`.
   - Verify `pomme_cor3` and `pomme_main` still go through.

7. **Verify end-to-end**: `lake build Pillai`, `#print axioms
   Pomme.pomme_main` should now show
   `bakerWustholz_linearForms_logs` + `pomme_small_range` +
   standard axioms.

## Open risks

1. **Numerical threshold**: need to actually compute the constants and
   verify `10^{17}` (or whichever) really works. The first-pass
   back-of-envelope above suggests yes, but with not a lot of slack.
   May need threshold `10^{20}` or similar to be safe.

2. **Height normalization**: mathlib's `logHeight₁` is un-normalized.
   Need to divide by `d` carefully inside the axiom statement to get
   the classical `h`. Easy but fiddly.

3. **Modified height `h'`**: involves `Real.pi`, a transcendental.
   Using it inside the axiom means the axiom's conclusion references
   `Real.pi`, which is fine but makes `norm_num` harder.

4. **Simulator interface**: `pomme_small_range` over `[50, 10^{17})` is
   still non-trivial to discharge. If we want to eventually eliminate
   it, we'd need a Lean-native verified arithmetic check (maybe
   `native_decide` on chunks, or reflection on a Go/C++ verifier).

5. **Axiom verification**: Baker–Wüstholz is a named and standard
   result, so the axiom is as credible as any external-citation
   axiom. But the specific constant `C(n,d)` should be double-checked
   against the paper.

## Comparison summary

| Aspect | Current (Baker via Ellison) | Proposed (Baker–Wüstholz) |
|---|---|---|
| Threshold on `i` | `10^{632}` | `~10^{17}` |
| Verified simulator | Infeasible | Feasible in CPU-hours |
| Pomme.lean calculus sorries | 5 | 0 |
| Ellison.lean sorries | 3 | 2 (`hH_α`, Lemma 1) |
| Analytic chain depth | 5 levels | 3 levels |
| Derivative trick needed | Yes | No |
| Constant comparison needed | Yes (and fragile) | No |
| Axiom statement size | ~30 lines | ~70 lines |
| Axiom complexity | Moderate | High (modified height, factorial constants) |
| Mathematical credibility | Standard (Baker 1966) | Standard (BW 1993) |

## Recommendation

**Worth doing.** The proof structure becomes substantially cleaner and,
more importantly, the verification threshold drops from physically
impossible to computationally feasible. The one-time cost of writing a
more intricate axiom statement is outweighed by eliminating the
derivative-extension machinery and making the whole approach potentially
sorry-free in the limit.

The ONLY reason not to do this would be if formalizing the modified
height `h'` with `Real.pi` causes unexpected `norm_num` / `decide`
difficulties. This is a low risk — `Real.pi` is well-supported in
mathlib.

## Next steps

1. Double-check the threshold computation (honest estimate of `C(3,4)`
   and the resulting critical `i`).
2. Write `BakerWustholz.lean` as described.
3. Incrementally port `Ellison.lean` → new `direct_pillai_bound`.
4. Simplify `Pomme.lean`.
5. Retire the old `Baker.lean` + `ellison_cor1` once the new chain
   passes `lake build`.
