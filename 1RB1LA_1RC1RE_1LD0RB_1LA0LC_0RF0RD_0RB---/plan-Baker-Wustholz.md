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

## Progress log

### Step 1 — ✅ `BakerWustholz.lean` axiomatized

Created the file with:
- `BakerWustholz.C (n d : ℕ) : ℝ` — the constant
  `18 · (n+1)! · n^{n+1} · (32d)^{n+2} · log(2nd)`.
- `BakerWustholz.modifiedHeight (φ : K →+* ℂ) (α : K) : ℝ` — the modified
  height `max(h(α), |log φ(α)|/d, 1/d)` faithful to Baker–Wüstholz 1993.
- `bakerWustholz_linearForms_logs` — the main axiom, with hypotheses
  `0 < n`, `2 ≤ B`, `hbB`, and `hΛ_ne_zero`. Conclusion:
  `log |Λ| ≥ -C(n,d) · log B · ∏ h'(αᵢ)`.

Updated `lakefile.toml` to add `BakerWustholz` as a new root of the
`Pillai` library. `lake build Pillai` passes with only the pre-existing
sorry warnings (in `Pomme.lean`); `BakerWustholz.lean` itself compiles
clean with no errors or warnings.

Notes:
- Used `Height.logHeight₁` from `Mathlib.NumberTheory.Height.NumberField`
  as mathlib's un-normalized logarithmic height, dividing by `d` inside
  `modifiedHeight` to recover the classical `h`.
- The axiom takes `φ : K →+* ℂ` as an explicit ring-hom (matching the
  convention of the older `Baker.lean`), so the "any determination" of
  the logarithm is fixed by the choice of embedding.
- No `Real.pi` needed in the end — the `π/d` term in the modified
  height proposed in the plan was unnecessary; the standard
  Baker–Wüstholz form uses `|log α|/d` instead.

### Step 2–5 — ✅ `Ellison.lean` rewritten around Baker–Wüstholz

Replaced the old Baker-via-Ellison machinery (`ellisonX₀`,
`baker_helper_degree4`, `ellison_cor1`) with three declarations:

1. **`pommeThreshold := 2^60`** — moved from `Pomme.lean` into
   `Ellison.lean` because it's the threshold at which the direct
   Baker–Wüstholz argument becomes effective. Was `2^{2100}` before.
   Includes helper lemmas `pommeThreshold_pos`,
   `pommeThreshold_ge_eight`, `pommeThreshold_ge_106`.

2. **`log_bound_to_integer_bound`** (stated, sorry) — Ellison's Lemma 1
   style: given `|2·3^i − c·2^k| ≤ ε < 3^i`, the linear form
   `(k−1)·log 2 − i·log 3 + log c` has norm at most `2ε/(2·3^i)`.
   ~60–100 lines of real analysis to fill.

3. **`direct_pillai_bound_small`** (stated, sorry) — replaces
   `ellison_cor1 + pomme_case_c_small`. For `i ≥ pommeThreshold`,
   `1 ≤ c ≤ 4i`, `3^i/(2i) ≤ 2^k`, gives `|2·3^i − c·2^k| > i + 5`
   directly via Baker–Wüstholz + Lemma 1.

**Key simplification**: Baker–Wüstholz works with `K = ℚ` directly
(no `d ≥ 4` restriction), so the entire `CyclotomicField 5 ℚ`
infrastructure disappears. No `NumberField.ComplexEmbedding.lift`,
no `IsCyclotomicExtension.finrank`, no `baker_helper_degree4`
specialization. Just apply the axiom with `K := ℚ`.

`Ellison.lean` went from 191 lines to ~85 lines. The old file (before
this rewrite) is available in git history.

Build status: `Ellison.lean` compiles standalone. `Pomme.lean` now
has errors because it still references `ellisonX₀` and
`ellison_cor1` — these are the expected broken references that
Step 6 will fix.

### Step 6 — ✅ `Pomme.lean` simplified around the new threshold

Rewrote `Pomme.lean` around the Baker–Wüstholz direct bound. Changes:

**Deleted** (dead code from the old calculus cluster):
- `pomme_case_c_small` (replaced by `direct_pillai_bound_small`)
- `ellisonX₀_upper`
- `pomme_k_ge_x₀_base`
- `pomme_derivative_comparison`
- `pomme_k_ge_x₀`
- `pomme_two_pow_beats_linear`
- `Pomme.pommeThreshold` (now lives at top level in `Ellison.lean`)

**Kept** (still needed):
- `N`, `N_def`, `N_pos`, `N_odd_iff_even`, `pomme_even_case`
- `pomme_not_dvd_of_gap`
- `pomme_case_c_large` (handles the `c > 4·i` elementary case)
- `two_i_sq_plus_ten_i_lt_three_pow`
- `pomme_ip5_lt_ratio` (rewritten to use `pommeThreshold_ge_eight`)
- `pomme_cor3`, `pomme_small_range`, `pomme_main`

**Simplified**:
- `pomme_thm1` is now a clean 10-line proof:
  ```
  apply pomme_not_dvd_of_gap
  intro c hc_pos
  by_cases h : c ≤ 4 * i
  · exact direct_pillai_bound_small i k c hi hc_pos h hk
  · push_neg at h
    exact pomme_case_c_large i k c hi_pos hk hi_large h
  ```
- `pomme_cor3` uses `pommeThreshold_ge_eight` instead of manually
  deriving `7 ≤ i` from `2^{2100}`.

File sizes:
- `Pomme.lean`: was 398 lines, now 256 lines (-36%).
- `Ellison.lean`: was 191 lines, now 99 lines (-48%).
- Total old (Baker+Ellison+Pomme): ~630 lines.
- Total new (Baker+BakerWustholz+Ellison+Pomme): ~400 lines (-36%).

### Step 7 — ✅ End-to-end build passing

`lake build Pillai` succeeds. The dependency chain as reported by
`#print axioms`:

```
'Pomme.pomme_main' depends on axioms:
  [propext, sorryAx, Classical.choice, Pomme.pomme_small_range, Quot.sound]

'direct_pillai_bound_small' depends on axioms:
  [propext, sorryAx, Classical.choice, Quot.sound]
```

Notes:
- `baker_linearForms_logs` (from the old `Baker.lean`) is no longer
  referenced by Pomme. The old file could be retired.
- `bakerWustholz_linearForms_logs` does not yet appear in the axiom
  set, because `direct_pillai_bound_small` is still a `sorry`
  (its proof hasn't been written yet, so nothing references the
  axiom). Once filled in, it will appear.

### Current sorry inventory

Refined after breaking down `direct_pillai_bound_small` into helpers
so that `bakerWustholz_linearForms_logs` structurally appears in the
proof term (previously the sorry swallowed the axiom reference).

| # | File | Lemma | Role |
|---|---|---|---|
| 1 | `Ellison.lean:72` | `log_bound_to_integer_bound` | Ellison's Lemma 1: Taylor bound `\|log(1+z)\| ≤ 2\|z\|`. Pure real analysis. |
| 2 | `Ellison.lean:93` | `pillai_k_ge_two` | Arithmetic: for `i ≥ 2^60` and `3^i/(2i) ≤ 2^k`, `k ≥ 2`. |
| 3 | `Ellison.lean:102` | `pillai_linear_form_ne_zero` | `(k-1)·log 2 − i·log 3 + log c ≠ 0` when `k ≥ 2` (v₂ argument). |
| 4 | `Ellison.lean:111` | `pillai_baker_application` | **Only** call to `bakerWustholz_linearForms_logs`. Remaining sub-sorries: `hΛ_ne_sum` (lift `ne_zero` from expanded to sum form) and the final rearrangement from sum-form conclusion to expanded-form conclusion. |
| 5 | `Ellison.lean:157` | `pillai_baker_rhs_upper_bound` | Numerical: the RHS `C·log B·∏h'` is `≤ i·log 3 / 2` for `i ≥ 2^60`, `c ≤ 4i`. |
| 6 | `Ellison.lean:184` | `direct_pillai_bound_small` | Combines 1–5 via the chain in the docstring. |

**Axiom verification**:
```
'direct_pillai_bound_small' depends on axioms:
  [bakerWustholz_linearForms_logs, propext, sorryAx, Classical.choice, Quot.sound]

'Pomme.pomme_main' depends on axioms:
  [bakerWustholz_linearForms_logs, propext, sorryAx, Classical.choice,
   Pomme.pomme_small_range, Quot.sound]
```

`bakerWustholz_linearForms_logs` now appears in both axiom sets. The
chain is: `pomme_main → pomme_cor3 → pomme_thm1 → direct_pillai_bound_small
→ pillai_baker_application → bakerWustholz_linearForms_logs`.

**Note** the old `baker_linearForms_logs` is no longer referenced.
`Baker.lean` could now be retired; left in place only to avoid a
late-session breakage.

## Net outcome

Compared to the starting state (Baker-1966 via Ellison):

| Metric | Before | After |
|---|---|---|
| Threshold on `i` | `2^{2100} ≈ 10^{632}` | `2^{60} ≈ 10^{18}` |
| Top-level sorries in Ellison/Pomme | 11 | 6 |
| Load-bearing axiom | `baker_linearForms_logs` (Baker 1966) | `bakerWustholz_linearForms_logs` (Baker–Wüstholz 1993) |
| Number-field complications | CyclotomicField 5 ℚ + finrank plumbing + height computations | K = ℚ throughout |
| Proof chain depth | `Baker → Ellison Lemma 1 → Ellison Thm 1 (skipped) → Ellison Cor 1 → Pomme Thm 1 (derivative trick) → Cor 3 → main` | `BW → log-to-int translation → Pomme Thm 1 → Cor 3 → main` |
| `Pomme.lean` size | 398 lines | 256 lines (-36%) |
| `Ellison.lean` size | 191 lines | 185 lines (≈ same, different content) |
| Verified small-`i` simulator needed | Yes (infeasible: `50 ≤ i < 10^{632}`) | Yes (feasible: `50 ≤ i < 10^{18}`) |

The six remaining sorries split into:
- **2 conceptual** (`pillai_k_ge_two`, `pillai_linear_form_ne_zero`):
  elementary v₂ arguments, each ~10-20 lines.
- **1 analytic** (`log_bound_to_integer_bound`): Ellison's Lemma 1,
  ~60-100 lines using `Real.abs_log_one_add_le`.
- **1 numerical** (`pillai_baker_rhs_upper_bound`): constant comparison,
  requires unfolding `BakerWustholz.C` and `modifiedHeight` and doing
  real arithmetic. ~50 lines.
- **1 bookkeeping** (`pillai_baker_application`): two internal sorries
  for `Fin 3 →` sum expansion — mechanical, ~30 lines.
- **1 assembly** (`direct_pillai_bound_small`): combines the above via
  the documented proof chain. ~20 lines once the helpers are in.

None of these require number-field machinery or mathlib-gap work
(unlike the old approach, which needed `Rat.mulHeight₁_eq_max_num_natAbs_den`
that doesn't exist). They're all within reach of straightforward
real-analysis tactics.

## Detour: Could we use Matveev's theorem instead?

**Matveev's theorem (2000)** is the current best general-purpose effective
bound on linear forms in logarithms. From E. M. Matveev, *An explicit lower
bound for a homogeneous rational linear form in the logarithms of algebraic
numbers*, Izv. Math. **64** (2000), 1217–1269. The conclusion is:

```
|Λ| > exp(−C(n, D) · h'(α₁) · … · h'(αₙ) · log B)
```

where:
- `Ω = h'(α₁) · … · h'(αₙ)` with **modified height**
  `h'(α) = max(D · h(α), |log α|, 0.16)` — note `D · h` (not `h / D` as
  in Baker–Wüstholz);
- `C(n, D) ≈ 1.4 · 30^{n+3} · n^{4.5} · D² · (1 + log D)`.

### Numerical comparison for our `(n, D) = (3, 1)` case

| Bound | Outer exponent on `log B` | Constant `C(3, 1)` |
|---|---|---|
| Ellison (Baker 1966) | `(2n+1)² = 49` | absorbed into `(…)^{49}` |
| Baker–Wüstholz 1993 | 1 | `~2.1 · 10^{12}` |
| **Matveev 2000** | 1 | **`~4.8 · 10^{10}`** |

Matveev gives **~40× tighter constant** than Baker–Wüstholz for `n = 3`.
The big-`n` advantage of Matveev (`n^{4.5}` vs `n^{n+1}`) is wasted at
`n = 3`, but the small-`n` constants still improve modestly.

### Threshold for Pomme

Pomme's threshold equation is `i · log 3 / 2 > C · (log i)²` (after the
chain through `log_bound_to_integer_bound`).

| Bound | Critical `i` | Choice for `pommeThreshold` |
|---|---|---|
| Ellison (Baker 1966) | `~10^{632}` | `2^{2100}` |
| Baker–Wüstholz | `~10^{17}` | `2^{60}` |
| **Matveev** | **`~10^{14}` to `10^{15}`** | **`2^{50}`** |

So Matveev gives **another ~3 orders of magnitude** off the threshold,
on top of the Baker–Wüstholz improvement.

### What changes in the argument chain

**Almost nothing structurally.** The proof skeleton in `Ellison.lean`
ports verbatim:

| Helper | Status under Matveev |
|---|---|
| `BakerWustholz.lean` (axiom file) | Replace by `Matveev.lean`. Same shape, different `C` and `modifiedHeight`. |
| `log_bound_to_integer_bound` | **Unchanged.** Pure analytic Lemma 1; doesn't reference any Baker-style axiom. |
| `pillai_k_ge_two` | **Unchanged.** Pure number-theoretic. |
| `pillai_linear_form_ne_zero` | **Unchanged.** v₂ argument. |
| `pillai_baker_application` → `pillai_matveev_application` | Replace one axiom call. Same shape. |
| `pillai_baker_rhs_upper_bound` → `pillai_matveev_rhs_upper_bound` | Tighter constant, same form. |
| `pillai_log_dominates`, `pillai_ip5_lt_three_pow` | **Unchanged** (only `pommeThreshold` value updated). |
| `direct_pillai_bound_small` | **Unchanged structure**, just calls the new `_matveev_*` helpers. |

Effort to switch: ~1–2 hours of editing. Mechanical find-and-replace plus
one numerical re-derivation.

### What changes in the axiom statement

The Matveev axiom is **slightly more complex** to state than Baker–Wüstholz:

```lean
-- Matveev's modified height: max(D·h, |log α|, 0.16)
noncomputable def modifiedHeight ... :=
  let D : ℝ := Module.finrank ℚ K
  max (Height.logHeight₁ α)               -- = D · h(α) since logHeight₁ = D·h
      (max (‖Complex.log (φ α)‖) (0.16 : ℝ))

-- C(n, D) ≈ 1.4 · 30^(n+3) · n^4.5 · D² · (1 + log D)
noncomputable def C (n D : ℕ) : ℝ :=
  1.4 * 30 ^ (n + 3) * (n : ℝ) ^ ((4.5 : ℝ)) *
    (D : ℝ) ^ 2 * (1 + Real.log D)
```

Two notable differences:

1. **`n^{4.5}` requires `Real.rpow`** because `4.5 ∉ ℕ`. Baker–Wüstholz
   used integer powers (`n^{n+1}`), which is cleaner.
2. **The `0.16` magic constant** in the modified height is harder to
   justify than Baker–Wüstholz's `1/D`. It comes from a specific bound
   on imaginary parts of certain logs, deep inside Matveev's proof.

These are minor cosmetic complications.

### Verdict on Matveev

**Marginal improvement, not worth switching for the current state of the
proof.** Reasoning:

- For `n = 3`, the constant improvement (~40×) is real but not huge.
- The threshold drop (`~10^{17} → ~10^{14}`) helps the simulator but
  doesn't change the basic feasibility analysis (see "Dense vs sparse"
  below).
- The slightly more intricate axiom (Real.rpow, magic constant) costs
  a bit of clarity.
- The proof structure stays identical, so this isn't a one-way door —
  we can switch later if useful.

**The case for switching would be stronger if**:
- Pomme's problem had `n ≥ 5` variables (where Matveev's polynomial
  dependence on `n` would dominate).
- We actually needed dense verification of `pomme_small_range` (where
  every order of magnitude matters).
- Matveev were already in mathlib (it isn't; neither is BW).

**Aside: even better bounds for `n = 2`**.
For special-case `n = 2`, **Laurent–Mignotte–Nesterenko (1995)** gives
the best known constants. But Pomme's problem has `n = 3`, so LMN is
not directly applicable.

The hierarchy of "best effective Baker-type bound for `n` logarithms" is:
- `n = 2`: Laurent–Mignotte–Nesterenko.
- `n = 3`: Baker–Wüstholz or Matveev (within ~50× of each other).
- `n ≥ 4` or `5`: Matveev wins clearly.

## Dense vs sparse simulation: what `pomme_small_range` really requires

The `pomme_small_range` axiom states:

```lean
axiom pomme_small_range
    (i : ℕ) (hi_lo : 50 ≤ i) (hi_hi : i < pommeThreshold) :
    2 * i + 14 ≤ N i / 2 ^ padicValNat 2 (N i)
```

This is a **universal** statement: the inequality must hold for **every**
`i` in `[50, pommeThreshold)`. To discharge this axiom by computation,
the verification must be exhaustive over the entire range.

### What "sparse" verification actually does

In the Discord transcript (`previous-work/discord_kit_*.txt`), pomme,
vyx, and dihedralgroup discuss a **sparse iteration strategy** based on
poppuncher's observation (`previous-work/discord3.txt`):

> If `v₂(N_n) = k`, then `v₂(N_{n + 2^k}) ≥ k + 1`.

This says: starting from any `i` with `v₂(N_i) = k`, the value at
`i + 2^k` has `v₂ ≥ k + 1`. Iterating gives a **sequence of "first
occurrences"** of larger and larger v₂ values, found by jumping in
strides of `2^k`.

The sparse strategy used by Pomme/vyx:
1. Compute `v₂(N_i)` only at carefully chosen `i` values.
2. Increment `i` by `2^k` (where `k` is the current "smallest unseen v₂").
3. Each step is `O(1)` (modular arithmetic mod `2^k`); total work
   `O((log threshold)²)`.

For `threshold = 10^{300}`, this finishes in a few seconds. **But this
is verification by sampling, not proof.**

### Why sparse verification is incomplete for our axiom

The sparse strategy explores only `O(log threshold)` values of `i`. The
remaining `~threshold` values are skipped. The skipped i's aren't
checked against the inequality, so:

- A counterexample to the inequality at some skipped `i` would not be
  detected by sparse verification.
- Pomme's argument relies on a *probabilistic heuristic* that
  counterexamples are extremely unlikely (~`1/3^{10^{8}}`), but this
  is not a proof.

In the Discord chat, awnmp explicitly raised this objection:

> "why do you check for your next i `i += 2^k` / why only checking the
> ones that are accessible in this manner allows to say that you can say
> that the inequality holds also for the ones not of this form"

Pomme's response: *"its def true up to i ≤ 10^4 and i kinda assumed it
was true"*. This is honest — the sparse verification is informal.

### What the proof needs

To replace `pomme_small_range` with a verified theorem (rather than an
axiom), we need **dense** verification: explicitly compute `v₂(N i)` and
check `2·i + 14 ≤ N i / 2^{v₂(N i)}` for **every** `i` in `[50, threshold)`.

| Strategy | Iterations needed | Per-iteration cost | Total cost |
|---|---|---|---|
| Sparse (informal) | `~log²(threshold)` | `O(1)` | trivial (seconds) |
| Dense | `threshold` | `O(log² threshold)` (bigint v₂, division) | scales linearly |

### Computational feasibility of dense verification

For each candidate `pommeThreshold`:

| Bound | Threshold | Dense iterations | Dense wall time (1 CPU, GMP) |
|---|---|---|---|
| Ellison (Baker 1966) | `2^{2100}` | `~10^{632}` | physically impossible |
| Baker–Wüstholz | `2^{60}` | `~10^{18}` | `~10^{6}` CPU-years |
| **Matveev** | **`2^{50}`** | **`~10^{15}`** | **`~10^{3}` CPU-years** |

**Neither bound makes single-CPU dense verification practical.** Both
need either massive parallelization or a smarter algorithm.

### Why "smarter algorithm" is hard

The natural question: can we replace `O(threshold)` work with something
like `O(polylog(threshold))` while maintaining correctness?

Poppuncher's lemma `v₂(N_{i+2^k}) ≥ v₂(N_i) + 1` (when `v₂(N_i) = k`)
is *suggestive* but doesn't immediately imply that the inequality holds
at intermediate `i`. The intermediate `i` between sparse jumps can have
*any* v₂ value, not just predictable ones. A rigorous skip strategy
would need to control v₂ at *every* `i`, not just the sparse checkpoints.

Poppuncher tried this (see the Discord chat) and concluded:

> "But that doesnt tell us enough — in particular, its possible for the
> v2 to jump by a lot if the digits of r line up just right"

So no rigorous sparse algorithm is currently known.

### Practical implications for the proof

This leaves us with three options for handling `pomme_small_range`:

1. **Keep as axiom indefinitely.** The current state. The axiom is
   `pomme_small_range` and is justified by sparse verification +
   probabilistic heuristic. Not a formal proof, but morally accepted.

2. **Replace with verified parallel computation.** Generate a witness
   externally (a few CPU-decades on a cluster), encode the result in
   Lean as a large constant, prove it discharges the axiom. Requires
   trusting the cluster computation.

3. **Replace with verified Lean-internal computation** via `decide` or
   `native_decide`. Currently impractical because:
   - Lean's `Nat` arithmetic is slow (no GMP backend in the kernel).
   - `native_decide` adds the C compiler to the trusted base.
   - Threshold of `2^{50}` would still take CPU-decades even with
     compiled code.

### Why the threshold size matters even for sparse verification

A subtle point: even though sparse verification is informal, it does
become **harder** as the threshold grows, because:

- **Range of v₂ values to check**: the sparse strategy looks for first
  occurrences of each v₂. Larger threshold means more v₂ values to
  enumerate. With `threshold = 2^{2100}`, you need to verify v₂ values
  up to ~`log₂(3^{2^{2100}}/(2·2^{2100})) ≈ 2^{2100}·log₂ 3`, which is
  effectively infinite.
- **Confidence interval**: the probabilistic heuristic that "no
  counterexample exists in the unchecked i" gives a confidence bound
  that depends on the threshold. Lower threshold ↔ tighter heuristic.

So even informal verification benefits from a tight threshold. The
Baker–Wüstholz threshold (`2^{60}`) is at the boundary of what's
feasible to "morally check" via sparse iteration. The Matveev threshold
(`2^{50}`) is comfortably inside that boundary.

### Conclusion

**For the formal Lean proof**, sparse vs dense doesn't matter — we
have an axiom either way, and the axiom is universally quantified
over `[50, threshold)`.

**For *eliminating* the axiom**, we need dense verification, which is
not currently feasible at any of our thresholds (Baker–Wüstholz or
Matveev). This is the main reason `pomme_small_range` is likely to
remain an axiom for the foreseeable future, regardless of which
analytic bound we use.

**The threshold reduction from Baker–Wüstholz to Matveev**
(`2^{60} → 2^{50}`) would **not** make the small-`i` simulator
formally verifiable. It would, however, narrow the gap between
"informal sparse verification" and "rigorous dense verification" by
about 3 orders of magnitude — useful for confidence but not for
proof status.

**Recommendation for the small-`i` axiom**:
- Short term: keep as axiom, justify in the docstring.
- Medium term: ship a verified C++ dense verifier (independent of
  Lean) producing a checksum file; encode the checksum + a trusted
  reflection in Lean.
- Long term: when mathlib gets a verified bigint backend, port to
  Lean-native `decide`. (This is the only path to a fully axiom-free
  proof.)
