# Review of arguments in `1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---/previous-work/`

## Context
The TM is a BB(6) holdout. Its nonhalting reduces (per mxdys) to the number-theoretic claim:
```
(2·3^i + i + 5) / 2^{v2(2·3^i + i + 5)} >= 2i + 14      for all i >= 50   (*)
```
The directory contains multiple attempts at proving (*). Below is a file-by-file assessment of which arguments are flawed, incomplete, or correct.

---

## Files with flaws

### `Pomme.pdf` — concrete bug (fixed in Pomme2.pdf)
- Misstates Ellison's theorem: writes `|a m^x + b n^y| >= m^{(1−δ)x}` (**sum**) instead of `|a m^x − b n^y|` (**difference**).
- Then equates `|c·2^k − 2·3^i| = |a m^x + b n^y|` with `(a,b,m,n)=(c,2,2,3)`, which literally says
  `|c·2^k − 2·3^i| = |c·2^k + 2·3^i|`, i.e. false.
- With the sum form, the "or = 0" branch is also vacuous (positive integers, positive sum ≠ 0), so the disjunction is nonsense.
- Conclusion: the proof is not rigorous as stated; the step from the expression to Ellison does not type-check.

### `discord1.txt` — unjustified LLM claim
- Claims `∃ r, v2(3^i·2 + i + 5) = v2(i − r)` with `v2(i − r) = O(log i)`.
- In the chat (`discord_kit_*.txt`, ~10:10 PM), Pomme explicitly points out that **existence of r does not imply the O(log i) bound** — "you can keep on creating big jumps to just barely achieve O(i) growth". So the LLM's reduction is not a proof.

### `discord2.txt` — incomplete algebraic fragment (Autumn Pan)
- Case-splits on parity of `m_0` in `i = 2m_0 + 1`. Algebra through the excerpt is correct, but the fragment only reduces `N_{2m_0+1}` to `N_{4m_1+?}` — a halving descent that would need infinite iteration / a strong induction closing the loop.
- As written, it proves nothing; it simply restates the problem after one halving.

### `discord3.txt` — proves the wrong statement
- poppuncher shows that if `v2(N_n)=k` then `v2(N_{n+2^k}) >= k+1`, i.e. v2 is unbounded.
- Correct but **irrelevant**: (*) requires a *lower bound* on the odd part of `N_i`, not unboundedness of `v2(N_i)`. Unboundedness of v2 is actually the obstacle, not the solution.

### `discord_kit_2025_11_25 ... .txt` — chat log with suspect sim methodology
- The simulator advertised by Pomme/vyx uses `i += 2^{current_exponent}` — it **skips most i values**. User awnmp explicitly questions this (at ~9:40 PM): "why would repeating it would find a counterexample if such one exist?". Pomme responds with "it's def true up to i≤10^4 and i kinda assumed it was true". So the sim up to `i ≈ 10^{300}` / `10^{660}` does **not** verify (*) for every i in that range — only for a sparse subset. The bbwiki claim "verified for all 50 ≤ i ≤ 10^{660}" is therefore overstated unless a separate dense verification also exists.
- The `O(log i)` bound is never established in the discussion.

### Screenshots (`Screenshot_2026-04-10_10-35-42.png`, `10-39-24.png`, `10-40-42.png`) — only the trivial case
- The hand-written/typeset proof treats **Case 1: i even**. For even i, `2·3^i + i + 5` is odd, so `v2 = 0` and the inequality collapses to `2·3^i + i + 5 >= 2i + 14`, i.e. `2·3^i >= i + 9` — trivially true, proved by a needless induction on `i → i+2`.
- Lemma 1.3 (`v2(2^{2n+1} − 1) = 0`): this just says an odd number has `v2 = 0`. Proven via binomial expansion, which is absurdly over-engineered. Also, this lemma is never actually needed for (*).
- **The nontrivial odd-i case is not addressed in the screenshots provided.** The hard half of (*) is entirely missing.

### `bbwiki.txt` — status description, but two caveats
- States the inequality is "known...proven informally by Pomme, though it references an external paper which makes it difficult to prove using computer proof assistants" — this is accurate for Pomme2.pdf.
- The sim claim "verified for all 50 ≤ i ≤ 10^{660}" inherits the sim-methodology issue from the chat log (sparse i sampling).

---

## Files that appear OK

### `Pomme2.pdf` — corrected version, appears valid modulo external citation
- Fixes the `+` → `−` sign error: Theorem 2 is stated as `|a m^x − b n^y|`, which matches Pillai/Ellison.
- The overall argument:
  1. Reduce (*) to showing `|c·2^k − 2·3^i| > i + 5` for all positive c with `c ≤ 4i` and `k ≥ log2(3^i/(2i))`.
  2. Apply Ellison's Corollary 1 with `δ = 0.9` to get `|c·2^k − 2·3^i| >= 2^{0.1 k}` for `k ≥ x_0`.
  3. Show `k ≥ x_0` holds for all `i ≥ 2^{2100}` via a derivative comparison.
  4. Show `2^{0.1 k} ≥ (3^i/(2i))^{0.1} > 1.1^i/(2i) > i + 5` for i ≥ 106.
- Derivative check (spot-verified): at `i = 2^{2100}`, `log(4i) ≈ 1457`, `x_0 ≈ 2^{1556}·1457^{49} ≈ 2^{2070}`, and `k ≈ 2^{2100}` — so `k ≥ x_0` with room. The derivative `2^{1556}·49·log(4i)^{48}/i` at that point is `≈ 2^{−40} ≈ 4.5·10^{−11} < 0.0035` ✓; and `d/di log_2(3^i/(2i)) ≈ log_2 3 ≈ 1.585 > 0.0035` ✓. Derivative argument is fine.
- **Caveats**:
  - Only covers `i ≥ 2^{2100} ≈ 1.5·10^{632}`. The range `50 ≤ i < 2^{2100}` must be verified by a separate (dense!) simulator.
  - Relies on Ellison 1970-71, Corollary 1 — a formalization would need to either formalize Ellison or admit it as an axiom.
  - **Ellison citation verified against `STNB_1970-1971____A10_0.pdf`** (the actual Séminaire de théorie des nombres de Bordeaux paper, exposé n° 12, 10 Décembre 1970, pp. 12-01 — 12-05). Pomme2's Theorem 2 reproduces Ellison's Corollary 1 faithfully: the paper states, for positive integers `a,b,m,n` with `m ≤ n` and `δ > 0`, that for all `x ≥ x_0(δ,a,b,m,n)` either `|a m^x − b n^y| ≥ m^{(1−δ)x}` or `|a m^x − b n^y| = 0`, with `x_0 = (2^{31} log A / Δ)^{49}`, `A = max{4,a,b,m,n}` (from Theorem 1), `Δ = min{2, δ log m, δ log n}`. This matches Pomme2's statement verbatim, and the hypotheses are correctly discharged in Pomme2 (`m=2 ≤ n=3`; `δ=0.9 < 1` gives `Δ = 0.9 log 2 > 0.6`; `A = max{4,c} ≤ 4i`; and the numeric bound `(2^{31}/0.6)^{49} < 2^{1556}` is tight — the exact value is `2^{1519}·(5/3)^{49} ≈ 2^{1555}`).
  - The paper's proof of Corollary 1 depends on Lemma 2 of the paper, which in turn is "due to Baker [2]" (Baker's theorem on linear forms in logarithms). So a formal **proof** of Pomme2's Theorem 1 would reduce to formalizing Baker's theorem — a substantial undertaking; no such formalization is present in current mathlib.

  **Can Ellison's Corollary 1 be stated in current mathlib, e.g. as an axiom, to be used by Pomme's proof?** Yes — trivially. Corollary 1 is a purely elementary statement about nonnegative integers and reals (no algebraic numbers, no heights, no complex logs appear in its statement). A direct Lean axiom would be something like:
  ```
  axiom ellison_cor1 :
    ∀ (a b m n : ℕ) (δ : ℝ), 0 < a → 0 < b → 2 ≤ m → m ≤ n → 0 < δ →
    ∃ x₀ : ℕ, ∀ x y : ℕ, x₀ ≤ x →
      (a * m^x : ℤ) = b * n^y ∨
      (m : ℝ) ^ ((1 - δ) * x) ≤ |((a * m^x : ℤ) - b * n^y : ℤ)|
  ```
  This uses only `ℕ`, `ℤ`, `ℝ`, and `Real.rpow` / `HPow`, all of which are in core mathlib. One could alternatively make `x₀` explicit as `⌈(2^31 * Real.log (max 4 (max a (max b n))) / Δ)^49⌉` (with `Δ := min 2 (δ * Real.log m)` since `m ≤ n`), matching Ellison's formula. Nothing prevents writing this today.

  **Can Baker's theorem *proper* (Ellison's Lemma 2) be stated in current mathlib?** Also yes, as of Lean `leanprover/lean4:v4.29.0-rc8` / the mathlib bundled here. Mathlib now has:
  - `Mathlib.NumberTheory.Height.Basic`: multiplicative / logarithmic Weil heights `Height.mulHeight₁`, `Height.logHeight₁` via an `AdmissibleAbsValues` type class;
  - `Mathlib.NumberTheory.Height.NumberField`: an `AdmissibleAbsValues` instance for number fields (so `mulHeight₁ (α : K)` is a well-formed Weil height of an algebraic number once one picks `K = ℚ(α₁, ..., αₙ)`);
  - `Mathlib.NumberTheory.Height.Northcott`: Northcott finiteness;
  - `Complex.log`: principal-value logarithm;
  - `minpoly`, `IsAlgebraic`, `Polynomial.natDegree`: degree of an algebraic number.

  So Baker's theorem could be *stated* — pick a number field `K` containing the `αᵢ`, use `Height.mulHeight₁` for the height, `Complex.log` (after embedding into `ℂ`) for the logs, and phrase the conclusion as an explicit effective lower bound in terms of degree, heights, and `H = max |bᵢ|`. But mathlib contains **no proof** of any Baker-type result: a search under `Mathlib/NumberTheory/` for `Baker` / `linear.*form.*log` returns nothing, and the only transcendence results present are `Transcendental/Liouville/*` and `Transcendental/Lindemann/AnalyticalPart.lean` (partial Lindemann–Weierstrass — not Baker).

  **Practical implication for this project:** formalizing Pomme2's proof of (*) in Lean does not strictly require stating Baker. Axiomatising Ellison's Corollary 1 directly (in the elementary integer form above) is strictly weaker, closer to what Pomme actually uses, and lets the rest of Pomme2 (the derivative comparison and the `2^{0.1k} > i+5` estimate) be proved constructively in mathlib. However, Baker's theorem is the *standard* named result and the intended starting point, so below is a direct Lean axiomatization.

  **Lean statement of Baker's theorem (following Ellison's Lemma 2):**
  ```lean
  import Mathlib.NumberTheory.Height.NumberField
  import Mathlib.Analysis.SpecialFunctions.Complex.Log

  open Complex

  /-- **Baker's theorem on linear forms in logarithms**, effective form.

  Reference: A. Baker, *Linear forms in the logarithms of algebraic numbers*,
  Mathematika (1966–68); quoted as Lemma 2 of W. J. Ellison,
  *On a theorem of S. Sivasankaranarayana Pillai*,
  Séminaire de théorie des nombres de Bordeaux (1970-71), exposé n° 12.

  Let `α₁, …, αₙ` be nonzero elements of a number field `K` of degree `d ≥ 4`
  embedded into `ℂ` via `φ`, and suppose each `αᵢ` has multiplicative Weil height
  at most `A`, where `A ≥ 4`. Let `log (φ (αᵢ))` denote the principal value of
  the complex logarithm. Let `0 < δ ≤ 1`. If there exist rational integers
  `b₁, …, bₙ`, of absolute value at most `H`, such that the linear form
  `Λ := ∑ bᵢ · log (φ (αᵢ))` satisfies
      `0 < |Λ| < exp (−δ · H)`,
  then
      `H ≤ (4 ^ (n²) · δ⁻¹ · d ^ (2n) · log A) ^ ((2n + 1)²)`. -/
  axiom baker_linearForms_logs
      {n : ℕ}
      {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ)
      (hd : 4 ≤ Module.finrank ℚ K)
      (α : Fin n → K) (hα : ∀ i, α i ≠ 0)
      {A : ℝ} (hA : 4 ≤ A) (hH_α : ∀ i, Height.mulHeight₁ (α i) ≤ A)
      (b : Fin n → ℤ) {H : ℕ} (hH_b : ∀ i, (b i).natAbs ≤ H)
      {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
      (hΛ_pos :
        0 < ‖∑ i, (b i : ℂ) * Complex.log (φ (α i))‖)
      (hΛ_small :
        ‖∑ i, (b i : ℂ) * Complex.log (φ (α i))‖ < Real.exp (-(δ * (H : ℝ)))) :
      (H : ℝ) ≤
        (4 ^ (n ^ 2) * δ⁻¹ *
          (Module.finrank ℚ K : ℝ) ^ (2 * n) * Real.log A) ^ ((2 * n + 1) ^ 2)
  ```

  Notes on the formulation:

  1. **Working in a number field `K` with an embedding `φ : K →+* ℂ`** is the
     standard mathlib idiom for "algebraic numbers" with both an ambient
     algebraic structure (needed for `Height.mulHeight₁`) and a concrete complex
     realization (needed for `Complex.log`). Any ring hom `K →+* ℂ` is
     automatically injective (since `K` is a field), so `φ (α i) ≠ 0` follows
     from `α i ≠ 0`; Lemma 2 needs this to make `Complex.log (φ (α i))`
     meaningful (non-zero argument).
  2. **Height**: `Height.mulHeight₁` from `Mathlib.NumberTheory.Height.Basic`,
     combined with the `AdmissibleAbsValues` instance for number fields from
     `Mathlib.NumberTheory.Height.NumberField`, is the classical Weil height —
     this is exactly Ellison's "height" when `α ∈ K`.
  3. **Degree**: Ellison's `d ≥ 4` is on the common number field containing all
     `αᵢ`; `Module.finrank ℚ K` is the correct mathlib term (post-rename from
     `FiniteDimensional.finrank`).
  4. **Coefficient bound**: Ellison writes "rational integers of absolute value
     at most `H`"; `(b i).natAbs ≤ H` with `H : ℕ` encodes this.
  5. **`log` branch**: Ellison says "principal values of the logarithms"; this
     matches `Complex.log`, which is the principal branch.
  6. **Hypothesis `4 ≤ A`**: Ellison requires this so that `log A ≥ log 4 > 0`,
     ensuring the RHS of the conclusion is a positive real.
  7. **Hypothesis `4 ≤ d`**: similarly used in Ellison's bound; taking
     `d = Module.finrank ℚ K` is a (very mild) overestimate of the individual
     degrees of the `αᵢ`, but Ellison's bound is monotone in `d` so this is
     harmless.
  8. **Conclusion**: the explicit bound
     `(4 ^ (n²) · δ⁻¹ · d ^ (2n) · log A) ^ ((2n+1)²)` is copied verbatim from
     Ellison's Lemma 2 (p. 12-03 of the paper), which is how `x₀` in Corollary 1
     is derived.

  With this axiom in place, Ellison's Corollary 1 can be *proved* in Lean
  (non-trivially but without further number-theoretic axioms), following
  pages 12-03 / 12-04 of the paper; and Pomme2's Theorem 1 / Corollary 3 then
  follow from Corollary 1 by the elementary calculations already in Pomme2.pdf
  (log/derivative comparison), which are pure real analysis and fit comfortably
  in mathlib.
  - Ellison's Theorem 1 requires `0 < Δ < min{2, log m, log n}`. With `δ = 0.9` this becomes `0.9 log m < log m` and `0.9 log n < log n`, both trivially true for `m,n ≥ 2`. ✓
  - The bound `∆ > 0.6` is used as if `∆ = 0.6`; this is fine for an upper bound on `x_0`, but should be noted.

### `Screenshot_2026-04-10_10-34-30.png` — a variant of Pomme2 with threshold `7·10^{696}`
- Same Ellison-based argument, different numeric threshold. No new flaws visible; same caveats as Pomme2.pdf.

### `nt.number theory - ... MathOverflow.pdf`
- Reference material (Silverman's answer on p-adic valuations of linear recurrences). Not an argument about this TM. Note: Silverman's result applies only for `p > 2`, so it is *not* directly usable here, as savask observes in discord1.txt.

---

## Summary table

| File | Verdict |
|---|---|
| `Pomme.pdf` | **Flawed** — sum/difference bug in Ellison statement |
| `Pomme2.pdf` | OK (modulo Ellison citation + dense sim for small i) |
| `Screenshot_10-34-30.png` | OK (variant of Pomme2) |
| `Screenshot_10-35-42.png` | Incomplete — only fragment |
| `Screenshot_10-39-24.png` | Trivial lemma, over-proved, unused |
| `Screenshot_10-40-42.png` | **Flawed** — treats only the trivial even case |
| `discord1.txt` | **Flawed** — LLM claim unjustified |
| `discord2.txt` | Incomplete — halving descent not closed |
| `discord3.txt` | **Wrong target** — proves unboundedness, not the needed bound |
| `discord_kit_*.txt` | Sim methodology issue (sparse sampling); no complete proof |
| `bbwiki.txt` | Descriptive; inherits sim caveat |
| `nt...MathOverflow.pdf` | Reference only, not applicable (`p > 2`) |

**Bottom line**: Only `Pomme2.pdf` (and its variant `Screenshot_10-34-30.png`) constitutes a plausibly correct proof, and it depends on an external Ellison/Pillai theorem plus a dense verification of the small-i range that has **not** been convincingly done in the materials provided (the chat-based sim skips most i).
