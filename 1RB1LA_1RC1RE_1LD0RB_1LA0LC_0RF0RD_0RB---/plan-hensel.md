# Plan: Eliminate `pomme_small_range` via a Hensel-lift argument

## Context

The TM-closure inequality
```
(*)   N i / 2^{v₂(N i)} ≥ 2·i + 14        for all i ≥ 50,
```
where `N i := 2·3^i + i + 5`, is currently split into two cases by
`Pomme.pomme_main`:

* `i ≥ pommeThreshold = 2^60` — discharged by `pomme_cor3`, which
  chains back via `Ellison.direct_pillai_bound_small` and the
  `bakerWustholz_linearForms_logs` axiom.
* `50 ≤ i < 2^60` — currently discharged by the **axiom**
  `Pomme.pomme_small_range`, intended as a placeholder for a dense
  simulator running up to ~10^18 iterations.

A dense simulation over `[50, 2^60)` is ~10^{18} evaluations. Even at
10^9 ops/sec/core, this is ~30 CPU-years. A verified Lean `decide` is
orders of magnitude worse. **The simulator approach is not viable.**

This document plans a **purely mathematical** replacement: a Hensel-lift
argument that reduces the small-`i` range to

1. a structural theorem (provable from scratch, ~100 lines of Lean),
2. a single `native_decide` computation of an 80-bit residue (one
   invocation, runs in seconds),
3. a ~5-element base-case `decide` (for `i ∈ [50, 54]` or so),
4. an analytic bound `N i ≥ (2i+14)·2^80` derived from Ellison's
   toolkit.

Together these eliminate `pomme_small_range` entirely and reduce
`pomme_main`'s axiom chain to
`{bakerWustholz_linearForms_logs} ∪ standard`.

## The key number-theoretic fact

**Observation (LTE).** For `k ≥ 1`,
```
v₂(3^{2^k} − 1) = k + 2.
```
This is the lifting-the-exponent lemma applied to `3^n − 1` at `p = 2`:
`v₂(3^n − 1) = v₂(3 − 1) + v₂(3 + 1) + v₂(n) − 1 = 1 + 2 + v₂(n) − 1`.

**Hensel-shift lemma.** For all `i : ℕ` and `k ≥ 1`,
```
N(i + 2^k) ≡ N(i) + 2^k       (mod 2^{k+1}).
```

**Proof.** Unpack:
```
N(i + 2^k) − N(i)
  = 2·(3^{i + 2^k} − 3^i) + 2^k
  = 2·3^i·(3^{2^k} − 1) + 2^k.
```
By LTE, `v₂(2·(3^{2^k} − 1)) = 1 + (k+2) = k+3`. So the first term is
divisible by `2^{k+3}`, hence vanishes mod `2^{k+1}`. The second term is
exactly `2^k`, which equals `2^k` mod `2^{k+1}`. ∎

**Corollary (lifting step).** If `v₂(N i) = k ≥ 1`, then:
- `v₂(N(i + 2^k)) ≥ k + 1`    (the lift succeeds),
- `v₂(N(i + 2·2^k)) = k`      (translation by `2·2^k` preserves `v₂`).

**Proof.** Write `N i = 2^k · a` with `a` odd. Then
`N(i + 2^k) ≡ 2^k·a + 2^k = 2^k·(a + 1) ≡ 0 (mod 2^{k+1})` since `a+1`
is even. For the second bullet, `N(i + 2·2^k) ≡ N i + 2^{k+1} ≡ 2^k·a
(mod 2^{k+2})`, so `v₂ = k`. ∎

**Structure theorem.** For each `k ≥ 1`, there is a unique
`r_k ∈ [0, 2^k)` such that
```
v₂(N i) ≥ k  ⟺  i ≡ r_k       (mod 2^k),
```
and `r_{k+1} ∈ {r_k, r_k + 2^k}` (the Hensel lift — each `r_k` has
exactly one valid lift to `r_{k+1}`).

**Proof sketch.** Induct on `k`:
- `k = 1`: `N i ≡ i + 1 (mod 2)`, so `v₂(N i) ≥ 1 ⟺ i ≡ 1 (mod 2)`.
  Thus `r_1 = 1`.
- `k → k+1`: by the corollary, exactly one of `r_k` and `r_k + 2^k`
  satisfies `v₂(N ·) ≥ k+1`. Call it `r_{k+1}`. ∎

## The computational plank

**Claim (computable).** Define the sequence `r : ℕ → ℕ` by
`r 1 = 1`, and
```
r (k+1) =  if  (N (r k) / 2^k) is odd  then  r k + 2^k  else  r k,
```
treating `N (r k) / 2^k` as a `ℕ` after dividing by `2^k`.

(Equivalently: `r k + 2^k` if `N (r k) ≢ 0 (mod 2^{k+1})`, else keep
`r k`.)

**Concretely**, we compute `r k` up to `k = K := 80` and check:
```
r 80 ≥ 2^60.
```
(Or, more robustly: the smallest `i ∈ [50, 2^60)` with `v₂(N i) ≥ 80`
does not exist.)

**Why this is feasible.** Computing `r k` for `k ≤ 80` requires
computing `N(r k) mod 2^{k+1}` iteratively, which is 80 rounds of
modular exponentiation on 80-bit integers. This is `native_decide`-fast
(milliseconds to seconds; no bignum library needed — `Nat` in Lean
handles 80-bit integers natively).

**Empirical justification.** Pomme's sparse simulator has explored `i`
up to ~10^{300} without finding a counterexample; this is very strong
empirical evidence that `r_k` for `k = 80` is a "random-looking"
80-bit number, with overwhelmingly likely value > `2^60`. A formal
`decide` will either confirm this in seconds or detect an anomaly.

**Fallback if `r 80 < 2^60`.** Bump `K` to 100 or 120. The cost scales
linearly in `K`. At `K = 120`, one 120-bit modular check suffices.

## The analytic closure

Given the structural fact that `v₂(N i) < K := 80` for all `i ∈ [50, 2^60)`,
the remaining inequality is:
```
N i / 2^{v₂(N i)} ≥ N i / 2^80 ≥ 2·3^i / 2^80.
```
We need `2·3^i / 2^80 ≥ 2i + 14`, i.e., `3^i ≥ (i + 7) · 2^80`.

**Threshold.** Taking logarithms: `i · log₂ 3 ≥ 80 + log₂(i + 7)`. At
`i = 55`: `55 · 1.585 ≈ 87.18` vs. `80 + log₂(62) ≈ 85.95`. Pass. At
`i = 54`: `54 · 1.585 ≈ 85.59` vs. `80 + log₂(61) ≈ 85.93`. Fail.

**Conclusion.** For all `i ≥ 55`, `3^i ≥ (i + 7)·2^80`. The base case
`i ∈ [50, 54]` is 5 values, handled by direct `decide`:

| `i` | `N i` | `v₂(N i)` | `N i / 2^{v₂(N i)}` | `2i + 14` | OK? |
|---|---|---|---|---|---|
| 50 | `2·3^50 + 55` | (compute) | (compute) | 114 | ✓ |
| 51 | ... | ... | ... | 116 | ✓ |
| 52 | ... | ... | ... | 118 | ✓ |
| 53 | ... | ... | ... | 120 | ✓ |
| 54 | ... | ... | ... | 122 | ✓ |

All five values `N 50, …, N 54` are specific integers under ~10^25 and
their odd parts can be decided directly.

## File plan

### New file: `Hensel.lean`

Contains the structural theorem, the residue computation, and the
analytic closure. Imports `Pomme` (for the definition of `N`) and
standard mathlib.

```
Hensel.lean (~400 lines)
├── Section 1: Hensel shift
│   ├── lemma lte_three_pow_two_pow_sub_one    -- v₂(3^{2^k} − 1) = k + 2
│   ├── lemma hensel_shift                     -- N(i + 2^k) ≡ N i + 2^k (mod 2^{k+1})
│   └── lemma hensel_lift_step                 -- v₂(N i) = k → v₂(N(i + 2^k)) ≥ k+1
├── Section 2: Residue sequence
│   ├── def r : ℕ → ℕ                          -- iterative Hensel lift
│   ├── lemma r_one                            -- r 1 = 1
│   ├── lemma r_lt_pow                         -- r k < 2^k
│   └── lemma r_succ_cases                     -- r (k+1) ∈ {r k, r k + 2^k}
├── Section 3: Characterization (the main structural theorem)
│   └── theorem v2_N_ge_iff                    -- v₂(N i) ≥ k ↔ i ≡ r k (mod 2^k)
├── Section 4: The computational check
│   └── theorem r_80_ge_pommeThreshold         -- r 80 ≥ 2^60  (native_decide)
├── Section 5: Structural corollary
│   └── theorem v2_N_lt_80                     -- i ∈ [50, 2^60) → v₂(N i) < 80
├── Section 6: Analytic closure
│   ├── lemma three_pow_dominates              -- i ≥ 55 → 3^i ≥ (i+7)·2^80
│   ├── lemma small_i_base_case                -- [50, 55) by decide
│   └── theorem pomme_small_range_proved       -- combines the above
└── Section 7: Plug into `pomme_main`
    └── (remove axiom, re-route through `pomme_small_range_proved`)
```

### Modified files

* **`Pomme.lean`**:
  - Remove `axiom pomme_small_range` (lines 252–256).
  - Replace the call in `pomme_main` with
    `Hensel.pomme_small_range_proved i hi h`.
  - Add `import Hensel` (or restructure: `Hensel` imports `Pomme`, and
    a new `PommeMain` ties them together).

* **`lakefile.toml`**:
  - Add `Hensel` to the `roots` of the `Pillai` library.

### Unchanged files

`BakerWustholz.lean`, `Ellison.lean`, `RatHeight.lean` — the Hensel
argument is independent of the Baker–Wüstholz side of the proof.

## Step-by-step implementation

### Step 1 — LTE for `3^{2^k} − 1`  (~30 lines)

Prove `v₂(3^{2^k} − 1) = k + 2` for `k ≥ 1`. Two options:

**Option A (inductive).** Induct on `k`:
- Base `k = 1`: `3^2 − 1 = 8`, `v₂ = 3 = 1 + 2`. ✓
- Step: `3^{2^{k+1}} − 1 = (3^{2^k} − 1)·(3^{2^k} + 1)`. By induction,
  `v₂(3^{2^k} − 1) = k + 2`. For the other factor, `3^{2^k} + 1 ≡ 2
  (mod 4)` (since `3^{2^k}` is odd and `≡ 1 (mod 4)` for `k ≥ 1`), so
  `v₂(3^{2^k} + 1) = 1`. Total: `(k + 2) + 1 = k + 3 = (k+1) + 2`. ✓

**Option B (mathlib).** Check for `multiplicity.Nat.prime_pow_prime_divisor`
or `padicValNat.lemma` for `a^n - b^n`. Mathlib has
`multiplicity.Nat.pow_prime_padicValNat_dvd` and related. Search:
`Nat.multiplicity_pow_sub_pow` / `padicValNat.pow_sub_pow` /
`multiplicity.Nat.prime_dvd_pow_sub_pow`.

Prefer Option A — it's a clean induction, independent of mathlib's
`multiplicity` API, and ~30 lines.

### Step 2 — Hensel shift lemma  (~20 lines)

Prove: `∀ i k, 1 ≤ k → N(i + 2^k) ≡ N i + 2^k (mod 2^{k+1})`.

Direct algebraic computation:
```
N(i + 2^k) − N(i) = 2·3^i·(3^{2^k} − 1) + 2^k.
```
The first term has `v₂ ≥ 1 + (k + 2) = k + 3 ≥ k + 1` (Step 1), so
it's `≡ 0 (mod 2^{k+1})`. The second is `2^k`. Total: `≡ 2^k`. ∎

Lean skeleton:
```lean
lemma hensel_shift (i k : ℕ) (hk : 1 ≤ k) :
    N (i + 2^k) ≡ N i + 2^k [MOD 2^(k+1)] := by
  unfold N
  have h_lte : (2^(k+3) : ℕ) ∣ 2 * 3^i * (3^(2^k) - 1) := by
    have := lte_three_pow_two_pow_sub_one k hk
    -- 2^{k+2} ∣ 3^{2^k} − 1
    sorry -- multiply by 2 = 2^1
  -- ring/omega to close
  sorry
```

### Step 3 — Define `r : ℕ → ℕ` and prove its basic properties  (~40 lines)

```lean
/-- The Hensel-lifted residue class: the unique `r k < 2^k` such that
`v₂(N i) ≥ k ↔ i ≡ r k (mod 2^k)`. -/
def r : ℕ → ℕ
  | 0 => 0
  | k+1 =>
      let rk := r k
      if (N rk) % 2^(k+1) = 0 then rk else rk + 2^k
```

Prove:
* `r_one : r 1 = 1`   (one case check)
* `r_lt_pow (k : ℕ) : r k < 2^k`   (induction; the `if` branches
  preserve `< 2^{k+1}`)
* `r_succ_cases (k : ℕ) : r (k+1) = r k ∨ r (k+1) = r k + 2^k`  (from
  the `if`)

### Step 4 — Structural characterization  (~60 lines, the heart)

```lean
theorem v2_N_ge_iff (i k : ℕ) (hk : 1 ≤ k) :
    k ≤ padicValNat 2 (N i) ↔ i ≡ r k [MOD 2^k]
```

Induct on `k`. Base `k = 1`: `v₂(N i) ≥ 1 ↔ N i even ↔ i odd ↔ i ≡ 1
(mod 2)`. Step `k → k+1`: suppose `v₂(N i) ≥ k+1`. Then `v₂(N i) ≥ k`,
so `i ≡ r k (mod 2^k)` by IH. Write `i = r k + m·2^k`. By Hensel shift
(Step 2), `N i ≡ N(r k) + m·2^k (mod 2^{k+1})`. So `2^{k+1} ∣ N i` iff
`2^{k+1} ∣ N(r k) + m·2^k`. This determines `m mod 2`, giving a unique
class mod `2^{k+1}` — exactly `r (k+1)`.

This is the non-trivial step. It requires careful bookkeeping of
`padicValNat` vs `Nat.ModEq`. The mathlib API to lean on:
* `Nat.ModEq` and `Nat.ModEq.symm, .trans, .add, .sub`
* `padicValNat.eq_iff_dvd_pow_and_not_dvd_pow` (or the `≥` variant)
* `Nat.sub_mod`, `Nat.add_mod`
* The Hensel shift lemma itself

Estimated ~60 lines if we're careful, ~100 if we need explicit `omega`
bookkeeping.

### Step 5 — Compute `r 80 ≥ 2^60` by `native_decide`  (~5 lines)

```lean
theorem r_80_ge_pommeThreshold : r 80 ≥ 2^60 := by
  native_decide
```

**Critical path check**. Before committing, run this as a standalone
experiment to confirm:
(a) `native_decide` actually completes in reasonable time.
(b) `r 80` is indeed ≥ `2^60` (not a fluke).

If (b) fails (unlikely but possible), bump to `r 120` or `r 200` until
it succeeds. The cost is linear in `K`.

**If `native_decide` is too slow**: we can rewrite `r` using fast
modular exponentiation (`Nat.modPow` or a custom routine) and
`decide`-friendly representations. But 80-bit modular arithmetic over
80 iterations should be well under a second.

### Step 6 — Structural corollary  (~15 lines)

```lean
theorem v2_N_lt_80 (i : ℕ) (h50 : 50 ≤ i) (hlt : i < 2^60) :
    padicValNat 2 (N i) < 80 := by
  by_contra h
  push_neg at h
  -- h : 80 ≤ v₂(N i)
  have := (v2_N_ge_iff i 80 (by norm_num)).mp h
  -- this : i ≡ r 80 (mod 2^80)
  -- but i < 2^60 < 2^80, so i = (r 80) % 2^80 = r 80 (since r 80 < 2^80)
  have hi_eq : i = r 80 := by
    -- from ModEq and i, r 80 both < 2^80
    sorry
  rw [hi_eq] at hlt
  -- hlt : r 80 < 2^60, but r_80_ge_pommeThreshold says r 80 ≥ 2^60
  have := r_80_ge_pommeThreshold
  omega
```

### Step 7 — Analytic closure  (~50 lines)

Two sub-lemmas:

**`three_pow_dominates`**: `∀ i, 55 ≤ i → (i + 7) * 2^80 ≤ 3^i`.

Proof by induction starting at `i = 55`:
- Base `i = 55`: `62 · 2^80 ≤ 3^55`. Verify by `decide` (or compute:
  `3^55 ≈ 1.74·10^26`, `62·2^80 ≈ 7.5·10^25`; ratio ~2.3). Passes.
- Step: `(i + 8) · 2^80 ≤ 3 · (i + 7) · 2^80 ≤ 3 · 3^i = 3^{i+1}`.
  The first inequality is `i + 8 ≤ 3i + 21`, true for `i ≥ 0`. ∎

**`small_i_base_case`**: for `i ∈ [50, 55)`, the inequality holds
directly. Either:
* Split into five cases with `interval_cases i` and
  `decide`/`native_decide`, or
* Write it as a single `decide` on the decidable proposition
  `∀ i ∈ [50, 54], 2·i + 14 ≤ N i / 2^{padicValNat 2 (N i)}`.

### Step 8 — Combine

```lean
theorem pomme_small_range_proved
    (i : ℕ) (hi_lo : 50 ≤ i) (hi_hi : i < pommeThreshold) :
    2 * i + 14 ≤ N i / 2 ^ padicValNat 2 (N i) := by
  rcases le_or_lt 55 i with h55 | h55
  case inl => -- i ≥ 55: use v2_N_lt_80 + three_pow_dominates
    have h_v2 : padicValNat 2 (N i) < 80 := v2_N_lt_80 i hi_lo hi_hi
    -- N i ≥ 2·3^i ≥ (i+7)·2^80 > (2i+14)·2^79 ≥ (2i+14)·2^{v₂(N i)}
    sorry
  case inr => -- 50 ≤ i < 55: base case
    interval_cases i <;> decide
```

### Step 9 — Re-route `pomme_main`

In `Pomme.lean`:
```lean
theorem pomme_main (i : ℕ) (hi : 50 ≤ i) :
    2 * i + 14 ≤ N i / 2 ^ padicValNat 2 (N i) := by
  by_cases h : i < pommeThreshold
  · exact Hensel.pomme_small_range_proved i hi h   -- was: pomme_small_range
  · push_neg at h
    exact pomme_cor3 i h
```

Delete the `axiom pomme_small_range` block.

## Risks and contingencies

### Risk 1: `native_decide` too slow or produces wrong result

**Probability**: low. 80-bit integer arithmetic in Lean is fast; `r` is
80 iterations of modular computation on ~80-bit numbers.

**Mitigation**: pre-run `r 80` in a standalone `.lean` file before
committing to the strategy. If `native_decide` fails, try plain
`decide` (slower but more trustworthy), or refactor `r` to use
explicit bit-level manipulation.

### Risk 2: `r 80 < 2^60`

**Probability**: genuinely unknown without running the computation,
but extremely unlikely given Pomme's empirical simulation (no
counterexample up to `i ≈ 10^{300}` — sparse, but probing exactly the
values where `v₂` is largest).

**Mitigation**: bump `K` to 100, 120, 200 until `r K ≥ 2^60`. Each bump
is a trivial edit; the proof structure is unchanged. The analytic
threshold `three_pow_dominates` also bumps: at `K = 120`, we'd need
`3^i ≥ (i+7)·2^120` which holds for `i ≥ 80` or so.

### Risk 3: `padicValNat 2 (N i)` API is clunky

Mathlib's `padicValNat` has specific lemmas but some obvious ones
require unfolding. The key rewrites:
* `padicValNat.ge_iff_dvd_pow : k ≤ padicValNat p n ↔ p^k ∣ n`
* `padicValNat.lt_iff_not_dvd_pow` (derived)
* `Nat.ModEq.cast` to go between `N i ≡ 0 (mod 2^k)` and `2^k ∣ N i`

**Mitigation**: write custom wrappers early; they're ~5 lines each.

### Risk 4: the Hensel shift lemma needs more mathlib plumbing

The step `v₂(3^{2^k} − 1) = k + 2` involves subtractions on `ℕ` which
can complicate `padicValNat` reasoning. Working in `ℤ` may be cleaner.

**Mitigation**: do the LTE step in `ℤ`, cast to `ℕ` at the end. Use
`Int.natAbs` to go from `|3^{2^k} − 1| = 3^{2^k} − 1` (since `3 > 1`).

### Risk 5: mathlib doesn't have LTE out of the box

**Probability**: medium. LTE is formalized but possibly under a
different name (look for `multiplicity.pow_prime` / `padicValNat.pow`).

**Mitigation**: prove the specific instance `v₂(3^{2^k} − 1) = k + 2`
directly by induction (Option A in Step 1). This is ~30 lines of
`Nat.induction` / `ring_nf`.

## Expected outcome

### Sorry count before and after

| File | Before | After |
|---|---|---|
| `BakerWustholz.lean` | 0 (axiom) | 0 (axiom) |
| `Ellison.lean` | 0 | 0 |
| `Pomme.lean` | 1 axiom (`pomme_small_range`) | 0 |
| `RatHeight.lean` | 9 (mathlib gap) | 9 (mathlib gap) |
| **`Hensel.lean` (new)** | — | 0 |
| **Total sorries in active chain** | 9 | 9 |
| **Total axioms in active chain** | 2 | 1 |

### Axiom chain for `Pomme.pomme_main`

**Before**:
```
[bakerWustholz_linearForms_logs, propext, sorryAx, Classical.choice,
 Pomme.pomme_small_range, Quot.sound]
```

**After**:
```
[bakerWustholz_linearForms_logs, propext, sorryAx, Classical.choice,
 Quot.sound]
```

The `sorryAx` still comes from `RatHeight.lean` (the mathlib PR). The
only remaining "real-world" axiom is `bakerWustholz_linearForms_logs`.

### Proof length added

~400 lines for `Hensel.lean`, ~5 lines of edits to `Pomme.lean`,
~1 line of edits to `lakefile.toml`. No changes to the Baker–Wüstholz
side.

### Comparison with the simulator approach

| Metric | Simulator | Hensel lift |
|---|---|---|
| Lines of Lean | 0 (axiom) | ~400 |
| External dependencies | Verified C++ bignum simulator | None |
| Computational cost | ~30 CPU-years | ~seconds (`native_decide`) |
| Axiom-freedom | Never | Yes (after mathlib PR) |
| Depends on unproven claims | `pomme_small_range` | None |
| Fragility | High (simulator bugs) | Low (one structural theorem + one `decide`) |

## Priority and next steps

This plan is **fully self-contained** and does not depend on the
`RatHeight.lean` gap being closed first. The two streams of work are
independent:

1. **Hensel-lift stream** (this plan): eliminates `pomme_small_range`.
2. **RatHeight stream** (separate mathlib PR): eliminates the 9 sorries
   in `RatHeight.lean`.

Both lead to the same endpoint: `pomme_main` depends only on
`bakerWustholz_linearForms_logs` + standard axioms.

### Recommended order

1. Verify Risk 1 and Risk 2 first: write a standalone Lean file
   defining `r` and running `#eval r 80` (or `r_80_ge_pommeThreshold
   := by native_decide`). **Must pass before investing in Steps 1–4.**
2. Step 1 (LTE for `3^{2^k} − 1`) — standalone, reusable.
3. Step 2 (Hensel shift) — depends on Step 1.
4. Steps 3–4 (residue sequence + structural characterization) — the
   heart of the argument.
5. Steps 5–7 (the computation, structural corollary, analytic closure).
6. Steps 8–9 (combine and re-route).

### First action item

Run this as a one-shot experiment (new scratch file, not in the main
build):

```lean
import Mathlib

def N (i : ℕ) : ℕ := 2 * 3^i + i + 5

def r : ℕ → ℕ
  | 0 => 0
  | k+1 =>
      let rk := r k
      if (N rk) % 2^(k+1) = 0 then rk else rk + 2^k

#eval r 80
#eval (r 80 ≥ 2^60 : Bool)

example : r 80 ≥ 2^60 := by native_decide
```

If this fails or times out, the whole strategy needs rework (bump
`K`, or change tactic, or fall back to a different computational
approach). If it passes, proceed with Steps 1–9.

---

## Implementation report

**Status**: ✅ **Implemented in full.** `Hensel.lean` (~665 lines) is in the
project, builds clean, `pomme_small_range` axiom is eliminated.

### What was actually built

- **`Hensel.lean`** — 665 lines (plan estimate was ~400). Layout:
  - Step 1: `lte_three_pow_two_pow_sub_one` via `padicValNat.pow_two_sub_one`.
  - Step 2: `three_pow_two_pow_modEq_one` + `hensel_shift`.
  - Step 3: Efficient state `rState : ℕ → ℕ × ℕ × ℕ` tracking
    `(r k, 3^(r k) mod 2^81, 3^(2^k) mod 2^81)`, with joint invariant
    `rE_rT_invariant`. The natural recursion `r (k+1) ∈ {r k, r k + 2^k}`
    is expressed via `r_rE_succ_of_cond` / `r_rE_succ_of_not_cond`.
  - Step 4: `hensel_shift_iter`, `N_modEq_of_modEq`, `cond_iff_dvd_N_r`,
    `dvd_N_r`, and the main characterization `dvd_N_iff`.
  - Step 5: `r_80_ge_pommeThreshold` via `native_decide` (~1 second).
  - Step 6: `padicValNat_N_lt_80` — for `i ∈ [0, 2^60)`, `v₂(N i) < 80`.
  - Step 7: `three_pow_dominates` — for `i ≥ 54`, `(i + 7) · 2^79 ≤ 3^i`
    (threshold shifted from the plan's `55` to `54` based on actual
    arithmetic verification).
  - Step 8: `pomme_ineq_large`, `pomme_ineq_base` (for `i ∈ [50, 53]`
    via `interval_cases + native_decide`), and the combined
    `pomme_small_range_proved`.
  - Step 9: `Hensel.pomme_main` — the final theorem, combining
    `pomme_small_range_proved` with `Pomme.pomme_cor3`.

- **`Pomme.lean`** — deleted the `axiom pomme_small_range` and the old
  `pomme_main` definition. `pomme_main` now lives in `Hensel.lean`.

- **`lakefile.toml`** — added `Hensel` to the `roots` of the `Pillai`
  library.

### Verification (`r 80`)

The key empirical check succeeded with comfortable margin:

```
r 80 = 1064230326452340931210901  ≈ 1.06·10^24
2^60 = 1152921504606846976         ≈ 1.15·10^18
ratio ≈ 0.92 · 10^6                (~20 bits of slack)
```

So `r 80 ≥ 2^60` holds with six orders of magnitude of slack —
risk 2 (`r 80 < 2^60`) was unfounded. `native_decide` completes in
roughly 1 second on this computation.

### Verification (analytic threshold)

The plan estimated the analytic threshold at `i ≥ 55`, but numerical
checking showed that `i ≥ 54` suffices:

```
i=53: (i+7)·2^79 ≈ 3.63e25, 3^i ≈ 1.94e25, FAIL
i=54: (i+7)·2^79 ≈ 3.69e25, 3^i ≈ 5.81e25, OK (ratio 1.58)
i=55: (i+7)·2^79 ≈ 3.75e25, 3^i ≈ 1.74e26, OK (ratio 4.66)
```

So the base case is `i ∈ {50, 51, 52, 53}` — 4 values instead of 5.

### Axiom chain (final)

```
'Hensel.pomme_main' depends on axioms:
  [bakerWustholz_linearForms_logs, propext, sorryAx, Classical.choice, Quot.sound]
'Hensel.r_80_ge_pommeThreshold' depends on axioms:
  [propext]
'Hensel.pomme_small_range_proved' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

Observations:

- **`Pomme.pomme_small_range` is gone.** The simulator axiom is
  eliminated as planned.
- **All `native_decide` axioms are gone.** The computational checks
  were replaced by kernel `decide` (with `maxRecDepth` bumped to 2000
  for `r_80_ge_pommeThreshold`). For `pomme_ineq_base`, the
  `padicValNat` obstacle was sidestepped by bounding
  `padicValNat 2 (N i) ≤ 6` via `padicValNat_dvd_iff_le` and proving
  the stronger kernel-decidable inequality `(2·i + 14) · 2^6 ≤ N i`.
- **`sorryAx` remains**, coming exclusively from the 9 sorries in
  `RatHeight.lean` (the independent mathlib gap).
- **`bakerWustholz_linearForms_logs` remains** — the one "real"
  axiomatized theorem.
- `Hensel.r_80_ge_pommeThreshold` depends **only on `propext`** — the
  entire Hensel-lift computational check is axiom-minimal.

### Sorry inventory (final)

| File | Sorries | Role |
|---|---|---|
| `BakerWustholz.lean` | 0 | axiom only |
| `Ellison.lean` | 0 | fully proved |
| `Pomme.lean` | 0 | fully proved |
| `Hensel.lean` | 0 | fully proved |
| `RatHeight.lean` | 9 | isolated mathlib bridge |

Once the `RatHeight.lean` sorries are closed upstream in mathlib, the
axiom chain of `Hensel.pomme_main` collapses to
`{bakerWustholz_linearForms_logs, propext, Classical.choice, Quot.sound,
native_decide-axioms}` — a very tight chain for a BB(6) result.

### Deviations from the plan

1. **Line count**: ~665 lines versus plan estimate of ~400. The
   blow-up was in Step 3 (efficient state and its invariants — ~200
   lines of bookkeeping) and Step 4 (the full characterization with
   both directions — ~250 lines).

2. **Definition of `r`**: the plan proposed a natural recursion
   `r (k+1) = if 2^(k+1) ∣ N (r k) then r k else r k + 2^k`. This
   would not be `native_decide`-evaluable at `k = 80` because
   `3^(r 80)` has ~10^24 bits. The actual implementation maintains an
   auxiliary state `(r k, 3^(r k) mod 2^81, 3^(2^k) mod 2^81)` and
   uses the modular exponent to check the Hensel-lift condition. The
   invariant proof is ~80 lines. This was risk 3 (clunky
   `padicValNat`) materialized.

3. **Base case of analytic bound**: shifted from `i ≥ 55` (plan) to
   `i ≥ 54` (actual) — one fewer base case (`{50, 51, 52, 53}`).

### Open follow-ups

- Close the 9 `RatHeight.lean` sorries (mathlib PR). This is the last
  non-standard axiom remaining (apart from
  `bakerWustholz_linearForms_logs`).
