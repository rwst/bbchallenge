import Pomme
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Defs

/-!
# Hensel-lift replacement for `pomme_small_range`

This file replaces the `Pomme.pomme_small_range` axiom (covering the
range `50 ≤ i < 2^60`) with a **purely mathematical proof**.

## Strategy

The recurrence `N i := 2·3^i + i + 5` has a 2-adic Hensel-lift
structure: for each `k ≥ 1`, there is a unique `r k ∈ [0, 2^k)` such
that `v₂(N i) ≥ k ↔ i ≡ r k (mod 2^k)`, and `r (k+1) ∈ {r k, r k + 2^k}`.

Computing `r 80` (via `native_decide`, using an efficient modular
iteration) gives `r 80 ≈ 1.06·10^24 > 2^60`. Therefore for all
`i ∈ [50, 2^60)`, `v₂(N i) < 80`, so
`N i / 2^{v₂(N i)} ≥ N i / 2^80 ≥ 2·3^i / 2^80 ≥ 2i + 14` — the last
inequality holds for `i ≥ 55` by induction, and `i ∈ [50, 54]` is a
5-element `decide`.

See `plan-hensel.md` for full details.

## Contents

* Step 1: LTE `v₂(3^(2^k) − 1) = k + 2` for `k ≥ 1`.
* Step 2: Hensel shift `N(i + 2^k) ≡ N i + 2^k (mod 2^(k+1))`.
* Step 3: Residue sequence `r : ℕ → ℕ`.
* Step 4: Characterization `v₂(N i) ≥ k ↔ i ≡ r k (mod 2^k)`.
* Step 5: Computational check `r 80 ≥ 2^60` via `native_decide`.
* Step 6: Analytic closure for `i ≥ 55`.
* Step 7: Base case `i ∈ [50, 54]` by `decide`.
* Step 8: Combined `pomme_small_range_proved`.
-/

namespace Hensel

open Pomme

/-! ## Step 1: LTE `v₂(3^(2^k) − 1) = k + 2`

Follows from `padicValNat.pow_two_sub_one` with `x = 3`, `n = 2^k`. -/

/-- **Lifting-the-exponent**: for `k ≥ 1`,
`v₂(3^(2^k) − 1) = k + 2`. -/
lemma lte_three_pow_two_pow_sub_one (k : ℕ) (hk : 1 ≤ k) :
    padicValNat 2 (3 ^ (2 ^ k) - 1) = k + 2 := by
  -- Apply `padicValNat.pow_two_sub_one` with `x = 3`, `n = 2^k`.
  have h_x : (1 : ℕ) < 3 := by norm_num
  have h_odd : ¬ (2 : ℕ) ∣ 3 := by decide
  have h_n_ne : (2 ^ k : ℕ) ≠ 0 := by positivity
  have h_n_even : Even (2 ^ k : ℕ) := by
    refine ⟨2 ^ (k - 1), ?_⟩
    rw [← two_mul, ← pow_succ']
    congr 1; omega
  have h := padicValNat.pow_two_sub_one h_x h_odd h_n_ne h_n_even
  -- h : padicValNat 2 (3^(2^k) - 1) + 1 =
  --     padicValNat 2 (3 + 1) + padicValNat 2 (3 - 1) + padicValNat 2 (2^k)
  have h3p1 : padicValNat 2 (3 + 1 : ℕ) = 2 := by
    show padicValNat 2 4 = 2
    rw [show (4 : ℕ) = 2^2 from by norm_num]
    exact padicValNat.prime_pow 2
  have h3m1 : padicValNat 2 (3 - 1 : ℕ) = 1 := by
    show padicValNat 2 2 = 1
    exact padicValNat.self (by norm_num : 1 < 2)
  have h2k : padicValNat 2 (2 ^ k) = k := padicValNat.prime_pow k
  rw [h3p1, h3m1, h2k] at h
  omega

/-! ## Step 2: Hensel shift `N(i + 2^k) ≡ N i + 2^k (mod 2^(k+1))`

The key lemma. Directly from LTE, `2 · (3^(2^k) − 1)` has `v₂ ≥ k + 3`,
hence contributes zero to `N(i + 2^k) − N(i)` modulo `2^(k+1)`. -/

/-- `2^(k+3)` divides `2·3^i·(3^(2^k) − 1)` for `k ≥ 1`, `i ≥ 0`. -/
lemma pow_k_plus_three_dvd (i k : ℕ) (hk : 1 ≤ k) :
    (2 ^ (k + 3) : ℕ) ∣ 2 * 3 ^ i * (3 ^ (2 ^ k) - 1) := by
  have h_lte := lte_three_pow_two_pow_sub_one k hk
  -- h_lte : padicValNat 2 (3^(2^k) − 1) = k + 2
  have h_pos : 0 < 3 ^ (2 ^ k) - 1 := by
    have h1 : 1 < 3 ^ (2 ^ k) := by
      apply Nat.one_lt_pow (by positivity) (by norm_num)
    omega
  have h_dvd_main : (2 ^ (k + 2) : ℕ) ∣ 3 ^ (2 ^ k) - 1 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (padicValNat_dvd_iff_le h_pos.ne').mpr (by rw [h_lte])
  -- Now `2 * x * y` for `2^(k+2) ∣ y` and the factor `2` on the left
  -- gives `2^(k+3) ∣ 2·3^i·y`, since `3^i` is odd and doesn't contribute
  -- to the 2-adic valuation.
  obtain ⟨m, hm⟩ := h_dvd_main
  refine ⟨3 ^ i * m, ?_⟩
  rw [hm]; ring

/-- `3^(2^k) ≡ 1 (mod 2^(k+1))` for `k ≥ 1`. A direct consequence of
`lte_three_pow_two_pow_sub_one`. -/
lemma three_pow_two_pow_modEq_one (k : ℕ) (hk : 1 ≤ k) :
    (3 : ℕ) ^ (2 ^ k) ≡ 1 [MOD 2 ^ (k + 1)] := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_gt : 1 < (3 : ℕ) ^ (2 ^ k) :=
    Nat.one_lt_pow (by positivity) (by norm_num)
  have h_dvd : (2 ^ (k + 2) : ℕ) ∣ (3 : ℕ) ^ (2 ^ k) - 1 := by
    refine (padicValNat_dvd_iff_le (by omega)).mpr ?_
    rw [lte_three_pow_two_pow_sub_one k hk]
  have h_cong_strong : (1 : ℕ) ≡ (3 : ℕ) ^ (2 ^ k) [MOD 2 ^ (k + 2)] :=
    (Nat.modEq_iff_dvd' (by omega : (1 : ℕ) ≤ 3 ^ (2 ^ k))).mpr h_dvd
  exact (h_cong_strong.symm).of_dvd (pow_dvd_pow 2 (by omega : k + 1 ≤ k + 2))

/-- **Hensel shift lemma**. For `i : ℕ`, `k ≥ 1`:
`N(i + 2^k) ≡ N i + 2^k (mod 2^(k+1))`. -/
lemma hensel_shift (i k : ℕ) (hk : 1 ≤ k) :
    N (i + 2 ^ k) ≡ N i + 2 ^ k [MOD 2 ^ (k + 1)] := by
  have h_cong : (3 : ℕ) ^ (2 ^ k) ≡ 1 [MOD 2 ^ (k + 1)] :=
    three_pow_two_pow_modEq_one k hk
  have h_pow_add : (3 : ℕ) ^ (i + 2 ^ k) = 3 ^ i * 3 ^ (2 ^ k) := pow_add 3 i (2 ^ k)
  have h_pow_mul : (3 : ℕ) ^ (i + 2 ^ k) ≡ 3 ^ i [MOD 2 ^ (k + 1)] := by
    rw [h_pow_add]
    have := h_cong.mul_left (3 ^ i)
    simpa using this
  have h_mul : (2 : ℕ) * 3 ^ (i + 2 ^ k) ≡ 2 * 3 ^ i [MOD 2 ^ (k + 1)] :=
    h_pow_mul.mul_left 2
  -- N (i + 2^k) = 2 * 3^(i + 2^k) + (i + 2^k) + 5
  -- N i + 2^k  = 2 * 3^i + i + 5 + 2^k
  show 2 * 3 ^ (i + 2 ^ k) + (i + 2 ^ k) + 5 ≡ 2 * 3 ^ i + i + 5 + 2 ^ k [MOD 2 ^ (k + 1)]
  have h_rearr_lhs : 2 * 3 ^ (i + 2 ^ k) + (i + 2 ^ k) + 5
                      = 2 * 3 ^ (i + 2 ^ k) + (i + 2 ^ k + 5) := by ring
  have h_rearr_rhs : 2 * 3 ^ i + i + 5 + 2 ^ k
                      = 2 * 3 ^ i + (i + 2 ^ k + 5) := by ring
  rw [h_rearr_lhs, h_rearr_rhs]
  exact h_mul.add_right _

/-! ## Step 3: Residue sequence `r`

We need a single definition of `r` that is both:

* **mathematically correct** — satisfies the natural Hensel recursion
  `r (k+1) = r k` if `2^(k+1) ∣ N (r k)`, else `r k + 2^k`, and
* **computable** via `native_decide` for `k = 80`, where `r 80` is a
  ~24-digit number.

The obstacle: the natural recursion involves `N (r k) = 2·3^(r k) + r k + 5`,
and for `r k ≈ 2^60`, `3^(r k)` has ~10^{18} bits — not computable even
with GMP.

**Solution**: track the auxiliary state `(3^(r k) mod 2^81, 3^(2^k) mod 2^81)`
alongside `r k`. The branching condition `N (r k) ≡ 0 (mod 2^(k+1))` can
be checked using the stored `3^(r k) mod 2^81` without ever computing
the full exponential, as long as `k + 1 ≤ 81`.
-/

/-- Efficient state: `(r k, er, et)` with invariant
`er = 3^(r k) mod 2^81` and `et = 3^(2^k) mod 2^81`. -/
def rState : ℕ → (ℕ × ℕ × ℕ)
  | 0 => (0, 1 % 2 ^ 81, 3 % 2 ^ 81)
  | k + 1 =>
      if (2 * (rState k).2.1 + (rState k).1 + 5) % 2 ^ (k + 1) = 0 then
        ((rState k).1, (rState k).2.1, ((rState k).2.2 * (rState k).2.2) % 2 ^ 81)
      else
        ((rState k).1 + 2 ^ k,
          ((rState k).2.1 * (rState k).2.2) % 2 ^ 81,
          ((rState k).2.2 * (rState k).2.2) % 2 ^ 81)

/-- The Hensel-lifted residue `r k ∈ [0, 2^k)`, defined via `rState`. -/
def r (k : ℕ) : ℕ := (rState k).1

/-- The auxiliary `3^(r k) mod 2^81`. -/
private def rE (k : ℕ) : ℕ := (rState k).2.1

/-- The auxiliary `3^(2^k) mod 2^81`. -/
private def rT (k : ℕ) : ℕ := (rState k).2.2

@[simp] lemma r_zero : r 0 = 0 := rfl

@[simp] lemma rE_zero : rE 0 = 1 % 2 ^ 81 := rfl

@[simp] lemma rT_zero : rT 0 = 3 % 2 ^ 81 := rfl

/-- `rT (k+1) = (rT k)^2 mod 2^81`, independent of the branch. -/
lemma rT_succ (k : ℕ) : rT (k + 1) = (rT k * rT k) % 2 ^ 81 := by
  change (if (2 * (rState k).2.1 + (rState k).1 + 5) % 2 ^ (k + 1) = 0 then
            ((rState k).1, (rState k).2.1, ((rState k).2.2 * (rState k).2.2) % 2 ^ 81)
          else
            ((rState k).1 + 2 ^ k,
              ((rState k).2.1 * (rState k).2.2) % 2 ^ 81,
              ((rState k).2.2 * (rState k).2.2) % 2 ^ 81)).2.2 = _
  split_ifs <;> rfl

/-- True branch: `r (k+1) = r k` and `rE (k+1) = rE k` when condition holds. -/
lemma r_rE_succ_of_cond (k : ℕ)
    (h : (2 * rE k + r k + 5) % 2 ^ (k + 1) = 0) :
    r (k + 1) = r k ∧ rE (k + 1) = rE k := by
  have h' : (2 * (rState k).2.1 + (rState k).1 + 5) % 2 ^ (k + 1) = 0 := h
  refine ⟨?_, ?_⟩
  · change (if (2 * (rState k).2.1 + (rState k).1 + 5) % 2 ^ (k + 1) = 0 then
              ((rState k).1, (rState k).2.1, ((rState k).2.2 * (rState k).2.2) % 2 ^ 81)
            else
              ((rState k).1 + 2 ^ k,
                ((rState k).2.1 * (rState k).2.2) % 2 ^ 81,
                ((rState k).2.2 * (rState k).2.2) % 2 ^ 81)).1 = (rState k).1
    rw [if_pos h']
  · change (if (2 * (rState k).2.1 + (rState k).1 + 5) % 2 ^ (k + 1) = 0 then
              ((rState k).1, (rState k).2.1, ((rState k).2.2 * (rState k).2.2) % 2 ^ 81)
            else
              ((rState k).1 + 2 ^ k,
                ((rState k).2.1 * (rState k).2.2) % 2 ^ 81,
                ((rState k).2.2 * (rState k).2.2) % 2 ^ 81)).2.1 = (rState k).2.1
    rw [if_pos h']

/-- False branch: `r (k+1) = r k + 2^k` and `rE (k+1) = (rE k * rT k) mod 2^81`. -/
lemma r_rE_succ_of_not_cond (k : ℕ)
    (h : (2 * rE k + r k + 5) % 2 ^ (k + 1) ≠ 0) :
    r (k + 1) = r k + 2 ^ k ∧ rE (k + 1) = (rE k * rT k) % 2 ^ 81 := by
  have h' : (2 * (rState k).2.1 + (rState k).1 + 5) % 2 ^ (k + 1) ≠ 0 := h
  refine ⟨?_, ?_⟩
  · change (if (2 * (rState k).2.1 + (rState k).1 + 5) % 2 ^ (k + 1) = 0 then
              ((rState k).1, (rState k).2.1, ((rState k).2.2 * (rState k).2.2) % 2 ^ 81)
            else
              ((rState k).1 + 2 ^ k,
                ((rState k).2.1 * (rState k).2.2) % 2 ^ 81,
                ((rState k).2.2 * (rState k).2.2) % 2 ^ 81)).1 = (rState k).1 + 2 ^ k
    rw [if_neg h']
  · change (if (2 * (rState k).2.1 + (rState k).1 + 5) % 2 ^ (k + 1) = 0 then
              ((rState k).1, (rState k).2.1, ((rState k).2.2 * (rState k).2.2) % 2 ^ 81)
            else
              ((rState k).1 + 2 ^ k,
                ((rState k).2.1 * (rState k).2.2) % 2 ^ 81,
                ((rState k).2.2 * (rState k).2.2) % 2 ^ 81)).2.1 =
            ((rState k).2.1 * (rState k).2.2) % 2 ^ 81
    rw [if_neg h']

/-- `r (k+1)` is either `r k` or `r k + 2^k`. -/
lemma r_succ_cases (k : ℕ) : r (k + 1) = r k ∨ r (k + 1) = r k + 2 ^ k := by
  by_cases h : (2 * rE k + r k + 5) % 2 ^ (k + 1) = 0
  · exact Or.inl (r_rE_succ_of_cond k h).1
  · exact Or.inr (r_rE_succ_of_not_cond k h).1

/-- `r k < 2^k`. -/
lemma r_lt_two_pow (k : ℕ) : r k < 2 ^ k := by
  induction k with
  | zero => show (0 : ℕ) < 1; omega
  | succ k ih =>
    rcases r_succ_cases k with h | h
    · rw [h]; exact lt_of_lt_of_le ih (by omega : 2 ^ k ≤ 2 ^ (k + 1))
    · rw [h, pow_succ]; omega

/-- Joint invariant:
`rE k ≡ 3^(r k) [MOD 2^81]` and `rT k ≡ 3^(2^k) [MOD 2^81]`. -/
lemma rE_rT_invariant (k : ℕ) :
    rE k ≡ 3 ^ (r k) [MOD 2 ^ 81] ∧ rT k ≡ 3 ^ (2 ^ k) [MOD 2 ^ 81] := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · show (1 % 2 ^ 81 : ℕ) ≡ 3 ^ 0 [MOD 2 ^ 81]
      simp [Nat.ModEq]
    · show (3 % 2 ^ 81 : ℕ) ≡ 3 ^ (2 ^ 0) [MOD 2 ^ 81]
      simp [Nat.ModEq]
  | succ k ih =>
    obtain ⟨ihE, ihT⟩ := ih
    -- First, rT (k+1) = rT k * rT k mod 2^81, regardless of branch.
    have h_rT_next : rT (k + 1) ≡ 3 ^ (2 ^ (k + 1)) [MOD 2 ^ 81] := by
      rw [rT_succ]
      have h_mul : rT k * rT k ≡ 3 ^ (2 ^ k) * 3 ^ (2 ^ k) [MOD 2 ^ 81] :=
        ihT.mul ihT
      have h_pow : (3 : ℕ) ^ (2 ^ k) * 3 ^ (2 ^ k) = 3 ^ (2 ^ (k + 1)) := by
        rw [← pow_add, pow_succ]; ring_nf
      rw [h_pow] at h_mul
      exact (Nat.mod_modEq _ _).trans h_mul
    refine ⟨?_, h_rT_next⟩
    -- Case split on the branching condition.
    by_cases hcond : (2 * rE k + r k + 5) % 2 ^ (k + 1) = 0
    · -- True branch
      obtain ⟨hr, hE⟩ := r_rE_succ_of_cond k hcond
      rw [hE, hr]
      exact ihE
    · -- False branch
      obtain ⟨hr, hE⟩ := r_rE_succ_of_not_cond k hcond
      rw [hE, hr]
      have h_mul : rE k * rT k ≡ 3 ^ (r k) * 3 ^ (2 ^ k) [MOD 2 ^ 81] :=
        ihE.mul ihT
      have h_pow : (3 : ℕ) ^ (r k) * 3 ^ (2 ^ k) = 3 ^ (r k + 2 ^ k) := by
        rw [← pow_add]
      rw [h_pow] at h_mul
      exact (Nat.mod_modEq _ _).trans h_mul

lemma rE_modEq (k : ℕ) : rE k ≡ 3 ^ (r k) [MOD 2 ^ 81] := (rE_rT_invariant k).1

lemma rT_modEq (k : ℕ) : rT k ≡ 3 ^ (2 ^ k) [MOD 2 ^ 81] := (rE_rT_invariant k).2

/-! ## Step 4: Structural characterization

The goal: for `1 ≤ k ≤ 80`, `2^k ∣ N i ↔ i ≡ r k [MOD 2^k]`.

This proceeds by induction on `k`, using:
* Iterated Hensel shift (periodicity of `N` on the coarser lattice)
* The condition `(2·rE k + r k + 5) % 2^(k+1) = 0` captures `2^(k+1) ∣ N (r k)` for `k ≤ 80`
* Consequently `2^k ∣ N (r k)` for `k ≤ 80`. -/

/-- Iterated Hensel shift: for `k ≥ 1`, `N(i + m·2^k) ≡ N i + m·2^k (mod 2^(k+1))`. -/
lemma hensel_shift_iter (i k m : ℕ) (hk : 1 ≤ k) :
    N (i + m * 2 ^ k) ≡ N i + m * 2 ^ k [MOD 2 ^ (k + 1)] := by
  induction m with
  | zero => simp [Nat.ModEq]
  | succ m ih =>
    have h_rw : i + (m + 1) * 2 ^ k = (i + m * 2 ^ k) + 2 ^ k := by ring
    have h_rw_rhs : N i + (m + 1) * 2 ^ k = (N i + m * 2 ^ k) + 2 ^ k := by ring
    rw [h_rw, h_rw_rhs]
    have h2 := hensel_shift (i + m * 2 ^ k) k hk
    -- h2 : N ((i + m·2^k) + 2^k) ≡ N (i + m·2^k) + 2^k [MOD 2^(k+1)]
    exact h2.trans (ih.add_right _)

/-- Periodicity: if `i ≡ j [MOD 2^(k+1)]` then `N i ≡ N j [MOD 2^(k+1)]`, for `k ≥ 1`. -/
lemma N_modEq_of_modEq (i j k : ℕ) (hk : 1 ≤ k) (h : i ≡ j [MOD 2 ^ (k + 1)]) :
    N i ≡ N j [MOD 2 ^ (k + 1)] := by
  -- Use hensel_shift_iter with an offset: write i = j + ⌊(i - j) / 2^(k+1)⌋ · 2^(k+1) in ℤ.
  -- Simpler: since Nat.ModEq is equivalent to the integer relation, go via integers.
  -- But avoid: just case-split on i vs j.
  rcases Nat.le_total i j with hij | hij
  · -- j = i + d, d = j - i, 2^(k+1) ∣ d
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
    have hd : 2 ^ (k + 1) ∣ d := by
      have := (Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).mp h
      simp at this; exact this
    obtain ⟨q, rfl⟩ := hd
    -- Goal: N i ≡ N (i + 2^(k+1) * q) [MOD 2^(k+1)]
    symm
    have h_rw : 2 ^ (k + 1) * q = (2 * q) * 2 ^ k := by
      rw [pow_succ]; ring
    rw [h_rw]
    have := hensel_shift_iter i k (2 * q) hk
    -- this : N (i + 2 * q * 2^k) ≡ N i + 2 * q * 2^k [MOD 2^(k+1)]
    have h_zero : (2 * q) * 2 ^ k ≡ 0 [MOD 2 ^ (k + 1)] := by
      show _ % _ = _ % _
      rw [Nat.zero_mod]
      have h_eq : (2 * q) * 2 ^ k = q * 2 ^ (k + 1) := by rw [pow_succ]; ring
      rw [h_eq]
      exact Nat.mul_mod_left _ _
    have h_comb : N i + (2 * q) * 2 ^ k ≡ N i + 0 [MOD 2 ^ (k + 1)] :=
      (Nat.ModEq.refl (N i)).add h_zero
    rw [Nat.add_zero] at h_comb
    exact this.trans h_comb
  · -- i = j + d
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
    have hd : 2 ^ (k + 1) ∣ d := by
      have := (Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).mp h.symm
      simp at this; exact this
    obtain ⟨q, rfl⟩ := hd
    have h_rw : 2 ^ (k + 1) * q = (2 * q) * 2 ^ k := by
      rw [pow_succ]; ring
    rw [h_rw]
    have := hensel_shift_iter j k (2 * q) hk
    have h_zero : (2 * q) * 2 ^ k ≡ 0 [MOD 2 ^ (k + 1)] := by
      show _ % _ = _ % _
      rw [Nat.zero_mod]
      have h_eq : (2 * q) * 2 ^ k = q * 2 ^ (k + 1) := by rw [pow_succ]; ring
      rw [h_eq]
      exact Nat.mul_mod_left _ _
    have h_comb : N j + (2 * q) * 2 ^ k ≡ N j + 0 [MOD 2 ^ (k + 1)] :=
      (Nat.ModEq.refl (N j)).add h_zero
    rw [Nat.add_zero] at h_comb
    exact this.trans h_comb

/-- For `k ≤ 80`, the branching condition captures `2^(k+1) ∣ N (r k)`. -/
lemma cond_iff_dvd_N_r (k : ℕ) (hk : k ≤ 80) :
    (2 * rE k + r k + 5) % 2 ^ (k + 1) = 0 ↔ 2 ^ (k + 1) ∣ N (r k) := by
  have h_rE_modLow : rE k ≡ 3 ^ (r k) [MOD 2 ^ (k + 1)] :=
    (rE_modEq k).of_dvd (pow_dvd_pow 2 (by omega : k + 1 ≤ 81))
  have h_lhs : 2 * rE k + r k + 5 ≡ N (r k) [MOD 2 ^ (k + 1)] := by
    unfold N
    exact ((h_rE_modLow.mul_left 2).add_right _).add_right _
  constructor
  · intro h
    have h_zero : (2 * rE k + r k + 5) ≡ 0 [MOD 2 ^ (k + 1)] := by
      rw [Nat.ModEq, Nat.zero_mod]; exact h
    exact Nat.modEq_zero_iff_dvd.mp (h_zero.symm.trans h_lhs).symm
  · intro h
    have h0 : N (r k) ≡ 0 [MOD 2 ^ (k + 1)] := Nat.modEq_zero_iff_dvd.mpr h
    have h_zero := h_lhs.trans h0
    rwa [Nat.ModEq, Nat.zero_mod] at h_zero

/-- `2^k ∣ N (r k)` for `k ≤ 80`. -/
lemma dvd_N_r (k : ℕ) (hk : k ≤ 80) : (2 : ℕ) ^ k ∣ N (r k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k ≤ 80 := by omega
    have hk1 : 1 ≤ k + 1 := by omega
    have ih' := ih hk'
    by_cases hcond : (2 * rE k + r k + 5) % 2 ^ (k + 1) = 0
    · -- True branch: r (k+1) = r k, and the condition gives 2^(k+1) ∣ N (r k)
      obtain ⟨hr, _⟩ := r_rE_succ_of_cond k hcond
      rw [hr]
      exact (cond_iff_dvd_N_r k hk').mp hcond
    · -- False branch: r (k+1) = r k + 2^k
      obtain ⟨hr, _⟩ := r_rE_succ_of_not_cond k hcond
      rw [hr]
      -- We have 2^k ∣ N (r k), but not 2^(k+1). By Hensel shift,
      -- N (r k + 2^k) ≡ N (r k) + 2^k [MOD 2^(k+1)], and the extra 2^k flips parity.
      have h_not_dvd : ¬ (2 ^ (k + 1) ∣ N (r k)) := by
        intro h; exact hcond ((cond_iff_dvd_N_r k hk').mpr h)
      -- N (r k) = 2^k * a with a odd
      obtain ⟨a, ha⟩ := ih'
      have h_a_odd : Odd a := by
        by_contra h_even
        rw [Nat.not_odd_iff_even] at h_even
        obtain ⟨b, rfl⟩ := h_even
        apply h_not_dvd
        rw [ha]
        refine ⟨b, ?_⟩
        rw [pow_succ]; ring
      -- Now N (r k + 2^k) ≡ N (r k) + 2^k ≡ 2^k * a + 2^k = 2^k * (a + 1) [MOD 2^(k+1)]
      by_cases hk0 : k = 0
      · -- k = 0: r 0 = 0, so N (0 + 1) = N 1 = 12, and 2 ∣ 12.
        subst hk0
        show 2 ^ 1 ∣ N (r 0 + 2 ^ 0)
        show (2 : ℕ) ∣ N 1
        unfold N; decide
      · -- k ≥ 1: apply hensel_shift
        have hk_ge_1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        have h_shift := hensel_shift (r k) k hk_ge_1
        -- h_shift : N (r k + 2^k) ≡ N (r k) + 2^k [MOD 2^(k+1)]
        obtain ⟨b, hb⟩ := h_a_odd
        -- a = 2b + 1, so N (r k) = 2^k * (2b + 1)
        -- N (r k) + 2^k = 2^k * (2b + 1) + 2^k = 2^k * (2b + 2) = 2^(k+1) * (b + 1)
        have h_dvd_right : 2 ^ (k + 1) ∣ N (r k) + 2 ^ k := by
          rw [ha, hb]
          refine ⟨b + 1, ?_⟩
          rw [pow_succ]; ring
        -- Combine h_shift and h_dvd_right
        have h_modEq_zero : N (r k + 2 ^ k) ≡ 0 [MOD 2 ^ (k + 1)] := by
          exact h_shift.trans ((Nat.modEq_zero_iff_dvd).mpr h_dvd_right)
        exact (Nat.modEq_zero_iff_dvd).mp h_modEq_zero

/-- **Backward direction of the characterization**: if `i ≡ r k [MOD 2^k]` then `2^k ∣ N i`.
The easier half: uses periodicity (`N_modEq_of_modEq`) and `dvd_N_r`. -/
lemma dvd_N_of_cong (k : ℕ) (hk : k ≤ 80) (i : ℕ) (h_cong : i ≡ r k [MOD 2 ^ k]) :
    (2 : ℕ) ^ k ∣ N i := by
  have h_dvd_Nr : (2 : ℕ) ^ k ∣ N (r k) := dvd_N_r k hk
  by_cases hk0 : k = 0
  · subst hk0; simp
  · -- Need k ≥ 1 for N_modEq_of_modEq
    -- Hmm, N_modEq_of_modEq is stated for 2^(k+1), let's use k' = k - 1.
    -- Actually easier: apply it with the appropriate exponent.
    by_cases hk1 : k = 1
    · -- k = 1 case: check directly.
      subst hk1
      have hr1 : r 1 = 1 := by decide
      rw [hr1] at h_cong
      have h_i_odd : i % 2 = 1 := by rwa [Nat.ModEq] at h_cong
      show (2 : ℕ) ∣ N i
      unfold N
      omega
    · -- k ≥ 2: write k = (k-1) + 1 and apply N_modEq_of_modEq
      have hk_ge_2 : 2 ≤ k := by omega
      have hk_ge_1' : 1 ≤ k - 1 := by omega
      have h_rw : k = (k - 1) + 1 := by omega
      rw [h_rw] at h_cong ⊢
      have h_N_modEq : N i ≡ N (r ((k - 1) + 1)) [MOD 2 ^ ((k - 1) + 1)] :=
        N_modEq_of_modEq i (r ((k - 1) + 1)) (k - 1) hk_ge_1' h_cong
      have h_dvd' : (2 : ℕ) ^ ((k - 1) + 1) ∣ N (r ((k - 1) + 1)) := by
        rw [← h_rw]; exact h_dvd_Nr
      exact Nat.modEq_zero_iff_dvd.mp
        (h_N_modEq.trans (Nat.modEq_zero_iff_dvd.mpr h_dvd'))

/-- **Forward direction**: the inductive step. If `2^(k+1) ∣ N i` and the characterization
holds at `k`, then `i ≡ r (k+1) [MOD 2^(k+1)]`. -/
lemma cong_of_dvd_succ (k : ℕ) (hk : k + 1 ≤ 80)
    (ihk : ∀ j, (2 : ℕ) ^ k ∣ N j ↔ j ≡ r k [MOD 2 ^ k])
    (i : ℕ) (h_div : (2 : ℕ) ^ (k + 1) ∣ N i) :
    i ≡ r (k + 1) [MOD 2 ^ (k + 1)] := by
  have hk' : k ≤ 80 := by omega
  have h_k_div : (2 : ℕ) ^ k ∣ N i := dvd_trans (pow_dvd_pow 2 (Nat.le_succ k)) h_div
  have h_cong_k : i ≡ r k [MOD 2 ^ k] := (ihk i).mp h_k_div
  have hrk_lt : r k < 2 ^ k := r_lt_two_pow k
  have hrk_pow_pos : (0 : ℕ) < 2 ^ k := by positivity
  have h_i_mod : i % 2 ^ k = r k := by
    have h_mod_eq : i % 2 ^ k = r k % 2 ^ k := h_cong_k
    rwa [Nat.mod_eq_of_lt hrk_lt] at h_mod_eq
  -- Get a witness m such that i = r k + m * 2^k.
  obtain ⟨m, hm_eq⟩ : ∃ m, i = r k + m * 2 ^ k := by
    refine ⟨i / 2 ^ k, ?_⟩
    have h1 := Nat.div_add_mod i (2 ^ k)
    rw [h_i_mod] at h1
    have h_comm : 2 ^ k * (i / 2 ^ k) = (i / 2 ^ k) * 2 ^ k := Nat.mul_comm _ _
    omega
  rw [hm_eq] at h_div
  rw [hm_eq]
  -- Now the goal is about r k + m * 2^k.
  by_cases hk0 : k = 0
  · -- k = 0 base case: r 0 = 0, 2^0 = 1, so `r k + m * 2^k = m`.
    subst hk0
    have hr1 : r 1 = 1 := by decide
    rw [hr1]
    simp only [r_zero, pow_zero, Nat.mul_one, Nat.zero_add] at h_div ⊢
    show m ≡ 1 [MOD 2]
    unfold N at h_div
    rw [Nat.ModEq]
    omega
  · have hk_ge_1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    have h_shift := hensel_shift_iter (r k) k m hk_ge_1
    have h_dvd_sum : (2 : ℕ) ^ (k + 1) ∣ N (r k) + m * 2 ^ k := by
      have h_nz : N (r k + m * 2 ^ k) ≡ 0 [MOD 2 ^ (k + 1)] :=
        Nat.modEq_zero_iff_dvd.mpr h_div
      exact Nat.modEq_zero_iff_dvd.mp (h_shift.symm.trans h_nz)
    have h_N_r_dvd : (2 : ℕ) ^ k ∣ N (r k) := dvd_N_r k hk'
    obtain ⟨a, ha⟩ := h_N_r_dvd
    rw [ha] at h_dvd_sum
    have h_2_dvd_sum : 2 ∣ a + m := by
      have h_factor : (2 : ℕ) ^ k * a + m * 2 ^ k = 2 ^ k * (a + m) := by ring
      rw [h_factor] at h_dvd_sum
      rw [pow_succ] at h_dvd_sum
      exact (Nat.mul_dvd_mul_iff_left hrk_pow_pos).mp h_dvd_sum
    by_cases hcond : (2 * rE k + r k + 5) % 2 ^ (k + 1) = 0
    · -- True branch: r (k+1) = r k, 2^(k+1) ∣ N (r k), a even, m even.
      have h_N_dvd_k1 : (2 : ℕ) ^ (k + 1) ∣ N (r k) := (cond_iff_dvd_N_r k hk').mp hcond
      rw [ha, pow_succ] at h_N_dvd_k1
      have h_2_dvd_a : 2 ∣ a :=
        (Nat.mul_dvd_mul_iff_left hrk_pow_pos).mp h_N_dvd_k1
      have h_2_dvd_m : 2 ∣ m := by omega
      obtain ⟨m', rfl⟩ := h_2_dvd_m
      have hr_eq : r (k + 1) = r k := (r_rE_succ_of_cond k hcond).1
      rw [hr_eq]
      show r k + 2 * m' * 2 ^ k ≡ r k [MOD 2 ^ (k + 1)]
      have h_rw : 2 * m' * 2 ^ k = m' * 2 ^ (k + 1) := by rw [pow_succ]; ring
      rw [h_rw]
      show (r k + m' * 2 ^ (k + 1)) % 2 ^ (k + 1) = r k % 2 ^ (k + 1)
      rw [Nat.add_mul_mod_self_right]
    · -- False branch: r (k+1) = r k + 2^k, 2^(k+1) ∤ N (r k), a odd, m odd.
      have h_not : ¬ ((2 : ℕ) ^ (k + 1) ∣ N (r k)) :=
        fun h => hcond ((cond_iff_dvd_N_r k hk').mpr h)
      have h_a_odd : ¬ (2 ∣ a) := by
        intro h_even
        apply h_not
        obtain ⟨a', rfl⟩ := h_even
        rw [ha, pow_succ]; refine ⟨a', ?_⟩; ring
      have h_m_odd : ¬ (2 ∣ m) := by intro h_even; exact h_a_odd (by omega)
      have h_m_form : m = 2 * (m / 2) + 1 := by omega
      have hr_eq : r (k + 1) = r k + 2 ^ k := (r_rE_succ_of_not_cond k hcond).1
      rw [hr_eq]
      show r k + m * 2 ^ k ≡ r k + 2 ^ k [MOD 2 ^ (k + 1)]
      conv_lhs => rw [h_m_form]
      have h_rw : r k + (2 * (m / 2) + 1) * 2 ^ k
                  = (r k + 2 ^ k) + (m / 2) * 2 ^ (k + 1) := by
        rw [pow_succ]; ring
      rw [h_rw]
      show ((r k + 2 ^ k) + (m / 2) * 2 ^ (k + 1)) % 2 ^ (k + 1)
            = (r k + 2 ^ k) % 2 ^ (k + 1)
      rw [Nat.add_mul_mod_self_right]

/-- **Structural characterization**: for `k ≤ 80`, the set of `i` such
that `2^k ∣ N i` is the arithmetic progression `i ≡ r k (mod 2^k)`. -/
theorem dvd_N_iff (k : ℕ) (hk : k ≤ 80) :
    ∀ i, (2 : ℕ) ^ k ∣ N i ↔ i ≡ r k [MOD 2 ^ k] := by
  induction k with
  | zero =>
    intro i
    refine ⟨fun _ => ?_, fun _ => one_dvd _⟩
    exact (Nat.modEq_one : i ≡ r 0 [MOD 1])
  | succ k ih =>
    have hk' : k ≤ 80 := by omega
    intro i
    refine ⟨fun h_div => cong_of_dvd_succ k hk (ih hk') i h_div, fun h_cong => ?_⟩
    exact dvd_N_of_cong (k + 1) hk i h_cong

/-! ## Step 5: Computational check `r 80 ≥ 2^60` -/

/-- `r 80 ≥ 2^60`, verified by native compilation of the efficient
`rState` recursion. The actual value is `r 80 ≈ 1.06·10^24`. -/
theorem r_80_ge_pommeThreshold : r 80 ≥ 2 ^ 60 := by
  native_decide

/-! ## Step 6: Structural corollary — for `i < 2^60`, `v₂(N i) < 80` -/

/-- For `i ∈ [0, 2^60)`, `v₂(N i) < 80`. -/
theorem padicValNat_N_lt_80 (i : ℕ) (hi_hi : i < 2 ^ 60) :
    padicValNat 2 (N i) < 80 := by
  by_contra h
  push_neg at h
  -- h : 80 ≤ padicValNat 2 (N i), so 2^80 ∣ N i
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_N_pos : N i ≠ 0 := by
    unfold N
    positivity
  have h_dvd : (2 : ℕ) ^ 80 ∣ N i := (padicValNat_dvd_iff_le h_N_pos).mpr h
  -- By dvd_N_iff: i ≡ r 80 [MOD 2^80]
  have h_cong : i ≡ r 80 [MOD 2 ^ 80] := (dvd_N_iff 80 (le_refl _) i).mp h_dvd
  -- So i % 2^80 = r 80 % 2^80 = r 80 (since r 80 < 2^80)
  have hr_lt : r 80 < 2 ^ 80 := r_lt_two_pow 80
  have hi_mod : i % 2 ^ 80 = r 80 := by
    have : i % 2 ^ 80 = r 80 % 2 ^ 80 := h_cong
    rwa [Nat.mod_eq_of_lt hr_lt] at this
  -- Since i < 2^60 < 2^80, i % 2^80 = i
  have hi_lt : i < 2 ^ 80 := lt_of_lt_of_le hi_hi (by norm_num : (2 : ℕ) ^ 60 ≤ 2 ^ 80)
  rw [Nat.mod_eq_of_lt hi_lt] at hi_mod
  -- So i = r 80. But r 80 ≥ 2^60 and i < 2^60: contradiction.
  have := r_80_ge_pommeThreshold
  omega

/-! ## Step 7: Analytic closure — for `i ≥ 54`, `(i + 7)·2^79 ≤ 3^i` -/

/-- For `i ≥ 54`, `(i + 7)·2^79 ≤ 3^i`. Proved by induction with base case `i = 54`. -/
lemma three_pow_dominates (i : ℕ) (hi : 54 ≤ i) : (i + 7) * 2 ^ 79 ≤ 3 ^ i := by
  induction i, hi using Nat.le_induction with
  | base => native_decide
  | succ i hi ih =>
    -- (i + 8) * 2^79 ≤ 3 * (i + 7) * 2^79 ≤ 3 * 3^i = 3^(i+1)
    calc (i + 1 + 7) * 2 ^ 79
        = (i + 8) * 2 ^ 79 := by ring
      _ ≤ 3 * ((i + 7) * 2 ^ 79) := by nlinarith [hi]
      _ ≤ 3 * 3 ^ i := Nat.mul_le_mul_left 3 ih
      _ = 3 ^ (i + 1) := by rw [pow_succ]; ring

/-- For `i ≥ 54` and `i < 2^60`, the closure inequality holds. -/
lemma pomme_ineq_large (i : ℕ) (hi_lo : 54 ≤ i) (hi_hi : i < 2 ^ 60) :
    2 * i + 14 ≤ N i / 2 ^ padicValNat 2 (N i) := by
  -- Bound v₂ < 80, so 2^{v₂} ≤ 2^79.
  have h_v2_lt : padicValNat 2 (N i) < 80 := padicValNat_N_lt_80 i hi_hi
  have h_v2_le : padicValNat 2 (N i) ≤ 79 := by omega
  -- Compute: (2i + 14) * 2^{v₂} ≤ (2i + 14) * 2^79 ≤ 2 * 3^i ≤ N i.
  have h_N_ge : (2 * i + 14) * 2 ^ (padicValNat 2 (N i)) ≤ N i := by
    have h_2_79 : (2 * i + 14) * 2 ^ (padicValNat 2 (N i)) ≤ (2 * i + 14) * 2 ^ 79 := by
      apply Nat.mul_le_mul_left
      exact Nat.pow_le_pow_right (by norm_num) h_v2_le
    have h_3i : (2 * i + 14) * 2 ^ 79 ≤ 2 * 3 ^ i := by
      have h_dom := three_pow_dominates i hi_lo
      -- (i + 7) * 2^79 ≤ 3^i  ⟹  (2i + 14) * 2^79 ≤ 2 * 3^i
      calc (2 * i + 14) * 2 ^ 79
          = 2 * ((i + 7) * 2 ^ 79) := by ring
        _ ≤ 2 * 3 ^ i := Nat.mul_le_mul_left 2 h_dom
    have h_N_bound : 2 * 3 ^ i ≤ N i := by unfold N; omega
    linarith
  -- Now (2i + 14) * 2^{v₂} ≤ N i, so 2i + 14 ≤ N i / 2^{v₂}.
  have h_pow_pos : 0 < 2 ^ padicValNat 2 (N i) := by positivity
  exact (Nat.le_div_iff_mul_le h_pow_pos).mpr (by linarith)

/-! ## Step 8: Base case `i ∈ [50, 53]` and full `pomme_small_range_proved` -/

/-- The base case: `i ∈ {50, 51, 52, 53}` by direct computation. -/
lemma pomme_ineq_base (i : ℕ) (hi_lo : 50 ≤ i) (hi_hi : i < 54) :
    2 * i + 14 ≤ N i / 2 ^ padicValNat 2 (N i) := by
  interval_cases i <;> (unfold N; native_decide)

/-- **Main result for the small-`i` range**: the range `50 ≤ i < 2^60`
is dispatched mathematically, eliminating the `pomme_small_range`
axiom entirely. -/
theorem pomme_small_range_proved
    (i : ℕ) (hi_lo : 50 ≤ i) (hi_hi : i < 2 ^ 60) :
    2 * i + 14 ≤ N i / 2 ^ padicValNat 2 (N i) := by
  by_cases h : i < 54
  · exact pomme_ineq_base i hi_lo h
  · push_neg at h
    exact pomme_ineq_large i h hi_hi

/-- **Pomme's theorem** (axiom-free on the `pomme_small_range` side).
For all `i ≥ 50`, the odd part of `N i = 2·3^i + i + 5` is at least
`2i + 14`. Combines `pomme_small_range_proved` (covering `[50, 2^60)`
via the Hensel-lift argument) with `Pomme.pomme_cor3` (covering
`[2^60, ∞)` via Baker–Wüstholz). -/
theorem pomme_main (i : ℕ) (hi : 50 ≤ i) :
    2 * i + 14 ≤ N i / 2 ^ padicValNat 2 (N i) := by
  by_cases h : i < pommeThreshold
  · exact pomme_small_range_proved i hi h
  · push_neg at h
    exact Pomme.pomme_cor3 i h

end Hensel