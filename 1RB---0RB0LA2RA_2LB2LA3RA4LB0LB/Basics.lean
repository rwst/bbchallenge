import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.NormNum
import bb2x5

/-!
# Basics — provable building-block lemmas for the TM5 nonhalt proof

This file states lemmas that are implied by the existing definitions
(`binValue`, `ternValue`, `rep`, `repPair`, etc.) and by elementary
number theory. Most are proved; a few hard or strategy-dependent ones
remain as `sorry`.

The motivation comes from `claude-said.txt`:

> This TM's behavior involves an interaction between base-2 and base-3
> counters where the base-2 counter value determines overflow behavior.
> The non-halting argument requires showing that the base-2 value never
> hits 2^n-1 at specific moments. This is inherently about the 2-adic
> properties of iterates of the map V → (V+3^d)/2 with growing d.

The lemmas are grouped by which path in `strategy.md` they support:
- §1–3: elementary (path A, foundational)
- §4: 2-adic / Diophantine (path C)
- §5: abstract iterate (paths C, E)
- §6: length-growth (paths B, E)

See `strategy.md` for how these combine into a full proof.
-/

set_option autoImplicit false

open BB2x5

namespace TM5.Basics

-- ============================================================
-- §1. binValue (LSB-first binary interpretation)
-- ============================================================

/-- Binary value of a list of {s2, s3} cells (LSB first, s2=0, s3=1). -/
def binValue : List Sym → Nat
  | [] => 0
  | s :: rest => (if s = s3 then 1 else 0) + 2 * binValue rest

@[simp] theorem binValue_nil : binValue ([] : List Sym) = 0 := rfl

private theorem s2_ne_s3 : (s2 : Sym) ≠ s3 := by decide

theorem binValue_cons_s2 (rest : List Sym) :
    binValue (s2 :: rest) = 2 * binValue rest := by
  show (if (s2 : Sym) = s3 then 1 else 0) + 2 * binValue rest = _
  simp [s2_ne_s3]

theorem binValue_cons_s3 (rest : List Sym) :
    binValue (s3 :: rest) = 1 + 2 * binValue rest := by
  show (if (s3 : Sym) = s3 then 1 else 0) + 2 * binValue rest = _
  simp

/-- rep s2 n has value 0. -/
theorem binValue_rep_s2 : (n : Nat) → binValue (rep s2 n) = 0
  | 0 => rfl
  | n + 1 => by
    show binValue (s2 :: rep s2 n) = 0
    rw [binValue_cons_s2, binValue_rep_s2 n, Nat.mul_zero]

/-- rep s3 n has value 2^n - 1. -/
theorem binValue_rep_s3 : (n : Nat) → binValue (rep s3 n) = 2^n - 1
  | 0 => rfl
  | n + 1 => by
    show binValue (s3 :: rep s3 n) = 2^(n+1) - 1
    rw [binValue_cons_s3, binValue_rep_s3 n, Nat.pow_succ]
    have : 2^n ≥ 1 := Nat.one_le_pow n 2 (by omega); omega

/-- Upper bound on binValue: for valid binary cells, value < 2^length. -/
theorem binValue_lt_two_pow (l : List Sym) (h : ∀ s ∈ l, s = s2 ∨ s = s3) :
    binValue l < 2^l.length := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    have hl := h a (by simp)
    have htl : ∀ s ∈ tl, s = s2 ∨ s = s3 := fun s hs => h s (by simp [hs])
    have ih' := ih htl
    rcases hl with rfl | rfl
    · rw [binValue_cons_s2, List.length_cons, pow_succ]; omega
    · rw [binValue_cons_s3, List.length_cons, pow_succ]; omega

/-- Tight upper bound: for valid binary, value ≤ 2^length - 1. -/
theorem binValue_le (l : List Sym) (h : ∀ s ∈ l, s = s2 ∨ s = s3) :
    binValue l ≤ 2^l.length - 1 := by
  have h1 := binValue_lt_two_pow l h
  have h2 : 2^l.length ≥ 1 := Nat.one_le_pow _ _ (by omega)
  omega

/-- Characterization: all-s3 iff binValue equals the maximum 2^length - 1. -/
theorem binValue_eq_max_iff (l : List Sym) (h : ∀ s ∈ l, s = s2 ∨ s = s3) :
    binValue l = 2^l.length - 1 ↔ l = rep s3 l.length := by
  constructor
  · intro hv
    induction l with
    | nil => rfl
    | cons a tl ih =>
      have hl := h a (by simp)
      have htl : ∀ s ∈ tl, s = s2 ∨ s = s3 := fun s hs => h s (by simp [hs])
      have hbtl := binValue_le tl htl
      have hptl : 2^tl.length ≥ 1 := Nat.one_le_pow _ _ (by omega)
      rcases hl with rfl | rfl
      · -- a = s2 case: binValue = 2 * binValue tl ≤ 2 * (2^tl.length - 1) < 2^(tl.length+1) - 1
        exfalso
        rw [binValue_cons_s2, List.length_cons, pow_succ] at hv
        omega
      · -- a = s3 case: binValue = 1 + 2 * binValue tl; need binValue tl = 2^tl.length - 1
        rw [binValue_cons_s3, List.length_cons, pow_succ] at hv
        have hvtl : binValue tl = 2^tl.length - 1 := by omega
        have htl_eq := ih htl hvtl
        show s3 :: tl = rep s3 (tl.length + 1)
        rw [rep_succ, ← htl_eq]
  · intro hl
    have hlen : (rep s3 l.length).length = l.length := by
      simp [rep, List.length_replicate]
    calc binValue l = binValue (rep s3 l.length) := by rw [← hl]
      _ = 2^l.length - 1 := binValue_rep_s3 _

/-- The all-s3 case (binary counter = 2^n - 1) is a strict maximum: any
    non-all-s3 valid binary has value strictly less than 2^length - 1. -/
theorem binValue_lt_max_of_not_all_s3 (l : List Sym)
    (h : ∀ s ∈ l, s = s2 ∨ s = s3) (hne : ∃ s ∈ l, s = s2) :
    binValue l < 2^l.length - 1 := by
  have hle := binValue_le l h
  rcases Nat.lt_or_ge (binValue l) (2^l.length - 1) with hlt | hge
  · exact hlt
  · exfalso
    have heq : binValue l = 2^l.length - 1 := by omega
    rw [binValue_eq_max_iff l h] at heq
    obtain ⟨s, hs, hseq⟩ := hne
    have hsmem : s ∈ rep s3 l.length := heq ▸ hs
    have hs3 : s = s3 := List.eq_of_mem_replicate hsmem
    rw [hseq] at hs3
    exact absurd hs3 (by decide)

-- ============================================================
-- §2. ternValue (paired-cell ternary interpretation)
-- ============================================================

/-- Ternary value: pairs (s2,s2)=0, (s0,s2)=1, (s4,s2)=2 (LSB pair first). -/
def ternValue : List Sym → Nat
  | [] => 0
  | [_] => 0
  | a :: _ :: rest =>
    (if a = s0 then 1 else if a = s4 then 2 else 0) + 3 * ternValue rest

private theorem s2_ne_s0 : (s2 : Sym) ≠ s0 := by decide
private theorem s2_ne_s4 : (s2 : Sym) ≠ s4 := by decide
private theorem s4_ne_s0 : (s4 : Sym) ≠ s0 := by decide

theorem ternValue_cons_s2_s2 (rest : List Sym) :
    ternValue (s2 :: s2 :: rest) = 3 * ternValue rest := by
  show (if (s2 : Sym) = s0 then 1 else if (s2 : Sym) = s4 then 2 else 0) + 3 * ternValue rest = _
  simp [s2_ne_s0, s2_ne_s4]

theorem ternValue_cons_s4_s2 (rest : List Sym) :
    ternValue (s4 :: s2 :: rest) = 2 + 3 * ternValue rest := by
  show (if (s4 : Sym) = s0 then 1 else if (s4 : Sym) = s4 then 2 else 0) + 3 * ternValue rest = _
  simp [s4_ne_s0]

theorem ternValue_cons_s0_s2 (rest : List Sym) :
    ternValue (s0 :: s2 :: rest) = 1 + 3 * ternValue rest := by
  show (if (s0 : Sym) = s0 then 1 else if (s0 : Sym) = s4 then 2 else 0) + 3 * ternValue rest = _
  simp

/-- rep s2 n has ternary value 0. -/
theorem ternValue_rep_s2 : (n : Nat) → ternValue (rep s2 n) = 0
  | 0 => rfl
  | 1 => by show ternValue [s2] = 0; rfl
  | n + 2 => by
    show ternValue (s2 :: s2 :: rep s2 n) = 0
    rw [ternValue_cons_s2_s2, ternValue_rep_s2 n, Nat.mul_zero]

/-- repPair s4 s2 d has ternary value 3^d - 1 (all digits = 2). -/
theorem ternValue_repPair_s4_s2 : (d : Nat) → ternValue (repPair s4 s2 d) = 3^d - 1
  | 0 => rfl
  | d + 1 => by
    show ternValue (s4 :: s2 :: repPair s4 s2 d) = _
    rw [ternValue_cons_s4_s2, ternValue_repPair_s4_s2 d]
    have : 3^d ≥ 1 := Nat.one_le_pow d 3 (by omega); omega

/-- 3^d - 1 is even (because 3^d is odd for all d). -/
theorem three_pow_sub_one_even (d : Nat) : Even (3^d - 1) := by
  have h : Odd (3^d) := Odd.pow (by decide : Odd 3)
  obtain ⟨k, hk⟩ := h; exact ⟨k, by omega⟩

-- ============================================================
-- §3. Parities (binOdd / ternOdd; provable without invariants)
-- ============================================================

/-- Parity of a binary value list: first element = s3 means odd. -/
def binOdd (l : List Sym) : Bool :=
  match l with
  | [] => false
  | a :: _ => a == s3

/-- Parity of ternary value. Only s0 (digit 1) flips parity. -/
def ternOdd : List Sym → Bool
  | [] => false
  | [_] => false
  | a :: _ :: rest => if a == s0 then !ternOdd rest else ternOdd rest

/-- binOdd agrees with Odd (binValue _) for valid binary. -/
theorem binOdd_iff_odd_binValue (l : List Sym) (h : ∀ s ∈ l, s = s2 ∨ s = s3) :
    binOdd l = true ↔ Odd (binValue l) := by
  cases l with
  | nil => simp [binOdd]
  | cons s rest =>
    have hs := h s (by simp)
    rcases hs with rfl | rfl
    · simp only [binOdd, show ((s2 : Sym) == s3) = false from by decide]
      rw [binValue_cons_s2]
      constructor
      · intro h; exact absurd h (by decide)
      · intro ⟨k, hk⟩; omega
    · rw [binValue_cons_s3]
      constructor
      · intro; exact ⟨binValue rest, by omega⟩
      · intro; simp [binOdd]

/-- 2^n - 1 is odd for n ≥ 1. -/
theorem two_pow_sub_one_odd (n : Nat) (hn : n ≥ 1) : Odd (2^n - 1) := by
  cases n with
  | zero => omega
  | succ m =>
    rw [pow_succ]
    have hpm : 2^m ≥ 1 := Nat.one_le_pow _ _ (by omega)
    exact ⟨2^m - 1, by omega⟩

/-- 3^d is always odd. -/
theorem three_pow_odd (d : Nat) : Odd (3^d) := Odd.pow (by decide : Odd 3)

-- ============================================================
-- §4. 2-adic valuation and Diophantine lemmas
-- ============================================================

/-- The 2-adic valuation ν₂(n): largest k with 2^k ∣ n (0 for n = 0 here). -/
abbrev nu2 : Nat → Nat := fun n => padicValNat 2 n

/-- If V is odd and 3^d is odd, then V + 3^d is even. -/
theorem add_three_pow_even_of_odd (V d : Nat) (hV : Odd V) : Even (V + 3^d) :=
  hV.add_odd (three_pow_odd d)

/-- The odd sequence: V + 3^d has 2-adic valuation ≥ 1 when V is odd. -/
theorem nu2_add_three_pow_ge_one (V d : Nat) (hV : Odd V) (hpos : V + 3^d > 0) :
    nu2 (V + 3^d) ≥ 1 := by
  have he : Even (V + 3^d) := hV.add_odd (three_pow_odd d)
  have h2dvd : 2 ∣ (V + 3^d) := he.two_dvd
  exact one_le_padicValNat_of_dvd (by omega) h2dvd

/-- 2^n ≠ 3^d for n ≥ 1 (parity argument: 2^n is even, 3^d is odd). -/
theorem two_pow_ne_three_pow (n d : Nat) (hn : n ≥ 1) :
    2^n ≠ 3^d := by
  intro h
  have h_even : Even (2^n) := by
    cases n with
    | zero => omega
    | succ m => rw [pow_succ]; exact ⟨2^m, by ring⟩
  have h_odd : Odd (3^d) := three_pow_odd d
  rw [h] at h_even
  obtain ⟨a, ha⟩ := h_even
  obtain ⟨b, hb⟩ := h_odd
  omega

/-- A specific Diophantine fact: `(2^n - 1) mod 2^m = 2^m - 1` for m ≤ n.
    Exposed for reasoning about era-to-era wraps. -/
theorem two_pow_sub_one_mod (n m : Nat) (hmn : m ≤ n) :
    (2^n - 1) % 2^m = 2^m - 1 := by
  have hpm : 2^m ≥ 1 := Nat.one_le_pow _ _ (by omega)
  have hpq : 2^(n-m) ≥ 1 := Nat.one_le_pow _ _ (by omega)
  have hpow_split : 2^n = 2^m * 2^(n-m) := by
    rw [← pow_add]; congr 1; omega
  have heq : 2^n - 1 = 2^m * (2^(n-m) - 1) + (2^m - 1) := by
    have h1 : 2^m * (2^(n-m) - 1) = 2^m * 2^(n-m) - 2^m := by
      rw [Nat.mul_sub_one]
    have h2 : 2^m * 2^(n-m) ≥ 2^m := Nat.le_mul_of_pos_right _ hpq
    rw [hpow_split, h1]; omega
  rw [heq, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (by omega)

-- ============================================================
-- §5. Abstract overflow iterate V → (V + 3^d)
-- ============================================================

/-- One abstract "big era" step: add 3^d - 1 (the cycle_nonzero sum)
    modulo 2^n (the binary wrap length at the end of the era).
    This models the binary trajectory ignoring the intra-era detail. -/
def overflowStep (V d n : Nat) : Nat := (V + (3^d - 1)) % 2^n

/-- Parity of overflowStep: `V + (3^d - 1)` has the parity of V since
    `3^d - 1` is even. Thus `overflowStep V d n` has the parity of V mod 2^n. -/
theorem overflowStep_parity (V d n : Nat) (hn : n ≥ 1) :
    overflowStep V d n % 2 = V % 2 := by
  unfold overflowStep
  have h2dvd : 2 ∣ 2^n := by
    rw [show (2 : Nat) = 2^1 from rfl]
    exact pow_dvd_pow 2 hn
  rw [Nat.mod_mod_of_dvd _ h2dvd]
  have he : Even (3^d - 1) := three_pow_sub_one_even d
  obtain ⟨k, hk⟩ := he
  rw [hk]; omega

/-- Key Diophantine equation: if overflowStep V d n = 2^n - 1,
    then `2^n ∣ V + 3^d`. This is the condition the TM must never satisfy. -/
theorem overflowStep_eq_max_iff (V d n : Nat) (hn : n ≥ 1) :
    overflowStep V d n = 2^n - 1 ↔ 2^n ∣ (V + 3^d) := by
  unfold overflowStep
  have h3 : 3^d ≥ 1 := Nat.one_le_pow _ _ (by omega)
  have hp : 2^n ≥ 2 := by
    calc 2 = 2^1 := (pow_one 2).symm
      _ ≤ 2^n := Nat.pow_le_pow_right (by omega) hn
  rw [show V + (3^d - 1) = V + 3^d - 1 from by omega]
  constructor
  · intro h
    have hpos : V + 3^d ≥ 1 := by omega
    have hmod : (V + 3^d) % 2^n = 0 := by
      rw [show V + 3^d = (V + 3^d - 1) + 1 from by omega,
          Nat.add_mod, h,
          Nat.mod_eq_of_lt (show 1 < 2^n from by omega),
          show 2^n - 1 + 1 = 2^n from by omega, Nat.mod_self]
    exact Nat.dvd_of_mod_eq_zero hmod
  · intro h
    obtain ⟨k, hk⟩ := h
    have hpos : V + 3^d ≥ 1 := by omega
    have hk_pos : k ≥ 1 := by
      rw [hk] at hpos
      by_contra hne; push_neg at hne
      interval_cases k; omega
    have heq : V + 3^d - 1 = 2^n * (k - 1) + (2^n - 1) := by
      rw [hk]
      cases k with
      | zero => omega
      | succ m =>
        rw [show (m + 1 : Nat) - 1 = m from rfl]
        have : 2^n * (m + 1) = 2^n * m + 2^n := by ring
        omega
    rw [heq, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod]
    exact Nat.mod_eq_of_lt (by omega)

-- ============================================================
-- §6. Length growth: binary region grows slower than ternary
--      but in a controlled way. Supports path B/E.
-- ============================================================

/-- Odd overflow (k=0) shrinks binary by exactly 1 cell. -/
theorem bin_length_shrink_odd_overflow_k0 (bin_rest : List Sym) :
    bin_rest.length = (s2 :: bin_rest).length - 1 := by simp

/-- Odd overflow (k=1) shrinks binary by exactly 2 cells. -/
theorem bin_length_shrink_odd_overflow_k1 (bin_rest : List Sym) :
    bin_rest.length = (s3 :: s2 :: bin_rest).length - 2 := by simp

/-- The "gap invariant": binary length is at least log2(V+1)
    for valid binary value V. This is the structural bound relating bit-width
    to encoded value. -/
theorem bin_length_ge_log_binValue (l : List Sym)
    (h : ∀ s ∈ l, s = s2 ∨ s = s3) :
    l.length ≥ Nat.log 2 (binValue l + 1) := by
  have h1 := binValue_lt_two_pow l h
  have h2 : binValue l + 1 ≤ 2^l.length := by omega
  calc Nat.log 2 (binValue l + 1)
      ≤ Nat.log 2 (2^l.length) := Nat.log_mono_right h2
    _ = l.length := Nat.log_pow (by omega) _

-- ============================================================
-- §7. Halting condition at all-s3 odd overflow
-- ============================================================

/-- Reformulation of the nonhalt crux: the TM reaches A,1 (halting) precisely
    when, starting from an odd overflow with binary = rep s3 n, the carry
    cascades through all s3s, consuming the terminator's s1 bit. The
    precise structural fact we need (stated abstractly): no reachable
    canonical config at odd overflow has bin = rep s3 n. This is the
    key missing lemma. Once proved, it closes the remaining sorry in
    `canonical_progress` at the all-s3 case.

    Here we state it as: if `bin = rep s3 n` at odd overflow (pad=1,
    tern all-zero), then that configuration is not reachable from
    `initConfig`. Formalizing the "reachability" predicate depends on
    the proof strategy and is left as a design choice.
-/
theorem all_s3_odd_overflow_unreachable
    (n d : Nat) (bin tern : List Sym) (pad : Nat)
    (h_bin : bin = rep s3 n)
    (h_tern_zero : tern = rep s2 (2 * d))
    (h_pad : pad = 1)
    -- placeholder: "the CycleStart bin tern pad is reachable from initConfig"
    (h_reach : True) :
    False := by
  sorry

end TM5.Basics
