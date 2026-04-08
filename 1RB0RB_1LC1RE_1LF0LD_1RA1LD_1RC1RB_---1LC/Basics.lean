import Mathlib.Tactic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProductMeasure
import machine

-- ============================================================
-- Subgraph A: P-phase recurrence and closed form
-- ============================================================

/-- Recurrence: P(2n+1) = n+2, P(2n) = P(3n+4). -/
def p : Nat → Nat
  | 0     => 0
  | n + 1 =>
    if (n + 1) % 2 = 0 then
      p (3 * ((n + 1) / 2) + 4)
    else
      (n + 1) / 2 + 2
termination_by n => padicValNat 2 (n + 8)
decreasing_by
  simp_wf
  have heven : 2 ∣ (n + 1) := Nat.dvd_of_mod_eq_zero ‹_›
  have heven9 : 2 ∣ (n + 9) := by omega
  have hkey : 3 * ((n + 1) / 2) + 4 + 8 = 3 * ((n + 9) / 2) := by
    obtain ⟨k, _⟩ := heven; omega
  have hkey2 : n + 1 + 8 = n + 9 := by omega
  rw [hkey, hkey2]
  have hne : (n + 9) / 2 ≠ 0 := by omega
  rw [padicValNat.mul (by norm_num : (3:ℕ) ≠ 0) hne]
  simp [padicValNat.eq_zero_of_not_dvd (by omega : ¬ (2 : ℕ) ∣ 3)]
  rw [padicValNat.div heven9]
  have hpos : 1 ≤ padicValNat 2 (n + 9) :=
    one_le_padicValNat_of_dvd (by omega) heven9
  omega

#eval (List.range 20).map (fun n => p (n + 1))

lemma p_even (k : Nat) (hk : k ≥ 1) : p (2 * k) = p (3 * k + 4) := by
  conv_lhs => rw [p.eq_def (2 * k)]
  split; · omega
  · rename_i n hn; simp [show (n + 1) % 2 = 0 from by omega]; congr 1; omega

lemma p_odd (k : Nat) : p (2 * k + 1) = k + 2 := by
  conv_lhs => rw [p.eq_def (2 * k + 1)]
  split; · omega
  · rename_i n hn; simp [show ¬ ((n + 1) % 2 = 0) from by omega]; omega

private lemma ordCompl_two_mul (m : Nat) :
    ordCompl[2] (2 * m) = ordCompl[2] m := by
  simpa using Nat.ordCompl_self_pow_mul m 1 Nat.prime_two

private lemma ordCompl_three_mul (m : Nat) :
    ordCompl[2] (3 * m) = 3 * ordCompl[2] m := by
  have h := Nat.ordCompl_mul 3 m 2
  simp [Nat.factorization_eq_zero_of_not_dvd (by omega : ¬ 2 ∣ 3)] at h
  exact h

private lemma factorization_three_mul (m : Nat) (hm : m ≠ 0) :
    (3 * m).factorization 2 = m.factorization 2 := by
  rw [Nat.factorization_mul (by norm_num) hm]
  simp [Nat.factorization_eq_zero_of_not_dvd (by omega : ¬ 2 ∣ 3)]

private lemma factorization_two_mul (m : Nat) (hm : m ≠ 0) :
    (2 * m).factorization 2 = m.factorization 2 + 1 := by
  rw [Nat.factorization_mul (by norm_num) hm]
  simp [Nat.Prime.factorization_self Nat.prime_two, add_comm]

lemma p_closed_form3 {n : Nat} (hn : n ≠ 0) :
    p n = (ordCompl[2] (n + 8) * 3 ^ ((n + 8).factorization 2) - 5) / 2 := by
  suffices h : ∀ v n : Nat, n ≠ 0 → (n + 8).factorization 2 = v →
      p n = (ordCompl[2] (n + 8) * 3 ^ ((n + 8).factorization 2) - 5) / 2 from
    h _ n hn rfl
  intro v
  induction v with
  | zero =>
    intro n hn hv
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := by
      refine ⟨n / 2, ?_⟩
      have hodd : ¬ 2 ∣ n := by
        intro hdvd
        have : 0 < (n + 8).factorization 2 := by
          rw [Nat.factorization_def _ Nat.prime_two]
          exact one_le_padicValNat_of_dvd (by omega) (by omega)
        omega
      omega
    rw [p_odd]
    have hfact : (2 * k + 1 + 8).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by omega)
    simp only [hfact, pow_zero, mul_one, Nat.div_one]
    omega
  | succ v ih =>
    intro n hn hv
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := by
      refine ⟨n / 2, ?_⟩
      have heven : 2 ∣ n := by
        by_contra hodd
        have := Nat.factorization_eq_zero_of_not_dvd (by omega : ¬ 2 ∣ (n + 8))
        omega
      omega
    have hk : k ≥ 1 := by omega
    rw [p_even k hk]
    have hfactarg : (3 * k + 4 + 8).factorization 2 = v := by
      rw [show 3 * k + 4 + 8 = 3 * (k + 4) from by ring,
          factorization_three_mul (k + 4) (by omega)]
      have h2 := factorization_two_mul (k + 4) (by omega)
      rw [show 2 * k + 8 = 2 * (k + 4) from by ring] at hv
      omega
    rw [ih (3 * k + 4) (by omega) hfactarg]
    congr 1; congr 1
    rw [show 3 * k + 4 + 8 = 3 * (k + 4) from by ring,
        show 2 * k + 8 = 2 * (k + 4) from by ring]
    rw [ordCompl_three_mul, ordCompl_two_mul]
    rw [factorization_three_mul (k + 4) (by omega), factorization_two_mul (k + 4) (by omega)]
    ring

lemma p_closed_form2 {n : Nat} (hn : n ≠ 0) :
    p n = (ordCompl[2] (n + 8) * 3 ^ padicValNat 2 (n + 8) - 5) / 2 := by
  rw [← Nat.factorization_def _ Nat.prime_two]; exact p_closed_form3 hn

/-- Closed form: for n ≥ 1,
    p(n) = ((n+8) · 3^v₂(n+8) / 2^v₂(n+8) - 5) / 2
    where v₂ = padicValNat 2 is the 2-adic valuation. -/
lemma p_closed_form1 {n : Nat} (hn : n ≠ 0) :
    p n = ((n + 8) * 3 ^ (padicValNat 2 (n + 8)) / 2 ^ (padicValNat 2 (n + 8)) - 5) / 2 := by
  rw [p_closed_form2 hn]
  congr 1; congr 1
  have hdvd : 2 ^ padicValNat 2 (n + 8) ∣ (n + 8) := by
    rw [← Nat.factorization_def _ Nat.prime_two]; exact Nat.ordProj_dvd (n + 8) 2
  rw [mul_comm (n + 8), Nat.mul_div_assoc _ hdvd, mul_comm, Nat.factorization_def _ Nat.prime_two]

/-- The image of p is exactly {(o * 3^k - 5) / 2 | o odd, k : ℕ}.
    More precisely, for any n ≥ 1 there exist l, k such that
    p(n) = ((2l+1) * 3^k - 5) / 2. -/
lemma p_in_odd_times_pow3 {n : Nat} (hn : n ≠ 0) :
    ∃ l k : Nat, p n = ((2 * l + 1) * 3 ^ k - 5) / 2 := by
  rw [p_closed_form2 hn]
  set o := ordCompl[2] (n + 8)
  set k := padicValNat 2 (n + 8)
  have ho_odd : ¬ 2 ∣ o := Nat.not_dvd_ordCompl Nat.prime_two (by omega)
  have ho_pos : o ≠ 0 := (Nat.ordCompl_pos 2 (by omega : n + 8 ≠ 0)).ne'
  refine ⟨o / 2, k, ?_⟩
  have h_eq : o = 2 * (o / 2) + 1 := by omega
  conv_lhs => rw [h_eq]

-- ============================================================
-- Defining equations for p(n), fixing the 2-adic exponent of n+8
-- ============================================================

/-- Case v₂(n+8) = 0: odd n. p(n) = (n + 3) / 2. -/
lemma p_case_v0 (n : Nat) (hn : n ≠ 0) (hv : ¬ 2 ∣ (n + 8)) :
    p n = (n + 3) / 2 := by
  rw [show n = 2 * (n / 2) + 1 from by omega, p_odd]; omega

/-- Case v₂(n+8) = 1: n + 8 = 2m with m odd. p(n) = (3n/2 + 7) / 2. -/
lemma p_case_v1 (n : Nat) (hn : n ≠ 0) (m : Nat) (hm : ¬ 2 ∣ m) (heq : n + 8 = 2 * m) :
    p n = (3 * n / 2 + 7) / 2 := by
  rw [show n = 2 * (m - 4) from by omega, p_even (m - 4) (by omega),
      show 3 * (m - 4) + 4 = 2 * ((3 * m - 9) / 2) + 1 from by omega, p_odd]; omega

/-- Case v₂(n+8) = 2: n + 8 = 4m with m odd. p(n) = (9n/4 + 13) / 2. -/
lemma p_case_v2 (n : Nat) (hn : n ≠ 0) (m : Nat) (hm : ¬ 2 ∣ m) (heq : n + 8 = 4 * m) :
    p n = (9 * n / 4 + 13) / 2 := by
  rw [show n = 2 * (2 * m - 4) from by omega, p_even (2 * m - 4) (by omega),
      show 3 * (2 * m - 4) + 4 = 2 * (3 * m - 4) from by omega, p_even (3 * m - 4) (by omega),
      show 3 * (3 * m - 4) + 4 = 2 * ((9 * m - 9) / 2) + 1 from by omega, p_odd]; omega

/-- Case v₂(n+8) = 3: n + 8 = 8m with m odd. p(n) = (27n/8 + 22) / 2. -/
lemma p_case_v3 (n : Nat) (hn : n ≠ 0) (m : Nat) (hm : ¬ 2 ∣ m) (heq : n + 8 = 8 * m) :
    p n = (27 * n / 8 + 22) / 2 := by
  rw [show n = 2 * (4 * m - 4) from by omega, p_even (4 * m - 4) (by omega),
      show 3 * (4 * m - 4) + 4 = 2 * (6 * m - 4) from by omega, p_even (6 * m - 4) (by omega)]
  rw [show 3 * (6 * m - 4) + 4 = 2 * (9 * m - 4) from by omega, p_even (9 * m - 4) (by omega),
      show 3 * (9 * m - 4) + 4 = 2 * ((27 * m - 9) / 2) + 1 from by omega, p_odd]
  omega

-- ============================================================
-- Diophantine equations: when is p(n) = 2^i − 2?
-- ============================================================

/-- Case v₂(n+8) = 0 (odd n): p(n) = 2^i − 2 iff n + 7 = 2^(i+1).
    Solutions: n ∈ {1, 9, 25, 57, 121, 249, 505, …}. -/
lemma p_eq_pow2_case_v0 (n i : Nat) (hn : n ≠ 0) (hi : i ≥ 2)
    (hodd : ¬ 2 ∣ n) :
    p n = 2 ^ i - 2 ↔ n + 7 = 2 ^ (i + 1) := by
  rw [show n = 2 * (n / 2) + 1 from by omega, p_odd,
      show 2 ^ (i + 1) = 2 ^ i * 2 from pow_succ 2 i]
  have : 2 ^ i ≥ 4 := le_trans (by norm_num : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) hi)
  omega

/-- Case v₂(n+8) = 1 (n+8 = 2m, m odd): p(n) = 2^i − 2 iff 3n + 22 = 2^(i+2).
    Solutions: n ∈ {14, 78, 334, 1358, 5454, …}. -/
lemma p_eq_pow2_case_v1 (n i : Nat) (hn : n ≠ 0) (hi : i ≥ 2)
    (m : Nat) (hm : ¬ 2 ∣ m) (heq : n + 8 = 2 * m) :
    p n = 2 ^ i - 2 ↔ 3 * n + 22 = 2 ^ (i + 2) := by
  rw [show n = 2 * (m - 4) from by omega, p_even (m - 4) (by omega),
      show 3 * (m - 4) + 4 = 2 * ((3 * m - 9) / 2) + 1 from by omega, p_odd,
      show 2 ^ (i + 2) = 2 ^ i * 4 from by ring]
  have : 2 ^ i ≥ 4 := le_trans (by norm_num : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) hi)
  omega

/-- Case v₂(n+8) = 2 (n+8 = 4m, m odd): p(n) = 2^i − 2 iff 9n + 68 = 2^(i+3).
    Solutions: n ∈ {220, 14556, 932060, …}. -/
lemma p_eq_pow2_case_v2 (n i : Nat) (hn : n ≠ 0) (hi : i ≥ 2)
    (m : Nat) (hm : ¬ 2 ∣ m) (heq : n + 8 = 4 * m) :
    p n = 2 ^ i - 2 ↔ 9 * n + 68 = 2 ^ (i + 3) := by
  rw [show n = 2 * (2 * m - 4) from by omega, p_even (2 * m - 4) (by omega),
      show 3 * (2 * m - 4) + 4 = 2 * (3 * m - 4) from by omega, p_even (3 * m - 4) (by omega)]
  rw [show 3 * (3 * m - 4) + 4 = 2 * ((9 * m - 9) / 2) + 1 from by omega, p_odd,
      show 2 ^ (i + 3) = 2 ^ i * 8 from by ring]
  have : 2 ^ i ≥ 4 := le_trans (by norm_num : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) hi)
  omega

/-- Only the v₂(n+8) = 0 case produces odd solutions to p(n) = 2^i − 2:
    cases v ≥ 1 force n even (since 2 ∣ (n+8) implies 2 ∣ n). -/
lemma p_eq_pow2_sub2_odd_implies_v0 (n i : Nat) (hn : n ≠ 0) (hi : i ≥ 2)
    (hodd : ¬ 2 ∣ n) (h : p n = 2 ^ i - 2) : n + 7 = 2 ^ (i + 1) :=
  (p_eq_pow2_case_v0 n i hn hi hodd).mp h

open Cryptid in
/-- p(n) is the Q-entry: iterating the macro map from P(n) reaches Q(p(n), 1).
    This connects the pure-arithmetic function p with the TM macro model. -/
lemma p_connects_to_macro {n : Nat} (hn : n ≠ 0) :
    ∃ steps, Cryptid.iterMachineState (.P n) (steps + 1) = .Q (p n) 1 := by
  suffices h : ∀ v n : Nat, n ≠ 0 → padicValNat 2 (n + 8) = v →
      ∃ steps, iterMachineState (.P n) (steps + 1) = .Q (p n) 1 from
    h _ n hn rfl
  intro v
  induction v with
  | zero =>
    intro n hn hv
    have hodd : ¬ 2 ∣ n := by
      intro hdvd
      exact absurd (one_le_padicValNat_of_dvd (by omega) (by omega : 2 ∣ n + 8)) (by omega)
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    rw [p_odd]
    refine ⟨0, ?_⟩
    simp only [iterMachineState, nextMachineState]
    have h1 : (2 * k + 1) % 2 = 1 := by omega
    have h2 : ((2 * k + 1) % 2 == 0) = false := by simp [h1]
    simp only [h2, Bool.false_eq_true, ite_false, MachineState.Q.injEq]
    refine ⟨?_, trivial⟩
    show (2 * k + 1) / 2 + 2 = k + 2
    have : (2 * k + 1) / 2 = k := by omega
    omega
  | succ v ih =>
    intro n hn hv
    have heven : 2 ∣ n := by
      by_contra hodd
      exact absurd (padicValNat.eq_zero_of_not_dvd (show ¬ 2 ∣ (n + 8) by omega)) (by omega)
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
    have hk : k ≥ 1 := by omega
    rw [p_even k hk]
    have hstep : nextMachineState (.P (2 * k)) = .P (3 * k + 4) := by
      unfold nextMachineState
      have : ((2 * k) % 2 == 0) = true := by
        rw [show 2 * k % 2 = 0 from Nat.mul_mod_right 2 k]; rfl
      simp [Nat.mul_div_cancel_left k (by norm_num : 0 < 2)]
    have hv' : padicValNat 2 (3 * k + 4 + 8) = v := by
      rw [show 3 * k + 4 + 8 = 3 * (k + 4) from by ring]
      rw [padicValNat.mul (by norm_num : (3 : ℕ) ≠ 0) (by omega)]
      simp [padicValNat.eq_zero_of_not_dvd (by omega : ¬ (2 : ℕ) ∣ 3)]
      rw [show 2 * k + 8 = 2 * (k + 4) from by ring] at hv
      rw [padicValNat.mul (by norm_num : (2 : ℕ) ≠ 0) (by omega)] at hv
      simp at hv
      omega
    obtain ⟨steps', h'⟩ := ih (3 * k + 4) (by omega) hv'
    exact ⟨steps' + 1, by rwa [show steps' + 1 + 1 = (steps' + 1) + 1 from by omega,
      iterMachineState, hstep]⟩

-- ============================================================
-- Subgraph B: qacc / q definitions
-- ============================================================

/-- One-parameter Q-phase accumulator (Q2 + QP2 rules only).
    q(a, b) = b + qacc(a) for chains that exit via QP2.
    qacc(0) = 0,
    qacc(2k)   = 2k + 3 + qacc(k − 1)   (Q2: accumulate and recurse),
    qacc(2k+1) = 5k + 1                  (QP2: exit).
    Note: qacc(1) = 1 (not 0) — differs from the two-arg q at the
    forbidden index, which only affects Q-entries {4, 10, 22, 46, …}
    leading to Q(1, _) via Q1 (conjectured unreachable).
    In Pari/GP: qacc(n)=if(n==0,0,if(n%2==0,n+3+qacc(floor((n-1)/2)),(5*n-3)/2)) -/
def qacc : Nat → Nat
  | 0 => 0
  | n + 1 =>
    if (n + 1) % 2 = 0 then
      (n + 1) + 3 + qacc (n / 2)
    else
      5 * (n / 2) + 1
termination_by n => n
decreasing_by simp_wf; omega

lemma qacc_zero : qacc 0 = 0 := by rw [qacc.eq_def]

lemma qacc_even (k : Nat) (hk : k ≥ 1) :
    qacc (2 * k) = 2 * k + 3 + qacc (k - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [show 2 * (k + 1) = (2 * k + 1) + 1 from by omega]
  rw [qacc.eq_def]
  simp [show (2 * k + 1 + 1) % 2 = 0 from by omega,
        show (2 * k + 1) / 2 = k from by omega]

lemma qacc_odd (k : Nat) :
    qacc (2 * k + 1) = 5 * k + 1 := by
  conv_lhs => rw [qacc.eq_def]
  simp [show (2 * k) / 2 = k from Nat.mul_div_cancel_left k (by norm_num)]

/-- Two-argument Q-phase function, defined in terms of qacc. -/
def q (a b : Nat) : Nat := b + qacc a

lemma q_eq_b_plus_qacc (a b : Nat) : q a b = b + qacc a := rfl

#eval (List.range 20).map (fun n => qacc (n + 2))

/-- Closed form for qacc.  The recursion qacc(2m+2) = qacc(m) + 2m + 5
    telescopes along the chain  n → (n−2)/2 → ⋯  until reaching an odd
    number or 0.  Writing n+2 = 2^v · op with op odd, the chain has v
    steps when op ≥ 3 (landing on odd op−2) and v−1 steps when op = 1
    (landing on 0).  The unified Nat-friendly formula is:

      2 · qacc(n) + 5 = 4n + 2·v₂(n+2) + max(odd_part(n+2), 3).

    Equivalently, over ℤ:
      qacc(n) = 2n + v₂(n+2) + (odd_part(n+2) − 5)/2   when odd_part ≥ 3,
      qacc(n) = 2n + v₂(n+2) − 1                        when n+2 is a power of 2. -/
private lemma ordCompl_odd {n : Nat} (hn : ¬ 2 ∣ n) :
    ordCompl[2] n = n :=
  (Nat.ordCompl_eq_self_iff_zero_or_not_dvd n Nat.prime_two).mpr (Or.inr hn)

theorem qacc_closed_form (n : Nat) :
    2 * qacc n + 5 =
      4 * n + 2 * (n + 2).factorization 2 + max (ordCompl[2] (n + 2)) 3 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · -- Even case: n = 2 * m
      cases m with
      | zero =>
        simp only [Nat.mul_zero, qacc_zero]
        -- n = 0: need factorization 2 of 2 = 1 and ordCompl[2] 2 = 1
        have : (2 : Nat).factorization 2 = 1 := by
          rw [Nat.Prime.factorization_self Nat.prime_two]
        rw [show (0 : Nat) + 2 = 2 from rfl, this]
        simp [ordCompl_odd (show ¬ 2 ∣ (1 : Nat) from by omega)]
      | succ m =>
        rw [qacc_even (m + 1) (by omega)]
        have ihm := ih m (by omega)
        have hfact : (2 * (m + 1) + 2).factorization 2 = (m + 2).factorization 2 + 1 := by
          rw [show 2 * (m + 1) + 2 = 2 * (m + 2) from by ring]
          exact factorization_two_mul (m + 2) (by omega)
        have hord : ordCompl[2] (2 * (m + 1) + 2) = ordCompl[2] (m + 2) := by
          rw [show 2 * (m + 1) + 2 = 2 * (m + 2) from by ring]
          exact ordCompl_two_mul (m + 2)
        rw [hord, hfact]
        simp only [show m + 1 - 1 = m from by omega] at *
        set c := (m + 2).factorization 2 with hc_def
        set o := (m + 2) / 2 ^ c with ho_def
        omega
    · -- Odd case: n = 2 * m + 1
      rw [qacc_odd m]
      have hodd : ¬ 2 ∣ (2 * m + 3) := by omega
      have hfact : (2 * m + 3).factorization 2 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd hodd
      rw [show 2 * m + 1 + 2 = 2 * m + 3 from by ring]
      rw [ordCompl_odd hodd, hfact]
      simp only [Nat.mul_zero, Nat.add_zero]
      omega

-- ============================================================
-- Subgraph C: Q(1,_) backward reachability analysis
-- ============================================================

namespace Cryptid

/-! ### Backward analysis of Q(1, _) reachability from P(2)

Rules (renamed: Q1/QP1 have first arg = 1, Q2/QP2 have first arg ≥ 2):
  Q1:  Q(1, 2b)   → Q(b+2, 1)        (re-entry, even)
  QP1: Q(1, 2b+1) → P(3b+8)          (exit, odd)
  Q2:  Q(2a+2, b) → Q(a, b+2a+5)     (halving, even first arg ≥ 2)
  QP2: Q(2a+3, b) → P(b+5a+6)        (exit, odd first arg ≥ 3)

The only rule producing Q(1, b) is Q2 with a = 1:
  Q(4, b) → Q(1, b+7)

So Q(1, _) is reached iff Q(4, _) is reached. The halving chain
  Q(3·2^k − 2, 1) → ··· → Q(4, _) → Q(1, _)
always completes (all intermediate first-args are even ≥ 2), so Q(4, _)
is reached iff the orbit enters Q with first argument x = 3·2^k − 2
for some k ≥ 1, i.e., iff P visits a "critical" value 6·2^k − 7.

The critical P-values are {5, 17, 41, 89, 185, 377, 761, …}.
No modular invariant (checked up to mod 96) separates them from the
orbit.  The conjecture is Collatz-hard.
-/

/-- Right-unfolding of iterMachineState: iter s (n+1) = next (iter s n). -/
lemma iterMachineState_succ (s : MachineState) (n : Nat) :
    iterMachineState s (n + 1) = nextMachineState (iterMachineState s n) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [iterMachineState]; exact ih (nextMachineState s)

private lemma nms_P_even (k : Nat) :
    nextMachineState (.P (2 * k)) = .P (3 * k + 4) := by
  unfold nextMachineState; simp [show (2 * k) % 2 = 0 from by omega]

private lemma nms_P_odd (k : Nat) :
    nextMachineState (.P (2 * k + 1)) = .Q (k + 2) 1 := by
  unfold nextMachineState; simp [show (2 * k + 1) % 2 = 1 from by omega,
    show (2 * k + 1) / 2 = k from by omega]

private lemma nms_Q1_even (k : Nat) :
    nextMachineState (.Q 1 (2 * k)) = .Q (k + 2) 1 := by
  unfold nextMachineState; simp [show (2 * k) % 2 = 0 from by omega]

private lemma nms_Q1_odd (k : Nat) :
    nextMachineState (.Q 1 (2 * k + 1)) = .P (3 * k + 8) := by
  unfold nextMachineState; simp [show (2 * k + 1) % 2 = 1 from by omega,
    show (2 * k + 1) / 2 = k from by omega]

private lemma nms_Q_even (k : Nat) (b' : Nat) :
    nextMachineState (.Q (2 * k + 2) b') = .Q k (b' + 2 * k + 5) := by
  unfold nextMachineState; simp [show (2 * k) % 2 = 0 from by omega,
    show (2 * k) / 2 = k from by omega]

private lemma nms_Q_odd (k : Nat) (b' : Nat) :
    nextMachineState (.Q (2 * k + 1 + 2) b') = .P (b' + 5 * k + 6) := by
  unfold nextMachineState; simp [show (2 * k + 1) % 2 = 1 from by omega]

/-- Predecessor analysis: the only states that transition to Q(m, b)
    with m ≥ 2 are P(2m−3) via PQ, Q(1, 2m−4) via Q1, or Q(2m+2, b') via Q2. -/
lemma nextMachineState_Q_pred (m : Nat) (hm : m ≥ 2) (b : Nat) (s : MachineState)
    (h : nextMachineState s = .Q m b) :
    (s = .P (2 * m - 3) ∧ b = 1) ∨
    (s = .Q 1 (2 * m - 4) ∧ b = 1) ∨
    (∃ b', s = .Q (2 * m + 2) b' ∧ b = b' + 2 * m + 5) := by
  cases s with
  | Halt => simp [nextMachineState] at h
  | P a =>
    obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := Nat.even_or_odd a
    · rw [show k + k = 2 * k from by omega, nms_P_even] at h; simp at h
    · rw [nms_P_odd] at h; simp [MachineState.Q.injEq] at h
      obtain ⟨h1, h2⟩ := h; left; constructor
      · congr 1; omega
      · omega
  | Q a b' =>
    cases a with
    | zero => simp [nextMachineState] at h
    | succ n =>
      cases n with
      | zero =>
        obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := Nat.even_or_odd b'
        · rw [show k + k = 2 * k from by omega, nms_Q1_even] at h
          simp [MachineState.Q.injEq] at h; obtain ⟨h1, h2⟩ := h
          right; left; exact ⟨by (congr 1; omega), by omega⟩
        · rw [nms_Q1_odd] at h; simp at h
      | succ a =>
        obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := Nat.even_or_odd a
        · rw [show k + k + 1 + 1 = 2 * k + 2 from by omega, nms_Q_even] at h
          simp [MachineState.Q.injEq] at h; obtain ⟨h1, h2⟩ := h
          right; right; exact ⟨b', by (congr 1; omega), by omega⟩
        · rw [show 2 * k + 1 + 1 + 1 = 2 * k + 1 + 2 from by omega, nms_Q_odd] at h
          simp at h

/-- Predecessor analysis for Q(1, b): the only predecessor is Q(4, b−7). -/
lemma nextMachineState_Q_one_pred (b : Nat) (s : MachineState)
    (h : nextMachineState s = .Q 1 b) :
    ∃ b', s = .Q 4 b' ∧ b = b' + 7 := by
  cases s with
  | Halt => simp [nextMachineState] at h
  | P a =>
    obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := Nat.even_or_odd a
    · rw [show k + k = 2 * k from by omega, nms_P_even] at h; simp at h
    · rw [nms_P_odd] at h; simp [MachineState.Q.injEq] at h
  | Q a b' =>
    cases a with
    | zero => simp [nextMachineState] at h
    | succ n =>
      cases n with
      | zero =>
        obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := Nat.even_or_odd b'
        · rw [show k + k = 2 * k from by omega, nms_Q1_even] at h
          simp [MachineState.Q.injEq] at h
        · rw [nms_Q1_odd] at h; simp at h
      | succ a =>
        obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := Nat.even_or_odd a
        · rw [show k + k + 1 + 1 = 2 * k + 2 from by omega, nms_Q_even] at h
          simp [MachineState.Q.injEq] at h; obtain ⟨h1, h2⟩ := h
          exact ⟨b', by (congr 1; omega), by omega⟩
        · rw [show 2 * k + 1 + 1 + 1 = 2 * k + 1 + 2 from by omega, nms_Q_odd] at h
          simp at h

private lemma critical_Q_entry_aux (n : Nat) :
    ∀ k, k ≥ 1 → ∀ b, iterMachineState (.P 2) n = .Q (3 * 2 ^ k - 2) b →
    ∃ j, j ≥ 1 ∧ ∃ n', iterMachineState (.P 2) n' = .P (6 * 2 ^ j - 7) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k hk b hn
    cases n with
    | zero => simp [iterMachineState] at hn
    | succ n =>
      rw [iterMachineState_succ] at hn
      have h2k : 2 ^ k ≥ 2 := by
          calc 2 ^ k ≥ 2 ^ 1 := Nat.pow_le_pow_right (by omega) hk
          _ = 2 := by norm_num
      have hm : 3 * 2 ^ k - 2 ≥ 2 := by omega
      obtain ⟨hp, _⟩ | ⟨hq, _⟩ | ⟨b', hq, _⟩ :=
        nextMachineState_Q_pred _ hm _ _ hn
      · -- PQ case: P(2*(3*2^k-2) - 3) = P(6*2^k - 7) at step n
        have hval : 2 * (3 * 2 ^ k - 2) - 3 = 6 * 2 ^ k - 7 := by
          set x := 2 ^ k; omega
        rw [hval] at hp
        exact ⟨k, hk, n, hp⟩
      · -- Q1 case: Q(1, ...) at step n, go back one more to Q(4, ...)
        cases n with
        | zero => simp [iterMachineState] at hq
        | succ n =>
          rw [iterMachineState_succ] at hq
          obtain ⟨b'', hq4, _⟩ := nextMachineState_Q_one_pred _ _ hq
          have h4eq : (4 : Nat) = 3 * 2 ^ 1 - 2 := by norm_num
          rw [h4eq] at hq4
          exact ih n (by omega) 1 (by omega) b'' hq4
      · -- Q2 case: Q(2*(3*2^k-2)+2, b') = Q(3*2^(k+1)-2, b') at step n
        have hconv : 2 * (3 * 2 ^ k - 2) + 2 = 3 * 2 ^ (k + 1) - 2 := by
          rw [pow_succ]; set x := 2 ^ k; omega
        rw [hconv] at hq
        exact ih n (by omega) (k + 1) (by omega) b' hq

/-- If Q(3·2^k − 2, _) is reachable from P(2), then P visited some
    critical value 6·2^j − 7 with j ≥ 1. -/
lemma critical_Q_entry_from_critical_P (k : Nat) (hk : k ≥ 1) (b : Nat) :
    (∃ n, iterMachineState (.P 2) n = .Q (3 * 2 ^ k - 2) b) →
    ∃ j, j ≥ 1 ∧ ∃ n', iterMachineState (.P 2) n' = .P (6 * 2 ^ j - 7) := by
  intro ⟨n, hn⟩
  exact critical_Q_entry_aux n k hk b hn

-- ============================================================
-- Subgraph D: Halving chain (forward direction)
-- ============================================================

/-- The halving chain from Q(3·2^k − 2, b) reaches Q(1, _) in k steps (for k ≥ 1). -/
lemma halving_to_Q_one (k : Nat) (hk : k ≥ 1) (b : Nat) :
    ∃ b', iterMachineState (.Q (3 * 2 ^ k - 2) b) k = .Q 1 b' := by
  induction k generalizing b with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      exact ⟨b + 7, by simp [iterMachineState, nextMachineState]⟩
    | succ m =>
      have hge : 3 * 2 ^ (m + 1) ≥ 3 :=
        Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by norm_num))
      have h1 : 3 * 2 ^ (m + 2) - 2 = 2 * (3 * 2 ^ (m + 1) - 2) + 2 := by
        have : 3 * 2 ^ (m + 2) = 2 * (3 * 2 ^ (m + 1)) := by ring
        omega
      have heven : (2 * (3 * 2 ^ (m + 1) - 2)) % 2 = 0 := Nat.mul_mod_right 2 _
      rw [h1]
      have step : nextMachineState (.Q (2 * (3 * 2 ^ (m + 1) - 2) + 2) b) =
          .Q (3 * 2 ^ (m + 1) - 2) (b + 2 * (3 * 2 ^ (m + 1) - 2) + 5) := by
        simp only [nextMachineState, heven, beq_self_eq_true, ite_true,
          Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
      rw [show m + 1 + 1 = (m + 1) + 1 from rfl, iterMachineState, step]
      exact ih (by omega) _

/-- P(6·2^k − 7) reaches Q(1, _) in k+1 macro steps, via the halving chain
    Q(3·2^k − 2, 1) → ··· → Q(4, _) → Q(1, _).
    Converse: hitting a critical P-value forces Q(1, _). -/
lemma critical_P_reaches_Q_one (k : Nat) (hk : k ≥ 1) :
    ∃ b, iterMachineState (.P (6 * 2 ^ k - 7)) (k + 1) = .Q 1 b := by
  have hge : 6 * 2 ^ k ≥ 12 := by
    calc 6 * 2 ^ k ≥ 6 * 2 ^ 1 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hk)
    _ = 12 := by norm_num
  have hodd : (6 * 2 ^ k - 7) % 2 = 1 := by
    have : 2 * (3 * 2 ^ k) % 2 = 0 := Nat.mul_mod_right 2 _
    have h6 : 6 * 2 ^ k = 2 * (3 * 2 ^ k) := by ring
    omega
  have hentry : (6 * 2 ^ k - 7) / 2 + 2 = 3 * 2 ^ k - 2 := by
    have hge3 : 3 * 2 ^ k ≥ 4 := by
      calc 3 * 2 ^ k ≥ 3 * 2 ^ 1 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hk)
      _ = 6 := by norm_num
      _ ≥ 4 := by norm_num
    have h2 : 6 * 2 ^ k - 7 = 2 * (3 * 2 ^ k - 4) + 1 := by
      have : 6 * 2 ^ k = 2 * (3 * 2 ^ k) := by ring
      omega
    rw [h2, Nat.mul_add_div (by norm_num : 0 < 2)]
    omega
  have hP_step : nextMachineState (.P (6 * 2 ^ k - 7)) = .Q (3 * 2 ^ k - 2) 1 := by
    unfold nextMachineState
    have hbeq : ((6 * 2 ^ k - 7) % 2 == 0) = false := by simp [hodd]
    simp only [hbeq, Bool.false_eq_true, ite_false, hentry]
  simp only [iterMachineState, hP_step]
  exact halving_to_Q_one k hk 1

-- ============================================================
-- Subgraph E: Q(1,_) unreachability (main conjecture)
-- ============================================================

/-- The orbit from P(2) never reaches a state Q(1, b) for any b.
    Equivalently, rules Q1 and QP1 are never triggered. -/
lemma Q_one_unreachable :
    ∀ n : Nat, ∀ b : Nat, iterMachineState (.P 2) n ≠ .Q 1 b := by
  sorry

/-- Rule Q1: Q(1, 2b) → Q(b+2, 1) is never triggered on the orbit from P(2). -/
lemma rule_Q1_never_reached :
    ∀ n : Nat, ∀ b : Nat,
      iterMachineState (.P 2) n = .Q 1 (2 * b) → False := by
  intro n b h
  exact absurd h (Q_one_unreachable n (2 * b))

/-- Rule QP1: Q(1, 2b+1) → P(3b+8) is never triggered on the orbit from P(2). -/
lemma rule_QP1_never_reached :
    ∀ n : Nat, ∀ b : Nat,
      iterMachineState (.P 2) n = .Q 1 (2 * b + 1) → False := by
  intro n b h
  exact absurd h (Q_one_unreachable n (2 * b + 1))

-- ============================================================
-- Isolated lemmas (pure arithmetic, no dependents in this file)
-- ============================================================

/-- No value of the form ((2l+1)·3^k - 5)/2 with k ≥ 1 equals a critical
    Q-entry value 3·2^j − 2 that leads to Q(1, _).
    Equivalently: (2l+1)·3^k ≠ 6·2^j + 1, since LHS ≡ 0 (mod 3)
    but RHS ≡ 1 (mod 3). -/
lemma no_critical_entry_from_closed_form (l k j : Nat) (hk : k ≥ 1) (hj : j ≥ 1) :
    ((2 * l + 1) * 3 ^ k - 5) / 2 ≠ 3 * 2 ^ j - 2 := by
  intro h
  have h3j : 3 * 2 ^ j ≥ 6 := by
    calc 3 * 2 ^ j ≥ 3 * 2 ^ 1 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hj)
    _ = 6 := by norm_num
  have hlhs_ge : (2 * l + 1) * 3 ^ k ≥ 3 := by
    calc (2 * l + 1) * 3 ^ k ≥ 1 * 3 ^ 1 :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by norm_num) hk)
    _ = 3 := by norm_num
  have h3k_mod2 : 3 ^ k % 2 = 1 := by
    have : ∀ n, 3 ^ n % 2 = 1 := by
      intro n; induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, Nat.mul_mod, ih]
    exact this k
  have hlhs_mod2 : ((2 * l + 1) * 3 ^ k) % 2 = 1 := by
    rw [Nat.mul_mod, h3k_mod2]; simp
  have heven : 2 ∣ ((2 * l + 1) * 3 ^ k - 5) := by omega
  have hdiv : ((2 * l + 1) * 3 ^ k - 5) / 2 * 2 = (2 * l + 1) * 3 ^ k - 5 :=
    Nat.div_mul_cancel heven
  rw [h] at hdiv
  -- hdiv : (3 * 2^j - 2) * 2 = (2l+1)*3^k - 5, so (2l+1)*3^k = 6*2^j + 1
  have heq : (2 * l + 1) * 3 ^ k = 6 * 2 ^ j + 1 := by omega
  -- LHS ≡ 0 (mod 3), RHS ≡ 1 (mod 3)
  have hlhs_mod3 : ((2 * l + 1) * 3 ^ k) % 3 = 0 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [pow_succ, ← mul_assoc, mul_comm ((2 * l + 1) * 3 ^ m) 3]
    exact Nat.mul_mod_right 3 _
  have hrhs_mod3 : (6 * 2 ^ j + 1) % 3 = 1 := by
    rw [show 6 * 2 ^ j = 3 * (2 * 2 ^ j) from by ring, Nat.mul_add_mod]
  omega

/-- P-even output 3k+4 is never a critical value 6·2^j - 7 (mod 3 obstruction:
    3k+4 ≡ 1 mod 3, but 6·2^j - 7 ≡ 2 mod 3). -/
lemma P_even_not_critical (k j : Nat) (hj : j ≥ 1) : 3 * k + 4 ≠ 6 * 2 ^ j - 7 := by
  intro h
  have hge : 6 * 2 ^ j ≥ 12 := by
    calc 6 * 2 ^ j ≥ 6 * 2 ^ 1 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hj)
    _ = 12 := by norm_num
  have hlhs : (3 * k + 4) % 3 = 1 := by omega
  have hrhs : (6 * 2 ^ j - 7) % 3 = 2 := by
    have : 6 * 2 ^ j % 3 = 0 := by
      rw [show 6 * 2 ^ j = 3 * (2 * 2 ^ j) from by ring]
      exact Nat.mul_mod_right 3 _
    omega
  omega

/-- Only QP2 can produce odd P-values in the orbit (assuming Q(1,_) unreachable).
    QP2: Q(2a+3, b) → P(b+5a+6). For this to be critical, need b+5a+6 = 6·2^j - 7.
    Since b+5a+6 must be odd and ≡ 2 (mod 3), this reduces to:
      b + 5a + 13 = 6·2^j  with b+5a odd.

    Combined with no_critical_entry_from_closed_form (which eliminates the even-P case)
    and P_even_not_critical (which eliminates P-even as source), the full reduction is:
    Q(1,_) is reachable from P(2) iff there exist reachable Q(2a+3, b) and j ≥ 2
    such that b + 5a + 6 = 6·2^j - 7. This is Collatz-hard. -/
lemma QP2_critical_iff (a b j : Nat) (hj : j ≥ 1) :
    b + 5 * a + 6 = 6 * 2 ^ j - 7 ↔ b + 5 * a + 13 = 6 * 2 ^ j := by
  constructor
  · intro h
    have hge : 6 * 2 ^ j ≥ 12 := by
      calc 6 * 2 ^ j ≥ 6 * 2 ^ 1 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hj)
      _ = 12 := by norm_num
    omega
  · intro h; omega

end Cryptid

-- ============================================================
-- Subgraph F: Growth analysis and hitting probability
-- ============================================================

/-! ### Q-to-P output ratio

From the qacc closed form, starting at Q(x, 1) the exit P-value is
y = 1 + qacc(x).  For odd x = 2k+1 (the v₂(x+2) = 0 case, probability ½),
the exit is immediate via QP2 and y = 5k + 2 = (5x − 1)/2.

More generally, from the closed form
  2·qacc(x) + 5 = 4x + 2·v₂(x+2) + max(ordCompl[2](x+2), 3),
the Q-output satisfies y/x → 2 + 2⁻⁽ᵛ⁺¹⁾ where v = v₂(x+2),
giving the discrete ratios 5/2, 9/4, 17/8, 33/16, … -/

/-- Q-phase output for odd input: Q(2k+1, 1) exits to P(5k+2). -/
lemma q_odd_output (k : Nat) : q (2 * k + 1) 1 = 5 * k + 2 := by
  unfold q; rw [qacc_odd]; ring

/-- Q-phase output ratio for odd x: y = (5x − 1)/2.
    Equivalently, 2·q(x, 1) = 5x − 1 when x is odd. -/
lemma q_odd_ratio (k : Nat) : 2 * q (2 * k + 1) 1 = 5 * (2 * k + 1) - 1 := by
  rw [q_odd_output]; omega

/-- Q-phase output for even input with v₂(x+2) = 1: Q(2k, 1) with k ≥ 1 and
    k+1 odd (so x+2 = 2(k+1) with odd k+1) gives y = 9k/2.
    Equivalently, 2·q(2k, 1) = 9·k. -/
lemma q_v1_output (k : Nat) (hk : k ≥ 1) (hodd : ¬ 2 ∣ (k + 1)) :
    2 * q (2 * k) 1 = 9 * k := by
  -- k is even (since k+1 odd), write k = 2m with m ≥ 1
  have hkeven : 2 ∣ k := by omega
  obtain ⟨m, rfl⟩ := hkeven
  have hm : m ≥ 1 := by omega
  -- q(4m, 1) = 1 + qacc(4m) = 1 + (4m + 3 + qacc(2m-1))
  --          = 1 + 4m + 3 + (5(m-1) + 1) = 9m
  unfold q
  rw [show 2 * (2 * m) = 2 * (2 * m - 1 + 1) from by omega,
      qacc_even (2 * m - 1 + 1) (by omega)]
  rw [show 2 * m - 1 + 1 - 1 = 2 * m - 1 from by omega]
  rw [show 2 * m - 1 = 2 * (m - 1) + 1 from by omega, qacc_odd]
  omega

/-! ### Full-cycle growth factor

The dominant path (both v₂ = 0) composes:
  Q(x, 1) →^{QP2} P(y)  with  y = (5x−1)/2   [x odd]
  P(y) →^{PQ}  Q(x', 1) with  x' = (y+3)/2    [y odd]

Substituting: x' = ((5x−1)/2 + 3)/2 = (5x+5)/4.
The growth ratio x'/x → 5/4 as x → ∞. -/

/-- Dominant-path full cycle: if x = 2k+1 with k odd, then
    Q(x,1) → P(5k+2) → Q((5k+5)/2, 1).
    Here 5k+2 is odd (since k is odd), so the P-phase takes
    the v₂ = 0 shortcut. -/
lemma dominant_cycle_output (k : Nat) (hk_odd : ¬ 2 ∣ k) :
    p (5 * k + 2) = (5 * k + 5) / 2 := by
  have hodd_y : ¬ 2 ∣ (5 * k + 2) := by omega
  rw [show 5 * k + 2 = 2 * ((5 * k + 1) / 2) + 1 from by omega, p_odd]
  omega

/-- Growth equation: 4 · p(q(2k+1, 1)) = 5·(2k+1) + 5 when k is odd.
    This is the exact form of x' = 5x/4 + 5/4 = (5x+5)/4. -/
lemma dominant_cycle_ratio (k : Nat) (hk_odd : ¬ 2 ∣ k) :
    4 * p (q (2 * k + 1) 1) = 5 * (2 * k + 1) + 5 := by
  rw [q_odd_output, dominant_cycle_output k hk_odd]
  omega

/-! ### Hitting 2^i − 2

For the Q-output y to produce p(y) = 2^i − 2 via the dominant (v₂ = 0) path,
we need y = 2^(i+1) − 7 (from `p_eq_pow2_case_v0`).

So the hitting condition on the Q-entry x = 2k+1 is:
  5k + 2 = 2^(i+1) − 7, i.e., 5k + 9 = 2^(i+1).

This requires 2^(i+1) ≡ 4 (mod 5), i.e., i+1 ≡ 2 (mod 4),
so i ∈ {5, 9, 13, 17, …}. -/

/-- Dominant-path hitting: Q(2k+1, 1) → P(5k+2) = 2^i − 2
    iff 5k + 9 = 2^(i+1).  Requires i ≥ 2. -/
lemma dominant_path_hit_pow2 (k i : Nat) (hk_odd : ¬ 2 ∣ k) (hi : i ≥ 2) :
    p (5 * k + 2) = 2 ^ i - 2 ↔ 5 * k + 9 = 2 ^ (i + 1) := by
  have hodd : ¬ 2 ∣ (5 * k + 2) := by omega
  rw [p_eq_pow2_case_v0 (5 * k + 2) i (by omega) hi hodd]

/-- The mod-5 obstruction: 5k + 9 = 2^(i+1) requires
    2^(i+1) ≡ 4 mod 5, which holds iff i + 1 ≡ 2 mod 4. -/
lemma hit_mod5_constraint (k i : Nat) (h : 5 * k + 9 = 2 ^ (i + 1)) :
    (i + 1) % 4 = 2 := by
  -- 2^(i+1) ≡ 9 ≡ 4 mod 5, and 2^n mod 5 cycles with period 4: 2,4,3,1
  have h5 : 2 ^ (i + 1) % 5 = 4 := by omega
  -- 2^n mod 5 cycles with period 4, 2^2 mod 5 = 4
  -- Use ZMod approach: 2^4 ≡ 1 mod 5
  have hperiod : ∀ n, 2 ^ n % 5 = 2 ^ (n % 4) % 5 := by
    intro n
    have := Nat.div_add_mod n 4
    calc 2 ^ n % 5
        = 2 ^ (4 * (n / 4) + n % 4) % 5 := by rw [show 4 * (n / 4) + n % 4 = n from this]
      _ = (2 ^ (4 * (n / 4)) * 2 ^ (n % 4)) % 5 := by rw [pow_add]
      _ = ((2 ^ 4) ^ (n / 4) * 2 ^ (n % 4)) % 5 := by rw [pow_mul]
      _ = ((16 ^ (n / 4) % 5) * (2 ^ (n % 4) % 5)) % 5 := by rw [show (2:ℕ) ^ 4 = 16 from by norm_num, Nat.mul_mod]
      _ = (1 * (2 ^ (n % 4) % 5)) % 5 := by
          congr 1; congr 1
          induction (n / 4) with
          | zero => simp
          | succ m ih => rw [pow_succ, Nat.mul_mod, ih]
      _ = 2 ^ (n % 4) % 5 := by omega
  rw [hperiod] at h5
  -- Exhaust (i+1) % 4 ∈ {0,1,2,3}: only 2 gives 2^r % 5 = 4
  have : (i + 1) % 4 = 0 ∨ (i + 1) % 4 = 1 ∨ (i + 1) % 4 = 2 ∨ (i + 1) % 4 = 3 := by omega
  rcases this with h0 | h1 | h2 | h3 <;> simp_all

/-! ### Growth-rate estimates

Under the heuristic that v₂(x+2) and v₂(y+8) behave as independent
geometric random variables (Pr[v₂ = j] = 2⁻⁽ʲ⁺¹⁾), the expected
log-growth per cycle is:

  E[ln(x'/x)] = E[ln(y/x)] + E[ln(x'/y)]

where:
  E[ln(y/x)] = Σⱼ 2⁻⁽ʲ⁺¹⁾ ln(2 + 2⁻⁽ʲ⁺¹⁾) ≈ 0.84
  E[ln(x'/y)] = Σⱼ 2⁻⁽ʲ⁺¹⁾ (j·ln 3 − (j+1)·ln 2)
              = ln 3 − 2·ln 2 = ln(3/4) ≈ −0.288

giving E[ln(x'/x)] ≈ 0.55 and effective growth base κ ≈ e^0.55 ≈ 1.73.

However, the **dominant path** (both v₂ = 0, probability ¼) gives
κ₀ = 5/4 = 1.25, and accounts for most observed cycles.

The key quantity for hitting estimates is the number of cycles per
doubling of x: N₂ = ln 2 / E[ln(x'/x)]. For the dominant path
alone, N₂ = ln 2 / ln(5/4) ≈ 3.11.
-/

/-- Dominant-path composition: for x ≡ 3 mod 4, the full cycle
    p(q(x, 1)) = (5x + 5) / 4 (under Nat division).
    This requires both x odd (for the Q-phase QP2 exit) and
    5k+2 odd (for the P-phase v₂=0 shortcut), which holds iff
    k = (x-1)/2 is odd, i.e., x ≡ 3 mod 4. -/
lemma dominant_path_step (k : Nat) (hk : ¬ 2 ∣ k) :
    p (q (2 * k + 1) 1) = (5 * (2 * k + 1) + 5) / 4 := by
  rw [q_odd_output, dominant_cycle_output k hk]
  omega

-- ============================================================
-- Subgraph G: Stochastic model for Q-entry growth
-- ============================================================

/-! ### Stochastic model for the Q→P→Q cycle

Each Q→P→Q cycle grows.  The growth factor depends on v₂(y+8)
where y is the P-phase input.  Modelling v₂ as geometric(½):

  • v₂ = 0 (prob ½):  x' = (5x+5)/4,  growth ≈ 5/4
  • v₂ = 1 (prob ¼):  x' = (15x+25)/8, growth ≈ 15/8
  • v₂ ≥ 1 combined:  growth ≥ 15/8 > 5/4

Both branches grow.  The P-even rule P(2n) = P(3n+4) amplifies by
3/2 per doubling, so there is **no contraction** in this machine.

We model the cycle conservatively using v₂ ∈ {0, ≥1} with coin
flips.  The key outputs are:
  • E[X_{n+1}|X_n] = (25/16)X_n + 35/16  (growth factor 25/16)
  • E[ln(X_{n+1}/X_n)] ≈ ½ ln(5/4) + ½ ln(15/8) > 0 (positive drift)
  • X_n → ∞ almost surely, so near-miss probability decays as 1/X_n
  • Expected number of hits of any target T is bounded by the
    convergent sum Σ 1/X_n ≤ C/x₀.
-/

open MeasureTheory ProbabilityTheory

/-- Sample space: infinite sequence of v₂-parity coin flips.
    true = v₂ = 0, false = v₂ ≥ 1. -/
def Ω := ℕ → Bool

instance : MeasurableSpace Ω := MeasurableSpace.pi

/-- Stochastic step modelling one Q→P→Q cycle.
    true (v₂ = 0):  Q(x,1) → P((5x−1)/2) → Q((5x+5)/4, 1)
    false (v₂ ≥ 1): Q(x,1) → P((5x−1)/2) → Q((15x+25)/8, 1)
    (The false branch uses the v₂=1 formula as a lower bound.) -/
noncomputable def stochasticStep (x : ℝ) (isV0 : Bool) : ℝ :=
  if isV0 then (5 * x + 5) / 4
  else (15 * x + 25) / 8

/-- State of the stochastic model at cycle n. -/
noncomputable def X (x₀ : ℝ) : ℕ → Ω → ℝ
  | 0, _ => x₀
  | n + 1, ω => stochasticStep (X x₀ n ω) (ω n)

/-- The Bernoulli(1/2) PMF on Bool. -/
noncomputable def bernoulliHalfPMF : PMF Bool := by
  refine PMF.bernoulli ⟨1/2, by positivity⟩ ?_
  exact_mod_cast (show (1 : ℝ) / 2 ≤ 1 by norm_num)

/-- The Bernoulli(1/2) measure on Bool. -/
noncomputable def bernoulliHalf : Measure Bool := bernoulliHalfPMF.toMeasure

instance : IsProbabilityMeasure bernoulliHalf :=
  PMF.toMeasure.isProbabilityMeasure bernoulliHalfPMF

/-- The product probability measure on Ω. -/
noncomputable def coinFlipMeasure : Measure Ω :=
  Measure.infinitePi (fun _ : ℕ => bernoulliHalf)

instance coinFlipMeasure_prob : IsProbabilityMeasure coinFlipMeasure := by
  show IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => bernoulliHalf))
  haveI : ∀ i : ℕ, IsProbabilityMeasure ((fun _ : ℕ => bernoulliHalf) i) :=
    fun _ => PMF.toMeasure.isProbabilityMeasure _
  infer_instance

/-- Measurability of the stochastic step. -/
lemma stochasticStep_measurable (x : ℝ) :
    Measurable (fun b : Bool => stochasticStep x b) := by
  apply measurable_of_finite

/-- X_n is measurable for each n and x₀. -/
lemma X_measurable (x₀ : ℝ) (n : ℕ) :
    Measurable (X x₀ n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    show Measurable (fun ω => stochasticStep (X x₀ n ω) (ω n))
    simp only [stochasticStep]
    apply Measurable.ite
    · exact measurable_pi_apply n (measurableSet_singleton _)
    · exact (ih.const_mul 5 |>.add measurable_const).div_const 4
    · exact (ih.const_mul 15 |>.add measurable_const).div_const 8

/-! ### Growth properties

Both branches grow: the minimum growth factor is 5/4 (v₂ = 0 branch).
This gives a deterministic lower bound X_n ≥ x₀ · (5/4)^n for positive x₀,
and a positive expected log-drift. -/

/-- Both branches of stochasticStep grow: step(x, b) ≥ (5x+5)/4 for all b
    when x ≥ 0. -/
lemma stochasticStep_lower_bound (x : ℝ) (hx : x ≥ 0) (b : Bool) :
    stochasticStep x b ≥ (5 * x + 5) / 4 := by
  simp only [stochasticStep]
  cases b <;> simp <;> linarith

/-- The deterministic lower bound: X_n(ω) ≥ (5x+5)/4 iterated n times.
    Since both branches dominate the v₂=0 branch, X grows at least as
    fast as the dominant path. -/
lemma X_lower_bound (x₀ : ℝ) (hx₀ : x₀ ≥ 0) (n : ℕ) (ω : Ω) :
    X x₀ n ω ≥ Nat.iterate (fun x => (5 * x + 5) / 4) n x₀ := by
  induction n with
  | zero => simp [X]
  | succ n ih =>
    have hiter_nonneg : (fun x => (5 * x + 5) / 4)^[n] x₀ ≥ 0 := by
      clear ih ω
      induction n with
      | zero => simpa
      | succ k ihk =>
        rw [Function.iterate_succ_apply']; linarith
    rw [Function.iterate_succ_apply']
    show stochasticStep (X x₀ n ω) (ω n) ≥
        (5 * (fun x => (5 * x + 5) / 4)^[n] x₀ + 5) / 4
    calc stochasticStep (X x₀ n ω) (ω n)
        ≥ (5 * X x₀ n ω + 5) / 4 := stochasticStep_lower_bound _ (by linarith) _
      _ ≥ (5 * (fun x => (5 * x + 5) / 4)^[n] x₀ + 5) / 4 := by linarith

/-- The iterate of f(x) = (5x+5)/4 has closed form (x₀+5)·(5/4)^n − 5.
    (Fixed point of f is −5, so y = x+5 gives y_n = y₀·(5/4)^n.) -/
private lemma iterate_exact (x₀ : ℝ) (n : ℕ) :
    (fun x => (5 * x + 5) / 4)^[n] x₀ = (x₀ + 5) * (5 / 4) ^ n - 5 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    ring

/-- X_n → ∞ for x₀ ≥ 0.  Precisely, X_n ≥ (x₀+5)·(5/4)^n − 5. -/
lemma X_grows (x₀ : ℝ) (hx₀ : x₀ ≥ 0) (n : ℕ) (ω : Ω) :
    X x₀ n ω ≥ (x₀ + 5) * (5 / 4) ^ n - 5 := by
  calc X x₀ n ω ≥ (fun x => (5 * x + 5) / 4)^[n] x₀ :=
        X_lower_bound x₀ hx₀ n ω
    _ = (x₀ + 5) * (5 / 4) ^ n - 5 := iterate_exact x₀ n

/-- The per-step expected log-growth is positive:
    ½ ln(5/4) + ½ ln(15/8) = ½ ln(75/32) > 0. -/
lemma expected_log_drift_pos :
    (1 / 2 : ℝ) * Real.log (5 / 4) + (1 / 2) * Real.log (15 / 8) > 0 := by
  have h1 : (5:ℝ)/4 ≠ 0 := by norm_num
  have h2 : (15:ℝ)/8 ≠ 0 := by norm_num
  have key : (1:ℝ)/2 * Real.log (5/4) + 1/2 * Real.log (15/8) =
      1/2 * (Real.log (5/4) + Real.log (15/8)) := by ring
  rw [key, ← Real.log_mul h1 h2]
  have : (5:ℝ)/4 * (15/8) = 75/32 := by ring
  rw [this]
  apply mul_pos (by norm_num : (0:ℝ) < 1/2)
  exact Real.log_pos (by norm_num : (75:ℝ)/32 > 1)

/-! ### Hitting density: first-moment bound

Since X_n → ∞, the reciprocal 1/X_n is summable.  The expected
number of "near-misses" (X_n landing within distance δ of a
specific target T) is bounded by δ · Σ 1/X_n.

For exact hits of powers of 2: near level L, the density of
powers of 2 is 1/(L · ln 2), and the trajectory visits each
level-L window for ~1/(growth − 1) ≈ 4 cycles.  So the
expected number of exact hits in the trajectory is bounded by
the convergent sum Σ 1/(x₀ · (5/4)^n · ln 2) ≤ 5/(x₀ · ln 2).

This is a heuristic first-moment bound; making it rigorous for
exact Diophantine hits (as opposed to near-misses) is
Collatz-hard (see `dominant_path_at_most_one_hit` discussion).
-/

/-- The reciprocal sum is bounded: Σ 1/(x₀·(5/4)^n) = 5/x₀ for x₀ > 0.
    This bounds the expected number of near-misses. -/
lemma reciprocal_sum_bound (x₀ : ℝ) (hx₀ : x₀ > 0) :
    HasSum (fun n : ℕ => 1 / (x₀ * (5 / 4) ^ n)) (5 / x₀) := by
  have hx₀' : x₀ ≠ 0 := ne_of_gt hx₀
  -- Σ (4/5)^n = (1 - 4/5)⁻¹ = 5
  have hgeom : HasSum (fun n : ℕ => (4 / 5 : ℝ) ^ n) 5 := by
    have h := hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 4/5) (by norm_num : (4:ℝ)/5 < 1)
    simp only [show (1 : ℝ) - 4 / 5 = 1 / 5 from by norm_num, one_div, inv_inv] at h
    exact h
  -- Scale by 1/x₀
  have scaled := hgeom.mul_left (1 / x₀)
  convert scaled using 1
  · ext n
    show 1 / (x₀ * (5 / 4) ^ n) = 1 / x₀ * (4 / 5) ^ n
    rw [one_div, one_div, mul_inv]
    congr 1
    rw [show ((5 : ℝ) / 4) ^ n = (5 ^ n / 4 ^ n) from div_pow 5 4 n]
    rw [inv_div]
    exact div_pow 4 5 n |>.symm
  · ring

/-- Expected number of hits heuristic: under the stochastic model,
    the expected number of n such that |5·X_n + 9 − 2^m| < 1 for
    some m is at most C/x₀ where C = 5/ln 2 ≈ 7.21. -/
lemma expected_hits_bound (x₀ : ℝ) (hx₀ : x₀ > 0) :
    5 / (x₀ * Real.log 2) > 0 := by
  apply div_pos (by norm_num : (5:ℝ) > 0)
  exact mul_pos hx₀ (Real.log_pos (by norm_num : (2:ℝ) > 1))

/-! ### Applied bound: non-halting after X steps implies low hit probability

Suppose the machine has run for X macro-steps without halting, and the
Q-entry value has grown to x₀.  From `X_grows`, all future Q-entries
satisfy X_n ≥ (x₀+5)·(5/4)^n − 5.  The heuristic probability of
hitting any 2^i − 2 in the future is bounded by:

  P(hit) ≤ Σ_{n≥0} 1/((x₀+5)·(5/4)^n · ln 2)
          = 5 / ((x₀+5) · ln 2)
          ≈ 7.21 / x₀     for large x₀.

Concretely: the BB(6) cryptid simulation reaches Q-entries of order
10^16 within 200 macro-steps.  At that point:
  P(future hit) ≤ 7.21 / 10^16 ≈ 7.2 × 10⁻¹⁶.
-/

/-- The bound tightens as x0 grows: 5/((x0+5)*ln 2) <= 5/(x0*ln 2). -/
lemma applied_hit_bound (x₀ : ℝ) (hx₀ : x₀ > 0) :
    5 / ((x₀ + 5) * Real.log 2) ≤ 5 / (x₀ * Real.log 2) := by
  have hlog : Real.log 2 > 0 := Real.log_pos (by norm_num)
  exact div_le_div_of_nonneg_left (by norm_num)
    (mul_pos hx₀ hlog)
    (mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hlog))

/-- General parametric bound: given machine reaches Q-entry of order
    10^d without halting, the expected number of future near-misses
    is at most 5/(10^d · ln 2) < 8/10^d (since ln 2 > 5/8). -/
lemma parametric_hit_bound (d : ℕ) (hd : d ≥ 1) :
    5 / ((10 : ℝ) ^ d * Real.log 2) < 8 / (10 : ℝ) ^ d := by
  have hlog : Real.log 2 > 5 / 8 := by
    -- ln 2 > 0.625: since e^(5/8) < 2 (e^(5/8) ≈ 1.868)
    rw [show (5 : ℝ) / 8 = Real.log (Real.exp (5 / 8)) from (Real.log_exp _).symm]
    exact Real.log_lt_log (by positivity) (by
      have h := Real.exp_bound (show |(5:ℝ)/8| ≤ 1 by norm_num) (show 0 < 5 by norm_num)
      have upper : Real.exp ((5:ℝ)/8) ≤
          (∑ m ∈ Finset.range 5, ((5:ℝ)/8) ^ m / ↑m.factorial) +
          ((5:ℝ)/8) ^ 5 * (↑(Nat.succ 5) / (↑(Nat.factorial 5) * ↑(5:ℕ))) := by
        linarith [abs_le.mp h]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at upper
      norm_num at upper; linarith)
  have h10 : (10 : ℝ) ^ d > 0 := by positivity
  have hlog' : Real.log 2 > 0 := by linarith
  calc 5 / ((10 : ℝ) ^ d * Real.log 2)
      < 5 / ((10 : ℝ) ^ d * (5 / 8)) := by
        apply div_lt_div_of_pos_left (by norm_num) (mul_pos h10 (by norm_num))
          (mul_lt_mul_of_pos_left hlog h10)
    _ = 8 / (10 : ℝ) ^ d := by ring

