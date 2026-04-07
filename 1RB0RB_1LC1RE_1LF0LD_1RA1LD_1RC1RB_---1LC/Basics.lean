import Mathlib.Tactic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic
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
