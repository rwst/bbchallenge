import Mathlib.Tactic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic

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
