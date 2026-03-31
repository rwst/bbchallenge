import BusyLean
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open BusyLean

namespace Antihydra

-- The Antihydra TM (BB(6) candidate)
def antihydra : TM 6 := tm! "1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA"

-- 5. The Mathematical "High-Level" Model
structure MathState where
  a : Nat
  b : Nat
deriving Repr, Inhabited, DecidableEq

def nextMathState (m : MathState) : Option MathState :=
  let n := m.a / 2
  if n ≥ 1 then
    if m.a % 2 == 0 then
      some { a := 3 * n + 2, b := m.b + 2 }
    else
      if m.b == 0 then
        none
      else
        some { a := 3 * n + 3, b := m.b - 1 }
  else
    none

-- Total version of the map, ignoring the halting condition (b=0 on odd branch gives b-1=0 in ℕ)
def A (ab : ℕ × ℕ) : ℕ × ℕ :=
  let (a, b) := ab
  let n := a / 2
  if a % 2 == 0 then (3 * n + 2, b + 2)
  else              (3 * n + 3, b - 1)

-- Macro-level configuration
def P_Config_Pad (b : Nat) (m : Nat) (n : Nat) (p : Nat) : Config 6 :=
  { state := some stE,
    head := false,
    left := ones m ++ [false] ++ ones b,
    right := ones n ++ zeros p
  }

-- Stream-based macro config. No padding parameter — eliminates padding infrastructure.
def SP_Config (b m n : Nat) : SConfig 6 :=
  { state := some stE,
    head := false,
    left := ones m *> [false] *> ones b *> blank∞,
    right := ones n *> blank∞ }

lemma P_Config_Pad_toSP (b m n p : Nat) :
    (P_Config_Pad b m n p).toSConfig = SP_Config b m n := by
  simp [P_Config_Pad, SP_Config, Config.toSConfig]

-- Simp tactic for single TM steps (handles Fin literal vs stX abbreviation mismatch)
scoped macro "ah_simp" : tactic =>
  `(tactic| simp (config := { decide := true }) [run, step, antihydra, P_Config_Pad, ones])

-- Shift rules

lemma A_shift (k : Nat) (L R : List Sym) :
    run antihydra { state := some stA, head := true, left := L, right := ones k ++ R } (k + 1) =
    { state := some stA, head := listHead R false, left := ones (k + 1) ++ L, right := listTail R } := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih => tm_ind_succ ih stA [antihydra]

lemma C_shift (k : Nat) (L R : List Sym) :
    run antihydra { state := some stC, head := true, left := ones k ++ L, right := R } (k + 1) =
    { state := some stC, head := listHead L false, left := listTail L, right := ones (k + 1) ++ R } := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih => tm_ind_succ ih stC [antihydra]

lemma E_shift (k : Nat) (L R : List Sym) :
    run antihydra { state := some stE, head := true, left := L, right := ones k ++ R } (k + 1) =
    { state := some stE, head := listHead R false, left := ones (k + 1) ++ L, right := listTail R } := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih => tm_ind_succ ih stE [antihydra]

-- Macro Loop Steps

theorem tm_P_step (b m n p : Nat) :
    run antihydra (P_Config_Pad b (m+2+2) n (p+2)) (2*n + 12) = P_Config_Pad b (m+2) (n+3) (p+1) := by
  tm_exec [antihydra, P_Config_Pad] shifts [A_shift, C_shift, E_shift]


theorem tm_P_multistep (b m n p k : Nat) :
    run antihydra (P_Config_Pad b (m+2 + 2*k) n (p+1 + k)) (k*(2*n + 3*k + 9)) = P_Config_Pad b (m+2) (n+3*k) (p+1) := by
  induction k generalizing n with
  | zero => ring_nf; rfl
  | succ k' ih =>
    rw [show (k'+1)*(2*n+3*(k'+1)+9) = (2*n+12) + k'*(2*(n+3)+3*k'+9) from by ring,
        run_add,
        show m+2+2*(k'+1) = (m+2*k')+2+2 from by omega,
        show p+1+(k'+1) = (p+k')+2 from by omega,
        tm_P_step,
        show (m+2*k')+2 = m+2+2*k' from by omega,
        show (p+k')+1 = p+1+k' from by omega,
        ih,
        show (n+3)+3*k' = n+3*(k'+1) from by omega]

-- Even Endgame (m=0)
theorem tm_even_endgame (b N p : Nat) :
    (run antihydra (P_Config_Pad b 0 N (p+2)) 2).state = none := by
  rw [show (2:Nat) = 1 + 1 from rfl, run_add]; cases b <;> ah_simp

-- Odd Endgame (m=3, b>0)
theorem tm_odd_endgame (b' N p : Nat) :
    run antihydra (P_Config_Pad (b' + 1) 3 N (p+2)) (3*N + 20) = P_Config_Pad b' (N+6) 0 p := by
  tm_exec [antihydra, P_Config_Pad] shifts [A_shift, C_shift, E_shift]
  -- Remaining: tape folding for final config
  simp only [ones_cons_append]
  congr 1; unfold ones repeatSym; congr 1; omega

-- Even endgame: from a=2 to valid loop start with a=N+5, b=b+2
theorem tm_even_endgame_to_loop (b N p : Nat) :
    run antihydra (P_Config_Pad b 2 N (p+2)) (3*N + 2*b + 26) = P_Config_Pad (b+2) (N+5) 0 p := by
  tm_exec [antihydra, P_Config_Pad] shifts [A_shift, C_shift, E_shift]
  cases b with
  | zero =>
    simp only [ones_zero, Nat.mul_zero, Nat.add_zero]
    tm_exec [antihydra, P_Config_Pad] shifts [A_shift, C_shift, E_shift]
    simp only [ones_cons_append]
    congr 1; unfold ones repeatSym; congr 1; omega
  | succ b' =>
    rw [show N + 2 * (b' + 1) + 17 = N + 2 * b' + 19 from by omega]
    tm_exec [antihydra, P_Config_Pad]
    rw [show N + 2 * b' + 18 = (b' + 1) + (N + b' + 17) from by omega, run_add]
    conv => lhs; enter [2]; rw [show (2 : Fin 6) = stC from rfl,
      show ones b' = ones b' ++ ([] : List Sym) from (List.append_nil _).symm, C_shift]
    simp only [listHead_nil, listTail_nil]
    tm_exec [antihydra, P_Config_Pad]
    rw [show N + b' + 10 = (b' + 1) + (N + 9) from by omega, run_add]
    simp only [show (4 : Fin 6) = stE from rfl, E_shift, listHead, listTail]
    tm_exec [antihydra, P_Config_Pad] shifts [A_shift, C_shift, E_shift]
    simp only [ones_cons_append]
    congr 1; unfold ones repeatSym; congr 1; omega

-- Odd halt endgame: from a=3, b=0, the machine halts
theorem tm_odd_halt_endgame (N p : Nat) :
    (run antihydra (P_Config_Pad 0 3 N (p+2)) (2*N + 12)).state = none := by
  rw [show 2 * N + 12 = (2 * N + 11) + 1 from by omega, run_add]
  have h : run antihydra (P_Config_Pad 0 3 N (p+2)) (2*N + 11) =
    { state := some stF, head := false, left := ([] : List Sym),
      right := true :: true :: false :: ones (N+1+1+1) ++ false :: zeros p } := by
    tm_exec [antihydra, P_Config_Pad] shifts [A_shift, C_shift, E_shift]
  rw [h]; ah_simp

-- SConfig-lifted macro theorems
-- Lifting pattern: rewrite goal to Config form via ← P_Config_Pad_toSP, ← toSConfig_run

theorem stm_P_step (b m n : Nat) :
    srun antihydra (SP_Config b (m+2+2) n) (2*n + 12) = SP_Config b (m+2) (n+3) := by
  rw [← P_Config_Pad_toSP b (m+2+2) n 2, ← P_Config_Pad_toSP b (m+2) (n+3) 1, ← toSConfig_run]
  exact congrArg Config.toSConfig (tm_P_step b m n 0)

theorem stm_P_multistep (b m n k : Nat) :
    srun antihydra (SP_Config b (m+2 + 2*k) n) (k*(2*n + 3*k + 9)) = SP_Config b (m+2) (n+3*k) := by
  rw [← P_Config_Pad_toSP b (m+2+2*k) n (1+k), ← P_Config_Pad_toSP b (m+2) (n+3*k) 1, ← toSConfig_run]
  exact congrArg Config.toSConfig (tm_P_multistep b m n 0 k)

theorem stm_even_endgame (b N : Nat) :
    (srun antihydra (SP_Config b 0 N) 2).state = none := by
  rw [← P_Config_Pad_toSP b 0 N 2, ← toSConfig_run]
  exact tm_even_endgame b N 0

theorem stm_odd_endgame (b' N : Nat) :
    srun antihydra (SP_Config (b'+1) 3 N) (3*N + 20) = SP_Config b' (N+6) 0 := by
  rw [← P_Config_Pad_toSP (b'+1) 3 N 2, ← P_Config_Pad_toSP b' (N+6) 0 0, ← toSConfig_run]
  exact congrArg Config.toSConfig (tm_odd_endgame b' N 0)

theorem stm_even_endgame_to_loop (b N : Nat) :
    srun antihydra (SP_Config b 2 N) (3*N + 2*b + 26) = SP_Config (b+2) (N+5) 0 := by
  rw [← P_Config_Pad_toSP b 2 N 2, ← P_Config_Pad_toSP (b+2) (N+5) 0 0, ← toSConfig_run]
  exact congrArg Config.toSConfig (tm_even_endgame_to_loop b N 0)

theorem stm_odd_halt_endgame (N : Nat) :
    (srun antihydra (SP_Config 0 3 N) (2*N + 12)).state = none := by
  rw [← P_Config_Pad_toSP 0 3 N 2, ← toSConfig_run]
  exact tm_odd_halt_endgame N 0

-- SConfig bridge lemmas

theorem stm_even_full (b n : Nat) :
    ∃ k, k > 0 ∧ srun antihydra (SP_Config b (2*n+2) 0) k = SP_Config (b+2) (3*n+5) 0 := by
  refine ⟨n*(3*n+9) + (9*n+2*b+26), by omega, ?_⟩
  have h1 : srun antihydra (SP_Config b (2*n+2) 0) (n*(3*n+9)) = SP_Config b 2 (3*n) := by
    have h := stm_P_multistep b 0 0 n
    simp only [show 0+2+2*n = 2*n+2 from by omega,
               show (0:Nat)+2 = 2 from by omega,
               show (0:Nat)+3*n = 3*n from by omega] at h; exact h
  show srun antihydra (SP_Config b (2*n+2) 0) (n*(3*n+9) + (9*n+2*b+26)) = _
  rw [srun_add, h1]
  have h2 := stm_even_endgame_to_loop b (3*n); ring_nf at h2 ⊢; exact h2

theorem stm_odd_halt_ex (n : Nat) :
    ∃ k, k > 0 ∧ (srun antihydra (SP_Config 0 (2*n+3) 0) k).state = none := by
  refine ⟨n*(3*n+9) + (6*n+12), by omega, ?_⟩
  have h1 : srun antihydra (SP_Config 0 (2*n+3) 0) (n*(3*n+9)) = SP_Config 0 3 (3*n) := by
    have h := stm_P_multistep 0 1 0 n
    simp only [show 1+2+2*n = 2*n+3 from by omega,
               show (0:Nat)+3*n = 3*n from by omega] at h; exact h
  show (srun antihydra (SP_Config 0 (2*n+3) 0) (n*(3*n+9) + (6*n+12))).state = none
  rw [srun_add, h1, show 6*n+12 = 2*(3*n)+12 from by ring]
  exact stm_odd_halt_endgame (3*n)

theorem stm_odd_continue (b' n : Nat) :
    ∃ k, k > 0 ∧ srun antihydra (SP_Config (b'+1) (2*n+3) 0) k = SP_Config b' (3*n+6) 0 := by
  refine ⟨n*(3*n+9) + (9*n+20), by omega, ?_⟩
  have h1 : srun antihydra (SP_Config (b'+1) (2*n+3) 0) (n*(3*n+9)) = SP_Config (b'+1) 3 (3*n) := by
    have h := stm_P_multistep (b'+1) 1 0 n
    simp only [show 1+2+2*n = 2*n+3 from by omega,
               show (0:Nat)+3*n = 3*n from by omega] at h; exact h
  show srun antihydra (SP_Config (b'+1) (2*n+3) 0) (n*(3*n+9) + (9*n+20)) = _
  rw [srun_add, h1]
  have h2 := stm_odd_endgame b' (3*n); ring_nf at h2 ⊢; exact h2

-- SConfig simulation theorem

theorem stm_simulates_math (b a : Nat) (ha : a ≥ 2) :
    ∃ k, k > 0 ∧ (
      match nextMathState { a := a, b := b } with
      | some m' => srun antihydra (SP_Config b a 0) k = SP_Config m'.b m'.a 0
      | none    => (srun antihydra (SP_Config b a 0) k).state = none) := by
  cases h_mod : a % 2
  · obtain ⟨n, rfl⟩ : ∃ n, a = 2 * n + 2 := ⟨a / 2 - 1, by omega⟩
    rw [show nextMathState { a := 2*n+2, b := b } = some { a := 3*n+5, b := b+2 } from by
      unfold nextMathState; simp [show (2*n+2) % 2 = 0 from by omega]; omega]
    exact stm_even_full b n
  · obtain ⟨n, rfl⟩ : ∃ n, a = 2 * n + 3 := ⟨a / 2 - 1, by omega⟩
    cases b with
    | zero =>
      rw [show nextMathState { a := 2*n+3, b := 0 } = none from by
        unfold nextMathState; simp [show (2*n+3) % 2 = 1 from by omega]]
      exact stm_odd_halt_ex n
    | succ b' =>
      rw [show nextMathState { a := 2*n+3, b := b'+1 } = some { a := 3*n+6, b := b' } from by
        unfold nextMathState; simp [show (2*n+3) % 2 = 1 from by omega]; omega]
      exact stm_odd_continue b' n

-- D. The Halting Equivalence Theorem
inductive mathHalts : MathState → Prop where
| haltStep (m : MathState) (h : nextMathState m = none) : mathHalts m
| nextStep (m m' : MathState) (h : nextMathState m = some m') (h' : mathHalts m') : mathHalts m

-- Initial configuration
lemma antihydra_init_loop_start : run antihydra (initConfig 6) 58 = P_Config_Pad 2 8 0 0 := by
  rfl

-- i-th iterate of A
def Aiter (i : ℕ) (ab : ℕ × ℕ) : ℕ × ℕ := A^[i] ab

private lemma no_halt_before_58 : ∀ k < 58, (run antihydra (initConfig 6) k).state ≠ none := by
  decide

-- Helper lemmas for mathHalts_iff_Aiter_8_2
private lemma nextMathState_none_iff {a b : ℕ} (ha : a ≥ 2) :
    nextMathState { a := a, b := b } = none ↔ a % 2 = 1 ∧ b = 0 := by
  simp only [nextMathState, ge_iff_le, show a / 2 ≥ 1 from by omega, ite_true, beq_iff_eq]
  split_ifs <;> simp_all

private lemma nextMathState_some_eq_A {a b : ℕ} (ha : a ≥ 2) (hne : ¬(a % 2 = 1 ∧ b = 0)) :
    nextMathState { a := a, b := b } = some { a := (A (a, b)).1, b := (A (a, b)).2 } := by
  simp only [nextMathState, A, ge_iff_le, show a / 2 ≥ 1 from by omega, ite_true, beq_iff_eq]
  split_ifs <;> simp_all

private lemma A_fst_ge_2' (ab : ℕ × ℕ) (ha : ab.1 ≥ 2) : (A ab).1 ≥ 2 := by
  obtain ⟨a, b⟩ := ab; simp only [A, beq_iff_eq]; split_ifs <;> simp

private lemma Aiter_succ' (i : ℕ) (ab : ℕ × ℕ) : Aiter (i + 1) ab = Aiter i (A ab) := by
  simp [Aiter, Function.iterate_succ, Function.comp_apply]

private lemma mathHalts_implies_Aiter (m : MathState) (hm : m.a ≥ 2) (hmh : mathHalts m) :
    ∃ i, (Aiter i (m.a, m.b)).1 % 2 = 1 ∧ (Aiter i (m.a, m.b)).1 / 2 ≥ 1 ∧
         (Aiter i (m.a, m.b)).2 = 0 := by
  induction hmh with
  | haltStep m' hm' =>
    refine ⟨0, ?_⟩; simp only [Aiter, Function.iterate_zero, id]
    have h := (nextMathState_none_iff hm).mp hm'; exact ⟨h.1, by omega, h.2⟩
  | nextStep m' m'' hstep _hmh'' ih =>
    have hne : ¬(m'.a % 2 = 1 ∧ m'.b = 0) := by
      intro h; simp [(nextMathState_none_iff hm).mpr h] at hstep
    have heq := nextMathState_some_eq_A hm hne
    rw [heq] at hstep; cases Option.some.inj hstep
    obtain ⟨i, hi⟩ := ih (A_fst_ge_2' _ hm)
    exact ⟨i + 1, by rwa [Aiter_succ']⟩

private lemma Aiter_implies_mathHalts (a b : ℕ) (ha : a ≥ 2)
    (i : ℕ) (hi : (Aiter i (a, b)).1 % 2 = 1 ∧ (Aiter i (a, b)).1 / 2 ≥ 1 ∧ (Aiter i (a, b)).2 = 0) :
    mathHalts { a := a, b := b } := by
  induction i generalizing a b with
  | zero =>
    simp only [Aiter, Function.iterate_zero, id] at hi
    exact mathHalts.haltStep _ ((nextMathState_none_iff ha).mpr ⟨hi.1, hi.2.2⟩)
  | succ k ih =>
    by_cases hstop : a % 2 = 1 ∧ b = 0
    · exact mathHalts.haltStep _ ((nextMathState_none_iff ha).mpr hstop)
    · rw [Aiter_succ'] at hi
      exact mathHalts.nextStep _ ⟨_, _⟩ (nextMathState_some_eq_A ha hstop)
        (ih _ _ (A_fst_ge_2' _ ha) hi)

-- Key bridge: mathHalts {a=8,b=2} ↔ ∃ i, Aiter i (8,2) satisfies halt condition
lemma mathHalts_iff_Aiter_8_2 :
    mathHalts { a := 8, b := 2 } ↔
    ∃ i, (Aiter i (8, 2)).1 % 2 = 1 ∧ (Aiter i (8, 2)).1 / 2 ≥ 1 ∧ (Aiter i (8, 2)).2 = 0 := by
  constructor
  · intro h; exact mathHalts_implies_Aiter _ (by omega : (8 : ℕ) ≥ 2) h
  · rintro ⟨i, hi⟩; exact Aiter_implies_mathHalts 8 2 (by omega) i hi

-- Helper: nextMathState preserves a ≥ 2
private lemma nextMathState_a_ge_2 {a b : ℕ} {m' : MathState} (ha : a ≥ 2)
    (h : nextMathState { a := a, b := b } = some m') : m'.a ≥ 2 := by
  have hne : ¬(a % 2 = 1 ∧ b = 0) := by
    intro ⟨h1, h2⟩; simp [(nextMathState_none_iff ha).mpr ⟨h1, h2⟩] at h
  rw [nextMathState_some_eq_A ha hne] at h; cases Option.some.inj h; exact A_fst_ge_2' _ ha

-- SConfig halt equivalence
theorem stm_halt_iff_math_condition (b a : Nat) (ha : a ≥ 2) :
    (∃ k, (srun antihydra (SP_Config b a 0) k).state = none) ↔ mathHalts { a := a, b := b } := by
  constructor
  · -- Forward: if TM halts, then math halts (strong induction on step count)
    intro ⟨k, hk⟩
    suffices ∀ (n : Nat) (b a : Nat), a ≥ 2 →
        (srun antihydra (SP_Config b a 0) n).state = none → mathHalts { a := a, b := b } from
      this k b a ha hk
    intro n; induction n using Nat.strong_induction_on with
    | h n ih =>
      intro b a ha hk
      have ⟨k_sim, hk_pos, h_sim⟩ := stm_simulates_math b a ha
      cases h_next : nextMathState { a := a, b := b } with
      | none => exact mathHalts.haltStep _ h_next
      | some m' =>
        rw [h_next] at h_sim
        -- h_sim : srun ... k_sim = SP_Config m'.b m'.a 0
        by_cases h_lt : n < k_sim
        · exact absurd (h_sim ▸ rfl : (srun antihydra (SP_Config b a 0) k_sim).state = some stE)
            (by rw [show k_sim = n + (k_sim - n) from by omega, srun_add,
                srun_halted _ _ hk]; exact hk ▸ by simp)
        · -- n ≥ k_sim: split and recurse
          rw [show n = k_sim + (n - k_sim) from by omega, srun_add, h_sim] at hk
          exact mathHalts.nextStep _ _ h_next
            (ih (n - k_sim) (by omega) m'.b m'.a (nextMathState_a_ge_2 ha h_next) hk)
  · -- Backward: if math halts, then TM halts (induction on mathHalts)
    intro h_math
    suffices ∀ m : MathState, m.a ≥ 2 → mathHalts m →
        ∃ k, (srun antihydra (SP_Config m.b m.a 0) k).state = none from
      this _ ha h_math
    intro m hm hmh; induction hmh with
    | haltStep m h_none =>
      have ⟨k, _, h_sim⟩ := stm_simulates_math m.b m.a hm
      rw [h_none] at h_sim; exact ⟨k, h_sim⟩
    | nextStep m m' h_some _ ih =>
      have ⟨k, _, h_sim⟩ := stm_simulates_math m.b m.a hm
      rw [h_some] at h_sim
      have ⟨k', hk'⟩ := ih (nextMathState_a_ge_2 hm h_some)
      exact ⟨k + k', by rw [srun_add, h_sim]; exact hk'⟩

-- SConfig initial configuration
lemma antihydra_init_SP :
    srun antihydra (sinitConfig 6) 58 = SP_Config 2 8 0 := by
  have h := congrArg Config.toSConfig antihydra_init_loop_start
  rw [toSConfig_run, toSConfig_initConfig, P_Config_Pad_toSP] at h; exact h

-- Main result (SConfig version)
lemma antihydra_halts_iff :
    (∃ k, (run antihydra (initConfig 6) k).state = none) ↔
    ∃ i, (Aiter i (8, 2)).1 % 2 = 1 ∧ (Aiter i (8, 2)).1 / 2 ≥ 1 ∧ (Aiter i (8, 2)).2 = 0 := by
  -- Step 1: Lift Config halt ↔ SConfig halt
  have h_eq : ∀ k, (run antihydra (initConfig 6) k).state =
                    (srun antihydra (sinitConfig 6) k).state := fun k => by
    change _ = (srun antihydra (initConfig 6).toSConfig k).state
    rw [← toSConfig_run]; rfl
  -- Step 2: Split at 58 steps and connect to SP_Config 2 8 0
  have h_iff : (∃ k, (run antihydra (initConfig 6) k).state = none) ↔
               (∃ k, (srun antihydra (SP_Config 2 8 0) k).state = none) := by
    constructor
    · rintro ⟨k, hk⟩
      by_cases h : 58 ≤ k
      · refine ⟨k - 58, ?_⟩
        rw [h_eq, show k = 58 + (k - 58) from by omega, srun_add, antihydra_init_SP] at hk
        exact hk
      · exact absurd hk (no_halt_before_58 k (by omega))
    · rintro ⟨k, hk⟩
      exact ⟨58 + k, by rw [h_eq]; rw [srun_add, antihydra_init_SP]; exact hk⟩
  rw [h_iff, stm_halt_iff_math_condition 2 8 (by omega)]
  exact mathHalts_iff_Aiter_8_2

end Antihydra
