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

def mathHaltingCondition (m : MathState) : Prop :=
  m.a % 2 == 1 ∧ m.a / 2 ≥ 1 ∧ m.b == 0

-- Bridge lemma: ones k ++ true :: L = ones (k+1) ++ L
@[simp] theorem ones_append_true (k : Nat) (L : List Sym) :
    ones k ++ true :: L = ones (k + 1) ++ L := by
  simp [ones_succ, ones_true_cons, List.cons_append]

-- Additional simp lemmas for listHead/listTail with ones/zeros patterns
@[simp] lemma listHead_ones_succ (k : Nat) (R : List Sym) :
    listHead (ones (k + 1) ++ R) false = true := rfl

@[simp] lemma listTail_ones_succ (k : Nat) (R : List Sym) :
    listTail (ones (k + 1) ++ R) = ones k ++ R := rfl

@[simp] lemma listHead_ones_false (m : Nat) (L : List Sym) :
    listHead (ones m ++ false :: L) false = if m = 0 then false else true := by
  cases m with | zero => rfl | succ m => rfl

@[simp] lemma listTail_ones_false (m : Nat) (L : List Sym) :
    listTail (ones m ++ false :: L) = if m = 0 then L else ones (m-1) ++ false :: L := by
  cases m with | zero => rfl | succ m => rfl

-- Macro-level configuration
def P_Config_Pad (b : Nat) (m : Nat) (n : Nat) (p : Nat) : Config 6 :=
  { state := some stE,
    head := false,
    left := ones m ++ [false] ++ ones b,
    right := ones n ++ zeros p
  }

-- Simp tactic for single TM steps (handles Fin literal vs stX abbreviation mismatch)
scoped macro "ah_simp" : tactic =>
  `(tactic| simp (config := { decide := true }) [run, step, antihydra, P_Config_Pad, ones])

-- Shift rules

lemma A_shift (k : Nat) (L R : List Sym) :
    run antihydra { state := some stA, head := true, left := L, right := ones k ++ R } (k + 1) =
    { state := some stA, head := listHead R false, left := ones (k + 1) ++ L, right := listTail R } := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    calc
      run antihydra { state := some stA, head := true, left := L, right := ones (k + 1) ++ R } (k + 2)
      _ = run antihydra { state := some stA, head := true, left := true :: L, right := ones k ++ R } (k + 1) := rfl
      _ = _ := by rw [ih (true :: L)]; simp

lemma C_shift (k : Nat) (L R : List Sym) :
    run antihydra { state := some stC, head := true, left := ones k ++ L, right := R } (k + 1) =
    { state := some stC, head := listHead L false, left := listTail L, right := ones (k + 1) ++ R } := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    calc
      run antihydra { state := some stC, head := true, left := ones (k + 1) ++ L, right := R } (k + 2)
      _ = run antihydra { state := some stC, head := true, left := ones k ++ L, right := true :: R } (k + 1) := rfl
      _ = _ := by rw [ih (true :: R)]; simp

lemma E_shift (k : Nat) (L R : List Sym) :
    run antihydra { state := some stE, head := true, left := L, right := ones k ++ R } (k + 1) =
    { state := some stE, head := listHead R false, left := ones (k + 1) ++ L, right := listTail R } := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    calc
      run antihydra { state := some stE, head := true, left := L, right := ones (k + 1) ++ R } (k + 2)
      _ = run antihydra { state := some stE, head := true, left := true :: L, right := ones k ++ R } (k + 1) := rfl
      _ = _ := by rw [ih (true :: L)]; simp

-- Macro Loop Steps

theorem tm_P_step (b m n p : Nat) :
    run antihydra (P_Config_Pad b (m+2+2) n (p+2)) (2*n + 12) = P_Config_Pad b (m+2) (n+3) (p+1) := by
  tm_exec [antihydra, P_Config_Pad]
  rw [show 2 * n + 10 = (n + 1) + (n + 9) from by omega, run_add]
  simp only [show (0 : Fin 6) = stA from rfl, A_shift, listHead, listTail, zeros_succ]
  tm_exec [antihydra, P_Config_Pad]
  rw [show n + 6 = (n + 1) + 5 from by omega, run_add]
  simp only [show (2 : Fin 6) = stC from rfl, C_shift, listHead, listTail]
  tm_exec [antihydra, P_Config_Pad]


theorem tm_P_multistep (b m n p k : Nat) :
    run antihydra (P_Config_Pad b (m+2 + 2*k) n (p+1 + k)) (k*(2*n + 3*k + 9)) = P_Config_Pad b (m+2) (n+3*k) (p+1) := by
  induction k generalizing n with
  | zero =>
    have h0 : 0 * (2 * n + 3 * 0 + 9) = 0 := by ring
    rw [h0]
    have hm : m + 2 + 2 * 0 = m + 2 := by ring
    have hp : p + 1 + 0 = p + 1 := by ring
    have hn : n + 3 * 0 = n := by ring
    rw [hm, hp, hn]
    rfl
  | succ k' ih =>
    -- We want to do 1 step, then k' steps.
    -- Total steps = (2n + 12) + k' * (2(n+3) + 3k' + 9)
    have h_steps : (k' + 1) * (2 * n + 3 * (k' + 1) + 9) = (2 * n + 12) + k' * (2 * (n + 3) + 3 * k' + 9) := by ring
    rw [h_steps]
    rw [run_add]

    -- The first chunk of steps is tm_P_step for M = m + 2*k' and P = p + k'
    have h_m : m + 2 + 2 * (k' + 1) = (m + 2 * k') + 2 + 2 := by omega
    have h_p : p + 1 + (k' + 1) = (p + k') + 2 := by omega

    have step1 : run antihydra (P_Config_Pad b (m + 2 + 2 * (k' + 1)) n (p + 1 + (k' + 1))) (2 * n + 12) = P_Config_Pad b ((m + 2 * k') + 2) (n + 3) ((p + k') + 1) := by
      rw [h_m, h_p]
      exact tm_P_step b (m + 2 * k') n (p + k')

    rw [step1]

    have h_m2 : (m + 2 * k') + 2 = m + 2 + 2 * k' := by omega
    have h_p2 : (p + k') + 1 = p + 1 + k' := by omega
    have h_n2 : n + 3 * (k' + 1) = (n + 3) + 3 * k' := by omega

    rw [h_m2, h_p2]
    rw [ih (n + 3)]
    rw [h_n2]

-- Even Endgame (m=0)
theorem tm_even_endgame (b N p : Nat) :
    (run antihydra (P_Config_Pad b 0 N (p+2)) 2).state = none := by
  have step1 : run antihydra (P_Config_Pad b 0 N (p+2)) 1 =
    { state := some stF, head := false, left := ones b, right := true :: ones N ++ zeros (p+2) } := by
    ah_simp
  rw [show 2 = 1 + 1 from rfl, run_add, step1]
  have step2 : run antihydra { state := some stF, head := false, left := ones b, right := true :: ones N ++ zeros (p+2) } 1 =
    { state := none, head := false, left := ones b, right := true :: ones N ++ zeros (p+2) } := by
    cases b <;> simp (config := { decide := true }) only [run, step, antihydra]
  rw [step2, show (none : Option _) = none from rfl]

-- Odd Endgame (m=3, b>0)
theorem tm_odd_endgame (b' N p : Nat) :
    run antihydra (P_Config_Pad (b' + 1) 3 N (p+2)) (3*N + 20) = P_Config_Pad b' (N+6) 0 p := by
  tm_exec [antihydra, P_Config_Pad]
  rw [show 3 * N + 18 = (N + 1) + (2 * N + 17) from by omega, run_add]
  simp only [show (0 : Fin 6) = stA from rfl, A_shift, listHead, listTail, zeros_succ]
  tm_exec [antihydra, P_Config_Pad]
  rw [show 2 * N + 14 = (N + 1) + (N + 13) from by omega, run_add]
  simp only [show (2 : Fin 6) = stC from rfl, C_shift, listHead, listTail]
  tm_exec [antihydra, P_Config_Pad]
  simp only [show (4 : Fin 6) = stE from rfl, E_shift, listHead, listTail, zeros_succ]
  rw [show 1 + (1 + (1 + (1 + (1 + (N + 1))))) = N + 6 from by omega]
  simp only [P_Config_Pad, ones_zero, List.nil_append]
  congr 1
  rw [show (true :: true :: true :: true :: true :: false :: ones b' : List Sym) = ones 5 ++ false :: ones b' from rfl,
    ← List.append_assoc, ones_append]
  simp only [List.append_assoc, List.singleton_append]

-- Additional tape lemmas needed for later proofs

@[simp] lemma drop_ones (a : Nat) (L : List Sym) :
    (ones a ++ L).drop a = L := by
  induction a with
  | zero => rfl
  | succ a ih => simp [ones, *]

@[simp] lemma countOnes_ones' (a : Nat) :
    countOnes (ones a) = a := countOnes_ones a

@[simp] lemma countOnes_ones_false (a : Nat) (L : List Sym) :
    countOnes (ones a ++ false :: L) = a := by
  induction a with
  | zero => rfl
  | succ a ih => rw [ones_succ, List.cons_append, countOnes, ih]

-- A. The Abstraction Function (Decoding the Tape)
def decodeTape (c : Config 6) : MathState :=
  let a := countOnes c.left
  let after_a := c.left.drop a
  let b := match after_a with
           | false :: xs => countOnes xs
           | _ => 0
  { a := a, b := b }

@[simp] lemma decodeTape_P_Config_Pad (b a n p : Nat) :
    decodeTape (P_Config_Pad b a n p) = { a := a, b := b } := by
  unfold decodeTape P_Config_Pad
  simp

@[simp] lemma all_zeros' (p : Nat) : (zeros p).all (!·) = true := by
  induction p with
  | zero => rfl
  | succ p ih => simp [zeros]

@[simp] lemma drop_ones_exact (a : Nat) : (ones a).drop a = [] := by
  induction a with
  | zero => rfl
  | succ a ih => simp [ones]

-- B. Defining the "Clean" Invariant
def isValidLoopStart (c : Config 6) : Prop :=
  c.state = some stE ∧
  c.head = false ∧
  (c.right.all (!·) = true) ∧
  (countOnes c.left ≥ 2) ∧
  ∃ b : Nat, c.left.drop (countOnes c.left) = false :: ones b

lemma isValidLoopStart_P_Config_Pad (b a p : Nat) (ha : a ≥ 2) :
    isValidLoopStart (P_Config_Pad b a 0 p) := by
  unfold isValidLoopStart P_Config_Pad
  refine ⟨rfl, rfl, by simp, by simp [ha], b, by simp⟩

lemma take_countOnes_eq_ones (L : List Sym) :
    L.take (countOnes L) = ones (countOnes L) := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    cases x
    · rfl
    · simp [countOnes, ones]
      rw [ih]

lemma list_eq_ones_drop (L : List Sym) :
    L = ones (countOnes L) ++ L.drop (countOnes L) := by
  rw [← take_countOnes_eq_ones L]
  exact (List.take_append_drop _ _).symm

lemma all_false_eq_zeros (L : List Sym) (h : L.all (!·) = true) :
    L = zeros L.length := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    cases x
    · change (xs.all (!·) = true) at h
      exact congrArg (List.cons false) (ih h)
    · change (false = true) at h
      contradiction

lemma isValidLoopStart_eq_P_Config_Pad (c : Config 6) (hm : isValidLoopStart c) :
    ∃ a b p, c = P_Config_Pad b a 0 p ∧ a ≥ 2 := by
  rcases c with ⟨state, left, head, right⟩
  unfold isValidLoopStart at hm
  rcases hm with ⟨hstate, hhead, hright, ha, ⟨b, hb⟩⟩
  have hleft_full : left = ones (countOnes left) ++ [false] ++ ones b := by
    rw [list_eq_ones_drop left, hb]; simp [List.append_assoc]

  have hright_full : right = zeros right.length := all_false_eq_zeros _ hright

  use (countOnes left), b, right.length
  constructor
  · unfold P_Config_Pad; congr
  · exact ha

-- Right-tape padding independence via stream embedding.
-- Two P_Config_Pad configs with different padding p have the same toSConfig,
-- so their runs agree on state, head, and left tape. This replaces the
-- 120-line RightPadEquiv infrastructure with ~40 lines.

/-- P_Config_Pad maps to the same SConfig regardless of padding p. -/
lemma P_Config_Pad_toSConfig_eq (b m n p p' : Nat) :
    (P_Config_Pad b m n p).toSConfig = (P_Config_Pad b m n p').toSConfig := by
  apply toSConfig_padding_indep <;> simp [P_Config_Pad]

/-- The left tape after one step depends only on state, head, and left tape (not right). -/
private lemma step_left_eq {c₁ c₂ : Config 6}
    (hs : c₁.state = c₂.state) (hl : c₁.left = c₂.left) (hh : c₁.head = c₂.head) :
    (step antihydra c₁).left = (step antihydra c₂).left := by
  rcases c₁ with ⟨s, l, h, r₁⟩; rcases c₂ with ⟨_, _, _, r₂⟩
  simp only at hs hl hh; subst hs; subst hl; subst hh
  cases s with
  | none => rfl
  | some q =>
    cases h_tr : antihydra.tr q h with
    | none => simp [step, h_tr]
    | some val => obtain ⟨q', w, d⟩ := val; cases d <;> simp [step, h_tr]

/-- Running two padding-equivalent configs preserves left-list equality and SConfig equality. -/
private lemma run_pad_transfer {c₁ c₂ : Config 6} (k : Nat)
    (hl : c₁.left = c₂.left) (hsc : c₁.toSConfig = c₂.toSConfig) :
    (run antihydra c₁ k).left = (run antihydra c₂ k).left ∧
    (run antihydra c₁ k).toSConfig = (run antihydra c₂ k).toSConfig := by
  induction k generalizing c₁ c₂ with
  | zero => exact ⟨hl, hsc⟩
  | succ k ih =>
    have hsc' : (step antihydra c₁).toSConfig = (step antihydra c₂).toSConfig := by
      rw [toSConfig_step, toSConfig_step, hsc]
    have hs : c₁.state = c₂.state := by
      have := congrArg SConfig.state hsc; simp [Config.toSConfig] at this; exact this
    have hh : c₁.head = c₂.head := by
      have := congrArg SConfig.head hsc; simp [Config.toSConfig] at this; exact this
    exact ih (step_left_eq hs hl hh) hsc'

/-- If R.all (!·) = true, then listToSide R = Side.blank. -/
private lemma listToSide_blank_of_all_false {R : List Sym} (h : R.all (!·) = true) :
    listToSide R = Side.blank := by
  ext i; simp [listToSide, Side.blank]
  induction R generalizing i with
  | nil => simp [List.getD]
  | cons x xs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases i with
    | zero => simp [List.getD]; cases x <;> simp_all
    | succ i => simp [List.getD]; exact ih h.2 i

/-- Transfer isValidLoopStart across different right-tape padding. -/
lemma isValidLoopStart_of_pad_transfer {c₁ c₂ : Config 6}
    (hl : c₁.left = c₂.left) (hsc : c₁.toSConfig = c₂.toSConfig)
    (hv : isValidLoopStart c₂) : isValidLoopStart c₁ := by
  have hs : c₁.state = c₂.state := by
    have := congrArg SConfig.state hsc; simp [Config.toSConfig] at this; exact this
  have hh : c₁.head = c₂.head := by
    have := congrArg SConfig.head hsc; simp [Config.toSConfig] at this; exact this
  have hr_stream : listToSide c₁.right = listToSide c₂.right := by
    have := congrArg SConfig.right hsc; simp [Config.toSConfig] at this; exact this
  unfold isValidLoopStart at hv ⊢
  exact ⟨hs ▸ hv.1, hh ▸ hv.2.1,
    all_false_of_listToSide_blank (by rw [hr_stream]; exact listToSide_blank_of_all_false hv.2.2.1),
    hl ▸ hv.2.2.2.1, hl ▸ hv.2.2.2.2⟩

lemma decodeTape_of_left_eq {c1 c2 : Config 6} (hl : c1.left = c2.left) :
    decodeTape c1 = decodeTape c2 := by
  unfold decodeTape; rw [hl]

-- Even endgame: from a=2 to valid loop start with a=N+5, b=b+2
theorem tm_even_endgame_to_loop (b N p : Nat) :
    run antihydra (P_Config_Pad b 2 N (p+2)) (3*N + 2*b + 26) = P_Config_Pad (b+2) (N+5) 0 p := by
  tm_exec [antihydra, P_Config_Pad]
  rw [show 3 * N + 2 * b + 24 = (N + 1) + (2 * N + 2 * b + 23) from by omega, run_add]
  simp only [show (0 : Fin 6) = stA from rfl, A_shift, listHead, listTail, zeros_succ]
  tm_exec [antihydra, P_Config_Pad]
  rw [show 2 * N + 2 * b + 20 = (N + 1) + (N + 2 * b + 19) from by omega, run_add]
  simp only [show (2 : Fin 6) = stC from rfl, C_shift, listHead, listTail]
  tm_exec [antihydra, P_Config_Pad]
  cases b with
  | zero =>
    simp only [ones_zero, Nat.mul_zero, Nat.add_zero]
    tm_exec [antihydra, P_Config_Pad]
    simp only [show (4 : Fin 6) = stE from rfl, E_shift, listHead, listTail, zeros_succ]
    rw [show 1 + (1 + (1 + (1 + (N + 1)))) = N + 5 from by omega, show (0 : Nat) + 2 = 2 from by omega]
    simp only [P_Config_Pad, ones_zero, List.nil_append]
    congr 1
    rw [show ([true, true, true, true, false, true, true] : List Sym) = ones 4 ++ false :: ones 2 from rfl,
      ← List.append_assoc, ones_append]
    simp only [List.append_assoc, List.singleton_append]
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
    tm_exec [antihydra, P_Config_Pad]
    simp only [show (4 : Fin 6) = stE from rfl, E_shift, listHead, listTail, zeros_succ]
    rw [show 1 + (1 + (1 + (1 + (N + 1)))) = N + 5 from by omega, show b' + 1 + 2 = b' + 3 from by omega]
    simp only [P_Config_Pad, ones_zero, List.nil_append]
    congr 1
    rw [show (true :: true :: true :: true :: false :: ones (b' + 1 + 1 + 1) : List Sym) = ones 4 ++ false :: ones (b' + 3) from rfl,
      ← List.append_assoc, ones_append]
    simp only [List.append_assoc, List.singleton_append]

-- Odd halt endgame: from a=3, b=0, the machine halts
theorem tm_odd_halt_endgame (N p : Nat) :
    (run antihydra (P_Config_Pad 0 3 N (p+2)) (2*N + 12)).state = none := by
  rw [show 2 * N + 12 = (2 * N + 11) + 1 from by omega, run_add]
  have h : run antihydra (P_Config_Pad 0 3 N (p+2)) (2*N + 11) =
    { state := some stF, head := false, left := ([] : List Sym),
      right := true :: true :: false :: ones (N+1+1+1) ++ false :: zeros p } := by
    tm_exec [antihydra, P_Config_Pad]
    rw [show 2 * N + 9 = (N + 1) + (N + 8) from by omega, run_add]
    simp only [show (0 : Fin 6) = stA from rfl, A_shift, listHead, listTail, zeros_succ]
    tm_exec [antihydra, P_Config_Pad]
    rw [show N + 5 = (N + 1) + 4 from by omega, run_add]
    simp only [show (2 : Fin 6) = stC from rfl, C_shift, listHead, listTail]
    tm_exec [antihydra, P_Config_Pad]
  rw [h]; ah_simp

-- Helper lemmas for tm_simulates_math

theorem tm_even_full (b n p : Nat) :
    ∃ k, k > 0 ∧ isValidLoopStart (run antihydra (P_Config_Pad b (2*n+2) 0 p) k) ∧
      decodeTape (run antihydra (P_Config_Pad b (2*n+2) 0 p) k) = { a := 3 * n + 5, b := b + 2 } := by
  set p' := p + n + 2
  set k := n * (3 * n + 9) + (9 * n + 2 * b + 26)
  have h_multi : run antihydra (P_Config_Pad b (2*n+2) 0 p') (n * (3*n+9))
      = P_Config_Pad b 2 (3*n) (p+2) := by
    have h := tm_P_multistep b 0 0 (p+1) n
    simp only [show 0 + 2 + 2 * n = 2 * n + 2 from by omega, show p + 1 + 1 + n = p' from by omega,
      show (0:ℕ) + 3 * n = 3 * n from by omega, show p + 1 + 1 = p + 2 from by omega] at h; exact h
  have h_end : run antihydra (P_Config_Pad b 2 (3*n) (p+2)) (9*n + 2*b + 26)
      = P_Config_Pad (b+2) (3*n+5) 0 p := by
    have h := tm_even_endgame_to_loop b (3*n) p; ring_nf at h ⊢; exact h
  have h_padded : run antihydra (P_Config_Pad b (2*n+2) 0 p') k
      = P_Config_Pad (b+2) (3*n+5) 0 p := by
    show run antihydra (P_Config_Pad b (2*n+2) 0 p') (n*(3*n+9) + (9*n+2*b+26)) = _
    rw [run_add, h_multi, h_end]
  have hsc := P_Config_Pad_toSConfig_eq b (2*n+2) 0 p p'
  have h_run := run_pad_transfer k (by simp [P_Config_Pad]) hsc
  rw [h_padded] at h_run
  use k
  refine ⟨by omega, ?_, ?_⟩
  · exact isValidLoopStart_of_pad_transfer h_run.1 h_run.2
      (isValidLoopStart_P_Config_Pad (b+2) (3*n+5) p (by omega))
  · rw [decodeTape_of_left_eq h_run.1]; simp

-- Odd halt case: the TM halts
theorem tm_odd_halt_ex (n p : Nat) :
    ∃ k, k > 0 ∧ (run antihydra (P_Config_Pad 0 (2*n+3) 0 p) k).state = none := by
  set p' := p + n + 2
  set k := n * (3 * n + 9) + (6 * n + 12)
  have h_multi : run antihydra (P_Config_Pad 0 (2*n+3) 0 p') (n * (3*n+9))
      = P_Config_Pad 0 3 (3*n) (p+2) := by
    have h := tm_P_multistep 0 1 0 (p+1) n
    simp only [show 1 + 2 + 2 * n = 2 * n + 3 from by omega, show p + 1 + 1 + n = p' from by omega,
      show 1 + 2 = 3 from by omega, show (0:ℕ) + 3 * n = 3 * n from by omega,
      show p + 1 + 1 = p + 2 from by omega] at h; exact h
  have h_end : (run antihydra (P_Config_Pad 0 3 (3*n) (p+2)) (6*n+12)).state = none := by
    have h := tm_odd_halt_endgame (3*n) p; ring_nf at h ⊢; exact h
  have h_padded : (run antihydra (P_Config_Pad 0 (2*n+3) 0 p') k).state = none := by
    show (run antihydra (P_Config_Pad 0 (2*n+3) 0 p') (n*(3*n+9) + (6*n+12))).state = none
    rw [run_add, h_multi]; exact h_end
  have hsc := P_Config_Pad_toSConfig_eq 0 (2*n+3) 0 p p'
  have h_run := run_pad_transfer k (by simp [P_Config_Pad]) hsc
  have hs : (run antihydra (P_Config_Pad 0 (2*n+3) 0 p) k).state =
      (run antihydra (P_Config_Pad 0 (2*n+3) 0 p') k).state := by
    have := congrArg SConfig.state h_run.2; simp [Config.toSConfig] at this; exact this
  exact ⟨k, by omega, hs.symm ▸ h_padded⟩

-- Odd continue case: the TM reaches a valid loop start with the correct decoded state
theorem tm_odd_continue (b' n p : Nat) :
    ∃ k, k > 0 ∧ isValidLoopStart (run antihydra (P_Config_Pad (b'+1) (2*n+3) 0 p) k) ∧
      decodeTape (run antihydra (P_Config_Pad (b'+1) (2*n+3) 0 p) k) = { a := 3 * n + 6, b := b' } := by
  set p' := p + n + 2
  set k := n * (3 * n + 9) + (9 * n + 20)
  have h_multi : run antihydra (P_Config_Pad (b'+1) (2*n+3) 0 p') (n * (3*n+9))
      = P_Config_Pad (b'+1) 3 (3*n) (p+2) := by
    have h := tm_P_multistep (b'+1) 1 0 (p+1) n
    simp only [show 1 + 2 + 2 * n = 2 * n + 3 from by omega, show p + 1 + 1 + n = p' from by omega,
      show 1 + 2 = 3 from by omega, show (0:ℕ) + 3 * n = 3 * n from by omega,
      show p + 1 + 1 = p + 2 from by omega] at h; exact h
  have h_end : run antihydra (P_Config_Pad (b'+1) 3 (3*n) (p+2)) (9*n+20)
      = P_Config_Pad b' (3*n+6) 0 p := by
    have h := tm_odd_endgame b' (3*n) p; ring_nf at h ⊢; exact h
  have h_padded : run antihydra (P_Config_Pad (b'+1) (2*n+3) 0 p') k
      = P_Config_Pad b' (3*n+6) 0 p := by
    show run antihydra (P_Config_Pad (b'+1) (2*n+3) 0 p') (n*(3*n+9) + (9*n+20)) = _
    rw [run_add, h_multi, h_end]
  have hsc := P_Config_Pad_toSConfig_eq (b'+1) (2*n+3) 0 p p'
  have h_run := run_pad_transfer k (by simp [P_Config_Pad]) hsc
  rw [h_padded] at h_run
  use k
  refine ⟨by omega, ?_, ?_⟩
  · exact isValidLoopStart_of_pad_transfer h_run.1 h_run.2
      (isValidLoopStart_P_Config_Pad b' (3*n+6) p (by omega))
  · rw [decodeTape_of_left_eq h_run.1]; simp

-- C. The Block-Step Lemma (The Core Theorem)
theorem tm_simulates_math (c : Config 6) (hm : isValidLoopStart c) :
    ∃ (k : Nat), k > 0 ∧ (
      let c' := run antihydra c k
      match nextMathState (decodeTape c) with
      | some m' => isValidLoopStart c' ∧ decodeTape c' = m'
      | none    => c'.state = none) := by
  have ⟨a, b, p, hc, ha⟩ := isValidLoopStart_eq_P_Config_Pad c hm
  subst hc
  simp only [decodeTape_P_Config_Pad]
  cases h_mod : a % 2
  · -- Even case: a = 2*n+2
    have h_even : ∃ n, a = 2 * n + 2 := ⟨a / 2 - 1, by omega⟩
    rcases h_even with ⟨n, hn⟩
    subst hn
    have h_next : nextMathState { a := 2 * n + 2, b := b } = some { a := 3 * n + 5, b := b + 2 } := by
      unfold nextMathState
      have h1 : (2 * n + 2) % 2 = 0 := by omega
      simp [h1]
      omega
    rw [h_next]
    obtain ⟨k, hk, hvalid, hdecode⟩ := tm_even_full b n p
    exact ⟨k, hk, hvalid, hdecode⟩
  · -- Odd case: a = 2*n+3
    have h_odd : ∃ n, a = 2 * n + 3 := ⟨a / 2 - 1, by omega⟩
    rcases h_odd with ⟨n, hn⟩
    subst hn
    cases b with
    | zero =>
      have h_next : nextMathState { a := 2 * n + 3, b := 0 } = none := by
        unfold nextMathState
        have h1 : (2 * n + 3) % 2 = 1 := by omega
        simp [h1]
      rw [h_next]
      exact tm_odd_halt_ex n p
    | succ b' =>
      have h_next : nextMathState { a := 2 * n + 3, b := b' + 1 } = some { a := 3 * n + 6, b := b' } := by
        unfold nextMathState
        have h1 : (2 * n + 3) % 2 = 1 := by omega
        simp [h1]
        omega
      rw [h_next]
      obtain ⟨k, hk, hvalid, hdecode⟩ := tm_odd_continue b' n p
      exact ⟨k, hk, hvalid, hdecode⟩

lemma run_none_state (c : Config 6) (h : c.state = none) (k : Nat) :
    (run antihydra c k).state = none := by
  exact run_state_none antihydra c k h

-- D. The Halting Equivalence Theorem
inductive mathHalts : MathState → Prop where
| haltStep (m : MathState) (h : nextMathState m = none) : mathHalts m
| nextStep (m m' : MathState) (h : nextMathState m = some m') (h' : mathHalts m') : mathHalts m

theorem tm_halt_iff_math_condition (c : Config 6) (hm : isValidLoopStart c) :
    (∃ k, (run antihydra c k).state = none) ↔ mathHalts (decodeTape c) := by
  constructor
  · intro ⟨k, hk⟩
    induction k using Nat.strong_induction_on generalizing c with
    | h n ih =>
      have ⟨k_sim, hk_sim_pos, h_sim⟩ := tm_simulates_math c hm
      cases h_next : nextMathState (decodeTape c) with
      | none =>
        exact mathHalts.haltStep _ h_next
      | some m' =>
        have h_rewrite : match nextMathState (decodeTape c) with | some m' => isValidLoopStart (run antihydra c k_sim) ∧ decodeTape (run antihydra c k_sim) = m' | none => (run antihydra c k_sim).state = none = (isValidLoopStart (run antihydra c k_sim) ∧ decodeTape (run antihydra c k_sim) = m') := by rw [h_next]
        rw [h_rewrite] at h_sim
        have ⟨hm_c', hd_c'⟩ := h_sim
        by_cases h_lt : n < k_sim
        · exfalso
          have hc'_state : (run antihydra c k_sim).state = some stE := hm_c'.1
          have hc'_none : (run antihydra c k_sim).state = none := by
            have h_add : k_sim = n + (k_sim - n) := by omega
            change (run antihydra c k_sim).state = none
            rw [h_add, run_add]
            exact run_none_state _ hk _
          rw [hc'_none] at hc'_state
          contradiction
        · have h_ge : n ≥ k_sim := by omega
          let n' := n - k_sim
          have hk_n' : (run antihydra (run antihydra c k_sim) n').state = none := by
             have h_run_add : run antihydra (run antihydra c k_sim) n' = run antihydra c (k_sim + n') := by rw [run_add]
             rw [h_run_add]
             have h_ns : k_sim + n' = n := Nat.add_sub_of_le h_ge
             rw [h_ns]
             exact hk
          have h_math' := ih n' (by omega) (run antihydra c k_sim) hm_c' hk_n'
          rw [hd_c'] at h_math'
          exact mathHalts.nextStep _ _ h_next h_math'
  · intro h_math
    generalize hd : decodeTape c = m at h_math
    induction h_math generalizing c with
    | haltStep m h_none =>
      have ⟨k, hk_pos, hk⟩ := tm_simulates_math c hm
      have h_rewrite : match nextMathState (decodeTape c) with | some m' => isValidLoopStart (run antihydra c k) ∧ decodeTape (run antihydra c k) = m' | none => (run antihydra c k).state = none = ((run antihydra c k).state = none) := by
        rw [hd, h_none]
      rw [h_rewrite] at hk
      exact ⟨k, hk⟩
    | nextStep m m' h_some h_halt ih =>
      have ⟨k, hk_pos, hk⟩ := tm_simulates_math c hm
      have h_rewrite : match nextMathState (decodeTape c) with | some m' => isValidLoopStart (run antihydra c k) ∧ decodeTape (run antihydra c k) = m' | none => (run antihydra c k).state = none = (isValidLoopStart (run antihydra c k) ∧ decodeTape (run antihydra c k) = m') := by
        rw [hd, h_some]
      rw [h_rewrite] at hk
      rcases hk with ⟨hm_c', hd_c'⟩
      have ⟨k', hk'⟩ := ih (run antihydra c k) hm_c' hd_c'
      use k + k'
      rw [run_add]
      exact hk'

-- Initial configuration
lemma antihydra_init_loop_start : run antihydra (initConfig 6) 58 = P_Config_Pad 2 8 0 0 := by
  rfl

lemma antihydra_init_math_state : decodeTape (run antihydra (initConfig 6) 58) = { a := 8, b := 2 } := by
  decide

-- i-th iterate of A
def Aiter (i : ℕ) (ab : ℕ × ℕ) : ℕ × ℕ := A^[i] ab

private lemma isValidLoopStart_P248 : isValidLoopStart (P_Config_Pad 2 8 0 0) :=
  isValidLoopStart_P_Config_Pad 2 8 0 (by omega)

private lemma no_halt_before_58 : ∀ k < 58, (run antihydra (initConfig 6) k).state ≠ none := by
  decide

-- Helper lemmas for mathHalts_iff_Aiter_8_2
private lemma nextMathState_none_iff {a b : ℕ} (ha : a ≥ 2) :
    nextMathState { a := a, b := b } = none ↔ a % 2 = 1 ∧ b = 0 := by
  simp only [nextMathState]
  have hd : a / 2 ≥ 1 := by omega
  simp only [ge_iff_le, hd, ite_true, beq_iff_eq]
  split_ifs with h1 h2
  · simp; omega
  · simp [h2]; omega
  · simp; omega

private lemma nextMathState_some_eq_A {a b : ℕ} (ha : a ≥ 2) (hne : ¬(a % 2 = 1 ∧ b = 0)) :
    nextMathState { a := a, b := b } = some { a := (A (a, b)).1, b := (A (a, b)).2 } := by
  simp only [nextMathState, A]
  have hd : a / 2 ≥ 1 := by omega
  simp only [ge_iff_le, hd, ite_true, beq_iff_eq]
  split_ifs with h1 h2
  · rfl
  · exfalso; exact hne ⟨by omega, h2⟩
  · congr 1

private lemma A_fst_ge_2' (ab : ℕ × ℕ) (ha : ab.1 ≥ 2) : (A ab).1 ≥ 2 := by
  obtain ⟨a, b⟩ := ab
  simp only [A, beq_iff_eq]
  split_ifs with h <;> simp

private lemma Aiter_succ' (i : ℕ) (ab : ℕ × ℕ) : Aiter (i + 1) ab = Aiter i (A ab) := by
  change A^[i.succ] ab = A^[i] (A ab)
  rw [Function.iterate_succ, Function.comp_apply]

private lemma mathHalts_implies_Aiter (m : MathState) (hm : m.a ≥ 2) (hmh : mathHalts m) :
    ∃ i, (Aiter i (m.a, m.b)).1 % 2 = 1 ∧ (Aiter i (m.a, m.b)).1 / 2 ≥ 1 ∧
         (Aiter i (m.a, m.b)).2 = 0 := by
  induction hmh with
  | haltStep m' hm' =>
    refine ⟨0, ?_⟩
    simp only [Aiter, Function.iterate_zero, id]
    have h := (nextMathState_none_iff hm).mp hm'
    exact ⟨h.1, by omega, h.2⟩
  | nextStep m' m'' hstep _hmh'' ih =>
    have hne : ¬(m'.a % 2 = 1 ∧ m'.b = 0) := by
      intro ⟨h1, h2⟩
      have hnone := (nextMathState_none_iff hm).mpr ⟨h1, h2⟩
      simp [hnone] at hstep
    have heq := nextMathState_some_eq_A hm hne
    have hm''_eq : m'' = { a := (A (m'.a, m'.b)).1, b := (A (m'.a, m'.b)).2 } := by
      rw [heq] at hstep; exact (Option.some.inj hstep).symm
    have hm''_a : m''.a = (A (m'.a, m'.b)).1 := by rw [hm''_eq]
    have hm''_b : m''.b = (A (m'.a, m'.b)).2 := by rw [hm''_eq]
    have hm''_ge2 : m''.a ≥ 2 := by
      rw [hm''_a]; exact A_fst_ge_2' (m'.a, m'.b) hm
    obtain ⟨i, hi⟩ := ih hm''_ge2
    refine ⟨i + 1, ?_⟩
    rw [Aiter_succ']
    rwa [hm''_a, hm''_b] at hi

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
      have hA2 : (A (a, b)).1 ≥ 2 := A_fst_ge_2' (a, b) ha
      apply mathHalts.nextStep { a := a, b := b } { a := (A (a, b)).1, b := (A (a, b)).2 }
      · exact nextMathState_some_eq_A ha hstop
      · exact ih (A (a, b)).1 (A (a, b)).2 hA2 hi

-- Key bridge: mathHalts {a=8,b=2} ↔ ∃ i, Aiter i (8,2) satisfies halt condition
lemma mathHalts_iff_Aiter_8_2 :
    mathHalts { a := 8, b := 2 } ↔
    ∃ i, (Aiter i (8, 2)).1 % 2 = 1 ∧ (Aiter i (8, 2)).1 / 2 ≥ 1 ∧ (Aiter i (8, 2)).2 = 0 := by
  constructor
  · intro h; exact mathHalts_implies_Aiter _ (by norm_num : (8 : ℕ) ≥ 2) h
  · rintro ⟨i, hi⟩; exact Aiter_implies_mathHalts 8 2 (by norm_num) i hi

-- Main result: the Antihydra TM halts iff some iterate of A starting at (8,2)
-- produces a pair (a, 0) with a odd and a ≥ 3 (i.e. hits the halting condition).
lemma antihydra_halts_iff :
    (∃ k, (run antihydra (initConfig 6) k).state = none) ↔
    ∃ i, (Aiter i (8, 2)).1 % 2 = 1 ∧ (Aiter i (8, 2)).1 / 2 ≥ 1 ∧ (Aiter i (8, 2)).2 = 0 := by
  have hv : isValidLoopStart (run antihydra (initConfig 6) 58) :=
    antihydra_init_loop_start ▸ isValidLoopStart_P248
  have step1 : (∃ k, (run antihydra (initConfig 6) k).state = none) ↔
               (∃ k, (run antihydra (run antihydra (initConfig 6) 58) k).state = none) := by
    constructor
    · rintro ⟨k, hk⟩
      by_cases h : 58 ≤ k
      · refine ⟨k - 58, ?_⟩
        have heq : run antihydra (initConfig 6) (58 + (k - 58)) = run antihydra (run antihydra (initConfig 6) 58) (k - 58) := run_add _ _ _ _
        rw [Nat.add_sub_cancel' h] at heq
        rw [← heq]; exact hk
      · exact absurd hk (no_halt_before_58 k (by omega))
    · rintro ⟨k, hk⟩
      exact ⟨58 + k, show (run antihydra (initConfig 6) (58 + k)).state = none by rw [run_add]; exact hk⟩
  rw [step1, tm_halt_iff_math_condition _ hv, antihydra_init_math_state]
  exact mathHalts_iff_Aiter_8_2

end Antihydra
