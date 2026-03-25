import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Antihydra

-- 1. Finitary Types for optimal pattern matching
abbrev TapeSymbol := Bool -- false = 0 (blank), true = 1
abbrev State  := Fin 6 -- The 6 non-halt states of your BB(6)

inductive Dir where | L | R
deriving DecidableEq, Repr

-- 2. The Transition Table (deterministic function)
-- Returns: (Next State (none = HALT), Write Symbol, Move Direction)
def transition (q : State) (s : TapeSymbol) : Option State × TapeSymbol × Dir :=
  match q.val, s with
  -- A
  | 0, false => (some ⟨1, by decide⟩, true, Dir.R)
  | 0, true  => (some ⟨0, by decide⟩, true, Dir.R)
  -- B
  | 1, false => (some ⟨2, by decide⟩, false, Dir.L)
  | 1, true  => (some ⟨4, by decide⟩, true, Dir.L)
  -- C
  | 2, false => (some ⟨3, by decide⟩, true, Dir.L)
  | 2, true  => (some ⟨2, by decide⟩, true, Dir.L)
  -- D
  | 3, false => (some ⟨0, by decide⟩, true, Dir.L)
  | 3, true  => (some ⟨1, by decide⟩, false, Dir.L)
  -- E
  | 4, false => (some ⟨5, by decide⟩, true, Dir.L)
  | 4, true  => (some ⟨4, by decide⟩, true, Dir.R)
  -- F
  | 5, false => (none, false, Dir.R)
  | 5, true  => (some ⟨0, by decide⟩, false, Dir.R)
  | _, _     => (none, false, Dir.R)

-- 3. The Configuration using a Zipper Tape
structure Config where
  state : Option State      -- none represents the HALT state
  left  : List TapeSymbol       -- Reversed: first element is immediately left of head
  head  : TapeSymbol
  right : List TapeSymbol       -- First element is immediately right of head
deriving Repr, Inhabited

def tailD' {α : Type} (l : List α) : List α :=
  match l with
  | [] => []
  | _ :: as => as

def headD' {α : Type} (l : List α) (default : α) : α :=
  match l with
  | [] => default
  | a :: _ => a

-- 4. The Deterministic Step Function
-- A zipper makes moving O(1) and trivially easy to prove by `simp`.
def step (c : Config) : Config :=
  match c.state with
  | none => c -- HALT state is a fixed point
  | some q =>
    let (q', w, d) := transition q c.head
    match d with
    | Dir.R =>
      let newRight := tailD' c.right
      let newHead := headD' c.right false
      { state := q', left := w :: c.left, head := newHead, right := newRight }
    | Dir.L =>
      let newLeft := tailD' c.left
      let newHead := headD' c.left false
      { state := q', left := newLeft, head := newHead, right := w :: c.right }

-- Run the machine for `n` steps
def run (c : Config) (n : Nat) : Config :=
  match n with
  | 0 => c
  | n' + 1 => run (step c) n'

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

-- 6. The "p-Proof" (Connection Methodology)

def countOnes : List TapeSymbol → Nat
  | [] => 0
  | true :: xs => countOnes xs + 1
  | false :: _ => 0

def repeatOne (k : Nat) : List TapeSymbol :=
  List.replicate k true

def repeatFalse (k : Nat) : List TapeSymbol :=
  List.replicate k false

@[simp] lemma repeatOne_succ (k : Nat) : repeatOne (k + 1) = true :: repeatOne k := rfl
@[simp] lemma repeatFalse_succ (k : Nat) : repeatFalse (k + 1) = false :: repeatFalse k := rfl
@[simp] lemma repeatOne_zero : repeatOne 0 = [] := rfl
@[simp] lemma repeatFalse_zero : repeatFalse 0 = [] := rfl


lemma run_add (c : Config) (n m : Nat) : run c (n + m) = run (run c n) m := by
  induction n generalizing c with
  | zero => rw [Nat.zero_add]; rfl
  | succ n ih =>
    calc
      run c (n + 1 + m) = run c (n + m + 1) := by congr 1; omega
      _ = run (step c) (n + m) := rfl
      _ = run (run (step c) n) m := ih (step c)
      _ = run (run c (n + 1)) m := rfl

def P_Config_Pad (b : Nat) (m : Nat) (n : Nat) (p : Nat) : Config :=
  { state := some ⟨4, by decide⟩,
    head := false,
    left := repeatOne m ++ [false] ++ repeatOne b,
    right := repeatOne n ++ repeatFalse p
  }

@[simp] lemma repeatOne_append_true (k : Nat) (L : List TapeSymbol) :
  repeatOne k ++ true :: L = repeatOne (k + 1) ++ L := by
  induction k with | zero => rfl | succ k ih => simp [repeatOne_succ, ih]

@[simp] lemma headD'_replicate_true (k : Nat) (R : List TapeSymbol) :
  headD' (repeatOne (k + 1) ++ R) false = true := rfl

@[simp] lemma tailD'_replicate_true (k : Nat) (R : List TapeSymbol) :
  tailD' (repeatOne (k + 1) ++ R) = repeatOne k ++ R := rfl

@[simp] lemma run_step_succ (c : Config) (n : Nat) :
  run c (n + 1) = run (step c) n := rfl

lemma A_shift (k : Nat) (L R : List TapeSymbol) :
  run { state := some ⟨0, by decide⟩, head := true, left := L, right := repeatOne k ++ R } (k + 1) =
  { state := some ⟨0, by decide⟩, head := headD' R false, left := repeatOne (k + 1) ++ L, right := tailD' R } := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    calc
      run { state := some ⟨0, by decide⟩, head := true, left := L, right := repeatOne (k + 1) ++ R } (k + 2)
      _ = run { state := some ⟨0, by decide⟩, head := true, left := true :: L, right := repeatOne k ++ R } (k + 1) := rfl
      _ = _ := by rw [ih (true :: L)]; simp

lemma C_shift (k : Nat) (L R : List TapeSymbol) :
  run { state := some ⟨2, by decide⟩, head := true, left := repeatOne k ++ L, right := R } (k + 1) =
  { state := some ⟨2, by decide⟩, head := headD' L false, left := tailD' L, right := repeatOne (k + 1) ++ R } := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    calc
      run { state := some ⟨2, by decide⟩, head := true, left := repeatOne (k + 1) ++ L, right := R } (k + 2)
      _ = run { state := some ⟨2, by decide⟩, head := true, left := repeatOne k ++ L, right := true :: R } (k + 1) := rfl
      _ = _ := by rw [ih (true :: R)]; simp

lemma E_shift (k : Nat) (L R : List TapeSymbol) :
  run { state := some ⟨4, by decide⟩, head := true, left := L, right := repeatOne k ++ R } (k + 1) =
  { state := some ⟨4, by decide⟩, head := headD' R false, left := repeatOne (k + 1) ++ L, right := tailD' R } := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    calc
      run { state := some ⟨4, by decide⟩, head := true, left := L, right := repeatOne (k + 1) ++ R } (k + 2)
      _ = run { state := some ⟨4, by decide⟩, head := true, left := true :: L, right := repeatOne k ++ R } (k + 1) := rfl
      _ = _ := by rw [ih (true :: L)]; simp

@[simp] lemma headD'_cons {α} (x : α) (xs : List α) (d : α) : headD' (x :: xs) d = x := rfl
@[simp] lemma tailD'_cons {α} (x : α) (xs : List α) : tailD' (x :: xs) = xs := rfl

@[simp] lemma headD'_repeatOne_false (m : Nat) (L : List TapeSymbol) : headD' (repeatOne m ++ false :: L) false = if m = 0 then false else true := by
  cases m with
  | zero => rfl
  | succ m => rfl

@[simp] lemma tailD'_repeatOne_false (m : Nat) (L : List TapeSymbol) : tailD' (repeatOne m ++ false :: L) = if m = 0 then L else repeatOne (m-1) ++ false :: L := by
  cases m with
  | zero => rfl
  | succ m => rfl

@[simp] lemma headD'_false_cons (R : List TapeSymbol) : headD' (false :: R) false = false := rfl
@[simp] lemma tailD'_false_cons (R : List TapeSymbol) : tailD' (false :: R) = R := rfl
@[simp] lemma headD'_nil (b : TapeSymbol) : headD' [] b = b := rfl
@[simp] lemma tailD'_nil : @tailD' TapeSymbol [] = [] := rfl

-- Macro Loop Steps

theorem tm_P_step (b m n p : Nat) : run (P_Config_Pad b (m+2+2) n (p+2)) (2*n + 12) = P_Config_Pad b (m+2) (n+3) (p+1) := by
  -- Step 1: E(m+2+2, n) -> state 5
  rw [show 2*n + 12 = 1 + (2*n + 11) by omega, run_add]
  have step1 : run (P_Config_Pad b (m+2+2) n (p+2)) 1 =
    { state := some ⟨5, by decide⟩, head := true, left := repeatOne (m+2+1) ++ false :: repeatOne b, right := repeatOne (n+1) ++ repeatFalse (p+2) } := by
    simp [run, step, transition, P_Config_Pad]
  rw [step1]

  -- Step 2: state 5 -> A(m+2+1, n)
  rw [show 2*n + 11 = 1 + (2*n + 10) by omega, run_add]
  have step2 : run { state := some ⟨5, by decide⟩, head := true, left := repeatOne (m+2+1) ++ false :: repeatOne b, right := repeatOne (n+1) ++ repeatFalse (p+2) } 1 =
    { state := some ⟨0, by decide⟩, head := true, left := false :: repeatOne (m+2+1) ++ false :: repeatOne b, right := repeatOne n ++ repeatFalse (p+2) } := by
    simp [run, step, transition]
  rw [step2]

  -- Step 3: A_shift (n+1 steps)
  rw [show 2*n + 10 = (n+1) + (n+9) by omega, run_add]
  have step3 : run { state := some ⟨0, by decide⟩, head := true, left := false :: repeatOne (m+2+1) ++ false :: repeatOne b, right := repeatOne n ++ repeatFalse (p+2) } (n+1) =
    { state := some ⟨0, by decide⟩, head := false, left := repeatOne (n+1) ++ (false :: repeatOne (m+2+1) ++ false :: repeatOne b), right := repeatFalse (p+1) } := by
    have hA := A_shift n (false :: repeatOne (m+2+1) ++ false :: repeatOne b) (repeatFalse (p+2))
    have hp_head : headD' (repeatFalse (p+2)) false = false := rfl
    have hp_tail : tailD' (repeatFalse (p+2)) = repeatFalse (p+1) := rfl
    rw [hp_head, hp_tail] at hA
    exact hA
  rw [step3]

  -- Step 4: A0 -> B1
  rw [show n + 9 = 1 + (n + 8) by omega, run_add]
  have step4 : run { state := some ⟨0, by decide⟩, head := false, left := repeatOne (n+1) ++ (false :: repeatOne (m+2+1) ++ false :: repeatOne b), right := repeatFalse (p+1) } 1 =
    { state := some ⟨1, by decide⟩, head := false, left := true :: repeatOne (n+1) ++ (false :: repeatOne (m+2+1) ++ false :: repeatOne b), right := repeatFalse p } := by
    simp [run, step, transition]
  rw [step4]

  -- Step 5: B0 -> C1
  rw [show n + 8 = 1 + (n + 7) by omega, run_add]
  have step5 : run { state := some ⟨1, by decide⟩, head := false, left := true :: repeatOne (n+1) ++ (false :: repeatOne (m+2+1) ++ false :: repeatOne b), right := repeatFalse p } 1 =
    { state := some ⟨2, by decide⟩, head := true, left := repeatOne (n+1) ++ (false :: repeatOne (m+2+1) ++ false :: repeatOne b), right := false :: repeatFalse p } := by
    simp [run, step, transition]
  rw [step5]

  -- Step 6: C1 shift (n+2 steps)
  rw [show n + 7 = (n+2) + 5 by omega, run_add]
  have step6 : run { state := some ⟨2, by decide⟩, head := true, left := repeatOne (n+1) ++ (false :: repeatOne (m+2+1) ++ false :: repeatOne b), right := false :: repeatFalse p } (n+2) =
    { state := some ⟨2, by decide⟩, head := false, left := repeatOne (m+2+1) ++ false :: repeatOne b, right := repeatOne (n+2) ++ false :: repeatFalse p } := by
    have hC := C_shift (n+1) (false :: repeatOne (m+2+1) ++ false :: repeatOne b) (false :: repeatFalse p)
    have hC_head : headD' (false :: repeatOne (m+2+1) ++ false :: repeatOne b) false = false := rfl
    have hC_tail : tailD' (false :: repeatOne (m+2+1) ++ false :: repeatOne b) = repeatOne (m+2+1) ++ false :: repeatOne b := rfl
    rw [hC_head, hC_tail] at hC
    exact hC
  rw [step6]

  -- Step 7: C0 -> D1
  rw [show 5 = 1 + 4 by omega, run_add]
  have step7 : run { state := some ⟨2, by decide⟩, head := false, left := repeatOne (m+2+1) ++ false :: repeatOne b, right := repeatOne (n+2) ++ false :: repeatFalse p } 1 =
    { state := some ⟨3, by decide⟩, head := true, left := repeatOne (m+2) ++ false :: repeatOne b, right := true :: repeatOne (n+2) ++ false :: repeatFalse p } := by
    simp [run, step, transition]
  rw [step7]

  -- Step 8: D1 -> 1
  rw [show 4 = 1 + 3 by omega, run_add]
  have step8 : run { state := some ⟨3, by decide⟩, head := true, left := repeatOne (m+2) ++ false :: repeatOne b, right := true :: repeatOne (n+2) ++ false :: repeatFalse p } 1 =
    { state := some ⟨1, by decide⟩, head := headD' (repeatOne (m+2) ++ false :: repeatOne b) false, left := tailD' (repeatOne (m+2) ++ false :: repeatOne b), right := false :: true :: repeatOne (n+2) ++ false :: repeatFalse p } := by
    simp [run, step, transition]
  rw [step8]

  -- Step 9: 1 -> 4
  rw [show 3 = 1 + 2 by omega, run_add]
  have step9 : run { state := some ⟨1, by decide⟩, head := headD' (repeatOne (m+2) ++ false :: repeatOne b) false, left := tailD' (repeatOne (m+2) ++ false :: repeatOne b), right := false :: true :: repeatOne (n+2) ++ false :: repeatFalse p } 1 =
    { state := some ⟨4, by decide⟩, head := true, left := tailD' (tailD' (repeatOne (m+2) ++ false :: repeatOne b)), right := true :: false :: true :: repeatOne (n+2) ++ false :: repeatFalse p } := by
    -- m+2 >= 1, so head is true
    have h_head : headD' (repeatOne (m+2) ++ false :: repeatOne b) false = true := rfl
    rw [h_head]
    simp [run, step, transition]
  rw [step9]

  -- Step 10: 4 -> 4 (Right)
  rw [show 2 = 1 + 1 by omega, run_add]
  have step10 : run { state := some ⟨4, by decide⟩, head := true, left := tailD' (tailD' (repeatOne (m+2) ++ false :: repeatOne b)), right := true :: false :: true :: repeatOne (n+2) ++ false :: repeatFalse p } 1 =
    { state := some ⟨4, by decide⟩, head := true, left := true :: tailD' (tailD' (repeatOne (m+2) ++ false :: repeatOne b)), right := false :: true :: repeatOne (n+2) ++ false :: repeatFalse p } := by
    simp [run, step, transition]
  rw [step10]

  -- Step 11: 4 -> 4 (Right)
  rw [show 1 = 1 + 0 by omega, run_add]
  have step11 : run { state := some ⟨4, by decide⟩, head := true, left := true :: tailD' (tailD' (repeatOne (m+2) ++ false :: repeatOne b)), right := false :: true :: repeatOne (n+2) ++ false :: repeatFalse p } 1 =
    { state := some ⟨4, by decide⟩, head := false, left := true :: true :: tailD' (tailD' (repeatOne (m+2) ++ false :: repeatOne b)), right := true :: repeatOne (n+2) ++ false :: repeatFalse p } := by
    simp [run, step, transition]
  rw [step11]

  -- Final matching: P_Config_Pad b (m+2) (n+3) (p+1)
  change run _ 0 = _
  rw [run]
  simp [P_Config_Pad]





theorem tm_P_multistep (b m n p k : Nat) :
  run (P_Config_Pad b (m+2 + 2*k) n (p+1 + k)) (k*(2*n + 3*k + 9)) = P_Config_Pad b (m+2) (n+3*k) (p+1) := by
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
    -- Note that m + 2 + 2(k'+1) = (m + 2*k') + 2 + 2
    -- and p + 1 + (k'+1) = (p + k') + 2
    have h_m : m + 2 + 2 * (k' + 1) = (m + 2 * k') + 2 + 2 := by omega
    have h_p : p + 1 + (k' + 1) = (p + k') + 2 := by omega

    -- We can rewrite the inner run with tm_P_step
    have step1 : run (P_Config_Pad b (m + 2 + 2 * (k' + 1)) n (p + 1 + (k' + 1))) (2 * n + 12) = P_Config_Pad b ((m + 2 * k') + 2) (n + 3) ((p + k') + 1) := by
      rw [h_m, h_p]
      exact tm_P_step b (m + 2 * k') n (p + k')

    rw [step1]

    -- Now we need to apply the IH for n+3
    -- The IH state is P_Config_Pad b (m + 2 + 2*k') (n+3) (p + 1 + k')
    -- Let's check that
    have h_m2 : (m + 2 * k') + 2 = m + 2 + 2 * k' := by omega
    have h_p2 : (p + k') + 1 = p + 1 + k' := by omega
    have h_n2 : n + 3 * (k' + 1) = (n + 3) + 3 * k' := by omega

    rw [h_m2, h_p2]
    rw [ih (n + 3)]
    rw [h_n2]

-- Even Endgame (m=0)
theorem tm_even_endgame (b N p : Nat) :
  (run (P_Config_Pad b 0 N (p+2)) 2).state = none := by
  have step1 : run (P_Config_Pad b 0 N (p+2)) 1 =
    { state := some ⟨5, by decide⟩, head := false, left := repeatOne b, right := true :: repeatOne N ++ repeatFalse (p+2) } := by
    simp [run, step, transition, P_Config_Pad]
  rw [show 2 = 1 + 1 by rfl, run_add, step1]
  have step2 : run { state := some ⟨5, by decide⟩, head := false, left := repeatOne b, right := true :: repeatOne N ++ repeatFalse (p+2) } 1 =
    { state := none, head := true, left := false :: repeatOne b, right := repeatOne N ++ repeatFalse (p+2) } := by
    cases b with
    | zero => simp [run, step, transition]
    | succ b' => simp [run, step, transition]
  rw [step2]

-- Odd Endgame (m=3, b>0)
theorem tm_odd_endgame (b' N p : Nat) :
  run (P_Config_Pad (b' + 1) 3 N (p+2)) (3*N + 20) = P_Config_Pad b' (N+6) 0 p := by
  have step1 : run (P_Config_Pad (b' + 1) 3 N (p+2)) 1 =
    { state := some ⟨5, by decide⟩, head := true, left := repeatOne 2 ++ false :: repeatOne (b'+1), right := repeatOne (N+1) ++ repeatFalse (p+2) } := by
    simp [run, step, transition, P_Config_Pad]

  have step2 : run { state := some ⟨5, by decide⟩, head := true, left := repeatOne 2 ++ false :: repeatOne (b'+1), right := repeatOne (N+1) ++ repeatFalse (p+2) } 1 =
    { state := some ⟨0, by decide⟩, head := true, left := false :: repeatOne 2 ++ false :: repeatOne (b'+1), right := repeatOne N ++ repeatFalse (p+2) } := by
    cases N with
    | zero => simp [run, step, transition]
    | succ N' => simp [run, step, transition]

  -- Step 3: A_shift N
  have step3 : run { state := some ⟨0, by decide⟩, head := true, left := false :: repeatOne 2 ++ false :: repeatOne (b'+1), right := repeatOne N ++ repeatFalse (p+2) } (N+1) =
    { state := some ⟨0, by decide⟩, head := false, left := repeatOne (N+1) ++ (false :: repeatOne 2 ++ false :: repeatOne (b'+1)), right := repeatFalse (p+1) } := by
    have hA := A_shift N (false :: repeatOne 2 ++ false :: repeatOne (b'+1)) (repeatFalse (p+2))
    have hp_head : headD' (repeatFalse (p+2)) false = false := rfl
    have hp_tail : tailD' (repeatFalse (p+2)) = repeatFalse (p+1) := rfl
    rw [hp_head, hp_tail] at hA
    exact hA

  -- Step 4: State 0, reading false
  have step4 : run { state := some ⟨0, by decide⟩, head := false, left := repeatOne (N+1) ++ (false :: repeatOne 2 ++ false :: repeatOne (b'+1)), right := repeatFalse (p+1) } 1 =
    { state := some ⟨1, by decide⟩, head := false, left := true :: repeatOne (N+1) ++ (false :: repeatOne 2 ++ false :: repeatOne (b'+1)), right := repeatFalse p } := by
    simp [run, step, transition]

  -- Step 5: State 1, reading false
  have step5 : run { state := some ⟨1, by decide⟩, head := false, left := true :: repeatOne (N+1) ++ (false :: repeatOne 2 ++ false :: repeatOne (b'+1)), right := repeatFalse p } 1 =
    { state := some ⟨2, by decide⟩, head := true, left := repeatOne (N+1) ++ (false :: repeatOne 2 ++ false :: repeatOne (b'+1)), right := false :: repeatFalse p } := by
    simp [run, step, transition]

  -- Step 6: C_shift (N+1)
  have step6 : run { state := some ⟨2, by decide⟩, head := true, left := repeatOne (N+1) ++ (false :: repeatOne 2 ++ false :: repeatOne (b'+1)), right := false :: repeatFalse p } (N+2) =
    { state := some ⟨2, by decide⟩, head := false, left := repeatOne 2 ++ false :: repeatOne (b'+1), right := repeatOne (N+2) ++ false :: repeatFalse p } := by
    have hC := C_shift (N+1) (false :: repeatOne 2 ++ false :: repeatOne (b'+1)) (false :: repeatFalse p)
    have hp_head : headD' (false :: repeatOne 2 ++ false :: repeatOne (b'+1)) false = false := rfl
    have hp_tail : tailD' (false :: repeatOne 2 ++ false :: repeatOne (b'+1)) = repeatOne 2 ++ false :: repeatOne (b'+1) := rfl
    rw [hp_head, hp_tail] at hC
    exact hC

  -- Step 7: State 2, reading false
  have step7 : run { state := some ⟨2, by decide⟩, head := false, left := repeatOne 2 ++ false :: repeatOne (b'+1), right := repeatOne (N+2) ++ false :: repeatFalse p } 1 =
    { state := some ⟨3, by decide⟩, head := true, left := repeatOne 1 ++ false :: repeatOne (b'+1), right := repeatOne (N+3) ++ false :: repeatFalse p } := by
    simp [run, step, transition]

  -- Step 8: State 3, reading true
  have step8 : run { state := some ⟨3, by decide⟩, head := true, left := repeatOne 1 ++ false :: repeatOne (b'+1), right := repeatOne (N+3) ++ false :: repeatFalse p } 1 =
    { state := some ⟨1, by decide⟩, head := true, left := false :: repeatOne (b'+1), right := false :: repeatOne (N+3) ++ false :: repeatFalse p } := by
    simp [run, step, transition, repeatOne]

  -- Step 9: State 1, reading true
  have step9 : run { state := some ⟨1, by decide⟩, head := true, left := false :: repeatOne (b'+1), right := false :: repeatOne (N+3) ++ false :: repeatFalse p } 1 =
    { state := some ⟨4, by decide⟩, head := false, left := repeatOne (b'+1), right := true :: false :: repeatOne (N+3) ++ false :: repeatFalse p } := by
    simp [run, step, transition, repeatOne]

  -- Step 10: State 4, reading false
  have step10 : run { state := some ⟨4, by decide⟩, head := false, left := repeatOne (b'+1), right := true :: false :: repeatOne (N+3) ++ false :: repeatFalse p } 1 =
    { state := some ⟨5, by decide⟩, head := true, left := repeatOne b', right := true :: true :: false :: repeatOne (N+3) ++ false :: repeatFalse p } := by
    simp [run, step, transition]

  -- Step 11: State 5, reading true
  have step11 : run { state := some ⟨5, by decide⟩, head := true, left := repeatOne b', right := true :: true :: false :: repeatOne (N+3) ++ false :: repeatFalse p } 1 =
    { state := some ⟨0, by decide⟩, head := true, left := false :: repeatOne b', right := true :: false :: repeatOne (N+3) ++ false :: repeatFalse p } := by
    simp [run, step, transition]

  -- Step 12: State 0, reading true
  have step12 : run { state := some ⟨0, by decide⟩, head := true, left := false :: repeatOne b', right := true :: false :: repeatOne (N+3) ++ false :: repeatFalse p } 1 =
    { state := some ⟨0, by decide⟩, head := true, left := true :: false :: repeatOne b', right := false :: repeatOne (N+3) ++ false :: repeatFalse p } := by
    simp [run, step, transition, repeatOne]

  -- Step 13: State 0, reading true
  have step13 : run { state := some ⟨0, by decide⟩, head := true, left := true :: false :: repeatOne b', right := false :: repeatOne (N+3) ++ false :: repeatFalse p } 1 =
    { state := some ⟨0, by decide⟩, head := false, left := true :: true :: false :: repeatOne b', right := repeatOne (N+3) ++ false :: repeatFalse p } := by
    simp [run, step, transition, repeatOne]

  -- Step 14: State 0, reading false
  have step14 : run { state := some ⟨0, by decide⟩, head := false, left := true :: true :: false :: repeatOne b', right := repeatOne (N+3) ++ false :: repeatFalse p } 1 =
    { state := some ⟨1, by decide⟩, head := true, left := true :: true :: true :: false :: repeatOne b', right := repeatOne (N+2) ++ false :: repeatFalse p } := by
    have h_N3 : repeatOne (N+3) = true :: repeatOne (N+2) := rfl
    rw [h_N3]
    simp [run, step, transition, repeatOne]

  -- Step 15: State 1, reading true
  have step15 : run { state := some ⟨1, by decide⟩, head := true, left := true :: true :: true :: false :: repeatOne b', right := repeatOne (N+2) ++ false :: repeatFalse p } 1 =
    { state := some ⟨4, by decide⟩, head := true, left := true :: true :: false :: repeatOne b', right := repeatOne (N+3) ++ false :: repeatFalse p } := by
    have h_N3 : repeatOne (N+3) = true :: repeatOne (N+2) := rfl
    rw [h_N3]
    simp [run, step, transition, repeatOne]

  -- Step 16: E_shift (N+3)
  -- Wait, left is `true :: true :: false :: repeatOne b'`, which is exactly `repeatOne 2 ++ false :: repeatOne b'`!
  have step16 : run { state := some ⟨4, by decide⟩, head := true, left := repeatOne 2 ++ false :: repeatOne b', right := repeatOne (N+3) ++ false :: repeatFalse p } (N+4) =
    { state := some ⟨4, by decide⟩, head := false, left := repeatOne (N+4) ++ (repeatOne 2 ++ false :: repeatOne b'), right := repeatFalse p } := by
    have hE := E_shift (N+3) (repeatOne 2 ++ false :: repeatOne b') (false :: repeatFalse p)
    have hp_head : headD' (false :: repeatFalse p) false = false := rfl
    have hp_tail : tailD' (false :: repeatFalse p) = repeatFalse p := rfl
    rw [hp_head, hp_tail] at hE
    exact hE

  rw [show 3*N + 20 = 1 + (1 + ((N+1) + (1 + (1 + ((N+2) + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (N+4))))))))))))))) by omega]
  rw [run_add, step1]
  rw [run_add, step2]
  rw [run_add, step3]
  rw [run_add, step4]
  rw [run_add, step5]
  rw [run_add, step6]
  rw [run_add, step7]
  rw [run_add, step8]
  rw [run_add, step9]
  rw [run_add, step10]
  rw [run_add, step11]
  rw [run_add, step12]
  rw [run_add, step13]
  rw [run_add, step14]
  rw [run_add, step15]

  -- Before step16, the left tape is `true :: true :: false :: repeatOne b'`, which is definitional equal to `repeatOne 2 ++ ...`
  have h_left_eq : (true :: true :: false :: repeatOne b') = repeatOne 2 ++ false :: repeatOne b' := rfl
  rw [h_left_eq]
  rw [step16]

  have h_append : repeatOne (N+4) ++ (repeatOne 2 ++ false :: repeatOne b') = repeatOne (N+6) ++ false :: repeatOne b' := by
    rw [← List.append_assoc]
    have h1 : repeatOne (N+4) ++ repeatOne 2 = repeatOne (N+6) := by
      change List.replicate (N+4) true ++ List.replicate 2 true = List.replicate (N+6) true
      rw [← List.replicate_add]
    rw [h1]

  -- Apply definitional equality to match P_Config_Pad
  unfold P_Config_Pad
  have h_right : repeatOne 0 ++ repeatFalse p = repeatFalse p := rfl
  have h_left_pad : repeatOne (N+6) ++ [false] ++ repeatOne b' = repeatOne (N+6) ++ false :: repeatOne b' := by simp
  rw [h_right, h_left_pad, ← h_append]

@[simp] lemma drop_repeatOne (a : Nat) (L : List TapeSymbol) :
  (repeatOne a ++ L).drop a = L := by
  induction a with
  | zero => rfl
  | succ a ih =>
    simp [repeatOne, *]

@[simp] lemma countOnes_repeatOne (a : Nat) :
  countOnes (repeatOne a) = a := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [repeatOne_succ, countOnes, ih]

@[simp] lemma countOnes_repeatOne_false (a : Nat) (L : List TapeSymbol) :
  countOnes (repeatOne a ++ false :: L) = a := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [repeatOne_succ, List.cons_append, countOnes, ih]

-- A. The Abstraction Function (Decoding the Tape)
def decodeTape (c : Config) : MathState :=
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

@[simp] lemma all_repeatFalse (p : Nat) : (repeatFalse p).all (!·) = true := by
  induction p with
  | zero => rfl
  | succ p ih => simp [repeatFalse]

@[simp] lemma drop_repeatOne_exact (a : Nat) : (repeatOne a).drop a = [] := by
  induction a with
  | zero => rfl
  | succ a ih => simp [repeatOne]

-- B. Defining the "Clean" Invariant
-- Based on the BBchallenge definition, E(a,b) is TM in state E
def isValidLoopStart (c : Config) : Prop :=
  c.state = some ⟨4, by decide⟩ ∧
  c.head = false ∧
  (c.right.all (!·) = true) ∧
  (countOnes c.left ≥ 2) ∧
  ∃ b : Nat, c.left.drop (countOnes c.left) = false :: repeatOne b

lemma isValidLoopStart_P_Config_Pad (b a p : Nat) (ha : a ≥ 2) :
  isValidLoopStart (P_Config_Pad b a 0 p) := by
  unfold isValidLoopStart P_Config_Pad
  refine ⟨rfl, rfl, by simp, by simp [ha], b, by simp⟩

lemma take_countOnes_eq_repeatOne (L : List TapeSymbol) :
  L.take (countOnes L) = repeatOne (countOnes L) := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    cases x
    · rfl
    · simp [countOnes, repeatOne]
      rw [ih]
      rfl

lemma list_eq_repeatOne_drop (L : List TapeSymbol) :
  L = repeatOne (countOnes L) ++ L.drop (countOnes L) := by
  rw [← take_countOnes_eq_repeatOne L]
  exact (List.take_append_drop _ _).symm

lemma all_false_eq_repeatFalse (L : List TapeSymbol) (h : L.all (!·) = true) :
  L = repeatFalse L.length := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    cases x
    · change (xs.all (!·) = true) at h
      exact congrArg (List.cons false) (ih h)
    · change (false = true) at h
      contradiction

lemma isValidLoopStart_eq_P_Config_Pad (c : Config) (hm : isValidLoopStart c) :
  ∃ a b p, c = P_Config_Pad b a 0 p ∧ a ≥ 2 := by
  rcases c with ⟨state, left, head, right⟩
  unfold isValidLoopStart at hm
  rcases hm with ⟨hstate, hhead, hright, ha, ⟨b, hb⟩⟩
  have hleft_full : left = repeatOne (countOnes left) ++ [false] ++ repeatOne b := by
    rw [list_eq_repeatOne_drop left, hb]; simp [List.append_assoc]

  have hright_full : right = repeatFalse right.length := all_false_eq_repeatFalse _ hright

  use (countOnes left), b, right.length
  constructor
  · unfold P_Config_Pad; congr
  · exact ha



-- Right-tape padding independence: two configs that differ only in trailing zeros behave the same

/-- Two right tapes are equivalent if they agree at every index (with false as default). -/
def RightPadEquiv (R1 R2 : List TapeSymbol) : Prop :=
  ∀ i : Nat, R1.getD i false = R2.getD i false

lemma headD'_eq_getD_zero (R : List TapeSymbol) :
    headD' R false = R.getD 0 false := by
  cases R with | nil => rfl | cons x xs => rfl

lemma tailD'_getD (R : List TapeSymbol) (i : Nat) :
    (tailD' R).getD i false = R.getD (i + 1) false := by
  cases R with
  | nil => simp [tailD', List.getD]
  | cons x xs => simp [tailD', List.getD]

lemma rightPadEquiv_headD' (R1 R2 : List TapeSymbol) (h : RightPadEquiv R1 R2) :
    headD' R1 false = headD' R2 false := by
  rw [headD'_eq_getD_zero, headD'_eq_getD_zero]; exact h 0

lemma rightPadEquiv_tailD' (R1 R2 : List TapeSymbol) (h : RightPadEquiv R1 R2) :
    RightPadEquiv (tailD' R1) (tailD' R2) := by
  intro i; rw [tailD'_getD, tailD'_getD]; exact h (i + 1)

lemma rightPadEquiv_cons (w : TapeSymbol) (R1 R2 : List TapeSymbol) (h : RightPadEquiv R1 R2) :
    RightPadEquiv (w :: R1) (w :: R2) := by
  intro i; cases i with | zero => rfl | succ i => simp [List.getD]; exact h i

lemma step_rightPadEquiv (c1 c2 : Config)
    (hs : c1.state = c2.state) (hl : c1.left = c2.left)
    (hh : c1.head = c2.head) (hr : RightPadEquiv c1.right c2.right) :
    (step c1).state = (step c2).state ∧
    (step c1).left = (step c2).left ∧
    (step c1).head = (step c2).head ∧
    RightPadEquiv (step c1).right (step c2).right := by
  rcases c1 with ⟨s, L, hd, R1⟩
  rcases c2 with ⟨s2, L2, hd2, R2⟩
  simp only at hs hl hh
  subst hs; subst hl; subst hh
  have hhead := rightPadEquiv_headD' _ _ hr
  have htail := rightPadEquiv_tailD' _ _ hr
  cases s with
  | none => exact ⟨rfl, rfl, rfl, hr⟩
  | some q =>
    unfold step; dsimp only []
    generalize transition q hd = tr
    obtain ⟨q', w, d⟩ := tr
    cases d with
    | L => dsimp only []; exact ⟨rfl, rfl, rfl, rightPadEquiv_cons w R1 R2 hr⟩
    | R => dsimp only []; exact ⟨rfl, rfl, hhead, htail⟩

lemma run_rightPadEquiv (c1 c2 : Config) (k : Nat)
    (hs : c1.state = c2.state) (hl : c1.left = c2.left)
    (hh : c1.head = c2.head) (hr : RightPadEquiv c1.right c2.right) :
    (run c1 k).state = (run c2 k).state ∧
    (run c1 k).left = (run c2 k).left ∧
    (run c1 k).head = (run c2 k).head ∧
    RightPadEquiv (run c1 k).right (run c2 k).right := by
  induction k generalizing c1 c2 with
  | zero => exact ⟨hs, hl, hh, hr⟩
  | succ k ih =>
    simp only [run]
    have h := step_rightPadEquiv c1 c2 hs hl hh hr
    exact ih _ _ h.1 h.2.1 h.2.2.1 h.2.2.2

lemma rightPadEquiv_append_repeatFalse (R : List TapeSymbol) (p q : Nat) :
    RightPadEquiv (R ++ repeatFalse p) (R ++ repeatFalse q) := by
  intro i
  simp only [List.getD]
  by_cases hi : i < R.length
  · rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
  · push_neg at hi
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    simp [repeatFalse, List.getElem?_replicate]
    split <;> split <;> simp_all

lemma rightPadEquiv_repeatFalse (p q : Nat) :
    RightPadEquiv (repeatFalse p) (repeatFalse q) := by
  have := rightPadEquiv_append_repeatFalse [] p q; simpa

private lemma getD_false_of_all_false (R : List TapeSymbol) (h : R.all (!·) = true)
    (i : Nat) : R.getD i false = false := by
  induction R generalizing i with
  | nil => simp [List.getD]
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [List.getD, List.getElem?_cons_zero, Option.getD_some]
      simp only [List.all_cons, Bool.and_eq_true] at h
      cases x <;> simp_all
    | succ i =>
      simp only [List.getD, List.getElem?_cons_succ]
      simp only [List.all_cons, Bool.and_eq_true] at h
      exact ih h.2 i

private lemma all_false_of_getD_false (R : List TapeSymbol)
    (h : ∀ i : Nat, R.getD i false = false) : R.all (!·) = true := by
  induction R with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons, Bool.and_eq_true]
    constructor
    · have := h 0; simp only [List.getD, List.getElem?_cons_zero, Option.getD_some] at this
      cases x <;> simp_all
    · exact ih (fun i => by have := h (i + 1); simp only [List.getD, List.getElem?_cons_succ] at this; exact this)

lemma rightPadEquiv_all_false {R1 R2 : List TapeSymbol}
    (h : RightPadEquiv R1 R2) (h2 : R2.all (!·) = true) :
    R1.all (!·) = true :=
  all_false_of_getD_false R1 (fun i => by rw [h i]; exact getD_false_of_all_false R2 h2 i)

-- Transfer lemmas for padding independence

lemma isValidLoopStart_of_rightPadEquiv {c1 c2 : Config}
    (hs : c1.state = c2.state) (hl : c1.left = c2.left)
    (hh : c1.head = c2.head) (hr : RightPadEquiv c1.right c2.right)
    (hv : isValidLoopStart c2) : isValidLoopStart c1 := by
  unfold isValidLoopStart at hv ⊢
  exact ⟨hs ▸ hv.1, hh ▸ hv.2.1, rightPadEquiv_all_false hr hv.2.2.1,
    hl ▸ hv.2.2.2.1, hl ▸ hv.2.2.2.2⟩

lemma decodeTape_of_left_eq {c1 c2 : Config} (hl : c1.left = c2.left) :
    decodeTape c1 = decodeTape c2 := by
  unfold decodeTape; rw [hl]

-- New endgame lemmas (sorry'd -- require step-by-step TM proofs)

-- Even endgame: from a=2 to valid loop start with a=N+5, b=b+2
theorem tm_even_endgame_to_loop (b N p : Nat) :
  run (P_Config_Pad b 2 N (p+2)) (3*N + 2*b + 26) = P_Config_Pad (b+2) (N+5) 0 p := by
  -- Common prefix steps 1-8: 2N+9 steps total
  -- Step 1: E(0)→F, 1, L
  have step1 : run (P_Config_Pad b 2 N (p+2)) 1 =
    { state := some ⟨5, by decide⟩, head := true, left := repeatOne 1 ++ false :: repeatOne b, right := true :: repeatOne N ++ repeatFalse (p+2) } := by
    simp [run, step, transition, P_Config_Pad]
  -- Step 2: F(1)→A, 0, R
  have step2 : run { state := some ⟨5, by decide⟩, head := true, left := repeatOne 1 ++ false :: repeatOne b, right := true :: repeatOne N ++ repeatFalse (p+2) } 1 =
    { state := some ⟨0, by decide⟩, head := true, left := false :: repeatOne 1 ++ false :: repeatOne b, right := repeatOne N ++ repeatFalse (p+2) } := by
    simp [run, step, transition]
  -- Step 3: A_shift N (N+1 steps)
  have step3 : run { state := some ⟨0, by decide⟩, head := true, left := false :: repeatOne 1 ++ false :: repeatOne b, right := repeatOne N ++ repeatFalse (p+2) } (N+1) =
    { state := some ⟨0, by decide⟩, head := false, left := repeatOne (N+1) ++ (false :: repeatOne 1 ++ false :: repeatOne b), right := repeatFalse (p+1) } := by
    have hA := A_shift N (false :: repeatOne 1 ++ false :: repeatOne b) (repeatFalse (p+2))
    have hp_head : headD' (repeatFalse (p+2)) false = false := rfl
    have hp_tail : tailD' (repeatFalse (p+2)) = repeatFalse (p+1) := rfl
    rw [hp_head, hp_tail] at hA
    exact hA
  -- Step 4: A(0)→B, 1, R
  have step4 : run { state := some ⟨0, by decide⟩, head := false, left := repeatOne (N+1) ++ (false :: repeatOne 1 ++ false :: repeatOne b), right := repeatFalse (p+1) } 1 =
    { state := some ⟨1, by decide⟩, head := false, left := true :: repeatOne (N+1) ++ (false :: repeatOne 1 ++ false :: repeatOne b), right := repeatFalse p } := by
    simp [run, step, transition]
  -- Step 5: B(0)→C, 0, L
  have step5 : run { state := some ⟨1, by decide⟩, head := false, left := true :: repeatOne (N+1) ++ (false :: repeatOne 1 ++ false :: repeatOne b), right := repeatFalse p } 1 =
    { state := some ⟨2, by decide⟩, head := true, left := repeatOne (N+1) ++ (false :: repeatOne 1 ++ false :: repeatOne b), right := false :: repeatFalse p } := by
    simp [run, step, transition]
  -- Step 6: C_shift(N+1) (N+2 steps)
  have step6 : run { state := some ⟨2, by decide⟩, head := true, left := repeatOne (N+1) ++ (false :: repeatOne 1 ++ false :: repeatOne b), right := false :: repeatFalse p } (N+2) =
    { state := some ⟨2, by decide⟩, head := false, left := repeatOne 1 ++ false :: repeatOne b, right := repeatOne (N+2) ++ false :: repeatFalse p } := by
    have hC := C_shift (N+1) (false :: repeatOne 1 ++ false :: repeatOne b) (false :: repeatFalse p)
    have hC_head : headD' (false :: repeatOne 1 ++ false :: repeatOne b) false = false := rfl
    have hC_tail : tailD' (false :: repeatOne 1 ++ false :: repeatOne b) = repeatOne 1 ++ false :: repeatOne b := rfl
    rw [hC_head, hC_tail] at hC
    exact hC
  -- Step 7: C(0)→D, 1, L
  have step7 : run { state := some ⟨2, by decide⟩, head := false, left := repeatOne 1 ++ false :: repeatOne b, right := repeatOne (N+2) ++ false :: repeatFalse p } 1 =
    { state := some ⟨3, by decide⟩, head := true, left := false :: repeatOne b, right := repeatOne (N+3) ++ false :: repeatFalse p } := by
    simp [run, step, transition]
  -- Step 8: D(1)→B, 0, L
  have step8 : run { state := some ⟨3, by decide⟩, head := true, left := false :: repeatOne b, right := repeatOne (N+3) ++ false :: repeatFalse p } 1 =
    { state := some ⟨1, by decide⟩, head := false, left := repeatOne b, right := false :: repeatOne (N+3) ++ false :: repeatFalse p } := by
    simp [run, step, transition]
  -- Now split on b
  cases b with
  | zero =>
    -- b = 0 case: 17 more steps
    -- After step 8: { B, head=false, left=[], right=false :: repeatOne(N+3) ++ false :: repeatFalse p }
    have step9 : run { state := some ⟨1, by decide⟩, head := false, left := ([] : List TapeSymbol), right := false :: repeatOne (N+3) ++ false :: repeatFalse p } 1 =
      { state := some ⟨2, by decide⟩, head := false, left := [], right := false :: false :: repeatOne (N+3) ++ false :: repeatFalse p } := by
      simp [run, step, transition]
    have step10 : run { state := some ⟨2, by decide⟩, head := false, left := ([] : List TapeSymbol), right := false :: false :: repeatOne (N+3) ++ false :: repeatFalse p } 1 =
      { state := some ⟨3, by decide⟩, head := false, left := [], right := true :: false :: false :: repeatOne (N+3) ++ false :: repeatFalse p } := by
      simp [run, step, transition]
    have step11 : run { state := some ⟨3, by decide⟩, head := false, left := ([] : List TapeSymbol), right := true :: false :: false :: repeatOne (N+3) ++ false :: repeatFalse p } 1 =
      { state := some ⟨0, by decide⟩, head := false, left := [], right := true :: true :: false :: false :: repeatOne (N+3) ++ false :: repeatFalse p } := by
      simp [run, step, transition]
    have step12 : run { state := some ⟨0, by decide⟩, head := false, left := ([] : List TapeSymbol), right := true :: true :: false :: false :: repeatOne (N+3) ++ false :: repeatFalse p } 1 =
      { state := some ⟨1, by decide⟩, head := true, left := [true], right := true :: false :: false :: repeatOne (N+3) ++ false :: repeatFalse p } := by
      simp [run, step, transition]
    have step13 : run { state := some ⟨1, by decide⟩, head := true, left := [true], right := true :: false :: false :: repeatOne (N+3) ++ false :: repeatFalse p } 1 =
      { state := some ⟨4, by decide⟩, head := true, left := [], right := true :: true :: false :: false :: repeatOne (N+3) ++ false :: repeatFalse p } := by
      simp [run, step, transition]
    -- E_shift(2): 3 steps
    have step14 : run { state := some ⟨4, by decide⟩, head := true, left := ([] : List TapeSymbol), right := true :: true :: false :: false :: repeatOne (N+3) ++ false :: repeatFalse p } 3 =
      { state := some ⟨4, by decide⟩, head := false, left := repeatOne 3, right := false :: repeatOne (N+3) ++ false :: repeatFalse p } := by
      have hE := E_shift 2 ([] : List TapeSymbol) (false :: false :: repeatOne (N+3) ++ false :: repeatFalse p)
      simp only [List.append_nil] at hE
      exact hE
    have step15 : run { state := some ⟨4, by decide⟩, head := false, left := repeatOne 3, right := false :: repeatOne (N+3) ++ false :: repeatFalse p } 1 =
      { state := some ⟨5, by decide⟩, head := true, left := repeatOne 2, right := true :: false :: repeatOne (N+3) ++ false :: repeatFalse p } := by
      simp [run, step, transition]
    have step16 : run { state := some ⟨5, by decide⟩, head := true, left := repeatOne 2, right := true :: false :: repeatOne (N+3) ++ false :: repeatFalse p } 1 =
      { state := some ⟨0, by decide⟩, head := true, left := false :: repeatOne 2, right := false :: repeatOne (N+3) ++ false :: repeatFalse p } := by
      simp [run, step, transition]
    have step17 : run { state := some ⟨0, by decide⟩, head := true, left := false :: repeatOne 2, right := false :: repeatOne (N+3) ++ false :: repeatFalse p } 1 =
      { state := some ⟨0, by decide⟩, head := false, left := true :: false :: repeatOne 2, right := repeatOne (N+3) ++ false :: repeatFalse p } := by
      simp [run, step, transition]
    have step18 : run { state := some ⟨0, by decide⟩, head := false, left := true :: false :: repeatOne 2, right := repeatOne (N+3) ++ false :: repeatFalse p } 1 =
      { state := some ⟨1, by decide⟩, head := true, left := true :: true :: false :: repeatOne 2, right := repeatOne (N+2) ++ false :: repeatFalse p } := by
      simp [run, step, transition]
    have step19 : run { state := some ⟨1, by decide⟩, head := true, left := true :: true :: false :: repeatOne 2, right := repeatOne (N+2) ++ false :: repeatFalse p } 1 =
      { state := some ⟨4, by decide⟩, head := true, left := true :: false :: repeatOne 2, right := repeatOne (N+3) ++ false :: repeatFalse p } := by
      simp [run, step, transition]
    -- E_shift(N+3): N+4 steps
    have step20 : run { state := some ⟨4, by decide⟩, head := true, left := true :: false :: repeatOne 2, right := repeatOne (N+3) ++ false :: repeatFalse p } (N+4) =
      { state := some ⟨4, by decide⟩, head := false, left := repeatOne (N+4) ++ (true :: false :: repeatOne 2), right := repeatFalse p } := by
      have hE := E_shift (N+3) (true :: false :: repeatOne 2) (false :: repeatFalse p)
      have hp_head : headD' (false :: repeatFalse p) false = false := rfl
      have hp_tail : tailD' (false :: repeatFalse p) = repeatFalse p := rfl
      rw [hp_head, hp_tail] at hE
      exact hE
    rw [show 3*N + 2*0 + 26 = 1 + (1 + (N+1 + (1 + (1 + (N+2 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (3 + (1 + (1 + (1 + (1 + (1 + (N+4)))))))))))))))))))  by omega]
    rw [run_add, step1]
    rw [run_add, step2]
    rw [run_add, step3]
    rw [run_add, step4]
    rw [run_add, step5]
    rw [run_add, step6]
    rw [run_add, step7]
    rw [run_add, step8]
    simp only [repeatOne_zero]
    rw [run_add, step9]
    rw [run_add, step10]
    rw [run_add, step11]
    rw [run_add, step12]
    rw [run_add, step13]
    rw [run_add, step14]
    rw [run_add, step15]
    rw [run_add, step16]
    rw [run_add, step17]
    rw [run_add, step18]
    rw [run_add, step19]
    rw [step20]
    have h_left : repeatOne (N+4) ++ (true :: false :: repeatOne 2) = repeatOne (N+5) ++ false :: repeatOne 2 :=
      repeatOne_append_true (N+4) (false :: repeatOne 2)
    rw [h_left]
    unfold P_Config_Pad
    simp [repeatOne_zero]
  | succ b' =>
    -- b = b'+1 case
    have step9 : run { state := some ⟨1, by decide⟩, head := false, left := repeatOne (b'+1), right := false :: repeatOne (N+3) ++ false :: repeatFalse p } 1 =
      { state := some ⟨2, by decide⟩, head := true, left := repeatOne b', right := false :: false :: repeatOne (N+3) ++ false :: repeatFalse p } := by
      simp [run, step, transition]
    -- C_shift(b'): b'+1 steps
    have step10 : run { state := some ⟨2, by decide⟩, head := true, left := repeatOne b', right := false :: false :: repeatOne (N+3) ++ false :: repeatFalse p } (b'+1) =
      { state := some ⟨2, by decide⟩, head := false, left := [], right := repeatOne (b'+1) ++ false :: false :: repeatOne (N+3) ++ false :: repeatFalse p } := by
      have hC := C_shift b' ([] : List TapeSymbol) (false :: false :: repeatOne (N+3) ++ false :: repeatFalse p)
      simp only [List.append_nil, headD'_nil, tailD'_nil] at hC
      convert hC using 2
      simp [List.append_assoc]
    have step11 : run { state := some ⟨2, by decide⟩, head := false, left := ([] : List TapeSymbol), right := repeatOne (b'+1) ++ false :: false :: repeatOne (N+3) ++ false :: repeatFalse p } 1 =
      { state := some ⟨3, by decide⟩, head := false, left := [], right := true :: repeatOne (b'+1) ++ false :: false :: repeatOne (N+3) ++ false :: repeatFalse p } := by
      simp [run, step, transition]
    have step12 : run { state := some ⟨3, by decide⟩, head := false, left := ([] : List TapeSymbol), right := true :: repeatOne (b'+1) ++ false :: false :: repeatOne (N+3) ++ false :: repeatFalse p } 1 =
      { state := some ⟨0, by decide⟩, head := false, left := [], right := true :: true :: repeatOne (b'+1) ++ false :: false :: repeatOne (N+3) ++ false :: repeatFalse p } := by
      simp [run, step, transition]
    have step13 : run { state := some ⟨0, by decide⟩, head := false, left := ([] : List TapeSymbol), right := true :: true :: repeatOne (b'+1) ++ false :: false :: repeatOne (N+3) ++ false :: repeatFalse p } 1 =
      { state := some ⟨1, by decide⟩, head := true, left := [true], right := true :: repeatOne (b'+1) ++ false :: false :: repeatOne (N+3) ++ false :: repeatFalse p } := by
      simp [run, step, transition]
    have step14 : run { state := some ⟨1, by decide⟩, head := true, left := [true], right := true :: repeatOne (b'+1) ++ false :: false :: repeatOne (N+3) ++ false :: repeatFalse p } 1 =
      { state := some ⟨4, by decide⟩, head := true, left := [], right := true :: true :: repeatOne (b'+1) ++ false :: false :: repeatOne (N+3) ++ false :: repeatFalse p } := by
      simp [run, step, transition]
    -- E_shift(b'+2): b'+3 steps
    have step15 : run { state := some ⟨4, by decide⟩, head := true, left := ([] : List TapeSymbol), right := true :: true :: repeatOne (b'+1) ++ false :: false :: repeatOne (N+3) ++ false :: repeatFalse p } (b'+4) =
      { state := some ⟨4, by decide⟩, head := false, left := repeatOne (b'+4), right := false :: repeatOne (N+3) ++ false :: repeatFalse p } := by
      have h_right_eq : (true :: true :: repeatOne (b'+1) ++ false :: false :: repeatOne (N+3) ++ false :: repeatFalse p) =
        repeatOne (b'+3) ++ (false :: false :: repeatOne (N+3) ++ false :: repeatFalse p) := by
        simp [List.append_assoc]
      rw [h_right_eq]
      have hE := E_shift (b'+3) ([] : List TapeSymbol) (false :: false :: repeatOne (N+3) ++ false :: repeatFalse p)
      simp only [List.append_nil] at hE
      exact hE
    have step16 : run { state := some ⟨4, by decide⟩, head := false, left := repeatOne (b'+4), right := false :: repeatOne (N+3) ++ false :: repeatFalse p } 1 =
      { state := some ⟨5, by decide⟩, head := true, left := repeatOne (b'+3), right := true :: false :: repeatOne (N+3) ++ false :: repeatFalse p } := by
      simp [run, step, transition]
    have step17 : run { state := some ⟨5, by decide⟩, head := true, left := repeatOne (b'+3), right := true :: false :: repeatOne (N+3) ++ false :: repeatFalse p } 1 =
      { state := some ⟨0, by decide⟩, head := true, left := false :: repeatOne (b'+3), right := false :: repeatOne (N+3) ++ false :: repeatFalse p } := by
      simp [run, step, transition]
    have step18 : run { state := some ⟨0, by decide⟩, head := true, left := false :: repeatOne (b'+3), right := false :: repeatOne (N+3) ++ false :: repeatFalse p } 1 =
      { state := some ⟨0, by decide⟩, head := false, left := true :: false :: repeatOne (b'+3), right := repeatOne (N+3) ++ false :: repeatFalse p } := by
      simp [run, step, transition]
    have step19 : run { state := some ⟨0, by decide⟩, head := false, left := true :: false :: repeatOne (b'+3), right := repeatOne (N+3) ++ false :: repeatFalse p } 1 =
      { state := some ⟨1, by decide⟩, head := true, left := true :: true :: false :: repeatOne (b'+3), right := repeatOne (N+2) ++ false :: repeatFalse p } := by
      simp [run, step, transition]
    have step20 : run { state := some ⟨1, by decide⟩, head := true, left := true :: true :: false :: repeatOne (b'+3), right := repeatOne (N+2) ++ false :: repeatFalse p } 1 =
      { state := some ⟨4, by decide⟩, head := true, left := true :: false :: repeatOne (b'+3), right := repeatOne (N+3) ++ false :: repeatFalse p } := by
      simp [run, step, transition]
    -- E_shift(N+3): N+4 steps
    have step21 : run { state := some ⟨4, by decide⟩, head := true, left := true :: false :: repeatOne (b'+3), right := repeatOne (N+3) ++ false :: repeatFalse p } (N+4) =
      { state := some ⟨4, by decide⟩, head := false, left := repeatOne (N+4) ++ (true :: false :: repeatOne (b'+3)), right := repeatFalse p } := by
      have hE := E_shift (N+3) (true :: false :: repeatOne (b'+3)) (false :: repeatFalse p)
      have hp_head : headD' (false :: repeatFalse p) false = false := rfl
      have hp_tail : tailD' (false :: repeatFalse p) = repeatFalse p := rfl
      rw [hp_head, hp_tail] at hE
      exact hE
    rw [show 3*N + 2*(b'+1) + 26 = 1 + (1 + (N+1 + (1 + (1 + (N+2 + (1 + (1 + (1 + (b'+1 + (1 + (1 + (1 + (1 + (b'+4 + (1 + (1 + (1 + (1 + (1 + (N+4))))))))))))))))))))  by omega]
    rw [run_add, step1]
    rw [run_add, step2]
    rw [run_add, step3]
    rw [run_add, step4]
    rw [run_add, step5]
    rw [run_add, step6]
    rw [run_add, step7]
    rw [run_add, step8]
    rw [run_add, step9]
    rw [run_add, step10]
    rw [run_add, step11]
    rw [run_add, step12]
    rw [run_add, step13]
    rw [run_add, step14]
    rw [run_add, step15]
    rw [run_add, step16]
    rw [run_add, step17]
    rw [run_add, step18]
    rw [run_add, step19]
    rw [run_add, step20]
    rw [step21]
    have h_left : repeatOne (N+4) ++ (true :: false :: repeatOne (b'+3)) = repeatOne (N+5) ++ false :: repeatOne (b'+3) :=
      repeatOne_append_true (N+4) (false :: repeatOne (b'+3))
    rw [h_left]
    have h_b : b'+3 = b'+1+2 := by omega
    rw [h_b]
    unfold P_Config_Pad
    simp [repeatOne_zero]

-- Odd halt endgame: from a=3, b=0, the machine halts
theorem tm_odd_halt_endgame (N p : Nat) :
  (run (P_Config_Pad 0 3 N (p+2)) (2*N + 12)).state = none := by
  -- Step 1: E(0) reading false → (F=state5, 1, L)
  -- Starting config: P_Config_Pad 0 3 N (p+2) = { state=4, head=false, left=repeatOne 3 ++ [false], right=repeatOne N ++ repeatFalse(p+2) }
  -- transition(4, false) = (5, true, L): write true, move left
  -- new head = headD'(repeatOne 3 ++ [false]) = true, new left = tailD'(repeatOne 3 ++ [false]) = repeatOne 2 ++ [false]
  -- new right = true :: repeatOne N ++ repeatFalse(p+2)
  have step1 : run (P_Config_Pad 0 3 N (p+2)) 1 =
    { state := some ⟨5, by decide⟩, head := true, left := repeatOne 2 ++ [false], right := true :: repeatOne N ++ repeatFalse (p+2) } := by
    simp [run, step, transition, P_Config_Pad]
  -- Step 2: F(1) reading true → (A=state0, 0, R)
  -- transition(5, true) = (0, false, R): write false, move right
  -- new head = headD'(right) = headD'(repeatOne N ++ repeatFalse(p+2))
  -- For N=0: head = false; for N>0: head = true. Either way, new head = true (since right = true :: ...)
  -- Actually right = true :: repeatOne N ++ repeatFalse(p+2), so headD'(right) = true... wait
  -- The right tape in step1 result is `true :: repeatOne N ++ repeatFalse(p+2)`
  -- So tailD'(right) = repeatOne N ++ repeatFalse(p+2), headD'(right) = true
  -- Hmm, but transition(5, true) = (0, false, R), so we move right:
  -- new left = false :: (repeatOne 2 ++ [false])
  -- new head = headD'(true :: repeatOne N ++ repeatFalse(p+2)) = true
  -- new right = tailD'(true :: repeatOne N ++ repeatFalse(p+2)) = repeatOne N ++ repeatFalse(p+2)
  have step2 : run { state := some ⟨5, by decide⟩, head := true, left := repeatOne 2 ++ [false], right := true :: repeatOne N ++ repeatFalse (p+2) } 1 =
    { state := some ⟨0, by decide⟩, head := true, left := false :: (repeatOne 2 ++ [false]), right := repeatOne N ++ repeatFalse (p+2) } := by
    simp [run, step, transition]
  -- Step 3: A_shift N (N+1 steps)
  -- A_shift: run { state=0, head=true, left=L, right=repeatOne N ++ R } (N+1) = { state=0, head=headD' R false, left=repeatOne(N+1) ++ L, right=tailD' R }
  -- L = false :: (repeatOne 2 ++ [false]), R = repeatFalse(p+2)
  -- headD'(repeatFalse(p+2)) = false, tailD'(repeatFalse(p+2)) = repeatFalse(p+1)
  have step3 : run { state := some ⟨0, by decide⟩, head := true, left := false :: (repeatOne 2 ++ [false]), right := repeatOne N ++ repeatFalse (p+2) } (N+1) =
    { state := some ⟨0, by decide⟩, head := false, left := repeatOne (N+1) ++ (false :: (repeatOne 2 ++ [false])), right := repeatFalse (p+1) } := by
    have hA := A_shift N (false :: (repeatOne 2 ++ [false])) (repeatFalse (p+2))
    have hp_head : headD' (repeatFalse (p+2)) false = false := rfl
    have hp_tail : tailD' (repeatFalse (p+2)) = repeatFalse (p+1) := rfl
    rw [hp_head, hp_tail] at hA
    exact hA
  -- Step 4: A(0) → (B=state1, 1, R)
  -- transition(0, false) = (1, true, R): write true, move right
  -- new left = true :: (repeatOne(N+1) ++ (false :: (repeatOne 2 ++ [false])))
  -- new head = headD'(repeatFalse(p+1)) = false
  -- new right = tailD'(repeatFalse(p+1)) = repeatFalse p
  have step4 : run { state := some ⟨0, by decide⟩, head := false, left := repeatOne (N+1) ++ (false :: (repeatOne 2 ++ [false])), right := repeatFalse (p+1) } 1 =
    { state := some ⟨1, by decide⟩, head := false, left := true :: repeatOne (N+1) ++ (false :: (repeatOne 2 ++ [false])), right := repeatFalse p } := by
    simp [run, step, transition]
  -- Step 5: B(0) → (C=state2, 0, L)
  -- transition(1, false) = (2, false, L): write false, move left
  -- new head = headD'(true :: repeatOne(N+1) ++ ...) = true
  -- new left = tailD'(true :: repeatOne(N+1) ++ ...) = repeatOne(N+1) ++ (false :: (repeatOne 2 ++ [false]))
  -- new right = false :: repeatFalse p
  have step5 : run { state := some ⟨1, by decide⟩, head := false, left := true :: repeatOne (N+1) ++ (false :: (repeatOne 2 ++ [false])), right := repeatFalse p } 1 =
    { state := some ⟨2, by decide⟩, head := true, left := repeatOne (N+1) ++ (false :: (repeatOne 2 ++ [false])), right := false :: repeatFalse p } := by
    simp [run, step, transition]
  -- Step 6: C_shift (N+1) → N+2 steps
  -- C_shift: run { state=2, head=true, left=repeatOne(N+1) ++ L, right=R } (N+2) = { state=2, head=headD' L false, left=tailD' L, right=repeatOne(N+2) ++ R }
  -- L = false :: (repeatOne 2 ++ [false]), R = false :: repeatFalse p
  -- headD'(false :: ...) = false, tailD'(false :: ...) = repeatOne 2 ++ [false]
  have step6 : run { state := some ⟨2, by decide⟩, head := true, left := repeatOne (N+1) ++ (false :: (repeatOne 2 ++ [false])), right := false :: repeatFalse p } (N+2) =
    { state := some ⟨2, by decide⟩, head := false, left := repeatOne 2 ++ [false], right := repeatOne (N+2) ++ false :: repeatFalse p } := by
    have hC := C_shift (N+1) (false :: (repeatOne 2 ++ [false])) (false :: repeatFalse p)
    have hC_head : headD' (false :: (repeatOne 2 ++ [false])) false = false := rfl
    have hC_tail : tailD' (false :: (repeatOne 2 ++ [false])) = repeatOne 2 ++ [false] := rfl
    rw [hC_head, hC_tail] at hC
    exact hC
  -- Step 7: C(0) → (D=state3, 1, L)
  -- transition(2, false) = (3, true, L): write true, move left
  -- left = repeatOne 2 ++ [false] = [true, true, false]
  -- new head = headD'([true, true, false]) = true
  -- new left = tailD'([true, true, false]) = [true, false]
  -- new right = true :: (repeatOne(N+2) ++ false :: repeatFalse p) = repeatOne(N+3) ++ false :: repeatFalse p
  have step7 : run { state := some ⟨2, by decide⟩, head := false, left := repeatOne 2 ++ [false], right := repeatOne (N+2) ++ false :: repeatFalse p } 1 =
    { state := some ⟨3, by decide⟩, head := true, left := [true, false], right := repeatOne (N+3) ++ false :: repeatFalse p } := by
    simp [run, step, transition]
  -- Step 8: D(1) → (B=state1, 0, L)
  -- transition(3, true) = (1, false, L): write false, move left
  -- left = [true, false]
  -- new head = headD'([true, false]) = true
  -- new left = tailD'([true, false]) = [false]
  -- new right = false :: (repeatOne(N+3) ++ false :: repeatFalse p)
  have step8 : run { state := some ⟨3, by decide⟩, head := true, left := [true, false], right := repeatOne (N+3) ++ false :: repeatFalse p } 1 =
    { state := some ⟨1, by decide⟩, head := true, left := [false], right := false :: repeatOne (N+3) ++ false :: repeatFalse p } := by
    simp [run, step, transition]
  -- Step 9: B(1) → (E=state4, 1, L)
  -- transition(1, true) = (4, true, L): write true, move left
  -- left = [false]
  -- new head = headD'([false]) = false
  -- new left = tailD'([false]) = []
  -- new right = true :: false :: repeatOne(N+3) ++ false :: repeatFalse p
  have step9 : run { state := some ⟨1, by decide⟩, head := true, left := [false], right := false :: repeatOne (N+3) ++ false :: repeatFalse p } 1 =
    { state := some ⟨4, by decide⟩, head := false, left := [], right := true :: false :: repeatOne (N+3) ++ false :: repeatFalse p } := by
    simp [run, step, transition]
  -- Step 10: E(0) → (F=state5, 1, L)
  -- transition(4, false) = (5, true, L): write true, move left
  -- left = []
  -- new head = headD'([]) = false
  -- new left = []
  -- new right = true :: true :: false :: repeatOne(N+3) ++ false :: repeatFalse p
  have step10 : run { state := some ⟨4, by decide⟩, head := false, left := [], right := true :: false :: repeatOne (N+3) ++ false :: repeatFalse p } 1 =
    { state := some ⟨5, by decide⟩, head := false, left := [], right := true :: true :: false :: repeatOne (N+3) ++ false :: repeatFalse p } := by
    simp [run, step, transition]
  -- Chain all steps: 1 + 1 + (N+1) + 1 + 1 + (N+2) + 1 + 1 + 1 + 1 + 1 = 2N+12
  rw [show 2*N + 12 = 1 + (1 + ((N+1) + (1 + (1 + ((N+2) + (1 + (1 + (1 + (1 + 1))))))))) by omega]
  rw [run_add, step1]
  rw [run_add, step2]
  rw [run_add, step3]
  rw [run_add, step4]
  rw [run_add, step5]
  rw [run_add, step6]
  rw [run_add, step7]
  rw [run_add, step8]
  rw [run_add, step9]
  rw [run_add, step10]
  -- Step 11: F(0) → HALT. transition(5, false) = (none, false, R)
  -- The state is now some 5 (F) with head false, so it halts
  simp [run, step, transition]

-- Helper lemmas for tm_simulates_math

-- Even case: the TM reaches a valid loop start with the correct decoded state
theorem tm_even_full (b n p : Nat) :
  ∃ k, k > 0 ∧ isValidLoopStart (run (P_Config_Pad b (2*n+2) 0 p) k) ∧
    decodeTape (run (P_Config_Pad b (2*n+2) 0 p) k) = { a := 3 * n + 5, b := b + 2 } := by
  -- Step 1: Define padded config with enough padding
  set p' := p + n + 2
  set k := n * (3 * n + 9) + (9 * n + 2 * b + 26)
  -- Step 2: Show padded run gives P_Config_Pad (b+2) (3*n+5) 0 p via tm_P_multistep + even endgame
  have h_multi : run (P_Config_Pad b (2*n+2) 0 p') (n * (3*n+9))
      = P_Config_Pad b 2 (3*n) (p+2) := by
    have h := tm_P_multistep b 0 0 (p+1) n
    simp only [show 0 + 2 + 2 * n = 2 * n + 2 from by omega, show p + 1 + 1 + n = p' from by omega,
      show (0:ℕ) + 3 * n = 3 * n from by omega, show p + 1 + 1 = p + 2 from by omega] at h; exact h
  have h_end : run (P_Config_Pad b 2 (3*n) (p+2)) (9*n + 2*b + 26)
      = P_Config_Pad (b+2) (3*n+5) 0 p := by
    have h := tm_even_endgame_to_loop b (3*n) p; ring_nf at h ⊢; exact h
  have h_padded : run (P_Config_Pad b (2*n+2) 0 p') k
      = P_Config_Pad (b+2) (3*n+5) 0 p := by
    show run (P_Config_Pad b (2*n+2) 0 p') (n*(3*n+9) + (9*n+2*b+26)) = _
    rw [run_add, h_multi, h_end]
  -- Step 3: Transfer via padding independence
  have h_equiv : RightPadEquiv (P_Config_Pad b (2*n+2) 0 p).right
      (P_Config_Pad b (2*n+2) 0 p').right := by
    simp only [P_Config_Pad]; exact rightPadEquiv_append_repeatFalse (repeatOne 0) p p'
  have h_run := run_rightPadEquiv
    (P_Config_Pad b (2*n+2) 0 p) (P_Config_Pad b (2*n+2) 0 p') k rfl rfl rfl h_equiv
  rw [h_padded] at h_run
  -- Step 4: Extract isValidLoopStart and decodeTape
  use k
  refine ⟨by omega, ?_, ?_⟩
  · exact isValidLoopStart_of_rightPadEquiv h_run.1 h_run.2.1 h_run.2.2.1 h_run.2.2.2
      (isValidLoopStart_P_Config_Pad (b+2) (3*n+5) p (by omega))
  · rw [decodeTape_of_left_eq h_run.2.1]; simp

-- Odd halt case: the TM halts
theorem tm_odd_halt_ex (n p : Nat) :
  ∃ k, k > 0 ∧ (run (P_Config_Pad 0 (2*n+3) 0 p) k).state = none := by
  set p' := p + n + 2
  set k := n * (3 * n + 9) + (6 * n + 12)
  -- Padded multistep
  have h_multi : run (P_Config_Pad 0 (2*n+3) 0 p') (n * (3*n+9))
      = P_Config_Pad 0 3 (3*n) (p+2) := by
    have h := tm_P_multistep 0 1 0 (p+1) n
    simp only [show 1 + 2 + 2 * n = 2 * n + 3 from by omega, show p + 1 + 1 + n = p' from by omega,
      show 1 + 2 = 3 from by omega, show (0:ℕ) + 3 * n = 3 * n from by omega,
      show p + 1 + 1 = p + 2 from by omega] at h; exact h
  -- Odd halt endgame
  have h_end : (run (P_Config_Pad 0 3 (3*n) (p+2)) (6*n+12)).state = none := by
    have h := tm_odd_halt_endgame (3*n) p; ring_nf at h ⊢; exact h
  -- Combine
  have h_padded : (run (P_Config_Pad 0 (2*n+3) 0 p') k).state = none := by
    show (run (P_Config_Pad 0 (2*n+3) 0 p') (n*(3*n+9) + (6*n+12))).state = none
    rw [run_add, h_multi]; exact h_end
  -- Transfer via padding independence
  have h_equiv : RightPadEquiv (P_Config_Pad 0 (2*n+3) 0 p).right
      (P_Config_Pad 0 (2*n+3) 0 p').right := by
    simp only [P_Config_Pad]; exact rightPadEquiv_append_repeatFalse (repeatOne 0) p p'
  have h_run := run_rightPadEquiv
    (P_Config_Pad 0 (2*n+3) 0 p) (P_Config_Pad 0 (2*n+3) 0 p') k rfl rfl rfl h_equiv
  exact ⟨k, by omega, h_run.1.symm ▸ h_padded⟩

-- Odd continue case: the TM reaches a valid loop start with the correct decoded state
theorem tm_odd_continue (b' n p : Nat) :
  ∃ k, k > 0 ∧ isValidLoopStart (run (P_Config_Pad (b'+1) (2*n+3) 0 p) k) ∧
    decodeTape (run (P_Config_Pad (b'+1) (2*n+3) 0 p) k) = { a := 3 * n + 6, b := b' } := by
  set p' := p + n + 2
  set k := n * (3 * n + 9) + (9 * n + 20)
  -- Padded multistep: reduce a from 2*n+3 to 3, accumulating 3*n ones on right
  have h_multi : run (P_Config_Pad (b'+1) (2*n+3) 0 p') (n * (3*n+9))
      = P_Config_Pad (b'+1) 3 (3*n) (p+2) := by
    have h := tm_P_multistep (b'+1) 1 0 (p+1) n
    simp only [show 1 + 2 + 2 * n = 2 * n + 3 from by omega, show p + 1 + 1 + n = p' from by omega,
      show 1 + 2 = 3 from by omega, show (0:ℕ) + 3 * n = 3 * n from by omega,
      show p + 1 + 1 = p + 2 from by omega] at h; exact h
  -- Odd endgame: P_Config_Pad (b'+1) 3 (3*n) (p+2) → P_Config_Pad b' (3*n+6) 0 p
  have h_end : run (P_Config_Pad (b'+1) 3 (3*n) (p+2)) (9*n+20)
      = P_Config_Pad b' (3*n+6) 0 p := by
    have h := tm_odd_endgame b' (3*n) p; ring_nf at h ⊢; exact h
  -- Combine
  have h_padded : run (P_Config_Pad (b'+1) (2*n+3) 0 p') k
      = P_Config_Pad b' (3*n+6) 0 p := by
    show run (P_Config_Pad (b'+1) (2*n+3) 0 p') (n*(3*n+9) + (9*n+20)) = _
    rw [run_add, h_multi, h_end]
  -- Transfer via padding independence
  have h_equiv : RightPadEquiv (P_Config_Pad (b'+1) (2*n+3) 0 p).right
      (P_Config_Pad (b'+1) (2*n+3) 0 p').right := by
    simp only [P_Config_Pad]; exact rightPadEquiv_append_repeatFalse (repeatOne 0) p p'
  have h_run := run_rightPadEquiv
    (P_Config_Pad (b'+1) (2*n+3) 0 p) (P_Config_Pad (b'+1) (2*n+3) 0 p') k rfl rfl rfl h_equiv
  rw [h_padded] at h_run
  use k
  refine ⟨by omega, ?_, ?_⟩
  · exact isValidLoopStart_of_rightPadEquiv h_run.1 h_run.2.1 h_run.2.2.1 h_run.2.2.2
      (isValidLoopStart_P_Config_Pad b' (3*n+6) p (by omega))
  · rw [decodeTape_of_left_eq h_run.2.1]; simp

-- C. The Block-Step Lemma (The Core Theorem)
theorem tm_simulates_math (c : Config) (hm : isValidLoopStart c) :
  ∃ (k : Nat), k > 0 ∧ (
    let c' := run c k
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

lemma run_none_state (c : Config) (h : c.state = none) (k : Nat) :
  (run c k).state = none := by
  induction k with
  | zero => exact h
  | succ k ih =>
    have hs : run c (k+1) = run (run c k) 1 := by rw [run_add]
    rw [hs]
    change (step (run c k)).state = none
    unfold step
    simp [ih]

-- D. The Halting Equivalence Theorem
-- We define a simple inductive predicate for reaching none
inductive mathHalts : MathState → Prop where
| haltStep (m : MathState) (h : nextMathState m = none) : mathHalts m
| nextStep (m m' : MathState) (h : nextMathState m = some m') (h' : mathHalts m') : mathHalts m

theorem tm_halt_iff_math_condition (c : Config) (hm : isValidLoopStart c) :
  (∃ k, (run c k).state = none) ↔ mathHalts (decodeTape c) := by
  constructor
  · intro ⟨k, hk⟩
    induction k using Nat.strong_induction_on generalizing c with
    | h n ih =>
      have ⟨k_sim, hk_sim_pos, h_sim⟩ := tm_simulates_math c hm
      cases h_next : nextMathState (decodeTape c) with
      | none =>
        exact mathHalts.haltStep _ h_next
      | some m' =>
        have h_rewrite : match nextMathState (decodeTape c) with | some m' => isValidLoopStart (run c k_sim) ∧ decodeTape (run c k_sim) = m' | none => (run c k_sim).state = none = (isValidLoopStart (run c k_sim) ∧ decodeTape (run c k_sim) = m') := by rw [h_next]
        rw [h_rewrite] at h_sim
        have ⟨hm_c', hd_c'⟩ := h_sim
        by_cases h_lt : n < k_sim
        · exfalso
          have hc'_state : (run c k_sim).state = some ⟨4, by decide⟩ := hm_c'.1
          have hc'_none : (run c k_sim).state = none := by
            have h_add : k_sim = n + (k_sim - n) := by omega
            change (run c k_sim).state = none
            rw [h_add, run_add]
            exact run_none_state _ hk _
          rw [hc'_none] at hc'_state
          contradiction
        · have h_ge : n ≥ k_sim := by omega
          let n' := n - k_sim
          have hk_n' : (run (run c k_sim) n').state = none := by
             have h_run_add : run (run c k_sim) n' = run c (k_sim + n') := by rw [run_add]
             rw [h_run_add]
             have h_ns : k_sim + n' = n := Nat.add_sub_of_le h_ge
             rw [h_ns]
             exact hk
          have h_math' := ih n' (by omega) (run c k_sim) hm_c' hk_n'
          rw [hd_c'] at h_math'
          exact mathHalts.nextStep _ _ h_next h_math'
  · intro h_math
    generalize hd : decodeTape c = m at h_math
    induction h_math generalizing c with
    | haltStep m h_none =>
      have ⟨k, hk_pos, hk⟩ := tm_simulates_math c hm
      have h_rewrite : match nextMathState (decodeTape c) with | some m' => isValidLoopStart (run c k) ∧ decodeTape (run c k) = m' | none => (run c k).state = none = ((run c k).state = none) := by
        rw [hd, h_none]
      rw [h_rewrite] at hk
      exact ⟨k, hk⟩
    | nextStep m m' h_some h_halt ih =>
      have ⟨k, hk_pos, hk⟩ := tm_simulates_math c hm
      have h_rewrite : match nextMathState (decodeTape c) with | some m' => isValidLoopStart (run c k) ∧ decodeTape (run c k) = m' | none => (run c k).state = none = (isValidLoopStart (run c k) ∧ decodeTape (run c k) = m') := by
        rw [hd, h_some]
      rw [h_rewrite] at hk
      rcases hk with ⟨hm_c', hd_c'⟩
      have ⟨k', hk'⟩ := ih (run c k) hm_c' hd_c'
      use k + k'
      rw [run_add]
      exact hk'

-- Initial configuration: TM starts on blank tape in state A
def initConfig : Config := { state := some ⟨0, by decide⟩, head := false, left := [], right := [] }

-- Initial loop state: the TM reaches its first valid loop start at step 58
-- with tape encoding (a=8, b=3), i.e. P_Config_Pad 3 8 0 0.
lemma antihydra_init_loop_start : run initConfig 58 = P_Config_Pad 2 8 0 0 := by
  rfl

-- Consequently the iteration of nextMathState starts at {a=8, b=2}
lemma antihydra_init_math_state : decodeTape (run initConfig 58) = { a := 8, b := 2 } := by
  decide

-- i-th iterate of A
def Aiter (i : ℕ) (ab : ℕ × ℕ) : ℕ × ℕ := A^[i] ab

-- Helper 1: P_Config_Pad 2 8 0 0 is a valid loop start
private lemma isValidLoopStart_P248 : isValidLoopStart (P_Config_Pad 2 8 0 0) :=
  isValidLoopStart_P_Config_Pad 2 8 0 (by omega)

-- Helper 2: initConfig doesn't halt in first 58 steps
private lemma no_halt_before_58 : ∀ k < 58, (run initConfig k).state ≠ none := by
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
    (∃ k, (run initConfig k).state = none) ↔
    ∃ i, (Aiter i (8, 2)).1 % 2 = 1 ∧ (Aiter i (8, 2)).1 / 2 ≥ 1 ∧ (Aiter i (8, 2)).2 = 0 := by
  have hv : isValidLoopStart (run initConfig 58) :=
    antihydra_init_loop_start ▸ isValidLoopStart_P248
  have step1 : (∃ k, (run initConfig k).state = none) ↔
               (∃ k, (run (run initConfig 58) k).state = none) := by
    constructor
    · rintro ⟨k, hk⟩
      by_cases h : 58 ≤ k
      · refine ⟨k - 58, ?_⟩
        have heq : run initConfig (58 + (k - 58)) = run (run initConfig 58) (k - 58) := run_add _ _ _
        rw [Nat.add_sub_cancel' h] at heq
        rw [← heq]; exact hk
      · exact absurd hk (no_halt_before_58 k (by omega))
    · rintro ⟨k, hk⟩
      exact ⟨58 + k, show (run initConfig (58 + k)).state = none by rw [run_add]; exact hk⟩
  rw [step1, tm_halt_iff_math_condition _ hv, antihydra_init_math_state]
  exact mathHalts_iff_Aiter_8_2
