import BusyLean
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open BusyLean

namespace Cryptid

/-!
# BB(6) Cryptid: 1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC

A potential BB(6) Cryptid found by @mxdys on 18 Aug 2024.

## Transition Table

       0     1
  A   1RB   0RB
  B   1LC   1RE
  C   1LF   0LD
  D   1RA   1LD
  E   1RC   1RB
  F   ---   1LC

## Macro Configurations

  P(a)   := 0^∞ 1^a 011 <D 0^∞    (state D reading rightmost 1 of "011")
  Q(a,b) := 0^∞ 1^(2a+1) <D 0 1^b 0^∞

## Map Rules

  P(2a)     → P(3a+4)
  P(2a+1)   → Q(a+2, 1)
  Q(0, b)   → halt
  Q(1, 2b)  → Q(b+2, 1)
  Q(1, 2b+1)→ P(3b+8)
  Q(2a+2, b)→ Q(a, b+2a+5)
  Q(2a+3, b)→ P(b+5a+6)
-/

-- The Cryptid TM
def cryptid : TM 6 := tm! "1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC"

-- Macro-level configurations
-- P(a): state D, head = 1, left = [1,0] ++ 1^a, right = 0^p
def P_Config (a : Nat) (p : Nat) : Config 6 :=
  { state := some stD,
    head := true,
    left := [true, false] ++ ones a,
    right := zeros p }

-- Q(a,b): state D, head = 1, left = 1^(2a), right = [0] ++ 1^b ++ 0^p
def Q_Config (a b : Nat) (p : Nat) : Config 6 :=
  { state := some stD,
    head := true,
    left := ones (2 * a),
    right := [false] ++ ones b ++ zeros p }

-- Mathematical model
inductive MachineState where
  | P : Nat → MachineState
  | Q : Nat → Nat → MachineState
  | Halt : MachineState
deriving Repr, DecidableEq

def nextMachineState : MachineState → MachineState
  | .Halt => .Halt
  | .P a =>
    if a % 2 == 0 then .P (3 * (a / 2) + 4)
    else .Q (a / 2 + 2) 1
  | .Q a b =>
    match a with
    | 0 => .Halt
    | 1 => if b % 2 == 0 then .Q (b / 2 + 2) 1
           else .P (3 * (b / 2) + 8)
    | a + 2 =>
      if a % 2 == 0 then .Q (a / 2) (b + a + 5)
      else .P (b + 5 * ((a - 1) / 2) + 6)

def iterMachineState (s : MachineState) : Nat → MachineState
  | 0 => s
  | n + 1 => iterMachineState (nextMachineState s) n

-- Shift lemmas

/-- D scans left through k ones: D reads 1, writes 1, moves L, stays D. -/
lemma D_shift (k : Nat) (L R : List Sym) :
    run cryptid { state := some stD, head := true, left := ones k ++ L, right := R } k =
    { state := some stD, head := true, left := L, right := ones k ++ R } := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih => tm_ind_zero ih stD [cryptid]

/-- EB alternating scan: E reads 1→1RB, B reads 1→1RE. After 2k steps,
    2k ones moved from right to left, state returns to E. -/
lemma EB_shift (k : Nat) (L R : List Sym) :
    run cryptid { state := some stE, head := true, left := L, right := ones (2 * k) ++ R } (2 * k) =
    { state := some stE, head := true, left := ones (2 * k) ++ L, right := R } := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    simp only [show 2 * (k + 1) = (2 * k + 1) + 1 from by omega, ones_succ, List.cons_append]
    conv => lhs; rw [show (2 * k + 1) + 1 = 2 + 2 * k from by omega, run_add]
    conv => lhs; enter [2]; dsimp [run, step, cryptid, listHead, listTail, List.cons_append,
      ones_succ, ones_zero, List.nil_append]
    conv => lhs; enter [2, 1]; change some stE
    rw [ih (true :: true :: L)]
    simp only [ones_true_cons, ones_cons_append]

-- Q(0, b) → halt
lemma tm_Q_halt (b : Nat) (p : Nat) :
    (run cryptid (Q_Config 0 b p) 8).state = none := by
  simp [run, step, cryptid, Q_Config, ones, zeros, repeatSym]

-- Macro simp for single steps
scoped macro "cr_simp" : tactic =>
  `(tactic| simp (config := { decide := true }) [run, step, cryptid, P_Config, Q_Config, ones, zeros,
    repeatSym, listHead, listTail, List.cons_append, List.nil_append, List.append_nil])

-- Transition lemmas: evaluate cryptid.tr without unfolding cryptid itself.
-- This prevents `simp [cryptid]` from expanding the TM definition globally.
@[simp] private theorem cr_A0 : cryptid.tr stA false = some (stB, true, Dir.R) := rfl
@[simp] private theorem cr_A1 : cryptid.tr stA true = some (stB, false, Dir.R) := rfl
@[simp] private theorem cr_B0 : cryptid.tr stB false = some (stC, true, Dir.L) := rfl
@[simp] private theorem cr_B1 : cryptid.tr stB true = some (stE, true, Dir.R) := rfl
@[simp] private theorem cr_C0 : cryptid.tr stC false = some (stF, true, Dir.L) := rfl
@[simp] private theorem cr_C1 : cryptid.tr stC true = some (stD, false, Dir.L) := rfl
@[simp] private theorem cr_D0 : cryptid.tr stD false = some (stA, true, Dir.R) := rfl
@[simp] private theorem cr_D1 : cryptid.tr stD true = some (stD, true, Dir.L) := rfl
@[simp] private theorem cr_E0 : cryptid.tr stE false = some (stC, true, Dir.R) := rfl
@[simp] private theorem cr_E1 : cryptid.tr stE true = some (stB, true, Dir.R) := rfl
@[simp] private theorem cr_F0 : cryptid.tr stF false = none := rfl
@[simp] private theorem cr_F1 : cryptid.tr stF true = some (stC, true, Dir.L) := rfl

-- Standard simp set for reducing concrete TM steps without unfolding `cryptid`
scoped macro "cr_steps" : tactic =>
  `(tactic| simp only [run, step, cr_A0, cr_A1, cr_B0, cr_B1, cr_C0, cr_C1, cr_D0, cr_D1,
    cr_E0, cr_E1, cr_F0, cr_F1, ones_succ, ones_zero, zeros_succ, zeros_zero,
    listHead_cons, listTail_cons, listHead_nil, listTail_nil, listHead_zeros, listTail_zeros,
    listHead_ones, listTail_ones, listHead_ones_succ, listTail_ones_succ,
    List.cons_append, List.nil_append, List.append_nil,
    ones_true_cons, zeros_false_cons])

-- Conv version of cr_steps for use inside `conv` blocks
scoped macro "cr_steps_c" : conv =>
  `(conv| simp only [run, step, cr_A0, cr_A1, cr_B0, cr_B1, cr_C0, cr_C1, cr_D0, cr_D1,
    cr_E0, cr_E1, cr_F0, cr_F1, ones_succ, ones_zero, zeros_succ, zeros_zero,
    listHead_cons, listTail_cons, listHead_nil, listTail_nil, listHead_zeros, listTail_zeros,
    listHead_ones, listTail_ones, listHead_ones_succ, listTail_ones_succ,
    List.cons_append, List.nil_append, List.append_nil,
    ones_true_cons, zeros_false_cons])

-- Single-step evaluation macro (no `run`, no `ones_succ` — for symbolic tapes)
scoped macro "cr_step1" : tactic =>
  `(tactic| simp only [step, cr_A0, cr_A1, cr_B0, cr_B1, cr_C0, cr_C1, cr_D0, cr_D1,
    cr_E0, cr_E1, cr_F0, cr_F1,
    listHead_cons, listTail_cons, listHead_nil, listTail_nil,
    List.cons_append, List.nil_append, List.append_nil])

-- P(2k+1) → Q(k+2, 1) in 15 steps
lemma tm_P_odd (k : Nat) (p : Nat) :
    ∃ padding,
      run cryptid (P_Config (2 * k + 1) p) 15 = Q_Config (k + 2) 1 padding := by
  refine ⟨p - 3, ?_⟩
  simp only [P_Config]
  -- D_shift(1): move 1 one from left to right
  rw [show (15 : Nat) = 1 + 14 from rfl, run_add,
      show ([true, false] ++ ones (2 * k + 1) : List Sym) =
        ones 1 ++ ([false] ++ ones (2 * k + 1)) from by simp [ones], D_shift]
  -- 14 concrete boundary steps
  cr_steps
  simp only [Q_Config, ← ones_succ, show p - 1 - 1 - 1 = p - 3 from by omega]
  congr 1

-- Q(1, 2b) → Q(b+2, 1) in 2b+24 steps
lemma tm_Q_one_even (b : Nat) (p : Nat) :
    ∃ padding,
      run cryptid (Q_Config 1 (2 * b) p) (2 * b + 24) = Q_Config (b + 2) 1 padding := by
  refine ⟨p - 1, ?_⟩
  simp only [Q_Config]
  -- Phase 1: D_shift 2
  rw [show 2 * b + 24 = 2 + (2 * b + 22) from by omega, run_add,
      show ones (2 * 1) = ones 2 ++ [] from by simp [ones], D_shift]
  -- Phase 2: 17 concrete steps + EB_shift + 3 final steps
  rw [show 2 * b + 22 = 17 + (2 * b + 5) from by omega, run_add]
  tm_exec [cryptid]
  -- EB_shift b
  conv => lhs; enter [2, 1]; change some stE
  rw [run_add, EB_shift b _ (zeros p)]
  -- 3 final concrete steps + cleanup
  cr_steps
  simp only [← ones_succ]; congr 1

-- ============================================================
-- Helper lemmas for complex macro rules
-- ============================================================

-- Intermediate configs use anonymous constructor syntax: (⟨st, left, head, right⟩ : Config 6)
-- to avoid multi-line struct literal parsing issues with `head` field name.

/-- Right scan cycle: 7 steps, moves one "one" from right to left accumulator. -/
lemma right_scan_cycle (k m p : Nat) : run cryptid
    (⟨some stD, [true, false] ++ ones k, true, [false] ++ ones (m + 1) ++ zeros p⟩ : Config 6) 7 =
    ⟨some stD, [true, false] ++ ones (k + 1), true, [false] ++ ones m ++ zeros p⟩ := by
  show run cryptid { state := some stD, head := true, left := [true, false] ++ ones k, right := [false] ++ ones (m + 1) ++ zeros p } 7 = { state := some stD, head := true, left := [true, false] ++ ones (k + 1), right := [false] ++ ones m ++ zeros p }
  rw [show (7 : Nat) = 1 + 6 from rfl, run_add,
      show ([true, false] ++ ones k : List Sym) = ones 1 ++ ([false] ++ ones k) from by simp [ones],
      D_shift]
  simp only [run, step, cr_A1, cr_D0, cr_D1, listHead_cons, listTail_cons,
    List.cons_append, List.nil_append, ← ones_succ]
  rfl

/-- Right scan: iterate right_scan_cycle to reach P_Config. -/
lemma right_scan (k m p : Nat) : ∃ steps, run cryptid
    (⟨some stD, [true, false] ++ ones k, true, [false] ++ ones m ++ zeros p⟩ : Config 6) steps =
    P_Config (k + m) (p + 1) := by
  induction m generalizing k with
  | zero =>
    refine ⟨0, ?_⟩; simp [run, P_Config]
  | succ m ih =>
    obtain ⟨rest, hrest⟩ := ih (k + 1)
    exact ⟨7 + rest, by rw [run_add, right_scan_cycle]; convert hrest using 2; omega⟩

/-- m1_to_scan: 7 steps from M=1 form to right-scan form. -/
lemma m1_to_scan (B p : Nat) : run cryptid
    (⟨some stD, ones 1, true, [false] ++ ones (B + 1) ++ zeros p⟩ : Config 6) 7 =
    ⟨some stD, [true, false] ++ ones 1, true, [false] ++ ones B ++ zeros p⟩ := by
  show run cryptid { state := some stD, head := true, left := ones 1, right := [false] ++ ones (B + 1) ++ zeros p } 7 = { state := some stD, head := true, left := [true, false] ++ ones 1, right := [false] ++ ones B ++ zeros p }
  rw [show (7 : Nat) = 1 + 6 from rfl, run_add,
      show (ones 1 : List Sym) = ones 1 ++ [] from by simp, D_shift]
  cr_steps

-- Helper abbreviation for intermediate configs to avoid struct parsing issues
private abbrev IC (l : List Sym) (r : List Sym) : Config 6 :=
  { state := some stD, head := true, left := l, right := r }

/-- gen_cycle: one cycle with (2a+1) leading ones. Consumes one "one" from right. -/
lemma gen_cycle (a n B p : Nat) (hB : B ≥ 1) :
    run cryptid (IC (ones (2 * a + 1) ++ [false] ++ ones n) ([false] ++ ones B ++ zeros p))
      (4 * a + 7) =
    IC (ones (2 * a + 1) ++ [false] ++ ones (n + 1)) ([false] ++ ones (B - 1) ++ zeros p) := by
  simp only [IC]
  rw [show 4 * a + 7 = (2 * a + 1) + (2 * a + 6) from by ring, run_add,
      show (ones (2 * a + 1) ++ [false] ++ ones n : List Sym) =
        ones (2 * a + 1) ++ ([false] ++ ones n) from by rw [List.append_assoc], D_shift]
  rw [show 2 * a + 6 = 4 + (2 * a + 2) from by ring, run_add]
  -- Steps 1-3 reduce fully; step 4 leaves listHead/listTail of ones(2*a) unreduced
  conv => lhs; enter [2]; simp only [run, step, cr_D1, cr_D0, cr_A1, cr_B1,
    listHead_cons, listTail_cons, listHead_nil, listTail_nil,
    listHead_ones_succ, listTail_ones_succ,
    List.cons_append, List.nil_append, List.append_nil]
  cases a with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, ones_zero, List.nil_append,
      listHead_cons, listTail_cons]
    rw [show B = (B - 1) + 1 from by omega, ones_succ, List.cons_append]
    cr_steps
    congr 1
  | succ a' =>
    -- Resolve listHead/listTail of ones(2*(a'+1)) by rewriting to (k+1) form
    conv =>
      lhs; enter [2]
      rw [show (2 : Nat) * (a' + 1) = (2 * a' + 1) + 1 from by ring]
      simp only [ones_succ, List.cons_append, listHead_cons, listTail_cons]
    -- Fold back: true :: (ones (2*a') ++ ...) → ones (2*a') ++ (true :: ...)
    conv => lhs; enter [2, 4]; rw [← ones_true_cons]
    rw [show 2 * (a' + 1) + 2 = 2 * a' + 4 from by ring, run_add,
        EB_shift a' (true :: false :: true :: ones n) (true :: false :: (ones B ++ zeros p))]
    cr_steps
    rw [show B = (B - 1) + 1 from by omega, ones_succ, List.cons_append,
        listHead_cons, listTail_cons]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    congr 1

/-- flat_init: like gen_cycle but starting from flat ones. -/
lemma flat_init (a B p : Nat) (hB : B ≥ 1) :
    run cryptid (IC (ones (2 * a + 1)) ([false] ++ ones B ++ zeros p)) (4 * a + 7) =
    IC (ones (2 * a + 1) ++ [false] ++ ones 1) ([false] ++ ones (B - 1) ++ zeros p) := by
  simp only [IC]
  rw [show 4 * a + 7 = (2 * a + 1) + (2 * a + 6) from by ring, run_add,
      show (ones (2 * a + 1) : List Sym) = ones (2 * a + 1) ++ [] from by simp, D_shift]
  rw [show 2 * a + 6 = 4 + (2 * a + 2) from by ring, run_add]
  conv => lhs; enter [2]; simp only [run, step, cr_D1, cr_D0, cr_A1, cr_B1,
    listHead_cons, listTail_cons, listHead_nil, listTail_nil,
    listHead_ones_succ, listTail_ones_succ,
    List.cons_append, List.nil_append, List.append_nil]
  cases a with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, ones_zero, List.nil_append,
      listHead_cons, listTail_cons]
    rw [show B = (B - 1) + 1 from by omega, ones_succ, List.cons_append]
    cr_steps
    congr 1
  | succ a' =>
    conv =>
      lhs; enter [2]
      rw [show (2 : Nat) * (a' + 1) = (2 * a' + 1) + 1 from by ring]
      simp only [ones_succ, List.cons_append, listHead_cons, listTail_cons]
    conv => lhs; enter [2, 4]; rw [← ones_true_cons]
    rw [show 2 * (a' + 1) + 2 = 2 * a' + 4 from by ring, run_add,
        EB_shift a' [true, false, true] (true :: false :: (ones B ++ zeros p))]
    cr_steps
    rw [show B = (B - 1) + 1 from by omega, ones_succ, List.cons_append,
        listHead_cons, listTail_cons]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    congr 1

/-- gen_multi: iterate gen_cycle to consume all right ones. -/
lemma gen_multi (a n B p : Nat) : ∃ steps,
    run cryptid (IC (ones (2 * a + 1) ++ [false] ++ ones n) ([false] ++ ones B ++ zeros p)) steps =
    IC (ones (2 * a + 1) ++ [false] ++ ones (n + B)) (zeros (p + 1)) := by
  induction B generalizing n with
  | zero => exact ⟨0, by simp [IC, run]⟩
  | succ B ih =>
    have cycle := gen_cycle a n (B + 1) p (by omega)
    obtain ⟨rest, hrest⟩ := ih (n + 1)
    refine ⟨(4 * a + 7) + rest, ?_⟩
    rw [run_add, cycle, show B + 1 - 1 = B from by omega]
    convert hrest using 2; congr 1; congr 1; omega

/-- gen_boundary: 7 concrete steps from gen(0) form to simpler form. -/
lemma gen_boundary (n B p : Nat) :
    run cryptid (IC ([false] ++ ones (n + 2)) ([false] ++ ones B ++ zeros p)) 7 =
    IC (ones n) ([false] ++ ones (B + 3) ++ zeros p) := by
  simp only [IC, run, step, cr_A1, cr_B0, cr_C0, cr_D0, cr_D1, listHead_cons, listTail_cons,
    List.cons_append, List.nil_append, ← ones_succ]
  congr 1

/-- even_gen_cycle: one cycle with even leading ones. -/
lemma even_gen_cycle (K n B p : Nat) :
    run cryptid (IC (ones (2 * (K + 1)) ++ [false] ++ ones n)
      ([false] ++ ones B ++ zeros p)) (4 * (K + 1) + 5) =
    IC (ones (2 * K) ++ [false] ++ ones (n + 1)) ([false] ++ ones (B + 1) ++ zeros p) := by
  simp only [IC]
  rw [show 4 * (K + 1) + 5 = 2 * (K + 1) + (2 * K + 7) from by ring, run_add]
  rw [show (ones (2 * (K + 1)) ++ [false] ++ ones n : List Sym) =
    ones (2 * (K + 1)) ++ ([false] ++ ones n) from by simp [List.append_assoc], D_shift]
  -- Rewrite ones arg to (k+1) form so listHead_ones_succ fires in cr_steps
  rw [show (2 : Nat) * (K + 1) = (2 * K + 1) + 1 from by ring]
  rw [show 2 * K + 7 = 4 + (2 * K + 3) from by ring, run_add]
  conv => lhs; enter [2]; cr_steps_c
  rw [run_add, EB_shift K (true :: false :: true :: ones n) (false :: (ones B ++ zeros p))]
  cr_steps
  simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- gen_multi_cycle: iterate even_gen_cycle K times. -/
lemma gen_multi_cycle (K n B p : Nat) : ∃ steps,
    run cryptid (IC (ones (2 * K) ++ [false] ++ ones n)
      ([false] ++ ones B ++ zeros p)) steps =
    IC ([false] ++ ones (n + K)) ([false] ++ ones (B + K) ++ zeros p) := by
  induction K generalizing n B with
  | zero => exact ⟨0, by simp [IC, run]⟩
  | succ k ih =>
    have cycle := even_gen_cycle k n B p
    obtain ⟨rest, hrest⟩ := ih (n + 1) (B + 1)
    refine ⟨4 * (k + 1) + 5 + rest, ?_⟩
    rw [run_add, cycle]; convert hrest using 2 <;> ring_nf

/-- reverse_boundary: reduce leading ones by 2, generate 2 right ones from zeros. -/
lemma reverse_boundary (a n p : Nat) :
    run cryptid (IC (ones (2 * a + 3) ++ [false] ++ ones n) (zeros p)) (4 * a + 13) =
    IC (ones (2 * a + 1) ++ [false] ++ ones (n + 1)) ([false] ++ ones 2 ++ zeros (p - 2)) := by
  simp only [IC]
  rw [show 4 * a + 13 = (2 * a + 3) + (2 * a + 10) from by ring, run_add]
  rw [show (ones (2 * a + 3) ++ [false] ++ ones n : List Sym) =
    ones (2 * a + 3) ++ ([false] ++ ones n) from by simp [List.append_assoc], D_shift]
  -- Rewrite ones arg to nested (k+1) form for listHead_ones_succ
  rw [show (2 : Nat) * a + 3 = ((2 * a + 1) + 1) + 1 from by ring]
  rw [show 2 * a + 10 = 4 + (2 * a + 6) from by ring, run_add]
  conv => lhs; enter [2]; cr_steps_c
  -- After 4 steps: state E, right = ones(2*a+1) ++ zeros p (ones_succ expanded)
  -- cr_steps expands ones(2*a+1) to true :: (ones(2*a) ++ zeros p) via ones_succ + List.cons_append
  -- Fold back for EB_shift: true :: (ones(2*a) ++ zeros p) = ones(2*a) ++ (true :: zeros p)
  conv => lhs; enter [2, 4]; rw [← ones_true_cons]
  rw [run_add, EB_shift a (true :: false :: true :: ones n) (true :: zeros p)]
  rw [show (ones (2 * a) ++ (true :: false :: true :: ones n) : List Sym) =
    ones (2 * a + 1) ++ [false] ++ ones (n + 1) from by
      rw [ones_true_cons, ones_cons_append, List.append_assoc]; rfl]
  -- 6 closing steps
  simp only [run, step, cr_B1, cr_C0, cr_C1, cr_E0, cr_E1, cr_F1, listHead_cons, listTail_cons,
    listHead_zeros, listTail_zeros, List.cons_append, List.nil_append]
  congr 1

/-- gen_to_P: from gen form with zeros on right, reach P_Config. -/
lemma gen_to_P (a : Nat) : ∀ n p, ∃ steps padding,
    run cryptid (IC (ones (2 * a + 1) ++ [false] ++ ones n) (zeros p)) steps =
    P_Config (n + 3 * a) padding := by
  induction a with
  | zero =>
    intro n p; exact ⟨0, p, rfl⟩
  | succ a ih =>
    intro n p
    have hrb := reverse_boundary a n p
    obtain ⟨s_gm, h_gm⟩ := gen_multi a (n + 1) 2 (p - 2)
    obtain ⟨s_ih, pad, h_ih⟩ := ih (n + 1 + 2) ((p - 2) + 1)
    refine ⟨(4 * a + 13) + s_gm + s_ih, pad, ?_⟩
    rw [show 2 * (a + 1) + 1 = 2 * a + 3 from by ring,
        show (4 * a + 13) + s_gm + s_ih = (4 * a + 13) + (s_gm + s_ih) from by ring,
        run_add, hrb, run_add, h_gm, h_ih]
    congr 1; ring

/-- flat_to_gen: from flat ones to gen form. -/
lemma flat_to_gen (a B p : Nat) (hB : B ≥ 1) : ∃ steps,
    run cryptid (IC (ones (2 * a + 1)) ([false] ++ ones B ++ zeros p)) steps =
    IC (ones (2 * a + 1) ++ [false] ++ ones B) (zeros (p + 1)) := by
  cases a with
  | zero =>
    simp only [IC, Nat.mul_zero, Nat.zero_add]
    rw [show B = (B - 1) + 1 from by omega]
    have h1 := m1_to_scan (B - 1) p
    obtain ⟨s2, h2⟩ := right_scan 1 (B - 1) p
    refine ⟨7 + s2, ?_⟩
    rw [run_add, h1, h2, show 1 + (B - 1) = (B - 1) + 1 from by omega]
    unfold P_Config; rfl
  | succ a =>
    rw [show B = (B - 1) + 1 from by omega]
    have h1 := flat_init (a + 1) ((B - 1) + 1) p (by omega)
    rw [show (B - 1) + 1 - 1 = B - 1 from by omega] at h1
    obtain ⟨s2, h2⟩ := gen_multi (a + 1) 1 (B - 1) p
    refine ⟨(4 * (a + 1) + 7) + s2, ?_⟩
    rw [run_add, h1, h2]; simp only [IC]; congr 2; ring_nf

/-- odd_left_to_P: from odd ones on left to P_Config. -/
lemma odd_left_to_P (a : Nat) : ∀ B p, B ≥ 1 → ∃ steps padding,
    run cryptid (IC (ones (2 * a + 1)) ([false] ++ ones B ++ zeros p)) steps =
    P_Config (B + 3 * a) padding := by
  intro B p hB
  obtain ⟨s1, h1⟩ := flat_to_gen a B p hB
  obtain ⟨s2, pad, h2⟩ := gen_to_P a B (p + 1)
  exact ⟨s1 + s2, pad, by rw [run_add, h1, h2]⟩

/-- first_big_cycle_even: Q(2a+2, b) → gen form in 8a+13 steps. -/
lemma first_big_cycle_even (a b p : Nat) :
    run cryptid (Q_Config (2 * a + 2) b p) (8 * a + 13) =
    IC (ones (2 * (2 * a + 1)) ++ [false] ++ ones 1) ([false] ++ ones (b + 1) ++ zeros p) := by
  simp only [Q_Config, IC]
  rw [show 8 * a + 13 = (4 * a + 4) + (4 * a + 9) from by ring, run_add,
      show 2 * (2 * a + 2) = 4 * a + 4 from by ring,
      show (ones (4 * a + 4) : List Sym) = ones (4 * a + 4) ++ [] from by simp, D_shift]
  -- Rewrite ones arg to nested (k+1) form for listHead_ones_succ
  rw [show (4 : Nat) * a + 4 = ((4 * a + 2) + 1) + 1 from by ring]
  rw [show 4 * a + 9 = 4 + (4 * a + 5) from by ring, run_add]
  conv => lhs; enter [2]; cr_steps_c
  -- Fold cons-normalized right tape back to ones prefix for EB_shift
  conv => lhs; enter [2, 4]; rw [ones_cons_append, ones_cons_append,
    show (4 : Nat) * a + 1 + 1 = 2 * (2 * a + 1) from by ring]
  rw [show 4 * a + 5 = 2 * (2 * a + 1) + 3 from by ring,
      run_add, EB_shift (2 * a + 1) [true, false, true] (false :: (ones b ++ zeros p))]
  cr_steps
  simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- first_big_cycle: Q(2a+3, b) → gen form in 8a+17 steps. -/
lemma first_big_cycle (a b p : Nat) :
    run cryptid (Q_Config (2 * a + 3) b p) (8 * a + 17) =
    IC (ones (2 * (2 * a + 2)) ++ [false] ++ ones 1) ([false] ++ ones (b + 1) ++ zeros p) := by
  simp only [Q_Config, IC]
  rw [show 8 * a + 17 = (4 * a + 6) + (4 * a + 11) from by ring, run_add,
      show 2 * (2 * a + 3) = 4 * a + 6 from by ring,
      show (ones (4 * a + 6) : List Sym) = ones (4 * a + 6) ++ [] from by simp, D_shift]
  -- Rewrite ones arg to nested (k+1) form for listHead_ones_succ
  rw [show (4 : Nat) * a + 6 = ((4 * a + 4) + 1) + 1 from by ring]
  rw [show 4 * a + 11 = 4 + (4 * a + 7) from by ring, run_add]
  conv => lhs; enter [2]; cr_steps_c
  -- Fold cons-normalized right tape back to ones prefix for EB_shift
  conv => lhs; enter [2, 4]; rw [ones_cons_append, ones_cons_append, ones_cons_append, ones_cons_append,
    show (4 : Nat) * a + 1 + 1 + 1 + 1 = 2 * (2 * a + 2) from by ring]
  rw [show 4 * a + 7 = 2 * (2 * a + 2) + 3 from by ring,
      run_add, EB_shift (2 * a + 2) [true, false, true] (false :: (ones b ++ zeros p))]
  cr_steps
  simp only [List.append_assoc, List.cons_append, List.nil_append]

-- ============================================================
-- Macro step lemmas (using helpers)
-- ============================================================

-- Q(1, 2b+1) → P(3b+8)
lemma tm_Q_one_odd (b : Nat) (p : Nat) :
    ∃ steps padding,
      run cryptid (Q_Config 1 (2 * b + 1) p) steps = P_Config (3 * b + 8) padding := by
  obtain ⟨s_last, pad_last, h_last⟩ := odd_left_to_P (b + 2) 2 (p - 2) (by omega)
  refine ⟨25 + 2 * (b + 1) + s_last, pad_last, ?_⟩
  simp only [Q_Config]
  rw [show 25 + 2 * (b + 1) + s_last = 2 + (23 + 2 * (b + 1) + s_last) from by omega, run_add,
      show ones (2 * 1) = ones 2 ++ [] from by simp [ones], D_shift]
  rw [show 23 + 2 * (b + 1) + s_last = 17 + (6 + 2 * (b + 1) + s_last) from by omega, run_add]
  conv => lhs; enter [2]; cr_steps_c
  -- cr_steps_c expanded ones(2b+1) to true :: ones(2b), giving right = true³ :: (ones(2b) ++ zeros p)
  rw [show (true :: true :: true :: (ones (2 * b) ++ zeros p) : List Sym) =
      ones (2 * (b + 1)) ++ (true :: zeros p) from by
    conv => rhs; rw [show (2 : Nat) * (b + 1) = ((2 * b) + 1) + 1 from by ring,
      ones_succ, ones_succ, List.cons_append, List.cons_append, ones_true_cons]]
  rw [show 6 + 2 * (b + 1) + s_last = 2 * (b + 1) + (6 + s_last) from by omega,
      run_add, EB_shift (b + 1) [true, true, true] (true :: zeros p)]
  rw [show (ones (2 * (b + 1)) ++ [true, true, true] : List Sym) = ones (2 * b + 5) from by
    rw [show [true, true, true] = ones 3 from by simp [ones], ones_append]; congr 1]
  -- Split off 6 concrete steps (run can't decompose 6 + s_last directly)
  rw [run_add]
  conv => lhs; enter [2]; cr_steps_c
  -- Now matches odd_left_to_P(b+2, 2, p-2) via IC
  simp only [IC] at h_last
  convert h_last using 2; ring

-- Q(2a+2, b) → Q(a, b+2a+5)
lemma tm_Q_even (a : Nat) (b : Nat) (p : Nat) :
    ∃ steps padding,
      run cryptid (Q_Config (2 * a + 2) b p) steps = Q_Config a (b + 2 * a + 5) padding := by
  have h1 := first_big_cycle_even a b p
  obtain ⟨s2, h2⟩ := gen_multi_cycle (2 * a + 1) 1 (b + 1) p
  have h3 := gen_boundary (2 * a) (b + 2 * a + 2) p
  refine ⟨8 * a + 13 + s2 + 7, p, ?_⟩
  rw [show 8 * a + 13 + s2 + 7 = (8 * a + 13) + (s2 + 7) from by ring, run_add, h1, run_add, h2]
  conv => lhs; rw [show 1 + (2 * a + 1) = (2 * a) + 2 from by omega,
                    show b + 1 + (2 * a + 1) = b + 2 * a + 2 from by omega]
  rw [h3]; simp only [IC, Q_Config]

-- Q(2a+3, b) → P(b+5a+6)
lemma tm_Q_odd (a : Nat) (b : Nat) (p : Nat) :
    ∃ steps padding,
      run cryptid (Q_Config (2 * a + 3) b p) steps = P_Config (b + 5 * a + 6) padding := by
  have h1 := first_big_cycle a b p
  obtain ⟨s2, h2⟩ := gen_multi_cycle (2 * a + 2) 1 (b + 1) p
  have h3 := gen_boundary (2 * a + 1) (b + 2 * a + 3) p
  obtain ⟨s4, pad4, h4⟩ := odd_left_to_P a (b + 2 * a + 6) p (by omega)
  refine ⟨(8 * a + 17) + s2 + 7 + s4, pad4, ?_⟩
  rw [show (8 * a + 17) + s2 + 7 + s4 = (8 * a + 17) + (s2 + (7 + s4)) from by ring,
      run_add, h1, run_add, h2]
  conv => lhs; rw [show 1 + (2 * a + 2) = (2 * a + 1) + 2 from by omega,
                    show b + 1 + (2 * a + 2) = b + 2 * a + 3 from by omega]
  rw [run_add, h3, h4]
  congr 1; ring

-- P(2a) → P(3a+4)
lemma tm_P_even (k : Nat) (p : Nat) :
    ∃ steps padding,
      run cryptid (P_Config (2 * k) p) steps = P_Config (3 * k + 4) padding := by
  obtain ⟨steps2, padding2, h2⟩ := odd_left_to_P (k + 1) 1 (p - 3) (by omega)
  refine ⟨15 + steps2, padding2, ?_⟩
  rw [run_add]; simp only [P_Config]
  rw [show (15 : Nat) = 1 + 14 from rfl, run_add,
      show ([true, false] ++ ones (2 * k) : List Sym) =
        ones 1 ++ ([false] ++ ones (2 * k)) from by simp [ones], D_shift]
  cr_steps
  simp only [IC] at h2
  convert h2 using 2
  · simp only [P_Config, ← ones_succ, List.cons_append, List.nil_append]
    congr 1; congr 1; congr 1; ring

-- ============================================================
-- Completeness: nextMachineState covers all cases
-- ============================================================

/-- The blank tape reaches P(2) after 24 steps. -/
lemma tm_init : ∃ steps padding, run cryptid
    { state := some stA, head := false, left := [], right := [] } steps =
    P_Config 2 padding :=
  ⟨24, 1, rfl⟩

/-- Q(0,b) halts: the TM reaches state=none in 8 steps. -/
theorem macro_step_halt (b : Nat) (p : Nat) :
    (run cryptid (Q_Config 0 b p) 8).state = none :=
  tm_Q_halt b p

/-- Every non-terminal macro state can take a macro step to another macro state.
    Q(0,b) is excluded since it halts (see `macro_step_halt`). -/
theorem macro_step_complete (ms : MachineState) (p : Nat) :
    ms ≠ .Halt → nextMachineState ms ≠ .Halt →
    ∃ steps padding ms',
      (match ms with
        | .P a => run cryptid (P_Config a p) steps = match ms' with
            | .P a' => P_Config a' padding
            | .Q a' b' => Q_Config a' b' padding
            | .Halt => P_Config 0 padding  -- unreachable
        | .Q a b => run cryptid (Q_Config a b p) steps = match ms' with
            | .P a' => P_Config a' padding
            | .Q a' b' => Q_Config a' b' padding
            | .Halt => P_Config 0 padding  -- unreachable
        | .Halt => True) ∧
      ms' = nextMachineState ms := by
  intro hne hne'
  match ms, hne with
  | .Halt, hne => exact absurd rfl hne
  | .P a, _ =>
    obtain ⟨k, rfl | rfl⟩ : ∃ k, a = 2 * k ∨ a = 2 * k + 1 := ⟨a / 2, by omega⟩
    · -- P(2k) → P(3k+4)
      obtain ⟨steps, padding, h⟩ := tm_P_even k p
      exact ⟨steps, padding, .P (3 * k + 4), h, by simp [nextMachineState]⟩
    · -- P(2k+1) → Q(k+2, 1)
      obtain ⟨padding, h⟩ := tm_P_odd k p
      exact ⟨15, padding, .Q (k + 2) 1, h, by simp [nextMachineState]; omega⟩
  | .Q a b, _ =>
    match a, hne' with
    | 0, hne' => exact absurd (by simp [nextMachineState]) hne'
    | 1, _ =>
      obtain ⟨k, rfl | rfl⟩ : ∃ k, b = 2 * k ∨ b = 2 * k + 1 := ⟨b / 2, by omega⟩
      · -- Q(1, 2k) → Q(k+2, 1)
        obtain ⟨padding, h⟩ := tm_Q_one_even k p
        exact ⟨2 * k + 24, padding, .Q (k + 2) 1, h, by simp [nextMachineState]⟩
      · -- Q(1, 2k+1) → P(3k+8)
        obtain ⟨steps, padding, h⟩ := tm_Q_one_odd k p
        exact ⟨steps, padding, .P (3 * k + 8), h, by simp [nextMachineState]; omega⟩
    | a' + 2, _ =>
      obtain ⟨k, rfl | rfl⟩ : ∃ k, a' = 2 * k ∨ a' = 2 * k + 1 := ⟨a' / 2, by omega⟩
      · -- Q(2k+2, b) → Q(k, b+2k+5)  [tm_Q_even with a=k]
        obtain ⟨steps, padding, h⟩ := tm_Q_even k b p
        exact ⟨steps, padding, .Q k (b + 2 * k + 5), h, by simp [nextMachineState]⟩
      · -- Q(2k+3, b) → P(b+5k+6)  [tm_Q_odd with a=k]
        obtain ⟨steps, padding, h⟩ := tm_Q_odd k b p
        exact ⟨steps, padding, .P (b + 5 * k + 6), h, by simp [nextMachineState]⟩

/-- The Cryptid TM does not halt (conjecture). -/
def nonHalting : Prop :=
  ∀ n, iterMachineState (.P 2) n ≠ .Halt

end Cryptid
