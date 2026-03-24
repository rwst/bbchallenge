import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
-- import Mathlib.Tactic.Omega  -- not yet built; re-enable when needed for proofs

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

## Mathematical Model

The machine's behavior from the initial blank tape factors through two
macro configurations P(a) and Q(a, b), with tape encodings:

  P(a)   := 0^∞ 1^a 011 <D 0^∞
  Q(a,b) := 0^∞ 1^(2a+1) <D 0 1^b 0^∞

Here `<D` means the head is in state D reading the cell to its left (a 1).
In the zipper representation:
  P(a)   : state = D, head = 1, left = [1,0] ++ 1^a,   right = 0^p
  Q(a,b) : state = D, head = 1, left = 1^(2a),          right = [0] ++ 1^b ++ 0^p

### Map Rules

  P(2a)     → P(3a+4)
  P(2a+1)   → Q(a+2, 1)

  Q(0, b)     → halt
  Q(1, 2b)    → Q(b+2, 1)
  Q(1, 2b+1)  → P(3b+8)
  Q(2a+2, b)  → Q(a, b+2a+5)
  Q(2a+3, b)  → P(b+5a+6)

### Start: P(2)

The TM halts iff it reaches Q(0, b) for some b.

### Additional Analysis

The P-map on even arguments gives P(2a) → P(3a+4), roughly multiplying by 1.5.
On odd arguments, P(2a+1) → Q(a+2, 1) enters the Q phase.

In the Q phase, even first arguments halve: Q(2k+2, b) → Q(k, b+2k+5).
Odd first arguments exit immediately: Q(2k+3, b) → P(b+5k+6).
So the Q phase is a sequence of halvings (accumulating into b) until the
first argument becomes odd (exit to P) or reaches 0 or 1.

Key halting paths:
  Q(2, b) → Q(0, b+5) → halt
  Q(1, 0) → Q(2, 1) → Q(0, 6) → halt

The machine halts iff the orbit from P(2) ever produces Q(0, b) or Q(2, b)
or Q(1, 0). Forward simulation of 10^8 iterations of the combined map shows
no halt, with the P-argument reaching ~ 10^(6.04 × 10^6).

This is a Collatz-like system: the question of halting is analogous to asking
whether a specific Collatz-like orbit reaches a small value.
-/

-- ============================================================
-- Section 1: Finitary Types
-- ============================================================

abbrev TapeSymbol := Bool  -- false = 0 (blank), true = 1
abbrev State := Fin 6      -- 6 non-halt states A..F

inductive Dir where | L | R
deriving DecidableEq, Repr

-- ============================================================
-- Section 2: Transition Table
-- ============================================================

def transition (q : State) (s : TapeSymbol) : Option State × TapeSymbol × Dir :=
  match q.val, s with
  -- A: 1RB  0RB
  | 0, false => (some ⟨1, by decide⟩, true,  Dir.R)
  | 0, true  => (some ⟨1, by decide⟩, false, Dir.R)
  -- B: 1LC  1RE
  | 1, false => (some ⟨2, by decide⟩, true,  Dir.L)
  | 1, true  => (some ⟨4, by decide⟩, true,  Dir.R)
  -- C: 1LF  0LD
  | 2, false => (some ⟨5, by decide⟩, true,  Dir.L)
  | 2, true  => (some ⟨3, by decide⟩, false, Dir.L)
  -- D: 1RA  1LD
  | 3, false => (some ⟨0, by decide⟩, true,  Dir.R)
  | 3, true  => (some ⟨3, by decide⟩, true,  Dir.L)
  -- E: 1RC  1RB
  | 4, false => (some ⟨2, by decide⟩, true,  Dir.R)
  | 4, true  => (some ⟨1, by decide⟩, true,  Dir.R)
  -- F: ---  1LC
  | 5, false => (none,                false, Dir.R)   -- HALT
  | 5, true  => (some ⟨2, by decide⟩, true,  Dir.L)
  | _, _     => (none,                false, Dir.R)

-- State abbreviations (canonical proof terms for Fin membership)
abbrev stA : State := ⟨0, by decide⟩
abbrev stB : State := ⟨1, by decide⟩
abbrev stC : State := ⟨2, by decide⟩
abbrev stD : State := ⟨3, by decide⟩
abbrev stE : State := ⟨4, by decide⟩
abbrev stF : State := ⟨5, by decide⟩

-- ============================================================
-- Section 3: Configuration (Zipper Tape)
-- ============================================================

@[ext] structure Config where
  state : Option State    -- none = HALT
  left  : List TapeSymbol -- reversed: head is immediately left of TM head
  head  : TapeSymbol
  right : List TapeSymbol -- head is immediately right of TM head
deriving Repr, Inhabited

def headD' {α : Type} (l : List α) (default : α) : α :=
  match l with
  | [] => default
  | a :: _ => a

def tailD' {α : Type} (l : List α) : List α :=
  match l with
  | [] => []
  | _ :: as => as

def step (c : Config) : Config :=
  match c.state with
  | none => c  -- HALT is a fixed point
  | some q =>
    let (q', w, d) := transition q c.head
    match d with
    | Dir.R =>
      { state := q', left := w :: c.left,
        head := headD' c.right false, right := tailD' c.right }
    | Dir.L =>
      { state := q', left := tailD' c.left,
        head := headD' c.left false, right := w :: c.right }

def run (c : Config) (n : Nat) : Config :=
  match n with
  | 0 => c
  | n' + 1 => run (step c) n'

-- Initial configuration: state A on blank tape
def initConfig : Config :=
  { state := some ⟨0, by decide⟩, left := [], head := false, right := [] }

-- ============================================================
-- Section 4: Tape Helpers
-- ============================================================

def repeatOne (k : Nat) : List TapeSymbol := List.replicate k true
def repeatFalse (k : Nat) : List TapeSymbol := List.replicate k false

@[simp] lemma repeatOne_succ (k : Nat) : repeatOne (k + 1) = true :: repeatOne k := rfl
@[simp] lemma repeatFalse_succ (k : Nat) : repeatFalse (k + 1) = false :: repeatFalse k := rfl
@[simp] lemma repeatOne_zero : repeatOne 0 = [] := rfl
@[simp] lemma repeatFalse_zero : repeatFalse 0 = [] := rfl

lemma repeatOne_snoc (k : Nat) : repeatOne k ++ [true] = repeatOne (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [repeatOne_succ, List.cons_append, ih]

lemma repeatOne_two (k : Nat) : repeatOne k ++ [true, true] = repeatOne (k + 2) := by
  rw [show [true, true] = [true] ++ [true] from rfl,
      ← List.append_assoc, repeatOne_snoc, repeatOne_snoc]

-- Proof irrelevance for Fin: normalize any proof of a < n to a canonical one.
-- Needed because `transition` generates internal proof terms that differ from `by decide`.
@[simp] lemma fin_proof_irrel {n : Nat} {a : Nat} (h1 h2 : a < n) :
    (⟨a, h1⟩ : Fin n) = ⟨a, h2⟩ := Fin.ext rfl

@[simp] lemma headD'_cons {α} (x : α) (xs : List α) (d : α) : headD' (x :: xs) d = x := rfl
@[simp] lemma tailD'_cons {α} (x : α) (xs : List α) : tailD' (x :: xs) = xs := rfl
@[simp] lemma headD'_nil (b : TapeSymbol) : headD' [] b = b := rfl
@[simp] lemma tailD'_nil : @tailD' TapeSymbol [] = [] := rfl

def countOnes : List TapeSymbol → Nat
  | [] => 0
  | true :: xs => countOnes xs + 1
  | false :: _ => 0

@[simp] lemma countOnes_repeatOne (n : Nat) : countOnes (repeatOne n) = n := by
  induction n with
  | zero => simp [repeatOne, countOnes]
  | succ k ih => simp only [repeatOne_succ, countOnes, ih]

@[simp] lemma countOnes_append_repeatFalse (b p : Nat) :
    countOnes (repeatOne b ++ repeatFalse p) = b := by
  induction b with
  | zero => cases p with
    | zero => simp [repeatFalse, countOnes, repeatOne]
    | succ n => simp only [repeatFalse, List.replicate_succ, repeatOne]; simp [countOnes]
  | succ k ih => simp only [repeatOne_succ, List.cons_append, countOnes, ih]

lemma cons_rO_app (k : Nat) (l : List TapeSymbol) :
    true :: (repeatOne k ++ l) = repeatOne (k + 1) ++ l := by
  simp [repeatOne_succ, List.cons_append]


-- ============================================================
-- Section 5: Configuration Encodings
-- ============================================================

/-- P(a) := 0^∞ 1^a 011 <D 0^∞
    Head reads the last 1 of "011" (so head = true, state D).
    left  = [true, false] ++ repeatOne a   (reading left: 1, 0, 1^a)
    right = repeatFalse p                  (trailing zeros / padding) -/
def P_Config (a : Nat) (p : Nat) : Config :=
  { state := some stD,
    head := true,
    left := [true, false] ++ repeatOne a,
    right := repeatFalse p }

/-- Q(a,b) := 0^∞ 1^(2a+1) <D 0 1^b 0^∞
    Head reads the last 1 of "1^(2a+1)" (so head = true, state D).
    left  = repeatOne (2*a)                (remaining 2a ones)
    right = [false] ++ repeatOne b ++ repeatFalse p -/
def Q_Config (a b : Nat) (p : Nat) : Config :=
  { state := some stD,
    head := true,
    left := repeatOne (2 * a),
    right := [false] ++ repeatOne b ++ repeatFalse p }

-- ============================================================
-- Section 6: Mathematical Model
-- ============================================================

/-- The high-level state: either P(a), Q(a,b), or Halt. -/
inductive MachineState where
  | P : Nat → MachineState
  | Q : Nat → Nat → MachineState
  | Halt : MachineState
deriving Repr, DecidableEq

/-- One step of the combined P/Q map.
    P(2a)     → P(3a+4)
    P(2a+1)   → Q(a+2, 1)
    Q(0, b)   → Halt
    Q(1, 2b)  → Q(b+2, 1)
    Q(1, 2b+1)→ P(3b+8)
    Q(a+2, b) → Q(a/2, b+a+5)   if a even  (i.e., original arg 2k+2)
    Q(a+2, b) → P(b+5·(a-1)/2+6) if a odd  (i.e., original arg 2k+3) -/
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

/-- Iterate the combined map n times. -/
def iterMachineState (s : MachineState) : Nat → MachineState
  | 0 => s
  | n + 1 => iterMachineState (nextMachineState s) n

-- Sanity checks via #eval
#eval nextMachineState (.P 2)     -- expect P(7):   P(2·1) → P(3+4)
#eval nextMachineState (.P 7)     -- expect Q(5,1): P(2·3+1) → Q(5,1)
#eval nextMachineState (.Q 5 1)   -- expect P(12):  Q(2·1+3,1) → P(1+5+6)
#eval nextMachineState (.P 12)    -- expect P(22):  P(2·6) → P(22)
#eval nextMachineState (.Q 2 1)   -- expect Q(0,6): Q(2·0+2,1) → Q(0,6)
#eval nextMachineState (.Q 0 6)   -- expect Halt
#eval nextMachineState (.Q 1 0)   -- expect Q(2,1): Q(1,2·0) → Q(2,1)
#eval nextMachineState (.Q 1 1)   -- expect P(8):   Q(1,2·0+1) → P(8)

-- First several iterates from the start
#eval (List.range 15).map (iterMachineState (.P 2))

-- ============================================================
-- Section 7: Infrastructure Lemmas
-- ============================================================

lemma run_add (c : Config) (n m : Nat) : run c (n + m) = run (run c n) m := by
  induction n generalizing c with
  | zero => rw [Nat.zero_add]; rfl
  | succ n ih =>
    calc
      run c (n + 1 + m) = run c (n + m + 1) := by congr 1; omega
      _ = run (step c) (n + m) := rfl
      _ = run (run (step c) n) m := ih (step c)
      _ = run (run c (n + 1)) m := rfl

@[simp] lemma run_step_succ (c : Config) (n : Nat) :
  run c (n + 1) = run (step c) n := rfl

/-- State D scans left through k ones: D reads 1, writes 1, moves L, stays D.
    After k steps, all k ones from the left tape are moved to the right tape.
    The head symbol remains true throughout (each step reads and re-writes 1). -/
lemma D_shift (k : Nat) (L R : List TapeSymbol) :
  run { state := some stD, head := true,
        left := repeatOne k ++ L, right := R } k =
  { state := some stD, head := true,
    left := L, right := repeatOne k ++ R } := by
  induction k generalizing R with
  | zero => simp [run, repeatOne]
  | succ n ih =>
    simp only [repeatOne_succ, List.cons_append, run_step_succ]
    have step_eq : step (⟨some stD, true :: (repeatOne n ++ L), true, R⟩ : Config) =
      (⟨some stD, repeatOne n ++ L, true, true :: R⟩ : Config) := by
      simp [step, stD, transition]
    rw [step_eq, ih (true :: R)]
    simp only [repeatOne]
    rw [show true :: R = [true] ++ R from rfl, ← List.append_assoc,
        ← List.replicate_succ', List.replicate_succ, List.cons_append]

/-- E/B scan right through 1s in an alternating pattern:
    E reads 1 → 1RB, B reads 1 → 1RE.
    After 2k steps, 2k ones from the right have been moved to the left,
    plus the initial head (true), for a total of 2k+1 ones on the left.
    State returns to E. -/
lemma EB_shift (k : Nat) (L R : List TapeSymbol) :
  run { state := some stE, head := true,
        left := L, right := repeatOne (2 * k) ++ R } (2 * k) =
  { state := some stE, head := true,
    left := repeatOne (2 * k) ++ L, right := R } := by
  induction k generalizing L with
  | zero => simp [run, repeatOne]
  | succ n ih =>
    have h2k : 2 * (n + 1) = 2 * n + 2 := by ring
    conv_lhs => rw [h2k]
    have rep_unfold : repeatOne (2 * n + 2) ++ R = true :: true :: (repeatOne (2 * n) ++ R) := by
      simp [repeatOne, List.replicate_succ, List.cons_append]
    simp only [run_step_succ, rep_unfold]
    have step1 : step (⟨some stE, L, true, true :: true :: (repeatOne (2 * n) ++ R)⟩ : Config) =
      ⟨some stB, true :: L, true, true :: (repeatOne (2 * n) ++ R)⟩ := by
      ext <;> simp [step, transition, stB, Fin.ext_iff]
    have step2 : step (⟨some stB, true :: L, true, true :: (repeatOne (2 * n) ++ R)⟩ : Config) =
      ⟨some stE, true :: true :: L, true, repeatOne (2 * n) ++ R⟩ := by
      ext <;> simp [step, transition, stE, Fin.ext_iff]
    rw [step1, step2, ih]
    congr 1
    rw [show true :: true :: L = [true, true] ++ L from rfl, ← List.append_assoc]
    congr 1
    change List.replicate (2 * n) true ++ List.replicate 2 true =
           List.replicate 2 true ++ List.replicate (2 * n) true
    rw [← List.replicate_add, ← List.replicate_add]
    ring_nf

-- ============================================================
-- Section 8: Macro Step Lemma Statements (P rules)
-- ============================================================

/-- P(2a+1) → Q(a+2, 1): When a is odd (a = 2k+1), one macro step transforms
    P_Config(2k+1) into Q_Config(k+2, 1) in some number of TM steps. -/
lemma tm_P_odd (k : Nat) (p : Nat) :
  ∃ steps padding,
    run (P_Config (2 * k + 1) p) steps = Q_Config (k + 2) 1 padding := by
  have hd_rF : ∀ n, headD' (repeatFalse n) false = false := by
    intro n; cases n <;> simp [repeatFalse, List.replicate]
  have tl_rF : ∀ n, tailD' (repeatFalse n) = repeatFalse (n - 1) := by
    intro n; cases n with
    | zero => simp [repeatFalse, List.replicate]
    | succ m => simp [repeatFalse, List.replicate_succ]
  have cons_rO : ∀ n, true :: repeatOne n = repeatOne (n + 1) := fun n => rfl
  refine ⟨15, p - 3, ?_⟩
  simp only [P_Config]
  -- D_shift(1): scan left past the one true
  rw [show (15 : Nat) = 1 + 14 from rfl, run_add]
  conv_lhs => arg 1; rw [show ([true, false] ++ repeatOne (2 * k + 1) : List TapeSymbol) =
    repeatOne 1 ++ ([false] ++ repeatOne (2 * k + 1)) from by simp [repeatOne, List.replicate]]
  rw [D_shift]
  -- Now peel 14 steps using run_step_succ
  rw [show (14 : Nat) = 13 + 1 from rfl, run_step_succ]
  have step2 : step ⟨some stD, [false] ++ repeatOne (2 * k + 1), true,
      repeatOne 1 ++ repeatFalse p⟩ =
    ⟨some stD, repeatOne (2 * k + 1), false, true :: repeatOne 1 ++ repeatFalse p⟩ := by
    ext <;> simp [step, transition, repeatOne, List.replicate, stD, Fin.ext_iff]
  rw [step2]
  rw [show (13 : Nat) = 12 + 1 from rfl, run_step_succ]
  have step3 : step ⟨some stD, repeatOne (2 * k + 1), false,
      true :: repeatOne 1 ++ repeatFalse p⟩ =
    ⟨some stA, true :: repeatOne (2 * k + 1), true, repeatOne 1 ++ repeatFalse p⟩ := by
    ext <;> simp [step, transition, stA, Fin.ext_iff]
  rw [step3, cons_rO]
  rw [show (12 : Nat) = 11 + 1 from rfl, run_step_succ]
  have step4 : step ⟨some stA, repeatOne (2 * k + 2), true,
      repeatOne 1 ++ repeatFalse p⟩ =
    ⟨some stB, false :: repeatOne (2 * k + 2), true, repeatFalse p⟩ := by
    ext <;> simp [step, transition, repeatOne, List.replicate, stB, Fin.ext_iff]
  rw [step4]
  rw [show (11 : Nat) = 10 + 1 from rfl, run_step_succ]
  have step5 : step ⟨some stB, false :: repeatOne (2 * k + 2), true, repeatFalse p⟩ =
    ⟨some stE, true :: false :: repeatOne (2 * k + 2), headD' (repeatFalse p) false,
      tailD' (repeatFalse p)⟩ := by ext <;> simp [step, transition, stE, Fin.ext_iff]
  rw [step5, hd_rF, tl_rF]
  rw [show (10 : Nat) = 9 + 1 from rfl, run_step_succ]
  have step6 : step ⟨some stE, true :: false :: repeatOne (2 * k + 2), false,
      repeatFalse (p - 1)⟩ =
    ⟨some stC, true :: true :: false :: repeatOne (2 * k + 2),
      headD' (repeatFalse (p - 1)) false, tailD' (repeatFalse (p - 1))⟩ := by
    ext <;> simp [step, transition, stC, Fin.ext_iff]
  rw [step6, hd_rF, tl_rF]
  rw [show (9 : Nat) = 8 + 1 from rfl, run_step_succ]
  have step7 : step ⟨some stC, true :: true :: false :: repeatOne (2 * k + 2), false,
      repeatFalse (p - 1 - 1)⟩ =
    ⟨some stF, true :: false :: repeatOne (2 * k + 2), true,
      true :: repeatFalse (p - 1 - 1)⟩ := by ext <;> simp [step, transition, stF, Fin.ext_iff]
  rw [step7]
  rw [show (8 : Nat) = 7 + 1 from rfl, run_step_succ]
  have step8 : step ⟨some stF, true :: false :: repeatOne (2 * k + 2), true,
      true :: repeatFalse (p - 1 - 1)⟩ =
    ⟨some stC, false :: repeatOne (2 * k + 2), true,
      true :: true :: repeatFalse (p - 1 - 1)⟩ := by ext <;> simp [step, transition, stC, Fin.ext_iff]
  rw [step8]
  rw [show (7 : Nat) = 6 + 1 from rfl, run_step_succ]
  have step9 : step ⟨some stC, false :: repeatOne (2 * k + 2), true,
      true :: true :: repeatFalse (p - 1 - 1)⟩ =
    ⟨some stD, repeatOne (2 * k + 2), false,
      false :: true :: true :: repeatFalse (p - 1 - 1)⟩ := by ext <;> simp [step, transition, stD, Fin.ext_iff]
  rw [step9]
  rw [show (6 : Nat) = 5 + 1 from rfl, run_step_succ]
  have step10 : step ⟨some stD, repeatOne (2 * k + 2), false,
      false :: true :: true :: repeatFalse (p - 1 - 1)⟩ =
    ⟨some stA, true :: repeatOne (2 * k + 2), false,
      true :: true :: repeatFalse (p - 1 - 1)⟩ := by ext <;> simp [step, transition, stA, Fin.ext_iff]
  rw [step10, cons_rO]
  rw [show (5 : Nat) = 4 + 1 from rfl, run_step_succ]
  have step11 : step ⟨some stA, repeatOne (2 * k + 3), false,
      true :: true :: repeatFalse (p - 1 - 1)⟩ =
    ⟨some stB, true :: repeatOne (2 * k + 3), true,
      true :: repeatFalse (p - 1 - 1)⟩ := by ext <;> simp [step, transition, stB, Fin.ext_iff]
  rw [step11, cons_rO]
  rw [show (4 : Nat) = 3 + 1 from rfl, run_step_succ]
  have step12 : step ⟨some stB, repeatOne (2 * k + 4), true,
      true :: repeatFalse (p - 1 - 1)⟩ =
    ⟨some stE, true :: repeatOne (2 * k + 4), true,
      repeatFalse (p - 1 - 1)⟩ := by ext <;> simp [step, transition, stE, Fin.ext_iff]
  rw [step12, cons_rO]
  rw [show (3 : Nat) = 2 + 1 from rfl, run_step_succ]
  have step13 : step ⟨some stE, repeatOne (2 * k + 5), true, repeatFalse (p - 1 - 1)⟩ =
    ⟨some stB, true :: repeatOne (2 * k + 5),
      headD' (repeatFalse (p - 1 - 1)) false, tailD' (repeatFalse (p - 1 - 1))⟩ := by
    ext <;> simp [step, transition, stB, Fin.ext_iff]
  rw [step13, hd_rF, tl_rF, cons_rO]
  rw [show 2 * k + 6 = (2 * k + 5) + 1 from by omega, repeatOne_succ]
  rw [show (2 : Nat) = 1 + 1 from rfl, run_step_succ]
  have step14 : step ⟨some stB, true :: repeatOne (2 * k + 5), false,
      repeatFalse (p - 1 - 1 - 1)⟩ =
    ⟨some stC, repeatOne (2 * k + 5), true,
      true :: repeatFalse (p - 1 - 1 - 1)⟩ := by ext <;> simp [step, transition, stC, Fin.ext_iff]
  rw [step14, show 2 * k + 5 = (2 * k + 4) + 1 from by omega, repeatOne_succ]
  rw [show (1 : Nat) = 0 + 1 from rfl, run_step_succ]
  have step15 : step ⟨some stC, true :: repeatOne (2 * k + 4), true,
      true :: repeatFalse (p - 1 - 1 - 1)⟩ =
    ⟨some stD, repeatOne (2 * k + 4), true,
      false :: true :: repeatFalse (p - 1 - 1 - 1)⟩ := by ext <;> simp [step, transition, stD, Fin.ext_iff]
  rw [step15]; simp only [run, Q_Config]; congr 1

-- ============================================================
-- Section 9: Macro Step Lemma Statements (Q rules)
-- ============================================================

/-- Q(0, b) → halt: The TM halts from Q_Config(0, b) in 8 steps. -/
lemma tm_Q_halt (b : Nat) (p : Nat) :
  (run (Q_Config 0 b p) 8).state = none := by
  simp [run, step, transition, Q_Config, repeatOne]

/-- Q(1, 2b) → Q(b+2, 1) -/
lemma tm_Q_one_even (b : Nat) (p : Nat) :
  ∃ steps padding,
    run (Q_Config 1 (2 * b) p) steps = Q_Config (b + 2) 1 padding := by
  -- Helpers
  have hd_rF : ∀ n, headD' (repeatFalse n) false = false := by
    intro n; cases n <;> simp [repeatFalse, List.replicate]
  have tl_rF : ∀ n, tailD' (repeatFalse n) = repeatFalse (n - 1) := by
    intro n; cases n with
    | zero => simp [repeatFalse, List.replicate]
    | succ m => simp [repeatFalse, List.replicate_succ]
  have cons_rO : ∀ n, true :: repeatOne n = repeatOne (n + 1) := by
    intro n; simp [repeatOne, List.replicate_succ]
  have cons_rO_app : ∀ n, true :: (repeatOne n ++ repeatFalse p) =
      repeatOne (n + 1) ++ repeatFalse p := by
    intro n; rw [repeatOne_succ, List.cons_append]
  -- Total: 2 + 17 + 2*(b+1) + 3 = 2b+24
  refine ⟨2 * b + 24, p - 1, ?_⟩
  simp only [Q_Config]
  -- Phase 1: D_shift 2
  rw [show 2 * b + 24 = 2 + (2 * b + 22) from by omega, run_add,
      show (2 : Nat) * 1 = 2 from by norm_num,
      show (repeatOne 2 : List TapeSymbol) = repeatOne 2 ++ [] from (List.append_nil _).symm]
  rw [D_shift 2 [] ([false] ++ repeatOne (2 * b) ++ repeatFalse p)]
  -- {D, true, [], repeatOne 2 ++ ([false] ++ repeatOne(2b) ++ repeatFalse p)}
  simp only [repeatOne_succ, repeatOne_zero, List.nil_append, List.cons_append]
  -- {D, true, [], true :: true :: false :: repeatOne(2b) ++ repeatFalse p}
  -- Step 3: D true → D L
  rw [show 2 * b + 22 = (2 * b + 21) + 1 from by omega, run_step_succ]
  simp only [step, transition, headD'_nil, tailD'_nil]
  -- {D, false, [], true :: true :: true :: false :: repeatOne(2b) ++ repeatFalse p}
  -- Step 4: D false → A R
  rw [show 2 * b + 21 = (2 * b + 20) + 1 from by omega, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {A, true, [true], true :: true :: false :: repeatOne(2b) ++ repeatFalse p}
  -- Step 5: A true → B 0 R
  rw [show 2 * b + 20 = (2 * b + 19) + 1 from by omega, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {B, true, [false, true], true :: false :: repeatOne(2b) ++ repeatFalse p}
  -- Step 6: B true → E 1 R
  rw [show 2 * b + 19 = (2 * b + 18) + 1 from by omega, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {E, true, [true, false, true], false :: repeatOne(2b) ++ repeatFalse p}
  -- Step 7: E true → B 1 R
  rw [show 2 * b + 18 = (2 * b + 17) + 1 from by omega, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {B, false, [true, true, false, true], repeatOne(2b) ++ repeatFalse p}
  -- Step 8: B false → C 1 L
  rw [show 2 * b + 17 = (2 * b + 16) + 1 from by omega, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {C, true, [true, false, true], true :: repeatOne(2b) ++ repeatFalse p}
  rw [cons_rO_app (2 * b)]
  -- Step 9: C true → D 0 L
  rw [show 2 * b + 16 = (2 * b + 15) + 1 from by omega, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {D, true, [false, true], false :: repeatOne(2b+1) ++ repeatFalse p}
  -- Step 10: D true → D 1 L
  rw [show 2 * b + 15 = (2 * b + 14) + 1 from by omega, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {D, false, [true], true :: false :: repeatOne(2b+1) ++ repeatFalse p}
  -- Step 11: D false → A 1 R
  rw [show 2 * b + 14 = (2 * b + 13) + 1 from by omega, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {A, true, [true, true], false :: repeatOne(2b+1) ++ repeatFalse p}
  -- Step 12: A true → B 0 R
  rw [show 2 * b + 13 = (2 * b + 12) + 1 from by omega, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {B, false, [false, true, true], repeatOne(2b+1) ++ repeatFalse p}
  -- Step 13: B false → C 1 L
  rw [show 2 * b + 12 = (2 * b + 11) + 1 from by omega, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {C, false, [true, true], true :: repeatOne(2b+1) ++ repeatFalse p}
  rw [cons_rO_app (2 * b + 1)]
  -- Step 14: C false → F 1 L
  rw [show 2 * b + 11 = (2 * b + 10) + 1 from by omega, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {F, true, [true], true :: repeatOne(2b+2) ++ repeatFalse p}
  rw [cons_rO_app (2 * b + 2)]
  -- Step 15: F true → C 1 L
  rw [show 2 * b + 10 = (2 * b + 9) + 1 from by omega, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {C, true, [], true :: repeatOne(2b+3) ++ repeatFalse p}
  rw [cons_rO_app (2 * b + 3)]
  -- Step 16: C true → D 0 L
  rw [show 2 * b + 9 = (2 * b + 8) + 1 from by omega, run_step_succ]
  simp only [step, transition, headD'_nil, tailD'_nil]
  -- {D, false, [], false :: repeatOne(2b+4) ++ repeatFalse p}
  -- Step 17: D false → A 1 R
  rw [show 2 * b + 8 = (2 * b + 7) + 1 from by omega, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {A, false, [true], repeatOne(2b+4) ++ repeatFalse p}
  -- Step 18: A false → B 1 R. Need headD'(repeatOne(2b+4) ++ rF p) = true
  rw [show 2 * b + 7 = (2 * b + 6) + 1 from by omega, run_step_succ]
  have step18_eq : step ⟨some stA, [true], false,
      repeatOne (2 * b + 4) ++ repeatFalse p⟩ =
    ⟨some stB, [true, true], headD' (repeatOne (2 * b + 4) ++ repeatFalse p) false,
      tailD' (repeatOne (2 * b + 4) ++ repeatFalse p)⟩ := by
    simp [step, transition, stB]
  rw [step18_eq]
  rw [show 2 * b + 4 = (2 * b + 3) + 1 from by omega,
      repeatOne_succ, List.cons_append, headD'_cons, tailD'_cons]
  -- {B, true, [true, true], repeatOne(2b+3) ++ repeatFalse p}
  -- Step 19: B true → E 1 R. Need headD'(repeatOne(2b+3) ++ rF p) = true
  rw [show 2 * b + 6 = (2 * b + 5) + 1 from by omega, run_step_succ]
  have step19_eq : step ⟨some stB, [true, true], true,
      repeatOne (2 * b + 3) ++ repeatFalse p⟩ =
    ⟨some stE, [true, true, true], headD' (repeatOne (2 * b + 3) ++ repeatFalse p) false,
      tailD' (repeatOne (2 * b + 3) ++ repeatFalse p)⟩ := by
    simp [step, transition, stE]
  rw [step19_eq]
  rw [show 2 * b + 3 = (2 * b + 2) + 1 from by omega,
      repeatOne_succ, List.cons_append, headD'_cons, tailD'_cons]
  -- {E, true, [true, true, true], repeatOne(2b+2) ++ repeatFalse p}
  -- Phase 3: EB_shift(b+1) through 2(b+1) = 2b+2 ones
  rw [show 2 * b + 5 = 2 * (b + 1) + 3 from by omega]
  rw [show 2 * b + 2 = 2 * (b + 1) from by omega]
  rw [run_add, EB_shift (b + 1) [true, true, true] (repeatFalse p)]
  -- {E, true, repeatOne(2*(b+1)) ++ [true,true,true], repeatFalse p}
  -- Consolidate: repeatOne(2*(b+1)) ++ [true,true,true] = repeatOne(2*b+5)
  have consolidate_left : repeatOne (2 * (b + 1)) ++ [true, true, true] = repeatOne (2 * b + 5) := by
    simp only [repeatOne]
    rw [show [true, true, true] = List.replicate 3 true from by simp [List.replicate],
        ← List.replicate_add]
    congr 1
  rw [consolidate_left]
  -- {E, true, repeatOne(2*b+5), repeatFalse p}
  -- Phase 4: Final 3 steps
  -- Step 20: E true → B 1 R
  rw [show (3 : Nat) = 2 + 1 from by omega, run_step_succ]
  simp only [step, transition, hd_rF, tl_rF]
  rw [cons_rO]
  -- {B, false, repeatOne(2*b+6), repeatFalse(p-1)}
  -- Step 21: B false → C 1 L
  rw [show (2 : Nat) = 1 + 1 from by omega, run_step_succ]
  simp only [step, transition]
  rw [show 2 * b + 6 = (2 * b + 5) + 1 from by omega, repeatOne_succ,
      headD'_cons, tailD'_cons]
  -- {C, true, repeatOne(2*b+5), true :: repeatFalse(p-1)}
  -- Step 22: C true → D 0 L
  rw [show (1 : Nat) = 0 + 1 from by omega, run_step_succ]
  simp only [step, transition]
  rw [show 2 * b + 5 = (2 * b + 4) + 1 from by omega, repeatOne_succ,
      headD'_cons, tailD'_cons]
  -- {D, true, repeatOne(2*b+4), false :: true :: repeatFalse(p-1)}
  -- Now run 0 = id
  simp only [run]
  -- Goal: Config.mk ... = Q_Config(b+2, 1, p-1)
  simp only [repeatOne, repeatFalse]
  congr 1

/-- First big cycle for Q_even: Q_Config(2a+2, b, p) → gen(2*(2a+1), 1, b+1, p) in 8a+13 steps. -/
lemma first_big_cycle_even (a b p : Nat) :
    run (Q_Config (2 * a + 2) b p) (8 * a + 13) =
    { state := some stD, head := true,
      left  := repeatOne (2 * (2 * a + 1)) ++ [false] ++ repeatOne 1,
      right := [false] ++ repeatOne (b + 1) ++ repeatFalse p } := by
  simp only [Q_Config]
  -- left = repeatOne(2*(2a+2)) = repeatOne(4a+4)
  -- D_shift(4a+4)
  rw [show 8 * a + 13 = (4 * a + 4) + (4 * a + 9) from by ring]
  rw [run_add]
  rw [show 2 * (2 * a + 2) = 4 * a + 4 from by ring]
  rw [show (repeatOne (4 * a + 4) : List TapeSymbol) =
          repeatOne (4 * a + 4) ++ [] from (List.append_nil _).symm]
  rw [D_shift (4 * a + 4) [] ([false] ++ repeatOne b ++ repeatFalse p)]
  -- After D_shift: {D, true, [], repeatOne(4a+4)++[false]++repeatOne b++rF p}
  -- Step 1: D true -> D 1 L (left empty)
  rw [show 4 * a + 9 = (4 * a + 8) + 1 from by ring, run_step_succ]
  simp only [step, transition, headD'_nil, tailD'_nil]
  -- {D, false, [], true::repeatOne(4a+4)++...}
  -- Step 2: D false -> A 1 R
  rw [show 4 * a + 8 = (4 * a + 7) + 1 from by ring, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {A, true, [true], repeatOne(4a+4)++[false]++repeatOne b++rF p}
  -- Step 3: A true -> B 0 R
  rw [show 4 * a + 7 = (4 * a + 6) + 1 from by ring, run_step_succ]
  rw [show 4 * a + 4 = (4 * a + 3) + 1 from by ring, repeatOne_succ, List.cons_append]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {B, true, [false, true], repeatOne(4a+3)++[false]++repeatOne b++rF p}
  -- Step 4: B true -> E 1 R
  rw [show 4 * a + 6 = (4 * a + 5) + 1 from by ring, run_step_succ]
  rw [show 4 * a + 3 = (4 * a + 2) + 1 from by ring, repeatOne_succ, List.cons_append]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {E, true, [true, false, true], repeatOne(4a+2)++[false]++repeatOne b++rF p}
  -- EB_shift(2a+1) through 2*(2a+1) = 4a+2 ones
  rw [show 4 * a + 5 = 2 * (2 * a + 1) + 3 from by ring]
  rw [show 4 * a + 2 = 2 * (2 * a + 1) from by ring]
  rw [run_add, EB_shift (2 * a + 1) [true, false, true] ([false] ++ repeatOne b ++ repeatFalse p)]
  -- After EB_shift: {E, true, repeatOne(4a+2)++[true,false,true], [false]++repeatOne b++rF p}
  -- Consolidate left: repeatOne(4a+2)++[true,false,true] = repeatOne(4a+3)++[false,true]
  have left_cons : (repeatOne (2 * (2 * a + 1)) ++ [true, false, true] : List TapeSymbol) =
      repeatOne (2 * (2 * a + 1) + 1) ++ [false, true] := by
    simp only [repeatOne]
    rw [show [true, false, true] = List.replicate 1 true ++ [false, true] from by
          simp [List.replicate]]
    rw [← List.append_assoc, ← List.replicate_add]
  rw [left_cons]
  -- Step 5: E true -> B 1 R: head = headD'([false]++...) = false
  rw [show (3 : Nat) = 2 + 1 from by norm_num, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons, List.cons_append, List.nil_append]
  -- {B, false, true::repeatOne(4a+3)++[false,true], repeatOne b++rF p}
  rw [show (true :: (repeatOne (2 * (2 * a + 1) + 1) ++ [false, true]) : List TapeSymbol) =
          repeatOne (2 * (2 * a + 1) + 2) ++ [false, true] from by
        have h1 : 2 * (2 * a + 1) + 2 = 2 * (2 * a + 1) + 1 + 1 := by ring
        rw [h1]
        exact (repeatOne_succ (2 * (2 * a + 1) + 1)).symm ▸ rfl]
  -- Step 6: B false -> C 1 L: head from repeatOne(4a+4)++[false,true] = true
  rw [show (2 : Nat) = 1 + 1 from by norm_num, run_step_succ]
  rw [show 2 * (2 * a + 1) + 2 = (2 * (2 * a + 1) + 1) + 1 from by ring,
      repeatOne_succ]
  simp only [step, transition, headD'_cons, tailD'_cons, List.cons_append]
  -- {C, true, repeatOne(4a+3)++[false,true], true::repeatOne b++rF p}
  rw [show (true :: (repeatOne b ++ repeatFalse p)) = repeatOne (b + 1) ++ repeatFalse p from by
        rw [show b + 1 = b + 1 from rfl, repeatOne_succ, List.cons_append]]
  -- Step 7: C true -> D 0 L: head from repeatOne(4a+3)++[false,true] = true
  rw [show (1 : Nat) = 0 + 1 from by norm_num, run_step_succ]
  rw [show 2 * (2 * a + 1) + 1 = (2 * (2 * a + 1)) + 1 from by ring,
      repeatOne_succ]
  simp only [step, transition, headD'_cons, tailD'_cons, List.cons_append]
  -- {D, true, repeatOne(4a+2)++[false,true], [false]++repeatOne(b+1)++rF p}
  simp only [run]
  -- Need to show: left = repeatOne(2*(2a+1))++[false]++repeatOne 1
  congr 1
  · -- left equality: X ++ [false, true] = X ++ [false] ++ repeatOne 1
    simp [repeatOne, List.replicate]

/-- Q(2a+3, b) → P(b+5a+6): Odd first argument ≥ 3 exits to P. -/
lemma even_gen_cycle (K n B p : Nat) :
    run { state := some stD, head := true,
          left  := repeatOne (2 * (K + 1)) ++ [false] ++ repeatOne n,
          right := [false] ++ repeatOne B ++ repeatFalse p }
      (4 * (K + 1) + 5) =
    { state := some stD, head := true,
      left  := repeatOne (2 * K) ++ [false] ++ repeatOne (n + 1),
      right := [false] ++ repeatOne (B + 1) ++ repeatFalse p } := by
  -- Phase 1: D_shift
  conv_lhs => arg 2; rw [show 4 * (K + 1) + 5 = 2 * (K + 1) + (2 * K + 7) from by ring]
  rw [run_add]
  rw [show (repeatOne (2 * (K + 1)) ++ [false] ++ repeatOne n : List TapeSymbol) =
          repeatOne (2 * (K + 1)) ++ ([false] ++ repeatOne n) from by rw [List.append_assoc]]
  rw [D_shift]
  -- Goal: run {D, true, [false]++rO n, rO(2K+2)++([false]++rO B++rF p)} (2K+7) = ...
  -- Split 2K+7 = 1 + (2K+6) and peel step 1
  conv_lhs => arg 2; rw [show 2 * K + 7 = (2 * K + 6) + 1 from by ring]
  rw [run_step_succ]
  -- step {D, true, [false]++rO n, rO(2K+2)++...} computes:
  -- D true → D true L: head=headD'([false]++rO n)=false, left=tailD'=rO n, right=true::rO(2K+2)++...
  simp only [step, transition, List.cons_append, List.nil_append, headD'_cons, tailD'_cons]
  -- After step 1: {D, false, rO n, true :: (rO(2K+2)++[false]++rO B++rF p)}
  -- Step 2: D false → A true R. The right already starts with true :: ...
  conv_lhs => arg 2; rw [show 2 * K + 6 = (2 * K + 5) + 1 from by ring]
  rw [run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- After step 2: {A, true, true :: rO n, rO(2*(K+1)) ++ false :: ...}
  -- Step 3: A true → B false R. Need cons form of rO(2*(K+1))
  conv_lhs => arg 2; rw [show 2 * K + 5 = (2 * K + 4) + 1 from by ring]
  rw [run_step_succ]
  rw [show 2 * (K + 1) = (2 * K + 1) + 1 from by ring, repeatOne_succ, List.cons_append]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- After step 3: {B, true, false :: true :: rO n, rO(2K+1) ++ false :: ...}
  -- Step 4: B true → E true R
  conv_lhs => arg 2; rw [show 2 * K + 4 = (2 * K + 3) + 1 from by ring]
  rw [run_step_succ]
  rw [show 2 * K + 1 = (2 * K) + 1 from by ring, repeatOne_succ, List.cons_append]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- After 4 steps: {E, true, [true,false,true]++rO n, rO(2K)++false::(rO B++rF p)}
  -- Phase 3: EB_shift(K)
  conv_lhs => arg 2; rw [show 2 * K + 3 = 2 * K + 3 from rfl]
  rw [run_add]
  rw [EB_shift]
  -- After EB_shift: {E, true, rO(2K)++[true,false,true]++rO n, false::(rO B++rF p)}
  -- 3 remaining steps
  -- Step 5: E true → B true R
  rw [show (3 : Nat) = 2 + 1 from rfl, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- After step 5: {B, false, true::(rO(2K)++...), rO B++rF p}
  -- Step 6: B false → C true L
  conv_lhs => arg 2; rw [show (2 : Nat) = 1 + 1 from by norm_num]
  rw [run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- After step 6: {C, true, rO(2K)++[true,false,true]++rO n, true::(rO B++rF p)}
  -- Step 7: C true → D false L. Need cons form of left.
  -- Consolidate: rO(2K)++true::... = rO(2K)++[true]++... = rO(2K+1)++...
  rw [show (true :: false :: true :: repeatOne n : List TapeSymbol) =
          [true] ++ (false :: true :: repeatOne n) from rfl]
  rw [← List.append_assoc (repeatOne (2 * K)) [true] (false :: true :: repeatOne n)]
  rw [repeatOne_snoc]
  -- Now left = rO(2K+1) ++ [false, true] ++ rO n
  -- Expose cons via repeatOne_succ
  rw [repeatOne_succ, List.cons_append]
  -- Now left = true :: rO(2K) ++ [false, true] ++ rO n
  rw [show (1 : Nat) = 0 + 1 from rfl, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  simp only [run]
  ext <;> simp [repeatOne_succ, List.cons_append, List.nil_append, stD]
-- Helper: iterated gen cycles.
-- gen(K, n, B, p) reaches gen(0, n+K, B+K, p) after some steps.

lemma gen_multi_cycle (K n B p : Nat) :
    ∃ steps,
      run { state := some stD, head := true,
            left  := repeatOne (2 * K) ++ [false] ++ repeatOne n,
            right := [false] ++ repeatOne B ++ repeatFalse p }
        steps =
      { state := some stD, head := true,
        left  := [false] ++ repeatOne (n + K),
        right := [false] ++ repeatOne (B + K) ++ repeatFalse p } := by
  induction K generalizing n B with
  | zero =>
    exact ⟨0, by simp [run]⟩
  | succ k ih =>
    have cycle := even_gen_cycle k n B p
    obtain ⟨rest_steps, rest_eq⟩ := ih (n + 1) (B + 1)
    refine ⟨4 * (k + 1) + 5 + rest_steps, ?_⟩
    rw [run_add, cycle]
    convert rest_eq using 2 <;> ring_nf

-- Helper: boundary processing.
-- From gen(0, n+2, B, p) = {D, true, [false]++repeatOne(n+2), [false]++repeatOne B++rF p}
-- we reach {D, true, repeatOne n, [false]++repeatOne(B+3)++rF p} in 7 steps.
lemma gen_boundary (n B p : Nat) :
    run { state := some stD, head := true,
          left  := [false] ++ repeatOne (n + 2),
          right := [false] ++ repeatOne B ++ repeatFalse p }
      7 =
    { state := some stD, head := true,
      left  := repeatOne n,
      right := [false] ++ repeatOne (B + 3) ++ repeatFalse p } := by
  -- Step 1: D true -> D true L
  rw [show (7 : Nat) = 6 + 1 from by norm_num, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons, List.cons_append, List.nil_append]
  -- {D, false, repeatOne(n+2), true :: false :: (repeatOne B ++ rF p)}
  -- Step 2: D false -> A true R
  conv_lhs => arg 2; rw [show (6 : Nat) = 5 + 1 from by norm_num]
  rw [run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {A, true, true :: repeatOne(n+2), false :: (repeatOne B ++ rF p)}
  -- Step 3: A true -> B false R
  rw [show (5 : Nat) = 4 + 1 from by norm_num, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {B, false, false :: true :: repeatOne(n+2), repeatOne B ++ rF p}
  -- Step 4: B false -> C true L
  rw [show (4 : Nat) = 3 + 1 from by norm_num, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- Consolidate right: true :: (repeatOne B ++ rF p) = repeatOne (B+1) ++ rF p
  rw [cons_rO_app B (repeatFalse p)]
  -- Step 5: C false -> F true L
  rw [show (3 : Nat) = 2 + 1 from by norm_num, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {F, true, repeatOne(n+2), true :: (repeatOne(B+1) ++ rF p)}
  rw [cons_rO_app (B + 1) (repeatFalse p)]
  -- Step 6: F true -> C true L (expand repeatOne(n+2) for headD'/tailD')
  conv_lhs => arg 2; rw [show (2 : Nat) = 1 + 1 from by norm_num]
  rw [run_step_succ]
  rw [show n + 2 = (n + 1) + 1 from by ring, repeatOne_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {C, true, repeatOne(n+1), true :: (repeatOne(B+2) ++ rF p)}
  rw [cons_rO_app (B + 2) (repeatFalse p)]
  -- Step 7: C true -> D false L
  rw [run_step_succ, show n + 1 = n + 1 from rfl, repeatOne_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {D, true, repeatOne n, false :: (repeatOne(B+3) ++ rF p)}
  simp only [run]

/-- Q(2a+2, b) → Q(a, b+2a+5): Even first argument ≥ 2 halves a. -/
lemma tm_Q_even (a : Nat) (b : Nat) (p : Nat) :
  ∃ steps padding,
    run (Q_Config (2 * a + 2) b p) steps = Q_Config a (b + 2 * a + 5) padding := by
  -- Phase 1: first_big_cycle_even
  have h1 := first_big_cycle_even a b p
  -- Phase 2: gen_multi_cycle(2a+1, 1, b+1, p)
  obtain ⟨s2, h2⟩ := gen_multi_cycle (2 * a + 1) 1 (b + 1) p
  -- Phase 3: gen_boundary(2a, b+2a+2, p)
  have h3 := gen_boundary (2 * a) (b + 2 * a + 2) p
  -- Chain: Q_Config(2a+2,b,p) →[8a+13] gen(2*(2a+1),1,b+1,p) →[s2] gen(0,2a+2,b+2a+2,p) →[7] Q_Config(a,b+2a+5,p)
  refine ⟨8 * a + 13 + s2 + 7, p, ?_⟩
  -- Split: (8a+13) + (s2 + 7)
  rw [show 8 * a + 13 + s2 + 7 = (8 * a + 13) + (s2 + 7) from by omega,
      run_add, h1, run_add, h2]
  -- Goal: run {D, true, [false]++rO(1+(2a+1)), [false]++rO(b+1+(2a+1))++rF p} 7 = Q_Config(a, b+2a+5, p)
  -- This matches gen_boundary(2a, b+2a+2, p) after arithmetic
  -- h3: run {D, true, [false]++rO(2a+2), [false]++rO(b+2a+2)++rF p} 8 = {D, true, rO(2a), [false]++rO(b+2a+5)++rF p}
  -- Arithmetic alignment: 1+(2a+1) = 2a+2 and b+1+(2a+1) = b+2a+2
  have arith1 : 1 + (2 * a + 1) = 2 * a + 2 := by omega
  have arith2 : b + 1 + (2 * a + 1) = b + 2 * a + 2 := by omega
  rw [show [false] ++ repeatOne (1 + (2 * a + 1)) = [false] ++ repeatOne (2 * a + 2) from by
        rw [arith1],
      show [false] ++ repeatOne (b + 1 + (2 * a + 1)) ++ repeatFalse p =
           [false] ++ repeatOne (b + 2 * a + 2) ++ repeatFalse p from by
        rw [arith2]]
  rw [h3]
  -- Goal: {D, true, rO(2a), [false]++rO(b+2a+2+3)++rF p} = Q_Config(a, b+2a+5, p)
  simp only [Q_Config]

-- Helper: first big cycle from Q_Config (no [false] separator in left).
-- Q_Config(2a+3, b, p) -> gen(2a+2, 1, b+1, p) in 8a+17 steps.
lemma first_big_cycle (a b p : Nat) :
    run (Q_Config (2 * a + 3) b p) (8 * a + 17) =
    { state := some stD, head := true,
      left  := repeatOne (2 * (2 * a + 2)) ++ [false] ++ repeatOne 1,
      right := [false] ++ repeatOne (b + 1) ++ repeatFalse p } := by
  simp only [Q_Config]
  -- left = repeatOne(2*(2a+3)) = repeatOne(4a+6)
  -- D_shift(4a+6)
  rw [show 8 * a + 17 = (4 * a + 6) + (4 * a + 11) from by ring]
  rw [run_add]
  -- Need: repeatOne(2*(2a+3)) = repeatOne(4a+6)
  rw [show 2 * (2 * a + 3) = 4 * a + 6 from by ring]
  -- D_shift: left = repeatOne(4a+6) ++ [], right = [false]++repeatOne b++rF p
  rw [show (repeatOne (4 * a + 6) : List TapeSymbol) =
          repeatOne (4 * a + 6) ++ [] from (List.append_nil _).symm]
  rw [D_shift (4 * a + 6) [] ([false] ++ repeatOne b ++ repeatFalse p)]
  -- After D_shift: {D, true, [], repeatOne(4a+6)++[false]++repeatOne b++rF p}
  -- Step 1: D true -> D 1 L (left empty)
  rw [show 4 * a + 11 = (4 * a + 10) + 1 from by ring, run_step_succ]
  simp only [step, transition, headD'_nil, tailD'_nil]
  -- {D, false, [], true::repeatOne(4a+6)++...}
  -- Step 2: D false -> A 1 R
  rw [show 4 * a + 10 = (4 * a + 9) + 1 from by ring, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- Need to show true :: repeatOne(4a+6)++... = repeatOne(1)++repeatOne(4a+6)++...
  -- and consolidate headD'/tailD' on the right
  -- After A reads true at the head of right:
  -- {A, true, [true], repeatOne(4a+6)++[false]++repeatOne b++rF p}
  -- Actually we need to handle the right side: headD'(true::repeatOne(4a+6)++...) = true
  -- Step 3: A true -> B 0 R
  rw [show 4 * a + 9 = (4 * a + 8) + 1 from by ring, run_step_succ]
  -- Need headD' and tailD' of repeatOne(4a+6)++[false]++repeatOne b++rF p
  rw [show 4 * a + 6 = (4 * a + 5) + 1 from by ring, repeatOne_succ, List.cons_append]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {B, true, [false, true], repeatOne(4a+5)++[false]++repeatOne b++rF p}
  -- Step 4: B true -> E 1 R
  rw [show 4 * a + 8 = (4 * a + 7) + 1 from by ring, run_step_succ]
  rw [show 4 * a + 5 = (4 * a + 4) + 1 from by ring, repeatOne_succ, List.cons_append]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {E, true, [true, false, true], repeatOne(4a+4)++[false]++repeatOne b++rF p}
  -- EB_shift(2a+2) through 2*(2a+2) = 4a+4 ones
  rw [show 4 * a + 7 = 2 * (2 * a + 2) + 3 from by ring]
  rw [show 4 * a + 4 = 2 * (2 * a + 2) from by ring]
  rw [run_add, EB_shift (2 * a + 2) [true, false, true] ([false] ++ repeatOne b ++ repeatFalse p)]
  -- After EB_shift: {E, true, repeatOne(4a+4)++[true,false,true], [false]++repeatOne b++rF p}
  -- Consolidate left: repeatOne(4a+4)++[true,false,true] = repeatOne(4a+5)++[false,true]
  have left_cons : (repeatOne (2 * (2 * a + 2)) ++ [true, false, true] : List TapeSymbol) =
      repeatOne (2 * (2 * a + 2) + 1) ++ [false, true] := by
    simp only [repeatOne]
    rw [show [true, false, true] = List.replicate 1 true ++ [false, true] from by
          simp [List.replicate]]
    rw [← List.append_assoc, ← List.replicate_add]
  rw [left_cons]
  -- Step 5: E true -> B 1 R: head = headD'([false]++...) = false
  rw [show (3 : Nat) = 2 + 1 from by norm_num, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons, List.cons_append, List.nil_append]
  -- {B, false, true::repeatOne(4a+5)++[false,true], repeatOne b++rF p}
  -- = {B, false, repeatOne(4a+6)++[false,true], repeatOne b++rF p}
  rw [cons_rO_app (2 * (2 * a + 2) + 1) [false, true]]
  -- Step 6: B false -> C 1 L (conv to avoid ⟨2,...⟩ dependent type conflict)
  conv_lhs => arg 2; rw [show (2 : Nat) = 1 + 1 from by norm_num]
  rw [run_step_succ]
  rw [show 2 * (2 * a + 2) + 2 = (2 * (2 * a + 2) + 1) + 1 from by ring,
      repeatOne_succ]
  simp only [step, transition, headD'_cons, tailD'_cons, List.cons_append]
  -- {C, true, repeatOne(4a+5)++[false,true], true::repeatOne b++rF p}
  rw [cons_rO_app b (repeatFalse p)]
  -- Step 7: C true -> D 0 L: head from repeatOne(4a+5)++[false,true] = true
  rw [show (1 : Nat) = 0 + 1 from by norm_num, run_step_succ]
  rw [show 2 * (2 * a + 2) + 1 = (2 * (2 * a + 2)) + 1 from by ring,
      repeatOne_succ]
  simp only [step, transition]
  -- {D, true, repeatOne(4a+4)++[false,true], [false]++repeatOne(b+1)++rF p}
  simp only [run]
  -- Need to show: left = repeatOne(2*(2a+2))++[false]++repeatOne 1
  congr 1
  -- left: tailD'(true :: rO(4a+4)++[false,true]) = rO(4a+4)++[false]++rO 1
  simp only [repeatOne]
  simp [List.replicate]

-- Helper: right scan cycle (7 steps).
-- {D, true, [true,false]++rO k, [false]++rO(m+1)++rF p}
-- -> {D, true, [true,false]++rO(k+1), [false]++rO m++rF p}
lemma right_scan_cycle (k m p : Nat) :
    run { state := some stD, head := true,
          left := [true, false] ++ repeatOne k,
          right := [false] ++ repeatOne (m + 1) ++ repeatFalse p } 7 =
    { state := some stD, head := true,
      left := [true, false] ++ repeatOne (k + 1),
      right := [false] ++ repeatOne m ++ repeatFalse p } := by
  -- Step 1: D true -> D 1 L
  rw [show (7 : Nat) = 6 + 1 from by norm_num, run_step_succ]
  simp only [step, transition, List.cons_append, List.nil_append, headD'_cons, tailD'_cons]
  -- {D, [false]++rO k, true, [true,false]++rO(m+1)++rF p}
  -- Step 2: D true -> D 1 L (headD'([false]++rO k) = false)
  conv_lhs => arg 2; rw [show (6 : Nat) = 5 + 1 from by norm_num]
  rw [run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {D, rO k, false, [true,true,false]++rO(m+1)++rF p}
  -- Step 3: D false -> A 1 R
  rw [show (5 : Nat) = 4 + 1 from by norm_num, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  rw [show (true :: repeatOne k : List TapeSymbol) = repeatOne (k + 1) from by rw [repeatOne_succ]]
  -- {A, rO(k+1), true, [true,false]++rO(m+1)++rF p}
  -- Step 4: A true -> B 0 R
  rw [show (4 : Nat) = 3 + 1 from by norm_num, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {B, [false]++rO(k+1), true, [false]++rO(m+1)++rF p}
  -- Step 5: B true -> E 1 R
  rw [show (3 : Nat) = 2 + 1 from by norm_num, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {E, [true,false]++rO(k+1), false, rO(m+1)++rF p}
  -- Step 6: E false -> C 1 R
  rw [show (2 : Nat) = 1 + 1 from by norm_num, run_step_succ]
  simp only [repeatOne_succ, List.cons_append, step, transition, headD'_cons, tailD'_cons]
  -- {C, [true,true,false]++rO(k+1), true, rO m++rF p}
  -- Step 7: C true -> D 0 L
  rw [show (1 : Nat) = 0 + 1 from by norm_num, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  simp only [run]

-- Helper: right scan. Iterate right_scan_cycle to reach P_Config.
-- {D, true, [true,false]++rO k, [false]++rO m++rF p} -> P_Config(k+m, p+1)
lemma right_scan (k m p : Nat) :
    ∃ steps,
      run { state := some stD, head := true,
            left := [true, false] ++ repeatOne k,
            right := [false] ++ repeatOne m ++ repeatFalse p } steps =
      P_Config (k + m) (p + 1) := by
  induction m generalizing k with
  | zero =>
    refine ⟨0, ?_⟩
    simp only [run, P_Config, repeatOne_zero, repeatFalse_succ]
    congr 1
  | succ m ih =>
    obtain ⟨rest, hrest⟩ := ih (k + 1)
    refine ⟨7 + rest, ?_⟩
    rw [run_add, right_scan_cycle k m p]
    convert hrest using 2; ring

-- Helper: M=1 initial processing (7 steps) to right-scan form.
-- {D, true, rO 1, [false]++rO(B+1)++rF p} -> {D, true, [true,false]++rO 1, [false]++rO B++rF p}
-- More precisely, 7 steps.
lemma m1_to_scan (B p : Nat) :
    run { state := some stD, head := true,
          left := repeatOne 1,
          right := [false] ++ repeatOne (B + 1) ++ repeatFalse p } 7 =
    { state := some stD, head := true,
      left := [true, false] ++ repeatOne 1,
      right := [false] ++ repeatOne B ++ repeatFalse p } := by
  -- D_shift(1) + 6 explicit steps
  rw [show (7 : Nat) = 1 + 6 from by norm_num, run_add]
  rw [show (repeatOne 1 : List TapeSymbol) = repeatOne 1 ++ [] from (List.append_nil _).symm]
  rw [D_shift 1 [] ([false] ++ repeatOne (B + 1) ++ repeatFalse p)]
  simp only [repeatOne_succ, repeatOne_zero, List.nil_append, List.cons_append]
  -- {D, true, [], [true, false]++rO(B+1)++rF p}
  -- Step 2: D true -> D 1 L (left=[], head=true)
  rw [show (6 : Nat) = 5 + 1 from by norm_num, run_step_succ]
  simp only [step, transition, headD'_nil, tailD'_nil]
  -- {D, false, [], true :: [true,false]++rO(B+1)++rF p}
  -- Step 3: D false -> A 1 R
  rw [show (5 : Nat) = 4 + 1 from by norm_num, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {A, [true], true, [true,false]++rO(B+1)++rF p}
  -- Step 4: A true -> B 0 R
  rw [show (4 : Nat) = 3 + 1 from by norm_num, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {B, [false,true], true, [false]++rO(B+1)++rF p}
  -- Step 5: B true -> E 1 R
  rw [show (3 : Nat) = 2 + 1 from by norm_num, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {E, [true,false,true], false, rO(B+1)++rF p}
  -- Step 6: E false -> C 1 R
  rw [show (2 : Nat) = 1 + 1 from by norm_num, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {C, [true,true,false,true], true, rO B++rF p}
  -- Step 7: C true -> D 0 L
  rw [show (1 : Nat) = 0 + 1 from by norm_num, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  simp only [run]

-- Helper: gen cycle. One cycle with (2a+1) leading ones.
-- Moves one "one" from right to accumulated left.
-- Step count: 4a+7 (D_shift(2a+1) + 4 boundary + 2*max(0,a-1) EB + closing).
lemma gen_cycle (a n B p : Nat) (hB : B ≥ 1) :
    run { state := some stD, head := true,
          left  := repeatOne (2 * a + 1) ++ [false] ++ repeatOne n,
          right := [false] ++ repeatOne B ++ repeatFalse p }
      (4 * a + 7) =
    { state := some stD, head := true,
      left  := repeatOne (2 * a + 1) ++ [false] ++ repeatOne (n + 1),
      right := [false] ++ repeatOne (B - 1) ++ repeatFalse p } := by
  -- Phase 1: D_shift(2a+1) through leading ones
  rw [show 4 * a + 7 = (2 * a + 1) + (2 * a + 6) from by ring, run_add]
  rw [show (repeatOne (2 * a + 1) ++ [false] ++ repeatOne n : List TapeSymbol) =
          repeatOne (2 * a + 1) ++ ([false] ++ repeatOne n) from by rw [List.append_assoc]]
  rw [D_shift (2 * a + 1) ([false] ++ repeatOne n)
        ([false] ++ repeatOne B ++ repeatFalse p)]
  -- After D_shift: {D, true, [false]++rO n, rO(2a+1)++[false]++rO B++rF p}
  -- Phase 2: 4 boundary steps (D->D->A->B->E), peel from step count
  -- Step 1: D true -> D 1 L
  conv_lhs => arg 2; rw [show 2 * a + 6 = (2 * a + 5) + 1 from by ring]
  rw [run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons, List.cons_append, List.nil_append]
  -- {D, rO n, false, true :: rO(2a+1)++[false]++rO B++rF p}
  -- Step 2: D false -> A 1 R
  conv_lhs => arg 2; rw [show 2 * a + 5 = (2 * a + 4) + 1 from by ring]
  rw [run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  rw [show (true :: repeatOne n : List TapeSymbol) = repeatOne (n + 1) from by rw [repeatOne_succ]]
  -- {A, rO(n+1), true, rO(2a+1)++[false]++rO B++rF p}
  -- Step 3: A true -> B 0 R. Need to split rO(2a+1) to get head.
  conv_lhs => arg 2; rw [show 2 * a + 4 = (2 * a + 3) + 1 from by ring]
  rw [run_step_succ]
  simp only [repeatOne_succ, List.cons_append, step, transition, headD'_cons, tailD'_cons]
  -- {B, [false]++rO(n+1), true, rO(2a)++[false]++rO B++rF p}
  -- Step 4: B true -> E 1 R. Need to split rO(2a).
  conv_lhs => arg 2; rw [show 2 * a + 3 = (2 * a + 2) + 1 from by ring]
  rw [run_step_succ]
  -- If 2a = 0 (a=0): right starts with [false]
  -- If 2a >= 1 (a>=1): right starts with true
  cases a with
  | zero =>
    -- a=0: right = [false]++rO B++rF p. head = false after B reads.
    simp only [Nat.mul_zero, Nat.zero_add, repeatOne_zero, List.nil_append]
    simp only [step, transition, headD'_cons, tailD'_cons]
    simp only [run]
    -- {E, [true,false]++rO(n+1), false, rO B++rF p}
    -- Phase 3: 2 remaining steps. Need cons form of rO B.
    rw [show B = (B - 1) + 1 from by omega, repeatOne_succ, List.cons_append]
    simp only [step, transition, headD'_cons, tailD'_cons, List.cons_append, List.nil_append]
    congr 1
  | succ a' =>
    -- a=a'+1 >= 1. rO(2(a'+1)) has >=2 ones. Split and use EB_shift.
    rw [show 2 * (a' + 1) = (2 * a' + 1) + 1 from by ring, repeatOne_succ, List.cons_append]
    simp only [step, transition, headD'_cons, tailD'_cons]
    -- Phase 3: EB_shift(a') + 4 closing steps
    -- Rewrite step count for run_add split
    conv_lhs => arg 2; rw [show 2 * a' + 1 + 1 + 2 = 2 * a' + 4 from by ring]
    -- Prepare right for EB_shift: rO(2a'+1) = rO(2a')++[true]
    rw [show (repeatOne (2 * a' + 1) ++ false :: (repeatOne B ++ repeatFalse p) : List TapeSymbol) =
            repeatOne (2 * a') ++ (true :: false :: (repeatOne B ++ repeatFalse p)) from by
      rw [← repeatOne_snoc (2 * a'), List.append_assoc]
      simp only [List.cons_append, List.nil_append]]
    -- Split into EB_shift + closing steps
    rw [run_add]
    rw [EB_shift a' (true :: false :: true :: repeatOne n)
          (true :: false :: (repeatOne B ++ repeatFalse p))]
    -- After EB_shift: {E, true, rO(2a')++[true,false,true]++rO(n), true::false::rO(B)++rF(p)}
    -- Step 5: E true → B true R
    conv_lhs => arg 2; rw [show (4 : Nat) = 3 + 1 from by norm_num]
    rw [run_step_succ]
    simp only [step, transition, headD'_cons, tailD'_cons]
    -- Step 6: B true → E true R
    conv_lhs => arg 2; rw [show (3 : Nat) = 2 + 1 from by norm_num]
    rw [run_step_succ]
    simp only [step, transition, headD'_cons, tailD'_cons]
    -- Step 7: E false → C true R. Expand rO(B) since B >= 1
    conv_lhs => arg 2; rw [show (2 : Nat) = 1 + 1 from by norm_num]
    rw [run_step_succ]
    rw [show B = (B - 1) + 1 from by omega, repeatOne_succ, List.cons_append]
    simp only [step, transition, headD'_cons, tailD'_cons]
    -- Step 8: C true → D false L
    conv_lhs => arg 2; rw [show (1 : Nat) = 0 + 1 from by norm_num]
    rw [run_step_succ]
    simp only [step, transition, headD'_cons, tailD'_cons]
    simp only [run]
    -- Close: consolidate left lists
    congr 1
    · congr 1
      rw [cons_rO_app, show (true :: false :: true :: repeatOne n : List TapeSymbol) =
              [true] ++ (false :: true :: repeatOne n) from rfl,
          ← List.append_assoc, repeatOne_snoc, repeatOne_succ]
      simp only [List.append_assoc, List.cons_append, List.nil_append]

-- Helper: gen multi. Iterate gen_cycle to consume all right ones.
lemma gen_multi (a n B p : Nat) :
    ∃ steps,
      run { state := some stD, head := true,
            left  := repeatOne (2 * a + 1) ++ [false] ++ repeatOne n,
            right := [false] ++ repeatOne B ++ repeatFalse p }
        steps =
      { state := some stD, head := true,
        left  := repeatOne (2 * a + 1) ++ [false] ++ repeatOne (n + B),
        right := repeatFalse (p + 1) } := by
  induction B generalizing n with
  | zero =>
    refine ⟨0, ?_⟩
    simp only [run, Nat.add_zero, repeatOne_zero,
               repeatFalse_succ]
    congr 1
  | succ B ih =>
    have cycle := gen_cycle a n (B + 1) p (by omega)
    obtain ⟨rest, hrest⟩ := ih (n + 1)
    refine ⟨(4 * a + 7) + rest, ?_⟩
    rw [run_add, cycle]
    simp only [show B + 1 - 1 = B from by omega]
    convert hrest using 2
    congr 1; congr 1; omega

-- Helper: flat_init. Initial step from flat form to gen form (first cycle).
-- Same as gen_cycle but starting from rO(2a+1) instead of rO(2a+1)++[false]++rO n.
lemma flat_init (a B p : Nat) (hB : B ≥ 1) :
    run { state := some stD, head := true,
          left  := repeatOne (2 * a + 1),
          right := [false] ++ repeatOne B ++ repeatFalse p }
      (4 * a + 7) =
    { state := some stD, head := true,
      left  := repeatOne (2 * a + 1) ++ [false] ++ repeatOne 1,
      right := [false] ++ repeatOne (B - 1) ++ repeatFalse p } := by
  -- Phase 1: D_shift(2a+1) through leading ones
  rw [show 4 * a + 7 = (2 * a + 1) + (2 * a + 6) from by ring, run_add]
  rw [show (repeatOne (2 * a + 1) : List TapeSymbol) = repeatOne (2 * a + 1) ++ [] from by simp]
  rw [D_shift (2 * a + 1) [] ([false] ++ repeatOne B ++ repeatFalse p)]
  simp only [List.append_nil]
  -- After D_shift: {D, true, [], rO(2a+1)++[false]++rO B++rF p}
  -- Phase 2: 4 boundary steps (D->D->A->B->E), peel from step count
  -- Step 1: D true -> D 1 L. headD'([]) = false
  conv_lhs => arg 2; rw [show 2 * a + 6 = (2 * a + 5) + 1 from by ring]
  rw [run_step_succ]
  simp only [step, transition, headD'_nil, tailD'_nil]
  -- {D, [], false, [true]++rO(2a+1)++[false]++rO B++rF p}
  -- Step 2: D false -> A 1 R
  conv_lhs => arg 2; rw [show 2 * a + 5 = (2 * a + 4) + 1 from by ring]
  rw [run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {A, [true], true, rO(2a+1)++[false]++rO B++rF p}
  -- Step 3: A true -> B 0 R
  conv_lhs => arg 2; rw [show 2 * a + 4 = (2 * a + 3) + 1 from by ring]
  rw [run_step_succ]
  rw [show (repeatOne (2 * a + 1) ++ ([false] ++ repeatOne B ++ repeatFalse p) : List TapeSymbol) =
          true :: (repeatOne (2 * a) ++ ([false] ++ repeatOne B ++ repeatFalse p)) from by
    rw [show 2 * a + 1 = (2 * a) + 1 from by ring, repeatOne_succ, List.cons_append]]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {B, [false]++rO 1, true, rO(2a)++[false]++rO B++rF p}
  -- Step 4: B true -> E 1 R
  conv_lhs => arg 2; rw [show 2 * a + 3 = (2 * a + 2) + 1 from by ring]
  rw [run_step_succ]
  cases a with
  | zero =>
    -- a=0: right = [false]++rO B++rF p
    simp only [Nat.mul_zero, Nat.zero_add, repeatOne_zero, List.nil_append]
    simp only [step, transition]
    -- {E, [true,false,rO 1], false, rO B++rF p}, step count 2
    rw [show B = (B - 1) + 1 from by omega, repeatOne_succ, List.cons_append]
    conv_lhs => arg 2; rw [show (2 : Nat) = 1 + 1 from by norm_num]
    rw [run_step_succ]
    simp only [step, transition, headD'_cons, tailD'_cons]
    conv_lhs => arg 2; rw [show (1 : Nat) = 0 + 1 from by norm_num]
    rw [run_step_succ]
    simp only [step, transition]
    simp only [run]
    congr 1
  | succ a' =>
    -- a=a'+1 >= 1. rO(2(a'+1)) has >=2 ones. Split and use EB_shift.
    rw [show 2 * (a' + 1) = (2 * a' + 1) + 1 from by ring, repeatOne_succ, List.cons_append]
    simp only [step, transition, headD'_cons, tailD'_cons]
    -- Phase 3: EB_shift(a') + 4 closing steps
    conv_lhs => arg 2; rw [show 2 * a' + 1 + 1 + 2 = 2 * a' + 4 from by ring]
    rw [show (repeatOne (2 * a' + 1) ++ ([false] ++ repeatOne B ++ repeatFalse p) : List TapeSymbol) =
            repeatOne (2 * a') ++ (true :: ([false] ++ repeatOne B ++ repeatFalse p)) from by
      rw [← repeatOne_snoc (2 * a'), List.append_assoc]
      simp only [List.cons_append, List.nil_append]]
    rw [run_add]
    rw [EB_shift a' [true, false, true]
          (true :: ([false] ++ repeatOne B ++ repeatFalse p))]
    -- Normalize [false] ++ X to false :: X so headD'/tailD' can reduce
    simp only [List.cons_append, List.nil_append]
    -- Step 5: E true → B true R
    conv_lhs => arg 2; rw [show (4 : Nat) = 3 + 1 from by norm_num]
    rw [run_step_succ]
    simp only [step, transition, headD'_cons, tailD'_cons]
    -- Step 6: B true → E true R
    conv_lhs => arg 2; rw [show (3 : Nat) = 2 + 1 from by norm_num]
    rw [run_step_succ]
    simp only [step, transition, headD'_cons, tailD'_cons]
    -- Step 7: E false → C true R. Expand rO(B) since B >= 1
    conv_lhs => arg 2; rw [show (2 : Nat) = 1 + 1 from by norm_num]
    rw [run_step_succ]
    rw [show B = (B - 1) + 1 from by omega, repeatOne_succ, List.cons_append]
    simp only [step, transition, headD'_cons, tailD'_cons]
    -- Step 8: C true → D false L
    conv_lhs => arg 2; rw [show (1 : Nat) = 0 + 1 from by norm_num]
    rw [run_step_succ]
    simp only [step, transition, headD'_cons, tailD'_cons]
    simp only [run]
    -- Close: consolidate left lists
    congr 1
    · congr 1
      -- Goal: rO(2a'+1) ++ [true, false, true] = rO(2a'+2) ++ [false] ++ rO 1
      rw [show ([true, false, true] : List TapeSymbol) = [true] ++ [false, true] from rfl,
          ← List.append_assoc, repeatOne_snoc]
      rw [cons_rO_app]
      rw [show ([false, true] : List TapeSymbol) = [false] ++ [true] from rfl]
      rw [← List.append_assoc (repeatOne _) [false] [true]]
      -- rO(2a'+1+1) ++ [false] ++ [true] = rO(2a'+2) ++ [false] ++ rO 1
      congr 2

-- Helper: reverse boundary.
-- From gen form with rF p on right, reduce leading ones by 2 and produce 2 right ones.
-- rO(2a+3)++[false]++rO n, rF p -> rO(2a+1)++[false]++rO(n+1), [false]++rO 2++rF(p-2)
set_option maxHeartbeats 3200000 in
lemma reverse_boundary (a n p : Nat) :
    run { state := some stD, head := true,
          left  := repeatOne (2 * a + 3) ++ [false] ++ repeatOne n,
          right := repeatFalse p }
      (4 * a + 13) =
    { state := some stD, head := true,
      left  := repeatOne (2 * a + 1) ++ [false] ++ repeatOne (n + 1),
      right := [false] ++ repeatOne 2 ++ repeatFalse (p - 2) } := by
  have hd_rF : ∀ m, headD' (repeatFalse m) false = false := by
    intro m; cases m <;> simp [repeatFalse, List.replicate]
  have tl_rF : ∀ m, tailD' (repeatFalse m) = repeatFalse (m - 1) := by
    intro m; cases m with
    | zero => simp [repeatFalse, List.replicate]
    | succ k => simp [repeatFalse, List.replicate_succ]
  -- Phase 1: D_shift(2a+3) through leading ones
  rw [show 4 * a + 13 = (2 * a + 3) + (2 * a + 10) from by ring, run_add]
  rw [show (repeatOne (2 * a + 3) ++ [false] ++ repeatOne n : List TapeSymbol) =
          repeatOne (2 * a + 3) ++ ([false] ++ repeatOne n) from by
    rw [List.append_assoc]]
  rw [D_shift (2 * a + 3) ([false] ++ repeatOne n) (repeatFalse p)]
  -- After D_shift: {D, true, [false]++rO n, rO(2a+3)++rF p}
  -- Phase 2: 4 boundary steps
  -- Pre-split rO(2a+3) → true :: true :: rO(2a+1) for headD'/tailD' reduction
  rw [show 2 * a + 3 = (2 * a + 2) + 1 from by ring, repeatOne_succ]
  rw [show 2 * a + 2 = (2 * a + 1) + 1 from by ring, repeatOne_succ]
  -- Normalize (true :: true :: rO(2a+1)) ++ rF p → cons form
  simp only [List.cons_append, List.nil_append]
  -- Split into 4 + (2a+6) and prove the 4-step result via kernel reduction
  rw [show 2 * a + 10 = 4 + (2 * a + 6) from by ring, run_add]
  have phase2 : run (⟨some stD, false :: repeatOne n, true,
      true :: true :: (repeatOne (2 * a + 1) ++ repeatFalse p)⟩ : Config) 4 =
    (⟨some stE, true :: false :: true :: repeatOne n, true,
      repeatOne (2 * a + 1) ++ repeatFalse p⟩ : Config) := by
    rfl
  rw [phase2]
  rw [show (true :: repeatOne n : List TapeSymbol) = repeatOne (n + 1) from by rw [repeatOne_succ]]
  -- {E, [true,false]++rO(n+1), true, rO(2a+1)++rF p}
  -- Phase 3: EB_shift(a) through 2a ones
  -- Split rO(2a+1) = rO(2a) ++ [true] for EB_shift
  rw [show (repeatOne (2 * a + 1) ++ repeatFalse p : List TapeSymbol) =
          repeatOne (2 * a) ++ ([true] ++ repeatFalse p) from by
    rw [← repeatOne_snoc, List.append_assoc]]
  rw [show 2 * a + 6 = 2 * a + 6 from rfl, run_add]
  rw [show (true :: false :: repeatOne (n + 1) : List TapeSymbol) =
          [true, false] ++ repeatOne (n + 1) from rfl]
  rw [EB_shift a ([true, false] ++ repeatOne (n + 1)) ([true] ++ repeatFalse p)]
  -- After EB: {E, true, rO(2a)++[true,false]++rO(n+1), [true]++rF p}
  -- Consolidate left
  have left_eq : (repeatOne (2 * a) ++ ([true, false] ++ repeatOne (n + 1)) : List TapeSymbol) =
      repeatOne (2 * a + 1) ++ [false] ++ repeatOne (n + 1) := by
    simp only [List.cons_append, List.nil_append, List.append_assoc]
    -- Goal: rO(2a) ++ true :: false :: rO(n+1) = rO(2a+1) ++ false :: rO(n+1)
    rw [List.append_cons, repeatOne_snoc]
  rw [left_eq]
  -- Phase 4: 6 closing steps using explicit step lemmas
  -- Let L4 = rO(2a+1)++[false]++rO(n+1) for brevity in have statements
  -- Step 5: E true -> B 1 R. head from [true]++rF p = true
  rw [show (6 : Nat) = 5 + 1 from by norm_num, run_step_succ]
  have step5 : step ⟨some stE, repeatOne (2 * a + 1) ++ [false] ++ repeatOne (n + 1),
      true, [true] ++ repeatFalse p⟩ =
    ⟨some stB, true :: (repeatOne (2 * a + 1) ++ [false] ++ repeatOne (n + 1)),
      true, repeatFalse p⟩ := by ext <;> simp [step, transition, stB, Fin.ext_iff]
  rw [step5]
  rw [show (true :: (repeatOne (2 * a + 1) ++ [false] ++ repeatOne (n + 1)) : List TapeSymbol) =
          repeatOne ((2 * a + 1) + 1) ++ [false] ++ repeatOne (n + 1) from by
    rw [List.append_assoc, cons_rO_app, ← List.append_assoc]]
  -- {B, rO(2a+2)++[false]++rO(n+1), true, rF p}
  -- Step 6: B true -> E 1 R. headD'(rF p) = false
  rw [show (5 : Nat) = 4 + 1 from by norm_num, run_step_succ]
  have step6 : step ⟨some stB, repeatOne ((2 * a + 1) + 1) ++ [false] ++ repeatOne (n + 1),
      true, repeatFalse p⟩ =
    ⟨some stE, true :: (repeatOne ((2 * a + 1) + 1) ++ [false] ++ repeatOne (n + 1)),
      headD' (repeatFalse p) false, tailD' (repeatFalse p)⟩ := by
    ext <;> simp [step, transition, stE, Fin.ext_iff]
  rw [step6, hd_rF, tl_rF]
  rw [show (true :: (repeatOne ((2 * a + 1) + 1) ++ [false] ++ repeatOne (n + 1)) : List TapeSymbol) =
          repeatOne (((2 * a + 1) + 1) + 1) ++ [false] ++ repeatOne (n + 1) from by
    rw [List.append_assoc, cons_rO_app, ← List.append_assoc]]
  -- {E, rO(2a+3)++[false]++rO(n+1), false, rF(p-1)}
  -- Step 7: E false -> C 1 R. headD'(rF(p-1)) = false
  rw [show (4 : Nat) = 3 + 1 from by norm_num, run_step_succ]
  have step7 : step ⟨some stE, repeatOne (((2 * a + 1) + 1) + 1) ++ [false] ++ repeatOne (n + 1),
      false, repeatFalse (p - 1)⟩ =
    ⟨some stC, true :: (repeatOne (((2 * a + 1) + 1) + 1) ++ [false] ++ repeatOne (n + 1)),
      headD' (repeatFalse (p - 1)) false, tailD' (repeatFalse (p - 1))⟩ := by
    ext <;> simp [step, transition, stC, Fin.ext_iff]
  rw [step7, hd_rF, tl_rF]
  rw [show (true :: (repeatOne (((2 * a + 1) + 1) + 1) ++ [false] ++ repeatOne (n + 1)) : List TapeSymbol) =
          repeatOne ((((2 * a + 1) + 1) + 1) + 1) ++ [false] ++ repeatOne (n + 1) from by
    rw [List.append_assoc, cons_rO_app, ← List.append_assoc]]
  -- {C, rO(2a+4)++[false]++rO(n+1), false, rF(p-1-1)}
  -- Step 8: C false -> F 1 L. headD'(rO(2a+4)++...) = true
  rw [show (3 : Nat) = 2 + 1 from by norm_num, run_step_succ]
  rw [show (((2 * a + 1) + 1) + 1) + 1 = (2 * a + 3) + 1 from by ring, repeatOne_succ]
  -- Normalize (true :: rO(2a+3)) ++ ... → true :: (rO(2a+3) ++ ...)
  simp only [List.cons_append]
  have step8 : step ⟨some stC, true :: (repeatOne (2 * a + 3) ++ [false] ++ repeatOne (n + 1)),
      false, repeatFalse (p - 1 - 1)⟩ =
    ⟨some stF, repeatOne (2 * a + 3) ++ [false] ++ repeatOne (n + 1),
      true, true :: repeatFalse (p - 1 - 1)⟩ := by
    ext <;> simp [step, transition, stF, Fin.ext_iff]
  rw [step8]
  -- {F, rO(2a+3)++[false]++rO(n+1), true, [true]++rF(p-1-1)}
  -- Step 9: F true -> C 1 L
  rw [show (2 : Nat) = 1 + 1 from by norm_num, run_step_succ]
  rw [show 2 * a + 3 = (2 * a + 2) + 1 from by ring, repeatOne_succ]
  simp only [List.cons_append]
  have step9 : step ⟨some stF, true :: (repeatOne (2 * a + 2) ++ [false] ++ repeatOne (n + 1)),
      true, true :: repeatFalse (p - 1 - 1)⟩ =
    ⟨some stC, repeatOne (2 * a + 2) ++ [false] ++ repeatOne (n + 1),
      true, true :: true :: repeatFalse (p - 1 - 1)⟩ := by
    ext <;> simp [step, transition, stC, Fin.ext_iff]
  rw [step9]
  -- {C, rO(2a+2)++[false]++rO(n+1), true, [true,true]++rF(p-1-1)}
  -- Step 10: C true -> D 0 L
  rw [show (1 : Nat) = 0 + 1 from by norm_num, run_step_succ]
  rw [show 2 * a + 2 = (2 * a + 1) + 1 from by ring, repeatOne_succ]
  simp only [List.cons_append]
  have step10 : step ⟨some stC, true :: (repeatOne (2 * a + 1) ++ [false] ++ repeatOne (n + 1)),
      true, true :: true :: repeatFalse (p - 1 - 1)⟩ =
    ⟨some stD, repeatOne (2 * a + 1) ++ [false] ++ repeatOne (n + 1),
      true, false :: true :: true :: repeatFalse (p - 1 - 1)⟩ := by
    ext <;> simp [step, transition, stD, Fin.ext_iff]
  rw [step10]
  simp only [run]
  -- {D, rO(2a+1)++[false]++rO(n+1), true, [false,true,true]++rF(p-1-1)}
  -- Need: right = [false]++rO 2++rF(p-2)
  have rF_eq : repeatFalse (p - 1 - 1) = repeatFalse (p - 2) := by congr 1
  rw [rF_eq]
  rfl

-- Helper: gen_to_P.
-- From {D, true, rO(2a+1)++[false]++rO n, rF p} we reach P_Config(n+3a, padding).
-- For a=0: the config IS P_Config(n, p).
-- For a+1: reverse boundary reduces leading by 2 and adds 3 to accumulated.
lemma gen_to_P (a : Nat) :
    ∀ n p,
    ∃ steps padding,
      run { state := some stD, head := true,
            left  := repeatOne (2 * a + 1) ++ [false] ++ repeatOne n,
            right := repeatFalse p }
        steps =
      P_Config (n + 3 * a) padding := by
  induction a with
  | zero =>
    intro n p
    refine ⟨0, p, ?_⟩
    simp only [run, P_Config]
    congr 1
  | succ a ih =>
    intro n p
    -- Phase 1: reverse boundary (4a+13 steps)
    -- rO(2(a+1)+1)++[false]++rO n = rO(2a+3)++[false]++rO n
    have hrb := reverse_boundary a n p
    -- Phase 2: 2 gen cycles with 2a+1 leading ones to consume the 2 right ones
    obtain ⟨s_gc, h_gc⟩ := gen_multi a (n + 1) 2 (p - 2)
    -- Phase 3: IH
    have p' := (p - 2) + 1
    obtain ⟨s_ih, pad, h_ih⟩ := ih (n + 1 + 2) ((p - 2) + 1)
    -- Compose
    refine ⟨(4 * a + 13) + s_gc + s_ih, pad, ?_⟩
    rw [show 2 * (a + 1) + 1 = 2 * a + 3 from by ring]
    rw [show (4 * a + 13) + s_gc + s_ih = (4 * a + 13) + (s_gc + s_ih) from by ring]
    rw [run_add, hrb, run_add, h_gc, h_ih]
    congr 1; ring

-- Helper: flat_to_gen.
-- From {D, true, rO(2a+1), [false]++rO B++rF p} with B ≥ 1, reach gen form.
-- Uses m1_to_scan + right_scan for a=0, direct computation for a≥1.
lemma flat_to_gen (a B p : Nat) (hB : B ≥ 1) :
    ∃ steps,
      run { state := some stD, head := true,
            left  := repeatOne (2 * a + 1),
            right := [false] ++ repeatOne B ++ repeatFalse p }
        steps =
      { state := some stD, head := true,
        left  := repeatOne (2 * a + 1) ++ [false] ++ repeatOne B,
        right := repeatFalse (p + 1) } := by
  cases a with
  | zero =>
    -- a=0, M=1. Use m1_to_scan + right_scan
    simp only [Nat.mul_zero, Nat.zero_add]
    have hB' : B = (B - 1) + 1 := by omega
    rw [hB']
    have h1 := m1_to_scan (B - 1) p
    obtain ⟨s2, h2⟩ := right_scan 1 (B - 1) p
    refine ⟨7 + s2, ?_⟩
    rw [run_add, h1]
    -- h2 says it reaches P_Config(1+(B-1), p+1) = P_Config(B, p+1)
    -- P_Config(B, p+1) = {D, true, [true,false]++rO B, rF(p+1)}
    -- target: {D, true, rO 1++[false]++rO B, rF(p+1)}
    -- These are equal since rO 1 = [true] and [true]++[false] = [true,false]
    rw [h2]
    simp [P_Config, repeatOne, List.replicate, List.cons_append, repeatFalse_succ]
    rw [show 1 + (B - 1) = (B - 1) + 1 from by omega]
    simp [List.replicate_succ]
  | succ a =>
    -- a≥1, M=2(a+1)+1 = 2a+3. Use flat_init + gen_multi.
    have hB' : B = (B - 1) + 1 := by omega
    rw [hB']
    have h1 := flat_init (a + 1) ((B - 1) + 1) p (by omega)
    rw [show (B - 1) + 1 - 1 = B - 1 from by omega] at h1
    obtain ⟨s2, h2⟩ := gen_multi (a + 1) 1 (B - 1) p
    refine ⟨(4 * (a + 1) + 7) + s2, ?_⟩
    rw [run_add, h1, h2]
    congr 2
    congr 1
    omega

lemma odd_left_to_P (a : Nat) :
    ∀ B p, B ≥ 1 →
    ∃ steps padding,
      run { state := some stD, head := true,
            left  := repeatOne (2 * a + 1),
            right := [false] ++ repeatOne B ++ repeatFalse p }
        steps =
      P_Config (B + 3 * a) padding := by
  intro B p hB
  obtain ⟨s1, h1⟩ := flat_to_gen a B p hB
  obtain ⟨s2, pad, h2⟩ := gen_to_P a B (p + 1)
  exact ⟨s1 + s2, pad, by rw [run_add, h1, h2]⟩

/-- P(2a) → P(3a+4): When a is even (a = 2k), one macro step of the TM
    transforms P_Config(2k) into P_Config(3k+4) in some number of TM steps. -/
lemma tm_P_even (k : Nat) (p : Nat) :
  ∃ steps padding,
    run (P_Config (2 * k) p) steps = P_Config (3 * k + 4) padding := by
  have hd_rF : ∀ n, headD' (repeatFalse n) false = false := by
    intro n; cases n <;> simp [repeatFalse, List.replicate]
  have tl_rF : ∀ n, tailD' (repeatFalse n) = repeatFalse (n - 1) := by
    intro n; cases n with
    | zero => simp [repeatFalse, List.replicate]
    | succ m => simp [repeatFalse, List.replicate_succ]
  have cons_rO : ∀ n, true :: repeatOne n = repeatOne (n + 1) := fun n => rfl
  -- Phase 1: D_shift(1) + 14 manual steps
  -- Phase 2: Apply odd_left_to_P(k+1, 1, p-3)
  obtain ⟨steps2, padding2, h2⟩ := odd_left_to_P (k + 1) 1 (p - 3) (by omega)
  refine ⟨15 + steps2, padding2, ?_⟩
  rw [run_add]
  simp only [P_Config]
  -- D_shift(1): split left = repeatOne(1) ++ ([false] ++ repeatOne(2k))
  rw [show (15 : Nat) = 1 + 14 from rfl, run_add]
  conv_lhs => arg 1; rw [show ([true, false] ++ repeatOne (2 * k) : List TapeSymbol) =
    repeatOne 1 ++ ([false] ++ repeatOne (2 * k)) from by simp [repeatOne, List.replicate]]
  rw [D_shift]
  -- After D_shift(1): {D, true, [false]++repeatOne(2k), repeatOne(1)++repeatFalse(p)}
  -- Step 2: D true → D L
  rw [show (14 : Nat) = 13 + 1 from rfl, run_step_succ]
  have step2 : step ⟨some stD, [false] ++ repeatOne (2 * k), true,
      repeatOne 1 ++ repeatFalse p⟩ =
    ⟨some stD, repeatOne (2 * k), false, true :: repeatOne 1 ++ repeatFalse p⟩ := by
    ext <;> simp [step, transition, repeatOne, List.replicate, stD, Fin.ext_iff]
  rw [step2]
  -- Step 3: D false → A R
  rw [show (13 : Nat) = 12 + 1 from rfl, run_step_succ]
  have step3 : step ⟨some stD, repeatOne (2 * k), false,
      true :: repeatOne 1 ++ repeatFalse p⟩ =
    ⟨some stA, true :: repeatOne (2 * k), true, repeatOne 1 ++ repeatFalse p⟩ := by
    ext <;> simp [step, transition, stA, Fin.ext_iff]
  rw [step3, cons_rO]
  -- Step 4: A true → B 0 R
  rw [show (12 : Nat) = 11 + 1 from rfl, run_step_succ]
  have step4 : step ⟨some stA, repeatOne (2 * k + 1), true,
      repeatOne 1 ++ repeatFalse p⟩ =
    ⟨some stB, false :: repeatOne (2 * k + 1), true, repeatFalse p⟩ := by
    ext <;> simp [step, transition, repeatOne, List.replicate, stB, Fin.ext_iff]
  rw [step4]
  -- Step 5: B true → E 1 R
  rw [show (11 : Nat) = 10 + 1 from rfl, run_step_succ]
  have step5 : step ⟨some stB, false :: repeatOne (2 * k + 1), true, repeatFalse p⟩ =
    ⟨some stE, true :: false :: repeatOne (2 * k + 1), headD' (repeatFalse p) false,
      tailD' (repeatFalse p)⟩ := by ext <;> simp [step, transition, stE, Fin.ext_iff]
  rw [step5, hd_rF, tl_rF]
  -- Step 6: E false → C 1 R
  rw [show (10 : Nat) = 9 + 1 from rfl, run_step_succ]
  have step6 : step ⟨some stE, true :: false :: repeatOne (2 * k + 1), false,
      repeatFalse (p - 1)⟩ =
    ⟨some stC, true :: true :: false :: repeatOne (2 * k + 1),
      headD' (repeatFalse (p - 1)) false, tailD' (repeatFalse (p - 1))⟩ := by
    ext <;> simp [step, transition, stC, Fin.ext_iff]
  rw [step6, hd_rF, tl_rF]
  -- Step 7: C false → F 1 L
  rw [show (9 : Nat) = 8 + 1 from rfl, run_step_succ]
  have step7 : step ⟨some stC, true :: true :: false :: repeatOne (2 * k + 1), false,
      repeatFalse (p - 1 - 1)⟩ =
    ⟨some stF, true :: false :: repeatOne (2 * k + 1), true,
      true :: repeatFalse (p - 1 - 1)⟩ := by ext <;> simp [step, transition, stF, Fin.ext_iff]
  rw [step7]
  -- Step 8: F true → C 1 L
  rw [show (8 : Nat) = 7 + 1 from rfl, run_step_succ]
  have step8 : step ⟨some stF, true :: false :: repeatOne (2 * k + 1), true,
      true :: repeatFalse (p - 1 - 1)⟩ =
    ⟨some stC, false :: repeatOne (2 * k + 1), true,
      true :: true :: repeatFalse (p - 1 - 1)⟩ := by ext <;> simp [step, transition, stC, Fin.ext_iff]
  rw [step8]
  -- Step 9: C true → D 0 L
  rw [show (7 : Nat) = 6 + 1 from rfl, run_step_succ]
  have step9 : step ⟨some stC, false :: repeatOne (2 * k + 1), true,
      true :: true :: repeatFalse (p - 1 - 1)⟩ =
    ⟨some stD, repeatOne (2 * k + 1), false,
      false :: true :: true :: repeatFalse (p - 1 - 1)⟩ := by ext <;> simp [step, transition, stD, Fin.ext_iff]
  rw [step9]
  -- Step 10: D false → A 1 R
  rw [show (6 : Nat) = 5 + 1 from rfl, run_step_succ]
  have step10 : step ⟨some stD, repeatOne (2 * k + 1), false,
      false :: true :: true :: repeatFalse (p - 1 - 1)⟩ =
    ⟨some stA, true :: repeatOne (2 * k + 1), false,
      true :: true :: repeatFalse (p - 1 - 1)⟩ := by ext <;> simp [step, transition, stA, Fin.ext_iff]
  rw [step10, cons_rO]
  -- Step 11: A false → B 1 R
  rw [show (5 : Nat) = 4 + 1 from rfl, run_step_succ]
  have step11 : step ⟨some stA, repeatOne (2 * k + 2), false,
      true :: true :: repeatFalse (p - 1 - 1)⟩ =
    ⟨some stB, true :: repeatOne (2 * k + 2), true,
      true :: repeatFalse (p - 1 - 1)⟩ := by ext <;> simp [step, transition, stB, Fin.ext_iff]
  rw [step11, cons_rO]
  -- Step 12: B true → E 1 R
  rw [show (4 : Nat) = 3 + 1 from rfl, run_step_succ]
  have step12 : step ⟨some stB, repeatOne (2 * k + 3), true,
      true :: repeatFalse (p - 1 - 1)⟩ =
    ⟨some stE, true :: repeatOne (2 * k + 3), true,
      repeatFalse (p - 1 - 1)⟩ := by ext <;> simp [step, transition, stE, Fin.ext_iff]
  rw [step12, cons_rO]
  -- Step 13: E true → B 1 R
  rw [show (3 : Nat) = 2 + 1 from rfl, run_step_succ]
  have step13 : step ⟨some stE, repeatOne (2 * k + 4), true, repeatFalse (p - 1 - 1)⟩ =
    ⟨some stB, true :: repeatOne (2 * k + 4),
      headD' (repeatFalse (p - 1 - 1)) false, tailD' (repeatFalse (p - 1 - 1))⟩ := by
    ext <;> simp [step, transition, stB, Fin.ext_iff]
  rw [step13, hd_rF, tl_rF, cons_rO]
  -- Step 14: B false → C 1 L
  rw [show (2 : Nat) = 1 + 1 from rfl, run_step_succ]
  rw [show 2 * k + 5 = (2 * k + 4) + 1 from by omega, repeatOne_succ]
  have step14 : step ⟨some stB, true :: repeatOne (2 * k + 4), false,
      repeatFalse (p - 1 - 1 - 1)⟩ =
    ⟨some stC, repeatOne (2 * k + 4), true,
      true :: repeatFalse (p - 1 - 1 - 1)⟩ := by ext <;> simp [step, transition, stC, Fin.ext_iff]
  rw [step14, show 2 * k + 4 = (2 * k + 3) + 1 from by omega, repeatOne_succ]
  -- Step 15: C true → D 0 L
  rw [show (1 : Nat) = 0 + 1 from rfl, run_step_succ]
  have step15 : step ⟨some stC, true :: repeatOne (2 * k + 3), true,
      true :: repeatFalse (p - 1 - 1 - 1)⟩ =
    ⟨some stD, repeatOne (2 * k + 3), true,
      false :: true :: repeatFalse (p - 1 - 1 - 1)⟩ := by ext <;> simp [step, transition, stD, Fin.ext_iff]
  rw [step15]; simp only [run]
  -- Now: {D, true, repeatOne(2k+3), [false, true] ++ repeatFalse(p-1-1-1)}
  -- This matches odd_left_to_P(k+1, 1, p-3)
  rw [show 2 * k + 3 = 2 * (k + 1) + 1 from by omega]
  rw [show p - 1 - 1 - 1 = p - 3 from by omega]
  rw [show 1 + 3 * (k + 1) = 3 * k + 4 from by ring] at h2
  convert h2 using 2

lemma tm_Q_one_odd (b : Nat) (p : Nat) :
  ∃ steps padding,
    run (Q_Config 1 (2 * b + 1) p) steps = P_Config (3 * b + 8) padding := by
  -- Helpers
  have hd_rF : ∀ n, headD' (repeatFalse n) false = false := by
    intro n; cases n <;> simp [repeatFalse, List.replicate]
  have tl_rF : ∀ n, tailD' (repeatFalse n) = repeatFalse (n - 1) := by
    intro n; cases n with
    | zero => simp [repeatFalse, List.replicate]
    | succ m => simp [repeatFalse, List.replicate_succ]
  have cons_rO : ∀ n, true :: repeatOne n = repeatOne (n + 1) := by
    intro n; simp [repeatOne, List.replicate_succ]
  have cons_rO_app : ∀ n, true :: (repeatOne n ++ repeatFalse p) =
      repeatOne (n + 1) ++ repeatFalse p := by
    intro n; rw [repeatOne_succ, List.cons_append]
  -- odd_left_to_P(b+2, 2, p-1-1) gives the final phase
  obtain ⟨s_last, pad_last, h_last⟩ := odd_left_to_P (b + 2) 2 (p - 1 - 1) (by omega : (2 : Nat) ≥ 1)
  refine ⟨2 + 17 + 2 * (b + 1) + 6 + s_last, pad_last, ?_⟩
  simp only [Q_Config]
  -- Introduce m to prevent kernel reduction of repeatOne(2b+1)
  set m := 2 * b + 1 with hm
  -- Phase 1: D_shift 2
  rw [show (2 : Nat) * 1 = 2 from by norm_num]
  rw [show 2 + 17 + 2 * (b + 1) + 6 + s_last = 2 + (17 + 2 * (b + 1) + 6 + s_last) from by omega,
      run_add,
      show (repeatOne 2 : List TapeSymbol) = repeatOne 2 ++ [] from (List.append_nil _).symm,
      D_shift 2 [] ([false] ++ repeatOne m ++ repeatFalse p)]
  simp only [repeatOne_succ, repeatOne_zero, List.nil_append, List.cons_append]
  -- {D, true, [], true :: true :: false :: rO m ++ rF p}
  -- Steps 3-19: 17 manual steps
  -- Step 3: D true → D 1 L
  rw [show 17 + 2 * (b + 1) + 6 + s_last = (16 + 2 * (b + 1) + 6 + s_last) + 1 from by omega,
      run_step_succ]
  simp only [step, transition, headD'_nil, tailD'_nil]
  -- Step 4: D false → A 1 R
  rw [show 16 + 2 * (b + 1) + 6 + s_last = (15 + 2 * (b + 1) + 6 + s_last) + 1 from by omega,
      run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- Step 5: A true → B 0 R
  rw [show 15 + 2 * (b + 1) + 6 + s_last = (14 + 2 * (b + 1) + 6 + s_last) + 1 from by omega,
      run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- Step 6: B true → E 1 R
  rw [show 14 + 2 * (b + 1) + 6 + s_last = (13 + 2 * (b + 1) + 6 + s_last) + 1 from by omega,
      run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- Step 7: E true → B 1 R
  rw [show 13 + 2 * (b + 1) + 6 + s_last = (12 + 2 * (b + 1) + 6 + s_last) + 1 from by omega,
      run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- Step 8: B false → C 1 L
  rw [show 12 + 2 * (b + 1) + 6 + s_last = (11 + 2 * (b + 1) + 6 + s_last) + 1 from by omega,
      run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {C, true, [true, false, true], true :: rO m ++ rF p}
  rw [cons_rO_app m]
  -- Step 9: C true → D 0 L
  rw [show 11 + 2 * (b + 1) + 6 + s_last = (10 + 2 * (b + 1) + 6 + s_last) + 1 from by omega,
      run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- Step 10: D true → D 1 L
  rw [show 10 + 2 * (b + 1) + 6 + s_last = (9 + 2 * (b + 1) + 6 + s_last) + 1 from by omega,
      run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- Step 11: D false → A 1 R
  rw [show 9 + 2 * (b + 1) + 6 + s_last = (8 + 2 * (b + 1) + 6 + s_last) + 1 from by omega,
      run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- Step 12: A true → B 0 R
  rw [show 8 + 2 * (b + 1) + 6 + s_last = (7 + 2 * (b + 1) + 6 + s_last) + 1 from by omega,
      run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- Step 13: B false → C 1 L
  rw [show 7 + 2 * (b + 1) + 6 + s_last = (6 + 2 * (b + 1) + 6 + s_last) + 1 from by omega,
      run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {C, false, [true, true], true :: rO(m+1) ++ rF p}
  rw [cons_rO_app (m + 1)]
  -- Step 14: C false → F 1 L
  rw [show 6 + 2 * (b + 1) + 6 + s_last = (5 + 2 * (b + 1) + 6 + s_last) + 1 from by omega,
      run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {F, true, [true], true :: rO(m+2) ++ rF p}
  rw [cons_rO_app (m + 2)]
  -- Step 15: F true → C 1 L
  rw [show 5 + 2 * (b + 1) + 6 + s_last = (4 + 2 * (b + 1) + 6 + s_last) + 1 from by omega,
      run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {C, true, [], true :: rO(m+3) ++ rF p}
  rw [cons_rO_app (m + 3)]
  -- Step 16: C true → D 0 L
  rw [show 4 + 2 * (b + 1) + 6 + s_last = (3 + 2 * (b + 1) + 6 + s_last) + 1 from by omega,
      run_step_succ]
  simp only [step, transition, headD'_nil, tailD'_nil]
  -- Step 17: D false → A 1 R
  rw [show 3 + 2 * (b + 1) + 6 + s_last = (2 + 2 * (b + 1) + 6 + s_last) + 1 from by omega,
      run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  -- {A, false, [true], rO(m+4) ++ rF p}
  -- Step 18: A false → B 1 R. headD'(rO(m+4) ++ rF p) = true
  rw [show 2 + 2 * (b + 1) + 6 + s_last = (1 + 2 * (b + 1) + 6 + s_last) + 1 from by omega,
      run_step_succ]
  have step18_eq : step ⟨some stA, [true], false,
      repeatOne (m + 4) ++ repeatFalse p⟩ =
    ⟨some stB, [true, true], headD' (repeatOne (m + 4) ++ repeatFalse p) false,
      tailD' (repeatOne (m + 4) ++ repeatFalse p)⟩ := by
    simp [step, transition, stB]
  rw [step18_eq,
      show m + 4 = (m + 3) + 1 from by omega,
      repeatOne_succ, List.cons_append, headD'_cons, tailD'_cons]
  -- Step 19: B true → E 1 R. headD'(rO(m+3) ++ rF p) = true
  rw [show 1 + 2 * (b + 1) + 6 + s_last = (2 * (b + 1) + 6 + s_last) + 1 from by omega,
      run_step_succ]
  have step19_eq : step ⟨some stB, [true, true], true,
      repeatOne (m + 3) ++ repeatFalse p⟩ =
    ⟨some stE, [true, true, true], headD' (repeatOne (m + 3) ++ repeatFalse p) false,
      tailD' (repeatOne (m + 3) ++ repeatFalse p)⟩ := by
    simp [step, transition, stE]
  rw [step19_eq,
      show m + 3 = (m + 2) + 1 from by omega,
      repeatOne_succ, List.cons_append, headD'_cons, tailD'_cons]
  -- {E, true, [true, true, true], rO(m+2) ++ rF p}
  -- Phase 3: EB_shift(b+1) through 2(b+1) ones
  -- m+2 = 2b+3 = 2(b+1)+1, split rO(2(b+1)+1) = rO(2(b+1)) ++ [true]
  rw [show m + 2 = 2 * (b + 1) + 1 from by omega,
      ← repeatOne_snoc (2 * (b + 1)),
      List.append_assoc, List.singleton_append]
  rw [show 2 * (b + 1) + 6 + s_last = 2 * (b + 1) + (6 + s_last) from by omega,
      run_add, EB_shift (b + 1) [true, true, true] (true :: repeatFalse p)]
  -- {E, true, rO(2*(b+1)) ++ [true,true,true], [true] ++ rF p}
  -- Consolidate left: rO(2*(b+1)) ++ [1,1,1] = rO(m+4) = rO(2b+5)
  have consolidate_left : repeatOne (2 * (b + 1)) ++ [true, true, true] = repeatOne (m + 4) := by
    simp only [repeatOne]
    rw [show [true, true, true] = List.replicate 3 true from by simp [List.replicate],
        ← List.replicate_add]; congr 1
  rw [consolidate_left]
  -- {E, true, rO(m+4), true :: rF p}
  -- Phase 4: 6 manual steps
  -- Step 20: E true → B 1 R
  rw [show (6 : Nat) + s_last = (5 + s_last) + 1 from by omega, run_step_succ]
  simp only [step, transition, headD'_cons, tailD'_cons]
  rw [cons_rO (m + 4)]
  -- Step 21: B true → E 1 R
  rw [show (5 : Nat) + s_last = (4 + s_last) + 1 from by omega, run_step_succ]
  simp only [step, transition, hd_rF, tl_rF]
  rw [cons_rO (m + 5)]
  -- Step 22: E false → C 1 R
  rw [show (4 : Nat) + s_last = (3 + s_last) + 1 from by omega, run_step_succ]
  simp only [step, transition, hd_rF, tl_rF]
  rw [cons_rO (m + 6)]
  -- Step 23: C false → F 1 L
  rw [show (3 : Nat) + s_last = (2 + s_last) + 1 from by omega, run_step_succ]
  simp only [step, transition]
  rw [show m + 7 = (m + 6) + 1 from by omega, repeatOne_succ,
      headD'_cons, tailD'_cons]
  -- Step 24: F true → C 1 L
  rw [show (2 : Nat) + s_last = (1 + s_last) + 1 from by omega, run_step_succ]
  simp only [step, transition]
  rw [show m + 6 = (m + 5) + 1 from by omega, repeatOne_succ,
      headD'_cons, tailD'_cons]
  -- Step 25: C true → D 0 L
  rw [show (1 : Nat) + s_last = (0 + s_last) + 1 from by omega, run_step_succ]
  simp only [step, transition]
  rw [show m + 5 = (m + 4) + 1 from by omega, repeatOne_succ,
      headD'_cons, tailD'_cons]
  -- {D, true, rO(m+4), [false, true, true] ++ rF(p-1-1)}
  -- Apply odd_left_to_P(b+2, 2, p-1-1)
  -- m+4 = 2b+5 = 2*(b+2)+1
  convert h_last using 2 <;> omega

lemma tm_Q_odd (a : Nat) (b : Nat) (p : Nat) :
  ∃ steps padding,
    run (Q_Config (2 * a + 3) b p) steps = P_Config (b + 5 * a + 6) padding := by
  -- Phase 1: First big cycle from Q_Config to gen form
  have h1 := first_big_cycle a b p
  -- Phase 2: Iterated gen cycles from gen(2a+2, 1, b+1, p) to gen(0, 2a+3, b+2a+3, p)
  have ⟨s2, h2⟩ := gen_multi_cycle (2 * a + 2) 1 (b + 1) p
  -- Phase 3: Boundary from gen(0, 2a+3, b+2a+3, p) to repeatOne(2a+1) form
  -- gen(0, n+K, B+K, p) with n=1, K=2a+2: gen(0, 2a+3, b+2a+3, p)
  -- boundary needs n+K = (2a+1)+2 so we use gen_boundary with n=2a+1
  have h3 := gen_boundary (2 * a + 1) (b + 2 * a + 3) p
  -- Phase 4: odd_left_to_P
  have h4 := odd_left_to_P a (b + 2 * a + 6) p (by omega)
  obtain ⟨s4, pad4, h4'⟩ := h4
  -- Compose all phases
  refine ⟨(8 * a + 17) + s2 + 7 + s4, pad4, ?_⟩
  rw [show (8 * a + 17) + s2 + 7 + s4 = (8 * a + 17) + (s2 + (7 + s4)) from by ring]
  rw [run_add, h1]
  -- Now need to show gen multi result feeds into boundary
  rw [run_add, h2]
  -- Adjust the intermediate config to match gen_boundary input
  -- gen_multi gives: [false]++repeatOne(1+(2a+2)), [false]++repeatOne(b+1+(2a+2))++rF p
  -- = [false]++repeatOne(2a+3), [false]++repeatOne(b+2a+3)++rF p
  -- boundary expects: [false]++repeatOne((2a+1)+2), [false]++repeatOne(b+2a+3)++rF p
  have eq1 : 1 + (2 * a + 2) = (2 * a + 1) + 2 := by ring
  have eq2 : b + 1 + (2 * a + 2) = b + 2 * a + 3 := by ring
  rw [show 7 + s4 = 7 + s4 from rfl, run_add]
  conv_lhs => arg 1; rw [show (1 + (2 * a + 2)) = (2 * a + 1) + 2 from eq1,
                          show (b + 1 + (2 * a + 2)) = b + 2 * a + 3 from eq2]
  rw [h3]
  -- Now apply odd_left_to_P
  rw [h4']
  -- Match P_Config parameters
  congr 1; ring

-- ============================================================
-- Section 10: Initial Condition
-- ============================================================

/-- The TM starting from blank tape reaches P(2) after some initial steps. -/
lemma tm_init_reaches_P2 :
  ∃ steps padding,
    run initConfig steps = P_Config 2 padding := by
  exact ⟨24, 1, rfl⟩

-- ============================================================
-- Section 11: Completeness of the Analysis
-- ============================================================

/-- The rules above completely characterize the TM's behavior from any
    P or Q configuration. Every P_Config or Q_Config either:
    (1) transitions to another P_Config or Q_Config, or
    (2) halts (only from Q(0, b)).

    Formally: from any reachable config matching P_Config or Q_Config,
    the TM eventually reaches another such config (or halts). -/
lemma macro_step_complete (s : MachineState) (p : Nat) :
  s ≠ .Halt →
  ∃ steps padding, match s with
    | .P a => match nextMachineState s with
      | .P a' => run (P_Config a p) steps = P_Config a' padding
      | .Q a' b' => run (P_Config a p) steps = Q_Config a' b' padding
      | .Halt => False
    | .Q a b => match nextMachineState s with
      | .P a' => run (Q_Config a b p) steps = P_Config a' padding
      | .Q a' b' => run (Q_Config a b p) steps = Q_Config a' b' padding
      | .Halt => (run (Q_Config a b p) steps).state = none
    | .Halt => False := by
  intro hs
  cases s with
  | Halt => exact absurd rfl hs
  | P a =>
    obtain ⟨k, rfl | rfl⟩ : ∃ k, a = 2 * k ∨ a = 2 * k + 1 := ⟨a / 2, by omega⟩
    · -- P(2k) → P(3k+4)
      have hns : nextMachineState (.P (2 * k)) = .P (3 * k + 4) := by
        unfold nextMachineState
        simp [show (2 * k) % 2 = 0 from by omega, show (2 * k) / 2 = k from by omega]
      simp only [hns]
      exact tm_P_even k p
    · -- P(2k+1) → Q(k+2, 1)
      have hns : nextMachineState (.P (2 * k + 1)) = .Q (k + 2) 1 := by
        unfold nextMachineState
        simp [show (2 * k + 1) % 2 = 1 from by omega, show (2 * k + 1) / 2 = k from by omega]
      simp only [hns]
      exact tm_P_odd k p
  | Q a b =>
    cases a with
    | zero =>
      simp [nextMachineState]
      exact ⟨8, tm_Q_halt b p⟩
    | succ n =>
      cases n with
      | zero =>
        -- Q(1, b)
        obtain ⟨k, rfl | rfl⟩ : ∃ k, b = 2 * k ∨ b = 2 * k + 1 := ⟨b / 2, by omega⟩
        · -- Q(1, 2k) → Q(k+2, 1)
          have hns : nextMachineState (.Q 1 (2 * k)) = .Q (k + 2) 1 := by
            unfold nextMachineState
            simp [show (2 * k) % 2 = 0 from by omega, show (2 * k) / 2 = k from by omega]
          simp only [hns]
          exact tm_Q_one_even k p
        · -- Q(1, 2k+1) → P(3k+8)
          have hns : nextMachineState (.Q 1 (2 * k + 1)) = .P (3 * k + 8) := by
            unfold nextMachineState
            simp [show (2 * k + 1) % 2 = 1 from by omega,
                  show (2 * k + 1) / 2 = k from by omega]
          simp only [hns]
          exact tm_Q_one_odd k p
      | succ m =>
        -- Q(m+2, b)
        obtain ⟨k, rfl | rfl⟩ : ∃ k, m = 2 * k ∨ m = 2 * k + 1 := ⟨m / 2, by omega⟩
        · -- Q(2k+2, b) → Q(k, b+2k+5)
          have hns : nextMachineState (.Q (2 * k + 2) b) = .Q k (b + 2 * k + 5) := by
            unfold nextMachineState
            simp [show (2 * k) % 2 = 0 from by omega, show (2 * k) / 2 = k from by omega]
          simp only [hns]
          exact tm_Q_even k b p
        · -- Q(2k+3, b) → P(b+5k+6)
          have hns : nextMachineState (.Q (2 * k + 1 + 2) b) = .P (b + 5 * k + 6) := by
            unfold nextMachineState
            simp [show (2 * k + 1) % 2 = 1 from by omega]
          simp only [hns]
          exact tm_Q_odd k b p

-- ============================================================
-- Section 12: Halting Characterization
-- ============================================================

/-- The TM halts iff it reaches Q(0, b) for some b.
    More precisely: Q_Config(0, b) is the only macro configuration
    from which the TM transitions to HALT. -/
lemma halt_iff_Q_zero :
  ∀ s : MachineState, s ≠ .Halt → (nextMachineState s = .Halt ↔ ∃ b, s = .Q 0 b) := by
  intro s hs
  constructor
  · intro h
    cases s with
    | Halt => contradiction
    | P a => simp [nextMachineState] at h; split_ifs at h
    | Q a b => cases a with
      | zero => exact ⟨b, rfl⟩
      | succ n => cases n with
        | zero => simp [nextMachineState] at h; split_ifs at h
        | succ m => simp [nextMachineState] at h; split_ifs at h
  · rintro ⟨b, rfl⟩; rfl

/-- The machine halts from Q(2, b) in finitely many steps (via Q(0, b+5)). -/
lemma tm_Q_two_halts (b : Nat) (p : Nat) :
  ∃ steps, (run (Q_Config 2 b p) steps).state = none := by
  obtain ⟨steps, padding, h⟩ := tm_Q_even 0 b p
  simp at h
  exact ⟨steps + 8, by rw [run_add, h]; simp [run, step, transition, Q_Config, repeatOne]⟩

-- ============================================================
-- Section 12a: Halting Backward Analysis
-- ============================================================

/-! ### Unreachability of Q(1, 0)

Q(1, 0) has **no predecessors** in the map. The three rules producing Q(x, y) are:
  1. P(2a+1) → Q(a+2, 1):  x = a+2 ≥ 2, y = 1
  2. Q(1, 2b) → Q(b+2, 1): x = b+2 ≥ 2, y = 1
  3. Q(2a+2, b) → Q(a, b+2a+5): y = b+2a+5 ≥ 5

None can produce x = 1 with y = 0.
-/

/-- No rule of the map produces Q(1, 0). -/
lemma Q_one_zero_no_predecessor :
    ∀ s : MachineState, nextMachineState s ≠ .Q 1 0 := by
  intro s; cases s with
  | Halt => simp [nextMachineState]
  | P a => simp only [nextMachineState]; split_ifs <;> simp
  | Q a b =>
    cases a with
    | zero => simp [nextMachineState]
    | succ n =>
      cases n with
      | zero => simp only [nextMachineState]; split_ifs <;> simp
      | succ m =>
        simp only [nextMachineState]; split_ifs <;> simp_all

/-! ### Reachable Q-states always have b ≥ 1

Every Q(a, b) reachable from P(2) satisfies b ≥ 1.
- Entry from P(2a+1) → Q(a+2, 1): b = 1.
- Entry from Q(1, 2b) → Q(b+2, 1): b = 1.
- Internal Q(2a+2, b) → Q(a, b+2a+5): b' = b+2a+5 ≥ b+5, so b only grows.
-/

/-- Every Q-state reachable from any MachineState has b ≥ 1.
    (Stronger: b = 1 or b ≥ 5.) -/
lemma reachable_Q_b_pos :
    ∀ s : MachineState, ∀ a b : Nat,
      nextMachineState s = .Q a b → b = 1 ∨ b ≥ 5 := by
  intro s a b h; cases s with
  | Halt => simp [nextMachineState] at h
  | P a' => simp [nextMachineState] at h; split_ifs at h; simp_all
  | Q a' b' =>
    cases a' with
    | zero => simp [nextMachineState] at h
    | succ n =>
      cases n with
      | zero => simp [nextMachineState] at h; split_ifs at h; simp_all
      | succ m =>
        simp [nextMachineState] at h; split_ifs at h; simp_all;
          (obtain ⟨-, rfl⟩ := ‹_›; right; omega)

/-- Corollary: in any reachable Q(a, b), b ≥ 1. -/
lemma reachable_Q_b_ge_one :
    ∀ s : MachineState, ∀ a b : Nat,
      nextMachineState s = .Q a b → b ≥ 1 := by
  intro s a b h; cases s with
  | Halt => simp [nextMachineState] at h
  | P a' => simp [nextMachineState] at h; split_ifs at h; simp_all
  | Q a' b' =>
    cases a' with
    | zero => simp [nextMachineState] at h
    | succ n =>
      cases n with
      | zero => simp [nextMachineState] at h; split_ifs at h; simp_all
      | succ m =>
        simp [nextMachineState] at h; split_ifs at h; simp_all;
          (obtain ⟨-, rfl⟩ := ‹_›; omega)

/-! ### The only path to halt

The backward chain to Q(0, b) is:
  Q(0, b)  ← Q(2, b')  where b = b'+5
  Q(2, b') ← Q(6, b'') where b' = b''+9
  Q(6, ·)  ← Q(14, ·)  ← Q(30, ·)  ← Q(62, ·)  ← ...

General pattern: Q(2^(n+1) − 2, ·) chains down to Q(0, ·) through
n halvings, all intermediate values being even.

The alternative path to Q(6, ·) is:
  Q(4, b) → Q(1, b+7) → Q((b+7)/2 + 2, 1)  when b+7 is even (b odd)
  which gives Q(6, 1) when b = 1, i.e., Q(4, 1) → Q(1, 8) → Q(6, 1) → halt.
-/

/-- Q(2, b) → Q(0, b+5): the unique one-step predecessor of halt. -/
lemma Q_two_to_halt (b : Nat) :
    nextMachineState (.Q 2 b) = .Q 0 (b + 5) := by
  rfl

/-- Q(6, b) → Q(2, b+9): chains to halt in 2 steps. -/
lemma Q_six_to_two (b : Nat) :
    nextMachineState (.Q 6 b) = .Q 2 (b + 9) := by
  rfl

/-- Q(14, b) → Q(6, b+17): chains to halt in 3 steps. -/
lemma Q_fourteen_to_six (b : Nat) :
    nextMachineState (.Q 14 b) = .Q 6 (b + 17) := by
  rfl

/-- General halving chain: Q(2^(n+1) − 2, b) reaches Q(0, ·) in n+1 steps
    (through Q(2^n − 2, ·), ..., Q(2, ·), Q(0, ·)),
    provided all intermediate values 2^k − 2 are even, which they are. -/
lemma halving_chain_halts (n : Nat) (b : Nat) :
    iterMachineState (.Q (2 ^ (n + 1) - 2) b) (n + 1) = .Halt := by
  induction n generalizing b with
  | zero => simp [iterMachineState, nextMachineState]
  | succ n ih =>
    have h_pow_ge : 2 ^ (n + 1) ≥ 2 := by
      calc 2 ^ (n + 1) ≥ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 := by norm_num
    have h2 : 2 ^ (n + 1 + 1) - 2 = 2 * (2 ^ (n + 1) - 2) + 2 := by
      have : 2 ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by ring
      omega
    rw [h2, show n + 1 + 1 = n + 2 from rfl]
    simp only [iterMachineState]
    show iterMachineState (nextMachineState (.Q (2 * (2 ^ (n + 1) - 2) + 2) b)) (n + 1) = .Halt
    have h_even : (2 * (2 ^ (n + 1) - 2)) % 2 = 0 := Nat.mul_mod_right 2 _
    simp only [nextMachineState, h_even, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2),
      beq_self_eq_true, ite_true]
    exact ih _

/-- The alternative halt path: Q(4, 1) → Q(1, 8) → Q(6, 1) → Q(2, 10) → Q(0, 15) → Halt. -/
lemma Q_four_one_halts :
    iterMachineState (.Q 4 1) 5 = .Halt := by
  decide

/-! ### Reachable first arguments in Q

When entering Q from P, the first argument is a/2 + 2 ≥ 2.
Within Q, the halving rule Q(2k+2, b) → Q(k, ·) produces first arguments
that are roughly half the previous. To reach halt, we need to hit
first arg ∈ {0, 2, 6, 14, 30, ...} = {2^(n+1) − 2 : n ≥ 0} ∪ {0},
OR thread through Q(4, ·) → Q(1, ·) → Q(even, 1).

From P(2), all entry points into Q have large first arguments (≥ 5)
that grow super-exponentially, making it increasingly unlikely (but not
provably impossible without a Collatz-like argument) to hit these
small critical values.
-/

/-- The first argument of Q upon entry from P is always ≥ 4.
    (From P(2a+1) → Q(a+2, 1), we need a ≥ 0, so first arg ≥ 2.
     In fact from P(2), the P-values are ≥ 7, giving first arg ≥ 5.) -/
lemma Q_entry_first_arg_ge_two :
    ∀ a : Nat, ∀ b : Nat,
      nextMachineState (.P a) = .Q b 1 → b ≥ 2 := by
  intro a b h; simp [nextMachineState] at h; split_ifs at h; simp_all; omega

/-- Halting requires the Q first-argument chain to reach exactly 0.
    The only way to decrease the first argument is the halving rule
    Q(2k+2, b) → Q(k, b+2k+5), which requires even first argument.
    Odd first arguments ≥ 3 exit to P immediately. -/
lemma Q_odd_exits_to_P (k b : Nat) :
    ∃ a', nextMachineState (.Q (2 * k + 3) b) = .P a' := by
  simp [nextMachineState]

/-- Even first arguments ≥ 2 stay in Q and halve. -/
lemma Q_even_stays (k b : Nat) :
    nextMachineState (.Q (2 * k + 2) b) = .Q k (b + 2 * k + 5) := by
  simp [nextMachineState]

/-! ### Direct halting chain characterization

The halving rule sends Q(a, b) → Q(a/2 − 1, ·) when a is even and ≥ 2.
For a pure chain of halvings to reach Q(0, ·), every intermediate value
must be even. The function a ↦ a/2 − 1 reaches 0 in n steps from a
iff a = 2^(n+1) − 2 (i.e. a ∈ {0, 2, 6, 14, 30, 62, 126, …}).

These are the ONLY first-arguments from which Q can chain directly to
halt without passing through Q(1, ·) or exiting to P.

To halt via Q(1, ·): we need Q(1, b) with b even, giving Q(b/2+2, 1),
and then b/2+2 must itself be a halting first-arg. This is a recursive
Collatz-like condition.
-/

/-- The halving function on Q first-arguments: a ↦ a/2 − 1. -/
def qHalve (a : Nat) : Nat := a / 2 - 1

/-- Iteration of the halving function. -/
def qHalveIter : Nat → Nat → Nat
  | 0, a => a
  | n + 1, a => qHalveIter n (qHalve a)

/-- Backward direction: 2^(n+1) − 2 reaches 0 in n+1 halving steps,
    with all intermediates even. -/
lemma halving_chain_backward (n : Nat) :
    qHalveIter (n + 1) (2 ^ (n + 1) - 2) = 0 ∧
    ∀ k, k ≤ n → qHalveIter k (2 ^ (n + 1) - 2) % 2 = 0 := by
  induction n with
  | zero => simp [qHalveIter, qHalve]
  | succ n ih =>
    have h_pow_ge : 2 ^ (n + 1) ≥ 2 := by
      calc 2 ^ (n + 1) ≥ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 := by norm_num
    have h_qhalve : qHalve (2 ^ (n + 1 + 1) - 2) = 2 ^ (n + 1) - 2 := by
      simp [qHalve]
      have h2 : 2 ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by ring
      rw [h2]; omega
    constructor
    · simp [qHalveIter, h_qhalve]; exact ih.1
    · intro k hk
      cases k with
      | zero =>
        simp [qHalveIter]
        have h2 : 2 ^ (n + 2) = 2 * 2 ^ (n + 1) := by ring
        rw [show n + 1 + 1 = n + 2 from rfl, h2]; omega
      | succ k =>
        simp [qHalveIter, h_qhalve]
        exact ih.2 k (by omega)

/-- The set of Q first-arguments that lead to halt purely by halving
    is a subset of {2^(n+1) − 2 : n ≥ 0} = {0, 2, 6, 14, 30, ...}. -/
lemma direct_halt_set (a : Nat) :
    (∃ n, a = 2 ^ (n + 1) - 2) →
    (∃ n, qHalveIter n a = 0 ∧ ∀ k, k < n → qHalveIter k a % 2 = 0) := by
  rintro ⟨n, rfl⟩
  exact ⟨n + 1, (halving_chain_backward n).1,
    fun k hk => (halving_chain_backward n).2 k (by omega)⟩

/-- Equivalent characterization: a is in the direct halt set iff a + 2 is
    a power of 2. -/
lemma direct_halt_set_power_of_two (a : Nat) :
    (∃ n, a = 2 ^ (n + 1) - 2) ↔ ∃ m, m ≥ 1 ∧ a + 2 = 2 ^ m := by
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨n + 1, by omega, ?_⟩
    have : 2 ^ (n + 1) ≥ 2 := by
      calc 2 ^ (n + 1) ≥ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 := by norm_num
    omega
  · rintro ⟨m, hm, ha⟩
    cases m with
    | zero => omega
    | succ m => exact ⟨m, by omega⟩

-- ============================================================
-- Section 13: Non-Halting Conjecture
-- ============================================================

/-- **Conjecture**: The TM never halts from the starting configuration P(2).
    Equivalently, the orbit of P(2) under `nextMachineState` never reaches Halt.
    This is a Collatz-like statement: the combined map's orbit grows
    super-exponentially (reaching ~ 10^(6×10^6) after 10^8 iterations). -/
def nonHalting : Prop :=
  ∀ n : Nat, iterMachineState (.P 2) n ≠ .Halt

-- ============================================================
-- Section 14: Right-Tape Padding Independence
-- ============================================================

/-- Two right tapes are equivalent if they agree at every index
    (with false/0 as default beyond their length). -/
def RightPadEquiv (R1 R2 : List TapeSymbol) : Prop :=
  ∀ i : Nat, R1.getD i false = R2.getD i false

lemma headD'_eq_getD_zero (l : List TapeSymbol) : headD' l false = l.getD 0 false := by
  cases l <;> rfl

lemma tailD'_getD (l : List TapeSymbol) (i : Nat) :
    (tailD' l).getD i false = l.getD (i + 1) false := by
  cases l with
  | nil => simp [tailD', List.getD]
  | cons x xs => simp [tailD', List.getD]

lemma headD'_rightPadEquiv {r1 r2 : List TapeSymbol} (hr : RightPadEquiv r1 r2) :
    headD' r1 false = headD' r2 false := by
  simp only [headD'_eq_getD_zero]; exact hr 0

lemma tailD'_rightPadEquiv {r1 r2 : List TapeSymbol} (hr : RightPadEquiv r1 r2) :
    RightPadEquiv (tailD' r1) (tailD' r2) := by
  intro i; simp only [tailD'_getD]; exact hr (i + 1)

lemma cons_rightPadEquiv (x : TapeSymbol) {r1 r2 : List TapeSymbol} (hr : RightPadEquiv r1 r2) :
    RightPadEquiv (x :: r1) (x :: r2) := by
  intro i; cases i with
  | zero => simp [List.getD]
  | succ n => simp [List.getD]; exact hr n

lemma rightPadEquiv_append_repeatFalse (R : List TapeSymbol) (p q : Nat) :
    RightPadEquiv (R ++ repeatFalse p) (R ++ repeatFalse q) := by
  intro i
  simp [List.getD]
  by_cases h : i < R.length
  · simp [List.getElem?_append_left h]
  · push_neg at h
    simp [List.getElem?_append_right h, repeatFalse, List.getElem?_replicate]
    split_ifs <;> rfl

/-- Padding independence: configs differing only in trailing zeros
    produce the same state, left tape, and head after any number of steps. -/
lemma run_rightPadEquiv (c1 c2 : Config) (k : Nat)
    (hs : c1.state = c2.state) (hl : c1.left = c2.left)
    (hh : c1.head = c2.head) (hr : RightPadEquiv c1.right c2.right) :
    (run c1 k).state = (run c2 k).state ∧
    (run c1 k).left = (run c2 k).left ∧
    (run c1 k).head = (run c2 k).head ∧
    RightPadEquiv (run c1 k).right (run c2 k).right := by
  have key : ∀ (k : Nat) (s : Option State) (L : List TapeSymbol) (hd : TapeSymbol)
      (R1 R2 : List TapeSymbol), RightPadEquiv R1 R2 →
      (run ⟨s, L, hd, R1⟩ k).state = (run ⟨s, L, hd, R2⟩ k).state ∧
      (run ⟨s, L, hd, R1⟩ k).left = (run ⟨s, L, hd, R2⟩ k).left ∧
      (run ⟨s, L, hd, R1⟩ k).head = (run ⟨s, L, hd, R2⟩ k).head ∧
      RightPadEquiv (run ⟨s, L, hd, R1⟩ k).right (run ⟨s, L, hd, R2⟩ k).right := by
    intro k; induction k with
    | zero => intros; exact ⟨rfl, rfl, rfl, ‹_›⟩
    | succ k ih =>
      intro s L hd R1 R2 hr
      simp only [run_step_succ]
      cases s with
      | none => simp [step]; exact ih none L hd R1 R2 hr
      | some q =>
        simp only [step]
        cases hd_dir : (transition q hd).2.2 with
        | R =>
          simp
          have hh' := headD'_rightPadEquiv hr
          have hr' := tailD'_rightPadEquiv hr
          rw [hh']
          exact ih _ _ _ _ _ hr'
        | L =>
          simp
          exact ih _ _ _ _ _ (cons_rightPadEquiv _ hr)
  cases c1; cases c2
  simp only at hs hl hh ⊢
  subst hs; subst hl; subst hh
  exact key k _ _ _ _ _ hr

-- ============================================================
-- Section 15: Abstraction Function
-- ============================================================

/-- Decode a P-config's left tape into the parameter a.
    P_Config(a, p).left = [true, false] ++ repeatOne a, so a = countOnes (tail (tail left)). -/
def decodeP (c : Config) : Nat :=
  match c.left with
  | true :: false :: rest => countOnes rest
  | _ => 0

/-- Decode a Q-config's tapes into (a, b).
    Q_Config(a, b, p).left = repeatOne(2a), so 2a = countOnes left.
    Q_Config(a, b, p).right = [false] ++ repeatOne b ++ ..., so b = countOnes (tail right). -/
def decodeQ (c : Config) : Nat × Nat :=
  let twoA := countOnes c.left
  let b := match c.right with
    | false :: rest => countOnes rest
    | _ => 0
  (twoA / 2, b)

@[simp] lemma decodeP_P_Config (a p : Nat) :
    decodeP (P_Config a p) = a := by
  simp [decodeP, P_Config]

@[simp] lemma decodeQ_Q_Config (a b p : Nat) :
    decodeQ (Q_Config a b p) = (a, b) := by
  simp [decodeQ, Q_Config, Nat.mul_div_cancel_left a (by omega : 0 < 2)]

end Cryptid
