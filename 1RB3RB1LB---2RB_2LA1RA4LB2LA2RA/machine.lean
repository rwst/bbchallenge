import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.NormNum
import BusyLean.bb2x5

/-!
# Nonhalting proof for TM 1RB3RB1LB---2RB_2LA1RA4LB2LA2RA

A 2-state 5-symbol Turing machine. Transition (A,3) is undefined (halt).

```
       0     1     2     3     4
  A   1RB   3RB   1LB   ---   2RB
  B   2LA   1RA   4LB   2LA   2RA
```

See `previous-work/dyuan01.txt` for the conjectured macro rules.

Macro tape representation (dyuan01 notation):
  [x₁, x₂, …, xₖ] := 1 <B 4^x₁ 1 2 4^x₂ 1 2 … 1 2 4^xₖ
with `<B` marking state B with head on the `1` immediately to its left.
That is:  state = some stB,  head = s1,  left = [],
          right = 4^x₁ ++ [1, 2] ++ 4^x₂ ++ [1, 2] ++ … ++ 4^xₖ.
Starting macro config: [1, 1].

Macro rules (conjectured):
  (R1)  [0,     a,                         b, …]   →  [a+3, b, …]
  (R2)  [2n+1,  2a, 2b, …,                 0]      →  halt  (unreachable)
  (R3)  [2n+1,  2a, 2b, …,                 2m+2]   →  [2n, 2a, 2b, …, 2m+2, 0]
  (R4)  [2n+1,  2a, 2b, …,                 2m+1]   →  [2n, 2a, 2b, …, 2m+1, 1]
  (R5)  [2n+1,  2a, 2b, …, 2m+1, x,        …rest]  →  [2n, 2a, 2b, …, 2m+1, x+1, …rest]
  (R6)  [2n+2,  a,                         b, …]   →  [2n+1, a+1, b, …]
-/

set_option autoImplicit false

open BB2x5

namespace TM5c

-- ============================================================
-- Section 1: The TM 1RB3RB1LB---2RB_2LA1RA4LB2LA2RA
-- ============================================================

/-- Transition function.

```
       0     1     2     3     4
  A   1RB   3RB   1LB   ---   2RB
  B   2LA   1RA   4LB   2LA   2RA
```
-/
def tm (q : St) (s : Sym) : Option (St × Sym × Dir) :=
  match q.val, s.val with
  | 0, 0 => some (stB, s1, .R)   -- A,0 → 1RB
  | 0, 1 => some (stB, s3, .R)   -- A,1 → 3RB
  | 0, 2 => some (stB, s1, .L)   -- A,2 → 1LB
  | 0, 3 => none                  -- A,3 → ---  (HALT)
  | 0, 4 => some (stB, s2, .R)   -- A,4 → 2RB
  | 1, 0 => some (stA, s2, .L)   -- B,0 → 2LA
  | 1, 1 => some (stA, s1, .R)   -- B,1 → 1RA
  | 1, 2 => some (stB, s4, .L)   -- B,2 → 4LB
  | 1, 3 => some (stA, s2, .L)   -- B,3 → 2LA
  | 1, 4 => some (stA, s2, .R)   -- B,4 → 2RA
  | _, _ => none

abbrev tmStep := step tm
abbrev tmRun := run tm

/-- Sanity: the `tm!` parser produces the same transition function. -/
example : ∀ q s, tm q s = (tm! "1RB3RB1LB---2RB_2LA1RA4LB2LA2RA") q s := by decide

-- Transition simp lemmas (avoid unfolding `tm` globally)
@[simp] theorem tm_A0 : tm stA s0 = some (stB, s1, .R) := rfl
@[simp] theorem tm_A1 : tm stA s1 = some (stB, s3, .R) := rfl
@[simp] theorem tm_A2 : tm stA s2 = some (stB, s1, .L) := rfl
@[simp] theorem tm_A3 : tm stA s3 = none := rfl
@[simp] theorem tm_A4 : tm stA s4 = some (stB, s2, .R) := rfl
@[simp] theorem tm_B0 : tm stB s0 = some (stA, s2, .L) := rfl
@[simp] theorem tm_B1 : tm stB s1 = some (stA, s1, .R) := rfl
@[simp] theorem tm_B2 : tm stB s2 = some (stB, s4, .L) := rfl
@[simp] theorem tm_B3 : tm stB s3 = some (stA, s2, .L) := rfl
@[simp] theorem tm_B4 : tm stB s4 = some (stA, s2, .R) := rfl

-- ============================================================
-- Section 2: Macro Tape Representation
-- ============================================================

/-- Flatten a list of digits into the right-tape layout
    `4^x₁ ++ [1, 2] ++ 4^x₂ ++ [1, 2] ++ … ++ 4^xₖ`. -/
def macroRight : List Nat → List Sym
  | []       => []
  | [x]      => rep s4 x
  | x :: rest => rep s4 x ++ [s1, s2] ++ macroRight rest

@[simp] theorem macroRight_nil : macroRight [] = [] := rfl
@[simp] theorem macroRight_singleton (x : Nat) : macroRight [x] = rep s4 x := rfl

/-- Unfold `macroRight` at a two-element prefix. Valid whenever the tail after
    `x` is nonempty (so the full list has length ≥ 2). -/
@[simp] theorem macroRight_cons_cons (x y : Nat) (rest : List Nat) :
    macroRight (x :: y :: rest) = rep s4 x ++ [s1, s2] ++ macroRight (y :: rest) := rfl

/-- Canonical macro configuration `[x₁, x₂, …, xₖ]`:
    state B, head `s1`, left blank, right = `macroRight xs`. -/
def MacroConfig (xs : List Nat) : Config :=
  { state := some stB, head := s1, left := [], right := macroRight xs }

-- ============================================================
-- Section 3: Initial configuration and startup
-- ============================================================

def initConfig : Config :=
  { state := some stA, head := s0, left := [], right := [] }

/-- After 17 steps from the blank tape, the machine enters the canonical
    macro config [1, 1]. -/
theorem init_to_macro : tmRun initConfig 17 = MacroConfig [1, 1] := by
  native_decide

-- ============================================================
-- Section 4: Step Unfolding Tactic
-- ============================================================

/-- Unfold one TM step via `run_succ` and simplify. -/
macro "tm_step" : tactic => `(tactic| (
  rw [run_succ]; simp only [step, tm, listHd_cons, listTl_cons, listHd_nil, listTl_nil,
    List.cons_append, List.append_assoc, List.nil_append]))

-- ============================================================
-- Section 5: Macro Rules (main conjectured transitions)
-- ============================================================

/-- Every even natural number `x` satisfies `x = 2 * (x / 2)`. -/
def AllEven (xs : List Nat) : Prop := ∀ x ∈ xs, Even x

/-- Each element is a positive even number `2 * k + 2` for some `k`.
    Strictly stronger than `AllEven`: excludes zero digits.
    The macro rules R3/R4 require this on the middle list — a zero middle
    digit creates consecutive `[s1, s2, s1, s2]` separators on the tape, and
    the TM's behaviour there does NOT match the claimed rule output (e.g.
    `[1, 0, 2]` actually reaches `[3, 2]`, not `[0, 0, 2, 0]`). -/
def AllPosEven (xs : List Nat) : Prop := ∀ y ∈ xs, ∃ k, y = 2 * k + 2

/-- Tape representation of a middle digit list: each digit `y` becomes
    `rep s4 y ++ [s1, s2]` (block + trailing separator). The result is what
    appears on the right tape between the first separator (after the
    leading block) and the last block. -/
def middlePrefix : List Nat → List Sym
  | []      => []
  | y :: ys => rep s4 y ++ [s1, s2] ++ middlePrefix ys

@[simp] theorem middlePrefix_nil : middlePrefix [] = [] := rfl

@[simp] theorem middlePrefix_cons (y : Nat) (ys : List Nat) :
    middlePrefix (y :: ys) = rep s4 y ++ [s1, s2] ++ middlePrefix ys := rfl

/-- Step-count contribution of traversing `middle` forward-and-backward:
    each digit `yᵢ` contributes `2·yᵢ + 8` steps total. -/
def middle_cost : List Nat → Nat
  | []      => 0
  | y :: ys => (2 * y + 8) + middle_cost ys

@[simp] theorem middle_cost_nil : middle_cost [] = 0 := rfl

@[simp] theorem middle_cost_cons (y : Nat) (ys : List Nat) :
    middle_cost (y :: ys) = (2 * y + 8) + middle_cost ys := rfl

/-- One-sided (forward OR backward) traversal cost: `yᵢ + 4` per digit.
    The total `middle_cost` is `2 * middle_half_cost`. -/
def middle_half_cost : List Nat → Nat
  | []      => 0
  | y :: ys => (y + 4) + middle_half_cost ys

@[simp] theorem middle_half_cost_nil : middle_half_cost [] = 0 := rfl

@[simp] theorem middle_half_cost_cons (y : Nat) (ys : List Nat) :
    middle_half_cost (y :: ys) = (y + 4) + middle_half_cost ys := rfl

/-- Accumulated left context produced by traversing `middle` forward:
    each digit `y` adds `rep s2 y ++ s3 :: s1 ::` in front (in processing
    order, so the last-processed digit's stack is outermost). Defined as
    a fold so the induction peels one digit at a time. -/
def stack_L : List Nat → List Sym → List Sym
  | [],      L => L
  | y :: ys, L => stack_L ys (rep s2 y ++ s3 :: s1 :: L)

@[simp] theorem stack_L_nil (L : List Sym) : stack_L [] L = L := rfl

@[simp] theorem stack_L_cons (y : Nat) (ys : List Nat) (L : List Sym) :
    stack_L (y :: ys) L = stack_L ys (rep s2 y ++ s3 :: s1 :: L) := rfl

/-- Total cost is twice the half cost (forward + backward contribute equally). -/
theorem middle_cost_eq_two_half (middle : List Nat) :
    middle_cost middle = 2 * middle_half_cost middle := by
  induction middle with
  | nil => simp
  | cons y ys ih => simp [ih]; omega

/-- `middlePrefix` with one element appended: pushes the digit and separator
    onto the end of the existing prefix. -/
theorem middlePrefix_snoc (middle : List Nat) (x : Nat) :
    middlePrefix (middle ++ [x]) = middlePrefix middle ++ rep s4 x ++ [s1, s2] := by
  induction middle with
  | nil => simp [middlePrefix]
  | cons y ys ih => simp [middlePrefix, ih, List.append_assoc]

/-- `macroRight` with a single element appended: the prefix factorization. -/
theorem macroRight_snoc (middle : List Nat) (x : Nat) :
    macroRight (middle ++ [x]) = middlePrefix middle ++ rep s4 x := by
  induction middle with
  | nil => simp [macroRight]
  | cons y ys ih =>
    cases ys with
    | nil => simp [macroRight, middlePrefix]
    | cons z zs =>
      simp [macroRight, middlePrefix, List.append_assoc] at ih ⊢
      rw [ih]

/-- `macroRight` of `middle ++ [a, b]` expands as
    `middlePrefix middle ++ rep s4 a ++ [s1, s2] ++ rep s4 b`. -/
theorem macroRight_snoc2 (middle : List Nat) (a b : Nat) :
    macroRight (middle ++ [a, b]) =
      middlePrefix middle ++ rep s4 a ++ [s1, s2] ++ rep s4 b := by
  rw [show (middle ++ [a, b] : List Nat) = (middle ++ [a]) ++ [b] from by simp,
      macroRight_snoc, middlePrefix_snoc]

/-- Right-tape unfolding for R3's input config `(2n+1) :: middle ++ [2m+2]`. -/
theorem macroRight_R3_input (n : Nat) (middle : List Nat) (m : Nat) :
    macroRight ((2 * n + 1) :: (middle ++ [2 * m + 2])) =
      rep s4 (2 * n + 1) ++ [s1, s2] ++ middlePrefix middle ++ rep s4 (2 * m + 2) := by
  cases middle with
  | nil => simp [macroRight]
  | cons y ys =>
    show macroRight ((2 * n + 1) :: y :: (ys ++ [2 * m + 2])) = _
    rw [macroRight_cons_cons]
    rw [show (y :: (ys ++ [2 * m + 2]) : List Nat) = (y :: ys) ++ [2 * m + 2] from rfl,
        macroRight_snoc]
    simp [List.append_assoc]

/-- Right-tape unfolding for R3's output config `(2n) :: middle ++ [2m+2, 0]`. -/
theorem macroRight_R3_output (n : Nat) (middle : List Nat) (m : Nat) :
    macroRight ((2 * n) :: (middle ++ [2 * m + 2, 0])) =
      rep s4 (2 * n) ++ [s1, s2] ++ middlePrefix middle ++ rep s4 (2 * m + 2) ++ [s1, s2] := by
  cases middle with
  | nil => simp [macroRight]
  | cons y ys =>
    show macroRight ((2 * n) :: y :: (ys ++ [2 * m + 2, 0])) = _
    rw [macroRight_cons_cons]
    rw [show (y :: (ys ++ [2 * m + 2, 0]) : List Nat) = (y :: ys) ++ [2 * m + 2, 0] from rfl,
        macroRight_snoc2]
    simp [List.append_assoc]

/-- Right-tape unfolding for R4's input config `(2n+1) :: middle ++ [2m+1]`. -/
theorem macroRight_R4_input (n : Nat) (middle : List Nat) (m : Nat) :
    macroRight ((2 * n + 1) :: (middle ++ [2 * m + 1])) =
      rep s4 (2 * n + 1) ++ [s1, s2] ++ middlePrefix middle ++ rep s4 (2 * m + 1) := by
  cases middle with
  | nil => simp [macroRight]
  | cons y ys =>
    show macroRight ((2 * n + 1) :: y :: (ys ++ [2 * m + 1])) = _
    rw [macroRight_cons_cons]
    rw [show (y :: (ys ++ [2 * m + 1]) : List Nat) = (y :: ys) ++ [2 * m + 1] from rfl,
        macroRight_snoc]
    simp [List.append_assoc]

/-- Right-tape unfolding for R4's output config `(2n) :: middle ++ [2m+1, 1]`. -/
theorem macroRight_R4_output (n : Nat) (middle : List Nat) (m : Nat) :
    macroRight ((2 * n) :: (middle ++ [2 * m + 1, 1])) =
      rep s4 (2 * n) ++ [s1, s2] ++ middlePrefix middle ++ rep s4 (2 * m + 1) ++ [s1, s2]
        ++ rep s4 1 := by
  cases middle with
  | nil => simp [macroRight, List.append_assoc]
  | cons y ys =>
    show macroRight ((2 * n) :: y :: (ys ++ [2 * m + 1, 1])) = _
    rw [macroRight_cons_cons]
    rw [show (y :: (ys ++ [2 * m + 1, 1]) : List Nat) = (y :: ys) ++ [2 * m + 1, 1] from rfl,
        macroRight_snoc2]
    simp [List.append_assoc]

/-- Tail-agnostic core for R1: starting with `s1 :: s2 :: rep s4 a ++ TAIL` on
    the right (state B, head s1, left empty), 9 TM steps yield
    `rep s4 (a+3) ++ TAIL`. -/
theorem rule_R1_core (a : Nat) (TAIL : List Sym) :
    run tm ({ state := some stB, head := s1, left := [],
              right := s1 :: s2 :: (rep s4 a ++ TAIL) } : Config) 9 =
      { state := some stB, head := s1, left := [],
        right := rep s4 (a + 3) ++ TAIL } := by
  tm_step; tm_step; tm_step; tm_step; tm_step
  tm_step; tm_step; tm_step; tm_step
  simp [run_zero, rep_succ]

/-- **Rule R1**  `[0, a, …rest]  →  [a+3, …rest]`.
    Takes 9 TM steps regardless of `a` and `rest`. -/
theorem rule_R1 (a : Nat) (rest : List Nat) :
    tmRun (MacroConfig (0 :: a :: rest)) 9 =
      MacroConfig ((a + 3) :: rest) := by
  -- Normalise the right tape on both sides, then apply `rule_R1_core`.
  cases rest with
  | nil =>
    show run tm _ 9 = _
    simp only [MacroConfig, macroRight_cons_cons, macroRight_singleton, rep_zero,
               List.nil_append]
    -- Right side: s1 :: s2 :: rep s4 a
    have h := rule_R1_core a []
    simp only [List.append_nil] at h
    exact h
  | cons y rest' =>
    show run tm _ 9 = _
    simp only [MacroConfig, macroRight_cons_cons, rep_zero, List.nil_append,
               List.cons_append, List.append_assoc]
    -- Right side: s1 :: s2 :: (rep s4 a ++ ([s1, s2] ++ macroRight (y :: rest')))
    exact rule_R1_core a ([s1, s2] ++ macroRight (y :: rest'))

/-- Sweep right through a block of `2k+2` consecutive `s4` cells (with the head
    at the leftmost `s4` and state `A`). Each pair of steps (`A,s4→2RB` then
    `B,s4→2RA`) consumes two `s4`s and converts them to `s2`s on the left.
    The block size is `2k+1` cells to the right of the head, plus the head
    itself, for a total of `2k+2` symbols and `2k+2` steps. -/
theorem sweep_s4_2k (k : Nat) (L R : List Sym) :
    run tm ({ state := some stA, head := s4, left := L,
              right := rep s4 (2 * k + 1) ++ R } : Config) (2 * k + 2) =
      { state := some stA, head := listHd R, left := rep s2 (2 * k + 2) ++ L,
        right := listTl R } := by
  induction k generalizing L R with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, rep_succ, rep_zero]
    tm_step; tm_step; simp [run_zero]
  | succ k ih =>
    have hrep : rep s4 (2 * (k + 1) + 1) = s4 :: s4 :: rep s4 (2 * k + 1) := by
      show List.replicate _ _ = _
      rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 from by omega]; rfl
    rw [hrep]
    rw [show 2 * (k + 1) + 2 = (2 * k + 2) + 1 + 1 from by omega]
    tm_step; tm_step
    rw [ih (s2 :: s2 :: L) R]
    have hL : rep s2 (2 * k + 2 + 1 + 1) = rep s2 (2 * k + 2) ++ [s2, s2] := by
      show List.replicate _ _ = _
      rw [show 2 * k + 2 + 1 + 1 = 2 * k + 2 + 2 from by omega, List.replicate_add]; rfl
    rw [hL, List.append_assoc]; rfl

/-- Sweep left through `k` consecutive `s2` cells ending at `s1`, starting with
    state `B` and head on an `s2`. Each step (`B,s2→4LB`) writes an `s4` to the
    right and advances left. After `k+1` steps the head is on `s1`, the left is
    empty, and the right has gained `rep s4 (k+1)` at its front. -/
theorem sweep_s2_carry (k : Nat) (R : List Sym) :
    run tm ({ state := some stB, head := s2, left := rep s2 k ++ [s1],
              right := R } : Config) (k + 1) =
      { state := some stB, head := s1, left := [],
        right := rep s4 (k + 1) ++ R } := by
  induction k generalizing R with
  | zero =>
    simp only [rep_zero, List.nil_append]
    tm_step; simp [run_zero, rep_succ]
  | succ k ih =>
    have hrep : rep s2 (k + 1) = s2 :: rep s2 k := by
      show List.replicate _ _ = _; rfl
    rw [hrep]
    rw [show k + 1 + 1 = (k + 1) + 1 from by omega]
    tm_step
    rw [ih (s4 :: R)]
    have hR : rep s4 (k + 1 + 1) = rep s4 (k + 1) ++ [s4] := by
      show List.replicate _ _ = _
      rw [List.replicate_add]; rfl
    rw [hR, List.append_assoc]; rfl

/-- Left-context-generalized `sweep_s2_carry`. Same behaviour but the trailing
    `s1` on the left has an arbitrary context `L` beyond it, preserved to the
    final state. Setting `L = []` recovers `sweep_s2_carry`. -/
theorem sweep_s2_carry_L (k : Nat) (L R : List Sym) :
    run tm ({ state := some stB, head := s2, left := rep s2 k ++ s1 :: L,
              right := R } : Config) (k + 1) =
      { state := some stB, head := s1, left := L,
        right := rep s4 (k + 1) ++ R } := by
  induction k generalizing R with
  | zero =>
    simp only [rep_zero, List.nil_append]
    tm_step; simp [run_zero, rep_succ]
  | succ k ih =>
    have hrep : rep s2 (k + 1) = s2 :: rep s2 k := by
      show List.replicate _ _ = _; rfl
    rw [hrep, List.cons_append]
    rw [show k + 1 + 1 = (k + 1) + 1 from by omega]
    tm_step
    rw [ih (s4 :: R)]
    have hR : rep s4 (k + 1 + 1) = rep s4 (k + 1) ++ [s4] := by
      show List.replicate _ _ = _
      rw [List.replicate_add]; rfl
    rw [hR, List.append_assoc]; rfl

/-- Tail-agnostic core for R6: with `rep s4 (2n+2) ++ [s1, s2] ++ rep s4 a ++ TAIL`
    on the right (state B, head s1, left empty), `4n+8` TM steps yield
    `rep s4 (2n+1) ++ [s1, s2] ++ rep s4 (a+1) ++ TAIL`. -/
theorem rule_R6_core (n a : Nat) (TAIL : List Sym) :
    run tm ({ state := some stB, head := s1, left := [],
              right := rep s4 (2 * n + 2) ++ [s1, s2] ++ rep s4 a ++ TAIL } : Config)
        (4 * n + 8) =
      { state := some stB, head := s1, left := [],
        right := rep s4 (2 * n + 1) ++ [s1, s2] ++ rep s4 (a + 1) ++ TAIL } := by
  -- Phase breakdown (total = 4n+8):
  --   1 (enter) + (2n+2) (sweep right) + 2 (bounce) + 1 (turn) + 1 (new sep)
  --   + (2n+1) (sweep left) = 4n+8.
  rw [show 2 * n + 2 = (2 * n + 1) + 1 from by omega, rep_succ]
  simp only [List.cons_append]
  -- Phase 1: 1 step.
  rw [show 4 * n + 8 = (4 * n + 7) + 1 from by omega]
  tm_step
  -- Phase 2: sweep right (2n+2 steps via `sweep_s4_2k n`).
  rw [show 4 * n + 7 = (2 * n + 2) + (2 * n + 5) from by omega, run_add,
      sweep_s4_2k n [s1] (s1 :: s2 :: (rep s4 a ++ TAIL))]
  simp only [listHd_cons, listTl_cons]
  -- Phase 3: 2 steps.
  rw [show 2 * n + 5 = ((2 * n + 3) + 1) + 1 from by omega]
  tm_step; tm_step
  -- Phase 4: expose head `s2` from `rep s2 (2n+2) ++ [s1]`, then 1 step.
  have hrep1 : rep s2 (2 * n + 2) = s2 :: rep s2 (2 * n + 1) := by
    show List.replicate _ _ = _
    rw [show 2 * n + 2 = (2 * n + 1) + 1 from by omega]; rfl
  rw [hrep1]
  simp only [List.cons_append]
  rw [show 2 * n + 3 = (2 * n + 2) + 1 from by omega]
  tm_step
  -- Phase 5: expose head `s2` from `rep s2 (2n+1) ++ [s1]`, then 1 step.
  have hrep2 : rep s2 (2 * n + 1) = s2 :: rep s2 (2 * n) := by
    show List.replicate _ _ = _; rfl
  rw [hrep2]
  simp only [List.cons_append]
  rw [show 2 * n + 2 = (2 * n + 1) + 1 from by omega]
  tm_step
  -- Phase 6: sweep left (2n+1 steps via `sweep_s2_carry (2n)`).
  rw [sweep_s2_carry (2 * n) (s1 :: s2 :: s4 :: (rep s4 a ++ TAIL))]
  rfl

/-- **Rule R6**  `[2n+2, a, …rest]  →  [2n+1, a+1, …rest]`.
    Takes `4n + 8` TM steps. -/
theorem rule_R6 (n a : Nat) (rest : List Nat) :
    tmRun (MacroConfig ((2 * n + 2) :: a :: rest)) (4 * n + 8) =
      MacroConfig ((2 * n + 1) :: (a + 1) :: rest) := by
  cases rest with
  | nil =>
    show run tm _ _ = _
    have h := rule_R6_core n a []
    simp only [List.append_nil] at h
    simp only [MacroConfig, macroRight_cons_cons, macroRight_singleton]
    exact h
  | cons y rest' =>
    show run tm _ _ = _
    have h := rule_R6_core n a ([s1, s2] ++ macroRight (y :: rest'))
    simp only [MacroConfig, macroRight_cons_cons, List.append_assoc]
    simp only [List.append_assoc] at h
    exact h

-- =====================================================================
-- Section 5b: Helpers for R3 / R4 / R5
-- =====================================================================
--
-- All three rules share a common shape: a long right-then-left sweep that
-- decrements the first digit by one and (for R3/R4) appends a new trailing
-- digit, or (for R5) increments an interior digit past the first odd.
-- The forward sweep passes through all the even middle digits; the
-- backward sweep writes fresh `s4`s as it retreats.
--
-- See the end of this file for the compositional plan.

/-- Concrete base case for R3 (the smallest instance, `n = 0`, `m = 0`,
    `middle = []`): `[1, 2]` reaches `[0, 2, 0]` in 16 TM steps. -/
theorem rule_R3_base : tmRun (MacroConfig [1, 2]) 16 = MacroConfig [0, 2, 0] := by
  native_decide

-- ---------------------------------------------------------------------
-- Forward-sweep helpers
-- ---------------------------------------------------------------------

/-- Odd-length forward sweep through a block of `2k+1` `s4`s from state A,
    head s4. Each step alternates state A/B; after `2k+1` steps the head has
    moved past the block, the state ended in B (odd toggles), and the `2k+1`
    `s4`s have been rewritten as `s2`s on the left tape. -/
theorem sweep_s4_odd_A (k : Nat) (L R : List Sym) :
    run tm ({ state := some stA, head := s4, left := L,
              right := rep s4 (2 * k) ++ R } : Config) (2 * k + 1) =
      { state := some stB, head := listHd R, left := rep s2 (2 * k + 1) ++ L,
        right := listTl R } := by
  induction k generalizing L R with
  | zero =>
    simp only [Nat.mul_zero, rep_zero, List.nil_append]
    tm_step; simp [run_zero, rep_succ]
  | succ k ih =>
    have hrep : rep s4 (2 * (k + 1)) = s4 :: s4 :: rep s4 (2 * k) := by
      show List.replicate _ _ = _
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by omega]; rfl
    rw [hrep]
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by omega]
    tm_step; tm_step
    rw [ih (s2 :: s2 :: L) R]
    have hL : rep s2 (2 * k + 1 + 1 + 1) = rep s2 (2 * k + 1) ++ [s2, s2] := by
      show List.replicate _ _ = _
      rw [show 2 * k + 1 + 1 + 1 = 2 * k + 1 + 2 from by omega, List.replicate_add]; rfl
    rw [hL, List.append_assoc]; rfl

/-- Four-step separator crossing. From state B head s1 with the separator `[s2, s4]`
    ahead (i.e. right starts with `s2 :: s4 :: ...`), this zigzag maneuver
    writes markers `s3 :: s1` onto the left and advances the head onto the
    first `s4` of the next block. -/
theorem cross_sep_enter_block (L R : List Sym) :
    run tm ({ state := some stB, head := s1, left := L,
              right := s2 :: s4 :: R } : Config) 4 =
      { state := some stB, head := s4, left := s3 :: s1 :: L, right := R } := by
  tm_step; tm_step; tm_step; tm_step; simp [run_zero]

/-- Forward sweep through `2k+1` `s4`s from state B head s4 (an odd total).
    Ends in state A. Used by R4 where the last block has odd length. -/
theorem sweep_s4_from_B_odd (k : Nat) (L R : List Sym) :
    run tm ({ state := some stB, head := s4, left := L,
              right := rep s4 (2 * k) ++ R } : Config) (2 * k + 1) =
      { state := some stA, head := listHd R, left := rep s2 (2 * k + 1) ++ L,
        right := listTl R } := by
  induction k generalizing L R with
  | zero =>
    simp only [Nat.mul_zero, rep_zero, List.nil_append]
    tm_step; simp [run_zero, rep_succ]
  | succ k ih =>
    have hrep : rep s4 (2 * (k + 1)) = s4 :: s4 :: rep s4 (2 * k) := by
      show List.replicate _ _ = _
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by omega]; rfl
    rw [hrep]
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by omega]
    tm_step; tm_step
    rw [ih (s2 :: s2 :: L) R]
    have hL : rep s2 (2 * k + 1 + 1 + 1) = rep s2 (2 * k + 1) ++ [s2, s2] := by
      show List.replicate _ _ = _
      rw [show 2 * k + 1 + 1 + 1 = 2 * k + 1 + 2 from by omega, List.replicate_add]; rfl
    rw [hL, List.append_assoc]; rfl

/-- Forward sweep through `2k+2` `s4`s from state B head s4 (the situation
    after `cross_sep_enter_block`). Ends back in state B (even toggles). -/
theorem sweep_s4_from_B_even (k : Nat) (L R : List Sym) :
    run tm ({ state := some stB, head := s4, left := L,
              right := rep s4 (2 * k + 1) ++ R } : Config) (2 * k + 2) =
      { state := some stB, head := listHd R, left := rep s2 (2 * k + 2) ++ L,
        right := listTl R } := by
  induction k generalizing L R with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, rep_succ, rep_zero]
    tm_step; tm_step; simp [run_zero]
  | succ k ih =>
    have hrep : rep s4 (2 * (k + 1) + 1) = s4 :: s4 :: rep s4 (2 * k + 1) := by
      show List.replicate _ _ = _
      rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 from by omega]; rfl
    rw [hrep]
    rw [show 2 * (k + 1) + 2 = (2 * k + 2) + 1 + 1 from by omega]
    tm_step; tm_step
    rw [ih (s2 :: s2 :: L) R]
    have hL : rep s2 (2 * k + 2 + 1 + 1) = rep s2 (2 * k + 2) ++ [s2, s2] := by
      show List.replicate _ _ = _
      rw [show 2 * k + 2 + 1 + 1 = 2 * k + 2 + 2 from by omega, List.replicate_add]; rfl
    rw [hL, List.append_assoc]; rfl

-- ---------------------------------------------------------------------
-- Right-edge bounce
-- ---------------------------------------------------------------------

/-- Right-edge bounce at blank. From state B head s0 with `s2 :: L` on the
    left and empty right tape, 2 steps (`B,s0→2LA`, `A,s2→1LB`) write the new
    separator `[s1, s2]` onto the right and advance the head deeper into the
    left. -/
theorem bounce_at_blank (L : List Sym) :
    run tm ({ state := some stB, head := s0, left := s2 :: L, right := [] } : Config) 2 =
      { state := some stB, head := listHd L, left := listTl L,
        right := [s1, s2] } := by
  tm_step; tm_step; simp [run_zero]

/-- A-variant of the right-edge bounce. Used by R4: when the forward sweep
    through the last (odd-length) block ends in state A at blank, this bounce
    writes a `[s2]` onto the right and positions the head at `s1`.  Takes
    2 steps (`A,s0→1RB`, `B,s0→2LA`). -/
theorem bounce_at_blank_from_A (L : List Sym) :
    run tm ({ state := some stA, head := s0, left := L, right := [] } : Config) 2 =
      { state := some stA, head := s1, left := L, right := [s2] } := by
  tm_step; tm_step; simp [run_zero]

-- ---------------------------------------------------------------------
-- Backward-sweep helpers
-- ---------------------------------------------------------------------

/-- Sweep left through `k` cells of `s2` then consume a single `s3` marker.
    `k+2` steps: the `s2`s become `s4`s on the right (rebuilding a `rep s4`
    block there) and the `s3` is absorbed (`B,s3→2LA`).

    Already left-generalized via the `L` parameter: any left context beyond
    the `s3` marker is decomposed as `listHd L :: listTl L` in the output,
    so callers can pass `L = s1 :: L'` and get `head := s1, left := L'`. -/
theorem sweep_s2_to_s3 (k : Nat) (L R : List Sym) :
    run tm ({ state := some stB, head := s2, left := rep s2 k ++ s3 :: L,
              right := R } : Config) (k + 2) =
      { state := some stA, head := listHd L, left := listTl L,
        right := s2 :: rep s4 (k + 1) ++ R } := by
  induction k generalizing R with
  | zero =>
    simp only [rep_zero, List.nil_append]
    tm_step; tm_step; simp [run_zero, rep_succ]
  | succ k ih =>
    have hrep : rep s2 (k + 1) = s2 :: rep s2 k := by
      show List.replicate _ _ = _; rfl
    rw [hrep, List.cons_append]
    rw [show k + 1 + 2 = (k + 2) + 1 from by omega]
    tm_step
    rw [ih (s4 :: R)]
    have hR : rep s4 (k + 1 + 1) = rep s4 (k + 1) ++ [s4] := by
      show List.replicate _ _ = _
      rw [List.replicate_add]; rfl
    rw [hR, List.append_assoc]; rfl

/-- R1-style backward carry (3 steps: `A,s1→3RB`, `B,s2→4LB`, `B,s3→2LA`).
    Pops one cell from the left and prepends an extra `s4` to the right. -/
theorem backward_carry (L R : List Sym) :
    run tm ({ state := some stA, head := s1, left := L,
              right := s2 :: R } : Config) 3 =
      { state := some stA, head := listHd L, left := listTl L,
        right := s2 :: s4 :: R } := by
  tm_step; tm_step; tm_step; simp [run_zero]

/-- Turn-and-sweep tail. For every `n ≥ 0`, starting at state A head s2 with
    `rep s2 (2n) ++ [s1]` on the left, `2n+1` steps finish the computation:
    head returns to `s1`, left becomes empty, right is prefixed by `rep s4 (2n)`
    and a fresh `s1`.  Unifies the single-step `A,s2→1LB` turnaround with the
    trailing `sweep_s2_carry`. -/
theorem finalize_tail (n : Nat) (R : List Sym) :
    run tm ({ state := some stA, head := s2, left := rep s2 (2 * n) ++ [s1],
              right := R } : Config) (2 * n + 1) =
      { state := some stB, head := s1, left := [],
        right := rep s4 (2 * n) ++ (s1 :: R) } := by
  cases n with
  | zero =>
    simp only [Nat.mul_zero, rep_zero, List.nil_append]
    tm_step; simp [run_zero]
  | succ n =>
    have hrep : rep s2 (2 * (n + 1)) = s2 :: rep s2 (2 * n + 1) := by
      show List.replicate _ _ = _
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 from by omega]; rfl
    rw [hrep, List.cons_append]
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 from by omega]
    tm_step
    rw [sweep_s2_carry (2 * n + 1) (s1 :: R)]
    rfl

/-- Left-context-generalized `finalize_tail`. Starting at state A head s2 with
    `rep s2 (2n) ++ s1 :: L` on the left, `2n+1` steps end at state B head s1
    with left `L` (preserved) and right prefixed by `rep s4 (2n) ++ [s1]`.
    Setting `L = []` recovers `finalize_tail`. -/
theorem finalize_tail_L (n : Nat) (L R : List Sym) :
    run tm ({ state := some stA, head := s2, left := rep s2 (2 * n) ++ s1 :: L,
              right := R } : Config) (2 * n + 1) =
      { state := some stB, head := s1, left := L,
        right := rep s4 (2 * n) ++ (s1 :: R) } := by
  cases n with
  | zero =>
    simp only [Nat.mul_zero, rep_zero, List.nil_append]
    tm_step; simp [run_zero]
  | succ n =>
    have hrep : rep s2 (2 * (n + 1)) = s2 :: rep s2 (2 * n + 1) := by
      show List.replicate _ _ = _
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 from by omega]; rfl
    rw [hrep, List.cons_append]
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 from by omega]
    tm_step
    rw [sweep_s2_carry_L (2 * n + 1) L (s1 :: R)]
    rfl

/-
# Composition plan for R3 / R4 / R5

## R3 (middle = [], step count = 4n+4m+16)

Starting MacroConfig: state B, head s1, left [],
    right = rep s4 (2n+1) ++ [s1, s2] ++ rep s4 (2m+2).

Phase breakdown (composing the helpers above):

| # steps | helper                                           |
|---------|--------------------------------------------------|
| 1       | `tm_step` (B,s1→1RA — enter)                     |
| 2n+1    | `sweep_s4_odd_A n`                               |
| 4       | `cross_sep_enter_block`                          |
| 2m+2    | `sweep_s4_from_B_even m`                         |
| 2       | `bounce_at_blank`                                |
| 2m+2    | `sweep_s2_to_s3 (2m)`                            |
| 3       | `backward_carry`                                 |
| 2n+1    | `finalize_tail n`                                |

Total: 4n+4m+16. ✓

## R3 (middle = x₁ :: rest, each xᵢ even)

Needs an additional helper **`cross_even_digit`**: from state B head s1 with
`[s2, s4, rep s4 (2x-1), s1, s2, …]` on the right (i.e. an even middle digit
`2x` between two separators), `2·(2x)+5` steps traverse the digit via
`cross_sep_enter_block` + `sweep_s4_from_B_even (x-1)` + … and end at the
next separator in state B head s1 (again). Fold over `middle` to reduce to
the `middle = []` case, then apply R3-nil above.

Each even middle digit `2x` contributes `8x + 4` steps (forward and backward).
Step formula: `4n + 4m + 16 + Σ_{i} (8xᵢ + 4)` where `middle = [2x₁, …, 2xⱼ]`.

## R4 (ends in odd digit `2m+1`, step count = 4n+4m+14)

Structurally identical to R3 but last-block sweep is `sweep_s4_from_B_odd m`
(ending in state A rather than B), with a different bounce-pattern
(`A,s0→undefined` — wait, A,s0 = 1RB). So the bounce may produce a different
tail. A third variant bounce helper `bounce_at_blank_from_A` is needed.
Trailing `1` comes from a post-bounce write; verify empirically via
`sim.py --trace`.

## R5 (increments first interior odd digit, step count varies)

Fundamentally different from R3/R4: the head does **not** reach the right
edge. It sweeps rightward through the even prefix of `middle`, encounters
the first odd digit `2m+1`, advances past it by one cell, then sweeps back.

New helpers:
- `cross_odd_digit`: 4 steps to cross `[s1, s2] ++ rep s4 (2m+1) ++ [s1, s2]`
  in a way that "imprints" the increment on the next block.

For R5, the forward sweep stops at the first odd; the backward sweep is
shorter (doesn't traverse the full tape). Exact step count: `4n + ...` —
see `sim.py` for empirical values.

## Induction strategy

1. Prove the 7 helpers above (all straightforward inductions or multi-step
   concrete traces).
2. Prove `rule_R3_nil` (middle = []) by composition.
3. Introduce `cross_even_digit` and prove it via the helpers.
4. Prove `rule_R3` by induction on `middle`, folding `cross_even_digit` onto
   both the input and output configs.
5. Repeat for R4 (using an `A`-variant bounce) and R5 (using
   `cross_odd_digit` which halts the forward sweep).

## Open sub-problems (roughly ordered by independence)

All the helpers above are PROVED:
- `sweep_s4_odd_A`, `sweep_s4_from_B_even`, `sweep_s4_from_B_odd`,
  `cross_sep_enter_block`, `bounce_at_blank`, `bounce_at_blank_from_A`,
  `sweep_s2_to_s3`, `backward_carry`, `finalize_tail`,
  `cross_even_digit_forward`, `cross_even_digit_backward`.
- `rule_R3_nil` PROVED (middle=[]).

Remaining:
- `rule_R3` for middle ≠ []:  induction on middle; each step peels one
  `cross_even_digit_forward` off the front of the input and one
  `cross_even_digit_backward` (+ trailing `backward_carry`) off the back
  of the output. The hypothesis is now `AllPosEven middle` (every digit
  `2k+2`) — a zero middle digit makes the rule actually false (verified
  empirically: `[1, 0, 2]` reaches `[3, 2]`, not `[0, 0, 2, 0]`).
- `rule_R4`: need `rule_R4_nil` via composition. Backward phase differs
  qualitatively from R3 (state A → backward_carry ≠ sweep_s2_to_s3). Needs
  case-split on `m=0` vs `m≥1` or a unified helper.
- `rule_R5`: needs `cross_odd_digit` (head turns around past the first odd
  digit rather than reaching blank).
- `canonical_progress`: strengthen `ValidDigits` + case-analysis over rules.
-/

/-- R3 for `middle = []`: `[2n+1, 2m+2] → [2n, 2m+2, 0]` in `4n+4m+16` steps.
    Direct composition of the seven sweep helpers above. -/
theorem rule_R3_nil (n m : Nat) :
    tmRun (MacroConfig [2 * n + 1, 2 * m + 2]) (4 * n + 4 * m + 16) =
      MacroConfig [2 * n, 2 * m + 2, 0] := by
  show run tm _ _ = _
  -- Unfold the two MacroConfig right-tapes.
  simp only [MacroConfig, macroRight_cons_cons, macroRight_singleton, rep_zero,
             List.append_nil]
  -- Expose the leading s4 of the first block.
  have h_first : rep s4 (2 * n + 1) = s4 :: rep s4 (2 * n) := by
    show List.replicate _ _ = _; rfl
  rw [h_first, List.cons_append, List.cons_append]
  -- Phase 1: enter (1 step).
  rw [show 4 * n + 4 * m + 16 = (4 * n + 4 * m + 15) + 1 from by omega]
  tm_step
  -- Phase 2: sweep_s4_odd_A n (2n+1 steps).
  rw [show 4 * n + 4 * m + 15 = (2 * n + 1) + (2 * n + 4 * m + 14) from by omega, run_add,
      sweep_s4_odd_A n [s1] (s1 :: s2 :: rep s4 (2 * m + 2))]
  simp only [listHd_cons, listTl_cons]
  -- Expose the leading s4 of the last block.
  have h_last : rep s4 (2 * m + 2) = s4 :: rep s4 (2 * m + 1) := by
    show List.replicate _ _ = _
    rw [show 2 * m + 2 = 2 * m + 1 + 1 from by omega]; rfl
  rw [h_last]
  -- Phase 3: cross_sep_enter_block (4 steps).
  rw [show 2 * n + 4 * m + 14 = 4 + (2 * n + 4 * m + 10) from by omega, run_add,
      cross_sep_enter_block (rep s2 (2 * n + 1) ++ [s1]) (rep s4 (2 * m + 1))]
  -- Phase 4: sweep_s4_from_B_even m (2m+2 steps).
  rw [show 2 * n + 4 * m + 10 = (2 * m + 2) + (2 * n + 2 * m + 8) from by omega, run_add]
  rw [show rep s4 (2 * m + 1) = rep s4 (2 * m + 1) ++ ([] : List Sym) from by simp]
  rw [sweep_s4_from_B_even m (s3 :: s1 :: (rep s2 (2 * n + 1) ++ [s1])) []]
  simp only [listHd_nil, listTl_nil]
  -- Phase 5: bounce_at_blank (2 steps).
  -- Need left to start with s2 :: ... :: Need to peel off the first s2 from rep s2 (2m+2).
  have h_rep2m : rep s2 (2 * m + 2) = s2 :: rep s2 (2 * m + 1) := by
    show List.replicate _ _ = _
    rw [show 2 * m + 2 = 2 * m + 1 + 1 from by omega]; rfl
  rw [h_rep2m, List.cons_append]
  rw [show 2 * n + 2 * m + 8 = 2 + (2 * n + 2 * m + 6) from by omega, run_add,
      bounce_at_blank (rep s2 (2 * m + 1) ++ s3 :: s1 :: (rep s2 (2 * n + 1) ++ [s1]))]
  -- Phase 6: sweep_s2_to_s3 (2m) (2m+2 steps).
  -- Need left to match `rep s2 k ++ s3 :: L` form with k = 2m.
  have h_rep2m1 : rep s2 (2 * m + 1) = s2 :: rep s2 (2 * m) := by
    show List.replicate _ _ = _; rfl
  rw [h_rep2m1]
  simp only [listHd_cons, listTl_cons, List.cons_append]
  rw [show 2 * n + 2 * m + 6 = (2 * m + 2) + (2 * n + 4) from by omega, run_add,
      sweep_s2_to_s3 (2 * m) (s1 :: (rep s2 (2 * n + 1) ++ [s1])) [s1, s2]]
  simp only [listHd_cons, listTl_cons, List.cons_append]
  -- Phase 7: backward_carry (3 steps).
  -- Need right `s2 :: R`. Currently right = `s2 :: rep s4 (2m+1) ++ [s1, s2]`.
  rw [show 2 * n + 4 = 3 + (2 * n + 1) from by omega, run_add,
      backward_carry (rep s2 (2 * n + 1) ++ [s1]) (rep s4 (2 * m + 1) ++ [s1, s2])]
  -- Phase 8: finalize_tail n (2n+1 steps).
  -- Need head s2 with left `rep s2 (2n) ++ [s1]`.
  have h_rep2n1 : rep s2 (2 * n + 1) = s2 :: rep s2 (2 * n) := by
    show List.replicate _ _ = _; rfl
  rw [h_rep2n1]
  simp only [listHd_cons, listTl_cons, List.cons_append]
  rw [finalize_tail n (s2 :: s4 :: (rep s4 (2 * m + 1) ++ [s1, s2]))]
  -- Close: the final right should match target.
  -- Target: rep s4 (2n) ++ [s1, s2] ++ rep s4 (2m+2) ++ [s1, s2]
  -- Actual: rep s4 (2n) ++ (s1 :: s2 :: s4 :: (rep s4 (2m+1) ++ [s1, s2]))
  --       = rep s4 (2n) ++ [s1, s2] ++ (s4 :: rep s4 (2m+1)) ++ [s1, s2]
  --       = rep s4 (2n) ++ [s1, s2] ++ rep s4 (2m+2) ++ [s1, s2]
  congr 1
  simp

/-- Forward-sweep traversal of one even middle digit `2(y+1)`.
    From state B head s1 with tape `[s2] ++ rep s4 (2y+2) ++ [s1, s2]` followed by
    `R`, `2y + 6` steps land back at state B head s1 on the next separator's s1.
    The block's `s4`s are rewritten as `s2`s on the left, behind fresh `s3, s1`
    markers at the boundary. -/
theorem cross_even_digit_forward (y : Nat) (L R : List Sym) :
    run tm ({ state := some stB, head := s1, left := L,
              right := s2 :: (rep s4 (2 * y + 2) ++ [s1, s2] ++ R) } : Config)
        (2 * y + 6) =
      { state := some stB, head := s1, left := rep s2 (2 * y + 2) ++ (s3 :: s1 :: L),
        right := s2 :: R } := by
  -- Expose the leading s4 of the block.
  have hrep : rep s4 (2 * y + 2) = s4 :: rep s4 (2 * y + 1) := by
    show List.replicate _ _ = _
    rw [show 2 * y + 2 = 2 * y + 1 + 1 from by omega]; rfl
  rw [hrep]
  simp only [List.cons_append]
  -- Peel cross_sep_enter_block (4 steps).
  rw [show 2 * y + 6 = 4 + (2 * y + 2) from by omega, run_add,
      cross_sep_enter_block L (rep s4 (2 * y + 1) ++ [s1, s2] ++ R)]
  -- Apply sweep_s4_from_B_even y (2y+2 steps).
  rw [List.append_assoc,
      sweep_s4_from_B_even y (s3 :: s1 :: L) ([s1, s2] ++ R)]
  simp only [List.cons_append, List.nil_append, listHd_cons, listTl_cons]

/-- Backward-sweep traversal of one even middle digit `2y+2`.
    Starts from state A head s2 with left `rep s2 (2y+1) ++ s3 :: s1 :: L_next`
    (as produced by the preceding `backward_carry`) and ends at state A head s1
    with the left fully past the middle-digit markers and the right rebuilt
    with `rep s4 (2y+1) ++ s1`. Takes `2y + 3` steps:
    `turn_at_s2` (1) + `sweep_s2_to_s3 (2y)` (`2y + 2`). -/
theorem cross_even_digit_backward (y : Nat) (L_next R : List Sym) :
    run tm ({ state := some stA, head := s2,
              left := rep s2 (2 * y + 1) ++ s3 :: s1 :: L_next,
              right := R } : Config) (2 * y + 3) =
      { state := some stA, head := s1, left := L_next,
        right := s2 :: rep s4 (2 * y + 1) ++ s1 :: R } := by
  have hrep : rep s2 (2 * y + 1) = s2 :: rep s2 (2 * y) := by
    show List.replicate _ _ = _; rfl
  rw [hrep, List.cons_append]
  rw [show 2 * y + 3 = (2 * y + 2) + 1 from by omega]
  tm_step
  rw [sweep_s2_to_s3 (2 * y) (s1 :: L_next) (s1 :: R)]
  simp only [listHd_cons, listTl_cons, List.cons_append]

/-- Forward traversal of a list of positive-even middle digits. Starting
    at state B head s1 with left `L` and right `s2 :: (middlePrefix middle ++ Rtail)`,
    `middle_half_cost middle` steps end at state B head s1 with left
    `stack_L middle L` and right `s2 :: Rtail`. Each digit `y = 2k+2`
    contributes `y + 4` steps via `cross_even_digit_forward k`. -/
theorem forward_pass (middle : List Nat) (hmid : AllPosEven middle) (L Rtail : List Sym) :
    run tm ({ state := some stB, head := s1, left := L,
              right := s2 :: (middlePrefix middle ++ Rtail) } : Config)
        (middle_half_cost middle) =
      { state := some stB, head := s1, left := stack_L middle L,
        right := s2 :: Rtail } := by
  induction middle generalizing L with
  | nil =>
    simp only [middlePrefix_nil, middle_half_cost_nil, stack_L_nil, List.nil_append, run_zero]
  | cons y ys ih =>
    obtain ⟨k, hk⟩ := hmid y (by simp)
    subst hk
    rw [middlePrefix_cons, middle_half_cost_cons, stack_L_cons]
    rw [show 2 * k + 2 + 4 + middle_half_cost ys = (2 * k + 6) + middle_half_cost ys
        from by omega, run_add]
    rw [show (rep s4 (2 * k + 2) ++ [s1, s2] ++ middlePrefix ys ++ Rtail : List Sym) =
            rep s4 (2 * k + 2) ++ [s1, s2] ++ (middlePrefix ys ++ Rtail)
        from by rw [List.append_assoc]]
    rw [cross_even_digit_forward k L (middlePrefix ys ++ Rtail)]
    exact ih (fun z hz => hmid z (by simp [hz])) _

/-- Backward traversal of a list of positive-even middle digits. Starting
    at state A head s1 with left `stack_L middle L` (the accumulated stack
    from the forward pass) and right `s2 :: Rsuf`, `middle_half_cost middle + 3`
    steps end at state A with head `listHd L`, left `listTl L`, and right
    `s2 :: (middlePrefix middle ++ s4 :: Rsuf)` — i.e., the middle digits
    have been rebuilt on the right tape and one element popped from `L`. -/
theorem backward_pass (middle : List Nat) (hmid : AllPosEven middle) (L Rsuf : List Sym) :
    run tm ({ state := some stA, head := s1, left := stack_L middle L,
              right := s2 :: Rsuf } : Config)
        (middle_half_cost middle + 3) =
      { state := some stA, head := listHd L, left := listTl L,
        right := s2 :: (middlePrefix middle ++ s4 :: Rsuf) } := by
  induction middle generalizing L Rsuf with
  | nil =>
    simp only [stack_L_nil, middlePrefix_nil, middle_half_cost_nil, Nat.zero_add, List.nil_append]
    exact backward_carry L Rsuf
  | cons y ys ih =>
    obtain ⟨k, hk⟩ := hmid y (by simp)
    subst hk
    rw [stack_L_cons, middle_half_cost_cons, middlePrefix_cons]
    -- Peel the INNERMOST layer (y = 2k+2) last: first apply IH for ys with
    -- transformed L' = rep s2 (2k+2) ++ s3 :: s1 :: L, then do cedb + bc for y.
    rw [show 2 * k + 2 + 4 + middle_half_cost ys + 3
          = (middle_half_cost ys + 3) + (2 * k + 6) from by omega, run_add]
    rw [ih (fun z hz => hmid z (by simp [hz])) (rep s2 (2 * k + 2) ++ s3 :: s1 :: L) Rsuf]
    -- After IH: state A, head = s2 (from rep s2 (2k+2)), left = rep s2 (2k+1) ++ s3 :: s1 :: L,
    -- right = s2 :: (middlePrefix ys ++ s4 :: Rsuf).
    have hrep : rep s2 (2 * k + 2) = s2 :: rep s2 (2 * k + 1) := by
      show List.replicate _ _ = _
      rw [show 2 * k + 2 = 2 * k + 1 + 1 from by omega]; rfl
    rw [hrep]
    simp only [List.cons_append, listHd_cons, listTl_cons]
    -- Now cedb (2k+3 steps) + backward_carry (3 steps). Total = 2k+6.
    rw [show 2 * k + 6 = (2 * k + 3) + 3 from by omega, run_add]
    rw [cross_even_digit_backward k L (s2 :: (middlePrefix ys ++ s4 :: Rsuf))]
    simp only [List.cons_append]
    rw [backward_carry L (rep s4 (2 * k + 1) ++ s1 :: s2 :: (middlePrefix ys ++ s4 :: Rsuf))]
    -- Target right: s2 :: (rep s4 (2k+2) ++ [s1, s2] ++ middlePrefix ys ++ s4 :: Rsuf)
    -- Actual right: s2 :: s4 :: (rep s4 (2k+1) ++ s1 :: s2 :: (middlePrefix ys ++ s4 :: Rsuf))
    -- Equal since s4 :: rep s4 (2k+1) = rep s4 (2k+2), and re-associate.
    have hrep4 : rep s4 (2 * k + 2) = s4 :: rep s4 (2 * k + 1) := by
      show List.replicate _ _ = _
      rw [show 2 * k + 2 = 2 * k + 1 + 1 from by omega]; rfl
    rw [hrep4]
    simp [List.append_assoc]

/-- R3 for `middle = [2x+2]` (single positive even middle digit):
    `[2n+1, 2x+2, 2m+2] → [2n, 2x+2, 2m+2, 0]` in `4n+4m+4x+28` steps.
    Direct composition using `cross_even_digit_forward/backward`. -/
theorem rule_R3_single (n m x : Nat) :
    tmRun (MacroConfig [2 * n + 1, 2 * x + 2, 2 * m + 2]) (4 * n + 4 * m + 4 * x + 28) =
      MacroConfig [2 * n, 2 * x + 2, 2 * m + 2, 0] := by
  show run tm _ _ = _
  simp only [MacroConfig, macroRight_cons_cons, macroRight_singleton]
  have h_first : rep s4 (2 * n + 1) = s4 :: rep s4 (2 * n) := by
    show List.replicate _ _ = _; rfl
  rw [h_first, List.cons_append, List.cons_append]
  -- Phase 1: enter (1 step)
  rw [show 4 * n + 4 * m + 4 * x + 28 = (4 * n + 4 * m + 4 * x + 27) + 1 from by omega]
  tm_step
  -- Phase 2: sweep_s4_odd_A n (2n+1 steps)
  rw [show 4 * n + 4 * m + 4 * x + 27 = (2 * n + 1) + (2 * n + 4 * m + 4 * x + 26)
        from by omega, run_add,
      sweep_s4_odd_A n [s1]
        (s1 :: s2 :: (rep s4 (2 * x + 2) ++ s1 :: s2 :: rep s4 (2 * m + 2)))]
  simp only [listHd_cons, listTl_cons]
  -- Phase 3: cross_even_digit_forward x (2x+6 steps)
  rw [show 2 * n + 4 * m + 4 * x + 26 = (2 * x + 6) + (2 * n + 4 * m + 2 * x + 20)
        from by omega, run_add]
  rw [show (s1 :: s2 :: rep s4 (2 * m + 2) : List Sym) = [s1, s2] ++ rep s4 (2 * m + 2)
        from rfl, ← List.append_assoc]
  rw [cross_even_digit_forward x (rep s2 (2 * n + 1) ++ [s1]) (rep s4 (2 * m + 2))]
  -- Now state B head s1, left = rep s2 (2x+2) ++ s3 :: s1 :: rep s2 (2n+1) ++ [s1],
  -- right = s2 :: rep s4 (2m+2)
  have h_last : rep s4 (2 * m + 2) = s4 :: rep s4 (2 * m + 1) := by
    show List.replicate _ _ = _
    rw [show 2 * m + 2 = 2 * m + 1 + 1 from by omega]; rfl
  rw [h_last]
  -- Phase 4: cross_sep_enter_block (4 steps)
  rw [show 2 * n + 4 * m + 2 * x + 20 = 4 + (2 * n + 4 * m + 2 * x + 16) from by omega, run_add,
      cross_sep_enter_block (rep s2 (2 * x + 2) ++ s3 :: s1 :: (rep s2 (2 * n + 1) ++ [s1]))
        (rep s4 (2 * m + 1))]
  -- Phase 5: sweep_s4_from_B_even m (2m+2 steps)
  rw [show 2 * n + 4 * m + 2 * x + 16 = (2 * m + 2) + (2 * n + 2 * m + 2 * x + 14)
        from by omega, run_add]
  rw [show rep s4 (2 * m + 1) = rep s4 (2 * m + 1) ++ ([] : List Sym) from by simp]
  rw [sweep_s4_from_B_even m
        (s3 :: s1 :: (rep s2 (2 * x + 2) ++ s3 :: s1 :: (rep s2 (2 * n + 1) ++ [s1]))) []]
  simp only [listHd_nil, listTl_nil]
  -- Phase 6: bounce_at_blank (2 steps)
  have h_rep2m : rep s2 (2 * m + 2) = s2 :: rep s2 (2 * m + 1) := by
    show List.replicate _ _ = _
    rw [show 2 * m + 2 = 2 * m + 1 + 1 from by omega]; rfl
  rw [h_rep2m, List.cons_append]
  rw [show 2 * n + 2 * m + 2 * x + 14 = 2 + (2 * n + 2 * m + 2 * x + 12) from by omega, run_add,
      bounce_at_blank (rep s2 (2 * m + 1) ++ s3 :: s1 ::
        (rep s2 (2 * x + 2) ++ s3 :: s1 :: (rep s2 (2 * n + 1) ++ [s1])))]
  -- Phase 7: sweep_s2_to_s3 (2m) (2m+2 steps)
  have h_rep2m1 : rep s2 (2 * m + 1) = s2 :: rep s2 (2 * m) := by
    show List.replicate _ _ = _; rfl
  rw [h_rep2m1]
  simp only [listHd_cons, listTl_cons, List.cons_append]
  rw [show 2 * n + 2 * m + 2 * x + 12 = (2 * m + 2) + (2 * n + 2 * x + 10)
        from by omega, run_add,
      sweep_s2_to_s3 (2 * m) (s1 :: (rep s2 (2 * x + 2) ++ s3 :: s1 ::
        (rep s2 (2 * n + 1) ++ [s1]))) [s1, s2]]
  simp only [listHd_cons, listTl_cons, List.cons_append]
  -- Phase 8: backward_carry (3 steps)
  rw [show 2 * n + 2 * x + 10 = 3 + (2 * n + 2 * x + 7) from by omega, run_add,
      backward_carry (rep s2 (2 * x + 2) ++ s3 :: s1 :: (rep s2 (2 * n + 1) ++ [s1]))
        (rep s4 (2 * m + 1) ++ [s1, s2])]
  have h_rep2x : rep s2 (2 * x + 2) = s2 :: rep s2 (2 * x + 1) := by
    show List.replicate _ _ = _
    rw [show 2 * x + 2 = 2 * x + 1 + 1 from by omega]; rfl
  rw [h_rep2x]
  simp only [listHd_cons, listTl_cons, List.cons_append]
  -- Phase 9: cross_even_digit_backward x (2x+3 steps)
  rw [show 2 * n + 2 * x + 7 = (2 * x + 3) + (2 * n + 4) from by omega, run_add,
      cross_even_digit_backward x (rep s2 (2 * n + 1) ++ [s1])
        (s2 :: s4 :: (rep s4 (2 * m + 1) ++ [s1, s2]))]
  simp only [List.cons_append]
  -- Phase 10: backward_carry (3 steps)
  rw [show 2 * n + 4 = 3 + (2 * n + 1) from by omega, run_add,
      backward_carry (rep s2 (2 * n + 1) ++ [s1])
        (rep s4 (2 * x + 1) ++ s1 :: s2 :: s4 :: (rep s4 (2 * m + 1) ++ [s1, s2]))]
  have hrepn : rep s2 (2 * n + 1) = s2 :: rep s2 (2 * n) := by
    show List.replicate _ _ = _; rfl
  rw [hrepn]
  simp only [listHd_cons, listTl_cons, List.cons_append]
  -- Phase 11: finalize_tail n (2n+1 steps)
  rw [finalize_tail n (s2 :: s4 :: (rep s4 (2 * x + 1) ++ s1 :: s2 :: s4 ::
        (rep s4 (2 * m + 1) ++ [s1, s2])))]
  -- Target: macroRight [2n, 2x+2, 2m+2, 0]
  --   = rep s4 (2n) ++ [s1, s2] ++ rep s4 (2x+2) ++ [s1, s2] ++ rep s4 (2m+2) ++ [s1, s2]
  -- Actual: rep s4 (2n) ++ s1 :: (s2 :: s4 :: (rep s4 (2x+1) ++ s1 :: s4 ::
  --            (rep s4 (2m+1) ++ [s1, s2])))
  --       = rep s4 (2n) ++ [s1, s2] ++ (s4 :: rep s4 (2x+1)) ++ [s1] ++ (s4 :: rep s4 (2m+1))
  --           ++ [s1, s2]
  --       = rep s4 (2n) ++ [s1, s2] ++ rep s4 (2x+2) ++ [s1, s2] ++ rep s4 (2m+2) ++ [s1, s2]
  simp

/-- R3 for arbitrary `AllPosEven middle`: `[2n+1, middle, 2m+2] → [2n, middle, 2m+2, 0]`
    in `4n+4m+16 + middle_cost middle` steps. Composes forward_pass and
    backward_pass around the rule_R3_nil skeleton. -/
theorem rule_R3_general (n m : Nat) (middle : List Nat) (hmid : AllPosEven middle) :
    tmRun (MacroConfig ((2 * n + 1) :: (middle ++ [2 * m + 2])))
        (4 * n + 4 * m + 16 + middle_cost middle) =
      MacroConfig ((2 * n) :: (middle ++ [2 * m + 2, 0])) := by
  show run tm _ _ = _
  simp only [MacroConfig]
  rw [macroRight_R3_input, macroRight_R3_output, middle_cost_eq_two_half]
  have h_first : rep s4 (2 * n + 1) = s4 :: rep s4 (2 * n) := by
    show List.replicate _ _ = _; rfl
  rw [h_first, List.cons_append, List.cons_append]
  -- Phase 1: enter (1 step)
  rw [show 4 * n + 4 * m + 16 + 2 * middle_half_cost middle =
      (4 * n + 4 * m + 15 + 2 * middle_half_cost middle) + 1 from by omega]
  tm_step
  -- Phase 2: sweep_s4_odd_A n (2n+1 steps)
  rw [show 4 * n + 4 * m + 15 + 2 * middle_half_cost middle
        = (2 * n + 1) + (2 * n + 4 * m + 14 + 2 * middle_half_cost middle)
        from by omega, run_add,
      sweep_s4_odd_A n [s1]
        (s1 :: s2 :: (middlePrefix middle ++ rep s4 (2 * m + 2)))]
  simp only [listHd_cons, listTl_cons]
  -- Phase 3: forward_pass middle (middle_half_cost middle steps)
  rw [show 2 * n + 4 * m + 14 + 2 * middle_half_cost middle
        = middle_half_cost middle + (2 * n + 4 * m + 14 + middle_half_cost middle)
        from by omega, run_add,
      forward_pass middle hmid (rep s2 (2 * n + 1) ++ [s1]) (rep s4 (2 * m + 2))]
  -- Expose s4 from rep s4 (2m+2)
  have h_last : rep s4 (2 * m + 2) = s4 :: rep s4 (2 * m + 1) := by
    show List.replicate _ _ = _
    rw [show 2 * m + 2 = 2 * m + 1 + 1 from by omega]; rfl
  rw [h_last]
  -- Phase 4: cross_sep_enter_block (4 steps)
  rw [show 2 * n + 4 * m + 14 + middle_half_cost middle
        = 4 + (2 * n + 4 * m + 10 + middle_half_cost middle) from by omega, run_add,
      cross_sep_enter_block (stack_L middle (rep s2 (2 * n + 1) ++ [s1]))
        (rep s4 (2 * m + 1))]
  -- Phase 5: sweep_s4_from_B_even m (2m+2 steps)
  rw [show 2 * n + 4 * m + 10 + middle_half_cost middle
        = (2 * m + 2) + (2 * n + 2 * m + 8 + middle_half_cost middle)
        from by omega, run_add]
  rw [show rep s4 (2 * m + 1) = rep s4 (2 * m + 1) ++ ([] : List Sym) from by simp]
  rw [sweep_s4_from_B_even m
        (s3 :: s1 :: stack_L middle (rep s2 (2 * n + 1) ++ [s1])) []]
  simp only [listHd_nil, listTl_nil]
  -- Phase 6: bounce_at_blank (2 steps)
  have h_rep2m : rep s2 (2 * m + 2) = s2 :: rep s2 (2 * m + 1) := by
    show List.replicate _ _ = _
    rw [show 2 * m + 2 = 2 * m + 1 + 1 from by omega]; rfl
  rw [h_rep2m, List.cons_append]
  rw [show 2 * n + 2 * m + 8 + middle_half_cost middle
        = 2 + (2 * n + 2 * m + 6 + middle_half_cost middle) from by omega, run_add,
      bounce_at_blank (rep s2 (2 * m + 1) ++ s3 :: s1 ::
        stack_L middle (rep s2 (2 * n + 1) ++ [s1]))]
  -- Phase 7: sweep_s2_to_s3 (2m) (2m+2 steps)
  have h_rep2m1 : rep s2 (2 * m + 1) = s2 :: rep s2 (2 * m) := by
    show List.replicate _ _ = _; rfl
  rw [h_rep2m1]
  simp only [listHd_cons, listTl_cons, List.cons_append]
  rw [show 2 * n + 2 * m + 6 + middle_half_cost middle
        = (2 * m + 2) + (2 * n + 4 + middle_half_cost middle)
        from by omega, run_add,
      sweep_s2_to_s3 (2 * m) (s1 :: stack_L middle (rep s2 (2 * n + 1) ++ [s1]))
        [s1, s2]]
  simp only [listHd_cons, listTl_cons, List.cons_append]
  -- Phase 8: backward_pass middle (middle_half_cost middle + 3 steps)
  rw [show 2 * n + 4 + middle_half_cost middle
        = (middle_half_cost middle + 3) + (2 * n + 1)
        from by omega, run_add,
      backward_pass middle hmid (rep s2 (2 * n + 1) ++ [s1])
        (rep s4 (2 * m + 1) ++ [s1, s2])]
  have hrepn : rep s2 (2 * n + 1) = s2 :: rep s2 (2 * n) := by
    show List.replicate _ _ = _; rfl
  rw [hrepn]
  simp only [listHd_cons, listTl_cons, List.cons_append]
  -- Phase 9: finalize_tail n (2n+1 steps)
  rw [finalize_tail n
        (s2 :: (middlePrefix middle ++ s4 :: (rep s4 (2 * m + 1) ++ [s1, s2])))]
  -- Show final right = rep s4 (2n) ++ [s1, s2] ++ middlePrefix middle ++ rep s4 (2m+2) ++ [s1, s2]
  -- Note: s4 :: rep s4 (2m+1) = rep s4 (2m+2) by h_last (reversed).
  simp [List.append_assoc, ← h_last]

/-- **Rule R3**  `[2n+1, 2a₁, 2a₂, …, 2aⱼ, 2m+2]  →  [2n, 2a₁, …, 2aⱼ, 2m+2, 0]`.
    `middle` is a list of positive even digits. -/
theorem rule_R3 (n m : Nat) (middle : List Nat) (hmid : AllPosEven middle) :
    ∃ steps, 0 < steps ∧
      tmRun (MacroConfig ((2 * n + 1) :: (middle ++ [2 * m + 2]))) steps =
        MacroConfig ((2 * n) :: (middle ++ [2 * m + 2, 0])) := by
  refine ⟨4 * n + 4 * m + 16 + middle_cost middle, by omega, ?_⟩
  exact rule_R3_general n m middle hmid

/-- Concrete base case for R4 (n=0, m=0, middle=[]): `[1, 1] → [0, 1, 1]` in 18 steps. -/
theorem rule_R4_base : tmRun (MacroConfig [1, 1]) 18 = MacroConfig [0, 1, 1] := by
  native_decide

/-- R4 for `middle = []`: `[2n+1, 2m+1] → [2n, 2m+1, 1]` in `4n+4m+18` steps.
    Structurally similar to `rule_R3_nil` but the forward sweep through the
    last block has odd length (ending in state A rather than B). The backward
    phase diverges qualitatively between `m = 0` and `m ≥ 1`. -/
theorem rule_R4_nil (n m : Nat) :
    tmRun (MacroConfig [2 * n + 1, 2 * m + 1]) (4 * n + 4 * m + 18) =
      MacroConfig [2 * n, 2 * m + 1, 1] := by
  show run tm _ _ = _
  simp only [MacroConfig, macroRight_cons_cons, macroRight_singleton]
  have h_first : rep s4 (2 * n + 1) = s4 :: rep s4 (2 * n) := by
    show List.replicate _ _ = _; rfl
  rw [h_first, List.cons_append, List.cons_append]
  -- Phase 1: enter (1 step)
  rw [show 4 * n + 4 * m + 18 = (4 * n + 4 * m + 17) + 1 from by omega]
  tm_step
  -- Phase 2: sweep_s4_odd_A n (2n+1 steps)
  rw [show 4 * n + 4 * m + 17 = (2 * n + 1) + (2 * n + 4 * m + 16) from by omega, run_add,
      sweep_s4_odd_A n [s1] (s1 :: s2 :: rep s4 (2 * m + 1))]
  simp only [listHd_cons, listTl_cons]
  have h_last : rep s4 (2 * m + 1) = s4 :: rep s4 (2 * m) := by
    show List.replicate _ _ = _; rfl
  rw [h_last]
  -- Phase 3: cross_sep_enter_block (4 steps)
  rw [show 2 * n + 4 * m + 16 = 4 + (2 * n + 4 * m + 12) from by omega, run_add,
      cross_sep_enter_block (rep s2 (2 * n + 1) ++ [s1]) (rep s4 (2 * m))]
  -- Phase 4: sweep_s4_from_B_odd m (2m+1 steps)
  rw [show 2 * n + 4 * m + 12 = (2 * m + 1) + (2 * n + 2 * m + 11) from by omega, run_add]
  rw [show rep s4 (2 * m) = rep s4 (2 * m) ++ ([] : List Sym) from by simp]
  rw [sweep_s4_from_B_odd m (s3 :: s1 :: (rep s2 (2 * n + 1) ++ [s1])) []]
  simp only [listHd_nil, listTl_nil]
  -- Phase 5: bounce_at_blank_from_A (2 steps)
  rw [show 2 * n + 2 * m + 11 = 2 + (2 * n + 2 * m + 9) from by omega, run_add,
      bounce_at_blank_from_A
        (rep s2 (2 * m + 1) ++ s3 :: s1 :: (rep s2 (2 * n + 1) ++ [s1]))]
  -- Phase 6+7+8: post-bounce. Case split on m.
  cases m with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add]
    have hrep : rep s2 1 = [s2] := rfl
    rw [hrep, List.cons_append]
    -- Peel 5 individual steps
    rw [show 2 * n + 9 = 2 * n + 4 + 1 + 1 + 1 + 1 + 1 from by omega]
    tm_step; tm_step; tm_step; tm_step; tm_step
    -- Now state A, head s1, left = rep s2 (2n+1) ++ [s1], right = [s2, s1, s2, s4]
    rw [show 2 * n + 4 = 3 + (2 * n + 1) from by omega, run_add,
        backward_carry (rep s2 (2 * n + 1) ++ [s1]) [s1, s2, s4]]
    have hrep2 : rep s2 (2 * n + 1) = s2 :: rep s2 (2 * n) := by
      show List.replicate _ _ = _; rfl
    rw [hrep2]
    simp only [listHd_cons, listTl_cons, List.cons_append]
    rw [finalize_tail n [s2, s4, s1, s2, s4]]
    simp [rep_succ]
  | succ m' =>
    have hrep : rep s2 (2 * (m' + 1) + 1) = s2 :: s2 :: rep s2 (2 * m' + 1) := by
      show List.replicate _ _ = _
      rw [show 2 * (m' + 1) + 1 = 2 * m' + 1 + 1 + 1 from by omega]; rfl
    rw [hrep, List.cons_append, List.cons_append]
    -- Peel 4 individual steps to reach state B, head s2
    rw [show 2 * n + 2 * (m' + 1) + 9 = 2 * n + 2 * m' + 7 + 1 + 1 + 1 + 1 from by omega]
    tm_step; tm_step; tm_step; tm_step
    -- Now state B, head s2, left = rep s2 (2m'+1) ++ s3 :: s1 :: (rep s2 (2n+1) ++ [s1]),
    -- right = [s1, s2, s4]
    rw [show 2 * n + 2 * m' + 7 = (2 * m' + 1 + 2) + (2 * n + 4) from by omega, run_add,
        sweep_s2_to_s3 (2 * m' + 1) (s1 :: (rep s2 (2 * n + 1) ++ [s1])) [s1, s2, s4]]
    simp only [listHd_cons, listTl_cons, List.cons_append]
    rw [show 2 * n + 4 = 3 + (2 * n + 1) from by omega, run_add,
        backward_carry (rep s2 (2 * n + 1) ++ [s1])
          (rep s4 (2 * m' + 1 + 1) ++ [s1, s2, s4])]
    have hrep2 : rep s2 (2 * n + 1) = s2 :: rep s2 (2 * n) := by
      show List.replicate _ _ = _; rfl
    rw [hrep2]
    simp only [listHd_cons, listTl_cons, List.cons_append]
    rw [finalize_tail n (s2 :: s4 :: (rep s4 (2 * m' + 1 + 1) ++ [s1, s2, s4]))]
    have heq : 2 * m' + 1 + 1 = 2 * (m' + 1) := by omega
    rw [heq]
    simp [rep_succ]

/-- R4 for `middle = [2x+2]` (single positive even middle digit):
    `[2n+1, 2x+2, 2m+1] → [2n, 2x+2, 2m+1, 1]` in `4n+4m+4x+30` steps.
    Parallels `rule_R3_single` but with `sweep_s4_from_B_odd` and
    `bounce_at_blank_from_A`; the backward phase splits on `m=0` vs `m≥1`. -/
theorem rule_R4_single (n m x : Nat) :
    tmRun (MacroConfig [2 * n + 1, 2 * x + 2, 2 * m + 1]) (4 * n + 4 * m + 4 * x + 30) =
      MacroConfig [2 * n, 2 * x + 2, 2 * m + 1, 1] := by
  show run tm _ _ = _
  simp only [MacroConfig, macroRight_cons_cons, macroRight_singleton]
  have h_first : rep s4 (2 * n + 1) = s4 :: rep s4 (2 * n) := by
    show List.replicate _ _ = _; rfl
  rw [h_first, List.cons_append, List.cons_append]
  -- Phase 1: enter (1 step)
  rw [show 4 * n + 4 * m + 4 * x + 30 = (4 * n + 4 * m + 4 * x + 29) + 1 from by omega]
  tm_step
  -- Phase 2: sweep_s4_odd_A n (2n+1 steps)
  rw [show 4 * n + 4 * m + 4 * x + 29 = (2 * n + 1) + (2 * n + 4 * m + 4 * x + 28)
        from by omega, run_add,
      sweep_s4_odd_A n [s1]
        (s1 :: s2 :: (rep s4 (2 * x + 2) ++ s1 :: s2 :: rep s4 (2 * m + 1)))]
  simp only [listHd_cons, listTl_cons]
  -- Phase 3: cross_even_digit_forward x (2x+6 steps)
  rw [show 2 * n + 4 * m + 4 * x + 28 = (2 * x + 6) + (2 * n + 4 * m + 2 * x + 22)
        from by omega, run_add]
  rw [show (s1 :: s2 :: rep s4 (2 * m + 1) : List Sym) = [s1, s2] ++ rep s4 (2 * m + 1)
        from rfl, ← List.append_assoc]
  rw [cross_even_digit_forward x (rep s2 (2 * n + 1) ++ [s1]) (rep s4 (2 * m + 1))]
  have h_last : rep s4 (2 * m + 1) = s4 :: rep s4 (2 * m) := by
    show List.replicate _ _ = _; rfl
  rw [h_last]
  -- Phase 4: cross_sep_enter_block (4 steps)
  rw [show 2 * n + 4 * m + 2 * x + 22 = 4 + (2 * n + 4 * m + 2 * x + 18) from by omega, run_add,
      cross_sep_enter_block (rep s2 (2 * x + 2) ++ s3 :: s1 :: (rep s2 (2 * n + 1) ++ [s1]))
        (rep s4 (2 * m))]
  -- Phase 5: sweep_s4_from_B_odd m (2m+1 steps)
  rw [show 2 * n + 4 * m + 2 * x + 18 = (2 * m + 1) + (2 * n + 2 * m + 2 * x + 17)
        from by omega, run_add]
  rw [show rep s4 (2 * m) = rep s4 (2 * m) ++ ([] : List Sym) from by simp]
  rw [sweep_s4_from_B_odd m
        (s3 :: s1 :: (rep s2 (2 * x + 2) ++ s3 :: s1 :: (rep s2 (2 * n + 1) ++ [s1]))) []]
  simp only [listHd_nil, listTl_nil]
  -- Phase 6: bounce_at_blank_from_A (2 steps)
  rw [show 2 * n + 2 * m + 2 * x + 17 = 2 + (2 * n + 2 * m + 2 * x + 15) from by omega, run_add,
      bounce_at_blank_from_A (rep s2 (2 * m + 1) ++ s3 :: s1 ::
        (rep s2 (2 * x + 2) ++ s3 :: s1 :: (rep s2 (2 * n + 1) ++ [s1])))]
  -- Phase 7+: case on m for backward phase (same shape as rule_R4_nil)
  cases m with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    have hrep_m : rep s2 1 = [s2] := rfl
    rw [hrep_m, List.cons_append, List.nil_append]
    -- Peel 5 individual steps
    rw [show 2 * n + 2 * x + 15 = 2 * n + 2 * x + 10 + 1 + 1 + 1 + 1 + 1 from by omega]
    tm_step; tm_step; tm_step; tm_step; tm_step
    -- Now state A, head s1, left = rep s2 (2x+2) ++ s3 :: s1 :: rep s2 (2n+1) ++ [s1],
    -- right = [s2, s1, s2, s4]
    rw [show 2 * n + 2 * x + 10 = 3 + (2 * n + 2 * x + 7) from by omega, run_add,
        backward_carry (rep s2 (2 * x + 2) ++ s3 :: s1 :: (rep s2 (2 * n + 1) ++ [s1]))
          [s1, s2, s4]]
    have h_rep2x : rep s2 (2 * x + 2) = s2 :: rep s2 (2 * x + 1) := by
      show List.replicate _ _ = _
      rw [show 2 * x + 2 = 2 * x + 1 + 1 from by omega]; rfl
    rw [h_rep2x]
    simp only [listHd_cons, listTl_cons, List.cons_append]
    -- cross_even_digit_backward x (2x+3 steps)
    rw [show 2 * n + 2 * x + 7 = (2 * x + 3) + (2 * n + 4) from by omega, run_add,
        cross_even_digit_backward x (rep s2 (2 * n + 1) ++ [s1]) (s2 :: s4 :: [s1, s2, s4])]
    simp only [List.cons_append]
    -- backward_carry (3 steps)
    rw [show 2 * n + 4 = 3 + (2 * n + 1) from by omega, run_add,
        backward_carry (rep s2 (2 * n + 1) ++ [s1])
          (rep s4 (2 * x + 1) ++ s1 :: s2 :: s4 :: [s1, s2, s4])]
    have hrepn : rep s2 (2 * n + 1) = s2 :: rep s2 (2 * n) := by
      show List.replicate _ _ = _; rfl
    rw [hrepn]
    simp only [listHd_cons, listTl_cons, List.cons_append]
    rw [finalize_tail n (s2 :: s4 :: (rep s4 (2 * x + 1) ++ s1 :: s2 :: s4 :: [s1, s2, s4]))]
    simp [rep_succ]
  | succ m' =>
    have hrep_m : rep s2 (2 * (m' + 1) + 1) = s2 :: s2 :: rep s2 (2 * m' + 1) := by
      show List.replicate _ _ = _
      rw [show 2 * (m' + 1) + 1 = 2 * m' + 1 + 1 + 1 from by omega]; rfl
    rw [hrep_m, List.cons_append, List.cons_append]
    -- Peel 4 individual steps to reach state B, head s2
    rw [show 2 * n + 2 * (m' + 1) + 2 * x + 15 = 2 * n + 2 * m' + 2 * x + 13 + 1 + 1 + 1 + 1
        from by omega]
    tm_step; tm_step; tm_step; tm_step
    -- Now state B, head s2, left = rep s2 (2m'+1) ++ s3 :: s1 :: (rep s2 (2x+2) ++ s3 :: s1 ::
    --                                       rep s2 (2n+1) ++ [s1]), right = [s1, s2, s4]
    rw [show 2 * n + 2 * m' + 2 * x + 13 = (2 * m' + 1 + 2) + (2 * n + 2 * x + 10)
          from by omega, run_add,
        sweep_s2_to_s3 (2 * m' + 1)
          (s1 :: (rep s2 (2 * x + 2) ++ s3 :: s1 :: (rep s2 (2 * n + 1) ++ [s1])))
          [s1, s2, s4]]
    simp only [listHd_cons, listTl_cons, List.cons_append]
    -- backward_carry (3 steps) + peel rep s2 (2x+2) into s2 :: ...
    rw [show 2 * n + 2 * x + 10 = 3 + (2 * n + 2 * x + 7) from by omega, run_add,
        backward_carry (rep s2 (2 * x + 2) ++ s3 :: s1 :: (rep s2 (2 * n + 1) ++ [s1]))
          (rep s4 (2 * m' + 1 + 1) ++ [s1, s2, s4])]
    have h_rep2x : rep s2 (2 * x + 2) = s2 :: rep s2 (2 * x + 1) := by
      show List.replicate _ _ = _
      rw [show 2 * x + 2 = 2 * x + 1 + 1 from by omega]; rfl
    rw [h_rep2x]
    simp only [listHd_cons, listTl_cons, List.cons_append]
    -- cross_even_digit_backward x (2x+3 steps)
    rw [show 2 * n + 2 * x + 7 = (2 * x + 3) + (2 * n + 4) from by omega, run_add,
        cross_even_digit_backward x (rep s2 (2 * n + 1) ++ [s1])
          (s2 :: s4 :: (rep s4 (2 * m' + 1 + 1) ++ [s1, s2, s4]))]
    simp only [List.cons_append]
    -- backward_carry (3 steps)
    rw [show 2 * n + 4 = 3 + (2 * n + 1) from by omega, run_add,
        backward_carry (rep s2 (2 * n + 1) ++ [s1])
          (rep s4 (2 * x + 1) ++ s1 :: s2 :: s4 ::
            (rep s4 (2 * m' + 1 + 1) ++ [s1, s2, s4]))]
    have hrepn : rep s2 (2 * n + 1) = s2 :: rep s2 (2 * n) := by
      show List.replicate _ _ = _; rfl
    rw [hrepn]
    simp only [listHd_cons, listTl_cons, List.cons_append]
    rw [finalize_tail n (s2 :: s4 :: (rep s4 (2 * x + 1) ++ s1 :: s2 :: s4 ::
          (rep s4 (2 * m' + 1 + 1) ++ [s1, s2, s4])))]
    have heq : 2 * m' + 1 + 1 = 2 * (m' + 1) := by omega
    rw [heq]
    simp [rep_succ]

/-- R4 for arbitrary `AllPosEven middle`: `[2n+1, middle, 2m+1] → [2n, middle, 2m+1, 1]`
    in `4n+4m+18 + middle_cost middle` steps. Composes forward_pass and
    backward_pass around the rule_R4_nil skeleton, with the m=0/m≥1 case split. -/
theorem rule_R4_general (n m : Nat) (middle : List Nat) (hmid : AllPosEven middle) :
    tmRun (MacroConfig ((2 * n + 1) :: (middle ++ [2 * m + 1])))
        (4 * n + 4 * m + 18 + middle_cost middle) =
      MacroConfig ((2 * n) :: (middle ++ [2 * m + 1, 1])) := by
  show run tm _ _ = _
  simp only [MacroConfig]
  rw [macroRight_R4_input, macroRight_R4_output, middle_cost_eq_two_half]
  have h_first : rep s4 (2 * n + 1) = s4 :: rep s4 (2 * n) := by
    show List.replicate _ _ = _; rfl
  rw [h_first, List.cons_append, List.cons_append]
  -- Phase 1: enter (1 step)
  rw [show 4 * n + 4 * m + 18 + 2 * middle_half_cost middle =
      (4 * n + 4 * m + 17 + 2 * middle_half_cost middle) + 1 from by omega]
  tm_step
  -- Phase 2: sweep_s4_odd_A n (2n+1 steps)
  rw [show 4 * n + 4 * m + 17 + 2 * middle_half_cost middle
        = (2 * n + 1) + (2 * n + 4 * m + 16 + 2 * middle_half_cost middle)
        from by omega, run_add,
      sweep_s4_odd_A n [s1]
        (s1 :: s2 :: (middlePrefix middle ++ rep s4 (2 * m + 1)))]
  simp only [listHd_cons, listTl_cons]
  -- Phase 3: forward_pass middle (middle_half_cost middle steps)
  rw [show 2 * n + 4 * m + 16 + 2 * middle_half_cost middle
        = middle_half_cost middle + (2 * n + 4 * m + 16 + middle_half_cost middle)
        from by omega, run_add,
      forward_pass middle hmid (rep s2 (2 * n + 1) ++ [s1]) (rep s4 (2 * m + 1))]
  have h_last : rep s4 (2 * m + 1) = s4 :: rep s4 (2 * m) := by
    show List.replicate _ _ = _; rfl
  rw [h_last]
  -- Phase 4: cross_sep_enter_block (4 steps)
  rw [show 2 * n + 4 * m + 16 + middle_half_cost middle
        = 4 + (2 * n + 4 * m + 12 + middle_half_cost middle) from by omega, run_add,
      cross_sep_enter_block (stack_L middle (rep s2 (2 * n + 1) ++ [s1]))
        (rep s4 (2 * m))]
  -- Phase 5: sweep_s4_from_B_odd m (2m+1 steps)
  rw [show 2 * n + 4 * m + 12 + middle_half_cost middle
        = (2 * m + 1) + (2 * n + 2 * m + 11 + middle_half_cost middle)
        from by omega, run_add]
  rw [show rep s4 (2 * m) = rep s4 (2 * m) ++ ([] : List Sym) from by simp]
  rw [sweep_s4_from_B_odd m
        (s3 :: s1 :: stack_L middle (rep s2 (2 * n + 1) ++ [s1])) []]
  simp only [listHd_nil, listTl_nil]
  -- Phase 6: bounce_at_blank_from_A (2 steps)
  rw [show 2 * n + 2 * m + 11 + middle_half_cost middle
        = 2 + (2 * n + 2 * m + 9 + middle_half_cost middle) from by omega, run_add,
      bounce_at_blank_from_A (rep s2 (2 * m + 1) ++ s3 :: s1 ::
        stack_L middle (rep s2 (2 * n + 1) ++ [s1]))]
  cases m with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    have hrep_m : rep s2 1 = [s2] := rfl
    rw [hrep_m, List.cons_append, List.nil_append]
    -- Peel 5 direct steps
    rw [show 2 * n + 9 + middle_half_cost middle
          = 2 * n + 4 + middle_half_cost middle + 1 + 1 + 1 + 1 + 1 from by omega]
    tm_step; tm_step; tm_step; tm_step; tm_step
    -- Now state A, head s1, left = stack_L middle (rep s2 (2n+1) ++ [s1]),
    -- right = [s2, s1, s2, s4]
    -- Apply backward_pass middle (middle_half_cost middle + 3 steps) then finalize_tail
    rw [show 2 * n + 4 + middle_half_cost middle
          = (middle_half_cost middle + 3) + (2 * n + 1) from by omega, run_add,
        backward_pass middle hmid (rep s2 (2 * n + 1) ++ [s1]) [s1, s2, s4]]
    have hrepn : rep s2 (2 * n + 1) = s2 :: rep s2 (2 * n) := by
      show List.replicate _ _ = _; rfl
    rw [hrepn]
    simp only [listHd_cons, listTl_cons, List.cons_append]
    rw [finalize_tail n (s2 :: (middlePrefix middle ++ s4 :: [s1, s2, s4]))]
    simp [rep_succ, List.append_assoc]
  | succ m' =>
    have hrep_m : rep s2 (2 * (m' + 1) + 1) = s2 :: s2 :: rep s2 (2 * m' + 1) := by
      show List.replicate _ _ = _
      rw [show 2 * (m' + 1) + 1 = 2 * m' + 1 + 1 + 1 from by omega]; rfl
    rw [hrep_m, List.cons_append, List.cons_append]
    -- Peel 4 direct steps
    rw [show 2 * n + 2 * (m' + 1) + 9 + middle_half_cost middle
          = 2 * n + 2 * m' + 7 + middle_half_cost middle + 1 + 1 + 1 + 1 from by omega]
    tm_step; tm_step; tm_step; tm_step
    -- Now state B, head s2, left = rep s2 (2m'+1) ++ s3 :: s1 :: stack_L middle (...),
    -- right = [s1, s2, s4]
    rw [show 2 * n + 2 * m' + 7 + middle_half_cost middle
          = (2 * m' + 1 + 2) + (2 * n + 4 + middle_half_cost middle)
          from by omega, run_add,
        sweep_s2_to_s3 (2 * m' + 1)
          (s1 :: stack_L middle (rep s2 (2 * n + 1) ++ [s1])) [s1, s2, s4]]
    simp only [listHd_cons, listTl_cons, List.cons_append]
    rw [show 2 * n + 4 + middle_half_cost middle
          = (middle_half_cost middle + 3) + (2 * n + 1) from by omega, run_add,
        backward_pass middle hmid (rep s2 (2 * n + 1) ++ [s1])
          (rep s4 (2 * m' + 1 + 1) ++ [s1, s2, s4])]
    have hrepn : rep s2 (2 * n + 1) = s2 :: rep s2 (2 * n) := by
      show List.replicate _ _ = _; rfl
    rw [hrepn]
    simp only [listHd_cons, listTl_cons, List.cons_append]
    rw [finalize_tail n
         (s2 :: (middlePrefix middle ++ s4 :: (rep s4 (2 * m' + 1 + 1) ++ [s1, s2, s4])))]
    have heq : 2 * m' + 1 + 1 = 2 * (m' + 1) := by omega
    rw [heq]
    simp [rep_succ, List.append_assoc]

/-- **Rule R4**  `[2n+1, 2a₁, …, 2aⱼ, 2m+1]  →  [2n, 2a₁, …, 2aⱼ, 2m+1, 1]`.
    `middle` is a list of positive even digits. -/
theorem rule_R4 (n m : Nat) (middle : List Nat) (hmid : AllPosEven middle) :
    ∃ steps, 0 < steps ∧
      tmRun (MacroConfig ((2 * n + 1) :: (middle ++ [2 * m + 1]))) steps =
        MacroConfig ((2 * n) :: (middle ++ [2 * m + 1, 1])) := by
  refine ⟨4 * n + 4 * m + 18 + middle_cost middle, by omega, ?_⟩
  exact rule_R4_general n m middle hmid

/-- Concrete base case for R5 (n=0, m=1, x=0, middle=[], rest=[]):
    `[1, 3, 0] → [0, 3, 1]` in 20 steps. -/
theorem rule_R5_base : tmRun (MacroConfig [1, 3, 0]) 20 = MacroConfig [0, 3, 1] := by
  native_decide

/-- R5 for `middle = []` with arbitrary trailing tape `Tail`:
    `4n+4m+16` steps take `rep s4 (2n+1) ++ [s1, s2] ++ rep s4 (2m+1) ++ [s1, s2] ++
    rep s4 x ++ Tail` to `rep s4 (2n) ++ [s1, s2] ++ rep s4 (2m+1) ++ [s1, s2] ++
    rep s4 (x+1) ++ Tail`. The head does NOT reach blank — it turns around
    after the `2m+1` block. -/
theorem rule_R5_core_tail (n m x : Nat) (Tail : List Sym) :
    run tm ({state := some stB, head := s1, left := [],
             right := rep s4 (2 * n + 1) ++ [s1, s2] ++ rep s4 (2 * m + 1) ++ [s1, s2] ++
                      rep s4 x ++ Tail} : Config) (4 * n + 4 * m + 16) =
      {state := some stB, head := s1, left := [],
       right := rep s4 (2 * n) ++ [s1, s2] ++ rep s4 (2 * m + 1) ++ [s1, s2] ++
                rep s4 (x + 1) ++ Tail} := by
  have h_first : rep s4 (2 * n + 1) = s4 :: rep s4 (2 * n) := by
    show List.replicate _ _ = _; rfl
  rw [h_first]
  simp only [List.cons_append, List.append_assoc]
  -- Phase 1: enter (1 step)
  rw [show 4 * n + 4 * m + 16 = (4 * n + 4 * m + 15) + 1 from by omega]
  tm_step
  -- Phase 2: sweep_s4_odd_A n (2n+1 steps)
  rw [show 4 * n + 4 * m + 15 = (2 * n + 1) + (2 * n + 4 * m + 14) from by omega, run_add,
      sweep_s4_odd_A n [s1]
        (s1 :: s2 :: (rep s4 (2 * m + 1) ++ s1 :: s2 :: (rep s4 x ++ Tail)))]
  simp only [listHd_cons, listTl_cons]
  have h_mid : rep s4 (2 * m + 1) = s4 :: rep s4 (2 * m) := by
    show List.replicate _ _ = _; rfl
  rw [h_mid]
  simp only [List.cons_append]
  -- Phase 3: cross_sep_enter_block (4 steps)
  rw [show 2 * n + 4 * m + 14 = 4 + (2 * n + 4 * m + 10) from by omega, run_add,
      cross_sep_enter_block (rep s2 (2 * n + 1) ++ [s1])
        (rep s4 (2 * m) ++ s1 :: s2 :: (rep s4 x ++ Tail))]
  -- Phase 4: sweep_s4_from_B_odd m (2m+1 steps)
  rw [show 2 * n + 4 * m + 10 = (2 * m + 1) + (2 * n + 2 * m + 9) from by omega, run_add,
      sweep_s4_from_B_odd m (s3 :: s1 :: (rep s2 (2 * n + 1) ++ [s1]))
        (s1 :: s2 :: (rep s4 x ++ Tail))]
  simp only [listHd_cons, listTl_cons]
  -- Phase 5-8: 4 direct steps modify the x-block to x+1; case on m
  cases m with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    have hrep_m : rep s2 1 = [s2] := rfl
    rw [hrep_m, List.cons_append, List.nil_append]
    rw [show 2 * n + 9 = 2 * n + 4 + 1 + 1 + 1 + 1 + 1 from by omega]
    tm_step; tm_step; tm_step; tm_step; tm_step
    rw [show (s4 :: (rep s4 x ++ Tail) : List Sym) = rep s4 (x + 1) ++ Tail from rfl]
    rw [show 2 * n + 4 = 3 + (2 * n + 1) from by omega, run_add,
        backward_carry (rep s2 (2 * n + 1) ++ [s1]) (s1 :: s2 :: (rep s4 (x + 1) ++ Tail))]
    have hrepn : rep s2 (2 * n + 1) = s2 :: rep s2 (2 * n) := by
      show List.replicate _ _ = _; rfl
    rw [hrepn]
    simp only [listHd_cons, listTl_cons, List.cons_append]
    rw [finalize_tail n (s2 :: s4 :: s1 :: s2 :: (rep s4 (x + 1) ++ Tail))]
    simp [rep_succ]
  | succ m' =>
    have hrep_m : rep s2 (2 * (m' + 1) + 1) = s2 :: s2 :: rep s2 (2 * m' + 1) := by
      show List.replicate _ _ = _
      rw [show 2 * (m' + 1) + 1 = 2 * m' + 1 + 1 + 1 from by omega]; rfl
    rw [hrep_m, List.cons_append, List.cons_append]
    rw [show 2 * n + 2 * (m' + 1) + 9 = 2 * n + 2 * m' + 7 + 1 + 1 + 1 + 1 from by omega]
    tm_step; tm_step; tm_step; tm_step
    rw [show (s4 :: (rep s4 x ++ Tail) : List Sym) = rep s4 (x + 1) ++ Tail from rfl]
    rw [show 2 * n + 2 * m' + 7 = (2 * m' + 1 + 2) + (2 * n + 4) from by omega, run_add,
        sweep_s2_to_s3 (2 * m' + 1) (s1 :: (rep s2 (2 * n + 1) ++ [s1]))
          (s1 :: s2 :: (rep s4 (x + 1) ++ Tail))]
    simp only [listHd_cons, listTl_cons, List.cons_append]
    rw [show 2 * n + 4 = 3 + (2 * n + 1) from by omega, run_add,
        backward_carry (rep s2 (2 * n + 1) ++ [s1])
          (rep s4 (2 * m' + 1 + 1) ++ s1 :: s2 :: (rep s4 (x + 1) ++ Tail))]
    have hrepn : rep s2 (2 * n + 1) = s2 :: rep s2 (2 * n) := by
      show List.replicate _ _ = _; rfl
    rw [hrepn]
    simp only [listHd_cons, listTl_cons, List.cons_append]
    rw [finalize_tail n
         (s2 :: s4 :: (rep s4 (2 * m' + 1 + 1) ++ s1 :: s2 :: (rep s4 (x + 1) ++ Tail)))]
    have heq : 2 * m' + 1 + 1 = 2 * (m' + 1) := by omega
    rw [heq]

/-- R5 for `middle = []` and `rest = []`: `[2n+1, 2m+1, x] → [2n, 2m+1, x+1]`
    in `4n+4m+16` steps. Derived from `rule_R5_core_tail` with empty tail. -/
theorem rule_R5_simple (n m x : Nat) :
    tmRun (MacroConfig [2 * n + 1, 2 * m + 1, x]) (4 * n + 4 * m + 16) =
      MacroConfig [2 * n, 2 * m + 1, x + 1] := by
  have h := rule_R5_core_tail n m x []
  show run tm _ _ = _
  simp only [MacroConfig, macroRight_cons_cons, macroRight_singleton, List.append_assoc]
  convert h using 2 <;> simp

/-- R5 with arbitrary `AllPosEven middle` and arbitrary trailing tape `Tail`.
    Composes `forward_pass` + R5's local x-block rewrite + `backward_pass`
    around the `rule_R5_core_tail` skeleton. The step count is
    `4n+4m+16 + middle_cost middle`. -/
theorem rule_R5_core_with_middle (n m x : Nat) (middle : List Nat) (hmid : AllPosEven middle)
    (Tail : List Sym) :
    run tm ({ state := some stB, head := s1, left := [],
              right := rep s4 (2 * n + 1) ++ [s1, s2] ++ middlePrefix middle ++
                        rep s4 (2 * m + 1) ++ [s1, s2] ++ rep s4 x ++ Tail } : Config)
        (4 * n + 4 * m + 16 + middle_cost middle) =
      { state := some stB, head := s1, left := [],
        right := rep s4 (2 * n) ++ [s1, s2] ++ middlePrefix middle ++
                 rep s4 (2 * m + 1) ++ [s1, s2] ++ rep s4 (x + 1) ++ Tail } := by
  have h_first : rep s4 (2 * n + 1) = s4 :: rep s4 (2 * n) := by
    show List.replicate _ _ = _; rfl
  rw [h_first]
  simp only [List.cons_append, List.append_assoc]
  rw [middle_cost_eq_two_half]
  -- Phase 1: enter (1 step)
  rw [show 4 * n + 4 * m + 16 + 2 * middle_half_cost middle
        = (4 * n + 4 * m + 15 + 2 * middle_half_cost middle) + 1 from by omega]
  tm_step
  -- Phase 2: sweep_s4_odd_A n (2n+1 steps)
  rw [show 4 * n + 4 * m + 15 + 2 * middle_half_cost middle
        = (2 * n + 1) + (2 * n + 4 * m + 14 + 2 * middle_half_cost middle)
        from by omega, run_add,
      sweep_s4_odd_A n [s1]
        (s1 :: s2 :: (middlePrefix middle ++ (rep s4 (2 * m + 1) ++
          s1 :: s2 :: (rep s4 x ++ Tail))))]
  simp only [listHd_cons, listTl_cons]
  -- Phase 3: forward_pass middle (middle_half_cost steps)
  rw [show 2 * n + 4 * m + 14 + 2 * middle_half_cost middle
        = middle_half_cost middle + (2 * n + 4 * m + 14 + middle_half_cost middle)
        from by omega, run_add]
  rw [show (rep s4 (2 * m + 1) ++ s1 :: s2 :: (rep s4 x ++ Tail) : List Sym) =
          rep s4 (2 * m + 1) ++ ([s1, s2] ++ (rep s4 x ++ Tail))
        from by simp [List.append_assoc]]
  rw [forward_pass middle hmid (rep s2 (2 * n + 1) ++ [s1])
        (rep s4 (2 * m + 1) ++ ([s1, s2] ++ (rep s4 x ++ Tail)))]
  have h_mid : rep s4 (2 * m + 1) = s4 :: rep s4 (2 * m) := by
    show List.replicate _ _ = _; rfl
  rw [h_mid]
  simp only [List.cons_append, List.nil_append]
  -- Phase 4: cross_sep_enter_block (4 steps)
  rw [show 2 * n + 4 * m + 14 + middle_half_cost middle
        = 4 + (2 * n + 4 * m + 10 + middle_half_cost middle) from by omega, run_add,
      cross_sep_enter_block (stack_L middle (rep s2 (2 * n + 1) ++ [s1]))
        (rep s4 (2 * m) ++ s1 :: s2 :: (rep s4 x ++ Tail))]
  -- Phase 5: sweep_s4_from_B_odd m (2m+1 steps)
  rw [show 2 * n + 4 * m + 10 + middle_half_cost middle
        = (2 * m + 1) + (2 * n + 2 * m + 9 + middle_half_cost middle)
        from by omega, run_add,
      sweep_s4_from_B_odd m
        (s3 :: s1 :: stack_L middle (rep s2 (2 * n + 1) ++ [s1]))
        (s1 :: s2 :: (rep s4 x ++ Tail))]
  simp only [listHd_cons, listTl_cons]
  cases m with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    have hrep_m : rep s2 1 = [s2] := rfl
    rw [hrep_m, List.cons_append, List.nil_append]
    -- Peel 5 direct steps
    rw [show 2 * n + 9 + middle_half_cost middle
          = 2 * n + 4 + middle_half_cost middle + 1 + 1 + 1 + 1 + 1 from by omega]
    tm_step; tm_step; tm_step; tm_step; tm_step
    -- Now state A, head s1, left = stack_L middle (rep s2 (2n+1) ++ [s1]),
    -- right = s2 :: s1 :: s2 :: s4 :: rep s4 x ++ Tail
    rw [show (s4 :: (rep s4 x ++ Tail) : List Sym) = rep s4 (x + 1) ++ Tail from rfl]
    -- Apply backward_pass middle
    rw [show 2 * n + 4 + middle_half_cost middle
          = (middle_half_cost middle + 3) + (2 * n + 1) from by omega, run_add,
        backward_pass middle hmid (rep s2 (2 * n + 1) ++ [s1])
          (s1 :: s2 :: (rep s4 (x + 1) ++ Tail))]
    have hrepn : rep s2 (2 * n + 1) = s2 :: rep s2 (2 * n) := by
      show List.replicate _ _ = _; rfl
    rw [hrepn]
    simp only [listHd_cons, listTl_cons, List.cons_append]
    rw [finalize_tail n (s2 :: (middlePrefix middle ++ s4 ::
          s1 :: s2 :: (rep s4 (x + 1) ++ Tail)))]
    simp [rep_succ, List.append_assoc]
  | succ m' =>
    have hrep_m : rep s2 (2 * (m' + 1) + 1) = s2 :: s2 :: rep s2 (2 * m' + 1) := by
      show List.replicate _ _ = _
      rw [show 2 * (m' + 1) + 1 = 2 * m' + 1 + 1 + 1 from by omega]; rfl
    rw [hrep_m, List.cons_append, List.cons_append]
    -- Peel 4 direct steps
    rw [show 2 * n + 2 * (m' + 1) + 9 + middle_half_cost middle
          = 2 * n + 2 * m' + 7 + middle_half_cost middle + 1 + 1 + 1 + 1 from by omega]
    tm_step; tm_step; tm_step; tm_step
    rw [show (s4 :: (rep s4 x ++ Tail) : List Sym) = rep s4 (x + 1) ++ Tail from rfl]
    -- Now state B head s2, left = rep s2 (2m'+1) ++ s3 :: s1 :: stack_L middle (...),
    -- right = s1 :: s2 :: rep s4 (x+1) ++ Tail
    rw [show 2 * n + 2 * m' + 7 + middle_half_cost middle
          = (2 * m' + 1 + 2) + (2 * n + 4 + middle_half_cost middle)
          from by omega, run_add,
        sweep_s2_to_s3 (2 * m' + 1)
          (s1 :: stack_L middle (rep s2 (2 * n + 1) ++ [s1]))
          (s1 :: s2 :: (rep s4 (x + 1) ++ Tail))]
    simp only [listHd_cons, listTl_cons, List.cons_append]
    -- Apply backward_pass middle
    rw [show 2 * n + 4 + middle_half_cost middle
          = (middle_half_cost middle + 3) + (2 * n + 1) from by omega, run_add,
        backward_pass middle hmid (rep s2 (2 * n + 1) ++ [s1])
          (rep s4 (2 * m' + 1 + 1) ++ s1 :: s2 :: (rep s4 (x + 1) ++ Tail))]
    have hrepn : rep s2 (2 * n + 1) = s2 :: rep s2 (2 * n) := by
      show List.replicate _ _ = _; rfl
    rw [hrepn]
    simp only [listHd_cons, listTl_cons, List.cons_append]
    rw [finalize_tail n (s2 :: (middlePrefix middle ++ s4 ::
          (rep s4 (2 * m' + 1 + 1) ++ s1 :: s2 :: (rep s4 (x + 1) ++ Tail))))]
    have heq : 2 * m' + 1 + 1 = 2 * (m' + 1) := by omega
    rw [heq]

/-- Trailing tape for R5's rest list: empty tail if rest is empty, else the
    `[s1, s2]` separator plus macroRight of the rest. -/
def R5_tail : List Nat → List Sym
  | []      => []
  | r :: rs => s1 :: s2 :: macroRight (r :: rs)

/-- Unfold `macroRight ((a) :: middle ++ (m') :: x :: rest)` into the explicit
    block/separator structure. Used for both R5 input (a = 2n+1, m' = 2m+1)
    and R5 output (a = 2n, m' = 2m+1). -/
theorem macroRight_R5_unfold (a : Nat) (middle : List Nat) (m' x : Nat) (rest : List Nat) :
    macroRight (a :: (middle ++ m' :: x :: rest)) =
      rep s4 a ++ [s1, s2] ++ middlePrefix middle ++ rep s4 m' ++ [s1, s2] ++
        rep s4 x ++ R5_tail rest := by
  induction middle generalizing a with
  | nil =>
    cases rest with
    | nil =>
      show macroRight (a :: [m', x]) = _
      simp [macroRight, middlePrefix, R5_tail, List.append_assoc]
    | cons r rs =>
      show macroRight (a :: m' :: x :: (r :: rs)) = _
      rw [macroRight_cons_cons, macroRight_cons_cons, macroRight_cons_cons]
      simp [middlePrefix, R5_tail, List.append_assoc]
  | cons y ys ih =>
    show macroRight (a :: (y :: (ys ++ m' :: x :: rest))) = _
    rw [macroRight_cons_cons]
    rw [ih y]
    simp [middlePrefix, List.append_assoc]

/-- **Rule R5**  `[2n+1, 2a₁, …, 2aⱼ, 2m+1, x, …rest]
                 →  [2n, 2a₁, …, 2aⱼ, 2m+1, x+1, …rest]`.
    `middle` is a list of positive even digits; `rest` is arbitrary. -/
theorem rule_R5 (n m x : Nat) (middle rest : List Nat) (hmid : AllPosEven middle) :
    ∃ steps, 0 < steps ∧
      tmRun (MacroConfig ((2 * n + 1) :: (middle ++ (2 * m + 1) :: x :: rest))) steps =
        MacroConfig ((2 * n) :: (middle ++ (2 * m + 1) :: (x + 1) :: rest)) := by
  refine ⟨4 * n + 4 * m + 16 + middle_cost middle, by omega, ?_⟩
  show run tm _ _ = _
  simp only [MacroConfig]
  rw [macroRight_R5_unfold (2 * n + 1) middle (2 * m + 1) x rest,
      macroRight_R5_unfold (2 * n) middle (2 * m + 1) (x + 1) rest]
  exact rule_R5_core_with_middle n m x middle hmid (R5_tail rest)

-- Rule R2 is a halt precondition, not a transition. We will prove that
-- configurations of the form `[2n+1, evens…, 0]` are unreachable from `[1, 1]`,
-- packaged inside the canonical invariant `ValidDigits` below.

-- ============================================================
-- Section 6: Canonical invariant and progress
-- ============================================================

/-- The canonical macro shape. A list of digits `xs` is canonical when:
    * it has at least two elements (so some rule applies), and
    * if the first digit is odd and all middle digits are even, then the
      last digit is non-zero (so R2 is not triggered).
    The second clause is an **invariant**, not something to check pointwise:
    we maintain it as we progress through the rules. -/
def ValidDigits (xs : List Nat) : Prop :=
  2 ≤ xs.length ∧
  (∀ n middle,
      xs = (2 * n + 1) :: middle ++ [0] → ¬ AllEven middle)

/-- Any canonical configuration is a valid `MacroConfig`. -/
def IsCanonical (c : Config) : Prop :=
  ∃ xs, c = MacroConfig xs ∧ ValidDigits xs

/-- Rules R1, R3, R4, R5, R6 collectively advance every valid canonical
    configuration to another valid canonical configuration. Rule R2 is
    excluded by the invariant in `ValidDigits`.

    **Status**: The proof requires a strengthened `ValidDigits` invariant
    (current version is too weak — it allows `[0, a]` and doesn't ensure
    `AllPosEven middle` which R3/R4 now require). See `TODO_canonical_progress.md`
    for the full analysis. Concretely, we'd need additional clauses:
    - `xs.head? = some 0 → 3 ≤ xs.length`
    - `xs = (2*n+1) :: middle ++ [last] ∧ last ≠ 0 ∧ AllEven middle → AllPosEven middle`
    - `xs = (2*n+2) :: a :: rest ∧ rest.getLast? = some 0 → Even a`
    Each rule then requires a preservation lemma, plus the progress witness. -/
theorem canonical_progress :
    ∀ c, IsCanonical c →
      ∃ k, 0 < k ∧ IsCanonical (tmRun c k) ∧ (tmRun c k).state ≠ none := by
  sorry

/-- After 17 steps, the machine reaches a canonical configuration. -/
theorem reaches_canonical : IsCanonical (tmRun initConfig 17) := by
  refine ⟨[1, 1], init_to_macro, ?_, ?_⟩
  · decide
  · -- R2 is vacuously excluded: [1, 1] cannot be written as (2n+1) :: middle ++ [0].
    intro n middle hEq
    -- `[1, 1] = (2n+1) :: middle ++ [0]` forces `middle ++ [0] = [1]`, hence
    -- `middle = []` and `0 = 1`, a contradiction.
    rcases middle with _ | ⟨m, ms⟩ <;> simp at hEq

/-- **Main theorem**: from the blank initial configuration the machine
    never halts. -/
theorem nonhalt : ∀ m, (run tm initConfig m).state ≠ none := by
  intro m
  by_cases hm : m < 17
  · -- First 17 steps: verified by `init_to_macro` + `run_alive_of_later`.
    refine run_alive_of_later tm initConfig m 17 (by omega) ?_
    rw [show run tm initConfig 17 = tmRun initConfig 17 from rfl, init_to_macro]
    simp [MacroConfig]
  · -- From step 17 onward: progress invariant.
    have h17 := reaches_canonical
    have hnon :=
      nonhalt_of_progress tm IsCanonical canonical_progress
        (run tm initConfig 17) h17
    rw [show m = 17 + (m - 17) from by omega, run_add]
    exact hnon (m - 17)

end TM5c
