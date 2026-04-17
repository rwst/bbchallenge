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

-- ---------------------------------------------------------------------
-- Backward-sweep helpers
-- ---------------------------------------------------------------------

/-- Sweep left through `k` cells of `s2` then consume a single `s3` marker.
    `k+2` steps: the `s2`s become `s4`s on the right (rebuilding a `rep s4`
    block there) and the `s3` is absorbed (`B,s3→2LA`). -/
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

- `sweep_s4_odd_A`        — induction, ~15 lines (mirrors `sweep_s4_2k`).
- `cross_sep_enter_block` — 4 `tm_step`s, ~5 lines.
- `sweep_s4_from_B_even`  — induction, ~15 lines.
- `bounce_at_blank`       — 2 `tm_step`s, ~3 lines.
- `sweep_s2_to_s3`        — induction on `k`, ~15 lines.
- `backward_carry`        — 3 `tm_step`s, ~5 lines.
- `finalize_tail`         — induction on `n`, uses `sweep_s2_carry`, ~20 lines.
- `rule_R3_nil`           — compose the above, ~25 lines.
- `cross_even_digit`      — compose helpers, ~20 lines.
- `rule_R3`               — induction on `middle`, ~30 lines.
- R4 variants             — similar, factor shared helpers.
- R5 variants             — new helper `cross_odd_digit`.
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

/-- **Rule R3**  `[2n+1, 2a₁, 2a₂, …, 2aⱼ, 2m+2]  →  [2n, 2a₁, …, 2aⱼ, 2m+2, 0]`.
    Here `middle` is an arbitrary list of even digits. Currently proved only
    for `middle = []`; the inductive case over `middle` is still open. -/
theorem rule_R3 (n m : Nat) (middle : List Nat) (hmid : AllEven middle) :
    ∃ steps, 0 < steps ∧
      tmRun (MacroConfig ((2 * n + 1) :: (middle ++ [2 * m + 2]))) steps =
        MacroConfig ((2 * n) :: (middle ++ [2 * m + 2, 0])) := by
  cases middle with
  | nil =>
    refine ⟨4 * n + 4 * m + 16, by omega, ?_⟩
    simpa using rule_R3_nil n m
  | cons y ys =>
    sorry

/-- Concrete base case for R4 (n=0, m=0, middle=[]): `[1, 1] → [0, 1, 1]` in 18 steps. -/
theorem rule_R4_base : tmRun (MacroConfig [1, 1]) 18 = MacroConfig [0, 1, 1] := by
  native_decide

/-- **Rule R4**  `[2n+1, 2a₁, …, 2aⱼ, 2m+1]  →  [2n, 2a₁, …, 2aⱼ, 2m+1, 1]`.

    TODO: Step count formula is `4n + 4m + 18 + Σ middle_cost` where
    `middle_cost(2y) = 4y + 8`. Needs variants:
    - `sweep_s4_from_B_odd` — odd-length sweep ending in state A.
    - `bounce_at_blank_from_A` — A-variant bounce (uses `A,s0 → 1RB`).
    The backward phase writes the trailing `1` instead of `0`. -/
theorem rule_R4 (n m : Nat) (middle : List Nat) (hmid : AllEven middle) :
    ∃ steps, 0 < steps ∧
      tmRun (MacroConfig ((2 * n + 1) :: (middle ++ [2 * m + 1]))) steps =
        MacroConfig ((2 * n) :: (middle ++ [2 * m + 1, 1])) := by
  sorry

/-- Concrete base case for R5 (n=0, m=1, x=0, middle=[], rest=[]):
    `[1, 3, 0] → [0, 3, 1]` in 20 steps. -/
theorem rule_R5_base : tmRun (MacroConfig [1, 3, 0]) 20 = MacroConfig [0, 3, 1] := by
  native_decide

/-- **Rule R5**  `[2n+1, 2a₁, …, 2aⱼ, 2m+1, x, …rest]
                 →  [2n, 2a₁, …, 2aⱼ, 2m+1, x+1, …rest]`.
    The first odd digit after position 0 is at the end of `middle ++ [2m+1]`;
    the rule increments the digit immediately following it.

    TODO: Fundamentally different from R3/R4 — the head does not reach the
    right edge; it turns around just past the first odd digit `2m+1`.
    Needs a new helper `cross_odd_digit` capturing the turnaround. -/
theorem rule_R5 (n m x : Nat) (middle rest : List Nat) (hmid : AllEven middle) :
    ∃ steps, 0 < steps ∧
      tmRun (MacroConfig ((2 * n + 1) :: (middle ++ (2 * m + 1) :: x :: rest))) steps =
        MacroConfig ((2 * n) :: (middle ++ (2 * m + 1) :: (x + 1) :: rest)) := by
  sorry

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
    excluded by the invariant in `ValidDigits`. -/
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
