import BusyLean
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open BusyLean

namespace Sweeper

/-!
# 6-state 2-symbol TM: 1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF

## Transition Table

       0     1
  A   1RB   1LA
  B   1RC   0RF
  C   1RD   ---   (undefined)
  D   0LE   1RB
  E   ---   0LA   (undefined)
  F   1LD   1RF

Undefined transitions: C,1 and E,0.

## Tape Structure

The tape is a contiguous block of 1s with k ≥ 0 zero-markers at
distinct interior positions:

  0^∞  1^a₁  0  1^a₂  0  ...  1^aₖ  [HEAD]  1^b₁  0  1^b₂  0  ...  1^bₘ  0^∞

## Macro Configurations

  -- S(L, R): state A, head on leftmost cell of right segment
  --   left = L (list of Sym), right = R (list of Sym)
  --   A sweeps left through 1s, then B creates a zero, F sweeps right

  -- E(n): "era start" — tape is 1^n, all-1s, head at right end
  --   State D at position n (rightmost 1). BCD chain extends tape.

## Sweep Cycle (conjectured macro rule)

Each sweep cycle:
  1. A sweeps left over 1s until hitting 0 (left edge or zero-marker)
  2. A,0 → 1RB: consumes zero, B writes new zero one position right
  3. F sweeps right over 1s until hitting 0 (zero-marker or right edge)
  4a. Interior zero: F,0 → 1LD, D,1 → 1RB. Zero shifts left by 1.
  4b. Right edge: B,0 → 1RC → C,0 → 1RD → D,0 → 0LE → E,1 → 0LA.
      BCD extends tape by 2. E creates rightmost zero. Restart.

## Key Invariant

Each sweep cycle moves every zero-marker one position inward
(left zeros move right, right zeros move left).
-/

-- The TM
def sweeper : TM 6 := tm! "1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF"

-- Simp tactic for single TM steps
scoped macro "sw_simp" : tactic =>
  `(tactic| simp (config := { decide := true }) [run, step, sweeper, ones])

-- Transition lemmas
@[simp] private theorem sw_A0 : sweeper.tr stA false = some (stB, true, Dir.R) := rfl
@[simp] private theorem sw_A1 : sweeper.tr stA true = some (stA, true, Dir.L) := rfl
@[simp] private theorem sw_B0 : sweeper.tr stB false = some (stC, true, Dir.R) := rfl
@[simp] private theorem sw_B1 : sweeper.tr stB true = some (stF, false, Dir.R) := rfl
@[simp] private theorem sw_C0 : sweeper.tr stC false = some (stD, true, Dir.R) := rfl
@[simp] private theorem sw_C1 : sweeper.tr stC true = none := rfl
@[simp] private theorem sw_D0 : sweeper.tr stD false = some (stE, false, Dir.L) := rfl
@[simp] private theorem sw_D1 : sweeper.tr stD true = some (stB, true, Dir.R) := rfl
@[simp] private theorem sw_E0 : sweeper.tr stE false = none := rfl
@[simp] private theorem sw_E1 : sweeper.tr stE true = some (stA, false, Dir.L) := rfl
@[simp] private theorem sw_F0 : sweeper.tr stF false = some (stD, true, Dir.L) := rfl
@[simp] private theorem sw_F1 : sweeper.tr stF true = some (stF, true, Dir.R) := rfl

-- Standard simp set for reducing concrete steps without unfolding `sweeper`
scoped macro "sw_steps" : tactic =>
  `(tactic| simp only [run, step, sw_A0, sw_A1, sw_B0, sw_B1, sw_C0, sw_C1, sw_D0, sw_D1,
    sw_E0, sw_E1, sw_F0, sw_F1, ones_succ, ones_zero, zeros_succ, zeros_zero,
    listHead_cons, listTail_cons, listHead_nil, listTail_nil, listHead_zeros, listTail_zeros,
    listHead_ones, listTail_ones, listHead_ones_succ, listTail_ones_succ,
    List.cons_append, List.nil_append, List.append_nil,
    ones_true_cons, zeros_false_cons])

-- ============================================================
-- Shift lemmas (identity sweeps)
-- ============================================================

/-- A sweeps left through k ones: A reads 1, writes 1, moves L. -/
lemma A_shift (k : Nat) (L R : List Sym) :
    run sweeper { state := some stA, head := true, left := ones k ++ L, right := R } (k + 1) =
    { state := some stA, head := listHead L false, left := listTail L, right := ones (k + 1) ++ R } := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih => tm_ind_succ ih stA [sweeper]

/-- F sweeps right through k ones: F reads 1, writes 1, moves R. -/
lemma F_shift (k : Nat) (L R : List Sym) :
    run sweeper { state := some stF, head := true, left := L, right := ones k ++ R } (k + 1) =
    { state := some stF, head := listHead R false, left := ones (k + 1) ++ L, right := listTail R } := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih => tm_ind_succ ih stF [sweeper]

-- ============================================================
-- Macro configurations
-- ============================================================

/-- Era configuration: all-1s tape, state D at rightmost cell.
    E(n) = state D, head = true (on a 1), left = ones (n-1), right = []
    Represents tape 1^n with D reading the rightmost 1. -/
def E_Config (n : Nat) (p : Nat) : Config 6 :=
  { state := some stD,
    head := true,
    left := ones n,
    right := zeros p }

-- Sweep configuration: state A reading head cell, with zero-markers.
-- The tape to the left of head is `left`, to the right is `right`.
-- Both may contain zero-markers (false values) among ones.
-- (Generic; specific configurations will be refined as proofs develop.)

-- ============================================================
-- BCD chain extension (Phase 4b)
-- ============================================================

/-- BCD extension: B at right edge (reads 0), chain B→C→D extends
    tape by 2 ones, then D,0→0LE and E,1→0LA bounce back as A.

    After 5 steps from B reading 0 with ones (k+1) to the left:
    B,0 → 1RC; C,0 → 1RD; D,0 → 0LE; E,1 → 0LA; A,1 → 1LA
    Result: A reading 1, one step left, with [1,0,0] prepended to right. -/
theorem bcd_extension (k : Nat) (L : List Sym) (p : Nat) :
    run sweeper (⟨some stB, ones (k + 1) ++ L, false, zeros (p + 2)⟩ : Config 6) 5 =
    (⟨some stA, ones k ++ L, true, true :: false :: false :: zeros p⟩ : Config 6) := by
  sw_steps

-- ============================================================
-- Conjecture C1: Non-halting (structural)
-- ============================================================

/-! ### C1: The undefined transitions C,1 and E,0 are never reached.

C is only entered via B,0 → 1RC. B sees 0 only at positions beyond
the right tape edge. The next cell (what C reads) is also 0.
So C always reads 0, never 1.

E is only entered via D,0 → 0LE. D sees 0 only at the right tape
edge. The cell one step to the left is always a 1 (tape interior).
So E always reads 1, never 0. -/

/-- C,1 is unreachable: B reads 0 only at or beyond the right tape edge. -/
theorem c1_never_reached (k : Nat) :
    (run sweeper (initConfig 6) k).state ≠ some stC ∨
    (run sweeper (initConfig 6) k).head = false := by
  sorry

/-- E,0 is unreachable: D reads 0 only at the right tape edge;
    the cell to its left is always 1. -/
theorem e0_never_reached (k : Nat) :
    (run sweeper (initConfig 6) k).state ≠ some stE ∨
    (run sweeper (initConfig 6) k).head = true := by
  sorry

/-- F-bounce at interior zero: F hits a zero-marker, bounces as D→B,
    creating a new zero one position to the left.
    Requires k ≥ 1 (at least one 1 to the left so D sees 1, not 0). -/
theorem f_bounce_interior (k : Nat) (L R : List Sym) :
    run sweeper (⟨some stF, ones (k + 1) ++ L, false, R⟩ : Config 6) 3 =
    (⟨some stF, [false] ++ ones (k + 1) ++ L, listHead R false, listTail R⟩ : Config 6) := by
  sw_steps

-- ============================================================
-- Conjecture C3/C4: Era structure and growth
-- ============================================================

/-! ### Era boundaries

An era begins when the tape is all-1s. The BCD chain extends the
tape and creates an initial zero-pair. Sweep cycles converge the
zeros inward until they annihilate.

Observed E_Config events (D reading rightmost 1 of all-1s tape):
  step  19:  E_Config  4 0  (tape len  5)
  step  84:  E_Config 10 0  (tape len 11)

After E_Config 10, the machine enters a complex multi-zero-marker
phase and does not return to an all-1s E_Config within 1M+ steps.
The tape continues to grow but with persistent zero-markers. -/

/-- Era 0 → Era 1: from all-1s tape of length 5 to all-1s tape of length 11.
    E_Config 4 0 evolves to E_Config 10 0 in exactly 65 steps. -/
theorem era_0_to_1 :
    run sweeper (E_Config 4 0) 65 = E_Config 10 0 := by
  rfl

-- ============================================================
-- Conjecture C5: Identity sweeps
-- ============================================================

/-! ### C5: A,1→1LA and F,1→1RF are identity sweeps.

These are already proven above as `A_shift` and `F_shift`.
They read 1, write 1, and move — no tape modification. -/

-- ============================================================
-- Conjecture C6: Tape growth per BCD extension
-- ============================================================

/-! ### C6: Each BCD extension adds exactly 2 cells.

B,0 → 1RC writes 1 at position p.
C,0 → 1RD writes 1 at position p+1.
D,0 → 0LE writes 0 at position p+2 (this becomes the new zero-marker).
E,1 → 0LA writes 0 at position p+1 (hmm — need to verify).

Actually the BCD chain: B reads 0, writes 1, moves R to C.
C reads 0, writes 1, moves R to D. D reads 0, writes 0, moves L to E.
Net: 2 new 1-cells written (by B and C). -/

-- (See bcd_extension above for the formal statement.)

-- ============================================================
-- Conjecture C7: Step count growth
-- ============================================================

/-! ### C7: Step count is O(L²) per era, exponential overall.

Each sweep cycle traverses the tape twice (A left, F right): O(L) steps.
An era with tape length L has O(L) sweep cycles.
Total per era: O(L²). With L growing geometrically, cumulative
step count grows exponentially. -/

-- (No formal statement needed — this is a complexity observation.)

-- ============================================================
-- Initial configuration
-- ============================================================

/-- The machine starts in state A on a blank tape.
    After 19 steps it reaches E_Config 4 0 (all-1s tape of length 5). -/
theorem sweeper_init_to_era0 :
    run sweeper (initConfig 6) 19 = E_Config 4 0 := by
  rfl

-- ============================================================
-- Main non-halting conjecture
-- ============================================================

/-- The machine never halts: for all k, the state after k steps is not none. -/
theorem sweeper_never_halts (k : Nat) :
    (run sweeper (initConfig 6) k).state ≠ none := by
  sorry

end Sweeper
