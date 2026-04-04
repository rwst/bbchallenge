import BusyLean
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

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
-- Backward analysis: necessary conditions for halting
-- ============================================================

/-! ### Halt paths analysis

The two undefined transitions are C,1 and E,0.
Working backwards from each halt state:

**C,1 halt**: C entered only from B,0 → 1RC (move R).
C reads the first element of B's right tape.
C,1 requires: B read 0 AND the cell to B's right was 1.

**E,0 halt**: E entered only from D,0 → 0LE (move L).
D entered from C,0 → 1RD or F,0 → 1LD.
- Via C→D→E: E reads the cell C wrote 1 to → **always reads 1, never 0**.
- Via F→D→E: E reads 2 cells left of F. E,0 requires F read 0
  with the cell to its left also 0 and the cell 2 left also 0. -/

-- B reads 0 → C enters reading the first element of B's right tape
theorem b0_to_c (L : List Sym) (r : Sym) (R : List Sym) :
    run sweeper (⟨some stB, L, false, r :: R⟩ : Config 6) 1 =
    (⟨some stC, true :: L, r, R⟩ : Config 6) := by
  sw_steps

-- B reads 0 with zeros to the right → C reads 0 (safe, no halt)
theorem b0_zeros_safe (L : List Sym) (p : Nat) :
    run sweeper (⟨some stB, L, false, zeros (p + 1)⟩ : Config 6) 1 =
    (⟨some stC, true :: L, false, zeros p⟩ : Config 6) := by
  sw_steps

-- KEY ELIMINATION: C→D→E path cannot halt.
-- C reads 0, D reads 0 → E reads the 1 that C wrote. Always safe.
theorem cd_to_e_safe (L R : List Sym) :
    run sweeper (⟨some stC, L, false, false :: R⟩ : Config 6) 2 =
    (⟨some stE, L, true, false :: R⟩ : Config 6) := by
  sw_steps

-- F reads 0 with 0 to its left: the path to D reading 0, then E
-- E reads whatever is 2 positions left of F (= listHead L false)
theorem f0_d0_to_e (L R : List Sym) :
    run sweeper (⟨some stF, false :: L, false, R⟩ : Config 6) 2 =
    (⟨some stE, listTail L, listHead L false, false :: true :: R⟩ : Config 6) := by
  sw_steps

-- NECESSARY CONDITION for E,0 halt:
-- F reads 0 with false :: false :: L to its left → E reads 0
theorem e0_necessary (L R : List Sym) :
    run sweeper (⟨some stF, false :: false :: L, false, R⟩ : Config 6) 2 =
    (⟨some stE, L, false, false :: true :: R⟩ : Config 6) := by
  sw_steps

-- CONTRAPOSITIVE: F reads 0 with false :: true :: L to its left → E reads 1 (safe)
theorem f0_d0_e_safe (L R : List Sym) :
    run sweeper (⟨some stF, false :: true :: L, false, R⟩ : Config 6) 2 =
    (⟨some stE, L, true, false :: true :: R⟩ : Config 6) := by
  sw_steps

-- ============================================================
-- E,0 is FULLY ELIMINATED (no global invariant needed)
-- ============================================================

/-! ### E,0 elimination by backward chain analysis

E,0 requires D,0 as predecessor. D is entered from C,0 or F,0.
- Via C→D→E: eliminated by cd_to_e_safe (E reads 1).
- Via F→D→E: F reads 0, D reads F's left[0]. For D,0: left[0] = false.
  Then E reads F's left[1].

F is only created by B,1 → 0RF. B,1 writes 0, so F's left = false :: L_B.
B is entered from A,0 or D,1. Both write 1, so L_B = true :: L_prev.
Therefore F's left at creation = false :: true :: L_prev.

During F's sweep (F,1 → 1RF), ones are prepended to left:
  left = ones k ++ false :: true :: L_prev.
- If k ≥ 1: D reads true from the sweep ones → D,1 → B. No E entry.
- If k = 0: D reads false → E reads true (the 1 from A,0 or D,1). Safe.

After f_bounce_interior, F has left = false :: ones(k+1) ++ L.
Same pattern: false :: true :: ..., so E reads true if D reads false.

Conclusion: E always reads 1 in ALL reachable configurations. -/

-- A,0 → B: B's left starts with true (A wrote 1)
theorem a0_to_b (L R : List Sym) :
    run sweeper (⟨some stA, L, false, R⟩ : Config 6) 1 =
    (⟨some stB, true :: L, listHead R false, listTail R⟩ : Config 6) := by
  sw_steps

-- D,1 → B: B's left starts with true (D wrote 1)
theorem d1_to_b (L R : List Sym) :
    run sweeper (⟨some stD, L, true, R⟩ : Config 6) 1 =
    (⟨some stB, true :: L, listHead R false, listTail R⟩ : Config 6) := by
  sw_steps

-- B,1 → F: F's left starts with false :: L_B (B wrote 0)
theorem b1_to_f (L R : List Sym) :
    run sweeper (⟨some stB, L, true, R⟩ : Config 6) 1 =
    (⟨some stF, false :: L, listHead R false, listTail R⟩ : Config 6) := by
  sw_steps

-- CHAIN: A,0 → B(reads 1) → F(reads 0) → D,0 → E: E reads 1
-- A writes 1 at its position. B reads 1, writes 0, moves R to F.
-- F reads 0 immediately. D reads B's 0. E reads A's 1. Safe.
theorem a_b_f_d_e_safe (L R : List Sym) :
    run sweeper (⟨some stA, L, false, true :: false :: R⟩ : Config 6) 4 =
    (⟨some stE, L, true, false :: true :: R⟩ : Config 6) := by
  sw_steps

-- CHAIN: D,1 → B(reads 1) → F(reads 0) → D,0 → E: E reads 1
-- D writes 1 at its position. B reads 1, writes 0, moves R to F.
-- F reads 0 immediately. D reads B's 0. E reads D's 1. Safe.
theorem d_b_f_d_e_safe (L R : List Sym) :
    run sweeper (⟨some stD, L, true, true :: false :: R⟩ : Config 6) 4 =
    (⟨some stE, L, true, false :: true :: R⟩ : Config 6) := by
  sw_steps

-- NECESSARY CONDITION for C,1 halt:
-- B reads 0 with 1 to its right → C reads 1 → state becomes none
theorem c1_halt_via_b (L R : List Sym) :
    (run sweeper (⟨some stB, L, false, true :: R⟩ : Config 6) 2).state = none := by
  sw_steps

-- Step-inductive invariant: sufficient to prove E always reads 1.
-- B.left starts with true (B entered from A,0 or D,1, both write 1).
-- F.left[0]=true (sweep) or F.left[1]=true (fresh from B,1 or bounce).
-- D reading 0 has left starting with true (from C writing 1 or F structure).
-- E always reads true (follows from D condition).
private def E0Inv (c : Config 6) : Prop :=
  (c.state = some stB → listHead c.left false = true) ∧
  (c.state = some stF →
    listHead c.left false = true ∨ listHead (listTail c.left) false = true) ∧
  (c.state = some stD → c.head = false → listHead c.left false = true) ∧
  (c.state = some stE → c.head = true)

private lemma e0inv_init : E0Inv (initConfig 6) := by
  simp [E0Inv, initConfig, stB, stF, stD, stE]

private lemma e0inv_step (c : Config 6) (h : E0Inv c) : E0Inv (step sweeper c) := by
  obtain ⟨hB, hF, hD, hE⟩ := h
  rcases c with ⟨s, l, hd, r⟩
  simp only [] at hB hF hD hE
  cases s with
  | none => simp [E0Inv, step]
  | some q =>
    fin_cases q <;> cases hd <;>
      simp only [step, sw_A0, sw_A1, sw_B0, sw_B1, sw_C0, sw_C1, sw_D0, sw_D1,
        sw_E0, sw_E1, sw_F0, sw_F1, listHead_cons, listTail_cons, E0Inv] <;>
      simp_all [stA, stB, stC, stD, stE, stF]
    -- F,0 → D: remaining goal uses hF disjunction
    intro h; simp_all

private lemma e0inv_run (c : Config 6) (h : E0Inv c) (k : Nat) :
    E0Inv (run sweeper c k) := by
  induction k generalizing c with
  | zero => exact h
  | succ k ih =>
    simp only [run]
    exact ih (step sweeper c) (e0inv_step c h)

/-- E,0 is unreachable: follows from backward chain analysis.
    Every path to state E produces head = true. -/
theorem e0_never_reached (k : Nat) :
    (run sweeper (initConfig 6) k).state ≠ some stE ∨
    (run sweeper (initConfig 6) k).head = true := by
  have ⟨_, _, _, hE⟩ := e0inv_run _ e0inv_init k
  by_cases hs : (run sweeper (initConfig 6) k).state = some stE
  · exact Or.inr (hE hs)
  · exact Or.inl hs

/-- F-bounce at interior zero: F hits a zero-marker, bounces as D→B,
    creating a new zero one position to the left.
    Requires k ≥ 1 (at least one 1 to the left so D sees 1, not 0). -/
theorem f_bounce_interior (k : Nat) (L R : List Sym) :
    run sweeper (⟨some stF, ones (k + 1) ++ L, false, R⟩ : Config 6) 3 =
    (⟨some stF, [false] ++ ones (k + 1) ++ L, listHead R false, listTail R⟩ : Config 6) := by
  sw_steps

-- ============================================================
-- ones_append and multi-run bounce building blocks
-- ============================================================

lemma ones_append (a b : Nat) : ones a ++ ones b = ones (a + b) := by
  induction a with
  | zero => simp
  | succ a ih => simp [ones_succ, List.cons_append, ih, Nat.succ_add]

/-- F sweeps through m ones, then bounces at interior zero.
    Composes F_shift + f_bounce_interior.
    Requires k ≥ 1 (guaranteed by the preceding bounce or initial BCD). -/
theorem F_sweep_and_bounce (m k : Nat) (L R : List Sym) :
    run sweeper (⟨some stF, ones (k + 1) ++ L, true,
                  ones m ++ false :: R⟩ : Config 6) (m + 4) =
    (⟨some stF, false :: ones (m + k + 2) ++ L,
      listHead R false, listTail R⟩ : Config 6) := by
  rw [show m + 4 = (m + 1) + 3 from by omega]
  rw [run_add, F_shift m (ones (k + 1) ++ L) (false :: R)]
  simp only [listHead_cons, listTail_cons]
  rw [← List.append_assoc, ones_append, show m + 1 + (k + 1) = m + k + 1 + 1 from by omega]
  exact f_bounce_interior (m + k + 1) L R

/-- F sweeps to end of tape (no more zeros), then completes the bounce:
    f_bounce_interior + f0_d0_to_e + E,1→A.
    This is the final phase of any bounce sequence. -/
theorem F_final_bounce (m k : Nat) (L : List Sym) :
    run sweeper (⟨some stF, ones (k + 1) ++ L, true,
                  ones m⟩ : Config 6) (m + 7) =
    (⟨some stA, ones (m + k) ++ L, true,
      false :: false :: [true]⟩ : Config 6) := by
  rw [show ones m = ones m ++ ([] : List Sym) from (List.append_nil _).symm]
  rw [show m + 7 = (m + 1) + (3 + (2 + 1)) from by omega]
  rw [run_add, F_shift m (ones (k + 1) ++ L) []]
  simp only [listHead_nil, listTail_nil]
  rw [← List.append_assoc, ones_append, show m + 1 + (k + 1) = m + k + 1 + 1 from by omega]
  rw [run_add, f_bounce_interior (m + k + 1) L []]
  simp only [listHead_nil, listTail_nil, List.cons_append,
    List.nil_append, show m + k + 1 + 1 = m + k + 2 from by omega]
  rw [run_add, f0_d0_to_e (ones (m + k + 2) ++ L) []]
  simp only [listHead_ones_succ, listTail_ones_succ]
  simp only [run, step, sw_E1, listHead_ones_succ, listTail_ones_succ]

/-- Phase 0 of any zero-bounce: A reads 0 with ones(r+3) in right tape.
    5 steps: A,0 → B,0 → C,0 → D,1 → B,1 → F.
    Output: F with head = listHead(ones r ++ R_tail). -/
theorem M0_to_F (r : Nat) (L_raw R_tail : List Sym) :
    run sweeper (⟨some stA, L_raw, false,
                  false :: false :: (ones (r + 3) ++ R_tail)⟩ : Config 6) 5 =
    (⟨some stF, false :: true :: true :: true :: true :: L_raw,
      true, ones r ++ R_tail⟩ : Config 6) := by
  -- Expand ones(r+3) to 3 explicit cons cells
  rw [show ones (r + 3) ++ R_tail = true :: true :: true :: (ones r ++ R_tail) from by
    simp only [show r + 3 = (r + 2) + 1 from by omega, ones_succ, List.cons_append,
      show r + 2 = (r + 1) + 1 from by omega]]
  rw [show (5 : Nat) = 1 + (1 + (1 + (1 + 1))) from rfl]
  rw [run_add, a0_to_b]
  -- After a0_to_b: B reads false
  change run sweeper (⟨some stB, true :: L_raw, false,
    false :: true :: true :: true :: (ones r ++ R_tail)⟩ : Config 6) (1 + (1 + (1 + 1))) = _
  rw [run_add]
  change run sweeper (⟨some stC, true :: true :: L_raw, false,
    true :: true :: true :: (ones r ++ R_tail)⟩ : Config 6) (1 + (1 + 1)) = _
  rw [run_add]
  change run sweeper (⟨some stD, true :: true :: true :: L_raw, true,
    true :: true :: (ones r ++ R_tail)⟩ : Config 6) (1 + 1) = _
  rw [run_add, d1_to_b]
  change run sweeper (⟨some stB, true :: true :: true :: true :: L_raw, true,
    true :: (ones r ++ R_tail)⟩ : Config 6) 1 = _
  rw [b1_to_f]
  simp only [listHead_cons, listTail_cons]

-- ============================================================
-- Macro rules (from equivalent TM analysis by dyuan01)
-- ============================================================

/-! ### Macro-level representation

The equivalent TM `1RB0LE_1RC0RF_1RD---_0LA1RB_1RB1LE_1LD1RF` (same
equivalence class) has known macro rules operating on run-length
encoded tape [a₁, a₂, ..., aₖ] where each aᵢ counts consecutive 1s
between zero-markers.

Seven rules govern the dynamics:
1. `[a, (b+2), c] → [a+1, (b), c+1]`  — main sweep cycle
2. `[a, (1), R...] → [(a), 1, R...]`   — cursor shift left
3. `[a, (0), b+3, ..., z+1] → [a+4, b+1, ..., (z), 1]`  — zero bounce (multi)
4. `[a, (0), z+3] → [a+4, (z), 1]`     — zero bounce (single right run)
5. `[a, (0), 2, b, R...] → [(a+3), b+1, R...]`  — zero with right run = 2
6. `[(0), 1, z+1, R...] → Halt`        — C reads 1
7. `[a, (0), 1] → [(a+5)]`             — era completion
-/

/-- Build tape segment from run lengths.
    `runs [a, b, c] = ones a ++ [false] ++ ones b ++ [false] ++ ones c` -/
def runs : List Nat → List Sym
  | [] => []
  | [n] => ones n
  | n :: rest => ones n ++ [false] ++ runs rest

@[simp] lemma runs_nil : runs [] = [] := rfl
@[simp] lemma runs_singleton (n : Nat) : runs [n] = ones n := rfl
@[simp] lemma runs_cons₂ (n m : Nat) (rest : List Nat) :
    runs (n :: m :: rest) = ones n ++ [false] ++ runs (m :: rest) := rfl

/-- Prepending ones to a run list equals adding to the first run. -/
lemma ones_append_runs (n m : Nat) (L : List Nat) :
    ones n ++ runs (m :: L) = runs ((n + m) :: L) := by
  cases L with
  | nil => simp only [runs_singleton, ones_append]
  | cons a L' =>
    simp only [runs_cons₂, ← List.append_assoc]
    rw [ones_append]

/-- The first element of a nonempty run list is always true (a 1). -/
@[simp] lemma listHead_runs_pos (n : Nat) (R : List Nat) :
    listHead (runs ((n + 1) :: R)) false = true := by
  cases R with
  | nil => simp [runs]
  | cons m R' => simp [runs]

@[simp] lemma runs_succ (n : Nat) (R : List Nat) :
    runs ((n + 1) :: R) = true :: runs (n :: R) := by
  cases R with
  | nil => simp [runs, ones_succ]
  | cons m R' => simp [runs, ones_succ]

lemma runs_eq_ones_append (a : Nat) (L : List Nat) :
    runs (a :: L) = ones a ++ match L with | [] => [] | _ => false :: runs L := by
  cases L with
  | nil => simp [runs]
  | cons m L' => simp [runs]

/-- Macro configuration: state A, head on rightmost 1 of cursor run.
    `M_Config L c R` = state A, head=true, cursor run has c ones.
    L = left runs (nearest first), R = right runs (nearest first).
    Two boundary zeros separate cursor from right runs. -/
def M_Config (L : List Nat) (c : Nat) (R : List Nat) : Config 6 :=
  { state := some stA,
    left := ones (c - 1) ++ match L with | [] => [] | _ => false :: runs L,
    head := true,
    right := false :: false :: runs R }

/-- Macro configuration: state A reading 0 (cursor at zero between runs).
    `M0_Config L R` = state A, head=false, cursor between left and right runs. -/
def M0_Config (L : List Nat) (R : List Nat) : Config 6 :=
  { state := some stA,
    left := runs L,
    head := false,
    right := false :: false :: runs R }

@[simp] lemma M_Config_nil (c : Nat) (R : List Nat) :
    M_Config [] c R = ⟨some stA, ones (c - 1), true, false :: false :: runs R⟩ := by
  simp [M_Config]

@[simp] lemma M_Config_cons (a : Nat) (L : List Nat) (c : Nat) (R : List Nat) :
    M_Config (a :: L) c R =
    ⟨some stA, ones (c - 1) ++ false :: runs (a :: L), true, false :: false :: runs R⟩ := by
  simp [M_Config]

@[simp] lemma M0_Config_nil (R : List Nat) :
    M0_Config [] R = ⟨some stA, [], false, false :: false :: runs R⟩ := by
  simp [M0_Config]

@[simp] lemma M0_Config_cons (a : Nat) (L : List Nat) (R : List Nat) :
    M0_Config (a :: L) R =
    ⟨some stA, runs (a :: L), false, false :: false :: runs R⟩ := by
  simp [M0_Config]

/-- Era start to first macro configuration.
    E_Config n 0 (D at rightmost 1 of all-1s tape) evolves to M_Config in 5 steps. -/
theorem era_to_macro (n : Nat) :
    run sweeper (E_Config n 0) 5 = M_Config [] (n + 2) [] := by
  simp only [E_Config, M_Config, runs_nil, zeros_zero, run, step, sw_D1, sw_B0, sw_C0, sw_D0,
    sw_E1, listHead_cons, listTail_cons, listHead_nil, listTail_nil,
    show n + 2 - 1 = n + 1 from by omega, ones_succ, List.append_nil]

/-- Rule 1: Main sweep cycle, cursor ≥ 3 with neighbors.
    Step count = 2c+7 where c is cursor run size.
    [a, (c+3), d, R...] → [a+1, (c+1), d+1, R...] -/
theorem macro_sweep (a c d : Nat) (L R : List Nat) :
    run sweeper (M_Config (a :: L) (c + 3) (d :: R)) (2 * (c + 3) + 7) =
    M_Config ((a + 1) :: L) (c + 1) ((d + 1) :: R) := by
  -- Unfold M_Config to raw config
  conv_lhs => rw [M_Config_cons, show c + 3 - 1 = c + 2 from by omega]
  -- Decompose step count: (c+3) + 1 + 1 + (c+2) + 3 + 2 + 1 = 2c+13
  rw [show 2 * (c + 3) + 7 = (c + 2 + 1) + (1 + (1 + ((c + 1 + 1) + (3 + (2 + 1))))) from by omega]
  -- Phase 1: A_shift (c+3 steps)
  rw [run_add, A_shift (c + 2) (false :: runs (a :: L)) (false :: false :: runs (d :: R))]
  simp only [listHead_cons, listTail_cons]
  -- Phase 2: a0_to_b (1 step)
  rw [run_add, a0_to_b]
  simp only [listHead_ones_succ, listTail_ones_succ]
  -- Phase 3: b1_to_f (1 step)
  rw [run_add, b1_to_f]
  simp only [listHead_ones_succ, listTail_ones_succ]
  -- Phase 4: F_shift (c+2 steps)
  rw [run_add, F_shift (c + 1) (false :: true :: runs (a :: L)) (false :: false :: runs (d :: R))]
  simp only [listHead_cons, listTail_cons]
  -- Phase 5: f_bounce_interior (3 steps)
  rw [run_add, f_bounce_interior (c + 1) (false :: true :: runs (a :: L)) (false :: runs (d :: R))]
  simp only [listHead_cons, listTail_cons, List.cons_append,
    List.nil_append, show c + 1 + 1 = c + 2 from by omega]
  -- Phase 6: f0_d0_to_e (2 steps)
  rw [run_add, f0_d0_to_e (ones (c + 2) ++ false :: true :: runs (a :: L)) (runs (d :: R))]
  simp only [listHead_ones_succ, listTail_ones_succ]
  -- Phase 7: E,1→A (1 step)
  simp only [run, step, sw_E1, listHead_ones_succ, listTail_ones_succ]
  -- Match target
  conv_rhs => rw [M_Config_cons, show c + 1 - 1 = c from by omega, runs_succ, runs_succ]

/-- Rule 1 (terminal): Sweep reducing cursor from 2 to 0.
    [a, (2), d, R...] → M0[a+1, d+1, R...] -/
theorem macro_sweep_to_zero (a d : Nat) (L R : List Nat) :
    run sweeper (M_Config (a :: L) 2 (d :: R)) 11 =
    M0_Config ((a + 1) :: L) ((d + 1) :: R) := by
  simp only [M_Config, M0_Config, ones_succ, ones_zero, List.nil_append, List.cons_append, run,
    step, sw_A0, sw_A1, sw_B1, sw_D0, sw_D1, sw_E1, sw_F0, sw_F1, listHead_cons, listTail_cons,
    show 2 - 1 = 1 from rfl, runs_succ]

/-- Rule 1': Sweep with no neighbors (single-run config).
    [(c+3)] → [1, (c+1), 1] -/
theorem macro_sweep_solo (c : Nat) :
    run sweeper (M_Config [] (c + 3) []) (2 * (c + 3) + 7) =
    M_Config [1] (c + 1) [1] := by
  -- Unfold M_Config to raw config
  conv_lhs => rw [M_Config_nil, show c + 3 - 1 = c + 2 from by omega, runs_nil,
    show ones (c + 2) = ones (c + 2) ++ ([] : List Sym) from (List.append_nil _).symm]
  -- Decompose step count: (c+3) + 1 + 1 + (c+2) + 3 + 2 + 1 = 2c+13
  rw [show 2 * (c + 3) + 7 = (c + 2 + 1) + (1 + (1 + ((c + 1 + 1) + (3 + (2 + 1))))) from by omega]
  -- Phase 1: A_shift (c+3 steps)
  rw [run_add, A_shift (c + 2) [] [false, false]]
  simp only [listHead_nil, listTail_nil]
  -- Phase 2: a0_to_b (1 step)
  rw [run_add, a0_to_b]
  simp only [listHead_ones_succ, listTail_ones_succ]
  -- Phase 3: b1_to_f (1 step)
  rw [run_add, b1_to_f]
  simp only [listHead_ones_succ, listTail_ones_succ]
  -- Phase 4: F_shift (c+2 steps)
  rw [run_add, F_shift (c + 1) [false, true] [false, false]]
  simp only [listHead_cons, listTail_cons]
  -- Phase 5: f_bounce_interior (3 steps)
  rw [run_add, f_bounce_interior (c + 1) [false, true] [false]]
  simp only [listHead_cons, listTail_cons, List.cons_append,
    List.nil_append, show c + 1 + 1 = c + 2 from by omega]
  -- Phase 6: f0_d0_to_e (2 steps)
  rw [run_add, f0_d0_to_e (ones (c + 2) ++ [false, true]) []]
  simp only [listHead_ones_succ, listTail_ones_succ]
  -- Phase 7: E,1→A (1 step)
  simp only [run, step, sw_E1, listHead_ones_succ, listTail_ones_succ]
  -- Match target
  simp only [M_Config_cons, show c + 1 - 1 = c from by omega, runs_singleton,
    ones_succ, ones_zero]

/-- Rule 1' (terminal): Single-run sweep from cursor = 2.
    [(2)] → M0[1, 1] -/
theorem macro_sweep_solo_to_zero :
    run sweeper (M_Config [] 2 []) 11 = M0_Config [1] [1] := by
  rfl

/-- Rule 1a: Sweep with left empty, right nonempty.
    [(c+3), d, R...] → [1, (c+1), d+1, R...] -/
theorem macro_sweep_left_empty (c d : Nat) (R : List Nat) :
    run sweeper (M_Config [] (c + 3) (d :: R)) (2 * (c + 3) + 7) =
    M_Config [1] (c + 1) ((d + 1) :: R) := by
  conv_lhs => rw [M_Config_nil, show c + 3 - 1 = c + 2 from by omega,
    show ones (c + 2) = ones (c + 2) ++ ([] : List Sym) from (List.append_nil _).symm]
  rw [show 2 * (c + 3) + 7 = (c + 2 + 1) + (1 + (1 + ((c + 1 + 1) + (3 + (2 + 1))))) from by omega]
  -- Phase 1: A_shift
  rw [run_add, A_shift (c + 2) [] (false :: false :: runs (d :: R))]
  simp only [listHead_nil, listTail_nil]
  -- Phase 2: a0_to_b
  rw [run_add, a0_to_b]
  simp only [listHead_ones_succ, listTail_ones_succ]
  -- Phase 3: b1_to_f
  rw [run_add, b1_to_f]
  simp only [listHead_ones_succ, listTail_ones_succ]
  -- Phase 4: F_shift
  rw [run_add, F_shift (c + 1) [false, true] (false :: false :: runs (d :: R))]
  simp only [listHead_cons, listTail_cons]
  -- Phase 5: f_bounce_interior
  rw [run_add, f_bounce_interior (c + 1) [false, true] (false :: runs (d :: R))]
  simp only [listHead_cons, listTail_cons, List.cons_append,
    List.nil_append, show c + 1 + 1 = c + 2 from by omega]
  -- Phase 6: f0_d0_to_e
  rw [run_add, f0_d0_to_e (ones (c + 2) ++ [false, true]) (runs (d :: R))]
  simp only [listHead_ones_succ, listTail_ones_succ]
  -- Phase 7: E,1→A
  simp only [run, step, sw_E1, listHead_ones_succ, listTail_ones_succ]
  -- Match target
  conv_rhs => rw [M_Config_cons, show c + 1 - 1 = c from by omega, runs_succ, runs_succ]
  simp only [runs_singleton, ones_zero]

/-- Rule 1a (terminal): Sweep with left empty, cursor = 2.
    [(2), d, R...] → M0[1, d+1, R...] -/
theorem macro_sweep_to_zero_left_empty (d : Nat) (R : List Nat) :
    run sweeper (M_Config [] 2 (d :: R)) 11 =
    M0_Config [1] ((d + 1) :: R) := by
  simp only [M_Config, M0_Config, ones_succ, ones_zero, List.nil_append, List.cons_append, run,
    step, sw_A0, sw_A1, sw_B1, sw_D0, sw_D1, sw_E1, sw_F0, sw_F1,
    listHead_cons, listTail_cons, listHead_nil, listTail_nil,
    show 2 - 1 = 1 from rfl, runs_succ, runs_singleton]

/-- Rule 1b: Sweep with right empty, left nonempty.
    [a, (c+3)] → [a+1, (c+1), 1] -/
theorem macro_sweep_right_empty (a c : Nat) (L : List Nat) :
    run sweeper (M_Config (a :: L) (c + 3) []) (2 * (c + 3) + 7) =
    M_Config ((a + 1) :: L) (c + 1) [1] := by
  conv_lhs => rw [M_Config_cons, show c + 3 - 1 = c + 2 from by omega, runs_nil]
  rw [show 2 * (c + 3) + 7 = (c + 2 + 1) + (1 + (1 + ((c + 1 + 1) + (3 + (2 + 1))))) from by omega]
  -- Phase 1: A_shift
  rw [run_add, A_shift (c + 2) (false :: runs (a :: L)) [false, false]]
  simp only [listHead_cons, listTail_cons]
  -- Phase 2: a0_to_b
  rw [run_add, a0_to_b]
  simp only [listHead_ones_succ, listTail_ones_succ]
  -- Phase 3: b1_to_f
  rw [run_add, b1_to_f]
  simp only [listHead_ones_succ, listTail_ones_succ]
  -- Phase 4: F_shift
  rw [run_add, F_shift (c + 1) (false :: true :: runs (a :: L)) [false, false]]
  simp only [listHead_cons, listTail_cons]
  -- Phase 5: f_bounce_interior
  rw [run_add, f_bounce_interior (c + 1) (false :: true :: runs (a :: L)) [false]]
  simp only [listHead_cons, listTail_cons, List.cons_append,
    List.nil_append, show c + 1 + 1 = c + 2 from by omega]
  -- Phase 6: f0_d0_to_e
  rw [run_add, f0_d0_to_e (ones (c + 2) ++ false :: true :: runs (a :: L)) []]
  simp only [listHead_ones_succ, listTail_ones_succ]
  -- Phase 7: E,1→A
  simp only [run, step, sw_E1, listHead_ones_succ, listTail_ones_succ]
  -- Match target
  conv_rhs => rw [M_Config_cons, show c + 1 - 1 = c from by omega, runs_succ]
  simp only [runs_singleton, ones_succ, ones_zero]

/-- Rule 1b (terminal): Sweep with right empty, cursor = 2.
    [a, (2)] → M0[a+1, 1] -/
theorem macro_sweep_to_zero_right_empty (a : Nat) (L : List Nat) :
    run sweeper (M_Config (a :: L) 2 []) 11 =
    M0_Config ((a + 1) :: L) [1] := by
  simp only [M_Config_cons, M0_Config_cons, ones_succ, ones_zero, List.nil_append, List.cons_append,
    run, step, sw_A0, sw_A1, sw_B1, sw_D0, sw_D1, sw_E1, sw_F0, sw_F1,
    listHead_cons, listTail_cons,
    show 2 - 1 = 1 from rfl,
    runs_succ, runs_singleton, runs_nil]

/-- Rule 2: Cursor shift left (cursor = 1).
    [a+1, (1), d, R...] → [(a+1), 1, d, R...] -/
theorem macro_shift (a d : Nat) (L R : List Nat) :
    run sweeper (M_Config ((a + 1) :: L) 1 (d :: R)) 6 =
    M_Config L (a + 1) (1 :: d :: R) := by
  cases L with
  | nil =>
    simp only [M_Config_cons, M_Config_nil, ones_zero, List.nil_append, run, step,
      sw_A0, sw_A1, sw_B1, sw_D0, sw_E1, sw_F0, listHead_cons, listTail_cons,
      show (1 : Nat) - 1 = 0 from rfl, show a + 1 - 1 = a from by omega,
      runs_succ, runs_singleton, runs_cons₂,
      List.singleton_append]
  | cons b L' =>
    simp only [M_Config_cons, ones_zero, List.nil_append, run, step,
      sw_A0, sw_A1, sw_B1, sw_D0, sw_E1, sw_F0, listHead_cons, listTail_cons,
      show (1 : Nat) - 1 = 0 from rfl, show a + 1 - 1 = a from by omega,
      runs_succ, runs_cons₂, List.singleton_append, List.append_assoc]

/-- Rule 7: Era completion.
    [a+1, (0), 1] → [(a+6)] -/
theorem macro_era_complete (a : Nat) (L : List Nat) :
    run sweeper (M0_Config ((a + 1) :: L) [1]) 8 =
    M_Config L (a + 6) [] := by
  cases L with
  | nil =>
    simp only [M0_Config_cons, M_Config_nil, runs_nil, runs_singleton, ones_zero, ones_succ,
      run, step, sw_A0, sw_B0, sw_C0, sw_D0, sw_D1, sw_E1,
      listHead_cons, listTail_cons, listHead_nil, listTail_nil,
      show a + 6 - 1 = a + 5 from by omega]
  | cons b L' =>
    simp only [M0_Config_cons, M_Config_cons, runs_cons₂, runs_singleton, runs_nil, ones_zero,
      ones_succ, List.nil_append, List.cons_append, List.append_assoc, run, step, sw_A0, sw_B0,
      sw_C0, sw_D0, sw_D1, sw_E1, listHead_cons, listTail_cons, listHead_nil, listTail_nil,
      show a + 6 - 1 = a + 5 from by omega, runs_succ]

/-- Rule 4: Cursor at 0, single right run ≥ 4, result cursor ≥ 1.
    [a, (0), z+4] → [a+4, (z+1), 1] -/
theorem macro_zero_bounce (a z : Nat) (L : List Nat) :
    run sweeper (M0_Config (a :: L) [z + 4]) (z + 13) =
    M_Config ((a + 4) :: L) (z + 1) [1] := by
  -- Unfold M0_Config, use M0_to_F for the first 5 steps
  simp only [M0_Config_cons, runs_singleton]
  rw [show ones (z + 4) = ones ((z + 1) + 3) ++ ([] : List Sym) from by
    rw [show (z + 1) + 3 = z + 4 from by omega, List.append_nil]]
  rw [show z + 13 = 5 + (z + 8) from by omega,
    run_add, M0_to_F (z + 1) (runs (a :: L)) []]
  -- F_shift (z+2 steps) — right tape is ones(z+1) ++ []
  rw [show z + 8 = (z + 1 + 1) + (3 + (2 + 1)) from by omega,
    run_add, F_shift (z + 1) (false :: true :: true :: true :: true :: runs (a :: L)) []]
  simp only [listHead_nil, listTail_nil]
  -- f_bounce_interior (3 steps)
  rw [show z + 1 + 1 = (z + 1) + 1 from by omega]
  rw [run_add, f_bounce_interior (z + 1) (false :: true :: true :: true :: true :: runs (a :: L)) []]
  simp only [listHead_nil, listTail_nil, List.cons_append,
    List.nil_append, show z + 1 + 1 = z + 2 from by omega]
  -- f0_d0_to_e (2 steps)
  rw [run_add, f0_d0_to_e (ones (z + 2) ++ false :: true :: true :: true :: true :: runs (a :: L)) []]
  simp only [listHead_ones_succ, listTail_ones_succ]
  -- E,1→A (1 step)
  simp only [run, step, sw_E1, listHead_ones_succ, listTail_ones_succ]
  -- Match target
  simp only [M_Config_cons, show z + 1 - 1 = z from by omega, runs_singleton, runs_succ,
    ones_zero]

/-- Rule 4 (terminal): Cursor at 0, right run = 3.
    [a, (0), 3] → M0[a+4, 1] -/
theorem macro_zero_bounce_to_zero (a : Nat) (L : List Nat) :
    run sweeper (M0_Config (a :: L) [3]) 12 =
    M0_Config ((a + 4) :: L) [1] := by
  cases L with
  | nil =>
    simp only [M0_Config_cons, runs_singleton, ones_zero, ones_succ,
      run, step, sw_A0, sw_B0, sw_B1, sw_C0, sw_D0, sw_D1, sw_E1, sw_F0, sw_F1,
      listHead_cons, listTail_cons, listHead_nil, listTail_nil]
  | cons b L' =>
    simp only [M0_Config_cons, runs_cons₂, runs_singleton, ones_zero,
      List.nil_append, List.cons_append, List.append_assoc, run, step,
      sw_A0, sw_B0, sw_B1, sw_C0, sw_D0, sw_D1, sw_E1, sw_F0, sw_F1,
      listHead_cons, listTail_cons, listHead_nil, listTail_nil, runs_succ]

/-- Rule 5: Cursor at 0, right run = 2.
    [a, (0), 2, d, R...] → [(a+3), d+1, R...] -/
theorem macro_zero_two (a d : Nat) (L R : List Nat) :
    run sweeper (M0_Config (a :: L) (2 :: d :: R)) 8 =
    M_Config L (a + 3) ((d + 1) :: R) := by
  cases L with
  | nil =>
    simp only [M0_Config_cons, M_Config_nil, runs_cons₂, runs_singleton, ones_zero,
      ones_succ, List.nil_append, List.singleton_append, run, step,
      sw_A0, sw_B0, sw_B1, sw_C0, sw_D0, sw_D1, sw_E1, sw_F0,
      listHead_cons, listTail_cons, runs_succ,
      show a + 3 - 1 = a + 2 from by omega]
  | cons b L' =>
    simp only [M0_Config_cons, M_Config_cons, runs_cons₂, ones_zero,
      ones_succ, List.nil_append, List.cons_append, List.append_assoc,
      run, step, sw_A0, sw_B0, sw_B1, sw_C0, sw_D0, sw_D1, sw_E1, sw_F0,
      listHead_cons, listTail_cons, runs_succ,
      show a + 3 - 1 = a + 2 from by omega]

/-- Rule 5 (terminal): Cursor at 0, single right run = 2.
    [a, (0), 2] → [(a+3), 1] -/
theorem macro_zero_two_solo (a : Nat) (L : List Nat) :
    run sweeper (M0_Config (a :: L) [2]) 8 =
    M_Config L (a + 3) [1] := by
  cases L with
  | nil =>
    simp only [M0_Config_cons, M_Config_nil, runs_singleton, ones_zero, ones_succ,
      run, step, sw_A0, sw_B0, sw_B1, sw_C0, sw_D0, sw_D1, sw_E1, sw_F0,
      listHead_cons, listTail_cons, listHead_nil, listTail_nil,
      show a + 3 - 1 = a + 2 from by omega]
  | cons b L' =>
    simp only [M0_Config_cons, M_Config_cons, runs_cons₂, runs_singleton, ones_zero, ones_succ,
      List.nil_append, List.cons_append, List.append_assoc, run, step,
      sw_A0, sw_B0, sw_B1, sw_C0, sw_D0, sw_D1, sw_E1, sw_F0,
      listHead_cons, listTail_cons, listHead_nil, listTail_nil, runs_succ,
      show a + 3 - 1 = a + 2 from by omega]

/-- Rule 6: Halt condition. Cursor at 0, run of 1 followed by positive run.
    C reads 1 from the run after the 1 → undefined transition.
    [..., (0), 1, z+1, R...] → halts -/
theorem macro_halt (z : Nat) (L R : List Nat) :
    (run sweeper (M0_Config L (1 :: (z + 1) :: R)) 6).state = none := by
  simp only [M0_Config, runs_cons₂, ones_succ, ones_zero, List.nil_append, List.cons_append,
    run, step, sw_A0, sw_B0, sw_C0, sw_D1, sw_C1, listHead_cons, listTail_cons,
    listHead_runs_pos]

-- ============================================================
-- Multi-run zero bounce
-- ============================================================

/-- Multi-run bounce with 2 runs: M₀(a∷L, [r+3, rₙ+2]) with r₁=r+3 ≥ 3, rₙ+2 ≥ 2.
    Output: M((r+1)::(a+4)::L, rₙ+1, [1]).
    Step count: 5 + (r+1) + 3 + (rₙ+2) + 3 + 2 + 1 = r+rₙ+17. -/
theorem macro_multi_bounce_2 (a r rₙ : Nat) (L : List Nat) :
    run sweeper (M0_Config (a :: L) [r + 3, rₙ + 2]) (r + rₙ + 17) =
    M_Config ((r + 1) :: (a + 4) :: L) (rₙ + 1) [1] := by
  -- Unfold M0_Config and runs to raw tape
  simp only [M0_Config_cons, runs_cons₂, runs_singleton]
  rw [List.append_assoc, show [false] ++ ones (rₙ + 2) = false :: ones (rₙ + 2) from rfl]
  -- Phase 0: M0_to_F (5 steps: A→B→C→D→B→F)
  rw [show r + rₙ + 17 = 5 + (r + rₙ + 12) from by omega,
    run_add, M0_to_F r (runs (a :: L)) (false :: ones (rₙ + 2))]
  -- Phase 1: F_shift through r ones (r+1 steps)
  rw [show r + rₙ + 12 = (r + 1) + (3 + (rₙ + 8)) from by omega,
    run_add, F_shift r (false :: true :: true :: true :: true :: runs (a :: L))
                       (false :: ones (rₙ + 2))]
  simp only [listHead_cons, listTail_cons]
  -- Phase 2: f_bounce_interior at inter-run zero (3 steps)
  rw [run_add, f_bounce_interior r
    (false :: true :: true :: true :: true :: runs (a :: L)) (ones (rₙ + 2))]
  -- Reduce ones(rₙ+2) for listHead/listTail
  rw [show ones (rₙ + 2) = true :: ones (rₙ + 1) from by
    rw [show rₙ + 2 = (rₙ + 1) + 1 from by omega, ones_succ]]
  simp only [listHead_cons, listTail_cons, List.cons_append,
    List.nil_append]
  -- Phase 3: F_shift through rₙ+1 ones (rₙ+2 steps)
  rw [show ones (rₙ + 1) = ones (rₙ + 1) ++ ([] : List Sym) from (List.append_nil _).symm]
  rw [show rₙ + 8 = (rₙ + 1 + 1) + (3 + (2 + 1)) from by omega,
    run_add, F_shift (rₙ + 1)
      (false :: (ones (r + 1) ++
        false :: true :: true :: true :: true :: runs (a :: L))) []]
  simp only [listHead_nil, listTail_nil]
  -- Phase 4: f_bounce_interior at end (3 steps), k = rₙ+1
  rw [show rₙ + 1 + 1 = (rₙ + 1) + 1 from by omega]
  rw [run_add, f_bounce_interior (rₙ + 1)
    (false :: (ones (r + 1) ++ false :: true :: true :: true :: true :: runs (a :: L))) []]
  simp only [listHead_nil, listTail_nil, List.cons_append,
    List.nil_append, show rₙ + 1 + 1 = rₙ + 2 from by omega]
  -- Phase 5: f0_d0_to_e (2 steps)
  rw [run_add, f0_d0_to_e
    (ones (rₙ + 2) ++ false :: (ones (r + 1) ++
      false :: true :: true :: true :: true :: runs (a :: L))) []]
  simp only [show rₙ + 2 = (rₙ + 1) + 1 from by omega,
    listHead_ones_succ, listTail_ones_succ]
  -- Phase 6: E,1→A (1 step)
  simp only [run, step, sw_E1, listHead_ones_succ, listTail_ones_succ]
  -- Match M_Config target
  simp only [M_Config_cons, show rₙ + 1 - 1 = rₙ from by omega]
  -- Strip ones rₙ ++ false :: from both sides
  congr 1; congr 1; congr 1
  -- Goal: ones (r+1) ++ false :: tttt :: runs(a::L)
  --     = runs((r+1) :: (a+4) :: L)
  -- Rewrite tttt :: runs(a::L) = ones 4 ++ runs(a::L) = runs((a+4)::L)
  rw [show (true :: true :: true :: true :: runs (a :: L) : List Sym) =
    ones 4 ++ runs (a :: L) from rfl]
  rw [ones_append_runs, show 4 + a = a + 4 from by omega]
  -- Goal: ones (r+1) ++ false :: runs((a+4)::L) = runs((r+1) :: (a+4) :: L)
  rw [show (false :: runs ((a + 4) :: L) : List Sym) =
    [false] ++ runs ((a + 4) :: L) from rfl]
  rw [← List.append_assoc]
  exact (runs_cons₂ (r + 1) (a + 4) L).symm

/-- Right-edge bounce with a single one: F sweeps through 1 one at the
    right edge, bounces F→D→B→F→D→E→A. The output is M0_Config shape
    (state A, head false). Requires k ≥ 0 (ones(k+1) in left). -/
theorem F_bounce_single_one (k : Nat) (L : List Sym) :
    run sweeper (⟨some stF, false :: ones (k + 1) ++ L, true, []⟩ : Config 6) 7 =
    (⟨some stA, ones (k + 1) ++ L, false, [false, false, true]⟩ : Config 6) := by
  sw_steps

/-- Multi-run bounce to zero: 2-run case with second run = 1.
    M0_Config (a::L) [r+3, 1] → M0_Config ((r+1)::(a+4)::L) [1] in r+16 steps. -/
theorem macro_multi_bounce_2_to_zero (a r : Nat) (L : List Nat) :
    run sweeper (M0_Config (a :: L) [r + 3, 1]) (r + 16) =
    M0_Config ((r + 1) :: (a + 4) :: L) [1] := by
  -- Unfold M0_Config and runs to raw tape
  simp only [M0_Config_cons, runs_cons₂, runs_singleton]
  rw [List.append_assoc, show [false] ++ ones 1 = [false, true] from rfl]
  -- Phase 0: M0_to_F (5 steps: A→B→C→D→B→F)
  rw [show r + 16 = 5 + (r + 11) from by omega,
    run_add, M0_to_F r (runs (a :: L)) [false, true]]
  -- Phase 1: F_shift through r ones (r+1 steps)
  rw [show r + 11 = (r + 1) + (3 + 7) from by omega,
    run_add, F_shift r (false :: true :: true :: true :: true :: runs (a :: L))
                       [false, true]]
  simp only [listHead_cons, listTail_cons]
  -- Phase 2: f_bounce_interior at inter-run zero (3 steps)
  rw [run_add, f_bounce_interior r
    (false :: true :: true :: true :: true :: runs (a :: L)) [true]]
  simp only [listHead_cons, listTail_cons, List.cons_append, List.nil_append]
  -- Phase 3: F_bounce_single_one (7 steps)
  -- Rewrite left to match F_bounce_single_one pattern
  rw [show false :: (ones (r + 1) ++ false :: true :: true :: true :: true :: runs (a :: L)) =
    false :: ones (r + 1) ++ (false :: true :: true :: true :: true :: runs (a :: L)) from by
    rw [List.cons_append]]
  rw [F_bounce_single_one r
    (false :: true :: true :: true :: true :: runs (a :: L))]
  -- Match M0_Config target
  -- RHS right: false :: false :: ones 1 = [false, false, true]
  simp only [ones_succ, ones_zero]
  -- LHS/RHS left: rewrite tttt :: runs(a::L) = ones 4 ++ runs(a::L) = runs((a+4)::L)
  congr 1
  rw [show (true :: true :: true :: true :: runs (a :: L) : List Sym) =
    ones 4 ++ runs (a :: L) from rfl]
  rw [ones_append_runs, show 4 + a = a + 4 from by omega]
  rw [show (false :: runs ((a + 4) :: L) : List Sym) =
    [false] ++ runs ((a + 4) :: L) from rfl]
  rw [← List.append_assoc]

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
    run sweeper (E_Config 4 0) 65 = E_Config 10 0 := rfl

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
-- Macro configuration type and invariant
-- ============================================================

/-- Abstract macro configuration type. -/
inductive MacroConfig where
  | M : List Nat → Nat → List Nat → MacroConfig   -- M_Config L c R
  | M0 : List Nat → List Nat → MacroConfig         -- M0_Config L R

/-- Embed a MacroConfig into a TM Config. -/
def MacroConfig.toConfig : MacroConfig → Config 6
  | .M L c R => M_Config L c R
  | .M0 L R => M0_Config L R

/-- All elements of a list are ≥ 1. -/
def AllGe1 : List Nat → Prop
  | [] => True
  | n :: L => n ≥ 1 ∧ AllGe1 L

lemma AllGe1_nil : AllGe1 [] := trivial

lemma AllGe1_cons {n : Nat} {L : List Nat} :
    AllGe1 (n :: L) ↔ n ≥ 1 ∧ AllGe1 L := Iff.rfl

lemma AllGe1_singleton {n : Nat} (h : n ≥ 1) : AllGe1 [n] :=
  ⟨h, trivial⟩

/-- The macro invariant: all run-length values ≥ 1, cursor ≥ 1. -/
def MacroInvariant : MacroConfig → Prop
  | .M L c R => AllGe1 L ∧ c ≥ 1 ∧ AllGe1 R
  | .M0 L R => AllGe1 L ∧ AllGe1 R

-- ============================================================
-- Invariant preservation by macro rules
-- ============================================================

/-- Sweep preserves invariant. -/
theorem invariant_sweep {a c d : Nat} {L R : List Nat}
    (h : MacroInvariant (.M (a :: L) (c + 3) (d :: R))) :
    MacroInvariant (.M ((a + 1) :: L) (c + 1) ((d + 1) :: R)) := by
  obtain ⟨hL, _, hR⟩ := h
  rw [AllGe1_cons] at hL hR
  exact ⟨AllGe1_cons.mpr ⟨by omega, hL.2⟩, by omega, AllGe1_cons.mpr ⟨by omega, hR.2⟩⟩

/-- Sweep to zero preserves invariant. -/
theorem invariant_sweep_to_zero {a d : Nat} {L R : List Nat}
    (h : MacroInvariant (.M (a :: L) 2 (d :: R))) :
    MacroInvariant (.M0 ((a + 1) :: L) ((d + 1) :: R)) := by
  obtain ⟨hL, _, hR⟩ := h
  rw [AllGe1_cons] at hL hR
  exact ⟨AllGe1_cons.mpr ⟨by omega, hL.2⟩, AllGe1_cons.mpr ⟨by omega, hR.2⟩⟩

/-- Solo sweep preserves invariant. -/
theorem invariant_sweep_solo {c : Nat}
    (_ : MacroInvariant (.M [] (c + 3) [])) :
    MacroInvariant (.M [1] (c + 1) [1]) := by
  exact ⟨AllGe1_singleton (by omega), by omega, AllGe1_singleton (by omega)⟩

/-- Solo sweep to zero preserves invariant. -/
theorem invariant_sweep_solo_to_zero
    (_ : MacroInvariant (.M [] 2 [])) :
    MacroInvariant (.M0 [1] [1]) := by
  exact ⟨AllGe1_singleton (by omega), AllGe1_singleton (by omega)⟩

/-- Left-empty sweep preserves invariant. -/
theorem invariant_sweep_left_empty {c d : Nat} {R : List Nat}
    (h : MacroInvariant (.M [] (c + 3) (d :: R))) :
    MacroInvariant (.M [1] (c + 1) ((d + 1) :: R)) := by
  obtain ⟨_, _, hR⟩ := h
  rw [AllGe1_cons] at hR
  exact ⟨AllGe1_singleton (by omega), by omega, AllGe1_cons.mpr ⟨by omega, hR.2⟩⟩

/-- Left-empty sweep to zero preserves invariant. -/
theorem invariant_sweep_to_zero_left_empty {d : Nat} {R : List Nat}
    (h : MacroInvariant (.M [] 2 (d :: R))) :
    MacroInvariant (.M0 [1] ((d + 1) :: R)) := by
  obtain ⟨_, _, hR⟩ := h
  rw [AllGe1_cons] at hR
  exact ⟨AllGe1_singleton (by omega), AllGe1_cons.mpr ⟨by omega, hR.2⟩⟩

/-- Right-empty sweep preserves invariant. -/
theorem invariant_sweep_right_empty {a c : Nat} {L : List Nat}
    (h : MacroInvariant (.M (a :: L) (c + 3) [])) :
    MacroInvariant (.M ((a + 1) :: L) (c + 1) [1]) := by
  obtain ⟨hL, _, _⟩ := h
  rw [AllGe1_cons] at hL
  exact ⟨AllGe1_cons.mpr ⟨by omega, hL.2⟩, by omega, AllGe1_singleton (by omega)⟩

/-- Right-empty sweep to zero preserves invariant. -/
theorem invariant_sweep_to_zero_right_empty {a : Nat} {L : List Nat}
    (h : MacroInvariant (.M (a :: L) 2 [])) :
    MacroInvariant (.M0 ((a + 1) :: L) [1]) := by
  obtain ⟨hL, _, _⟩ := h
  rw [AllGe1_cons] at hL
  exact ⟨AllGe1_cons.mpr ⟨by omega, hL.2⟩, AllGe1_singleton (by omega)⟩

/-- Shift preserves invariant. -/
theorem invariant_shift {a d : Nat} {L R : List Nat}
    (h : MacroInvariant (.M ((a + 1) :: L) 1 (d :: R))) :
    MacroInvariant (.M L (a + 1) (1 :: d :: R)) := by
  obtain ⟨hL, _, hR⟩ := h
  rw [AllGe1_cons] at hL
  exact ⟨hL.2, by omega, AllGe1_cons.mpr ⟨by omega, hR⟩⟩

/-- Era complete preserves invariant. -/
theorem invariant_era_complete {a : Nat} {L : List Nat}
    (h : MacroInvariant (.M0 (a :: L) [1])) :
    MacroInvariant (.M L (a + 6) []) := by
  obtain ⟨hL, _⟩ := h
  rw [AllGe1_cons] at hL
  exact ⟨hL.2, by omega, AllGe1_nil⟩

/-- Zero two solo preserves invariant. -/
theorem invariant_zero_two_solo {a : Nat} {L : List Nat}
    (h : MacroInvariant (.M0 (a :: L) [2])) :
    MacroInvariant (.M L (a + 3) [1]) := by
  obtain ⟨hL, _⟩ := h
  rw [AllGe1_cons] at hL
  exact ⟨hL.2, by omega, AllGe1_singleton (by omega)⟩

/-- Zero bounce preserves invariant (R = [z+4]). -/
theorem invariant_zero_bounce {a z : Nat} {L : List Nat}
    (h : MacroInvariant (.M0 (a :: L) [z + 4])) :
    MacroInvariant (.M ((a + 4) :: L) (z + 1) [1]) := by
  obtain ⟨hL, _⟩ := h
  rw [AllGe1_cons] at hL
  exact ⟨AllGe1_cons.mpr ⟨by omega, hL.2⟩, by omega, AllGe1_singleton (by omega)⟩

/-- Zero bounce to zero preserves invariant (R = [3]). -/
theorem invariant_zero_bounce_to_zero {a : Nat} {L : List Nat}
    (h : MacroInvariant (.M0 (a :: L) [3])) :
    MacroInvariant (.M0 ((a + 4) :: L) [1]) := by
  obtain ⟨hL, _⟩ := h
  rw [AllGe1_cons] at hL
  exact ⟨AllGe1_cons.mpr ⟨by omega, hL.2⟩, AllGe1_singleton (by omega)⟩

/-- Zero two (multi-run) preserves invariant. -/
theorem invariant_zero_two {a d : Nat} {L R : List Nat}
    (h : MacroInvariant (.M0 (a :: L) (2 :: d :: R))) :
    MacroInvariant (.M L (a + 3) ((d + 1) :: R)) := by
  obtain ⟨hL, hR⟩ := h
  rw [AllGe1_cons] at hL
  rw [AllGe1_cons] at hR
  obtain ⟨_, hR2⟩ := hR
  rw [AllGe1_cons] at hR2
  exact ⟨hL.2, by omega, AllGe1_cons.mpr ⟨by omega, hR2.2⟩⟩

/-- Multi-run bounce (2-run, rₙ ≥ 2) preserves invariant. -/
theorem invariant_multi_bounce_2 {a r rₙ : Nat} {L : List Nat}
    (h : MacroInvariant (.M0 (a :: L) [r + 3, rₙ + 2])) :
    MacroInvariant (.M ((r + 1) :: (a + 4) :: L) (rₙ + 1) [1]) := by
  obtain ⟨hL, _⟩ := h
  rw [AllGe1_cons] at hL
  exact ⟨AllGe1_cons.mpr ⟨by omega, AllGe1_cons.mpr ⟨by omega, hL.2⟩⟩,
         by omega, AllGe1_singleton (by omega)⟩

/-- Multi-run bounce to zero (2-run, rₙ = 1) preserves invariant. -/
theorem invariant_multi_bounce_2_to_zero {a r : Nat} {L : List Nat}
    (h : MacroInvariant (.M0 (a :: L) [r + 3, 1])) :
    MacroInvariant (.M0 ((r + 1) :: (a + 4) :: L) [1]) := by
  obtain ⟨hL, _⟩ := h
  rw [AllGe1_cons] at hL
  exact ⟨AllGe1_cons.mpr ⟨by omega, AllGe1_cons.mpr ⟨by omega, hL.2⟩⟩,
         AllGe1_singleton (by omega)⟩

-- ============================================================
-- Invariant prevents halting
-- ============================================================

/-- The only source of M0 with |R| ≥ 2 is sweep_to_zero, producing (d+1)::R'.
    Under AllGe1, d ≥ 1 so d+1 ≥ 2.  HALT needs R[0] = 1, contradiction.
    This lemma captures the key step: if first element ≥ 2, halt pattern impossible. -/
theorem halt_pattern_impossible {r : Nat} {R : List Nat} (hr : r ≥ 2) :
    ∀ z R', r :: R = 1 :: (z + 1) :: R' → False := by
  intro z R' heq
  injection heq with h1 _
  omega

/-- sweep_to_zero outputs have first R element ≥ 2 when invariant holds. -/
theorem sweep_to_zero_first_ge2 {d : Nat} (hd : d ≥ 1) :
    d + 1 ≥ 2 := by omega

-- ============================================================
-- Initial configuration satisfies invariant
-- ============================================================

/-- The initial macro config M_Config [] 6 [] satisfies the invariant
    (vacuously — no runs). -/
theorem invariant_initial : MacroInvariant (.M [] 6 []) :=
  ⟨AllGe1_nil, by omega, AllGe1_nil⟩

-- ============================================================
-- Initial configuration
-- ============================================================

/-- The machine starts in state A on a blank tape.
    After 19 steps it reaches E_Config 4 0 (all-1s tape of length 5). -/
theorem sweeper_init_to_era0 :
    run sweeper (initConfig 6) 19 = E_Config 4 0 := rfl

-- ============================================================
-- Main non-halting conjecture
-- ============================================================

/-- The machine never halts: for all k, the state after k steps is not none. -/
theorem sweeper_never_halts (k : Nat) :
    (run sweeper (initConfig 6) k).state ≠ none := by
  sorry

end Sweeper
