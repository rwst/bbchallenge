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

-- ============================================================
-- Conjecture C1: Non-halting (structural)
-- ============================================================

/-! ### C1: Non-halting

E,0 is fully eliminated by backward chain analysis (see above).
The only remaining halt path is C,1, which requires B to read 0
with a 1 to its right (c1_halt_via_b).

The tape invariant only needs to show:
- B reads 0 only at the right tape edge (where right tape is all 0s)

### SafeRight predicate

Period-3 recursive predicate on B.right. Ensures C always reads 0
through arbitrary depth of B→C→D chain recursion:
- B reads 0, C reads R[0]. Must be false.
- C,0→1RD: D reads R[1].
  - D reads 0: BCD extension at right edge. Safe.
  - D reads 1: D,1→1RB. New B reads R[2].
    - B reads 1: goes to F. Safe.
    - B reads 0: enters C again. Recurse on R[3:].

### A-condition

At A,0→B: B.head = listHead(A.right), B.right = listTail(A.right).
If B reads 1 (listHead A.right = true), B→F (safe, no C entry).
If B reads 0, we need SafeRight(B.right) = SafeRight(listTail A.right).

So the A-condition is: A reads 0 → either B will read 1 (safe) or
B's right tape satisfies SafeRight. -/

/-- SafeRight: period-3 recursive predicate on B.right tape.
    Ensures C always reads 0 through arbitrary B→C→D chain depth. -/
def SafeRight : List Sym → Prop
  | [] => True
  | true :: _ => False
  | false :: [] => True
  | false :: false :: _ => True
  | false :: true :: [] => True
  | false :: true :: true :: _ => True
  | false :: true :: false :: rest => SafeRight rest

/-- SafeRight implies C reads 0 (the first element is false or list is empty). -/
lemma SafeRight_head {R : List Sym} (h : SafeRight R) : listHead R false = false := by
  cases R with
  | nil => rfl
  | cons r _ =>
    cases r with
    | true => simp [SafeRight] at h
    | false => rfl

/-- SafeRight1: shifted SafeRight for state C. Tracks positions 1+ of B.right
    through the B→C→D chain. C.right = listTail(B.right). -/
def SafeRight1 : List Sym → Prop
  | [] => True
  | false :: _ => True
  | true :: [] => True
  | true :: true :: _ => True
  | true :: false :: rest => SafeRight rest

/-- SafeRight → SafeRight1 after B→C shift. -/
lemma SafeRight_to_SafeRight1 {R : List Sym} (h : SafeRight R) :
    SafeRight1 (listTail R) := by
  match R, h with
  | [], _ => simp [listTail, SafeRight1]
  | true :: _, h => simp [SafeRight] at h
  | false :: [], _ => simp [listTail, SafeRight1]
  | false :: false :: _, _ => simp [listTail, SafeRight1]
  | false :: true :: [], _ => simp [listTail, SafeRight1]
  | false :: true :: true :: _, _ => simp [listTail, SafeRight1]
  | false :: true :: false :: rest, h => exact h

/-- SafeRight2: shifted SafeRight for state D. Tracks position 2+ of B.right.
    D.right = listTail(C.right) = listTail(listTail(B.right)). -/
def SafeRight2 : List Sym → Prop
  | [] => True
  | true :: _ => True
  | false :: rest => SafeRight rest

/-- SafeRight1 → SafeRight2 after C→D shift (when D reads 1). -/
lemma SafeRight1_to_SafeRight2 {R : List Sym} (h : SafeRight1 R)
    (hd : listHead R false = true) : SafeRight2 (listTail R) := by
  match R, h, hd with
  | [], _, hd => simp [listHead] at hd
  | false :: _, _, hd => simp [listHead] at hd
  | true :: [], _, _ => simp [listTail, SafeRight2]
  | true :: true :: _, _, _ => simp [listTail, SafeRight2]
  | true :: false :: rest, h, _ => exact h

/-- SafeRight2 → SafeRight after D→B shift (when new B reads 0). -/
lemma SafeRight2_to_SafeRight {R : List Sym} (h : SafeRight2 R)
    (hd : listHead R false = false) : SafeRight (listTail R) := by
  match R, h, hd with
  | [], _, _ => simp [listTail, SafeRight]
  | true :: _, _, hd => simp [listHead] at hd
  | false :: rest, h, _ => exact h

/-- Step-inductive invariant for C,1 elimination.
    B-condition: when B reads 0, SafeRight on right tape.
    A-condition: when A reads 0, B reads 1 or SafeRight for B's right.
    C-condition: when C reads 0, SafeRight1 on right (chain position 1+).
    D-condition: when D reads 1, SafeRight2 on right (chain position 2+). -/
private def C1Inv (c : Config 6) : Prop :=
  (c.state = some stB → c.head = false → SafeRight c.right) ∧
  (c.state = some stA → c.head = false →
    listHead c.right false = true ∨ SafeRight (listTail c.right)) ∧
  (c.state = some stC → c.head = false → SafeRight1 c.right) ∧
  (c.state = some stD → c.head = true → SafeRight2 c.right)

private lemma c1inv_init : C1Inv (initConfig 6) := by
  simp [C1Inv, initConfig, SafeRight, SafeRight1, SafeRight2, stB, stA, stC, stD]

private lemma c1inv_step (c : Config 6) (h : C1Inv c) : C1Inv (step sweeper c) := by
  obtain ⟨hB, hA, hC, hD⟩ := h
  rcases c with ⟨s, l, hd, r⟩
  simp only [] at hB hA hC hD
  cases s with
  | none => simp [C1Inv, step]
  | some q =>
    fin_cases q <;> cases hd <;>
      simp only [step, sw_A0, sw_A1, sw_B0, sw_B1, sw_C0, sw_C1, sw_D0, sw_D1,
        sw_E0, sw_E1, sw_F0, sw_F1, listHead_cons, listTail_cons, C1Inv] <;>
      simp_all [stA, stB, stC, stD, stE, stF]
    -- case A,0 → B: hA gives Or, listHead r = false kills left branch
    · intro h; rcases hA with h1 | h2
      · rw [h] at h1; exact absurd h1 Bool.noConfusion
      · exact h2
    -- case B,0 → C: SafeRight → SafeRight1
    · intro _; exact SafeRight_to_SafeRight1 hB
    -- case C,0 → D: SafeRight1 → SafeRight2
    · exact SafeRight1_to_SafeRight2 hC
    -- case D,1 → B: SafeRight2 → SafeRight
    · exact SafeRight2_to_SafeRight hD
    -- case E,1 → A: need SafeRight(E.right) when listHead l false = false
    -- This is the sole remaining sorry. See e1_to_a_safe below.
    · intro _; exact sorry
    -- case F,0 → D: SafeRight2(true :: r) = True
    · intro _; simp [SafeRight2]

-- ============================================================
-- E,1→A sorry analysis: the F-joint condition
-- ============================================================

/-! ### E,1→A: the sole remaining obstacle for c1inv_step

E enters only from D,0 → 0LE. D is entered from C,0 → 1RD or F,0 → 1LD.

**C→D→E path**: C reads 0, writes 1, moves R to D. D reads 0, writes 0,
moves L to E. E.left = `true :: B.left` (C wrote 1). So `listHead(E.left) = true`.
A reads 1 → A sweeps left (no B,0 event). **Vacuous** for the A-condition.

**F→D→E path**: F reads 0, writes 1, moves L to D. D reads 0, writes 0,
moves L to E. E.right = `false :: true :: F.right`. E.left[0] = F.left[2].

When F.left[2] = true: A reads 1 → vacuous for A-condition.
When F.left[2] = false: need `SafeRight(false :: true :: F.right)`.

`SafeRight(false :: true :: F.right)` is True except when
F.right = `false :: true :: rest` with ¬SafeRight(rest).

**The F-joint condition**: When F.head=false ∧ F.left[0]=false ∧ F.left[2]=false,
F.right never starts with `false :: true :: ...`. Equivalently:
  `SafeRight(false :: true :: F.right)` holds.

This is confirmed by simulation over 1M steps but couples F.left[2]
with F.right structure — a global tape property (zero-marker spacing). -/

/-- Extended invariant for C,1 elimination, adding an F-condition to C1Inv.
    The F-condition captures the joint left/right coupling:
    when F reads 0 with F.left[0]=false and F.left[2]=false,
    SafeRight must hold for the resulting E.right = false :: true :: F.right.

    This is equivalent to: F.left[2]=false → F.right does not start with
    false :: true :: rest where ¬SafeRight(rest).

    Simulation confirms over 1M steps: when F.left[2]=false,
    F.right is always empty or starts with true — never [false, true, ...].

    This is the SOLE remaining obstacle for c1_never_reached. -/
private def C1Inv_ext (c : Config 6) : Prop :=
  C1Inv c ∧
  -- Left-tape conditions (from E0Inv, needed to make D-cond vacuous at C→D)
  (c.state = some stB → listHead c.left false = true) ∧
  (c.state = some stC → listHead c.left false = true) ∧
  -- F-condition: when F reads 0 at interior zero (left[0]=false),
  -- and A will read 0 immediately (left[2]=false),
  -- the right tape satisfies SafeRight for the eventual B,0 event.
  (c.state = some stF → c.head = false →
    listHead c.left false = false →
    listHead (listTail (listTail c.left)) false = false →
    SafeRight (false :: true :: c.right)) ∧
  -- D-condition (augmented): when D reads 0 (head=false) and the
  -- cell 2 left of D's position is 0 (left[1]=false), the right
  -- tape prepended with false satisfies SafeRight.
  -- Propagates F-condition through F,0→D.
  (c.state = some stD → c.head = false →
    listHead (listTail c.left) false = false →
    SafeRight (false :: c.right)) ∧
  -- E-condition: when E reads 1 (head=true) and E.left[0]=false
  -- (meaning A will read 0 next), SafeRight holds on E's right tape.
  -- Propagates D-condition through D,0→E.
  (c.state = some stE → c.head = true →
    listHead c.left false = false →
    SafeRight c.right)

/-- C1Inv_ext holds for the initial configuration. -/
private lemma c1inv_ext_init : C1Inv_ext (initConfig 6) := by
  simp [C1Inv_ext, C1Inv, initConfig, SafeRight, SafeRight1, SafeRight2,
        stB, stA, stC, stD, stE, stF]

/-- C1Inv_ext is step-inductive. Once proven, c1_never_reached follows. -/
private lemma c1inv_ext_step (c : Config 6) (h : C1Inv_ext c) :
    C1Inv_ext (step sweeper c) := by
  rcases c with ⟨s, l, hd, r⟩
  cases s with
  | none => simp [C1Inv_ext, C1Inv, step]
  | some q =>
    unfold C1Inv_ext C1Inv at h
    fin_cases q <;> cases hd <;>
      simp only [step, sw_A0, sw_A1, sw_B0, sw_B1, sw_C0, sw_C1, sw_D0, sw_D1,
        sw_E0, sw_E1, sw_F0, sw_F1, listHead_cons, listTail_cons,
        C1Inv_ext, C1Inv, stA, stB, stC, stD, stE, stF] <;>
      simp_all [stA, stB, stC, stD, stE, stF, SafeRight2]
    -- A,0→B: A-condition gives B-condition
    · intro hh; cases h with
      | inl h1 => rw [hh] at h1; exact absurd h1 Bool.noConfusion
      | inr h2 => exact h2
    -- B,0→C: SafeRight → SafeRight1
    · intro _; exact SafeRight_to_SafeRight1 h.1
    -- B,1→F: SOLE REMAINING SORRY
    · sorry
    -- C,0→D: SafeRight1 → SafeRight2
    · exact SafeRight1_to_SafeRight2 h.1
    -- D,1→B: SafeRight2 → SafeRight
    · change SafeRight2 r at h
      exact SafeRight2_to_SafeRight h

/-- C,1 is unreachable: B reads 0 only at or beyond the right tape edge. -/
theorem c1_never_reached (k : Nat) :
    (run sweeper (initConfig 6) k).state ≠ some stC ∨
    (run sweeper (initConfig 6) k).head = false := by
  sorry

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
