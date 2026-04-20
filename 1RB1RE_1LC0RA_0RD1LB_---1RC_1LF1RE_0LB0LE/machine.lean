import BusyLean
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open BusyLean

namespace BMO1

/-!
# BMO1: 1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE

Beaver Math Olympiad #1 (BB(6) holdout, found by @-d on 25 Jun 2024).

## Transition table

       0     1
  A   1RB   1RE
  B   1LC   0RA
  C   0RD   1LB
  D   ---   1RC
  E   1LF   1RE
  F   0LB   0LE

## Macro configuration (wiki form)

  A(α, β) := 0^∞ (10)^(α-1) 0 1^β E> 0^∞    (α ≥ 1, β ≥ 1)

With the BusyLean `Config` convention (`left` is the tape left of head, reversed,
`head` the cell under the head, `right` the tape right of head), this is:

  left  := ones β ++ [false] ++ zebra (α-1)
  head  := false       (E scanning right on 0^∞)
  right := zeros p     (padding of p zeros, with 0^∞ implicit beyond)

## Macro rules (to be proven)

  A(α, β) → A(α - β, 4β + 2)      if α > β    (step count 6β² + 11β + 10)
  A(α, β) → A(2α + 1, β - α)      if α < β    (step count 2α² + 4αβ + 3α + 4)
  A(α, β) → Halt                  if α = β    (step count 6α² + 3α + 3)

Start: the blank tape reaches A(1, 2) in 10 steps.

## Verification status (via Python simulator `sim.py`)

All three rules verified on representative cases:
  a>b:  A(2,1)→A(1,6), A(5,2)→A(3,10), A(20,7)→A(13,30), A(50,3)→A(47,14), ...
  a<b:  A(1,2)→A(3,1), A(2,5)→A(5,3), A(5,13)→A(11,8), A(3,50)→A(7,47), ...
  a=b:  A(1,1), A(2,2), ..., A(10,10) all halt.
Step counts match the closed forms above to within observed range (100+ cases).
-/

-- The BMO1 TM
def bmo1 : TM 6 := tm! "1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE"

-- Transition shortcuts (evaluate `bmo1.tr` without unfolding the TM literal).
@[simp] private theorem tr_A0 : bmo1.tr stA false = some (stB, true, Dir.R) := rfl
@[simp] private theorem tr_A1 : bmo1.tr stA true  = some (stE, true, Dir.R) := rfl
@[simp] private theorem tr_B0 : bmo1.tr stB false = some (stC, true, Dir.L) := rfl
@[simp] private theorem tr_B1 : bmo1.tr stB true  = some (stA, false, Dir.R) := rfl
@[simp] private theorem tr_C0 : bmo1.tr stC false = some (stD, false, Dir.R) := rfl
@[simp] private theorem tr_C1 : bmo1.tr stC true  = some (stB, true, Dir.L) := rfl
@[simp] private theorem tr_D0 : bmo1.tr stD false = none := rfl
@[simp] private theorem tr_D1 : bmo1.tr stD true  = some (stC, true, Dir.R) := rfl
@[simp] private theorem tr_E0 : bmo1.tr stE false = some (stF, true, Dir.L) := rfl
@[simp] private theorem tr_E1 : bmo1.tr stE true  = some (stE, true, Dir.R) := rfl
@[simp] private theorem tr_F0 : bmo1.tr stF false = some (stB, false, Dir.L) := rfl
@[simp] private theorem tr_F1 : bmo1.tr stF true  = some (stE, false, Dir.L) := rfl

-- ============================================================
-- Mathematical model
-- ============================================================

/-- Abstract state: A(α, β) with α, β ≥ 1, or Halt. -/
inductive MathState where
  | A : Nat → Nat → MathState   -- A α β, stores α and β
  | Halt : MathState
deriving Repr, DecidableEq

/-- One-step transition on the abstract state. α, β ≥ 1 is assumed by callers;
    cases where one or both is 0 are mapped to `Halt` for totality. -/
def nextMathState : MathState → MathState
  | .Halt => .Halt
  | .A α β =>
    if α = 0 ∨ β = 0 then .Halt
    else if α = β then .Halt
    else if α > β then .A (α - β) (4 * β + 2)
    else .A (2 * α + 1) (β - α)

/-- k-fold iteration. -/
def iterMathState : MathState → Nat → MathState
  | s, 0 => s
  | s, k + 1 => iterMathState (nextMathState s) k

-- ============================================================
-- Macro configuration
-- ============================================================

/-- The A(α, β) macro configuration with right padding `p` and left padding `q`.

    State E, head on 0, left tape (reversed) = ones β ++ [false] ++ zebra (α-1)
    ++ zeros q (the `zeros q` accommodates the TM's finite-representation history
    — cells known to be 0 but explicitly written).  Requires α ≥ 1 and β ≥ 1;
    we encode this by taking `(a b : Nat)` with α = a + 1 and β = b + 1.
-/
def A_Config (a b p q : Nat) : Config 6 :=
  { state := some stE,
    head := false,
    left := ones (b + 1) ++ [false] ++ zebra a ++ zeros q,
    right := zeros p }

/-- Stream-based A(α, β) macro configuration (infinite tape, no padding).
    Rule lemmas are stated on this form to eliminate `(p, q)` bookkeeping;
    `A_Config a b p q` maps onto this via `A_Config_toSConfig` below. -/
def SA_Config (a b : Nat) : SConfig 6 :=
  { state := some stE,
    head := false,
    left := ones (b + 1) *> [false] *> zebra a *> blank∞,
    right := blank∞ }

/-- Bridge: any `A_Config a b p q` (with arbitrary paddings) lifts to the same
    `SA_Config a b` — the padding zeros are absorbed by the infinite blank tape. -/
lemma A_Config_toSConfig (a b p q : Nat) :
    (A_Config a b p q).toSConfig = SA_Config a b := by
  simp [A_Config, SA_Config, Config.toSConfig]

/-- Generalized Shawn form `E(a, b, c) = 0^∞ (10)^a 0 (10)^b 1^c E> 0^∞`.

Intermediate configurations during a rule-step trajectory lie in this
family even when they are **not** in the narrower `SA_Config` family; see
trace evidence in `TODO.md`.  We have `SA_Config a b = SE_Config a 0 (b+1)`. -/
def SE_Config (a b c : Nat) : SConfig 6 :=
  { state := some stE,
    head := false,
    left := ones c *> zebra b *> [false] *> zebra a *> blank∞,
    right := blank∞ }

/-- `SA_Config` is the `b = 0` slice of `SE_Config`. -/
lemma SA_Config_eq_SE (a b : Nat) : SA_Config a b = SE_Config a 0 (b + 1) := by
  simp [SA_Config, SE_Config]

-- ============================================================
-- Shift lemmas
-- ============================================================
-- Transition analysis (critical for macro steps):
--   E sweep right: E,1 → 1RE  (E devours a block of 1s moving right).
--   E turnaround:  E,0 → 1LF  (E hits the 0^∞ boundary, writes a 1, goes to F).
--   F retreat L:   F,1 → 0LE  (F erases a 1 moving left, returns to E).
--                  F,0 → 0LB  (F crosses a 0 going left, hands off to B).
--   B sweep left:  B,1 → 0RA  (B erases a 1 moving right → A).
--                  B,0 → 1LC  (B hits 0, writes 1, goes to C moving left).
--   C retreat:     C,1 → 1LB  (C moves left on 1, back to B).
--                  C,0 → 0RD  (C crosses 0 right, to D).
--   D sweep right: D,1 → 1RC  (D moves right on 1, to C).
--                  D,0 → HALT ← the only halting transition.
--   A right step:  A,0 → 1RB  |  A,1 → 1RE.

/-- State E moves right through a block of 1s. -/
lemma E_right_shift (k : Nat) (L R : List Sym) :
    run bmo1 { state := some stE, head := true, left := L, right := ones k ++ R } (k + 1) =
    { state := some stE, head := listHead R false, left := ones (k + 1) ++ L,
      right := listTail R } := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih => tm_ind_succ ih stE [bmo1]

/-- **D-C sweep**: state D at a 1, followed by `zebra k = (01)^k`, advances right
by 2k cells returning to state D at the 1 at the end of the zebra. -/
lemma DC_shift (k : Nat) (L R : List Sym) :
    run bmo1 { state := some stD, head := true, left := L, right := zebra k ++ R }
        (2 * k) =
    { state := some stD, head := true, left := zebra k ++ L, right := R } := by
  induction k generalizing L with
  | zero => rfl
  | succ k' ih =>
    rw [show 2 * (k' + 1) = 2 + 2 * k' from by ring, run_add]
    simp only [zebra_succ, List.cons_append]
    -- Perform the two concrete steps D,1 → 1RC then C,0 → 0RD.
    conv_lhs =>
      rw [show (2 : Nat) = 1 + 1 from rfl, run_add]
      simp only [run, step, tr_D1, tr_C0, listHead, listTail]
    -- Goal: run bmo1 ⟨D, false :: true :: L, true, zebra k' ++ R⟩ (2 * k') =
    --       ⟨D, false :: true :: (zebra k' ++ L), true, R⟩
    have := ih (false :: true :: L)
    convert this using 2
    show false :: true :: (zebra k' ++ L) = zebra k' ++ false :: true :: L
    rw [show (false :: true :: (zebra k' ++ L) : List Sym) = zebra 1 ++ (zebra k' ++ L) from rfl,
        show (false :: true :: L : List Sym) = zebra 1 ++ L from rfl,
        ← List.append_assoc, ← List.append_assoc, zebra_append, zebra_append, Nat.add_comm]

-- ============================================================
-- Initial configuration
-- ============================================================

/-- From the blank tape, BMO1 reaches A(1, 2) in 10 steps.  The left tape after
    these 10 steps ends in an extra explicit 0 (one cell that was visited and
    left as 0), captured by `q = 1` in the A_Config padding. -/
lemma init_to_A12 : run bmo1 (initConfig 6) 10 = A_Config 0 1 0 1 := by decide

-- ============================================================
-- Macro step lemmas (stream version)
-- ============================================================
--
-- Rules are stated on `SA_Config` (infinite tape) to eliminate padding
-- bookkeeping.  Base cases are proven by lifting their `A_Config`
-- counterparts (Config side with concrete padding) through `decide` +
-- `A_Config_toSConfig` + `toSConfig_run`.

-- ============================================================
-- Pass-shift: the key induction step for all three rules
-- ============================================================
-- Empirical finding (verified numerically on (a=0,b=0,c=1), (a=1,b=0,c=2),
-- (a=2,b=0,c=3), (a=0,b=2,c=1) via decide):
--
--   SE(a+1, b, c+1) → SE(a, b+2, c)   in   4*(b+c) + 9 steps.
--
-- One "pass" transfers one "(10)" from the left-10^a block into the
-- middle-10^b block, and one "1" from the right-1^c block into the
-- middle via the E/F ping-pong.  Iterating this pass `a+1` times from
-- SE(a+1, 0, a+2) starts of A(a+2, a+2) reaches SE(0, 2(a+1), a+1-a) =
-- SE(0, 2a+2, 1), the "pre-endgame" config.

/-- Config-side counterpart of `SE_Config` (with optional right padding).  Used
    to prove concrete `SE_Config` runs via `decide` + `toSConfig_run`. -/
def Config_for_SE (a b c q : Nat) : Config 6 :=
  { state := some stE, head := false,
    left := ones c ++ zebra b ++ [false] ++ zebra a ++ zeros q,
    right := [] }

lemma Config_for_SE_toSConfig (a b c q : Nat) :
    (Config_for_SE a b c q).toSConfig = SE_Config a b c := by
  simp [Config_for_SE, SE_Config, Config.toSConfig]

-- **Pass shift lemma**: one full pass of the outer loop.
-- Valid only when the output `c` slot is at least 1 (ensured by using `c+1`
-- in the output); if `c` slot drops to 0, the final state is `A`, not `E`.

-- Empirical check: pass_shift holds for a variety of (a, b, c).  Since the
-- step count `4(b+c)+13` does not depend on `a`, the extra zebra cells at
-- far-left (indexed by `a`) are untouched during the pass — a good `a`-
-- locality argument via `run_left_append` should reduce the claim to `a=0`.

/-- Intermediate SConfig: SE(a+1, b, c+2) initial but with right = [true] *> blank∞.
    Reached after exactly 3 steps of SE(a+1, b, c+3). -/
def SE_Bridge (a b c : Nat) : SConfig 6 :=
  { state := some stE, head := false,
    left := ones (c + 2) *> zebra b *> [false] *> zebra (a + 1) *> blank∞,
    right := [true] *> blank∞ }

/-- **Setup-3 lemma**: after 3 steps, SE(a+1, b, c+3) reaches SE_Bridge a b c.

The E/F/E cycle consumes the rightmost `true` of ones(c+3), producing the
intermediate with one extra `true` on right.  Proved entirely by `simp`. -/
lemma pass_shift_setup_3 (a b c : Nat) :
    srun bmo1 (SE_Config (a + 1) b (c + 3)) 3 = SE_Bridge a b c := by
  simp [SE_Config, SE_Bridge, srun, sstep, bmo1]

/-- Concrete base cases of `pass_shift` (proved by simp with generic `a`). -/
lemma pass_shift_base_b0_c0 (a : Nat) :
    srun bmo1 (SE_Config (a + 1) 0 2) 13 = SE_Config a 2 1 := by
  simp [SE_Config, srun, sstep, bmo1]

lemma pass_shift_base_b1_c0 (a : Nat) :
    srun bmo1 (SE_Config (a + 1) 1 2) 17 = SE_Config a 3 1 := by
  simp [SE_Config, srun, sstep, bmo1]

lemma pass_shift_base_b0_c1 (a : Nat) :
    srun bmo1 (SE_Config (a + 1) 0 3) 17 = SE_Config a 2 2 := by
  simp [SE_Config, srun, sstep, bmo1]

/-- **3-step E/F cycle** on `ones (c+2)`: consumes one `true` from the
    ones-block, appends one `true` to the right.  Fundamental c-recursion. -/
lemma ones_cycle3 (c : Nat) (rest R : Side) :
    srun bmo1 {state := some stE, left := ones (c + 2) *> rest, head := false, right := R} 3
    = {state := some stE, left := ones (c + 1) *> rest, head := false,
       right := Side.cons true R} := by
  simp [srun, sstep, bmo1]

/-- **5-step mixed cycle** for a zebra pair: from `ones 2 *> zebra (b+1) *> rest`,
    after 5 steps reach `ones 1 *> zebra b *> rest` with extra 3 cells on right.
    Handles one iteration of Phase A's zebra traversal. -/
lemma mixed_cycle5 (b : Nat) (rest R : Side) :
    srun bmo1 {state := some stE, left := ones 2 *> zebra (b + 1) *> rest,
               head := false, right := R} 5
    = {state := some stE, left := Side.cons true (zebra b *> rest),
       head := false,
       right := Side.cons false (Side.cons true (Side.cons true R))} := by
  simp [srun, sstep, bmo1]

/-- **2-step zebra cycle**: from state E, head=false, left = `[true] *> zebra (b+1) *> rest`,
    after 2 steps reach state E head=false with zebra decremented and `[false, true]`
    appended to right.  Fundamental b-recursion once we're in the `[true]` prefix regime. -/
lemma zebra_cycle2 (b : Nat) (rest R : Side) :
    srun bmo1 {state := some stE, left := Side.cons true (zebra (b + 1) *> rest),
               head := false, right := R} 2
    = {state := some stE, left := Side.cons true (zebra b *> rest),
       head := false, right := Side.cons false (Side.cons true R)} := by
  simp [srun, sstep, bmo1]

/-- **Iterated zebra cycle**: b iterations of `zebra_cycle2` take
    `[true] *> zebra (b+k) *> rest` to `[true] *> zebra k *> rest` in 2b steps. -/
lemma zebra_cycle2_iter (b k : Nat) (rest R : Side) :
    ∃ R', srun bmo1 {state := some stE,
                     left := Side.cons true (zebra (b + k) *> rest),
                     head := false, right := R} (2 * b)
          = {state := some stE, left := Side.cons true (zebra k *> rest),
             head := false, right := R'} := by
  induction b generalizing R with
  | zero => exact ⟨R, by simp⟩
  | succ b' ih =>
    have h : b' + 1 + k = (b' + k) + 1 := by omega
    rw [show 2 * (b' + 1) = 2 + 2 * b' from by ring, srun_add, h, zebra_cycle2]
    exact ih _

/-- **Phase C cycle**: state B, head=true, with `zebra 1 = [false, true] *> R` on
    right advances 2 cells right and stays at state B head=true.  Clean dual of
    `zebra_cycle2` for the AB-walk phase. -/
lemma BA_cycle2 (L R : Side) :
    srun bmo1 {state := some stB, left := L, head := true,
               right := Side.cons false (Side.cons true R)} 2
    = {state := some stB, left := Side.cons true (Side.cons false L), head := true,
       right := R} := by
  simp [srun, sstep, bmo1]

/-- **Iterated Phase C cycle**: k iterations of `BA_cycle2` consume `zebra k` from
    right, keeping state B head=true. -/
lemma BA_cycle2_iter (k : Nat) (L R : Side) :
    ∃ L', srun bmo1 {state := some stB, left := L, head := true,
                     right := zebra k *> R} (2 * k)
          = {state := some stB, left := L', head := true, right := R} := by
  induction k generalizing L with
  | zero => exact ⟨L, by simp⟩
  | succ k' ih =>
    have h2 : 2 * (k' + 1) = 2 + 2 * k' := by omega
    have hz : (zebra (k' + 1) *> R) = Side.cons false (Side.cons true (zebra k' *> R)) := rfl
    rw [h2, hz, srun_add, BA_cycle2]
    exact ih _

/-- **Generalized b=0 pass_shift**: with arbitrary right suffix `R`, the pass
    absorbs R's head and exposes R's tail.  Proved by induction on `c` using
    `ones_cycle3`. -/
lemma pass_shift_b0_gen (a c : Nat) (R : Side) :
    srun bmo1 { state := some stE,
                left := ones (c + 2) *> [false] *> zebra (a + 1) *> blank∞,
                head := false, right := R } (4 * c + 13)
    = { state := some stE,
        left := ones (c + 1) *> zebra 2 *> [false] *> zebra a *> blank∞,
        head := R.head, right := R.tail } := by
  induction c generalizing a R with
  | zero => simp [srun, sstep, bmo1]
  | succ c' ih =>
    have split : 4 * (c' + 1) + 13 = 3 + (4 * c' + 13) + 1 := by omega
    rw [show c' + 1 + 2 = (c' + 2) + 1 from by omega, split, srun_add, srun_add,
        show ones ((c' + 2) + 1) = ones ((c' + 1) + 2) from by
          rw [show (c' + 2) + 1 = (c' + 1) + 2 from by omega],
        ones_cycle3, ih a (Side.cons true R)]
    simp [srun, sstep, bmo1]

/-- **pass_shift at b=0**: the restricted b=0 slice of pass_shift, derived from
    `pass_shift_b0_gen` with `R = blank∞`. -/
lemma pass_shift_b0 (a c : Nat) :
    srun bmo1 (SE_Config (a + 1) 0 (c + 2)) (4 * c + 13) = SE_Config a 2 (c + 1) := by
  simp only [SE_Config]
  exact pass_shift_b0_gen a c Side.blank

-- ============================================================
-- Lemmas needed for b-induction of pass_shift_gen_c0.
-- ============================================================

/-- `rev_zebra n = (10)^n` — the reverse of `zebra n`.  Used for the accumulated
    left tape after Phase C's BA walk. -/
def rev_zebra : Nat → List Sym
  | 0 => []
  | n + 1 => true :: false :: rev_zebra n

@[simp] lemma rev_zebra_zero_simp : rev_zebra 0 = [] := rfl

lemma rev_zebra_succ_append (b : Nat) : rev_zebra (b + 1) = rev_zebra b ++ [true, false] := by
  induction b with
  | zero => rfl
  | succ k ih =>
    show rev_zebra (k + 2) = rev_zebra (k + 1) ++ [true, false]
    have h1 : rev_zebra (k + 2) = true :: false :: (rev_zebra k ++ [true, false]) := by
      show true :: false :: rev_zebra (k + 1) = true :: false :: (rev_zebra k ++ [true, false])
      rw [ih]
    have h2 : rev_zebra (k + 1) ++ [true, false] = true :: false :: (rev_zebra k ++ [true, false]) := rfl
    rw [h1, h2]

lemma ones1_zebra_false_eq_rev_zebra (n : Nat) :
    [true] ++ zebra n ++ [false] = rev_zebra (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show [true] ++ (false :: true :: zebra k) ++ [false] = rev_zebra (k + 2)
    show true :: false :: ([true] ++ zebra k ++ [false]) = true :: false :: rev_zebra (k + 1)
    rw [ih]

private lemma _full_left_list_eq (a b : Nat) :
    [true, false] ++ rev_zebra (b + 2) ++ [true, false] ++ zebra a =
    ones 1 ++ zebra (b + 3) ++ [false] ++ zebra a := by
  rw [show (ones 1 : List Sym) = [true] from rfl]
  congr 1
  rw [ones1_zebra_false_eq_rev_zebra (b + 3), rev_zebra_succ_append (b + 3)]
  congr 1

private lemma _right_pattern_eq (b : Nat) :
    [false, true] ++ (zebra b ++ [false, true, true]) = zebra (b + 2) ++ [true] := by
  rw [show ([false, true] ++ (zebra b ++ [false, true, true]) : List Sym) =
        ([false, true] ++ zebra b) ++ [false, true, true] from by rw [List.append_assoc]]
  rw [show ([false, true] ++ zebra b : List Sym) = zebra (b + 1) from rfl]
  rw [show ([false, true, true] : List Sym) = [false, true] ++ [true] from rfl,
      ← List.append_assoc, ← zebra_succ_append (b + 1)]

/-- 2-step cycle decrementing zebra in a specific intermediate state. -/
lemma zebra_cycle2_iter_explicit (b : Nat) (rest R : Side) :
    srun bmo1 {state := some stE,
               left := Side.cons true (zebra b *> rest),
               head := false, right := R} (2 * b)
    = {state := some stE, left := Side.cons true rest,
       head := false, right := zebra b *> R} := by
  induction b generalizing R with
  | zero => simp
  | succ b' ih =>
    rw [show 2 * (b' + 1) = 2 + 2 * b' from by omega, srun_add, zebra_cycle2 b', ih]
    congr 1
    show Side.prepend (zebra b') (Side.cons false (Side.cons true R)) =
         Side.prepend (zebra (b' + 1)) R
    rw [zebra_succ_append b']
    simp [Side.prepend_append]

/-- Iterated BA cycle — explicit left-tape accumulator. -/
lemma BA_cycle2_iter_explicit (k : Nat) (L R : Side) :
    srun bmo1 {state := some stB, left := L, head := true,
               right := zebra k *> R} (2 * k)
    = {state := some stB, left := rev_zebra k *> L, head := true, right := R} := by
  induction k generalizing L with
  | zero => simp
  | succ k' ih =>
    have hz : (zebra (k' + 1) *> R) = Side.cons false (Side.cons true (zebra k' *> R)) := rfl
    rw [show 2 * (k' + 1) = 2 + 2 * k' from by omega, hz, srun_add, BA_cycle2, ih]
    congr 1
    show Side.prepend (rev_zebra k') (Side.cons true (Side.cons false L)) =
         Side.prepend (rev_zebra (k' + 1)) L
    rw [rev_zebra_succ_append k']
    simp [Side.prepend_append]

-- ============================================================
-- Shared infrastructure for gt/lt endgames
-- ============================================================

/-- Iterated 3-step E/F cycle on a ones-block: reduces `ones (j+k+1)` to `ones (j+1)`
    in `3k` steps, pushing `ones k` onto the right tape.  Dual to
    `zebra_cycle2_iter_explicit` but for the β-block.  The `j` parameter preserves
    a baseline of ones; instantiate `j = 0` for the standard "reduce to ones 1" usage. -/
lemma ones_cycle3_iter_explicit (k j : Nat) (rest R : Side) :
    srun bmo1 {state := some stE,
               left := ones (j + k + 1) *> rest,
               head := false, right := R} (3 * k)
    = {state := some stE,
       left := ones (j + 1) *> rest,
       head := false, right := ones k *> R} := by
  induction k generalizing j R with
  | zero => simp
  | succ k' ih =>
    have hsteps : 3 * (k' + 1) = 3 + 3 * k' := by ring
    have hleft : j + (k' + 1) + 1 = (j + k') + 2 := by omega
    rw [hsteps, hleft, srun_add, ones_cycle3, ih j (Side.cons true R)]
    -- right is now ones k' *> [true] *> R; need ones (k'+1) *> R.
    congr 1
    show Side.prepend (ones k') (Side.cons true R) = Side.prepend (ones (k' + 1)) R
    show Side.prepend (ones k') (Side.prepend [true] R) = Side.prepend (ones (k' + 1)) R
    rw [← Side.prepend_append]
    congr 1
    show ones k' ++ ones 1 = ones (k' + 1)
    rw [ones_append]

/-- Phase 4 preamble (4 steps): from `state B, head=true, right=blank∞`, the
    machine writes two trues on the right and returns to `state B, head=false`.
    The left tape is preserved. -/
lemma gt_phase4_preamble (rest : Side) :
    srun bmo1 {state := some stB, head := true, left := rest, right := blank∞} 4
    = {state := some stB, head := false, left := rest,
       right := ones 2 *> blank∞} := by
  simp [srun, sstep, bmo1]

/-- Phase 4 cycle (2 steps): consumes one `[true, false]` pair from the left
    (state B head=false, via B,0→1LC then C,1→1LB), appending two `true`s to the
    right.  Fundamental cycle for absorbing `rev_zebra`. -/
lemma gt_phase4_cycle (rest R : Side) :
    srun bmo1 {state := some stB, head := false,
               left := Side.cons true (Side.cons false rest), right := R} 2
    = {state := some stB, head := false, left := rest,
       right := ones 2 *> R} := by
  simp [srun, sstep, bmo1]

/-- Iterated Phase 4 cycle: `m` iterations of `gt_phase4_cycle` consume
    `rev_zebra m` entirely, accumulating `ones (2m)` on the right. -/
lemma gt_phase4_cycle_iter (m : Nat) (rest R : Side) :
    srun bmo1 {state := some stB, head := false,
               left := rev_zebra m *> rest, right := R} (2 * m)
    = {state := some stB, head := false, left := rest,
       right := ones (2 * m) *> R} := by
  induction m generalizing R with
  | zero => simp
  | succ m' ih =>
    have hsteps : 2 * (m' + 1) = 2 + 2 * m' := by ring
    have hleft : (rev_zebra (m' + 1) *> rest : Side) =
                 Side.cons true (Side.cons false (rev_zebra m' *> rest)) := rfl
    rw [hsteps, hleft, srun_add, gt_phase4_cycle, ih]
    congr 1
    show Side.prepend (ones (2 * m')) (Side.prepend (ones 2) R) =
         Side.prepend (ones (2 + 2 * m')) R
    rw [← Side.prepend_append, ones_append, show 2 * m' + 2 = 2 + 2 * m' from by ring]

/-- **Phase 4 absorb**: from `state B, head=true, left=rev_zebra m *> rest, right=blank∞`,
    in `2m+4` steps the machine reaches `state B, head=false, left=rest,
    right=ones(2m+2) *> blank∞`.  Combines `gt_phase4_preamble` with
    `gt_phase4_cycle_iter`. -/
lemma gt_phase4_absorb (m : Nat) (rest : Side) :
    srun bmo1 {state := some stB, head := true,
               left := rev_zebra m *> rest, right := blank∞} (2 * m + 4)
    = {state := some stB, head := false, left := rest,
       right := ones (2 * m + 2) *> blank∞} := by
  have hsteps : 2 * m + 4 = 4 + 2 * m := by ring
  rw [hsteps, srun_add, gt_phase4_preamble, gt_phase4_cycle_iter]
  congr 1
  -- ones (2m) *> ones 2 *> blank = ones (2m+2) *> blank
  show Side.prepend (ones (2 * m)) (Side.prepend (ones 2) Side.blank) =
       Side.prepend (ones (2 * m + 2)) Side.blank
  rw [← Side.prepend_append, ones_append]

/-- SConfig-side DC_shift (analog of Config-side `DC_shift` for use within
    eq_endgame and lt_endgame). -/
lemma sDC_shift (k : Nat) (L R : Side) :
    srun bmo1 {state := some stD, left := L, head := true, right := zebra k *> R} (2 * k)
    = {state := some stD, left := zebra k *> L, head := true, right := R} := by
  induction k generalizing L with
  | zero => simp
  | succ k' ih =>
    have hz : (zebra (k' + 1) *> R) = Side.cons false (Side.cons true (zebra k' *> R)) := rfl
    have step2 :
        srun bmo1 {state := some stD, left := L, head := true,
                   right := Side.cons false (Side.cons true (zebra k' *> R))} 2
        = {state := some stD, left := Side.cons false (Side.cons true L), head := true,
           right := zebra k' *> R} := by
      simp [srun, sstep, bmo1]
    rw [show 2 * (k' + 1) = 2 + 2 * k' from by omega, hz, srun_add, step2, ih]
    congr 1
    show Side.prepend (zebra k') (Side.cons false (Side.cons true L)) =
         Side.prepend (zebra (k' + 1)) L
    rw [zebra_succ_append k']
    simp [Side.prepend_append]

/-- Phase 1 of pass_shift_gen_c0: first 5 steps convert the input SE shape
    into a `[true]`-prefix intermediate. -/
lemma pass_c0_phase1 (a b : Nat) (R : Side) :
    srun bmo1 {state := some stE,
               left := ones 2 *> zebra (b + 1) *> [false] *> zebra (a + 1) *> blank∞,
               head := false, right := R} 5
    = {state := some stE,
       left := Side.cons true (zebra b *> [false] *> zebra (a + 1) *> blank∞),
       head := false,
       right := Side.cons false (Side.cons true (Side.cons true R))} := by
  simp [srun, sstep, bmo1]

/-- Phase 3: 6 concrete steps crossing the `[false]` separator and reaching
    the AB walk in the zebra-(a+1) region. -/
lemma pass_c0_phase3 (a : Nat) (R' : Side) :
    srun bmo1 {state := some stE,
               left := Side.cons true ([false] *> zebra (a + 1) *> blank∞),
               head := false, right := R'} 6
    = {state := some stB,
       left := Side.cons true (Side.cons false (zebra a *> blank∞)),
       head := true,
       right := Side.cons false (Side.cons true R')} := by
  simp [srun, sstep, bmo1]

/-- Phase 5: 2 final concrete steps from the BA walk exit to the final SE form. -/
lemma pass_c0_phase5 (L R : Side) :
    srun bmo1 {state := some stB, left := L, head := true,
               right := Side.cons true R} 2
    = {state := some stE, left := Side.cons true (Side.cons false L),
       head := R.head, right := R.tail} := by
  simp [srun, sstep, bmo1]

/-- Base case `b=0` of pass_shift_gen_c0: no zebra in the middle, only ones.
    Follows directly from `pass_shift_b0_gen` (via `zebra 0 = []`). -/
private lemma pass_shift_gen_c0_zero (a : Nat) (R : Side) :
    srun bmo1 {state := some stE,
               left := ones 2 *> zebra 0 *> [false] *> zebra (a + 1) *> blank∞,
               head := false, right := R} 13
    = {state := some stE,
       left := ones 1 *> zebra 2 *> [false] *> zebra a *> blank∞,
       head := R.head, right := R.tail} := by
  simp [srun, sstep, bmo1]

/-- Inductive case `b + 1` of pass_shift_gen_c0: composes all 5 phases. -/
lemma pass_shift_gen_c0_succ (a b : Nat) (R : Side) :
    srun bmo1 {state := some stE,
               left := ones 2 *> zebra (b + 1) *> [false] *> zebra (a + 1) *> blank∞,
               head := false, right := R} (4 * (b + 1) + 13)
    = {state := some stE,
       left := ones 1 *> zebra (b + 3) *> [false] *> zebra a *> blank∞,
       head := R.head, right := R.tail} := by
  have hsum : 4 * (b + 1) + 13 = 5 + (2 * b + (6 + (2 * (b + 2) + 2))) := by ring
  rw [hsum, srun_add, pass_c0_phase1, srun_add, zebra_cycle2_iter_explicit,
      srun_add, pass_c0_phase3, srun_add]
  have right_eq : Side.cons false (Side.cons true (Side.prepend (zebra b)
                    (Side.cons false (Side.cons true (Side.cons true R)))))
                = Side.prepend (zebra (b + 2)) (Side.cons true R) := by
    rw [show Side.prepend (zebra b) (Side.cons false (Side.cons true (Side.cons true R))) =
           Side.prepend (zebra b ++ [false, true, true]) R from by rw [Side.prepend_append]; rfl]
    show Side.prepend [false, true] (Side.prepend (zebra b ++ [false, true, true]) R) =
         Side.prepend (zebra (b + 2)) (Side.cons true R)
    rw [← Side.prepend_append, show Side.prepend (zebra (b + 2)) (Side.cons true R) =
         Side.prepend (zebra (b + 2) ++ [true]) R from by rw [Side.prepend_append]; rfl]
    congr 1
    exact _right_pattern_eq b
  rw [right_eq, BA_cycle2_iter_explicit, pass_c0_phase5]
  congr 1
  show Side.cons true (Side.cons false (Side.prepend (rev_zebra (b + 2))
         (Side.cons true (Side.cons false (Side.prepend (zebra a) Side.blank)))))
     = Side.prepend (ones 1) (Side.prepend (zebra (b + 3)) (Side.prepend [false]
         (Side.prepend (zebra a) Side.blank)))
  show Side.prepend [true, false] (Side.prepend (rev_zebra (b + 2))
         (Side.prepend [true, false] (Side.prepend (zebra a) Side.blank)))
     = Side.prepend (ones 1) (Side.prepend (zebra (b + 3)) (Side.prepend [false]
         (Side.prepend (zebra a) Side.blank)))
  rw [← Side.prepend_append, ← Side.prepend_append, ← Side.prepend_append,
      ← Side.prepend_append, ← Side.prepend_append, ← Side.prepend_append]
  congr 1
  exact _full_left_list_eq a b

/-- **pass_shift_gen_c0** — full proof by b-induction, composing all 5 phase lemmas. -/
lemma pass_shift_gen_c0 (a b : Nat) (R : Side) :
    srun bmo1 { state := some stE,
                left := ones 2 *> zebra b *> [false] *> zebra (a + 1) *> blank∞,
                head := false, right := R } (4 * b + 13)
    = { state := some stE,
        left := ones 1 *> zebra (b + 2) *> [false] *> zebra a *> blank∞,
        head := R.head, right := R.tail } := by
  cases b with
  | zero => exact pass_shift_gen_c0_zero a R
  | succ b' => exact pass_shift_gen_c0_succ a b' R

/-- **pass_shift_gen** — the generalized pass_shift with arbitrary right suffix R.
    Proved by induction on c using `ones_cycle3`, reducing to `pass_shift_gen_c0`
    (which remains sorried for generic b). -/
lemma pass_shift_gen (a b c : Nat) (R : Side) :
    srun bmo1 { state := some stE,
                left := ones (c + 2) *> zebra b *> [false] *> zebra (a + 1) *> blank∞,
                head := false, right := R } (4 * (b + c) + 13)
    = { state := some stE,
        left := ones (c + 1) *> zebra (b + 2) *> [false] *> zebra a *> blank∞,
        head := R.head, right := R.tail } := by
  induction c generalizing a b R with
  | zero => exact pass_shift_gen_c0 a b R
  | succ c' ih =>
    have split : 4 * (b + (c' + 1)) + 13 = 3 + (4 * (b + c') + 13) + 1 := by omega
    rw [show c' + 1 + 2 = (c' + 2) + 1 from by omega, split, srun_add, srun_add,
        show ones ((c' + 2) + 1) = ones ((c' + 1) + 2) from by
          rw [show (c' + 2) + 1 = (c' + 1) + 2 from by omega],
        ones_cycle3, ih a b (Side.cons true R)]
    simp [srun, sstep, bmo1]

/-- **Pass shift lemma** — derived directly from `pass_shift_gen` with R = blank∞. -/
lemma pass_shift (a b c : Nat) :
    srun bmo1 (SE_Config (a + 1) b (c + 2)) (4 * (b + c) + 13) =
    SE_Config a (b + 2) (c + 1) := by
  simp only [SE_Config]
  exact pass_shift_gen a b c Side.blank

/-- Iterated pass: `k` passes from SE(a+k, b, c+1+k) reach SE(a, b+2k, c+1).

Output `c+1 ≥ 1` ensures each inner `pass_shift` is applied in the valid regime.
Step count: `4k(b+c) + 6k² + 7k`. -/
lemma passes_shift (k a b c : Nat) :
    srun bmo1 (SE_Config (a + k) b ((c + 1) + k))
        (4 * k * (b + c) + 6 * k^2 + 7 * k) =
    SE_Config a (b + 2 * k) (c + 1) := by
  induction k generalizing a b c with
  | zero => simp
  | succ k' ih =>
    have step_sum :
        4 * (k' + 1) * (b + c) + 6 * (k' + 1)^2 + 7 * (k' + 1) =
        (4 * (b + (c + k')) + 13) +
          (4 * k' * ((b + 2) + c) + 6 * k'^2 + 7 * k') := by ring
    rw [step_sum, srun_add,
        show SE_Config (a + (k' + 1)) b ((c + 1) + (k' + 1)) =
             SE_Config ((a + k') + 1) b ((c + k') + 2) from by
          simp only [show a + (k' + 1) = (a + k') + 1 from by omega,
                     show (c + 1) + (k' + 1) = (c + k') + 2 from by omega],
        pass_shift (a + k') b (c + k')]
    have hhyp := ih a (b + 2) c
    have e1 : b + 2 * (k' + 1) = b + 2 + 2 * k' := by omega
    have e2 : c + k' + 1 = c + 1 + k' := by omega
    simp only [e1, e2]
    -- but LHS in hhyp has `c + 1 + k'` already; convert the rest.
    exact hhyp

-- **Rule a>b**: A(α, β) → A(α - β, 4β + 2) in 6β² + 11β + 10 steps, when α > β.
-- Stream form: no padding parameters, clean statement.
-- Verified by simulator on A(2,1), A(3,1), A(5,2), A(7,3), A(10,4), A(20,7),
-- A(50,3), A(100,1)..A(100,8).  Step count matches 6b² + 11b + 10 exactly.

/-- Base case `b=0, k=0` of `stm_rule_gt`: A(2,1) → A(1,6) in 27 steps. -/
lemma stm_rule_gt_base : srun bmo1 (SA_Config 1 0) 27 = SA_Config 0 5 := by
  rw [show SA_Config 1 0 = (A_Config 1 0 2 0).toSConfig from
      (A_Config_toSConfig 1 0 2 0).symm,
    ← toSConfig_run,
    show run bmo1 (A_Config 1 0 2 0) 27 = A_Config 0 5 0 1 from by decide]
  exact A_Config_toSConfig 0 5 0 1

-- gt-endgame: from SE(k+1, 2b, 1) the machine reaches SA_Config k (4b+5)
-- in 16b + 27 steps.  Handles the final α-structure consumption AND the
-- middle zebra unfolding into 4β+2 trailing ones.

/-- Base case `k = 0, b = 0` of `gt_endgame`: equivalent to `stm_rule_gt_base`. -/
lemma gt_endgame_zero : srun bmo1 (SE_Config 1 0 1) 27 = SA_Config 0 5 := by
  rw [show SE_Config 1 0 1 = SA_Config 1 0 from (SA_Config_eq_SE 1 0).symm]
  exact stm_rule_gt_base

/-- Phase A-gt-2: 4 concrete steps crossing the `[false]` separator into `zebra (k+1)`.
    Consumes one `(01)` pair from `zebra (k+1)`, yielding state B head=true with the
    consumed pair deposited as two cells on the right (+`zebra 1 = [false, true]` from
    step 2 write + `[false, true]` from step 4 write = `zebra 2`). -/
private lemma gt_phase_A2 (k : Nat) (R : Side) :
    srun bmo1 {state := some stE, head := false,
               left := Side.cons true ([false] *> zebra (k + 1) *> blank∞),
               right := R} 4
    = {state := some stB, head := true, left := zebra k *> blank∞,
       right := zebra 2 *> R} := by
  simp [srun, sstep, bmo1]

/-- E sweeps right through a ones-block ending at blank: in `p+1` steps, consume
    `ones p *> blank∞` from right, append `ones (p+1)` to left, switch to head=false. -/
lemma sE_sweep_ones (p : Nat) (L : Side) :
    srun bmo1 {state := some stE, head := true, left := L,
               right := ones p *> blank∞} (p + 1)
    = {state := some stE, head := false, left := ones (p + 1) *> L,
       right := blank∞} := by
  induction p generalizing L with
  | zero => simp [srun, sstep, bmo1]
  | succ p' ih =>
    have hsum : p' + 1 + 1 = 1 + (p' + 1) := by omega
    have step1 : srun bmo1 {state := some stE, head := true, left := L,
                            right := ones (p' + 1) *> blank∞} 1
                 = {state := some stE, head := true, left := Side.cons true L,
                    right := ones p' *> blank∞} := by
      simp [srun, sstep, bmo1]
    rw [hsum, srun_add, step1, ih]
    congr 1
    show Side.prepend (ones (p' + 1)) (Side.cons true L) =
         Side.prepend (ones (1 + (p' + 1))) L
    show Side.prepend (ones (p' + 1)) (Side.prepend [true] L) =
         Side.prepend (ones (1 + (p' + 1))) L
    rw [← Side.prepend_append]
    congr 1
    show ones (p' + 1) ++ ones 1 = ones (1 + (p' + 1))
    rw [ones_append, show (p' + 1) + 1 = 1 + (p' + 1) from by omega]

/-- Phase 5 preamble for gt_endgame: 6 concrete steps from post-Phase-4 state.
    Left has form `zebra k *> blank∞`; dynamics consume 2 ones from right. -/
private lemma gt_phase5_preamble (k b : Nat) :
    srun bmo1 {state := some stB, head := false, left := zebra k *> blank∞,
               right := ones (4 * b + 6) *> blank∞} 6
    = {state := some stE, head := true,
       left := Side.cons true (Side.cons false (Side.cons false
                (zebra k *> blank∞).tail)),
       right := ones (4 * b + 4) *> blank∞} := by
  -- Unfold ones (4b+6) = ones 2 *> ones (4b+4) so simp can see the head cells.
  have hones : (ones (4 * b + 6) *> blank∞ : Side) =
               Side.cons true (Side.cons true (ones (4 * b + 4) *> blank∞)) := by
    show Side.prepend (ones (4 * b + 6)) Side.blank =
         Side.prepend (ones 2) (Side.prepend (ones (4 * b + 4)) Side.blank)
    rw [← Side.prepend_append, ones_append]
    congr 2; omega
  rw [hones]
  cases k with
  | zero => simp [srun, sstep, bmo1]
  | succ k' => simp [srun, sstep, bmo1]

/-- Phase 5 left-tape identity: after the preamble and sweep, the left tape form
    simplifies to the SA_Config left tape. -/
private lemma gt_phase5_left_eq (k b : Nat) :
    Side.prepend (ones (4 * b + 4 + 1))
      (Side.cons true (Side.cons false (Side.cons false
        (Side.tail (Side.prepend (zebra k) Side.blank)))))
    = Side.prepend (ones (4 * b + 5 + 1))
        (Side.prepend [false] (Side.prepend (zebra k) Side.blank)) := by
  -- LHS: ones(4b+5) *> [true] *> [false, false] *> (zebra k *> blank).tail
  --    = ones(4b+5+1) *> [false] *> [false] *> (zebra k *> blank).tail        (fold true into ones)
  --    = ones(4b+5+1) *> [false] *> cons false (zebra k *> blank).tail
  --    = ones(4b+5+1) *> [false] *> (zebra k *> blank)                        (by key identity)
  have hfold : Side.prepend (ones (4 * b + 4 + 1))
                 (Side.cons true (Side.cons false (Side.cons false
                   (Side.tail (Side.prepend (zebra k) Side.blank)))))
             = Side.prepend (ones (4 * b + 5 + 1))
                 (Side.cons false (Side.cons false
                   (Side.tail (Side.prepend (zebra k) Side.blank)))) := by
    rw [show (Side.cons true (Side.cons false (Side.cons false
              (Side.tail (Side.prepend (zebra k) Side.blank))))
            : Side)
         = Side.prepend [true] (Side.cons false (Side.cons false
              (Side.tail (Side.prepend (zebra k) Side.blank)))) from rfl,
        ← Side.prepend_append,
        show ones (4 * b + 4 + 1) ++ [true] = ones (4 * b + 5 + 1) from by
          rw [show ([true] : List Sym) = ones 1 from rfl, ones_append]]
  rw [hfold]
  congr 1
  -- Goal: cons false (cons false (tail (zebra k *> blank))) = [false] *> zebra k *> blank
  --     = cons false (zebra k *> blank)
  -- So need: cons false (tail (zebra k *> blank)) = zebra k *> blank.
  show Side.cons false (Side.cons false (Side.tail (Side.prepend (zebra k) Side.blank)))
     = Side.cons false (Side.prepend (zebra k) Side.blank)
  congr 1
  exact Side.cons_false_zebra_blank_tail k

/-- Phase 5 for gt_endgame: `4b+11` steps from post-Phase-4 state to SA_Config k (4b+5). -/
private lemma gt_phase5 (k b : Nat) :
    srun bmo1 {state := some stB, head := false, left := zebra k *> blank∞,
               right := ones (4 * b + 6) *> blank∞} (4 * b + 11)
    = SA_Config k (4 * b + 5) := by
  have hsum : 4 * b + 11 = 6 + (4 * b + 4 + 1) := by ring
  rw [hsum, srun_add, gt_phase5_preamble, sE_sweep_ones]
  -- Now goal: LHS = SA_Config k (4b+5).
  simp only [SA_Config]
  -- Goal: two SConfig records equal. Fields state, head, right match; only left differs.
  congr 1
  exact gt_phase5_left_eq k b

/-- **gt-endgame**: full proof via 5-phase composition. -/
lemma gt_endgame (k b : Nat) :
    srun bmo1 (SE_Config (k + 1) (2 * b) 1) (16 * b + 27) = SA_Config k (4 * b + 5) := by
  simp only [SE_Config]
  -- Goal: srun bmo1 {E, head=false, left=ones 1 *> zebra(2b) *> [false] *> zebra(k+1) *> blank,
  --                  right=blank} (16b+27) = SA_Config k (4b+5).
  -- Normalize ones 1 = [true], and refold the left tape.
  have hleft : (Side.prepend (ones 1) (Side.prepend (zebra (2 * b))
                 (Side.prepend [false] (Side.prepend (zebra (k + 1)) Side.blank))))
             = Side.cons true (Side.prepend (zebra (2 * b))
                 (Side.prepend [false] (Side.prepend (zebra (k + 1)) Side.blank))) := rfl
  rw [hleft]
  -- Step budget: 16b+27 = (4b) + (4 + ((4b+4) + ((4b+8) + (4b+11))))
  have hsum : 16 * b + 27 = 2*(2*b) + (4 + (2*(2*b+2) + ((2*(2*b+2) + 4) + (4*b+11)))) := by
    ring
  rw [hsum, srun_add]
  -- Apply Phase A-gt-1: zebra_cycle2_iter_explicit with b' = 2b.
  rw [zebra_cycle2_iter_explicit (2 * b) _ _]
  -- After Phase A-gt-1: left = cons true ([false] *> zebra(k+1) *> blank),
  --                     right = zebra(2b) *> blank.
  rw [srun_add]
  -- Apply Phase A-gt-2.
  rw [gt_phase_A2 k _]
  -- After Phase A-gt-2: {B, head=true, left=zebra k *> blank,
  --                       right=zebra 2 *> zebra (2b) *> blank}.
  -- Fold zebra 2 *> zebra (2b) = zebra (2b+2).
  rw [show Side.prepend (zebra 2) (Side.prepend (zebra (2 * b)) Side.blank)
         = Side.prepend (zebra (2 * b + 2)) Side.blank from by
        rw [← Side.prepend_append, zebra_append,
            show (2 + 2 * b : Nat) = 2 * b + 2 from by ring]]
  rw [srun_add]
  -- Apply Phase BA-gt: BA_cycle2_iter_explicit with k = 2b+2.
  rw [BA_cycle2_iter_explicit (2 * b + 2) _ _]
  rw [srun_add]
  -- Apply Phase 4: gt_phase4_absorb with m = 2b+2.
  rw [gt_phase4_absorb (2 * b + 2) _]
  -- Normalize right: ones(2*(2b+2)+2) = ones(4b+6).
  rw [show 2 * (2 * b + 2) + 2 = 4 * b + 6 from by ring]
  -- Apply Phase 5.
  exact gt_phase5 k b

/-- Rule gt on SConfig; `a = b + 1 + k`.

Compose `passes_shift b (k+1) 0 1` (6b²+7b steps, c_out=1 ≥ 1 so `pass_shift`
applies) with `gt_endgame k b` (16b+27 steps).  Total 6b²+23b+27. -/
theorem stm_rule_gt (b k : Nat) :
    srun bmo1 (SA_Config (b + 1 + k) b) (6 * b^2 + 23 * b + 27) =
    SA_Config k (4 * b + 5) := by
  have hpass := passes_shift b (k + 1) 0 0
  have hend := gt_endgame k b
  have hSA : SA_Config (b + 1 + k) b = SE_Config ((k + 1) + b) 0 ((0 + 1) + b) := by
    rw [SA_Config_eq_SE]; congr 1 <;> omega
  have hsplit :
      6 * b^2 + 23 * b + 27 = (4 * b * (0 + 0) + 6 * b^2 + 7 * b) + (16 * b + 27) := by ring
  rw [hSA, hsplit, srun_add, hpass]
  show srun bmo1 (SE_Config (k + 1) (0 + 2 * b) (0 + 1)) (16 * b + 27) = SA_Config k (4 * b + 5)
  have h1 : (0 + 2 * b) = 2 * b := by omega
  have h2 : (0 + 1 : Nat) = 1 := by omega
  rw [h1, h2]; exact hend

-- **Rule a<b**: A(α, β) → A(2α+1, β-α) in 2α²+4αβ+3α+4 steps, when α < β.
-- Verified on A(1,2), A(1,3), A(2,5), A(3,10), A(5,13), A(7,20), A(3,50),
-- A(a,100) for a∈{1..8}.

/-- Base case `a=0, k=0` of `stm_rule_lt`: A(1,2) → A(3,1) in 17 steps. -/
lemma stm_rule_lt_base : srun bmo1 (SA_Config 0 1) 17 = SA_Config 2 0 := by
  rw [show SA_Config 0 1 = (A_Config 0 1 2 0).toSConfig from
      (A_Config_toSConfig 0 1 2 0).symm,
    ← toSConfig_run,
    show run bmo1 (A_Config 0 1 2 0) 17 = A_Config 2 0 1 1 from by decide]
  exact A_Config_toSConfig 2 0 1 1

-- lt-endgame: from SE(0, 2a, k+2) the machine reaches SA_Config (2a+2) k
-- in 8a + 4k + 17 steps.  The 2a zebra middle is re-expanded into 2(a+1)
-- (10)-pairs of the new α-structure.

/-- Base case `a = 0, k = 0` of `lt_endgame`: equivalent to `stm_rule_lt_base`. -/
lemma lt_endgame_zero : srun bmo1 (SE_Config 0 0 2) 17 = SA_Config 2 0 := by
  rw [show SE_Config 0 0 2 = SA_Config 0 1 from (SA_Config_eq_SE 0 1).symm]
  exact stm_rule_lt_base

/-- Phase AB for lt_endgame: 6 concrete steps from post-Phase-A-lt-2 state.
    Crosses the `[false]` separator and reaches state D, head=true. -/
private lemma lt_phase_AB (R : Side) :
    srun bmo1 {state := some stE, head := false,
               left := Side.cons true (Side.prepend [false] Side.blank),
               right := R} 6
    = {state := some stD, head := true,
       left := Side.prepend [false] Side.blank,
       right := zebra 2 *> R} := by
  simp [srun, sstep, bmo1]

/-- State A consuming a ones-block on the right (via A,1→1RE then E-sweep). -/
lemma sA_consume_ones (k : Nat) (L : Side) :
    srun bmo1 {state := some stA, head := true, left := L,
               right := ones k *> blank∞} (k + 1)
    = {state := some stE, head := false, left := ones (k + 1) *> L,
       right := blank∞} := by
  cases k with
  | zero => simp [srun, sstep, bmo1]
  | succ k' =>
    have h : k' + 1 + 1 = 1 + (k' + 1) := by omega
    rw [h, srun_add]
    have step1 : srun bmo1 {state := some stA, head := true, left := L,
                            right := ones (k' + 1) *> blank∞} 1
               = {state := some stE, head := true, left := Side.cons true L,
                  right := ones k' *> blank∞} := by
      simp [srun, sstep, bmo1]
    rw [step1, sE_sweep_ones]
    congr 1
    show Side.prepend (ones (k' + 1)) (Side.prepend [true] L)
       = Side.prepend (ones (1 + (k' + 1))) L
    rw [← Side.prepend_append,
        show ones (k' + 1) ++ [true] = ones (1 + (k' + 1)) from by
          rw [show ([true] : List Sym) = ones 1 from rfl, ones_append,
              show k' + 1 + 1 = 1 + (k' + 1) from by omega]]

/-- Phase final for lt_endgame: from post-Phase-DC state, `k+4` steps reach SA_Config (2a+2) k. -/
private lemma lt_phase_final (a k : Nat) :
    srun bmo1 {state := some stD, head := true,
               left := zebra (2 * a + 2) *> Side.prepend [false] Side.blank,
               right := ones (k + 1) *> blank∞} (k + 4)
    = SA_Config (2 * a + 2) k := by
  have hsum : k + 4 = 3 + (k + 1) := by ring
  rw [hsum, srun_add]
  -- 3 concrete steps: D→C→B→A with head=true.
  have step3 : srun bmo1 {state := some stD, head := true,
                          left := zebra (2 * a + 2) *> Side.prepend [false] Side.blank,
                          right := ones (k + 1) *> blank∞} 3
             = {state := some stA, head := true,
                left := Side.cons false (zebra (2 * a + 2) *>
                          Side.prepend [false] Side.blank),
                right := ones k *> blank∞} := by
    simp [srun, sstep, bmo1]
  rw [step3]
  -- Apply sA_consume_ones.
  rw [sA_consume_ones]
  -- Now need: {E, head=false, left = ones (k+1) *> cons false (zebra(2a+2) *> [false] *> blank),
  --            right = blank} = SA_Config (2a+2) k.
  simp only [SA_Config]
  -- Goal: two SConfig records.  state, head, right match; left needs reduction.
  congr 1
  -- Goal: ones(k+1) *> cons false (zebra(2a+2) *> [false] *> blank)
  --     = ones(k+1) *> [false] *> zebra(2a+2) *> blank.
  -- Reduce: pop the ones (k+1) prefix and the outer false, then absorb trailing [false]*>blank.
  show Side.prepend (ones (k + 1)) (Side.cons false
          (Side.prepend (zebra (2 * a + 2)) (Side.prepend [false] Side.blank)))
     = Side.prepend (ones (k + 1)) (Side.prepend [false]
          (Side.prepend (zebra (2 * a + 2)) Side.blank))
  congr 1
  show Side.cons false (Side.prepend (zebra (2 * a + 2)) (Side.prepend [false] Side.blank))
     = Side.cons false (Side.prepend (zebra (2 * a + 2)) Side.blank)
  congr 2
  exact Side.cons_false_blank

/-- **lt-endgame**: full proof via 5-phase composition. -/
lemma lt_endgame (a k : Nat) :
    srun bmo1 (SE_Config 0 (2 * a) (k + 2)) (8 * a + 4 * k + 17) =
    SA_Config (2 * a + 2) k := by
  simp only [SE_Config]
  -- Goal: srun bmo1 {E, head=false, left=ones(k+2)*>zebra(2a)*>[false]*>zebra 0*>blank,
  --                  right=blank} (8a+4k+17) = SA_Config (2a+2) k.
  -- Normalize: zebra 0 *> blank = blank, so left = ones(k+2) *> zebra(2a) *> [false] *> blank.
  have hleft_in : (Side.prepend (ones (k + 2)) (Side.prepend (zebra (2 * a))
                    (Side.prepend [false] (Side.prepend (zebra 0) Side.blank))))
                = Side.prepend (ones (0 + (k + 1) + 1))
                    (Side.prepend (zebra (2 * a))
                      (Side.prepend [false] Side.blank)) := by
    simp [zebra_zero]
  rw [hleft_in]
  -- Step budget: 8a+4k+17 = 3(k+1) + 4a + 6 + (4a+4) + (k+4).
  have hsum : 8 * a + 4 * k + 17 = 3 * (k + 1) + (2 * (2 * a) +
              (6 + (2 * (2 * a + 2) + (k + 4)))) := by ring
  rw [hsum, srun_add]
  -- Phase A-lt-1: ones_cycle3_iter_explicit with k = k+1, j = 0.
  rw [ones_cycle3_iter_explicit (k + 1) 0 _ _]
  -- After: left = ones (0+1) *> zebra(2a) *> [false] *> blank = ones 1 *> ...
  --        right = ones (k+1) *> blank.
  -- Fold ones 1 = Side.cons true for zebra_cycle2_iter_explicit.
  have hleft_after_A1 : Side.prepend (ones (0 + 1))
                          (Side.prepend (zebra (2 * a)) (Side.prepend [false] Side.blank))
                      = Side.cons true (Side.prepend (zebra (2 * a))
                          (Side.prepend [false] Side.blank)) := rfl
  rw [hleft_after_A1]
  rw [srun_add]
  -- Phase A-lt-2: zebra_cycle2_iter_explicit with b = 2a.
  rw [zebra_cycle2_iter_explicit (2 * a) _ _]
  -- After: left = Side.cons true (Side.prepend [false] Side.blank),
  --        right = zebra (2a) *> ones (k+1) *> blank.
  rw [srun_add]
  -- Phase AB: 6 concrete steps.
  rw [lt_phase_AB _]
  -- After: {D, head=true, left = [false] *> blank, right = zebra 2 *> zebra(2a) *> ones(k+1) *> blank}.
  -- Fold zebra 2 *> zebra (2a) = zebra (2a+2).
  rw [show Side.prepend (zebra 2) (Side.prepend (zebra (2 * a))
          (Side.prepend (ones (k + 1)) Side.blank))
       = Side.prepend (zebra (2 * a + 2)) (Side.prepend (ones (k + 1)) Side.blank) from by
        rw [← Side.prepend_append, zebra_append,
            show (2 + 2 * a : Nat) = 2 * a + 2 from by ring]]
  rw [srun_add]
  -- Phase DC: sDC_shift with k = 2a+2.
  rw [sDC_shift (2 * a + 2) _ _]
  -- After: {D, head=true, left = zebra(2a+2) *> [false] *> blank, right = ones(k+1) *> blank}.
  -- Phase final.
  exact lt_phase_final a k

/-- Rule lt on SConfig; `b = a + 1 + k`.

Compose `passes_shift a 0 0 (k+2)` (6a²+4ak+11a steps) with
`lt_endgame a k` (8a+4k+17 steps).  Total 2(a+1)²+4(a+1)(a+k+2)+3(a+1)+4. -/
theorem stm_rule_lt (a k : Nat) :
    srun bmo1 (SA_Config a (a + k + 1))
      (2 * (a + 1)^2 + 4 * (a + 1) * (a + k + 2) + 3 * (a + 1) + 4) =
    SA_Config (2 * a + 2) k := by
  have hpass := passes_shift a 0 0 (k + 1)
  have hend := lt_endgame a k
  have hSA : SA_Config a (a + k + 1) = SE_Config (0 + a) 0 (((k + 1) + 1) + a) := by
    rw [SA_Config_eq_SE]; congr 1 <;> omega
  have hsplit :
      2 * (a + 1)^2 + 4 * (a + 1) * (a + k + 2) + 3 * (a + 1) + 4 =
      (4 * a * (0 + (k + 1)) + 6 * a^2 + 7 * a) + (8 * a + 4 * k + 17) := by ring
  rw [hSA, hsplit, srun_add, hpass]
  show srun bmo1 (SE_Config 0 (0 + 2 * a) ((k + 1) + 1)) (8 * a + 4 * k + 17) =
       SA_Config (2 * a + 2) k
  have h1 : (0 + 2 * a) = 2 * a := by omega
  have h2 : (k + 1) + 1 = k + 2 := by omega
  rw [h1, h2]; exact hend

/-- Base case `a=0` of `stm_rule_eq`: A(1,1) halts in 13 steps. Proved via
    the list-Config side using `decide`, lifted through `A_Config_toSConfig`. -/
lemma stm_rule_eq_zero : (srun bmo1 (SA_Config 0 0) 13).state = none := by
  rw [show SA_Config 0 0 = (A_Config 0 0 2 0).toSConfig from
      (A_Config_toSConfig 0 0 2 0).symm,
    ← toSConfig_run, toSConfig_state]
  decide

-- Eq-endgame shift: from the pre-endgame SE(0, 2k, 1), the machine halts
-- in 8k + 13 steps.  Three phases:
--   Phase A (pre-DC, 4k+6 steps): left-sweep through the middle zebra,
--     then B→C transition, reaching state D at left boundary with
--     right = zebra (2k+2) ++ [false] (ready for DC_shift).
--   Phase B (DC_shift, 4k+4 steps): DC_shift with 2k+2 cycles.
--   Phase C (post-DC, 3 steps): D,1→C, C,0→D, D,0 = HALT.
-- Total 4k+6 + 4k+4 + 3 = 8k+13.  To finish the proof:
--   (a) lift DC_shift from Config to SConfig (or define SDC_shift);
--   (b) prove phase A by induction on k (base k=0 via decide+bridge);
--   (c) compose.

/-- Base case `k = 0` of `eq_endgame`: equivalent to `stm_rule_eq_zero`. -/
lemma eq_endgame_zero : (srun bmo1 (SE_Config 0 0 1) 13).state = none := by
  rw [show SE_Config 0 0 1 = SA_Config 0 0 from (SA_Config_eq_SE 0 0).symm]
  exact stm_rule_eq_zero

-- Phase A-eq-2: 4 concrete steps from [true]*>[false]*>blank state to Phase B.
private lemma eq_phase_A2 (R : Side) :
    srun bmo1 {state := some stE, left := Side.cons true ([false] *> blank∞),
               head := false, right := R} 4
    = {state := some stB, left := blank∞, head := false,
       right := Side.cons false (Side.cons true (Side.cons false (Side.cons true R)))} := by
  simp [srun, sstep, bmo1]

-- Phase B-eq: 2 concrete steps transitioning B→C→D.
private lemma eq_phase_B (R : Side) :
    srun bmo1 {state := some stB, left := blank∞, head := false,
               right := Side.cons false (Side.cons true (Side.cons false (Side.cons true R)))} 2
    = {state := some stD, left := Side.cons false blank∞, head := true,
       right := Side.cons false (Side.cons true (Side.cons false (Side.cons true R)))} := by
  simp [srun, sstep, bmo1]

-- Phase D-eq: 3 concrete steps reaching halt from state D head=true with right=blank.
private lemma eq_phase_D (L : Side) :
    (srun bmo1 {state := some stD, left := L, head := true, right := blank∞} 3).state = none := by
  simp [srun, sstep, bmo1]

/-- **eq-endgame** — full proof by phase composition. -/
lemma eq_endgame (k : Nat) :
    (srun bmo1 (SE_Config 0 (2 * k) 1) (8 * k + 13)).state = none := by
  show (srun bmo1 {state := some stE, head := false,
                   left := ones 1 *> zebra (2 * k) *> [false] *> zebra 0 *> blank∞,
                   right := blank∞} (8 * k + 13)).state = none
  -- Normalize initial tape: ones 1 = [true], zebra 0 = [].
  have hinput : (ones 1 *> zebra (2 * k) *> [false] *> zebra 0 *> blank∞ : Side) =
                Side.cons true (zebra (2 * k) *> [false] *> blank∞) := by
    show Side.prepend (ones 1) (Side.prepend (zebra (2 * k)) (Side.prepend [false]
           (Side.prepend (zebra 0) Side.blank))) =
         Side.cons true (Side.prepend (zebra (2 * k)) (Side.prepend [false] Side.blank))
    simp [ones]
  rw [hinput]
  -- Split step count: 8k+13 = 4k + 4 + 2 + (4k+4) + 3.
  have hsum : 8 * k + 13 = 2 * (2 * k) + (4 + (2 + (2 * (2 * k + 2) + 3))) := by ring
  rw [hsum, srun_add, zebra_cycle2_iter_explicit, srun_add, eq_phase_A2,
      srun_add, eq_phase_B, srun_add]
  -- Right tape after Phase B = zebra 2 *> zebra (2k) *> blank = zebra (2k+2) *> blank.
  have right_eq :
      (Side.cons false (Side.cons true (Side.cons false (Side.cons true
        (Side.prepend (zebra (2 * k)) Side.blank)))) : Side)
      = Side.prepend (zebra (2 * k + 2)) Side.blank := rfl
  rw [right_eq, sDC_shift]
  exact eq_phase_D _

/-- **Rule a=b**: A(α, α) halts in 6α² + 3α + 3 + 1 steps.  Verified on α = 1..5, 7, 10.

Compose `passes_shift a 0 0 1` (reaches pre-endgame in 6a²+7a steps) with
`eq_endgame a` (8a+13 more steps to halt).  Total: 6a²+15a+13. -/
theorem stm_rule_eq (a : Nat) :
    (srun bmo1 (SA_Config a a) (6 * a^2 + 15 * a + 13)).state = none := by
  have hpass := passes_shift a 0 0 0
  have hend := eq_endgame a
  have hSA : SA_Config a a = SE_Config (0 + a) 0 ((0 + 1) + a) := by
    rw [SA_Config_eq_SE]; congr 1 <;> omega
  have hsplit : 6 * a^2 + 15 * a + 13 = (4 * a * (0 + 0) + 6 * a^2 + 7 * a) + (8 * a + 13) := by
    ring
  rw [hSA, hsplit, srun_add, hpass]
  show (srun bmo1 (SE_Config 0 (0 + 2 * a) (0 + 1)) (8 * a + 13)).state = none
  have h1 : (0 + 2 * a) = 2 * a := by omega
  have h2 : (0 + 1 : Nat) = 1 := by omega
  rw [h1, h2]; exact hend

-- ============================================================
-- From macro steps to nextMathState equivalence
-- ============================================================

/-- One macro step (stream version): for any (α, β) with α, β ≥ 1, the TM
    either halts or advances to the nextMathState in some positive number
    of steps.  Bridges the three `stm_rule_*` lemmas to the math model. -/
theorem stm_simulates_math (a b : Nat) :
    ∃ k, k > 0 ∧
      (match nextMathState (.A (a + 1) (b + 1)) with
       | .A α' β' =>
         α' ≥ 1 ∧ β' ≥ 1 ∧ srun bmo1 (SA_Config a b) k = SA_Config (α' - 1) (β' - 1)
       | .Halt => (srun bmo1 (SA_Config a b) k).state = none) := by
  rcases lt_trichotomy a b with hab | hab | hab
  · -- a < b: α = a+1 < b+1 = β, apply stm_rule_lt
    obtain ⟨m, rfl⟩ : ∃ m, b = a + 1 + m := ⟨b - a - 1, by omega⟩
    refine ⟨2 * (a + 1)^2 + 4 * (a + 1) * (a + m + 2) + 3 * (a + 1) + 4,
            by positivity, ?_⟩
    rw [show nextMathState (.A (a + 1) (a + 1 + m + 1)) = .A (2 * a + 3) (m + 1) from by
      simp only [nextMathState]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      congr 1
      omega]
    refine ⟨by omega, by omega, ?_⟩
    have h1 : 2 * a + 3 - 1 = 2 * a + 2 := by omega
    have h2 : m + 1 - 1 = m := by omega
    rw [h1, h2]
    have hb : a + 1 + m = a + m + 1 := by omega
    rw [hb]
    exact stm_rule_lt a m
  · -- a = b: halt branch
    subst hab
    refine ⟨6 * a^2 + 15 * a + 13, by positivity, ?_⟩
    rw [show nextMathState (.A (a + 1) (a + 1)) = .Halt from by simp [nextMathState]]
    exact stm_rule_eq a
  · -- a > b: apply stm_rule_gt
    obtain ⟨m, rfl⟩ : ∃ m, a = b + 1 + m := ⟨a - b - 1, by omega⟩
    refine ⟨6 * b^2 + 23 * b + 27, by positivity, ?_⟩
    rw [show nextMathState (.A (b + 1 + m + 1) (b + 1)) = .A (m + 1) (4 * b + 6) from by
      simp only [nextMathState]
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      congr 1
      omega]
    refine ⟨by omega, by omega, ?_⟩
    have h1 : m + 1 - 1 = m := by omega
    have h2 : 4 * b + 6 - 1 = 4 * b + 5 := by omega
    rw [h1, h2]
    exact stm_rule_gt b m

-- ============================================================
-- Halting ↔ mathematical condition
-- ============================================================

/-- Helper: once an SConfig is halted at step `m`, it remains halted at every later step. -/
private lemma srun_halted_at_later {c : SConfig 6} {m k : Nat}
    (hmk : m ≤ k) (hm : (srun bmo1 c m).state = none) :
    (srun bmo1 c k).state = none := by
  rw [show k = m + (k - m) from by omega, srun_add, srun_halted bmo1 _ hm]
  exact hm

/-- Backward bridge: if the math iteration starting from `(a+1, b+1)` reaches `.Halt`
    in `k` steps, then the TM halts starting from `SA_Config a b`. -/
private lemma tm_halts_of_math_halts (a b k : Nat)
    (hk : iterMathState (.A (a + 1) (b + 1)) k = .Halt) :
    ∃ n, (srun bmo1 (SA_Config a b) n).state = none := by
  induction k generalizing a b with
  | zero => simp [iterMathState] at hk
  | succ k' ih =>
    -- `iterMathState s (k'+1) = iterMathState (nextMathState s) k'`
    have hk' : iterMathState (nextMathState (.A (a + 1) (b + 1))) k' = .Halt := hk
    obtain ⟨n, _, hspec⟩ := stm_simulates_math a b
    -- Case-split on whether the next math state halts or advances.
    cases hnext : nextMathState (.A (a + 1) (b + 1)) with
    | Halt =>
      rw [hnext] at hspec
      exact ⟨n, hspec⟩
    | A α' β' =>
      rw [hnext] at hspec hk'
      obtain ⟨hα', hβ', hrun⟩ := hspec
      have h1 : α' - 1 + 1 = α' := by omega
      have h2 : β' - 1 + 1 = β' := by omega
      rw [show (MathState.A α' β' : MathState) = .A (α' - 1 + 1) (β' - 1 + 1) from by
            rw [h1, h2]] at hk'
      obtain ⟨m, hm⟩ := ih (α' - 1) (β' - 1) hk'
      exact ⟨n + m, by rw [srun_add, hrun]; exact hm⟩

/-- Forward bridge: if the TM halts starting from `SA_Config a b`, the math iteration
    from `(a+1, b+1)` eventually reaches `.Halt`.  Proved by strong induction on the
    TM step count `n`. -/
private lemma math_halts_of_tm_halts : ∀ (n : Nat) (a b : Nat),
    (srun bmo1 (SA_Config a b) n).state = none →
    ∃ k, iterMathState (.A (a + 1) (b + 1)) k = .Halt := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hn
    obtain ⟨s, hs_pos, hspec⟩ := stm_simulates_math a b
    cases hnext : nextMathState (.A (a + 1) (b + 1)) with
    | Halt =>
      refine ⟨1, ?_⟩
      show iterMathState (nextMathState (.A (a + 1) (b + 1))) 0 = .Halt
      rw [hnext]; rfl
    | A α' β' =>
      rw [hnext] at hspec
      obtain ⟨hα', hβ', hrun⟩ := hspec
      -- If `n < s`, halted-stays-halted contradicts `hrun` (non-halted at step s).
      by_cases hns : n < s
      · exfalso
        have hsn : (srun bmo1 (SA_Config a b) s).state = none :=
          srun_halted_at_later (by omega) hn
        rw [hrun] at hsn
        simp [SA_Config] at hsn
      · push_neg at hns
        -- `srun .. n = srun (SA_Config (α'-1) (β'-1)) (n - s)`.
        have hshift : srun bmo1 (SA_Config a b) n =
                      srun bmo1 (SA_Config (α' - 1) (β' - 1)) (n - s) := by
          conv_lhs => rw [show n = s + (n - s) from by omega]
          rw [srun_add, hrun]
        rw [hshift] at hn
        have hlt : n - s < n := by omega
        obtain ⟨k', hk'⟩ := ih (n - s) hlt (α' - 1) (β' - 1) hn
        have h1 : α' - 1 + 1 = α' := by omega
        have h2 : β' - 1 + 1 = β' := by omega
        rw [h1, h2] at hk'
        refine ⟨k' + 1, ?_⟩
        show iterMathState (nextMathState (.A (a + 1) (b + 1))) k' = .Halt
        rw [hnext]; exact hk'

/-- **Halting bridge**: the TM `bmo1` halts starting from `SA_Config a b` iff the
    mathematical iteration `iterMathState` starting from `(a+1, b+1)` eventually
    reaches `.Halt`.  Combines `math_halts_of_tm_halts` and `tm_halts_of_math_halts`. -/
theorem tm_sa_halts_iff (a b : Nat) :
    (∃ n, (srun bmo1 (SA_Config a b) n).state = none) ↔
    (∃ k, iterMathState (.A (a + 1) (b + 1)) k = .Halt) :=
  ⟨fun ⟨n, hn⟩ => math_halts_of_tm_halts n a b hn,
   fun ⟨k, hk⟩ => tm_halts_of_math_halts a b k hk⟩

/-- **Main halting ↔ mathematical condition**: the TM `bmo1` started on a blank tape
    halts iff the abstract iteration of the macro-rule map, started at `A(1, 2)`,
    eventually reaches `.Halt`.

Concretely, the RHS asserts that the sequence
  `(1, 2) → (3, 1) → (7, 2) → (5, 10) → (17, 5) → (12, 22) → …`
(applying `α > β ↦ (α-β, 4β+2)`, `α < β ↦ (2α+1, β-α)`, `α = β ↦ Halt`)
eventually hits `α = β`.  Whether this happens for `A(1, 2)` is the open problem
that the BMO1 cryptid asks. -/
theorem tm_halts_iff :
    (∃ n, (run bmo1 (initConfig 6) n).halted) ↔
    (∃ k, iterMathState (.A 1 2) k = .Halt) := by
  -- Reduce `halted` to `state = none` and lift `initConfig` to `SA_Config 0 1` via
  -- `init_to_A12` + `A_Config_toSConfig`.
  have hiff_sa : (∃ n, (run bmo1 (initConfig 6) n).halted) ↔
                 (∃ n, (srun bmo1 (SA_Config 0 1) n).state = none) := by
    constructor
    · rintro ⟨n, hn⟩
      -- Before step 10 the TM is non-halted (else `init_to_A12` would give a halted config).
      -- After step 10, reduce to SA_Config 0 1 via `init_to_A12` + bridge.
      by_cases h10 : n < 10
      · -- At step n < 10 the TM is halted; but at step 10 it's at A_Config 0 1 0 1 (non-halted).
        exfalso
        have h10state : (run bmo1 (initConfig 6) 10).state = none := by
          conv_lhs => rw [show 10 = n + (10 - n) from by omega]
          rw [run_add, run_halted bmo1 _ hn]; exact hn
        rw [init_to_A12] at h10state
        simp [A_Config] at h10state
      · push_neg at h10
        refine ⟨n - 10, ?_⟩
        have hstate : (run bmo1 (initConfig 6) n).state =
                      (run bmo1 (A_Config 0 1 0 1) (n - 10)).state := by
          conv_lhs => rw [show n = 10 + (n - 10) from by omega]
          rw [run_add, init_to_A12]
        have hnone : (run bmo1 (A_Config 0 1 0 1) (n - 10)).state = none := hstate ▸ hn
        rw [← toSConfig_state, toSConfig_run, A_Config_toSConfig] at hnone
        exact hnone
    · rintro ⟨n, hn⟩
      refine ⟨10 + n, ?_⟩
      show (run bmo1 (initConfig 6) (10 + n)).state = none
      rw [run_add, init_to_A12]
      have := hn
      rw [← A_Config_toSConfig 0 1 0 1, ← toSConfig_run, toSConfig_state] at this
      exact this
  rw [hiff_sa]; exact tm_sa_halts_iff 0 1

-- ============================================================
-- Pair iteration: unpacked mathematical condition
-- ============================================================

/-- The mathematical iteration map on positive pairs `(α, β)`, matching the macro
    rules: `α > β ↦ (α − β, 4β + 2)`, `α < β ↦ (2α + 1, β − α)`, fixed at `α = β`. -/
def macroMap : Nat × Nat → Nat × Nat
  | (α, β) =>
    if α > β then (α - β, 4 * β + 2)
    else if α < β then (2 * α + 1, β - α)
    else (α, β)

/-- `k`-fold iteration of `macroMap`. -/
def iterPair : Nat × Nat → Nat → Nat × Nat
  | p, 0 => p
  | p, k + 1 => iterPair (macroMap p) k

/-- `iterMathState` unfolds one step from the right. -/
lemma iterMathState_succ (s : MathState) (k : Nat) :
    iterMathState s (k + 1) = nextMathState (iterMathState s k) := by
  induction k generalizing s with
  | zero => rfl
  | succ k' ih => exact ih (nextMathState s)

/-- `iterPair` unfolds one step from the right. -/
lemma iterPair_succ (p : Nat × Nat) (k : Nat) :
    iterPair p (k + 1) = macroMap (iterPair p k) := by
  induction k generalizing p with
  | zero => rfl
  | succ k' ih => exact ih (macroMap p)

/-- Reduction of `nextMathState` on the `.A α β` branch as a `rfl` equation (lets
    `rw` see through the pattern match). -/
lemma nextMathState_A (α β : Nat) :
    nextMathState (.A α β) =
      (if α = 0 ∨ β = 0 then .Halt
       else if α = β then .Halt
       else if α > β then .A (α - β) (4 * β + 2)
       else .A (2 * α + 1) (β - α)) := rfl

/-- Reduction of `macroMap` on a concrete pair as a `rfl` equation. -/
lemma macroMap_mk (α β : Nat) :
    macroMap (α, β) =
      (if α > β then (α - β, 4 * β + 2)
       else if α < β then (2 * α + 1, β - α)
       else (α, β)) := rfl

/-- Correspondence: while the math iteration from `.A 1 2` has not halted at step `k`,
    it agrees with the pair iteration via `macroMap` from `(1, 2)`, and both
    components remain ≥ 1.  The `(1, 2)` start point never produces `0` entries under
    any number of iterations — so the only way to halt is `α = β`. -/
private lemma math_state_eq_pair (k : Nat)
    (h : iterMathState (.A 1 2) k ≠ .Halt) :
    ∃ α β : Nat, iterMathState (.A 1 2) k = .A α β ∧
                 iterPair (1, 2) k = (α, β) ∧ α ≥ 1 ∧ β ≥ 1 := by
  induction k with
  | zero => exact ⟨1, 2, rfl, rfl, by decide, by decide⟩
  | succ k' ih =>
    have hk' : iterMathState (.A 1 2) k' ≠ .Halt := fun hhalt => by
      apply h; rw [iterMathState_succ, hhalt]; rfl
    obtain ⟨α, β, hms, hpair, hα, hβ⟩ := ih hk'
    -- Non-halting at k'+1 with α, β ≥ 1 forces α ≠ β.
    have h_not_eq : α ≠ β := by
      intro heq12
      apply h
      rw [iterMathState_succ, hms, nextMathState_A,
          if_neg (by rintro (h | h) <;> omega), if_pos heq12]
    by_cases hgt : α > β
    · refine ⟨α - β, 4 * β + 2, ?_, ?_, by omega, by omega⟩
      · rw [iterMathState_succ, hms, nextMathState_A,
            if_neg (by rintro (h | h) <;> omega), if_neg h_not_eq, if_pos hgt]
      · rw [iterPair_succ, hpair, macroMap_mk, if_pos hgt]
    · have hlt : α < β := by omega
      refine ⟨2 * α + 1, β - α, ?_, ?_, by omega, by omega⟩
      · rw [iterMathState_succ, hms, nextMathState_A,
            if_neg (by rintro (h | h) <;> omega), if_neg h_not_eq, if_neg hgt]
      · rw [iterPair_succ, hpair, macroMap_mk, if_neg hgt, if_pos hlt]

/-- **Unpacked halting condition**: the math iteration reaches `.Halt` from `.A 1 2`
    iff the pair iteration via `macroMap` from `(1, 2)` ever hits a pair with
    `α = β`.  Reformulates the abstract Halt predicate as a concrete "reach `α = β`"
    predicate over iterations of the map
    `α > β ↦ (α − β, 4β + 2)`, `α < β ↦ (2α + 1, β − α)`. -/
theorem math_halts_iff_pair_eq :
    (∃ k, iterMathState (.A 1 2) k = .Halt) ↔
    (∃ k, (iterPair (1, 2) k).1 = (iterPair (1, 2) k).2) := by
  refine ⟨fun ⟨k, hk⟩ => ?_, fun ⟨k, heq⟩ => ?_⟩
  · -- Forward: find the smallest halting step via `Nat.find`.
    have hex : ∃ j, iterMathState (.A 1 2) j = .Halt := ⟨k, hk⟩
    let j := Nat.find hex
    have hj : iterMathState (.A 1 2) j = .Halt := Nat.find_spec hex
    have hmin : ∀ m < j, iterMathState (.A 1 2) m ≠ .Halt :=
      fun m hm h => Nat.find_min hex hm h
    have hj_pos : 0 < j := by
      by_contra hzero
      push_neg at hzero
      have hj0 : j = 0 := by omega
      rw [hj0] at hj; exact absurd hj (by decide)
    have hj_prev : iterMathState (.A 1 2) (j - 1) ≠ .Halt := hmin (j - 1) (by omega)
    obtain ⟨α, β, hms, hpair, hα, hβ⟩ := math_state_eq_pair (j - 1) hj_prev
    refine ⟨j - 1, ?_⟩
    have hj_eq : j = (j - 1) + 1 := by omega
    rw [hj_eq, iterMathState_succ, hms, nextMathState_A] at hj
    rw [if_neg (by rintro (h | h) <;> omega)] at hj
    by_cases h12 : α = β
    · rw [hpair]; exact h12
    · exfalso
      rw [if_neg h12] at hj
      split_ifs at hj
  · -- Backward: pair hits equal → one more math step halts.
    by_cases hh : iterMathState (.A 1 2) k = .Halt
    · exact ⟨k, hh⟩
    · obtain ⟨α, β, hms, hpair, hα, hβ⟩ := math_state_eq_pair k hh
      refine ⟨k + 1, ?_⟩
      rw [iterMathState_succ, hms, nextMathState_A,
          if_neg (by rintro (h | h) <;> omega)]
      rw [hpair] at heq
      exact if_pos heq

-- ============================================================
-- Progress log / TODO
-- ============================================================
-- 2026-04-20  First draft; SConfig refactor.
--
--  • Macro rules verified numerically by Python simulator sim.py over
--    >100 cases.  Step counts (α = a+1, β = b+1 in (a,b)-param):
--      a>b branch: 6b² + 23b + 27   (= 6β² + 11β + 10 in wiki form)
--      a<b branch: 2(a+1)² + 4(a+1)(a+k+2) + 3(a+1) + 4
--                 (= 2α² + 4αβ + 3α + 4 in wiki form)
--      a=b branch: 6a² + 15a + 13   halts  (= 6α² + 3α + 3 + 1, the
--                  "+1" accounts for the Lean convention that the
--                  halting transition itself is a step.)
--
--  • Scope change: after the SConfig refactor, rule lemmas are stated on
--    `SA_Config` (infinite tape, no padding).  `A_Config` is retained for
--    `init_to_A12` and for base-case `decide` checks which are lifted
--    through `A_Config_toSConfig` + `toSConfig_run`.
--
-- Proved so far:
--   * init_to_A12         (Config side, by `decide`)
--   * E_right_shift       (state-E sweep through a ones block)
--   * DC_shift            (state-D,C alternation through a zebra block)
--   * A_Config_toSConfig  (Config→SConfig bridge; padding vanishes)
--   * stm_rule_gt_base    (A(2,1)→A(1,6) in 27 steps, via decide+bridge)
--   * stm_rule_lt_base    (A(1,2)→A(3,1) in 17 steps, via decide+bridge)
--   * stm_rule_eq_zero    (A(1,1) halts in 13 steps, via decide+bridge)
--   * stm_simulates_math  (case split; reduces to the three rule lemmas)
--
-- Remaining sorries (scope: macro rules; halting equivalence out of scope):
--   * stm_rule_gt, stm_rule_lt, stm_rule_eq  (general induction)
--
-- Dynamics (from Python trace) for `tm_rule_eq` A(α, α):
--   Phase 1 (β-ones consumption, ≈ 2β steps): E/F ping-pong converting
--      the β-block into zebra-shaped pattern.
--   Phase 2 (left-sweep boundary, O(α+β) steps): reach state B at the
--      leftmost structural 1, bounce back via C.
--   Phase 3 (right-sweep D,C alternation): 2(2a+2) = 4a+4 steps. This
--      is exactly `DC_shift` with k = 2a+2.
--   Phase 4: 3 concrete steps — D,1→C, C,0→D, D,0→HALT.
--   Total = (preamble P) + (4a+4) + 3 = 6a²+15a+13, so P = 6a²+11a+6.
--
-- Each of the three rule lemmas has analogous structure (a preamble
-- ending at a state-D right-boundary followed by a large DC sweep).
-- Completing them requires, per rule:
--   (a) a shift lemma for the E/F ping-pong (β-phase);
--   (b) a shift lemma for the A/B left-walk through (10)^k;
--   (c) a boundary lemma for the leftmost bounce;
--   (d) a composition theorem assembling the phases.
-- Plus padding-locality bookkeeping (run_left_append + run_right_append
-- from BusyLean) to thread p, q through the phases.
--
-- Base-case `decide` runs (in `sim.py` + `lean_run_code`) fix the step
-- counts and next-config shapes exactly, so the remaining work is
-- structural induction and bookkeeping rather than discovery.

end BMO1
