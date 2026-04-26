import BusyLean
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open BusyLean

namespace HydraShift6

/-!
# 6-state TM `1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF`

BB(6) candidate with a "Hydra-like" macro structure (previous-work/wiki.txt by
Racheline).  Halt/nonhalt is **not** the target; this file records observed
macro rules.

## Transition table
|   | 0   | 1   |
|---|-----|-----|
| A | 1RB | 1RE |
| B | 1LC | 1LD |
| C | --- | 1LA |
| D | 1LB | 1LE |
| E | 0RF | 0RA |
| F | 1LD | 1RF |

The only halting transition is `C,0 → ---`.  C is entered only from `B,0 → 1LC`.

## Macro configuration (from previous-work/wiki.txt, Racheline)

  `A(m, n)`  encodes the tape
      `0^inf  1^m  (01)^n  0  [A]>  0^inf`
  (state A, head facing right, on a 0 cell; `0^inf` both sides).

Racheline uses a shifted second argument `k = n + 9` (so `A(m, k) = A(m, n = k-9)`
in our parametrization and her starting point `A(1, 10)` is our `A(1, 1)`).

The "canonical" form has `m ≥ 1` since a leading `0` of `(01)^n` is absorbed
into the infinite blank on the left.  `A(0, n) = A(1, n-1)` as tapes.

## Macro rules (all verified empirically by `verify_dt.py`)

Shift rules (all parameters `i ≥ 0`):
  `A(m+4, 2i)`   → `A(m, 3i+4)`          dt = 6i² + 28i + 28        (m ≥ 1)
  `A(m+4, 2i+1)` → `A(m, 3i+6)`          dt = 6i² + 40i + 54        (m ≥ 1)

m=4 bridge (RHS `m = 0` canonicalizes to `m = 1`, absorbing one zebra pair):
  `A(4, 2i)`     → `A(1, 3i+3)`          dt = 6i² + 28i + 28
  `A(4, 2i+1)`   → `A(1, 3i+5)`          dt = 6i² + 40i + 54

Small-m rules (halt or reset the trajectory to a new A(_, 1)):
  `A(1, 2i)`     → halt                  dt = 6i² + 22i + 18
  `A(1, 2i+1)`   → `A(6i+7, 1)`          dt = 6i² + 28i + 37
  `A(2, 2i)`     → halt                  dt = 6i² + 22i + 20
  `A(2, 2i+1)`   → halt                  dt = 6i² + 34i + 42
  `A(3, 2i)`     → `A(6i+6, 1)`          dt = 6i² + 28i + 33
  `A(3, 2i+1)`   → `A(6i+10, 1)`         dt = 6i² + 40i + 59

  From blank tape: initial config → `A(1, 1)` in 15 steps.

## Empirical orbit from `A(1, 1)`

(From `sim.py orbit`.)  The "compressed" orbit B(m) := A(m, 1) follows
`HydraMap`-driven jumps:

  i=0 B(1)    = A(1, 1)   →(37)    A(7, 1)    = B(7)
  i=1 B(7)    = A(7, 1)   →(54)    A(3, 6)    →(171)  A(24, 1) = B(24)
  i=2 B(24)   ...          through several shifts... reaches A(1, 99)
       (because i is large, dt ≈ 15815)                         →(15815) A(301, 1) = B(301)
  ...

HydraMap(k) := ⌊3k/2⌋.  Starting from 10: 10, 15, 22, 33, 49, 73, 109, 163,
244, 366, 549, 823, 1234, …

  B(1)  →(…)  B(7)    → B(24)   → B(301)   → B(459271258863235) → …

The BB(6) question then reduces to whether the Hydra-iterate ever lands on
an even (or specific pattern) at the right moment.
-/

def tm : TM 6 := tm! "1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF"

-- Transition simp lemmas: evaluate `tm.tr st sym` without unfolding the literal.
@[simp] private theorem tr_A0 : tm.tr stA false = some (stB, true,  Dir.R) := rfl
@[simp] private theorem tr_A1 : tm.tr stA true  = some (stE, true,  Dir.R) := rfl
@[simp] private theorem tr_B0 : tm.tr stB false = some (stC, true,  Dir.L) := rfl
@[simp] private theorem tr_B1 : tm.tr stB true  = some (stD, true,  Dir.L) := rfl
@[simp] private theorem tr_C0 : tm.tr stC false = none := rfl
@[simp] private theorem tr_C1 : tm.tr stC true  = some (stA, true,  Dir.L) := rfl
@[simp] private theorem tr_D0 : tm.tr stD false = some (stB, true,  Dir.L) := rfl
@[simp] private theorem tr_D1 : tm.tr stD true  = some (stE, true,  Dir.L) := rfl
@[simp] private theorem tr_E0 : tm.tr stE false = some (stF, false, Dir.R) := rfl
@[simp] private theorem tr_E1 : tm.tr stE true  = some (stA, false, Dir.R) := rfl
@[simp] private theorem tr_F0 : tm.tr stF false = some (stD, true,  Dir.L) := rfl
@[simp] private theorem tr_F1 : tm.tr stF true  = some (stF, true,  Dir.R) := rfl

-- ============================================================
-- Macro configuration
-- ============================================================

/-- `A_config m n` — state A, head on the `0` just right of the macro block.
    Tape pattern (L-to-R): `0^inf 1^m (01)^n 0 [A]> 0^inf`.

    Side encoding: with `left` indexed from the head outward (index 0 is the
    cell immediately left of head), the pattern reads
      left[0]            = 0   (separator)
      left[1..2n]        = 1, 0, 1, 0, … (last "1" of each `(01)` pair, then the "0")
      left[2n+1..2n+m]   = 1^m
      left[> 2n+m]       = blank

    As a list prefix this is `zebra n ++ [false] ++ ones m`, since
    `zebra n = [false, true, false, true, …, false, true]` of length `2n`. -/
def A_config (m n : Nat) : SConfig 6 :=
  { state := some stA,
    head := false,
    left := zebra n *> [false] *> ones m *> blank∞,
    right := blank∞ }

-- ============================================================
-- Shift rules  (m + 4 path, m ≥ 1 on RHS)
-- ============================================================

-- ============================================================
-- Structural lemmas for shift_even_high
-- ============================================================
--
-- Empirical finding (sim.py Mid-search): running A(m+5, 2i) on the TM for
-- `6i² + 10i + 3` steps always reaches a "Pivot" shape
--   { state A, head 0, left = ones 5 *> L, right = ones (6i+2) *> blank }
-- where `L` is the tail beyond the ones-5 window (= ones m *> blank for our
-- `A_config (m+5) (2i)`).  Then `3(6i+2) + 19 = 18i + 25` more steps complete
-- the rule.  Total: `6i² + 10i + 3 + 18i + 25 = 6i² + 28i + 28` ✓.
--
-- The first 3 steps (right-push) are a constant prelude independent of i;
-- they leave the zebra prefix alone and produce a "FlipConfig" intermediate
-- with `ones 2` on the right.  Then a quadratic-in-i "absorb" phase converts
-- the flipped-zebra prefix into right-ones, landing in Pivot.
-- ============================================================

/-- Auxiliary identity: `true :: zebra n ++ [false] = [true, false] ×× (n+1)`.
    Shifts a zebra-segment by one bit to turn it into a flipped-zebra. -/
lemma true_zebra_false (n : Nat) :
    true :: zebra n ++ [false] = [true, false] ×× (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show true :: (false :: true :: zebra k) ++ [false] = [true, false] ×× (k + 2)
    change [true, false] ++ (true :: zebra k ++ [false]) = [true, false] ×× (k + 2)
    rw [ih]; rfl

/-- List-append form: `[true, false] ×× n ++ [true, false] = [true, false] ×× (n+1)`. -/
lemma flipZebra_append (n : Nat) :
    [true, false] ×× n ++ [true, false] = [true, false] ×× (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih => show ([true, false] ++ [true, false] ×× k) ++ _ = _; simp [listRepeat]; exact ih

/-- **Right-push** (3 steps, constant): for any abstract `R : Side` after the
    `[false]` separator, the first 3 steps of the shift rule absorb the
    outermost `[false]`, converting `zebra (2i)` prefix on left into a
    flipped-zebra `[true, false] ×× (2i)` and appending `ones 2` on right. -/
lemma right_push_g (R : Side) (i : Nat) :
    srun tm
      { state := some stA, head := false,
        left := zebra (2*i) *> [false] *> R,
        right := blank∞ } 3 =
    { state := some stA, head := false,
      left := ([true, false] ×× (2*i)) *> R,
      right := ones 2 *> blank∞ } := by
  cases i with
  | zero =>
    simp [srun, sstep, tm, Side.prepend, ones, zebra, listRepeat]
  | succ j =>
    have hz : zebra (2 * (j + 1)) = false :: true :: zebra (2 * j + 1) := by
      show zebra (2 * j + 1 + 1) = false :: true :: zebra (2 * j + 1); rfl
    rw [hz]
    simp only [Side.prepend, srun, sstep, tm, Side.head_cons, Side.tail_cons,
               Side.head_blank, Side.tail_blank]
    congr 1
    rw [show [true, false] ×× (2 * (j + 1)) = true :: zebra (2 * j + 1) ++ [false] from by
          rw [show 2 * (j + 1) = (2 * j + 1) + 1 from by ring,
              ← true_zebra_false]]
    simp [Side.prepend, Side.prepend_append]

/-- Base case of shift_even_high (i = 0): `A(m+5, 0) → A(m+1, 4)` in 28 steps.
    Local statement with abstract left tail `L`.  Direct simp through 28
    concrete steps (head only visits the concrete `[false, 1,1,1,1,1]`
    prefix; `L` is never read). -/
lemma shift_even_high_base (L : Side) :
    srun tm
      { state := some stA, head := false,
        left := [false] *> ones 5 *> L,
        right := blank∞ } 28 =
    { state := some stA, head := false,
      left := zebra 4 *> [false] *> ones 1 *> L,
      right := blank∞ } := by
  simp [srun, sstep, tm, Side.prepend, ones, zebra]

/-- **Absorb-one base case** (k=0 means right = ones 2): consume 4 flip cells
    `[true, false, true, false]` on the left, producing ones 8 on the right
    in 16 steps.  Head never reaches `R`.  Pure direct simp. -/
lemma absorb_one_base (R : Side) :
    srun tm
      { state := some stA, head := false,
        left := [true, false, true, false] *> R,
        right := ones 2 *> blank∞ } 16 =
    { state := some stA, head := false,
      left := R,
      right := ones 8 *> blank∞ } := by
  simp [srun, sstep, tm, Side.prepend, ones]

/-- **Absorb-one Phase A** (3 steps, constant): right-push prelude inside
    one absorb iteration.  Starting from `Flip R (k+1) = state A head=0 with
    [T,F,T,F]*>R left and ones(k+1)*>blank right`, 3 steps land at
    `state E head=T, left=[F,T,F]*>R, right=ones(k+2)*>blank`. -/
lemma absorb_phaseA (R : Side) (k : Nat) :
    srun tm
      { state := some stA, head := false,
        left := [true, false, true, false] *> R,
        right := ones (k + 1) *> blank∞ } 3 =
    { state := some stE, head := true,
      left := [false, true, false] *> R,
      right := ones (k + 2) *> blank∞ } := by
  simp [srun, sstep, tm, Side.prepend, ones]

/-- Side identity: `ones (2*j + 3) *> blank∞ = ones (2*(j+1)) *> ones 1 *> blank∞`. -/
private lemma ones_2j3_split (j : Nat) :
    Side.prepend (ones (2*j + 3)) blank∞ =
      Side.prepend (ones (2*(j+1))) (Side.prepend (ones 1) blank∞) := by
  rw [← Side.prepend_append, ones_append, show 2*(j+1) + 1 = 2*j + 3 from by ring]

/-- **EA-cycle shift** (`2k` steps): from state E on a `1` with `ones (2k)` on
    right followed by arbitrary `R`, advance `2k` cells right (consuming the
    `2k` ones) and deposit `[true, false] ×× k` on the left. -/
lemma EA_shift (k : Nat) (L R : Side) :
    srun tm
      { state := some stE, head := true, left := L,
        right := ones (2 * k) *> R } (2 * k) =
    { state := some stE, head := true,
      left := ([true, false] ×× k) *> L,
      right := R } := by
  induction k generalizing L with
  | zero => simp [srun, ones, listRepeat]
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 + 2 * j from by ring, srun_add,
        show (2 + 2 * j : Nat) = (2 * j + 1) + 1 from by ring]
    -- ones unfolds as true :: true :: ones (2*j) now (via ones_succ twice).
    have h_two : srun tm
      { state := some stE, head := true, left := L,
        right := ones ((2 * j + 1) + 1) *> R } 2 =
      { state := some stE, head := true,
        left := [true, false] *> L,
        right := ones (2 * j) *> R } := by
      simp [srun, sstep, tm, Side.prepend]
    rw [h_two, ih]
    congr 1
    show (([true, false] ×× j) *> ([true, false] *> L) : Side)
       = (([true, false] ×× (j + 1)) *> L : Side)
    rw [← Side.prepend_append, flipZebra_append]

/-- **Absorb-one Phase B** (`2j+5` steps): E-A cycle through `2j+3` right ones
    + final E,0→0RF transition.  Goes from MidConfig (state E, head=T, left
    [F,T,F]*>R, right ones(2j+3)*>blank) to FConfig (state F, head=F, blank
    right, left has consumed the 3 prefix cells and j+1 [T,F] pairs got
    deposited from the EA cycle, plus 3 fresh [F,T,F] from the final 3 steps). -/
lemma absorb_phaseB (R : Side) (j : Nat) :
    srun tm
      { state := some stE, head := true,
        left := [false, true, false] *> R,
        right := ones (2*j + 3) *> blank∞ } (2*j + 5) =
    { state := some stF, head := false,
      left := [false, true, false] *> ([true, false] ×× (j + 1)) *> [false, true, false] *> R,
      right := blank∞ } := by
  rw [show (2*j + 5 : Nat) = 2*(j+1) + 3 from by ring, srun_add, ones_2j3_split]
  -- Apply EA_shift: 2(j+1) steps consume ones (2(j+1)) on the right.
  rw [EA_shift (j+1) ([false, true, false] *> R) (ones 1 *> blank∞)]
  -- Final 3 steps: E,1→0RA on last T; A,1→1RE on blank; E,0→0RF on blank.
  simp [srun, sstep, tm, Side.prepend, ones]

/-- **BD-iter** (induction on `k`, `2k` steps): from state B head=T with left
    `[false] *> [true, false] ×× k *> X`, after `2k` steps we reach state B
    head=T with left `[false] *> X`.  Each "BD-cycle" pair consumes one
    `[true, false]` block from the left and adds 2 right ones. -/
lemma BD_iter (k : Nat) (X : Side) (n : Nat) :
    srun tm
      { state := some stB, head := true,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× k) X),
        right := ones n *> blank∞ } (2 * k) =
    { state := some stB, head := true,
      left := Side.prepend [false] X,
      right := ones (n + 2 * k) *> blank∞ } := by
  induction k generalizing n with
  | zero => simp [srun, ones, listRepeat]
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 + 2 * j from by ring, srun_add]
    have h_two : srun tm
        { state := some stB, head := true,
          left := Side.prepend [false] (Side.prepend ([true, false] ×× (j + 1)) X),
          right := ones n *> blank∞ } 2 =
        { state := some stB, head := true,
          left := Side.prepend [false] (Side.prepend ([true, false] ×× j) X),
          right := ones (n + 2) *> blank∞ } := by
      show srun tm
        { state := some stB, head := true,
          left := Side.prepend [false] (Side.prepend ([true, false] ++ [true, false] ×× j) X),
          right := ones n *> blank∞ } 2 = _
      simp only [Side.prepend_append]
      simp [srun, sstep, tm, Side.prepend, ones]
    rw [h_two, ih (n + 2), show n + 2 + 2 * j = n + (2 + 2 * j) from by ring]

/-- **Absorb-one Phase C** (`2j+8` steps): F-sweep back through the zebra
    pattern; state transitions F → D → B → D → B → … → C → A.  Consumes the
    `2j+8` left cells and produces `ones (2j+8)` on right.  Ends at the
    Flip R 0 (2j+8) target. -/
lemma absorb_phaseC (R : Side) (j : Nat) :
    srun tm
      { state := some stF, head := false,
        left := [false, true, false] *> ([true, false] ×× (j + 1)) *> [false, true, false] *> R,
        right := blank∞ } (2 * j + 8) =
    { state := some stA, head := false,
      left := R,
      right := ones (2 * j + 8) *> blank∞ } := by
  -- Preamble (4 steps): F → D → B → D → B; lands at state B head=T with
  -- left = [F] *> [T,F]×j *> [F,T,F] *> R, right = ones 4.
  have h_pre : srun tm
      { state := some stF, head := false,
        left := [false, true, false] *> ([true, false] ×× (j + 1)) *> [false, true, false] *> R,
        right := blank∞ } 4 =
      { state := some stB, head := true,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× j)
                  (Side.prepend [false, true, false] R)),
        right := ones 4 *> blank∞ } := by
    show srun tm
      { state := some stF, head := false,
        left := Side.prepend [false, true, false]
                  (Side.prepend ([true, false] ++ [true, false] ×× j)
                    (Side.prepend [false, true, false] R)),
        right := blank∞ } 4 = _
    simp only [Side.prepend_append]
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [show (2 * j + 8 : Nat) = 4 + (2 * j + 4) from by ring, srun_add, h_pre,
      show (2 * j + 4 : Nat) = 2 * j + 4 from rfl, srun_add, BD_iter j _ 4]
  -- Terminator (4 steps): B → D → B → C → A.
  show srun tm
    { state := some stB, head := true,
      left := Side.prepend [false] (Side.prepend [false, true, false] R),
      right := ones (4 + 2 * j) *> blank∞ } 4 = _
  -- Peel ones 4 from the right so simp can step through 4 right cells.
  rw [show Side.prepend (ones (4 + 2 * j)) blank∞ =
        Side.prepend (ones 4) (Side.prepend (ones (2 * j)) blank∞) from by
      rw [← Side.prepend_append, ones_append]]
  simp [srun, sstep, tm, Side.prepend, ones]
  -- Refold: cons true^8 (ones (2*j) *> blank) = ones 8 *> ones (2*j) *> blank,
  -- which equals ones (4 + (2*j + 4)) *> blank by ones_append + Nat.add.
  show (Side.prepend (ones 8) (Side.prepend (ones (2 * j)) blank∞) : Side)
     = Side.prepend (ones (4 + (2 * j + 4))) blank∞
  rw [← Side.prepend_append, ones_append, show 8 + 2 * j = 4 + (2 * j + 4) from by ring]

/-- **Absorb-one** (`4j + 16` steps): one iteration of the flip-absorb loop
    inside the shift rule.  Consumes 2 flip pairs (4 cells) on the left and
    grows the right ones-count by 6.  Composes Phase A + B + C. -/
lemma absorb_one (R : Side) (j : Nat) :
    srun tm
      { state := some stA, head := false,
        left := [true, false, true, false] *> R,
        right := ones (2 * j + 2) *> blank∞ } (4 * j + 16) =
    { state := some stA, head := false,
      left := R,
      right := ones (2 * j + 8) *> blank∞ } := by
  rw [show (4 * j + 16 : Nat) = 3 + ((2 * j + 5) + (2 * j + 8)) from by ring,
      srun_add,
      show (2 * j + 2 : Nat) = (2 * j + 1) + 1 from by ring,
      absorb_phaseA R (2 * j + 1),
      show (2 * j + 1) + 2 = 2 * j + 3 from by ring,
      srun_add, absorb_phaseB R j, absorb_phaseC R j]

/-- **Absorb-iter** (`6*i² + 10*i + 12*t*i` steps): apply `absorb_one` `i`
    times.  Starting from `[T, F] ×× (2*i) *> L` with right `ones (6*t + 2)`,
    consume all flip pairs and grow right to `ones (6*(t+i) + 2)`.

    The `t` parameter tracks the "iteration index" — at outer-level use
    `t = 0` for `right = ones 2`. -/
lemma absorb_iter (L : Side) (t i : Nat) :
    srun tm
      { state := some stA, head := false,
        left := ([true, false] ×× (2 * i)) *> L,
        right := ones (6 * t + 2) *> blank∞ }
      (6 * i * i + 10 * i + 12 * t * i) =
    { state := some stA, head := false,
      left := L,
      right := ones (6 * (t + i) + 2) *> blank∞ } := by
  induction i generalizing t with
  | zero =>
    -- 0 steps, [T, F] ×× 0 = []. Right unchanged.
    simp [srun, listRepeat]
  | succ i' ih =>
    -- 2*(i'+1) = 2*i' + 2 flip pairs.
    -- Peel one absorb_one (consuming 2 pairs), then IH for i' more.
    have hflip : ([true, false] ×× (2 * (i' + 1)) : List Sym)
            = [true, false, true, false] ++ [true, false] ×× (2 * i') := by
      rw [show 2 * (i' + 1) = (2 * i') + 1 + 1 from by ring]
      show [true, false] ++ ([true, false] ++ [true, false] ×× (2 * i'))
         = _
      rfl
    rw [hflip]
    rw [Side.prepend_append]
    -- Now left = [T, F, T, F] *> [T, F] ×× (2*i') *> L.  Apply absorb_one.
    rw [show (6 * (i' + 1) * (i' + 1) + 10 * (i' + 1) + 12 * t * (i' + 1) : Nat)
            = (4 * (3 * t) + 16)
              + (6 * i' * i' + 10 * i' + 12 * (t + 1) * i') from by ring,
        srun_add,
        show (6 * t + 2 : Nat) = 2 * (3 * t) + 2 from by ring,
        absorb_one (([true, false] ×× (2 * i')) *> L) (3 * t),
        show 2 * (3 * t) + 8 = 6 * (t + 1) + 2 from by ring,
        ih (t + 1),
        show t + 1 + i' = t + (i' + 1) from by ring]

/-- Helper: `[false] ++ [true, false] ×× n ++ [true] = zebra (n + 1)`. -/
private lemma false_flip_true (n : Nat) :
    ([false] ++ [true, false] ×× n ++ [true] : List Sym) = zebra (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    -- LHS expansion: [false] ++ ([true, false] ++ [true, false] ×× k) ++ [true]
    --              = [false, true, false] ++ [true, false] ×× k ++ [true]
    --              = [false, true] ++ ([false] ++ [true, false] ×× k ++ [true])
    --              = [false, true] ++ zebra (k+1) [by ih]
    --              = zebra (k+2) [by zebra def]
    show ([false] ++ ([true, false] ++ [true, false] ×× k) ++ [true] : List Sym)
       = zebra (k + 2)
    have step : ([false] ++ ([true, false] ++ [true, false] ×× k) ++ [true] : List Sym)
              = [false, true] ++ ([false] ++ [true, false] ×× k ++ [true]) := by
      simp
    rw [step, ih]
    rfl

/-- Helper: `[false] ++ [true, false] ×× n = zebra n ++ [false]`. -/
private lemma false_flip (n : Nat) :
    ([false] ++ [true, false] ×× n : List Sym) = zebra n ++ [false] := by
  -- Derive from `false_flip_true` by appending `[true]` and using `zebra_succ_append`.
  have h1 : ([false] ++ [true, false] ×× n ++ [true] : List Sym) = zebra (n + 1) :=
    false_flip_true n
  have h2 : (zebra (n + 1) : List Sym) = zebra n ++ [false, true] := zebra_succ_append n
  have h3 : ([false] ++ [true, false] ×× n ++ [true] : List Sym)
          = zebra n ++ [false] ++ [true] := by
    rw [h1, h2, List.append_assoc]; rfl
  -- Cancel trailing `[true]`.
  exact List.append_cancel_right h3

/-- Side-level fold (general): `cons F ([T,F] ×× n *> ones m *> L) =
    zebra n *> [false] *> ones m *> L`. -/
private lemma fold_zebra_g (n m : Nat) (L : Side) :
    Side.cons false (Side.prepend ([true, false] ×× n) (Side.prepend (ones m) L))
      = Side.prepend (zebra n) (Side.prepend [false] (Side.prepend (ones m) L)) := by
  show Side.prepend [false] (Side.prepend ([true, false] ×× n) (Side.prepend (ones m) L))
     = Side.prepend (zebra n) (Side.prepend [false] (Side.prepend (ones m) L))
  rw [← Side.prepend_append, ← Side.prepend_append, false_flip,
      Side.prepend_append, Side.prepend_append]

/-- Closing **Phase α** (m-generalized, 3 steps). -/
private lemma closing_phaseA_g (m : Nat) (L : Side) (i : Nat) :
    srun tm
      { state := some stA, head := false,
        left := ones (m + 4) *> L,
        right := ones (6 * i + 2) *> blank∞ } 3 =
    { state := some stE, head := true,
      left := ones (m + 3) *> L,
      right := ones (6 * i + 3) *> blank∞ } := by
  rw [show Side.prepend (ones (m + 4)) L =
        Side.cons true (Side.prepend (ones (m + 3)) L) from by
      show Side.prepend (ones (m + 3 + 1)) L = _; rfl,
      show Side.prepend (ones (6 * i + 2)) blank∞ =
        Side.cons true (Side.prepend (ones (6 * i + 1)) blank∞) from by
      show Side.prepend (ones (6 * i + 1 + 1)) blank∞ = _; rfl,
      show Side.prepend (ones (6 * i + 3)) blank∞ =
        Side.cons true (Side.cons true (Side.prepend (ones (6 * i + 1)) blank∞)) from by
      show Side.prepend (ones (6 * i + 1 + 1 + 1)) blank∞ = _; rfl]
  simp [srun, sstep, tm, Side.prepend, ones]

/-- Closing **Phase β** (m-generalized, `6i+5` steps). -/
private lemma closing_phaseB_g (m : Nat) (L : Side) (i : Nat) :
    srun tm
      { state := some stE, head := true,
        left := ones (m + 3) *> L,
        right := ones (6 * i + 3) *> blank∞ } (6 * i + 5) =
    { state := some stF, head := false,
      left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 2))
                  (Side.prepend (ones (m + 3)) L)),
      right := blank∞ } := by
  rw [show (6 * i + 5 : Nat) = 2 * (3 * i + 1) + 3 from by ring,
      srun_add,
      show Side.prepend (ones (6 * i + 3)) blank∞ =
        Side.prepend (ones (2 * (3 * i + 1))) (Side.prepend (ones 1) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 2 * (3 * i + 1) + 1 = 6 * i + 3 from by ring],
      EA_shift (3 * i + 1) (Side.prepend (ones (m + 3)) L) (Side.prepend (ones 1) blank∞),
      show Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 2))
              (Side.prepend (ones (m + 3)) L))
        = Side.prepend [false, true, false] (Side.prepend ([true, false] ×× (3 * i + 1))
              (Side.prepend (ones (m + 3)) L)) from by
        rw [show 3 * i + 2 = (3 * i + 1) + 1 from by ring,
            show ([true, false] ×× ((3 * i + 1) + 1) : List Sym)
              = [true, false] ++ [true, false] ×× (3 * i + 1) from rfl,
            Side.prepend_append]
        rfl]
  simp [srun, sstep, tm, Side.prepend, ones]

/-- Closing **Phase γ** (m-generalized, `6i+8` steps). -/
private lemma closing_phaseC_g (m : Nat) (L : Side) (i : Nat) :
    srun tm
      { state := some stF, head := false,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 2))
                  (Side.prepend (ones (m + 3)) L)),
        right := blank∞ } (6 * i + 8) =
    { state := some stE, head := true,
      left := Side.prepend (ones m) L,
      right := ones (6 * i + 8) *> blank∞ } := by
  rw [show (6 * i + 8 : Nat) = 2 + (2 * (3 * i + 1) + 4) from by ring,
      srun_add]
  have h_pre : srun tm
      { state := some stF, head := false,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 2))
                  (Side.prepend (ones (m + 3)) L)),
        right := blank∞ } 2 =
      { state := some stB, head := true,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 1))
                  (Side.prepend (ones (m + 3)) L)),
        right := ones 2 *> blank∞ } := by
    rw [show ([true, false] ×× (3 * i + 2) : List Sym)
          = [true, false] ++ [true, false] ×× (3 * i + 1) from by
        show [true, false] ×× (3 * i + 1 + 1) = _; rfl,
        Side.prepend_append]
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_pre, srun_add, BD_iter (3 * i + 1) (Side.prepend (ones (m + 3)) L) 2]
  -- Post (4 steps): peel [F] *> ones (m+3) → ones m on left, growing right.
  show srun tm
    { state := some stB, head := true,
      left := Side.prepend [false] (Side.prepend (ones (m + 3)) L),
      right := ones (2 + 2 * (3 * i + 1)) *> blank∞ } 4 = _
  rw [show (2 + 2 * (3 * i + 1) : Nat) = 4 + 6 * i from by ring,
      show Side.prepend (ones (4 + 6 * i)) blank∞ =
        Side.prepend (ones 4) (Side.prepend (ones (6 * i)) blank∞) from by
      rw [← Side.prepend_append, ones_append],
      show Side.prepend (ones (m + 3)) L
            = Side.cons true (Side.cons true (Side.cons true
                (Side.prepend (ones m) L))) from by
        show Side.prepend (ones (m + 2 + 1)) L = _
        show Side.cons true (Side.prepend (ones (m + 2)) L) = _
        show Side.cons true (Side.cons true (Side.prepend (ones (m + 1)) L)) = _
        rfl]
  simp [srun, sstep, tm, Side.prepend, ones]
  show (Side.prepend (ones 8) (Side.prepend (ones (6 * i)) blank∞) : Side)
     = Side.prepend (ones (2 + (2 * (3 * i + 1) + 4))) blank∞
  rw [← Side.prepend_append, ones_append,
      show 8 + 6 * i = 2 + (2 * (3 * i + 1) + 4) from by ring]

/-- Closing **Phase δ** (m-generalized, `6i+9` steps). -/
private lemma closing_phaseD_g (m : Nat) (L : Side) (i : Nat) :
    srun tm
      { state := some stE, head := true,
        left := Side.prepend (ones m) L,
        right := ones (6 * i + 8) *> blank∞ } (6 * i + 9) =
    { state := some stA, head := false,
      left := Side.prepend (zebra (3 * i + 4)) (Side.prepend [false]
              (Side.prepend (ones m) L)),
      right := blank∞ } := by
  rw [show (6 * i + 9 : Nat) = 2 * (3 * i + 4) + 1 from by ring, srun_add,
      show Side.prepend (ones (6 * i + 8)) blank∞ =
        Side.prepend (ones (2 * (3 * i + 4))) blank∞ from by
        congr 1; congr 1; ring,
      EA_shift (3 * i + 4) (Side.prepend (ones m) L) blank∞,
      ← fold_zebra_g (3 * i + 4) m L]
  simp [srun, sstep, tm, Side.prepend, ones]

/-- **Closing-phase (general)** (linear `18i + 25` steps): from `state A head=F`
    with `left = ones (m+4) *> L` and `right = ones (6i+2) *> blank`, run to
    `state A head=F, left = zebra (3i+4) *> [false] *> ones m *> L, right = blank`.

    Specializations: m=1 ⇒ shift_even_high's closing (`zebra (3i+5) *> L`
    Side-equal); m=0 ⇒ shift_m4_even's closing. -/
lemma closing_phase_g (m : Nat) (L : Side) (i : Nat) :
    srun tm
      { state := some stA, head := false,
        left := ones (m + 4) *> L,
        right := ones (6 * i + 2) *> blank∞ } (18 * i + 25) =
    { state := some stA, head := false,
      left := zebra (3 * i + 4) *> [false] *> ones m *> L,
      right := blank∞ } := by
  rw [show (18 * i + 25 : Nat) = 3 + ((6 * i + 5) + ((6 * i + 8) + (6 * i + 9))) from by ring,
      srun_add, closing_phaseA_g m L i, srun_add, closing_phaseB_g m L i,
      srun_add, closing_phaseC_g m L i, closing_phaseD_g m L i]

/-- **Shift_even_general** (parameterized over an abstract left-tail `L`).

    Given `state A head=F` with `left = zebra (2i) *> [false] *> ones 4 *> L`
    and blank right tape, after `6i² + 28i + 28` steps reach
    `state A head=F, left = zebra (3i+4) *> [false] *> L, right = blank`.

    The `ones 4` is the *active* ones-block consumed by the closing phase.
    Whatever lies beyond (`L`) is untouched.  Specializations:

    - `L = ones (m+1) *> blank∞` ⇒ recovers `shift_even_high` (LHS `ones 5`
      becomes `ones 4 *> ones (m+1) = ones (m+5)`; RHS adds `[false] *> ones (m+1) *> blank` = `[false] *> ones (m+1) *> blank` after the zebra).
    - `L = blank∞` ⇒ recovers `shift_m4_even` (LHS `ones 4 *> blank`; RHS
      `zebra (3i+4) *> [false] *> blank` is Side-equal to `zebra (3i+3) *>
      [false] *> ones 1 *> blank` = A(1, 3i+3) via `[false] *> blank = blank`
      and `zebra_succ_append`). -/
lemma shift_even_general (L : Side) (i : Nat) :
    srun tm
      { state := some stA, head := false,
        left := zebra (2 * i) *> [false] *> ones 4 *> L,
        right := blank∞ } (6*i*i + 28*i + 28) =
    { state := some stA, head := false,
      left := zebra (3 * i + 4) *> [false] *> L,
      right := blank∞ } := by
  rw [show (6 * i * i + 28 * i + 28 : Nat)
          = 3 + ((6 * i * i + 10 * i + 12 * 0 * i) + (18 * i + 25)) from by ring,
      srun_add, right_push_g (Side.prepend (ones 4) L) i, srun_add,
      show (ones 2 : List Sym) = ones (6 * 0 + 2) from by rfl,
      absorb_iter (Side.prepend (ones 4) L) 0 i,
      show 0 + i = i from by ring,
      show Side.prepend (ones 4) L = Side.prepend (ones (0 + 4)) L from rfl,
      closing_phase_g 0 L i,
      show Side.prepend (ones 0) L = L from rfl]

/-- **Shift_even** (`dt = 6i² + 28i + 28`).  For any `m ≥ 0` and `i ≥ 0`:
    `A(m+4, 2i) → A(m+1, 3i+4)` is the "high-m" shift rule.

    NB: we state this with `m + 1` on the RHS rather than `m` to keep all
    parameters `≥ 1` uniformly.  Equivalent to the wiki's
    `A(m'+4, 2i) → A(m', 3i+4)` for `m' = m + 1 ≥ 1`.
-/
theorem shift_even_high (m i : Nat) :
    srun tm (A_config (m + 1 + 4) (2 * i)) (6*i*i + 28*i + 28) =
      A_config (m + 1) (3 * i + 4) := by
  unfold A_config
  -- Massage `ones (m+5) *> blank` into `ones 4 *> ones (m+1) *> blank` to fit
  -- `shift_even_general`'s input form.
  rw [show Side.prepend (ones (m + 1 + 4)) blank∞ =
        Side.prepend (ones 4) (Side.prepend (ones (m + 1)) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 4 + (m + 1) = m + 1 + 4 from by ring],
      shift_even_general (Side.prepend (ones (m + 1)) blank∞) i]

/-- Closing **Phase γ** parameterized by `j` (= flip pair count − 1).
    For `j = 3*i+1`: recovers `closing_phaseC_g` (cost `6i+8`).
    For `j = 3*i+3`: used by pivot_residual_close (cost `6i+12`). -/
private lemma closing_phaseC_p (m : Nat) (L : Side) (j : Nat) :
    srun tm
      { state := some stF, head := false,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (j + 1))
                  (Side.prepend (ones (m + 3)) L)),
        right := blank∞ } (2 * j + 6) =
    { state := some stE, head := true,
      left := Side.prepend (ones m) L,
      right := ones (2 * j + 6) *> blank∞ } := by
  rw [show (2 * j + 6 : Nat) = 2 + (2 * j + 4) from by ring, srun_add]
  have h_pre : srun tm
      { state := some stF, head := false,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (j + 1))
                  (Side.prepend (ones (m + 3)) L)),
        right := blank∞ } 2 =
      { state := some stB, head := true,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× j)
                  (Side.prepend (ones (m + 3)) L)),
        right := ones 2 *> blank∞ } := by
    rw [show ([true, false] ×× (j + 1) : List Sym)
          = [true, false] ++ [true, false] ×× j from rfl,
        Side.prepend_append]
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_pre, srun_add, BD_iter j (Side.prepend (ones (m + 3)) L) 2]
  show srun tm
    { state := some stB, head := true,
      left := Side.prepend [false] (Side.prepend (ones (m + 3)) L),
      right := ones (2 + 2 * j) *> blank∞ } 4 = _
  rw [show Side.prepend (ones (2 + 2 * j)) blank∞ =
        Side.prepend (ones 2) (Side.prepend (ones (2 * j)) blank∞) from by
        rw [← Side.prepend_append, ones_append],
      show Side.prepend (ones (m + 3)) L
        = Side.cons true (Side.cons true (Side.cons true (Side.prepend (ones m) L))) from by
        show Side.prepend (ones (m + 2 + 1)) L = _
        show Side.cons true (Side.prepend (ones (m + 2)) L) = _
        show Side.cons true (Side.cons true (Side.prepend (ones (m + 1)) L)) = _
        rfl]
  simp [srun, sstep, tm, Side.prepend, ones]
  show (Side.prepend (ones 6) (Side.prepend (ones (2 * j)) blank∞) : Side)
     = Side.prepend (ones (2 + (2 * j + 4))) blank∞
  rw [← Side.prepend_append, ones_append, show 6 + 2 * j = 2 + (2 * j + 4) from by ring]

/-- Closing **Phase δ** parameterized by `j`.
    For `j = 3*i+1`: recovers `closing_phaseD_g` (cost `6i+9`, output `zebra (3i+4)`).
    For `j = 3*i+3`: used by pivot_residual_close (cost `6i+13`, output `zebra (3i+6)`). -/
private lemma closing_phaseD_p (m : Nat) (L : Side) (j : Nat) :
    srun tm
      { state := some stE, head := true,
        left := Side.prepend (ones m) L,
        right := ones (2 * j + 6) *> blank∞ } (2 * j + 7) =
    { state := some stA, head := false,
      left := Side.prepend (zebra (j + 3)) (Side.prepend [false]
              (Side.prepend (ones m) L)),
      right := blank∞ } := by
  rw [show (2 * j + 7 : Nat) = 2 * (j + 3) + 1 from by ring, srun_add,
      show (2 * j + 6 : Nat) = 2 * (j + 3) from by ring,
      EA_shift (j + 3) (Side.prepend (ones m) L) blank∞,
      ← fold_zebra_g (j + 3) m L]
  simp [srun, sstep, tm, Side.prepend, ones]

/-- **Pivot Phase 0** (3 steps): A → B → D → E.  Constant prelude inside
    pivot_residual_close, consuming the `[T, F]` residual's first cell. -/
private lemma pivot_phase0 (L : Side) (i : Nat) :
    srun tm
      { state := some stA, head := false,
        left := [true, false] *> ones 4 *> L,
        right := ones (6 * i + 2) *> blank∞ } 3 =
    { state := some stE, head := true,
      left := Side.prepend [false] (Side.prepend (ones 4) L),
      right := ones (6 * i + 3) *> blank∞ } := by
  rw [show Side.prepend (ones (6 * i + 2)) blank∞ =
        Side.cons true (Side.prepend (ones (6 * i + 1)) blank∞) from by
      show Side.prepend (ones (6 * i + 1 + 1)) blank∞ = _; rfl,
      show Side.prepend (ones (6 * i + 3)) blank∞ =
        Side.cons true (Side.cons true (Side.prepend (ones (6 * i + 1)) blank∞)) from by
      show Side.prepend (ones (6 * i + 1 + 1 + 1)) blank∞ = _; rfl]
  simp [srun, sstep, tm, Side.prepend, ones]

/-- **Pivot Phase 1** (`6i+5` steps): EA-cycle through `6i+3` right ones plus
    3 finalizing steps reaching state F.  Mirrors `closing_phaseB_g` but with
    an extra `[F]` between the flip prefix and the ones block. -/
private lemma pivot_phase1 (L : Side) (i : Nat) :
    srun tm
      { state := some stE, head := true,
        left := Side.prepend [false] (Side.prepend (ones 4) L),
        right := ones (6 * i + 3) *> blank∞ } (6 * i + 5) =
    { state := some stF, head := false,
      left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 2))
              (Side.prepend [false] (Side.prepend (ones 4) L))),
      right := blank∞ } := by
  rw [show (6 * i + 5 : Nat) = 2 * (3 * i + 1) + 3 from by ring,
      srun_add,
      show Side.prepend (ones (6 * i + 3)) blank∞ =
        Side.prepend (ones (2 * (3 * i + 1))) (Side.prepend (ones 1) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 2 * (3 * i + 1) + 1 = 6 * i + 3 from by ring],
      EA_shift (3 * i + 1) (Side.prepend [false] (Side.prepend (ones 4) L))
        (Side.prepend (ones 1) blank∞),
      show Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 2))
              (Side.prepend [false] (Side.prepend (ones 4) L)))
        = Side.prepend [false, true, false] (Side.prepend ([true, false] ×× (3 * i + 1))
              (Side.prepend [false] (Side.prepend (ones 4) L))) from by
        rw [show 3 * i + 2 = (3 * i + 1) + 1 from by ring,
            show ([true, false] ×× ((3 * i + 1) + 1) : List Sym)
              = [true, false] ++ [true, false] ×× (3 * i + 1) from rfl,
            Side.prepend_append]
        rfl]
  simp [srun, sstep, tm, Side.prepend, ones]

/-- **Pivot Phase 2** (`6i+8` steps): F-sweep back through the flip prefix,
    crossing the `[F, F]` separator, ending at state A head=T with `ones 2 *> L`. -/
private lemma pivot_phase2 (L : Side) (i : Nat) :
    srun tm
      { state := some stF, head := false,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 2))
                  (Side.prepend [false] (Side.prepend (ones 4) L))),
        right := blank∞ } (6 * i + 8) =
    { state := some stA, head := true,
      left := Side.prepend (ones 2) L,
      right := ones (6 * i + 8) *> blank∞ } := by
  -- Preamble (2 steps): F → D → B at state B head=T with one [T,F] pair consumed.
  rw [show (6 * i + 8 : Nat) = 2 + ((2 * (3 * i + 1)) + 4) from by ring,
      srun_add]
  have h_pre : srun tm
      { state := some stF, head := false,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 2))
                  (Side.prepend [false] (Side.prepend (ones 4) L))),
        right := blank∞ } 2 =
      { state := some stB, head := true,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 1))
                  (Side.prepend [false] (Side.prepend (ones 4) L))),
        right := ones 2 *> blank∞ } := by
    rw [show ([true, false] ×× (3 * i + 2) : List Sym)
          = [true, false] ++ [true, false] ×× (3 * i + 1) from by
        show [true, false] ×× (3 * i + 1 + 1) = _; rfl,
        Side.prepend_append]
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_pre, srun_add,
      BD_iter (3 * i + 1) (Side.prepend [false] (Side.prepend (ones 4) L)) 2]
  -- Terminator (4 steps): B → D → B → C → A consuming [F, F] *> first 2 ones of `ones 4`.
  show srun tm
    { state := some stB, head := true,
      left := Side.prepend [false] (Side.prepend [false] (Side.prepend (ones 4) L)),
      right := ones (2 + 2 * (3 * i + 1)) *> blank∞ } 4 = _
  rw [show Side.prepend (ones (2 + 2 * (3 * i + 1))) blank∞ =
        Side.prepend (ones 2) (Side.prepend (ones (2 * (3 * i + 1))) blank∞) from by
        rw [← Side.prepend_append, ones_append],
      show Side.prepend [false] (Side.prepend [false] (Side.prepend (ones 4) L))
        = Side.cons false (Side.cons false (Side.cons true (Side.cons true
            (Side.prepend (ones 2) L)))) from by
        show Side.prepend [false] (Side.prepend [false]
              (Side.prepend (ones (1 + 1 + 2)) L)) = _
        show Side.prepend [false] (Side.prepend [false]
              (Side.cons true (Side.prepend (ones (1 + 2)) L))) = _
        show Side.prepend [false] (Side.prepend [false]
              (Side.cons true (Side.cons true (Side.prepend (ones 2) L)))) = _
        rfl]
  simp [srun, sstep, tm, Side.prepend, ones]
  show (Side.prepend (ones 6) (Side.prepend (ones (2 * (3 * i + 1))) blank∞) : Side)
     = Side.prepend (ones (2 + (2 * (3 * i + 1) + 4))) blank∞
  rw [← Side.prepend_append, ones_append,
      show 6 + 2 * (3 * i + 1) = 2 + (2 * (3 * i + 1) + 4) from by ring]

/-- **Pivot Phase 3** (`6i+10` steps): step 1 (A→E) + EA-cycle through `6i+6`
    right ones + 3 final steps reaching state F at the F-sweep start config. -/
private lemma pivot_phase3 (L : Side) (i : Nat) :
    srun tm
      { state := some stA, head := true,
        left := Side.prepend (ones 2) L,
        right := ones (6 * i + 8) *> blank∞ } (6 * i + 10) =
    { state := some stF, head := false,
      left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 4))
                (Side.prepend (ones 3) L)),
      right := blank∞ } := by
  rw [show (6 * i + 10 : Nat) = 1 + ((6 * i + 6) + 3) from by ring, srun_add]
  -- Step 1 (A,1→1RE): consume 1 right T, push T to left, state E.
  have h_step1 : srun tm
      { state := some stA, head := true,
        left := Side.prepend (ones 2) L,
        right := ones (6 * i + 8) *> blank∞ } 1 =
      { state := some stE, head := true,
        left := Side.prepend (ones 3) L,
        right := ones (6 * i + 7) *> blank∞ } := by
    rw [show Side.prepend (ones (6 * i + 8)) blank∞ =
          Side.cons true (Side.prepend (ones (6 * i + 7)) blank∞) from by
        show Side.prepend (ones (6 * i + 7 + 1)) blank∞ = _; rfl]
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_step1, srun_add,
      show (6 * i + 6 : Nat) = 2 * (3 * i + 3) from by ring,
      -- Split right: ones (6i+7) = ones (2*(3i+3)) ++ ones 1.
      show Side.prepend (ones (6 * i + 7)) blank∞ =
        Side.prepend (ones (2 * (3 * i + 3))) (Side.prepend (ones 1) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 2 * (3 * i + 3) + 1 = 6 * i + 7 from by ring],
      -- EA_shift: 2*(3i+3) = 6i+6 steps; head stays T (next cell is the lone T).
      EA_shift (3 * i + 3) (Side.prepend (ones 3) L) (Side.prepend (ones 1) blank∞)]
  -- Now state E head=T, left = [T,F]××(3i+3) *> ones 3 *> L, right = [T] *> blank.
  -- 3 final steps: (E,T→0RA), (A,T→1RE), (E,F→0RF).
  -- Convert target's `[T,F] ×× (3i+4)` to `[T,F] ++ [T,F] ×× (3i+3)` so simp matches.
  rw [show ([true, false] ×× (3 * i + 4) : List Sym)
        = [true, false] ++ [true, false] ×× (3 * i + 3) from by
        show [true, false] ×× ((3 * i + 3) + 1) = _; rfl,
      Side.prepend_append]
  simp [srun, sstep, tm, Side.prepend, ones]

/-- **Pivot residual close** (`30i + 51` steps).  Closes the residual `[T, F]`
    pivot configuration into a `zebra (3i+6) *> [false] *> L` form.

    Composes pivot_phase0..3 (the 18i+23-step "novel dynamics") with
    closing_phaseC_p (j=3i+3, m=0) and closing_phaseD_p (j=3i+3, m=0). -/
lemma pivot_residual_close (L : Side) (i : Nat) :
    srun tm
      { state := some stA, head := false,
        left := Side.prepend [true, false] (Side.prepend (ones 4) L),
        right := ones (6 * i + 2) *> blank∞ } (30 * i + 51) =
    { state := some stA, head := false,
      left := Side.prepend (zebra (3 * i + 6)) (Side.prepend [false] L),
      right := blank∞ } := by
  rw [show (30 * i + 51 : Nat)
        = 3 + ((6 * i + 5) + ((6 * i + 8) + ((6 * i + 10) +
            ((2 * (3 * i + 3) + 6) + (2 * (3 * i + 3) + 7)))))
        from by ring,
      srun_add, pivot_phase0 L i,
      srun_add, pivot_phase1 L i,
      srun_add, pivot_phase2 L i,
      srun_add, pivot_phase3 L i,
      srun_add, closing_phaseC_p 0 L (3 * i + 3),
      closing_phaseD_p 0 L (3 * i + 3),
      show (3 * i + 3 + 3 : Nat) = 3 * i + 6 from by ring,
      show Side.prepend (ones 0) L = L from rfl]

/-- **Shift_odd** (`dt = 6i² + 40i + 54`).  For any `m ≥ 0` and `i ≥ 0`:
    `A(m+5, 2i+1) → A(m+1, 3i+6)`.

    Reduces to `right_push_g` (3 steps) + `absorb_iter` (i iterations,
    `6i² + 10i` steps) + `pivot_residual_close` (`30i + 51` steps).
    The key Side rewrite `zebra (2i+1) *> [false] *> R = zebra (2i) *> [false]
    *> [true, false] *> R` lets us reuse `right_push_g`. -/
theorem shift_odd_high (m i : Nat) :
    srun tm (A_config (m + 1 + 4) (2 * i + 1)) (6*i*i + 40*i + 54) =
      A_config (m + 1) (3 * i + 6) := by
  unfold A_config
  -- Rewrite LHS: zebra (2i+1) *> [false] *> ones (m+5) *> blank
  --            = zebra (2i) *> [false] *> [true, false] *> ones (m+5) *> blank.
  -- Then ones (m+5) = ones 4 ++ ones (m+1) lets us factor the active window.
  have h_left :
      Side.prepend (zebra (2 * i + 1))
        (Side.prepend [false] (Side.prepend (ones (m + 1 + 4)) blank∞))
      = Side.prepend (zebra (2 * i))
          (Side.prepend [false] (Side.prepend [true, false]
            (Side.prepend (ones 4) (Side.prepend (ones (m + 1)) blank∞)))) := by
    -- Collapse all prepends to single-list form, prove list equality, expand back.
    simp only [← Side.prepend_append]
    congr 1
    rw [show (zebra (2 * i + 1) : List Sym) = zebra (2 * i) ++ [false, true] from
          zebra_succ_append (2 * i),
        show (ones (m + 1 + 4) : List Sym) = ones 4 ++ ones (m + 1) from by
          rw [ones_append, show 4 + (m + 1) = m + 1 + 4 from by ring]]
    simp [List.append_assoc]
  rw [h_left,
      show (6 * i * i + 40 * i + 54 : Nat)
          = 3 + ((6 * i * i + 10 * i + 12 * 0 * i) + (30 * i + 51)) from by ring,
      srun_add,
      right_push_g (Side.prepend [true, false]
                    (Side.prepend (ones 4) (Side.prepend (ones (m + 1)) blank∞))) i,
      srun_add,
      show (ones 2 : List Sym) = ones (6 * 0 + 2) from by rfl,
      -- After right_push: left = [T,F]××(2i) *> [T,F] *> ones 4 *> ones (m+1) *> blank.
      -- Absorb_iter consumes the 2i pairs, leaving [T,F] *> ones 4 *> ones (m+1) *> blank.
      show Side.prepend ([true, false] ×× (2 * i))
            (Side.prepend [true, false]
              (Side.prepend (ones 4) (Side.prepend (ones (m + 1)) blank∞)))
        = Side.prepend ([true, false] ×× (2 * i))
            (Side.prepend ([true, false] ++ ones 4)
              (Side.prepend (ones (m + 1)) blank∞)) from by
        rw [Side.prepend_append],
      absorb_iter
        (Side.prepend ([true, false] ++ ones 4)
          (Side.prepend (ones (m + 1)) blank∞)) 0 i,
      show 0 + i = i from by ring,
      show Side.prepend ([true, false] ++ ones 4)
            (Side.prepend (ones (m + 1)) blank∞)
         = Side.prepend [true, false]
            (Side.prepend (ones 4) (Side.prepend (ones (m + 1)) blank∞)) from by
        rw [Side.prepend_append],
      pivot_residual_close (Side.prepend (ones (m + 1)) blank∞) i,
      show Side.prepend [false] (Side.prepend (ones (m + 1)) blank∞)
         = Side.prepend [false] (Side.prepend (ones (m + 1)) blank∞) from rfl]

-- ============================================================
-- m = 4 bridge  (RHS m = 0 is canonically A(1, n-1))
-- ============================================================

/-- **Shift_m4_even** (`dt = 6i² + 28i + 28`).  `A(4, 2i) → A(1, 3i+3)`.

    Discharged from `shift_even_general` with `L = blank`, plus a Side-equality
    bridge `zebra (3i+4) *> [false] *> blank = zebra (3i+3) *> [false] *> ones 1 *> blank`
    (via `cons F blank = blank` and `zebra_succ_append`). -/
theorem shift_m4_even (i : Nat) :
    srun tm (A_config 4 (2 * i)) (6*i*i + 28*i + 28) =
      A_config 1 (3 * i + 3) := by
  unfold A_config
  -- Massage LHS into the form expected by `shift_even_general`.
  rw [show (ones 4 : List Sym) = ones 4 ++ [] from by simp,
      show Side.prepend (ones 4 ++ []) blank∞ = Side.prepend (ones 4) blank∞ from by
        rw [List.append_nil],
      shift_even_general blank∞ i]
  -- Reconcile RHS Sides: zebra (3i+4) *> [false] *> blank
  --   = zebra (3i+3) *> [false] *> ones 1 *> blank.
  congr 1
  -- LHS Side: zebra (3i+4) *> [false] *> blank.
  -- RHS Side: zebra (3i+3) *> [false] *> ones 1 *> blank = zebra (3i+4) *> blank
  --   (via zebra_succ_append).  And [false] *> blank = blank (cons_false_blank).
  show Side.prepend (zebra (3 * i + 4)) (Side.prepend [false] blank∞)
     = Side.prepend (zebra (3 * i + 3)) (Side.prepend [false] (Side.prepend (ones 1) blank∞))
  rw [show Side.prepend [false] blank∞ = blank∞ from Side.cons_false_blank,
      show Side.prepend (ones 1) blank∞ = Side.prepend [true] blank∞ from rfl,
      ← Side.prepend_append, ← Side.prepend_append,
      show (zebra (3 * i + 3) ++ [false] ++ [true] : List Sym) = zebra (3 * i + 4) from by
        rw [List.append_assoc,
            show ([false] ++ [true] : List Sym) = [false, true] from rfl,
            ← zebra_succ_append, show 3 * i + 3 + 1 = 3 * i + 4 from by ring]]

/-- **Shift_m4_odd** (`dt = 6i² + 40i + 54`).  `A(4, 2i+1) → A(1, 3i+5)`.

    Discharged from the same shift_odd_high pipeline (right_push_g, absorb_iter,
    pivot_residual_close) using `L = blank`, plus a final Side-equality bridge
    `zebra (3i+6) *> [F] *> blank = zebra (3i+5) *> [F] *> ones 1 *> blank`. -/
theorem shift_m4_odd (i : Nat) :
    srun tm (A_config 4 (2 * i + 1)) (6*i*i + 40*i + 54) =
      A_config 1 (3 * i + 5) := by
  unfold A_config
  have h_left :
      Side.prepend (zebra (2 * i + 1))
        (Side.prepend [false] (Side.prepend (ones 4) blank∞))
      = Side.prepend (zebra (2 * i))
          (Side.prepend [false] (Side.prepend [true, false]
            (Side.prepend (ones 4) blank∞))) := by
    simp only [← Side.prepend_append]
    congr 1
    rw [show (zebra (2 * i + 1) : List Sym) = zebra (2 * i) ++ [false, true] from
          zebra_succ_append (2 * i)]
    simp [List.append_assoc]
  rw [h_left,
      show (6 * i * i + 40 * i + 54 : Nat)
          = 3 + ((6 * i * i + 10 * i + 12 * 0 * i) + (30 * i + 51)) from by ring,
      srun_add,
      right_push_g (Side.prepend [true, false]
                    (Side.prepend (ones 4) blank∞)) i,
      srun_add,
      show (ones 2 : List Sym) = ones (6 * 0 + 2) from by rfl,
      show Side.prepend ([true, false] ×× (2 * i))
            (Side.prepend [true, false]
              (Side.prepend (ones 4) blank∞))
        = Side.prepend ([true, false] ×× (2 * i))
            (Side.prepend ([true, false] ++ ones 4) blank∞) from by
        rw [Side.prepend_append],
      absorb_iter
        (Side.prepend ([true, false] ++ ones 4) blank∞) 0 i,
      show 0 + i = i from by ring,
      show Side.prepend ([true, false] ++ ones 4) blank∞
         = Side.prepend [true, false] (Side.prepend (ones 4) blank∞) from by
        rw [Side.prepend_append],
      pivot_residual_close blank∞ i]
  -- Bridge: zebra (3*i+6) *> [F] *> blank = zebra (3*i+5) *> [F] *> ones 1 *> blank.
  congr 1
  show Side.prepend (zebra (3 * i + 6)) (Side.prepend [false] blank∞)
     = Side.prepend (zebra (3 * i + 5)) (Side.prepend [false] (Side.prepend (ones 1) blank∞))
  rw [show Side.prepend [false] blank∞ = blank∞ from Side.cons_false_blank,
      show Side.prepend (ones 1) blank∞ = Side.prepend [true] blank∞ from rfl,
      ← Side.prepend_append, ← Side.prepend_append,
      show (zebra (3 * i + 5) ++ [false] ++ [true] : List Sym) = zebra (3 * i + 6) from by
        rw [List.append_assoc,
            show ([false] ++ [true] : List Sym) = [false, true] from rfl,
            ← zebra_succ_append, show 3 * i + 5 + 1 = 3 * i + 6 from by ring]]

-- ============================================================
-- Small-m rules  (m = 1, 2, 3)
-- ============================================================

-- ============================================================
-- closing_halt phase lemmas (used by m1_even_halt)
-- ============================================================

/-- **m1-Phase 1** (3 steps, A→B→D→E): from `{A, F, ones 1, ones (6i+2)}` to
    `{E, T, blank, ones (6i+3)}`. -/
private lemma m1_phase1 (i : Nat) :
    srun tm
      { state := some stA, head := false,
        left := Side.prepend (ones 1) blank∞,
        right := Side.prepend (ones (6 * i + 2)) blank∞ } 3 =
    { state := some stE, head := true,
      left := blank∞,
      right := Side.prepend (ones (6 * i + 3)) blank∞ } := by
  rw [show Side.prepend (ones (6 * i + 2)) blank∞ =
        Side.prepend (ones 2) (Side.prepend (ones (6 * i)) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 2 + 6 * i = 6 * i + 2 from by ring],
      show Side.prepend (ones (6 * i + 3)) blank∞ =
        Side.prepend (ones 3) (Side.prepend (ones (6 * i)) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 3 + 6 * i = 6 * i + 3 from by ring]]
  simp [srun, sstep, tm, Side.prepend, ones]

/-- **m1-Phase 2** (`6i+4` steps, EA-cycle + 2 finalizing): from `{E, T, blank,
    ones (6i+3)}` to `{E, F, [T,F]××(3i+2)*>blank, blank}`.

    Decomposes as `EA_shift k=3i+1` (consumes `ones (6i+2)`, prepends
    `[T,F]××(3i+1)`) + 2 finalizing steps (E,T→0RA + A,T→1RE). -/
private lemma m1_phase2 (i : Nat) :
    srun tm
      { state := some stE, head := true,
        left := blank∞,
        right := Side.prepend (ones (6 * i + 3)) blank∞ } (6 * i + 4) =
    { state := some stE, head := false,
      left := Side.prepend ([true, false] ×× (3 * i + 2)) blank∞,
      right := blank∞ } := by
  rw [show (6 * i + 4 : Nat) = 2 * (3 * i + 1) + 2 from by ring,
      srun_add,
      show Side.prepend (ones (6 * i + 3)) blank∞ =
        Side.prepend (ones (2 * (3 * i + 1))) (Side.prepend (ones 1) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 2 * (3 * i + 1) + 1 = 6 * i + 3 from by ring],
      EA_shift (3 * i + 1) blank∞ (Side.prepend (ones 1) blank∞),
      -- Convert target left's [T,F]××(3i+2) into [T,F] ++ [T,F]××(3i+1).
      show ([true, false] ×× (3 * i + 2) : List Sym)
        = [true, false] ++ [true, false] ×× (3 * i + 1) from by
        show [true, false] ×× ((3 * i + 1) + 1) = _; rfl,
      Side.prepend_append]
  simp [srun, sstep, tm, Side.prepend, ones]

/-- **m1-Phase 3** (1 step, E,F→0RF): from `{E, F, [T,F]××(3i+2)*>blank, blank}`
    to `{F, F, [F]*>[T,F]××(3i+2)*>blank, blank}`. -/
private lemma m1_phase3 (i : Nat) :
    srun tm
      { state := some stE, head := false,
        left := Side.prepend ([true, false] ×× (3 * i + 2)) blank∞,
        right := blank∞ } 1 =
    { state := some stF, head := false,
      left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 2)) blank∞),
      right := blank∞ } := by
  simp [srun, sstep, tm, Side.prepend, ones]

/-- **m1-Phase 4** (`6i+7` steps, F-sweep + BD-iter + tail): from
    `{F, F, [F]*>[T,F]××(3i+2)*>blank, blank}` to
    `{C, F, blank, ones (6i+7)*>blank}`.

    Decomposes as: F→D (1) + D→B init (1) + `BD_iter k=3i+1` (`6i+2`) +
    3 final steps (B,T→D,F → D,F→B,F → B,F→C,F). -/
private lemma m1_phase4 (i : Nat) :
    srun tm
      { state := some stF, head := false,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 2)) blank∞),
        right := blank∞ } (6 * i + 7) =
    { state := some stC, head := false,
      left := blank∞,
      right := Side.prepend (ones (6 * i + 7)) blank∞ } := by
  rw [show (6 * i + 7 : Nat) = 1 + (1 + (2 * (3 * i + 1) + 3)) from by ring, srun_add]
  -- Step 1 (F,F→1LD): pull leading [F], push T to right. State D head=F.
  have h_step1 : srun tm
      { state := some stF, head := false,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 2)) blank∞),
        right := blank∞ } 1 =
      { state := some stD, head := false,
        left := Side.prepend ([true, false] ×× (3 * i + 2)) blank∞,
        right := Side.prepend (ones 1) blank∞ } := by
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_step1, srun_add,
      -- Convert left from [T,F]××(3i+2) to [T,F]*>[T,F]××(3i+1).
      show ([true, false] ×× (3 * i + 2) : List Sym)
        = [true, false] ++ [true, false] ×× (3 * i + 1) from by
        show [true, false] ×× ((3 * i + 1) + 1) = _; rfl,
      Side.prepend_append]
  -- Step 2 (D,F→1LB): pull T from [T,F]××-pair, state B head=T.
  have h_step2 : srun tm
      { state := some stD, head := false,
        left := Side.prepend [true, false]
                  (Side.prepend ([true, false] ×× (3 * i + 1)) blank∞),
        right := Side.prepend (ones 1) blank∞ } 1 =
      { state := some stB, head := true,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 1)) blank∞),
        right := Side.prepend (ones 2) blank∞ } := by
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_step2, srun_add,
      BD_iter (3 * i + 1) blank∞ 2,
      show Side.prepend [false] blank∞ = blank∞ from Side.cons_false_blank,
      show Side.prepend (ones (2 + 2 * (3 * i + 1))) blank∞ =
        Side.prepend (ones 1) (Side.prepend (ones (6 * i + 3)) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 1 + (6 * i + 3) = 2 + 2 * (3 * i + 1) from by ring]]
  simp [srun, sstep, tm, Side.prepend, ones]
  show Side.prepend (ones 7) (Side.prepend (ones (6 * i)) blank∞) =
    Side.prepend (ones (1 + (1 + (2 * (3 * i + 1) + 3)))) blank∞
  rw [← Side.prepend_append, ones_append,
      show 7 + 6 * i = 1 + (1 + (2 * (3 * i + 1) + 3)) from by ring]

/-- **closing_halt** (`12i+15` steps): from `{A, F, ones 1, ones (6i+2)}` to
    `{C, F, blank, ones (6i+7)}`.  Composes `m1_phase{1..4}`. -/
private lemma closing_halt (i : Nat) :
    srun tm
      { state := some stA, head := false,
        left := Side.prepend (ones 1) blank∞,
        right := Side.prepend (ones (6 * i + 2)) blank∞ } (12 * i + 15) =
    { state := some stC, head := false,
      left := blank∞,
      right := Side.prepend (ones (6 * i + 7)) blank∞ } := by
  rw [show (12 * i + 15 : Nat) = 3 + ((6 * i + 4) + (1 + (6 * i + 7))) from by ring,
      srun_add, m1_phase1 i,
      srun_add, m1_phase2 i,
      srun_add, m1_phase3 i,
      m1_phase4 i]

/-- **m=1 even → halt** (`dt = 6i² + 22i + 19` Lean-step count).

    Note: `sim.py`/`verify_dt.py` report `dt = 18` for `i = 0` because sim's
    `t.steps` does not count the halting (None) transition.  In Lean's `sstep`
    model, transitioning from `state C, head=F` into `state = none` IS a step;
    so Lean's count is sim's + 1 for halt rules.  Same convention adjustment
    applies to `m2_even_halt` and `m2_odd_halt`.

    Decomposition: `right_push_g` (3) + `absorb_iter L=ones 1 t=0` (`6i²+10i`)
    + `closing_halt` (`12i+15`) + halt step (1) = `6i²+22i+19`. -/
theorem m1_even_halt (i : Nat) :
    (srun tm (A_config 1 (2 * i)) (6*i*i + 22*i + 19)).state = none := by
  unfold A_config
  rw [show (6 * i * i + 22 * i + 19 : Nat)
        = 3 + ((6 * i * i + 10 * i + 12 * 0 * i) + ((12 * i + 15) + 1)) from by ring,
      srun_add,
      right_push_g (Side.prepend (ones 1) blank∞) i,
      srun_add,
      show (ones 2 : List Sym) = ones (6 * 0 + 2) from rfl,
      absorb_iter (Side.prepend (ones 1) blank∞) 0 i,
      show 0 + i = i from by ring,
      srun_add, closing_halt i]
  -- Now we're at {C, F, blank, ones (6i+7)}; one more step gives state = none.
  simp [srun, sstep, tm, Side.prepend, ones]

-- ============================================================
-- closing_reset phase lemmas (used by m1_odd_reset)
-- ============================================================

/-- **F-sweep right** (`n+1` steps): from `{F, T, L, ones n *> blank}`, sweep
    right consuming all `n+1` head/right T's, deposit `ones (n+1)` to the
    left, end at state F head=F with right blank. -/
private lemma F_sweep_right (L : Side) (n : Nat) :
    srun tm
      { state := some stF, head := true, left := L,
        right := Side.prepend (ones n) blank∞ } (n + 1) =
    { state := some stF, head := false,
      left := Side.prepend (ones (n + 1)) L,
      right := blank∞ } := by
  induction n generalizing L with
  | zero => simp [srun, sstep, tm, Side.prepend, ones]
  | succ k ih =>
    have h1 : srun tm
        { state := some stF, head := true, left := L,
          right := Side.prepend (ones (k + 1)) blank∞ } 1 =
        { state := some stF, head := true, left := Side.cons true L,
          right := Side.prepend (ones k) blank∞ } := by
      show srun tm
          { state := some stF, head := true, left := L,
            right := Side.cons true (Side.prepend (ones k) blank∞) } 1 = _
      simp [srun, sstep, tm, Side.prepend]
    rw [show k + 1 + 1 = 1 + (k + 1) from by ring, srun_add, h1, ih (Side.cons true L),
        show Side.cons true L = Side.prepend (ones 1) L from rfl,
        ← Side.prepend_append, ones_append,
        show k + 1 + 1 = 1 + (k + 1) from by ring]

/-- **m1odd-Phase A1** (3 steps, A→B→D→E): from
    `{A, F, [T,F]*>ones 1*>blank, ones (6i+2)*>blank}` to
    `{E, T, [F,T]*>blank, ones (6i+3)*>blank}`. -/
private lemma m1odd_phaseA1 (i : Nat) :
    srun tm
      { state := some stA, head := false,
        left := Side.prepend [true, false] (Side.prepend (ones 1) blank∞),
        right := Side.prepend (ones (6 * i + 2)) blank∞ } 3 =
    { state := some stE, head := true,
      left := Side.prepend [false, true] blank∞,
      right := Side.prepend (ones (6 * i + 3)) blank∞ } := by
  rw [show Side.prepend (ones (6 * i + 2)) blank∞ =
        Side.prepend (ones 2) (Side.prepend (ones (6 * i)) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 2 + 6 * i = 6 * i + 2 from by ring],
      show Side.prepend (ones (6 * i + 3)) blank∞ =
        Side.prepend (ones 3) (Side.prepend (ones (6 * i)) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 3 + 6 * i = 6 * i + 3 from by ring]]
  simp [srun, sstep, tm, Side.prepend, ones]

/-- **m1odd-Phase A2** (`6i+4` steps): EA-cycle + 2 finalizing.
    `{E, T, [F,T]*>blank, ones (6i+3)*>blank}` →
    `{E, F, [T,F]××(3i+2)*>[F,T]*>blank, blank}`. -/
private lemma m1odd_phaseA2 (i : Nat) :
    srun tm
      { state := some stE, head := true,
        left := Side.prepend [false, true] blank∞,
        right := Side.prepend (ones (6 * i + 3)) blank∞ } (6 * i + 4) =
    { state := some stE, head := false,
      left := Side.prepend ([true, false] ×× (3 * i + 2))
              (Side.prepend [false, true] blank∞),
      right := blank∞ } := by
  rw [show (6 * i + 4 : Nat) = 2 * (3 * i + 1) + 2 from by ring,
      srun_add,
      show Side.prepend (ones (6 * i + 3)) blank∞ =
        Side.prepend (ones (2 * (3 * i + 1))) (Side.prepend (ones 1) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 2 * (3 * i + 1) + 1 = 6 * i + 3 from by ring],
      EA_shift (3 * i + 1) (Side.prepend [false, true] blank∞)
        (Side.prepend (ones 1) blank∞),
      show ([true, false] ×× (3 * i + 2) : List Sym)
        = [true, false] ++ [true, false] ×× (3 * i + 1) from by
        show [true, false] ×× ((3 * i + 1) + 1) = _; rfl,
      Side.prepend_append]
  simp [srun, sstep, tm, Side.prepend, ones]

/-- **m1odd-Phase A4** (`6i+7` steps): F→D init + D→B init + BD_iter +
    3-step tail to state C.
    `{F, F, [F]*>[T,F]××(3i+2)*>[F,T]*>blank, blank}` →
    `{C, T, blank, ones (6i+7)*>blank}`. -/
private lemma m1odd_phaseA4 (i : Nat) :
    srun tm
      { state := some stF, head := false,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 2))
                  (Side.prepend [false, true] blank∞)),
        right := blank∞ } (6 * i + 7) =
    { state := some stC, head := true,
      left := blank∞,
      right := Side.prepend (ones (6 * i + 7)) blank∞ } := by
  rw [show (6 * i + 7 : Nat) = 1 + (1 + (2 * (3 * i + 1) + 3)) from by ring, srun_add]
  have h_step1 : srun tm
      { state := some stF, head := false,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 2))
                  (Side.prepend [false, true] blank∞)),
        right := blank∞ } 1 =
      { state := some stD, head := false,
        left := Side.prepend ([true, false] ×× (3 * i + 2))
                  (Side.prepend [false, true] blank∞),
        right := Side.prepend (ones 1) blank∞ } := by
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_step1, srun_add,
      show ([true, false] ×× (3 * i + 2) : List Sym)
        = [true, false] ++ [true, false] ×× (3 * i + 1) from by
        show [true, false] ×× ((3 * i + 1) + 1) = _; rfl,
      Side.prepend_append]
  have h_step2 : srun tm
      { state := some stD, head := false,
        left := Side.prepend [true, false]
                  (Side.prepend ([true, false] ×× (3 * i + 1))
                    (Side.prepend [false, true] blank∞)),
        right := Side.prepend (ones 1) blank∞ } 1 =
      { state := some stB, head := true,
        left := Side.prepend [false]
                  (Side.prepend ([true, false] ×× (3 * i + 1))
                    (Side.prepend [false, true] blank∞)),
        right := Side.prepend (ones 2) blank∞ } := by
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_step2, srun_add,
      BD_iter (3 * i + 1) (Side.prepend [false, true] blank∞) 2,
      show Side.prepend (ones (2 + 2 * (3 * i + 1))) blank∞ =
        Side.prepend (ones 1) (Side.prepend (ones (6 * i + 3)) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 1 + (6 * i + 3) = 2 + 2 * (3 * i + 1) from by ring]]
  -- Now: {B, T, [F]*>[F,T]*>blank, ones 1*>ones (6i+3)*>blank}.
  -- 3 final steps: B,T→1LD; D,F→1LB; B,F→1LC.
  simp [srun, sstep, tm, Side.prepend, ones]
  show Side.prepend (ones 4) (Side.prepend (ones (6 * i + 3)) blank∞) =
    Side.prepend (ones (1 + (1 + (2 * (3 * i + 1) + 3)))) blank∞
  rw [← Side.prepend_append, ones_append,
      show 4 + (6 * i + 3) = 1 + (1 + (2 * (3 * i + 1) + 3)) from by ring]

/-- **closing_reset Phase A** (`12i+16` steps): from
    `{A, F, [T,F]*>ones 1*>blank, ones (6i+2)*>blank}` to
    `{A, F, blank, ones (6i+8)*>blank}`. -/
private lemma closing_reset_phaseA (i : Nat) :
    srun tm
      { state := some stA, head := false,
        left := Side.prepend [true, false] (Side.prepend (ones 1) blank∞),
        right := Side.prepend (ones (6 * i + 2)) blank∞ } (12 * i + 16) =
    { state := some stA, head := false,
      left := blank∞,
      right := Side.prepend (ones (6 * i + 8)) blank∞ } := by
  rw [show (12 * i + 16 : Nat) = 3 + ((6 * i + 4) + (1 + ((6 * i + 7) + 1))) from by ring,
      srun_add, m1odd_phaseA1 i,
      srun_add, m1odd_phaseA2 i,
      srun_add]
  -- Phase A3: 1 step E→F.
  have h_phaseA3 : srun tm
      { state := some stE, head := false,
        left := Side.prepend ([true, false] ×× (3 * i + 2))
                (Side.prepend [false, true] blank∞),
        right := blank∞ } 1 =
      { state := some stF, head := false,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 2))
                (Side.prepend [false, true] blank∞)),
        right := blank∞ } := by
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_phaseA3, srun_add, m1odd_phaseA4 i]
  -- Phase A5: 1 step C,T→1LA.
  show srun tm
      { state := some stC, head := true,
        left := blank∞,
        right := Side.prepend (ones (6 * i + 7)) blank∞ } 1 =
      { state := some stA, head := false,
        left := blank∞,
        right := Side.prepend (ones (6 * i + 8)) blank∞ }
  rw [show Side.prepend (ones (6 * i + 8)) blank∞ =
        Side.cons true (Side.prepend (ones (6 * i + 7)) blank∞) from by
        show Side.prepend (ones (6 * i + 7 + 1)) blank∞ = _; rfl]
  simp [srun, sstep, tm, Side.prepend, ones]

/-- **closing_reset Phase B** (`6i+18` steps): from
    `{A, F, blank, ones (6i+8)*>blank}` to
    `{A, F, [F,T,F]*>ones (6i+7)*>blank, blank}`. -/
private lemma closing_reset_phaseB (i : Nat) :
    srun tm
      { state := some stA, head := false,
        left := blank∞,
        right := Side.prepend (ones (6 * i + 8)) blank∞ } (6 * i + 18) =
    { state := some stA, head := false,
      left := Side.prepend [false, true, false] (Side.prepend (ones (6 * i + 7)) blank∞),
      right := blank∞ } := by
  rw [show (6 * i + 18 : Nat) = 3 + (1 + ((6 * i + 9) + 5)) from by ring, srun_add]
  -- B1 (3 steps): A→B→D→E. End: {E, F, blank, ones (6i+9)}.
  have h_B1 : srun tm
      { state := some stA, head := false,
        left := blank∞,
        right := Side.prepend (ones (6 * i + 8)) blank∞ } 3 =
      { state := some stE, head := false,
        left := blank∞,
        right := Side.prepend (ones (6 * i + 9)) blank∞ } := by
    rw [show Side.prepend (ones (6 * i + 8)) blank∞ =
          Side.prepend (ones 2) (Side.prepend (ones (6 * i + 6)) blank∞) from by
          rw [← Side.prepend_append, ones_append,
              show 2 + (6 * i + 6) = 6 * i + 8 from by ring],
        show Side.prepend (ones (6 * i + 9)) blank∞ =
          Side.prepend (ones 3) (Side.prepend (ones (6 * i + 6)) blank∞) from by
          rw [← Side.prepend_append, ones_append,
              show 3 + (6 * i + 6) = 6 * i + 9 from by ring]]
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_B1, srun_add]
  -- B2 (1 step): E,F→0RF. End: {F, T, blank, ones (6i+8)}.
  have h_B2 : srun tm
      { state := some stE, head := false,
        left := blank∞,
        right := Side.prepend (ones (6 * i + 9)) blank∞ } 1 =
      { state := some stF, head := true,
        left := blank∞,
        right := Side.prepend (ones (6 * i + 8)) blank∞ } := by
    rw [show Side.prepend (ones (6 * i + 9)) blank∞ =
          Side.cons true (Side.prepend (ones (6 * i + 8)) blank∞) from by
          show Side.prepend (ones (6 * i + 8 + 1)) blank∞ = _; rfl]
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_B2, srun_add,
      -- B3 (6i+9 steps): F-sweep right.
      show (6 * i + 9 : Nat) = (6 * i + 8) + 1 from by ring,
      F_sweep_right blank∞ (6 * i + 8),
      -- B4 (5 steps): pre-split left = ones 2 *> ones (6i+7) so simp consumes
      -- only the leading 2 cells, leaving ones (6i+7) intact.
      show Side.prepend (ones (6 * i + 8 + 1)) blank∞ =
        Side.prepend (ones 2) (Side.prepend (ones (6 * i + 7)) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 2 + (6 * i + 7) = 6 * i + 8 + 1 from by ring]]
  simp [srun, sstep, tm, Side.prepend, ones]

/-- **closing_reset** (`18i+34` steps): composes phase A and phase B. -/
private lemma closing_reset (i : Nat) :
    srun tm
      { state := some stA, head := false,
        left := Side.prepend [true, false] (Side.prepend (ones 1) blank∞),
        right := Side.prepend (ones (6 * i + 2)) blank∞ } (18 * i + 34) =
    { state := some stA, head := false,
      left := Side.prepend [false, true, false] (Side.prepend (ones (6 * i + 7)) blank∞),
      right := blank∞ } := by
  rw [show (18 * i + 34 : Nat) = (12 * i + 16) + (6 * i + 18) from by ring,
      srun_add, closing_reset_phaseA i, closing_reset_phaseB i]

/-- **m=1 odd → reset** (`dt = 6i² + 28i + 37`).  `A(1, 2i+1) → A(6i+7, 1)`.

    This is the "kick-back" rule that resets n to 1 while growing m.

    Decomposition: `right_push_g` (3) + Side rewrite (zebra (2i+1) =
    zebra (2i) ++ [F,T]) + `absorb_iter L=[T,F]++ones 1*>blank, t=0` (`6i²+10i`) +
    `closing_reset` (`18i+34`) = `6i²+28i+37`. -/
theorem m1_odd_reset (i : Nat) :
    srun tm (A_config 1 (2 * i + 1)) (6*i*i + 28*i + 37) =
      A_config (6 * i + 7) 1 := by
  unfold A_config
  -- Rewrite LHS: zebra (2i+1)*>[F]*>ones 1 = zebra (2i)*>[F]*>[T,F]*>ones 1.
  have h_left :
      Side.prepend (zebra (2 * i + 1))
        (Side.prepend [false] (Side.prepend (ones 1) blank∞))
      = Side.prepend (zebra (2 * i))
          (Side.prepend [false] (Side.prepend [true, false]
            (Side.prepend (ones 1) blank∞))) := by
    simp only [← Side.prepend_append]
    congr 1
    rw [show (zebra (2 * i + 1) : List Sym) = zebra (2 * i) ++ [false, true] from
          zebra_succ_append (2 * i)]
    simp [List.append_assoc]
  rw [h_left,
      show (6 * i * i + 28 * i + 37 : Nat)
          = 3 + ((6 * i * i + 10 * i + 12 * 0 * i) + (18 * i + 34)) from by ring,
      srun_add,
      right_push_g (Side.prepend [true, false] (Side.prepend (ones 1) blank∞)) i,
      srun_add,
      show (ones 2 : List Sym) = ones (6 * 0 + 2) from rfl,
      show Side.prepend ([true, false] ×× (2 * i))
            (Side.prepend [true, false] (Side.prepend (ones 1) blank∞))
        = Side.prepend ([true, false] ×× (2 * i))
            (Side.prepend ([true, false] ++ ones 1) blank∞) from by
        rw [Side.prepend_append],
      absorb_iter (Side.prepend ([true, false] ++ ones 1) blank∞) 0 i,
      show 0 + i = i from by ring,
      show Side.prepend ([true, false] ++ ones 1) blank∞
         = Side.prepend [true, false] (Side.prepend (ones 1) blank∞) from by
        rw [Side.prepend_append],
      closing_reset i]
  -- Final: bridge [F,T,F]*>ones (6i+7)*>blank = zebra 1 *> [F] *> ones (6i+7) *> blank.
  rfl

-- ============================================================
-- closing_halt_m2 phase lemmas (used by m2_even_halt)
-- ============================================================

/-- **m2-Phase 1** (3 steps, A→B→D→E): from `{A, F, ones 2, ones (6i+2)}` to
    `{E, T, ones 1, ones (6i+3)}`.  Like `m1_phase1` but starts with `ones 2`
    on left, ending with `ones 1` instead of blank. -/
private lemma m2_phase1 (i : Nat) :
    srun tm
      { state := some stA, head := false,
        left := Side.prepend (ones 2) blank∞,
        right := Side.prepend (ones (6 * i + 2)) blank∞ } 3 =
    { state := some stE, head := true,
      left := Side.prepend (ones 1) blank∞,
      right := Side.prepend (ones (6 * i + 3)) blank∞ } := by
  rw [show Side.prepend (ones (6 * i + 2)) blank∞ =
        Side.prepend (ones 2) (Side.prepend (ones (6 * i)) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 2 + 6 * i = 6 * i + 2 from by ring],
      show Side.prepend (ones (6 * i + 3)) blank∞ =
        Side.prepend (ones 3) (Side.prepend (ones (6 * i)) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 3 + 6 * i = 6 * i + 3 from by ring]]
  simp [srun, sstep, tm, Side.prepend, ones]

/-- **m2-Phase 2** (`6i+4` steps): EA-cycle + 2 finalizing.  Like `m1_phase2`
    but with `ones 1*>blank` as the L tail. -/
private lemma m2_phase2 (i : Nat) :
    srun tm
      { state := some stE, head := true,
        left := Side.prepend (ones 1) blank∞,
        right := Side.prepend (ones (6 * i + 3)) blank∞ } (6 * i + 4) =
    { state := some stE, head := false,
      left := Side.prepend ([true, false] ×× (3 * i + 2)) (Side.prepend (ones 1) blank∞),
      right := blank∞ } := by
  rw [show (6 * i + 4 : Nat) = 2 * (3 * i + 1) + 2 from by ring,
      srun_add,
      show Side.prepend (ones (6 * i + 3)) blank∞ =
        Side.prepend (ones (2 * (3 * i + 1))) (Side.prepend (ones 1) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 2 * (3 * i + 1) + 1 = 6 * i + 3 from by ring],
      EA_shift (3 * i + 1) (Side.prepend (ones 1) blank∞)
        (Side.prepend (ones 1) blank∞),
      show ([true, false] ×× (3 * i + 2) : List Sym)
        = [true, false] ++ [true, false] ×× (3 * i + 1) from by
        show [true, false] ×× ((3 * i + 1) + 1) = _; rfl,
      Side.prepend_append]
  simp [srun, sstep, tm, Side.prepend, ones]

/-- **m2-Phase 3** (1 step, E,F→0RF). -/
private lemma m2_phase3 (i : Nat) :
    srun tm
      { state := some stE, head := false,
        left := Side.prepend ([true, false] ×× (3 * i + 2)) (Side.prepend (ones 1) blank∞),
        right := blank∞ } 1 =
    { state := some stF, head := false,
      left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 2))
                (Side.prepend (ones 1) blank∞)),
      right := blank∞ } := by
  simp [srun, sstep, tm, Side.prepend, ones]

/-- **m2-Phase 4** (`6i+9` steps): F→D + D→B + BD_iter + 5-step tail to state C.
    Like `m1_phase4` but with extra `ones 1` prefix in left tail, giving 5-step
    tail (vs 3-step) and right ending at `ones (6i+9)` (vs `ones (6i+7)`). -/
private lemma m2_phase4 (i : Nat) :
    srun tm
      { state := some stF, head := false,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 2))
                  (Side.prepend (ones 1) blank∞)),
        right := blank∞ } (6 * i + 9) =
    { state := some stC, head := false,
      left := blank∞,
      right := Side.prepend (ones (6 * i + 9)) blank∞ } := by
  rw [show (6 * i + 9 : Nat) = 1 + (1 + (2 * (3 * i + 1) + 5)) from by ring, srun_add]
  have h_step1 : srun tm
      { state := some stF, head := false,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 2))
                  (Side.prepend (ones 1) blank∞)),
        right := blank∞ } 1 =
      { state := some stD, head := false,
        left := Side.prepend ([true, false] ×× (3 * i + 2))
                  (Side.prepend (ones 1) blank∞),
        right := Side.prepend (ones 1) blank∞ } := by
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_step1, srun_add,
      show ([true, false] ×× (3 * i + 2) : List Sym)
        = [true, false] ++ [true, false] ×× (3 * i + 1) from by
        show [true, false] ×× ((3 * i + 1) + 1) = _; rfl,
      Side.prepend_append]
  have h_step2 : srun tm
      { state := some stD, head := false,
        left := Side.prepend [true, false]
                  (Side.prepend ([true, false] ×× (3 * i + 1))
                    (Side.prepend (ones 1) blank∞)),
        right := Side.prepend (ones 1) blank∞ } 1 =
      { state := some stB, head := true,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 1))
                    (Side.prepend (ones 1) blank∞)),
        right := Side.prepend (ones 2) blank∞ } := by
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_step2, srun_add,
      BD_iter (3 * i + 1) (Side.prepend (ones 1) blank∞) 2,
      show Side.prepend (ones (2 + 2 * (3 * i + 1))) blank∞ =
        Side.prepend (ones 1) (Side.prepend (ones (6 * i + 3)) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 1 + (6 * i + 3) = 2 + 2 * (3 * i + 1) from by ring]]
  -- 5 final steps: B,T→1LD; D,F→1LB; B,T→1LD; D,F→1LB; B,F→1LC.
  simp [srun, sstep, tm, Side.prepend, ones]
  show Side.prepend (ones 9) (Side.prepend (ones (6 * i)) blank∞) =
    Side.prepend (ones (1 + (1 + (2 * (3 * i + 1) + 5)))) blank∞
  rw [← Side.prepend_append, ones_append,
      show 9 + 6 * i = 1 + (1 + (2 * (3 * i + 1) + 5)) from by ring]

/-- **closing_halt_m2** (`12i+17` steps): from `{A, F, ones 2, ones (6i+2)}` to
    `{C, F, blank, ones (6i+9)}`.  Composes `m2_phase{1..4}`. -/
private lemma closing_halt_m2 (i : Nat) :
    srun tm
      { state := some stA, head := false,
        left := Side.prepend (ones 2) blank∞,
        right := Side.prepend (ones (6 * i + 2)) blank∞ } (12 * i + 17) =
    { state := some stC, head := false,
      left := blank∞,
      right := Side.prepend (ones (6 * i + 9)) blank∞ } := by
  rw [show (12 * i + 17 : Nat) = 3 + ((6 * i + 4) + (1 + (6 * i + 9))) from by ring,
      srun_add, m2_phase1 i,
      srun_add, m2_phase2 i,
      srun_add, m2_phase3 i,
      m2_phase4 i]

/-- **m=2 even → halt** (`dt = 6i² + 22i + 21` Lean-step count, sim says 20).

    Decomposition: `right_push_g` (3) + `absorb_iter L=ones 2*>blank, t=0`
    (`6i²+10i`) + `closing_halt_m2` (`12i+17`) + halt step (1) = `6i²+22i+21`. -/
theorem m2_even_halt (i : Nat) :
    (srun tm (A_config 2 (2 * i)) (6*i*i + 22*i + 21)).state = none := by
  unfold A_config
  rw [show (6 * i * i + 22 * i + 21 : Nat)
        = 3 + ((6 * i * i + 10 * i + 12 * 0 * i) + ((12 * i + 17) + 1)) from by ring,
      srun_add,
      right_push_g (Side.prepend (ones 2) blank∞) i,
      srun_add,
      show (ones 2 : List Sym) = ones (6 * 0 + 2) from rfl,
      absorb_iter (Side.prepend (ones 2) blank∞) 0 i,
      show 0 + i = i from by ring,
      srun_add, closing_halt_m2 i]
  -- One more step from {C, F, blank, ones (6i+9)} → state none.
  simp [srun, sstep, tm, Side.prepend, ones]

-- ============================================================
-- closing_m2_odd phase lemmas (used by m2_odd_halt)
-- ============================================================

/-- **m2odd-Phase A1** (3 steps, A→B→D→E): from
    `{A, F, [T,F]*>ones 2*>blank, ones (6i+2)*>blank}` to
    `{E, T, [F]*>ones 2*>blank, ones (6i+3)*>blank}`. -/
private lemma m2odd_phaseA1 (i : Nat) :
    srun tm
      { state := some stA, head := false,
        left := Side.prepend [true, false] (Side.prepend (ones 2) blank∞),
        right := Side.prepend (ones (6 * i + 2)) blank∞ } 3 =
    { state := some stE, head := true,
      left := Side.prepend [false] (Side.prepend (ones 2) blank∞),
      right := Side.prepend (ones (6 * i + 3)) blank∞ } := by
  rw [show Side.prepend (ones (6 * i + 2)) blank∞ =
        Side.prepend (ones 2) (Side.prepend (ones (6 * i)) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 2 + 6 * i = 6 * i + 2 from by ring],
      show Side.prepend (ones (6 * i + 3)) blank∞ =
        Side.prepend (ones 3) (Side.prepend (ones (6 * i)) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 3 + 6 * i = 6 * i + 3 from by ring]]
  simp [srun, sstep, tm, Side.prepend, ones]

/-- **m2odd-Phase A2** (`6i+4` steps): EA cycle + 2 finalizing.
    `{E, T, [F]*>ones 2*>blank, ones (6i+3)*>blank}` →
    `{E, F, [T,F]××(3i+2)*>[F]*>ones 2*>blank, blank}`. -/
private lemma m2odd_phaseA2 (i : Nat) :
    srun tm
      { state := some stE, head := true,
        left := Side.prepend [false] (Side.prepend (ones 2) blank∞),
        right := Side.prepend (ones (6 * i + 3)) blank∞ } (6 * i + 4) =
    { state := some stE, head := false,
      left := Side.prepend ([true, false] ×× (3 * i + 2))
                (Side.prepend [false] (Side.prepend (ones 2) blank∞)),
      right := blank∞ } := by
  rw [show (6 * i + 4 : Nat) = 2 * (3 * i + 1) + 2 from by ring,
      srun_add,
      show Side.prepend (ones (6 * i + 3)) blank∞ =
        Side.prepend (ones (2 * (3 * i + 1))) (Side.prepend (ones 1) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 2 * (3 * i + 1) + 1 = 6 * i + 3 from by ring],
      EA_shift (3 * i + 1) (Side.prepend [false] (Side.prepend (ones 2) blank∞))
        (Side.prepend (ones 1) blank∞),
      show ([true, false] ×× (3 * i + 2) : List Sym)
        = [true, false] ++ [true, false] ×× (3 * i + 1) from by
        show [true, false] ×× ((3 * i + 1) + 1) = _; rfl,
      Side.prepend_append]
  simp [srun, sstep, tm, Side.prepend, ones]

/-- **m2odd-Phase A4** (`6i+7` steps): F→D + D→B init + BD_iter + 3 tail to C.
    Like `m1odd_phaseA4` but with `[F]*>ones 2*>blank` tail instead of
    `[F,T]*>blank`, ending at `{C, T, ones 1*>blank, ones (6i+7)*>blank}`. -/
private lemma m2odd_phaseA4 (i : Nat) :
    srun tm
      { state := some stF, head := false,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 2))
                  (Side.prepend [false] (Side.prepend (ones 2) blank∞))),
        right := blank∞ } (6 * i + 7) =
    { state := some stC, head := true,
      left := Side.prepend (ones 1) blank∞,
      right := Side.prepend (ones (6 * i + 7)) blank∞ } := by
  rw [show (6 * i + 7 : Nat) = 1 + (1 + (2 * (3 * i + 1) + 3)) from by ring, srun_add]
  have h_step1 : srun tm
      { state := some stF, head := false,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 2))
                  (Side.prepend [false] (Side.prepend (ones 2) blank∞))),
        right := blank∞ } 1 =
      { state := some stD, head := false,
        left := Side.prepend ([true, false] ×× (3 * i + 2))
                  (Side.prepend [false] (Side.prepend (ones 2) blank∞)),
        right := Side.prepend (ones 1) blank∞ } := by
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_step1, srun_add,
      show ([true, false] ×× (3 * i + 2) : List Sym)
        = [true, false] ++ [true, false] ×× (3 * i + 1) from by
        show [true, false] ×× ((3 * i + 1) + 1) = _; rfl,
      Side.prepend_append]
  have h_step2 : srun tm
      { state := some stD, head := false,
        left := Side.prepend [true, false]
                  (Side.prepend ([true, false] ×× (3 * i + 1))
                    (Side.prepend [false] (Side.prepend (ones 2) blank∞))),
        right := Side.prepend (ones 1) blank∞ } 1 =
      { state := some stB, head := true,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 1))
                    (Side.prepend [false] (Side.prepend (ones 2) blank∞))),
        right := Side.prepend (ones 2) blank∞ } := by
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_step2, srun_add,
      BD_iter (3 * i + 1) (Side.prepend [false] (Side.prepend (ones 2) blank∞)) 2,
      show Side.prepend (ones (2 + 2 * (3 * i + 1))) blank∞ =
        Side.prepend (ones 1) (Side.prepend (ones (6 * i + 3)) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 1 + (6 * i + 3) = 2 + 2 * (3 * i + 1) from by ring]]
  -- 3 tail steps: B,T→1LD; D,F→1LB; B,F→1LC.  Last step pulls T from ones 2.
  simp [srun, sstep, tm, Side.prepend, ones]
  show Side.prepend (ones 4) (Side.prepend (ones (6 * i + 3)) blank∞) =
    Side.prepend (ones (1 + (1 + (2 * (3 * i + 1) + 3)))) blank∞
  rw [← Side.prepend_append, ones_append,
      show 4 + (6 * i + 3) = 1 + (1 + (2 * (3 * i + 1) + 3)) from by ring]

/-- **closing_m2_odd Phase A** (`12i+16` steps): from
    `{A, F, [T,F]*>ones 2*>blank, ones (6i+2)*>blank}` to
    `{A, T, blank, ones (6i+8)*>blank}`. -/
private lemma closing_m2_odd_phaseA (i : Nat) :
    srun tm
      { state := some stA, head := false,
        left := Side.prepend [true, false] (Side.prepend (ones 2) blank∞),
        right := Side.prepend (ones (6 * i + 2)) blank∞ } (12 * i + 16) =
    { state := some stA, head := true,
      left := blank∞,
      right := Side.prepend (ones (6 * i + 8)) blank∞ } := by
  rw [show (12 * i + 16 : Nat) = 3 + ((6 * i + 4) + (1 + ((6 * i + 7) + 1))) from by ring,
      srun_add, m2odd_phaseA1 i,
      srun_add, m2odd_phaseA2 i,
      srun_add]
  -- Phase A3: 1 step E,F→0RF.
  have h_phaseA3 : srun tm
      { state := some stE, head := false,
        left := Side.prepend ([true, false] ×× (3 * i + 2))
                (Side.prepend [false] (Side.prepend (ones 2) blank∞)),
        right := blank∞ } 1 =
      { state := some stF, head := false,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 2))
                (Side.prepend [false] (Side.prepend (ones 2) blank∞))),
        right := blank∞ } := by
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_phaseA3, srun_add, m2odd_phaseA4 i]
  -- Phase A5: 1 step C,T→1LA.  Pull T from ones 1 → state A head=T, left=blank.
  show srun tm
      { state := some stC, head := true,
        left := Side.prepend (ones 1) blank∞,
        right := Side.prepend (ones (6 * i + 7)) blank∞ } 1 =
      { state := some stA, head := true,
        left := blank∞,
        right := Side.prepend (ones (6 * i + 8)) blank∞ }
  rw [show Side.prepend (ones (6 * i + 8)) blank∞ =
        Side.cons true (Side.prepend (ones (6 * i + 7)) blank∞) from by
        show Side.prepend (ones (6 * i + 7 + 1)) blank∞ = _; rfl]
  simp [srun, sstep, tm, Side.prepend, ones]

/-- **m2odd-Phase B1** (`6i+9` steps): EA-right cycle from
    `{A, T, blank, ones (6i+8)*>blank}` to
    `{E, F, [T,F]××(3i+4)*>ones 1*>blank, blank}`.

    Decomp: 1 step (A,T→1RE) + EA_shift k=3i+3 (`6i+6` steps consuming
    `ones (6i+6)`) + 2 finalizing (E,T→0RA + A,T→1RE). -/
private lemma m2odd_phaseB1 (i : Nat) :
    srun tm
      { state := some stA, head := true,
        left := blank∞,
        right := Side.prepend (ones (6 * i + 8)) blank∞ } (6 * i + 9) =
    { state := some stE, head := false,
      left := Side.prepend ([true, false] ×× (3 * i + 4))
                (Side.prepend (ones 1) blank∞),
      right := blank∞ } := by
  rw [show (6 * i + 9 : Nat) = 1 + ((6 * i + 6) + 2) from by ring, srun_add]
  -- Step 1 (A,T→1RE): peel right ones (6i+8) → ones (6i+7), state E head=T.
  have h_step1 : srun tm
      { state := some stA, head := true,
        left := blank∞,
        right := Side.prepend (ones (6 * i + 8)) blank∞ } 1 =
      { state := some stE, head := true,
        left := Side.prepend (ones 1) blank∞,
        right := Side.prepend (ones (6 * i + 7)) blank∞ } := by
    rw [show Side.prepend (ones (6 * i + 8)) blank∞ =
          Side.cons true (Side.prepend (ones (6 * i + 7)) blank∞) from by
          show Side.prepend (ones (6 * i + 7 + 1)) blank∞ = _; rfl]
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_step1, srun_add,
      show (6 * i + 6 : Nat) = 2 * (3 * i + 3) from by ring,
      -- Split right: ones (6i+7) = ones (2*(3i+3)) ++ ones 1.
      show Side.prepend (ones (6 * i + 7)) blank∞ =
        Side.prepend (ones (2 * (3 * i + 3))) (Side.prepend (ones 1) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 2 * (3 * i + 3) + 1 = 6 * i + 7 from by ring],
      EA_shift (3 * i + 3) (Side.prepend (ones 1) blank∞)
        (Side.prepend (ones 1) blank∞),
      show ([true, false] ×× (3 * i + 4) : List Sym)
        = [true, false] ++ [true, false] ×× (3 * i + 3) from by
        show [true, false] ×× ((3 * i + 3) + 1) = _; rfl,
      Side.prepend_append]
  simp [srun, sstep, tm, Side.prepend, ones]

/-- **m2odd-Phase B3** (`6i+13` steps): F→D + D→B init + BD_iter + 5 tail.
    Like `m2_phase4` but with `[T,F]××(3i+4)` (instead of (3i+2)) on left.

    `{F, F, [F]*>[T,F]××(3i+4)*>ones 1*>blank, blank}` →
    `{C, F, blank, ones (6i+13)*>blank}`. -/
private lemma m2odd_phaseB3 (i : Nat) :
    srun tm
      { state := some stF, head := false,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 4))
                  (Side.prepend (ones 1) blank∞)),
        right := blank∞ } (6 * i + 13) =
    { state := some stC, head := false,
      left := blank∞,
      right := Side.prepend (ones (6 * i + 13)) blank∞ } := by
  rw [show (6 * i + 13 : Nat) = 1 + (1 + (2 * (3 * i + 3) + 5)) from by ring, srun_add]
  have h_step1 : srun tm
      { state := some stF, head := false,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 4))
                  (Side.prepend (ones 1) blank∞)),
        right := blank∞ } 1 =
      { state := some stD, head := false,
        left := Side.prepend ([true, false] ×× (3 * i + 4))
                  (Side.prepend (ones 1) blank∞),
        right := Side.prepend (ones 1) blank∞ } := by
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_step1, srun_add,
      show ([true, false] ×× (3 * i + 4) : List Sym)
        = [true, false] ++ [true, false] ×× (3 * i + 3) from by
        show [true, false] ×× ((3 * i + 3) + 1) = _; rfl,
      Side.prepend_append]
  have h_step2 : srun tm
      { state := some stD, head := false,
        left := Side.prepend [true, false]
                  (Side.prepend ([true, false] ×× (3 * i + 3))
                    (Side.prepend (ones 1) blank∞)),
        right := Side.prepend (ones 1) blank∞ } 1 =
      { state := some stB, head := true,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 3))
                    (Side.prepend (ones 1) blank∞)),
        right := Side.prepend (ones 2) blank∞ } := by
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_step2, srun_add,
      BD_iter (3 * i + 3) (Side.prepend (ones 1) blank∞) 2,
      show Side.prepend (ones (2 + 2 * (3 * i + 3))) blank∞ =
        Side.prepend (ones 1) (Side.prepend (ones (6 * i + 7)) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 1 + (6 * i + 7) = 2 + 2 * (3 * i + 3) from by ring]]
  -- 5 tail steps: B,T→1LD; D,F→1LB; B,T→1LD; D,F→1LB; B,F→1LC.
  simp [srun, sstep, tm, Side.prepend, ones]
  show Side.prepend (ones 6) (Side.prepend (ones (6 * i + 7)) blank∞) =
    Side.prepend (ones (1 + (1 + (2 * (3 * i + 3) + 5)))) blank∞
  rw [← Side.prepend_append, ones_append,
      show 6 + (6 * i + 7) = 1 + (1 + (2 * (3 * i + 3) + 5)) from by ring]

/-- **closing_m2_odd Phase B** (`12i+23` steps): from
    `{A, T, blank, ones (6i+8)*>blank}` to
    `{C, F, blank, ones (6i+13)*>blank}`. -/
private lemma closing_m2_odd_phaseB (i : Nat) :
    srun tm
      { state := some stA, head := true,
        left := blank∞,
        right := Side.prepend (ones (6 * i + 8)) blank∞ } (12 * i + 23) =
    { state := some stC, head := false,
      left := blank∞,
      right := Side.prepend (ones (6 * i + 13)) blank∞ } := by
  rw [show (12 * i + 23 : Nat) = (6 * i + 9) + (1 + (6 * i + 13)) from by ring,
      srun_add, m2odd_phaseB1 i, srun_add]
  -- B2: 1 step E,F→0RF.
  have h_B2 : srun tm
      { state := some stE, head := false,
        left := Side.prepend ([true, false] ×× (3 * i + 4))
                  (Side.prepend (ones 1) blank∞),
        right := blank∞ } 1 =
      { state := some stF, head := false,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 4))
                  (Side.prepend (ones 1) blank∞)),
        right := blank∞ } := by
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_B2, m2odd_phaseB3 i]

/-- **closing_m2_odd** (`24i+39` steps): composes phaseA and phaseB. -/
private lemma closing_m2_odd (i : Nat) :
    srun tm
      { state := some stA, head := false,
        left := Side.prepend [true, false] (Side.prepend (ones 2) blank∞),
        right := Side.prepend (ones (6 * i + 2)) blank∞ } (24 * i + 39) =
    { state := some stC, head := false,
      left := blank∞,
      right := Side.prepend (ones (6 * i + 13)) blank∞ } := by
  rw [show (24 * i + 39 : Nat) = (12 * i + 16) + (12 * i + 23) from by ring,
      srun_add, closing_m2_odd_phaseA i, closing_m2_odd_phaseB i]

/-- **m=2 odd → halt** (`dt = 6i² + 34i + 43` Lean-step count, sim says 42).

    Decomposition: zebra rewrite (`zebra (2i+1) = zebra (2i) ++ [F,T]`) +
    `right_push_g` (3) + Side rewrite + `absorb_iter L=[T,F]++ones 2*>blank, t=0`
    (`6i²+10i`) + `closing_m2_odd` (`24i+39`) + halt step (1) = `6i²+34i+43`. -/
theorem m2_odd_halt (i : Nat) :
    (srun tm (A_config 2 (2 * i + 1)) (6*i*i + 34*i + 43)).state = none := by
  unfold A_config
  have h_left :
      Side.prepend (zebra (2 * i + 1))
        (Side.prepend [false] (Side.prepend (ones 2) blank∞))
      = Side.prepend (zebra (2 * i))
          (Side.prepend [false] (Side.prepend [true, false]
            (Side.prepend (ones 2) blank∞))) := by
    simp only [← Side.prepend_append]
    congr 1
    rw [show (zebra (2 * i + 1) : List Sym) = zebra (2 * i) ++ [false, true] from
          zebra_succ_append (2 * i)]
    simp [List.append_assoc]
  rw [h_left,
      show (6 * i * i + 34 * i + 43 : Nat)
          = 3 + ((6 * i * i + 10 * i + 12 * 0 * i) + ((24 * i + 39) + 1)) from by ring,
      srun_add,
      right_push_g (Side.prepend [true, false] (Side.prepend (ones 2) blank∞)) i,
      srun_add,
      show (ones 2 : List Sym) = ones (6 * 0 + 2) from rfl,
      show Side.prepend ([true, false] ×× (2 * i))
            (Side.prepend [true, false] (Side.prepend (ones 2) blank∞))
        = Side.prepend ([true, false] ×× (2 * i))
            (Side.prepend ([true, false] ++ ones 2) blank∞) from by
        rw [Side.prepend_append],
      absorb_iter (Side.prepend ([true, false] ++ ones 2) blank∞) 0 i,
      show 0 + i = i from by ring,
      show Side.prepend ([true, false] ++ ones 2) blank∞
         = Side.prepend [true, false] (Side.prepend (ones 2) blank∞) from by
        rw [Side.prepend_append],
      srun_add, closing_m2_odd i]
  -- Final halt step.
  simp [srun, sstep, tm, Side.prepend, ones]

-- ============================================================
-- closing_m3_even phase lemmas (used by m3_even_reset)
-- ============================================================

/-- **m3-Phase A1** (3 steps, A→B→D→E): from `{A, F, ones 3, ones (6i+2)}` to
    `{E, T, ones 2, ones (6i+3)}`. -/
private lemma m3_phaseA1 (i : Nat) :
    srun tm
      { state := some stA, head := false,
        left := Side.prepend (ones 3) blank∞,
        right := Side.prepend (ones (6 * i + 2)) blank∞ } 3 =
    { state := some stE, head := true,
      left := Side.prepend (ones 2) blank∞,
      right := Side.prepend (ones (6 * i + 3)) blank∞ } := by
  rw [show Side.prepend (ones (6 * i + 2)) blank∞ =
        Side.prepend (ones 2) (Side.prepend (ones (6 * i)) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 2 + 6 * i = 6 * i + 2 from by ring],
      show Side.prepend (ones (6 * i + 3)) blank∞ =
        Side.prepend (ones 3) (Side.prepend (ones (6 * i)) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 3 + 6 * i = 6 * i + 3 from by ring]]
  simp [srun, sstep, tm, Side.prepend, ones]

/-- **m3-Phase A2** (`6i+4` steps): EA cycle + 2 finalizing.
    `{E, T, ones 2, ones (6i+3)}` →
    `{E, F, [T,F]××(3i+2)*>ones 2*>blank, blank}`. -/
private lemma m3_phaseA2 (i : Nat) :
    srun tm
      { state := some stE, head := true,
        left := Side.prepend (ones 2) blank∞,
        right := Side.prepend (ones (6 * i + 3)) blank∞ } (6 * i + 4) =
    { state := some stE, head := false,
      left := Side.prepend ([true, false] ×× (3 * i + 2))
                (Side.prepend (ones 2) blank∞),
      right := blank∞ } := by
  rw [show (6 * i + 4 : Nat) = 2 * (3 * i + 1) + 2 from by ring,
      srun_add,
      show Side.prepend (ones (6 * i + 3)) blank∞ =
        Side.prepend (ones (2 * (3 * i + 1))) (Side.prepend (ones 1) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 2 * (3 * i + 1) + 1 = 6 * i + 3 from by ring],
      EA_shift (3 * i + 1) (Side.prepend (ones 2) blank∞)
        (Side.prepend (ones 1) blank∞),
      show ([true, false] ×× (3 * i + 2) : List Sym)
        = [true, false] ++ [true, false] ×× (3 * i + 1) from by
        show [true, false] ×× ((3 * i + 1) + 1) = _; rfl,
      Side.prepend_append]
  simp [srun, sstep, tm, Side.prepend, ones]

/-- **m3-Phase A4** (`6i+8` steps): F→D + D→B init + BD_iter + 4 tail to state E.
    Like `m2_phase4` but ends at state E head=F (not state C) because of extra
    boundary T's from `ones 2` trail.

    `{F, F, [F]*>[T,F]××(3i+2)*>ones 2*>blank, blank}` →
    `{E, F, blank, ones (6i+8)*>blank}`. -/
private lemma m3_phaseA4 (i : Nat) :
    srun tm
      { state := some stF, head := false,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 2))
                  (Side.prepend (ones 2) blank∞)),
        right := blank∞ } (6 * i + 8) =
    { state := some stE, head := false,
      left := blank∞,
      right := Side.prepend (ones (6 * i + 8)) blank∞ } := by
  rw [show (6 * i + 8 : Nat) = 1 + (1 + (2 * (3 * i + 1) + 4)) from by ring, srun_add]
  have h_step1 : srun tm
      { state := some stF, head := false,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 2))
                  (Side.prepend (ones 2) blank∞)),
        right := blank∞ } 1 =
      { state := some stD, head := false,
        left := Side.prepend ([true, false] ×× (3 * i + 2))
                  (Side.prepend (ones 2) blank∞),
        right := Side.prepend (ones 1) blank∞ } := by
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_step1, srun_add,
      show ([true, false] ×× (3 * i + 2) : List Sym)
        = [true, false] ++ [true, false] ×× (3 * i + 1) from by
        show [true, false] ×× ((3 * i + 1) + 1) = _; rfl,
      Side.prepend_append]
  have h_step2 : srun tm
      { state := some stD, head := false,
        left := Side.prepend [true, false]
                  (Side.prepend ([true, false] ×× (3 * i + 1))
                    (Side.prepend (ones 2) blank∞)),
        right := Side.prepend (ones 1) blank∞ } 1 =
      { state := some stB, head := true,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 1))
                    (Side.prepend (ones 2) blank∞)),
        right := Side.prepend (ones 2) blank∞ } := by
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_step2, srun_add,
      BD_iter (3 * i + 1) (Side.prepend (ones 2) blank∞) 2,
      show Side.prepend (ones (2 + 2 * (3 * i + 1))) blank∞ =
        Side.prepend (ones 1) (Side.prepend (ones (6 * i + 3)) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 1 + (6 * i + 3) = 2 + 2 * (3 * i + 1) from by ring]]
  -- 4 tail steps: B,T→1LD; D,F→1LB; B,T→1LD; D,T→1LE.
  -- Output: state E head=F, left=blank, right=ones (6i+8).
  simp [srun, sstep, tm, Side.prepend, ones]
  show Side.prepend (ones 5) (Side.prepend (ones (6 * i + 3)) blank∞) =
    Side.prepend (ones (1 + (1 + (2 * (3 * i + 1) + 4)))) blank∞
  rw [← Side.prepend_append, ones_append,
      show 5 + (6 * i + 3) = 1 + (1 + (2 * (3 * i + 1) + 4)) from by ring]

/-- **closing_m3_even Phase A** (`12i+16` steps): from `{A, F, ones 3, ones (6i+2)}`
    to `{E, F, blank, ones (6i+8)*>blank}`.  Composes m3_phase{A1, A2, A3, A4}. -/
private lemma closing_m3_even_phaseA (i : Nat) :
    srun tm
      { state := some stA, head := false,
        left := Side.prepend (ones 3) blank∞,
        right := Side.prepend (ones (6 * i + 2)) blank∞ } (12 * i + 16) =
    { state := some stE, head := false,
      left := blank∞,
      right := Side.prepend (ones (6 * i + 8)) blank∞ } := by
  rw [show (12 * i + 16 : Nat) = 3 + ((6 * i + 4) + (1 + (6 * i + 8))) from by ring,
      srun_add, m3_phaseA1 i,
      srun_add, m3_phaseA2 i,
      srun_add]
  -- Phase A3: 1 step E,F→0RF.
  have h_phaseA3 : srun tm
      { state := some stE, head := false,
        left := Side.prepend ([true, false] ×× (3 * i + 2))
                  (Side.prepend (ones 2) blank∞),
        right := blank∞ } 1 =
      { state := some stF, head := false,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 2))
                  (Side.prepend (ones 2) blank∞)),
        right := blank∞ } := by
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_phaseA3, m3_phaseA4 i]

/-- **closing_m3_even Phase B** (`6i+14` steps): from `{E, F, blank, ones (6i+8)}`
    to `{A, F, [F,T,F]*>ones (6i+6)*>blank, blank}` (= `A(6i+6, 1)`).

    Decomp: 1 step (E,F→0RF) + F-sweep right (`6i+8` steps) + 5-step tail. -/
private lemma closing_m3_even_phaseB (i : Nat) :
    srun tm
      { state := some stE, head := false,
        left := blank∞,
        right := Side.prepend (ones (6 * i + 8)) blank∞ } (6 * i + 14) =
    { state := some stA, head := false,
      left := Side.prepend [false, true, false] (Side.prepend (ones (6 * i + 6)) blank∞),
      right := blank∞ } := by
  rw [show (6 * i + 14 : Nat) = 1 + ((6 * i + 8) + 5) from by ring, srun_add]
  -- B1: 1 step E,F→0RF.
  have h_B1 : srun tm
      { state := some stE, head := false,
        left := blank∞,
        right := Side.prepend (ones (6 * i + 8)) blank∞ } 1 =
      { state := some stF, head := true,
        left := blank∞,
        right := Side.prepend (ones (6 * i + 7)) blank∞ } := by
    rw [show Side.prepend (ones (6 * i + 8)) blank∞ =
          Side.cons true (Side.prepend (ones (6 * i + 7)) blank∞) from by
          show Side.prepend (ones (6 * i + 7 + 1)) blank∞ = _; rfl]
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_B1, srun_add,
      -- B2: F-sweep right (6i+8 steps).
      show (6 * i + 8 : Nat) = (6 * i + 7) + 1 from by ring,
      F_sweep_right blank∞ (6 * i + 7),
      -- B3: 5 tail steps. Pre-split ones (6i+8) as ones 2 *> ones (6i+6) so simp
      -- consumes the leading 2 cells, leaving ones (6i+6) intact.
      show Side.prepend (ones (6 * i + 7 + 1)) blank∞ =
        Side.prepend (ones 2) (Side.prepend (ones (6 * i + 6)) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 2 + (6 * i + 6) = 6 * i + 7 + 1 from by ring]]
  simp [srun, sstep, tm, Side.prepend, ones]

/-- **closing_m3_even** (`18i+30` steps): composes phaseA and phaseB. -/
private lemma closing_m3_even (i : Nat) :
    srun tm
      { state := some stA, head := false,
        left := Side.prepend (ones 3) blank∞,
        right := Side.prepend (ones (6 * i + 2)) blank∞ } (18 * i + 30) =
    { state := some stA, head := false,
      left := Side.prepend [false, true, false] (Side.prepend (ones (6 * i + 6)) blank∞),
      right := blank∞ } := by
  rw [show (18 * i + 30 : Nat) = (12 * i + 16) + (6 * i + 14) from by ring,
      srun_add, closing_m3_even_phaseA i, closing_m3_even_phaseB i]

/-- **m=3 even → reset** (`dt = 6i² + 28i + 33`).  `A(3, 2i) → A(6i+6, 1)`.

    Decomposition: `right_push_g` (3) + `absorb_iter L=ones 3*>blank, t=0`
    (`6i²+10i`) + `closing_m3_even` (`18i+30`) = `6i²+28i+33`. -/
theorem m3_even_reset (i : Nat) :
    srun tm (A_config 3 (2 * i)) (6*i*i + 28*i + 33) =
      A_config (6 * i + 6) 1 := by
  unfold A_config
  rw [show (6 * i * i + 28 * i + 33 : Nat)
        = 3 + ((6 * i * i + 10 * i + 12 * 0 * i) + (18 * i + 30)) from by ring,
      srun_add,
      right_push_g (Side.prepend (ones 3) blank∞) i,
      srun_add,
      show (ones 2 : List Sym) = ones (6 * 0 + 2) from rfl,
      absorb_iter (Side.prepend (ones 3) blank∞) 0 i,
      show 0 + i = i from by ring,
      closing_m3_even i]
  -- Final form bridges directly: [F,T,F]*>ones (6i+6)*>blank = zebra 1*>[F]*>ones (6i+6)*>blank.
  rfl

-- ============================================================
-- closing_m3_odd phase lemmas (used by m3_odd_reset)
-- ============================================================

/-- **m3odd-Phase A1** (3 steps, A→B→D→E): from
    `{A, F, [T,F]*>ones 3*>blank, ones (6i+2)*>blank}` to
    `{E, T, [F]*>ones 3*>blank, ones (6i+3)*>blank}`. -/
private lemma m3odd_phaseA1 (i : Nat) :
    srun tm
      { state := some stA, head := false,
        left := Side.prepend [true, false] (Side.prepend (ones 3) blank∞),
        right := Side.prepend (ones (6 * i + 2)) blank∞ } 3 =
    { state := some stE, head := true,
      left := Side.prepend [false] (Side.prepend (ones 3) blank∞),
      right := Side.prepend (ones (6 * i + 3)) blank∞ } := by
  rw [show Side.prepend (ones (6 * i + 2)) blank∞ =
        Side.prepend (ones 2) (Side.prepend (ones (6 * i)) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 2 + 6 * i = 6 * i + 2 from by ring],
      show Side.prepend (ones (6 * i + 3)) blank∞ =
        Side.prepend (ones 3) (Side.prepend (ones (6 * i)) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 3 + 6 * i = 6 * i + 3 from by ring]]
  simp [srun, sstep, tm, Side.prepend, ones]

/-- **m3odd-Phase A2** (`6i+4` steps): EA cycle + 2 finalizing.  Like `m2odd_phaseA2`
    but with `[F]*>ones 3*>blank` as L tail. -/
private lemma m3odd_phaseA2 (i : Nat) :
    srun tm
      { state := some stE, head := true,
        left := Side.prepend [false] (Side.prepend (ones 3) blank∞),
        right := Side.prepend (ones (6 * i + 3)) blank∞ } (6 * i + 4) =
    { state := some stE, head := false,
      left := Side.prepend ([true, false] ×× (3 * i + 2))
                (Side.prepend [false] (Side.prepend (ones 3) blank∞)),
      right := blank∞ } := by
  rw [show (6 * i + 4 : Nat) = 2 * (3 * i + 1) + 2 from by ring,
      srun_add,
      show Side.prepend (ones (6 * i + 3)) blank∞ =
        Side.prepend (ones (2 * (3 * i + 1))) (Side.prepend (ones 1) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 2 * (3 * i + 1) + 1 = 6 * i + 3 from by ring],
      EA_shift (3 * i + 1) (Side.prepend [false] (Side.prepend (ones 3) blank∞))
        (Side.prepend (ones 1) blank∞),
      show ([true, false] ×× (3 * i + 2) : List Sym)
        = [true, false] ++ [true, false] ×× (3 * i + 1) from by
        show [true, false] ×× ((3 * i + 1) + 1) = _; rfl,
      Side.prepend_append]
  simp [srun, sstep, tm, Side.prepend, ones]

/-- **m3odd-Phase A4** (`6i+7` steps): F→D + D→B init + BD_iter + 3 tail to C.
    Like `m2odd_phaseA4` but with `[F]*>ones 3*>blank` tail (one more T),
    ending at `{C, T, ones 2*>blank, ones (6i+7)*>blank}`. -/
private lemma m3odd_phaseA4 (i : Nat) :
    srun tm
      { state := some stF, head := false,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 2))
                  (Side.prepend [false] (Side.prepend (ones 3) blank∞))),
        right := blank∞ } (6 * i + 7) =
    { state := some stC, head := true,
      left := Side.prepend (ones 2) blank∞,
      right := Side.prepend (ones (6 * i + 7)) blank∞ } := by
  rw [show (6 * i + 7 : Nat) = 1 + (1 + (2 * (3 * i + 1) + 3)) from by ring, srun_add]
  have h_step1 : srun tm
      { state := some stF, head := false,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 2))
                  (Side.prepend [false] (Side.prepend (ones 3) blank∞))),
        right := blank∞ } 1 =
      { state := some stD, head := false,
        left := Side.prepend ([true, false] ×× (3 * i + 2))
                  (Side.prepend [false] (Side.prepend (ones 3) blank∞)),
        right := Side.prepend (ones 1) blank∞ } := by
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_step1, srun_add,
      show ([true, false] ×× (3 * i + 2) : List Sym)
        = [true, false] ++ [true, false] ×× (3 * i + 1) from by
        show [true, false] ×× ((3 * i + 1) + 1) = _; rfl,
      Side.prepend_append]
  have h_step2 : srun tm
      { state := some stD, head := false,
        left := Side.prepend [true, false]
                  (Side.prepend ([true, false] ×× (3 * i + 1))
                    (Side.prepend [false] (Side.prepend (ones 3) blank∞))),
        right := Side.prepend (ones 1) blank∞ } 1 =
      { state := some stB, head := true,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 1))
                    (Side.prepend [false] (Side.prepend (ones 3) blank∞))),
        right := Side.prepend (ones 2) blank∞ } := by
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_step2, srun_add,
      BD_iter (3 * i + 1) (Side.prepend [false] (Side.prepend (ones 3) blank∞)) 2,
      show Side.prepend (ones (2 + 2 * (3 * i + 1))) blank∞ =
        Side.prepend (ones 1) (Side.prepend (ones (6 * i + 3)) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 1 + (6 * i + 3) = 2 + 2 * (3 * i + 1) from by ring]]
  -- 3 tail steps: B,T→1LD; D,F→1LB; B,F→1LC.  Pull T from ones 3 leaves ones 2.
  simp [srun, sstep, tm, Side.prepend, ones]
  show Side.prepend (ones 4) (Side.prepend (ones (6 * i + 3)) blank∞) =
    Side.prepend (ones (1 + (1 + (2 * (3 * i + 1) + 3)))) blank∞
  rw [← Side.prepend_append, ones_append,
      show 4 + (6 * i + 3) = 1 + (1 + (2 * (3 * i + 1) + 3)) from by ring]

/-- **closing_m3_odd Phase A** (`12i+16` steps): from
    `{A, F, [T,F]*>ones 3*>blank, ones (6i+2)*>blank}` to
    `{A, T, ones 1*>blank, ones (6i+8)*>blank}`. -/
private lemma closing_m3_odd_phaseA (i : Nat) :
    srun tm
      { state := some stA, head := false,
        left := Side.prepend [true, false] (Side.prepend (ones 3) blank∞),
        right := Side.prepend (ones (6 * i + 2)) blank∞ } (12 * i + 16) =
    { state := some stA, head := true,
      left := Side.prepend (ones 1) blank∞,
      right := Side.prepend (ones (6 * i + 8)) blank∞ } := by
  rw [show (12 * i + 16 : Nat) = 3 + ((6 * i + 4) + (1 + ((6 * i + 7) + 1))) from by ring,
      srun_add, m3odd_phaseA1 i,
      srun_add, m3odd_phaseA2 i,
      srun_add]
  have h_phaseA3 : srun tm
      { state := some stE, head := false,
        left := Side.prepend ([true, false] ×× (3 * i + 2))
                (Side.prepend [false] (Side.prepend (ones 3) blank∞)),
        right := blank∞ } 1 =
      { state := some stF, head := false,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 2))
                (Side.prepend [false] (Side.prepend (ones 3) blank∞))),
        right := blank∞ } := by
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_phaseA3, srun_add, m3odd_phaseA4 i]
  -- Phase A5: 1 step C,T→1LA.  Pull T from ones 2 → state A head=T, left=ones 1.
  show srun tm
      { state := some stC, head := true,
        left := Side.prepend (ones 2) blank∞,
        right := Side.prepend (ones (6 * i + 7)) blank∞ } 1 =
      { state := some stA, head := true,
        left := Side.prepend (ones 1) blank∞,
        right := Side.prepend (ones (6 * i + 8)) blank∞ }
  rw [show Side.prepend (ones (6 * i + 8)) blank∞ =
        Side.cons true (Side.prepend (ones (6 * i + 7)) blank∞) from by
        show Side.prepend (ones (6 * i + 7 + 1)) blank∞ = _; rfl]
  simp [srun, sstep, tm, Side.prepend, ones]

/-- **m3odd-Phase B1** (`6i+9` steps): EA-right cycle from
    `{A, T, ones 1*>blank, ones (6i+8)*>blank}` to
    `{E, F, [T,F]××(3i+4)*>ones 2*>blank, blank}`. -/
private lemma m3odd_phaseB1 (i : Nat) :
    srun tm
      { state := some stA, head := true,
        left := Side.prepend (ones 1) blank∞,
        right := Side.prepend (ones (6 * i + 8)) blank∞ } (6 * i + 9) =
    { state := some stE, head := false,
      left := Side.prepend ([true, false] ×× (3 * i + 4))
                (Side.prepend (ones 2) blank∞),
      right := blank∞ } := by
  rw [show (6 * i + 9 : Nat) = 1 + ((6 * i + 6) + 2) from by ring, srun_add]
  have h_step1 : srun tm
      { state := some stA, head := true,
        left := Side.prepend (ones 1) blank∞,
        right := Side.prepend (ones (6 * i + 8)) blank∞ } 1 =
      { state := some stE, head := true,
        left := Side.prepend (ones 2) blank∞,
        right := Side.prepend (ones (6 * i + 7)) blank∞ } := by
    rw [show Side.prepend (ones (6 * i + 8)) blank∞ =
          Side.cons true (Side.prepend (ones (6 * i + 7)) blank∞) from by
          show Side.prepend (ones (6 * i + 7 + 1)) blank∞ = _; rfl]
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_step1, srun_add,
      show (6 * i + 6 : Nat) = 2 * (3 * i + 3) from by ring,
      show Side.prepend (ones (6 * i + 7)) blank∞ =
        Side.prepend (ones (2 * (3 * i + 3))) (Side.prepend (ones 1) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 2 * (3 * i + 3) + 1 = 6 * i + 7 from by ring],
      EA_shift (3 * i + 3) (Side.prepend (ones 2) blank∞)
        (Side.prepend (ones 1) blank∞),
      show ([true, false] ×× (3 * i + 4) : List Sym)
        = [true, false] ++ [true, false] ×× (3 * i + 3) from by
        show [true, false] ×× ((3 * i + 3) + 1) = _; rfl,
      Side.prepend_append]
  simp [srun, sstep, tm, Side.prepend, ones]

/-- **m3odd-Phase B3** (`6i+12` steps): F→D + D→B init + BD_iter k=3i+3 + 4 tail
    to state E head=F.  From `{F, F, [F]*>[T,F]××(3i+4)*>ones 2*>blank, blank}`
    to `{E, F, blank, ones (6i+12)*>blank}`. -/
private lemma m3odd_phaseB3 (i : Nat) :
    srun tm
      { state := some stF, head := false,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 4))
                  (Side.prepend (ones 2) blank∞)),
        right := blank∞ } (6 * i + 12) =
    { state := some stE, head := false,
      left := blank∞,
      right := Side.prepend (ones (6 * i + 12)) blank∞ } := by
  rw [show (6 * i + 12 : Nat) = 1 + (1 + (2 * (3 * i + 3) + 4)) from by ring, srun_add]
  have h_step1 : srun tm
      { state := some stF, head := false,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 4))
                  (Side.prepend (ones 2) blank∞)),
        right := blank∞ } 1 =
      { state := some stD, head := false,
        left := Side.prepend ([true, false] ×× (3 * i + 4))
                  (Side.prepend (ones 2) blank∞),
        right := Side.prepend (ones 1) blank∞ } := by
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_step1, srun_add,
      show ([true, false] ×× (3 * i + 4) : List Sym)
        = [true, false] ++ [true, false] ×× (3 * i + 3) from by
        show [true, false] ×× ((3 * i + 3) + 1) = _; rfl,
      Side.prepend_append]
  have h_step2 : srun tm
      { state := some stD, head := false,
        left := Side.prepend [true, false]
                  (Side.prepend ([true, false] ×× (3 * i + 3))
                    (Side.prepend (ones 2) blank∞)),
        right := Side.prepend (ones 1) blank∞ } 1 =
      { state := some stB, head := true,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 3))
                    (Side.prepend (ones 2) blank∞)),
        right := Side.prepend (ones 2) blank∞ } := by
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_step2, srun_add,
      BD_iter (3 * i + 3) (Side.prepend (ones 2) blank∞) 2,
      show Side.prepend (ones (2 + 2 * (3 * i + 3))) blank∞ =
        Side.prepend (ones 1) (Side.prepend (ones (6 * i + 7)) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 1 + (6 * i + 7) = 2 + 2 * (3 * i + 3) from by ring]]
  -- 4 tail steps: B,T→1LD; D,F→1LB; B,T→1LD; D,T→1LE.
  simp [srun, sstep, tm, Side.prepend, ones]
  show Side.prepend (ones 5) (Side.prepend (ones (6 * i + 7)) blank∞) =
    Side.prepend (ones (1 + (1 + (2 * (3 * i + 3) + 4)))) blank∞
  rw [← Side.prepend_append, ones_append,
      show 5 + (6 * i + 7) = 1 + (1 + (2 * (3 * i + 3) + 4)) from by ring]

/-- **closing_m3_odd Phase B** (`18i+40` steps): from
    `{A, T, ones 1*>blank, ones (6i+8)*>blank}` to A(6i+10, 1). -/
private lemma closing_m3_odd_phaseB (i : Nat) :
    srun tm
      { state := some stA, head := true,
        left := Side.prepend (ones 1) blank∞,
        right := Side.prepend (ones (6 * i + 8)) blank∞ } (18 * i + 40) =
    { state := some stA, head := false,
      left := Side.prepend [false, true, false] (Side.prepend (ones (6 * i + 10)) blank∞),
      right := blank∞ } := by
  rw [show (18 * i + 40 : Nat) = (6 * i + 9) + (1 + ((6 * i + 12) + (1 + ((6 * i + 12) + 5))))
        from by ring,
      srun_add, m3odd_phaseB1 i, srun_add]
  -- B2: 1 step E,F→0RF.
  have h_B2 : srun tm
      { state := some stE, head := false,
        left := Side.prepend ([true, false] ×× (3 * i + 4))
                  (Side.prepend (ones 2) blank∞),
        right := blank∞ } 1 =
      { state := some stF, head := false,
        left := Side.prepend [false] (Side.prepend ([true, false] ×× (3 * i + 4))
                  (Side.prepend (ones 2) blank∞)),
        right := blank∞ } := by
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_B2, srun_add, m3odd_phaseB3 i, srun_add]
  -- B4: 1 step E,F→0RF.
  have h_B4 : srun tm
      { state := some stE, head := false,
        left := blank∞,
        right := Side.prepend (ones (6 * i + 12)) blank∞ } 1 =
      { state := some stF, head := true,
        left := blank∞,
        right := Side.prepend (ones (6 * i + 11)) blank∞ } := by
    rw [show Side.prepend (ones (6 * i + 12)) blank∞ =
          Side.cons true (Side.prepend (ones (6 * i + 11)) blank∞) from by
          show Side.prepend (ones (6 * i + 11 + 1)) blank∞ = _; rfl]
    simp [srun, sstep, tm, Side.prepend, ones]
  rw [h_B4, srun_add,
      -- B5: F-sweep right (6i+12 steps).
      show (6 * i + 12 : Nat) = (6 * i + 11) + 1 from by ring,
      F_sweep_right blank∞ (6 * i + 11),
      -- B6: 5 tail steps.  Pre-split ones (6i+12) = ones 2 *> ones (6i+10).
      show Side.prepend (ones (6 * i + 11 + 1)) blank∞ =
        Side.prepend (ones 2) (Side.prepend (ones (6 * i + 10)) blank∞) from by
        rw [← Side.prepend_append, ones_append,
            show 2 + (6 * i + 10) = 6 * i + 11 + 1 from by ring]]
  simp [srun, sstep, tm, Side.prepend, ones]

/-- **closing_m3_odd** (`30i+56` steps): composes phaseA and phaseB. -/
private lemma closing_m3_odd (i : Nat) :
    srun tm
      { state := some stA, head := false,
        left := Side.prepend [true, false] (Side.prepend (ones 3) blank∞),
        right := Side.prepend (ones (6 * i + 2)) blank∞ } (30 * i + 56) =
    { state := some stA, head := false,
      left := Side.prepend [false, true, false] (Side.prepend (ones (6 * i + 10)) blank∞),
      right := blank∞ } := by
  rw [show (30 * i + 56 : Nat) = (12 * i + 16) + (18 * i + 40) from by ring,
      srun_add, closing_m3_odd_phaseA i, closing_m3_odd_phaseB i]

/-- **m=3 odd → reset** (`dt = 6i² + 40i + 59`).  `A(3, 2i+1) → A(6i+10, 1)`.

    Decomposition: zebra rewrite (`zebra (2i+1) = zebra (2i) ++ [F,T]`) +
    `right_push_g` (3) + Side rewrite + `absorb_iter L=[T,F]++ones 3*>blank, t=0`
    (`6i²+10i`) + `closing_m3_odd` (`30i+56`) = `6i²+40i+59`. -/
theorem m3_odd_reset (i : Nat) :
    srun tm (A_config 3 (2 * i + 1)) (6*i*i + 40*i + 59) =
      A_config (6 * i + 10) 1 := by
  unfold A_config
  have h_left :
      Side.prepend (zebra (2 * i + 1))
        (Side.prepend [false] (Side.prepend (ones 3) blank∞))
      = Side.prepend (zebra (2 * i))
          (Side.prepend [false] (Side.prepend [true, false]
            (Side.prepend (ones 3) blank∞))) := by
    simp only [← Side.prepend_append]
    congr 1
    rw [show (zebra (2 * i + 1) : List Sym) = zebra (2 * i) ++ [false, true] from
          zebra_succ_append (2 * i)]
    simp [List.append_assoc]
  rw [h_left,
      show (6 * i * i + 40 * i + 59 : Nat)
          = 3 + ((6 * i * i + 10 * i + 12 * 0 * i) + (30 * i + 56)) from by ring,
      srun_add,
      right_push_g (Side.prepend [true, false] (Side.prepend (ones 3) blank∞)) i,
      srun_add,
      show (ones 2 : List Sym) = ones (6 * 0 + 2) from rfl,
      show Side.prepend ([true, false] ×× (2 * i))
            (Side.prepend [true, false] (Side.prepend (ones 3) blank∞))
        = Side.prepend ([true, false] ×× (2 * i))
            (Side.prepend ([true, false] ++ ones 3) blank∞) from by
        rw [Side.prepend_append],
      absorb_iter (Side.prepend ([true, false] ++ ones 3) blank∞) 0 i,
      show 0 + i = i from by ring,
      show Side.prepend ([true, false] ++ ones 3) blank∞
         = Side.prepend [true, false] (Side.prepend (ones 3) blank∞) from by
        rw [Side.prepend_append],
      closing_m3_odd i]
  rfl

-- ============================================================
-- Initial configuration
-- ============================================================

/-- Config-form initial run target (matches SConfig form under `.toSConfig`). -/
def Init_Config_A11 : Config 6 :=
  { state := some stA,
    head := false,
    left := [false, true, false, true, false],
    right := [] }

/-- Config-side lemma: from the blank tape, in 15 steps we reach the concrete
    `Init_Config_A11`, which is the tape `0^inf 1 0 1 0 [A]> 0^inf`. -/
lemma init_to_Init_Config_A11 :
    run tm (initConfig 6) 15 = Init_Config_A11 := by
  decide

/-- Bridge: `Init_Config_A11` lifts to `A_config 1 1`. -/
lemma Init_Config_A11_toSConfig :
    Init_Config_A11.toSConfig = A_config 1 1 := by
  simp [Init_Config_A11, A_config, Config.toSConfig, zebra]

/-- From the blank tape, the TM reaches macro configuration `A(1, 1)`
    (= wiki's `A(1, 10)`) at step 15.  I.e. tape = `0^inf 1 (01)^1 0 [A]> 0^inf`. -/
theorem init_to_A11 :
    srun tm (sinitConfig 6) 15 = A_config 1 1 := by
  have h := congrArg Config.toSConfig init_to_Init_Config_A11
  rw [toSConfig_run, toSConfig_initConfig, Init_Config_A11_toSConfig] at h
  exact h

-- ============================================================
-- Halting characterization (correspondence to macro orbit)
-- ============================================================

/-- The TM cannot halt before step 15 (verified by `decide` over the concrete
    initial trajectory). -/
private lemma no_halt_before_15 : ∀ k < 15, (run tm (initConfig 6) k).state ≠ none := by
  decide

/-- **Halting bridge**: the TM halts from the blank tape iff the macro orbit
    starting at `A(1, 1)` (= wiki's `A(1, 10)`) eventually halts.  Connects
    Config-level halting (the BB question) to SConfig-level macro analysis. -/
theorem tm_halt_iff :
    (∃ k, (run tm (initConfig 6) k).state = none) ↔
    (∃ k, (srun tm (A_config 1 1) k).state = none) := by
  have h_eq : ∀ k, (run tm (initConfig 6) k).state =
                    (srun tm (sinitConfig 6) k).state := fun k => by
    change _ = (srun tm (initConfig 6).toSConfig k).state
    rw [← toSConfig_run]; rfl
  constructor
  · rintro ⟨k, hk⟩
    by_cases h : k < 15
    · exact absurd hk (no_halt_before_15 k h)
    · push_neg at h
      refine ⟨k - 15, ?_⟩
      rw [h_eq, show k = 15 + (k - 15) from by omega, srun_add, init_to_A11] at hk
      exact hk
  · rintro ⟨k, hk⟩
    refine ⟨15 + k, ?_⟩
    rw [h_eq, srun_add, init_to_A11]; exact hk

/-- **Macro halt** predicate: an inductive characterization of which
    `A(m, n)` configurations eventually halt under the macro rules.

    A macro state `(m, n)` halts iff it matches one of the halt rules
    (`m1_even_halt`, `m2_even_halt`, `m2_odd_halt`) directly, or it transitions
    via a shift/reset rule to another `MacroHalts` state. -/
inductive MacroHalts : Nat → Nat → Prop where
  | m1_even (i : Nat) : MacroHalts 1 (2 * i)
  | m2_even (i : Nat) : MacroHalts 2 (2 * i)
  | m2_odd (i : Nat) : MacroHalts 2 (2 * i + 1)
  | m1_odd (i : Nat) : MacroHalts (6 * i + 7) 1 → MacroHalts 1 (2 * i + 1)
  | m3_even (i : Nat) : MacroHalts (6 * i + 6) 1 → MacroHalts 3 (2 * i)
  | m3_odd (i : Nat) : MacroHalts (6 * i + 10) 1 → MacroHalts 3 (2 * i + 1)
  | m4_even (i : Nat) : MacroHalts 1 (3 * i + 3) → MacroHalts 4 (2 * i)
  | m4_odd (i : Nat) : MacroHalts 1 (3 * i + 5) → MacroHalts 4 (2 * i + 1)
  | shift_even (m i : Nat) : MacroHalts (m + 1) (3 * i + 4) → MacroHalts (m + 5) (2 * i)
  | shift_odd (m i : Nat) : MacroHalts (m + 1) (3 * i + 6) → MacroHalts (m + 5) (2 * i + 1)

/-- **Forward implication**: if the macro orbit from `(m, n)` halts (per the
    inductive `MacroHalts` predicate), then the TM halts from `A(m, n)`. -/
theorem A_halts_of_MacroHalts (m n : Nat) (h : MacroHalts m n) :
    ∃ k, (srun tm (A_config m n) k).state = none := by
  induction h with
  | m1_even i => exact ⟨_, m1_even_halt i⟩
  | m2_even i => exact ⟨_, m2_even_halt i⟩
  | m2_odd i => exact ⟨_, m2_odd_halt i⟩
  | m1_odd i _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨6*i*i + 28*i + 37 + k, ?_⟩
    rw [srun_add, m1_odd_reset]; exact hk
  | m3_even i _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨6*i*i + 28*i + 33 + k, ?_⟩
    rw [srun_add, m3_even_reset]; exact hk
  | m3_odd i _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨6*i*i + 40*i + 59 + k, ?_⟩
    rw [srun_add, m3_odd_reset]; exact hk
  | m4_even i _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨6*i*i + 28*i + 28 + k, ?_⟩
    rw [srun_add, shift_m4_even]; exact hk
  | m4_odd i _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨6*i*i + 40*i + 54 + k, ?_⟩
    rw [srun_add, shift_m4_odd]; exact hk
  | shift_even m i _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨6*i*i + 28*i + 28 + k, ?_⟩
    rw [srun_add, shift_even_high]; exact hk
  | shift_odd m i _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨6*i*i + 40*i + 54 + k, ?_⟩
    rw [srun_add, shift_odd_high]; exact hk

/-- **Combined**: if `MacroHalts 1 1` holds, then the TM halts from the blank
    tape.  This is the constructive direction connecting the macro orbit
    characterization to the BB halting question. -/
theorem tm_halts_of_MacroHalts_11 (h : MacroHalts 1 1) :
    ∃ k, (run tm (initConfig 6) k).state = none :=
  tm_halt_iff.mpr (A_halts_of_MacroHalts 1 1 h)

-- ============================================================
-- Mathematical formulation: macro-step map `f` and iteration
-- ============================================================

/-- **Macro-step map `f`**: encodes the 10 proved macro rules as a single
    transition map on `(m, n)` pairs.  `f m n = none` means HALT;
    `f m n = some (m', n')` means transition to `(m', n')`.

    Cases (with `n = 2i` or `n = 2i+1`):
    - `f 1 (2i) = none`                         (m1_even_halt)
    - `f 1 (2i+1) = some (6i+7, 1)`             (m1_odd_reset)
    - `f 2 _ = none`                            (m2_*_halt)
    - `f 3 (2i) = some (6i+6, 1)`               (m3_even_reset)
    - `f 3 (2i+1) = some (6i+10, 1)`            (m3_odd_reset)
    - `f 4 (2i) = some (1, 3i+3)`               (shift_m4_even)
    - `f 4 (2i+1) = some (1, 3i+5)`             (shift_m4_odd)
    - `f (m+5) (2i) = some (m+1, 3i+4)`         (shift_even_high)
    - `f (m+5) (2i+1) = some (m+1, 3i+6)`       (shift_odd_high)

    For `m=0` (non-canonical) we return `none` to keep the function total. -/
def f : Nat → Nat → Option (Nat × Nat)
  | 0, _ => none
  | 1, n => if n % 2 = 0 then none else some (3 * n + 4, 1)
  | 2, _ => none
  | 3, n => if n % 2 = 0 then some (3 * n + 6, 1) else some (3 * n + 7, 1)
  | 4, n => if n % 2 = 0 then some (1, 3 * (n / 2) + 3)
            else some (1, 3 * ((n - 1) / 2) + 5)
  | m + 5, n => if n % 2 = 0 then some (m + 1, 3 * (n / 2) + 4)
                else some (m + 1, 3 * ((n - 1) / 2) + 6)

/-- Iterated `f`.  `fIter k (m, n)` applies `f` exactly `k` times starting
    from `(m, n)`; returns `none` if any application yields `none`. -/
def fIter : Nat → Nat × Nat → Option (Nat × Nat)
  | 0, mn => some mn
  | k + 1, mn =>
    match fIter k mn with
    | none => none
    | some (m, n) => f m n

/-- Helper: chaining lemma for `fIter`.  If `f m n = some (m', n')`, then
    `fIter (k+1) (m, n) = fIter k (m', n')`. -/
private lemma fIter_succ_chain (k : Nat) (mn mn' : Nat × Nat)
    (h : f mn.1 mn.2 = some mn') :
    fIter (k + 1) mn = fIter k mn' := by
  induction k generalizing mn with
  | zero => simp [fIter, h]
  | succ k ih =>
    show (match fIter (k + 1) mn with | none => none | some (m, n) => f m n)
       = (match fIter k mn' with | none => none | some (m, n) => f m n)
    rw [ih mn h]

/-- Helper: `f m n = none` with `m ≥ 1` implies `(m, n)` is a halt-leaf
    (i.e., `MacroHalts m n` holds via a base constructor). -/
private lemma MacroHalts_of_f_halt (m n : Nat) (hm : 1 ≤ m) (hf : f m n = none) :
    MacroHalts m n := by
  match m with
  | 0 => omega
  | 1 =>
    have hn : n % 2 = 0 := by
      by_contra h
      simp [f, h] at hf
    obtain ⟨i, rfl⟩ : ∃ i, n = 2 * i := ⟨n / 2, by omega⟩
    exact MacroHalts.m1_even i
  | 2 =>
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · obtain ⟨i, rfl⟩ : ∃ i, n = 2 * i := ⟨n / 2, by omega⟩
      exact MacroHalts.m2_even i
    · obtain ⟨i, rfl⟩ : ∃ i, n = 2 * i + 1 := ⟨n / 2, by omega⟩
      exact MacroHalts.m2_odd i
  | 3 => exfalso; rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;> simp [f, hn] at hf
  | 4 => exfalso; rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;> simp [f, hn] at hf
  | k + 5 => exfalso; rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;> simp [f, hn] at hf

/-- Helper: outputs of `f` (from `m ≥ 1` inputs) preserve `m' ≥ 1`. -/
private lemma f_some_pos_m (m n m' n' : Nat) (hm : 1 ≤ m)
    (hf : f m n = some (m', n')) : 1 ≤ m' := by
  match m with
  | 0 => omega
  | 1 =>
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · simp [f, hn] at hf
    · simp [f, hn] at hf; omega
  | 2 => simp [f] at hf
  | 3 =>
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;>
      (simp [f, hn] at hf; omega)
  | 4 =>
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;>
      (simp [f, hn] at hf; omega)
  | k + 5 =>
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;>
      (simp [f, hn] at hf; omega)

/-- Helper: back-step for `MacroHalts`.  If `f m n = some (m', n')` and
    `MacroHalts m' n'` holds, then `MacroHalts m n` holds (via the appropriate
    inductive constructor matching `f`'s case). -/
private lemma MacroHalts_back_step (m n m' n' : Nat) (hm : 1 ≤ m)
    (hf : f m n = some (m', n')) (h' : MacroHalts m' n') : MacroHalts m n := by
  match m with
  | 0 => omega
  | 1 =>
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · simp [f, hn] at hf
    · obtain ⟨i, rfl⟩ : ∃ i, n = 2 * i + 1 := ⟨n / 2, by omega⟩
      simp [f, show (2 * i + 1) % 2 ≠ 0 from by omega] at hf
      obtain ⟨h_m, h_n⟩ := hf
      have h_m_eq : m' = 6 * i + 7 := by omega
      have h_n_eq : n' = 1 := by omega
      rw [h_m_eq, h_n_eq] at h'
      exact MacroHalts.m1_odd i h'
  | 2 => simp [f] at hf
  | 3 =>
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · obtain ⟨i, rfl⟩ : ∃ i, n = 2 * i := ⟨n / 2, by omega⟩
      simp [f, show (2 * i) % 2 = 0 from by omega] at hf
      obtain ⟨h_m, h_n⟩ := hf
      have h_m_eq : m' = 6 * i + 6 := by omega
      have h_n_eq : n' = 1 := by omega
      rw [h_m_eq, h_n_eq] at h'
      exact MacroHalts.m3_even i h'
    · obtain ⟨i, rfl⟩ : ∃ i, n = 2 * i + 1 := ⟨n / 2, by omega⟩
      simp [f, show (2 * i + 1) % 2 ≠ 0 from by omega] at hf
      obtain ⟨h_m, h_n⟩ := hf
      have h_m_eq : m' = 6 * i + 10 := by omega
      have h_n_eq : n' = 1 := by omega
      rw [h_m_eq, h_n_eq] at h'
      exact MacroHalts.m3_odd i h'
  | 4 =>
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · obtain ⟨i, rfl⟩ : ∃ i, n = 2 * i := ⟨n / 2, by omega⟩
      simp [f, show (2 * i) % 2 = 0 from by omega,
            show 2 * i / 2 = i from by omega] at hf
      obtain ⟨h_m, h_n⟩ := hf
      have h_m_eq : m' = 1 := by omega
      have h_n_eq : n' = 3 * i + 3 := by omega
      rw [h_m_eq, h_n_eq] at h'
      exact MacroHalts.m4_even i h'
    · obtain ⟨i, rfl⟩ : ∃ i, n = 2 * i + 1 := ⟨n / 2, by omega⟩
      simp [f, show (2 * i + 1) % 2 ≠ 0 from by omega,
            show (2 * i + 1 - 1) / 2 = i from by omega] at hf
      obtain ⟨h_m, h_n⟩ := hf
      have h_m_eq : m' = 1 := by omega
      have h_n_eq : n' = 3 * i + 5 := by omega
      rw [h_m_eq, h_n_eq] at h'
      exact MacroHalts.m4_odd i h'
  | k + 5 =>
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · obtain ⟨i, rfl⟩ : ∃ i, n = 2 * i := ⟨n / 2, by omega⟩
      simp [f, show (2 * i) % 2 = 0 from by omega,
            show 2 * i / 2 = i from by omega] at hf
      obtain ⟨h_m, h_n⟩ := hf
      have h_m_eq : m' = k + 1 := by omega
      have h_n_eq : n' = 3 * i + 4 := by omega
      rw [h_m_eq, h_n_eq] at h'
      exact MacroHalts.shift_even k i h'
    · obtain ⟨i, rfl⟩ : ∃ i, n = 2 * i + 1 := ⟨n / 2, by omega⟩
      simp [f, show (2 * i + 1) % 2 ≠ 0 from by omega,
            show (2 * i + 1 - 1) / 2 = i from by omega] at hf
      obtain ⟨h_m, h_n⟩ := hf
      have h_m_eq : m' = k + 1 := by omega
      have h_n_eq : n' = 3 * i + 6 := by omega
      rw [h_m_eq, h_n_eq] at h'
      exact MacroHalts.shift_odd k i h'

/-- Helper: the backward direction of `MacroHalts_iff_fIter_halts` proved
    by induction on `k` (generalizing over `(m, n)` so the IH applies to
    transitioned states `(m', n')`). -/
private lemma MacroHalts_of_fIter_halt_aux : ∀ (k : Nat) (m n : Nat),
    1 ≤ m → fIter k (m, n) = none → MacroHalts m n := by
  intro k
  induction k with
  | zero => intros m n _ hk; simp [fIter] at hk
  | succ k ih =>
    intros m n hm hk
    rcases h_eq : f m n with _ | ⟨m', n'⟩
    · exact MacroHalts_of_f_halt m n hm h_eq
    · have h_chain : fIter (k + 1) (m, n) = fIter k (m', n') :=
        fIter_succ_chain k (m, n) (m', n') (by simp; exact h_eq)
      rw [h_chain] at hk
      have hm' : 1 ≤ m' := f_some_pos_m m n m' n' hm h_eq
      have h_macro : MacroHalts m' n' := ih m' n' hm' hk
      exact MacroHalts_back_step m n m' n' hm h_eq h_macro

/-- **Equivalence between inductive `MacroHalts` and `fIter` halt**: a state
    `(m, n)` (with `m ≥ 1`) halts under the macro orbit iff iterating `f`
    eventually returns `none`.  The constraint `m ≥ 1` excludes the
    non-canonical `m = 0` case (where `f 0 _ = none` but `MacroHalts` has no
    base constructor for `m = 0`). -/
theorem MacroHalts_iff_fIter_halts (m n : Nat) (hm : 1 ≤ m) :
    MacroHalts m n ↔ ∃ k, fIter k (m, n) = none := by
  constructor
  · intro h
    induction h with
    | m1_even i =>
      refine ⟨1, ?_⟩
      simp [fIter, f, show (2 * i) % 2 = 0 from by omega]
    | m2_even i => exact ⟨1, by simp [fIter, f]⟩
    | m2_odd i => exact ⟨1, by simp [fIter, f]⟩
    | m1_odd i _ ih =>
      obtain ⟨k, hk⟩ := ih (by omega)
      refine ⟨k + 1, ?_⟩
      have h_step : f 1 (2 * i + 1) = some (6 * i + 7, 1) := by
        simp [f, show (2 * i + 1) % 2 ≠ 0 from by omega]; ring
      rw [fIter_succ_chain k (1, 2 * i + 1) (6 * i + 7, 1) h_step]; exact hk
    | m3_even i _ ih =>
      obtain ⟨k, hk⟩ := ih (by omega)
      refine ⟨k + 1, ?_⟩
      have h_step : f 3 (2 * i) = some (6 * i + 6, 1) := by
        simp [f, show (2 * i) % 2 = 0 from by omega]; ring
      rw [fIter_succ_chain k (3, 2 * i) (6 * i + 6, 1) h_step]; exact hk
    | m3_odd i _ ih =>
      obtain ⟨k, hk⟩ := ih (by omega)
      refine ⟨k + 1, ?_⟩
      have h_step : f 3 (2 * i + 1) = some (6 * i + 10, 1) := by
        simp [f, show (2 * i + 1) % 2 ≠ 0 from by omega]; ring
      rw [fIter_succ_chain k (3, 2 * i + 1) (6 * i + 10, 1) h_step]; exact hk
    | m4_even i _ ih =>
      obtain ⟨k, hk⟩ := ih (by omega)
      refine ⟨k + 1, ?_⟩
      have h_step : f 4 (2 * i) = some (1, 3 * i + 3) := by
        simp [f, show (2 * i) % 2 = 0 from by omega, show 2 * i / 2 = i from by omega]
      rw [fIter_succ_chain k (4, 2 * i) (1, 3 * i + 3) h_step]; exact hk
    | m4_odd i _ ih =>
      obtain ⟨k, hk⟩ := ih (by omega)
      refine ⟨k + 1, ?_⟩
      have h_step : f 4 (2 * i + 1) = some (1, 3 * i + 5) := by
        simp [f, show (2 * i + 1) % 2 ≠ 0 from by omega,
              show (2 * i + 1 - 1) / 2 = i from by omega]
      rw [fIter_succ_chain k (4, 2 * i + 1) (1, 3 * i + 5) h_step]; exact hk
    | shift_even m i _ ih =>
      obtain ⟨k, hk⟩ := ih (by omega)
      refine ⟨k + 1, ?_⟩
      have h_step : f (m + 5) (2 * i) = some (m + 1, 3 * i + 4) := by
        simp [f, show (2 * i) % 2 = 0 from by omega, show 2 * i / 2 = i from by omega]
      rw [fIter_succ_chain k (m + 5, 2 * i) (m + 1, 3 * i + 4) h_step]; exact hk
    | shift_odd m i _ ih =>
      obtain ⟨k, hk⟩ := ih (by omega)
      refine ⟨k + 1, ?_⟩
      have h_step : f (m + 5) (2 * i + 1) = some (m + 1, 3 * i + 6) := by
        simp [f, show (2 * i + 1) % 2 ≠ 0 from by omega,
              show (2 * i + 1 - 1) / 2 = i from by omega]
      rw [fIter_succ_chain k (m + 5, 2 * i + 1) (m + 1, 3 * i + 6) h_step]; exact hk
  · rintro ⟨k, hk⟩
    -- Use auxiliary lemma generalized over (m, n).
    exact MacroHalts_of_fIter_halt_aux k m n hm hk

/-- **Macro simulation (some-case)**: if `f m n = some (m', n')` (so the
    macro rule is a non-halt transition), then there exists a positive step
    count `dt` such that `srun (A_config m n) dt = A_config m' n'`.  The
    `dt ≥ 1` constraint is needed for strong-induction termination. -/
private lemma simulates_macro_some (m n m' n' : Nat) (hm : 1 ≤ m)
    (hf : f m n = some (m', n')) :
    ∃ dt, 1 ≤ dt ∧ srun tm (A_config m n) dt = A_config m' n' := by
  match m with
  | 0 => omega
  | 1 =>
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · simp [f, hn] at hf
    · obtain ⟨i, rfl⟩ : ∃ i, n = 2 * i + 1 := ⟨n / 2, by omega⟩
      simp [f, show (2 * i + 1) % 2 ≠ 0 from by omega] at hf
      obtain ⟨h_m, h_n⟩ := hf
      have h_m_eq : m' = 6 * i + 7 := by omega
      have h_n_eq : n' = 1 := by omega
      refine ⟨6 * i * i + 28 * i + 37, by omega, ?_⟩
      rw [h_m_eq, h_n_eq]
      exact m1_odd_reset i
  | 2 => simp [f] at hf
  | 3 =>
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · obtain ⟨i, rfl⟩ : ∃ i, n = 2 * i := ⟨n / 2, by omega⟩
      simp [f, show (2 * i) % 2 = 0 from by omega] at hf
      obtain ⟨h_m, h_n⟩ := hf
      have h_m_eq : m' = 6 * i + 6 := by omega
      have h_n_eq : n' = 1 := by omega
      refine ⟨6 * i * i + 28 * i + 33, by omega, ?_⟩
      rw [h_m_eq, h_n_eq]
      exact m3_even_reset i
    · obtain ⟨i, rfl⟩ : ∃ i, n = 2 * i + 1 := ⟨n / 2, by omega⟩
      simp [f, show (2 * i + 1) % 2 ≠ 0 from by omega] at hf
      obtain ⟨h_m, h_n⟩ := hf
      have h_m_eq : m' = 6 * i + 10 := by omega
      have h_n_eq : n' = 1 := by omega
      refine ⟨6 * i * i + 40 * i + 59, by omega, ?_⟩
      rw [h_m_eq, h_n_eq]
      exact m3_odd_reset i
  | 4 =>
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · obtain ⟨i, rfl⟩ : ∃ i, n = 2 * i := ⟨n / 2, by omega⟩
      simp [f, show (2 * i) % 2 = 0 from by omega,
            show 2 * i / 2 = i from by omega] at hf
      obtain ⟨h_m, h_n⟩ := hf
      have h_m_eq : m' = 1 := by omega
      have h_n_eq : n' = 3 * i + 3 := by omega
      refine ⟨6 * i * i + 28 * i + 28, by omega, ?_⟩
      rw [h_m_eq, h_n_eq]
      exact shift_m4_even i
    · obtain ⟨i, rfl⟩ : ∃ i, n = 2 * i + 1 := ⟨n / 2, by omega⟩
      simp [f, show (2 * i + 1) % 2 ≠ 0 from by omega,
            show (2 * i + 1 - 1) / 2 = i from by omega] at hf
      obtain ⟨h_m, h_n⟩ := hf
      have h_m_eq : m' = 1 := by omega
      have h_n_eq : n' = 3 * i + 5 := by omega
      refine ⟨6 * i * i + 40 * i + 54, by omega, ?_⟩
      rw [h_m_eq, h_n_eq]
      exact shift_m4_odd i
  | k + 5 =>
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · obtain ⟨i, rfl⟩ : ∃ i, n = 2 * i := ⟨n / 2, by omega⟩
      simp [f, show (2 * i) % 2 = 0 from by omega,
            show 2 * i / 2 = i from by omega] at hf
      obtain ⟨h_m, h_n⟩ := hf
      have h_m_eq : m' = k + 1 := by omega
      have h_n_eq : n' = 3 * i + 4 := by omega
      refine ⟨6 * i * i + 28 * i + 28, by omega, ?_⟩
      rw [h_m_eq, h_n_eq]
      exact shift_even_high k i
    · obtain ⟨i, rfl⟩ : ∃ i, n = 2 * i + 1 := ⟨n / 2, by omega⟩
      simp [f, show (2 * i + 1) % 2 ≠ 0 from by omega,
            show (2 * i + 1 - 1) / 2 = i from by omega] at hf
      obtain ⟨h_m, h_n⟩ := hf
      have h_m_eq : m' = k + 1 := by omega
      have h_n_eq : n' = 3 * i + 6 := by omega
      refine ⟨6 * i * i + 40 * i + 54, by omega, ?_⟩
      rw [h_m_eq, h_n_eq]
      exact shift_odd_high k i

/-- **A-config halt → MacroHalts**: by strong induction on step count, if the
    TM halts in some number of steps from `A(m, n)` (with `m ≥ 1`), then the
    macro orbit also halts.  This is the "TM simulates macro" direction.

    Proof: case on `f m n`.  If `none`, `(m, n)` is a halt-leaf.  If
    `some (m', n')`, then by `simulates_macro_some` there's a step count `dt`
    such that `srun A(m,n) dt = A(m',n')` (which is alive).  By absorption of
    `state = none`, the halt step `k` must satisfy `k ≥ dt`, and recursing on
    `(m', n')` with step `k - dt < k` gives `MacroHalts m' n'`, then back-step
    to `MacroHalts m n`. -/
private lemma MacroHalts_of_A_halts (k : Nat) :
    ∀ (m n : Nat), 1 ≤ m → (srun tm (A_config m n) k).state = none →
      MacroHalts m n := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intros m n hm hk
    rcases h_eq : f m n with _ | ⟨m', n'⟩
    · exact MacroHalts_of_f_halt m n hm h_eq
    · have hm' : 1 ≤ m' := f_some_pos_m m n m' n' hm h_eq
      obtain ⟨dt, h_dt_pos, h_sim⟩ := simulates_macro_some m n m' n' hm h_eq
      have h_dt_alive : (srun tm (A_config m n) dt).state = some stA := by
        rw [h_sim]; rfl
      have hk_ge : dt ≤ k := by
        by_contra h
        push_neg at h
        have hdt_none : (srun tm (A_config m n) dt).state = none := by
          rw [show dt = k + (dt - k) from by omega, srun_add,
              srun_halted tm _ hk]
          exact hk
        rw [h_dt_alive] at hdt_none
        cases hdt_none
      have h_recurse : (srun tm (A_config m' n') (k - dt)).state = none := by
        rw [← h_sim, ← srun_add, show dt + (k - dt) = k from by omega]
        exact hk
      have h_macro' : MacroHalts m' n' :=
        ih (k - dt) (by omega) m' n' hm' h_recurse
      exact MacroHalts_back_step m n m' n' hm h_eq h_macro'

/-- **Halting correspondence (iff)**: the TM halts from the blank tape iff
    the math iteration `fIter` from `(1, 1)` eventually halts.

    Equivalent (per the conjecture stated in `wiki.txt`):
    <math>\text{TM halts} \iff \exists k,\ f^k(1, 1) = \mathrm{HALT}.</math>

    Proved in both directions:
    - Backward (`←`): math halts → `MacroHalts 1 1` → TM halts.
    - Forward (`→`): TM halts → A(1, 1) halts (via `tm_halt_iff`) →
      `MacroHalts 1 1` (via `MacroHalts_of_A_halts` strong induction) →
      `fIter` halts. -/
theorem tm_halt_iff_math :
    (∃ k, (run tm (initConfig 6) k).state = none) ↔
    ∃ k, fIter k (1, 1) = none := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := tm_halt_iff.mp h
    have h_macro : MacroHalts 1 1 := MacroHalts_of_A_halts k 1 1 (by omega) hk
    exact (MacroHalts_iff_fIter_halts 1 1 (by omega)).mp h_macro
  · rintro ⟨k, hk⟩
    have h_macro : MacroHalts 1 1 :=
      (MacroHalts_iff_fIter_halts 1 1 (by omega)).mpr ⟨k, hk⟩
    exact tm_halts_of_MacroHalts_11 h_macro

end HydraShift6
