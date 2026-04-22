import BusyLean
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Factorization.Basic

open BusyLean

namespace Shifty6

/-!
# 6-state TM `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`

BB(6) holdout candidate.  Halt/nonhalt is **not** the target; this file
records observed macro rules.

## Transition table
|   | 0   | 1   |
|---|-----|-----|
| A | 1RB | 1LA |
| B | 0LC | 0RC |
| C | 1LE | 1RD |
| D | 1RE | 1RC |
| E | 1LF | 0LA |
| F | --- | 1LE |

The only halting transition is `F,0 → ---`.  F is entered only from
`E,0 → 1LF`, so halting requires an E-with-0-head event whose left
neighbour is also a 0.

## Macro configuration (from previous-work/wiki.txt, Daniel Yuan)

With `A(m, n) := 1^m E> 1^n` (state E, head on first cell of the
right-block of ones, blank beyond both sides), the TM's E-turnarounds
compose into

```
  (0, 0)    → halt                                             dt = 2
  (1, 0)    → halt                                             dt = 4
  (1, n)    → halt for all n ≥ 1                               dt = 9
  (0, n+1)  → (2, n)                                           dt = 5
  (m+2, 0)  → (m, 3)      (degenerate — n = 0 case)            dt = 2
  (2m+2, n) → (3m+n+2, 2)                          (n ≥ 1)     dt = 6m² + 17m + 7 + 4mn + 7n
  (2m+3, n) → (m, m+n+4)                           (n ≥ 1)     dt = 2m² + 11m + 16   (indep. of n)
```

All step counts verified empirically by `sim.py` / `verify_dt.py`
(m ∈ 0..7, n ∈ 0..7 exhaustive).  The single-argument reformulation
(Yuan, Hipparcos) rewrites this as `f(b) = b + k + a` where
`b = (2a+1)·2^k` — the BB(6) question becomes whether the orbit `f^n(5)`
hits `2^k` or `3·2^k`.  Python simulations (sim.py / orbit.py) show
the trajectory growing steadily without reaching such powers in the
first ~10⁷ iterations.

## Representation

We split `A(m, n)` into two SConfig variants depending on whether the
head is over a `1` (right block non-empty) or a `0` (right block empty):

* `A_on m n`  represents `A(m, n+1)` — head on a `1`, with `n` more
  ones to its right before the blank.
* `A_off m`   represents `A(m, 0)`   — head on blank (right block empty).

This keeps the `head` field fixed within each variant.
-/

def tm : TM 6 := tm! "1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE"

-- Transition simp lemmas: evaluate `tm.tr st sym` without unfolding the literal.
@[simp] private theorem tr_A0 : tm.tr stA false = some (stB, true,  Dir.R) := rfl
@[simp] private theorem tr_A1 : tm.tr stA true  = some (stA, true,  Dir.L) := rfl
@[simp] private theorem tr_B0 : tm.tr stB false = some (stC, false, Dir.L) := rfl
@[simp] private theorem tr_B1 : tm.tr stB true  = some (stC, false, Dir.R) := rfl
@[simp] private theorem tr_C0 : tm.tr stC false = some (stE, true,  Dir.L) := rfl
@[simp] private theorem tr_C1 : tm.tr stC true  = some (stD, true,  Dir.R) := rfl
@[simp] private theorem tr_D0 : tm.tr stD false = some (stE, true,  Dir.R) := rfl
@[simp] private theorem tr_D1 : tm.tr stD true  = some (stC, true,  Dir.R) := rfl
@[simp] private theorem tr_E0 : tm.tr stE false = some (stF, true,  Dir.L) := rfl
@[simp] private theorem tr_E1 : tm.tr stE true  = some (stA, false, Dir.L) := rfl
@[simp] private theorem tr_F0 : tm.tr stF false = none := rfl
@[simp] private theorem tr_F1 : tm.tr stF true  = some (stE, true,  Dir.L) := rfl

-- ============================================================
-- Macro configurations
-- ============================================================

/-- `A_on m n` — state E scanning right at the first of a run of `n + 1`
ones, with `1^m` immediately to the left, blank beyond both sides.
Represents Yuan's `A(m, n+1) = 1^m E> 1^{n+1}`. -/
def A_on (m n : ℕ) : SConfig 6 :=
  { state := some stE,
    head := true,
    left := ones m *> blank∞,
    right := ones n *> blank∞ }

/-- `A_off m` — state E on a blank, with `1^m` immediately to the left,
blank beyond both sides.  Represents Yuan's `A(m, 0) = 1^m E> 0`. -/
def A_off (m : ℕ) : SConfig 6 :=
  { state := some stE,
    head := false,
    left := ones m *> blank∞,
    right := blank∞ }

-- ============================================================
-- Macro rules  (all sorried; verified empirically by verify_dt.py)
-- ============================================================

/-- **Rule R1a** (`dt = 5`).  `A(0, k+2) → A(2, k+1)`. -/
theorem rule_R1a (k : ℕ) :
    srun tm (A_on 0 (k + 1)) 5 = A_on 2 k := by
  simp [A_on, srun, sstep, tm]

/-- **Rule R1b** (`dt = 5`).  `A(0, 1) → A(2, 0)`.  Endpoint case of R1. -/
theorem rule_R1b :
    srun tm (A_on 0 0) 5 = A_off 2 := by
  simp [A_on, A_off, srun, sstep, tm]

-- ============================================================
-- Infrastructure for Rule R2
-- ============================================================

/-- Intermediate macro config for the R2 recursion.  When the sub-cycle runs,
an extra `[false] *> ones i` pattern accumulates between the outer left ones
block and the blank.  With `i = 0` this is equivalent to `A_on (2m+2) k`. -/
private def IntermOn (m i k : ℕ) : SConfig 6 :=
  { state := some stE, head := true,
    left := ones (2*m + 2) *> Side.cons false (ones i *> blank∞),
    right := ones k *> blank∞ }

/-- "Off" variant: head on blank, right exhausted. -/
private def IntermOff (m i : ℕ) : SConfig 6 :=
  { state := some stE, head := false,
    left := ones (2*m + 2) *> Side.cons false (ones i *> blank∞),
    right := blank∞ }

/-- **A-sweep lemma**: from state A head=1 with `ones j *> [false] *> L` on
the left, in `j+1` steps the head traverses all ones and lands on the false,
ending at state A head=0 with left=L and `ones (j+1)` deposited on right. -/
private lemma AL_sweep (j : ℕ) (L R : Side) :
    srun tm
      ({state := some stA, head := true,
        left := ones j *> Side.cons false L,
        right := R} : SConfig 6) (j + 1)
    = {state := some stA, head := false,
       left := L,
       right := ones (j + 1) *> R} := by
  induction j generalizing R with
  | zero => simp [srun, sstep, tm]
  | succ j' ih =>
    rw [show j' + 1 + 1 = 1 + (j' + 1) from by ring, srun_add]
    have h : srun tm
        ({state := some stA, head := true,
          left := ones (j' + 1) *> Side.cons false L,
          right := R} : SConfig 6) 1
        = {state := some stA, head := true,
           left := ones j' *> Side.cons false L,
           right := Side.cons true R} := by
      simp [srun, sstep, tm]
    rw [h, ih (Side.cons true R)]
    congr 1
    show Side.prepend (ones (j' + 1)) (Side.cons true R)
       = Side.prepend (ones (1 + (j' + 1))) R
    rw [show (1 + (j' + 1) : ℕ) = (j' + 1) + 1 from by ring,
        show ones ((j' + 1) + 1) = ones (j' + 1) ++ [true] from by
          rw [← ones_append]; rfl,
        Side.prepend_append]
    rfl

/-- **CD-sweep lemma**: `j` C-D pairs + one C,1 + one D,0 = `2j+2` steps.
From state C head=1 with `ones (2j) *> [false] *> R` on the right, the head
right-sweeps through the ones alternating C/D, then D reads the false and
fires D,0→E.  Ends at state E with `ones (2j+2)` pushed onto left. -/
private lemma CD_sweep (j : ℕ) (L R : Side) :
    srun tm
      ({state := some stC, head := true,
        left := L,
        right := ones (2*j) *> Side.cons false R} : SConfig 6) (2*j + 2)
    = {state := some stE, head := R.head,
       left := ones (2*j + 2) *> L,
       right := R.tail} := by
  induction j generalizing L with
  | zero => simp [srun, sstep, tm]
  | succ j' ih =>
    rw [show 2*(j'+1) + 2 = 2 + (2*j' + 2) from by ring, srun_add]
    have h : srun tm
        ({state := some stC, head := true,
          left := L,
          right := ones (2*(j'+1)) *> Side.cons false R} : SConfig 6) 2
        = {state := some stC, head := true,
           left := ones 2 *> L,
           right := ones (2*j') *> Side.cons false R} := by
      rw [show (2*(j'+1) : ℕ) = 2 + 2*j' from by ring,
          show ones (2 + 2*j') = ones 2 ++ ones (2*j') from (ones_append 2 (2*j')).symm]
      rw [Side.prepend_append]
      simp [srun, sstep, tm]
    rw [h, ih (ones 2 *> L)]
    congr 1
    rw [← Side.prepend_append, ones_append,
        show (2*j' + 2 + 2 : ℕ) = 2 + (2*j'+2) from by ring]

/-- **Sub-cycle**: the core building block.  `IntermOn m i (k+1) → IntermOn m
(i+1) k` in `4m+7` steps: consume one right-block one, push the pattern
further into the left "inner" ones block. -/
private lemma subcycle (m i k : ℕ) :
    srun tm (IntermOn m i (k + 1)) (4*m + 7) = IntermOn m (i + 1) k := by
  have hleft : (ones (2*m + 2) : List Sym) = true :: ones (2*m + 1) := rfl
  rw [show (4*m + 7 : ℕ) = 1 + ((2*m + 2) + (1 + (1 + (2*m + 2)))) from by ring,
      srun_add]
  have h1 : srun tm (IntermOn m i (k + 1)) 1
      = {state := some stA, head := true,
         left := ones (2*m + 1) *> Side.cons false (ones i *> blank∞),
         right := Side.cons false (ones (k + 1) *> blank∞)} := by
    unfold IntermOn; rw [hleft]; simp [srun, sstep, tm]
  rw [h1, srun_add, AL_sweep (2*m + 1), srun_add]
  have h2 : srun tm
      ({state := some stA, head := false,
        left := ones i *> blank∞,
        right := ones (2*m + 1 + 1) *> Side.cons false (ones (k + 1) *> blank∞)} : SConfig 6) 1
    = {state := some stB, head := true,
       left := ones (i + 1) *> blank∞,
       right := ones (2*m + 1) *> Side.cons false (ones (k + 1) *> blank∞)} := by
    simp [srun, sstep, tm]
  rw [h2, srun_add]
  have h3 : srun tm
      ({state := some stB, head := true,
        left := ones (i + 1) *> blank∞,
        right := ones (2*m + 1) *> Side.cons false (ones (k + 1) *> blank∞)} : SConfig 6) 1
    = {state := some stC, head := true,
       left := Side.cons false (ones (i + 1) *> blank∞),
       right := ones (2*m) *> Side.cons false (ones (k + 1) *> blank∞)} := by
    simp [srun, sstep, tm]
  rw [h3, CD_sweep m (Side.cons false (ones (i + 1) *> blank∞)) (ones (k + 1) *> blank∞)]
  unfold IntermOn; simp

/-- Iterated sub-cycle: `k` applications. -/
private lemma subcycle_iter (m i k : ℕ) :
    srun tm (IntermOn m i k) (k * (4*m + 7)) = IntermOn m (i + k) 0 := by
  induction k generalizing i with
  | zero => simp [IntermOn]
  | succ k' ih =>
    rw [show (k'+1) * (4*m + 7) = (4*m + 7) + k' * (4*m + 7) from by ring,
        srun_add, subcycle m i k', ih (i + 1),
        show i + 1 + k' = i + (k' + 1) from by ring]

/-- Closing sub-cycle for `k = 0`: like `subcycle` but ends with head=0
because the right block was already empty.  Same 4m+7 step count. -/
private lemma subcycle_close (m i : ℕ) :
    srun tm (IntermOn m i 0) (4*m + 7) = IntermOff m (i + 1) := by
  have hleft : (ones (2*m + 2) : List Sym) = true :: ones (2*m + 1) := rfl
  rw [show (4*m + 7 : ℕ) = 1 + ((2*m + 2) + (1 + (1 + (2*m + 2)))) from by ring,
      srun_add]
  have h1 : srun tm (IntermOn m i 0) 1
      = {state := some stA, head := true,
         left := ones (2*m + 1) *> Side.cons false (ones i *> blank∞),
         right := Side.cons false blank∞} := by
    unfold IntermOn; rw [hleft]; simp [srun, sstep, tm]
  rw [h1, srun_add, AL_sweep (2*m + 1), srun_add]
  have h2 : srun tm
      ({state := some stA, head := false,
        left := ones i *> blank∞,
        right := ones (2*m + 1 + 1) *> Side.cons false blank∞} : SConfig 6) 1
    = {state := some stB, head := true,
       left := ones (i + 1) *> blank∞,
       right := ones (2*m + 1) *> Side.cons false blank∞} := by
    simp [srun, sstep, tm]
  rw [h2, srun_add]
  have h3 : srun tm
      ({state := some stB, head := true,
        left := ones (i + 1) *> blank∞,
        right := ones (2*m + 1) *> Side.cons false blank∞} : SConfig 6) 1
    = {state := some stC, head := true,
       left := Side.cons false (ones (i + 1) *> blank∞),
       right := ones (2*m) *> Side.cons false blank∞} := by
    simp [srun, sstep, tm]
  rw [h3, CD_sweep m (Side.cons false (ones (i + 1) *> blank∞)) blank∞]
  unfold IntermOff; simp

/-- **Peel**: `IntermOff (m+1) i 0 → IntermOn m i 2` in 2 steps.
Steps: E,0→F (dir L, writes 1); F,1→E (dir L).  Two ones get moved from the
outer left block into the right-of-head region, effectively decrementing the
outer m by 1 and creating a fresh head=1 state. -/
private lemma peel (m i : ℕ) :
    srun tm (IntermOff (m + 1) i) 2 = IntermOn m i 2 := by
  unfold IntermOff IntermOn
  have : (ones (2*(m+1) + 2) : List Sym) = true :: true :: ones (2*m + 2) := rfl
  rw [this]; simp [srun, sstep, tm]

/-- **Base finalize**: for `m = 0`, `IntermOn 0 i 0 → A_on (i+3) 1` in 14 steps. -/
private lemma finalize_m0 (i : ℕ) :
    srun tm (IntermOn 0 i 0) 14 = A_on (i + 3) 1 := by
  unfold IntermOn A_on; simp [srun, sstep, tm]

/-- **Closing-phase R2** (induction on `m`): from `IntermOn m i 0`, run
`6m²+21m+14` steps to reach `A_on (3m+i+3) 1`.  Independent of the outer
right-block size.  Recursion: `cp_R2(m+1) = subcycle_close + peel +
subcycle_iter(k=2) + cp_R2(m)` with step count `4m+11 + 2 + 2(4m+7) +
(6m²+21m+14) = 6m²+33m+41 = 6(m+1)²+21(m+1)+14`. -/
private lemma cp_R2 : ∀ (m i : ℕ),
    srun tm (IntermOn m i 0) (6*m*m + 21*m + 14) = A_on (3*m + i + 3) 1 := by
  intro m
  induction m with
  | zero =>
    intro i
    rw [show (6*0*0 + 21*0 + 14 : ℕ) = 14 from by ring,
        show (3*0 + i + 3 : ℕ) = i + 3 from by ring]
    exact finalize_m0 i
  | succ m' ih =>
    intro i
    rw [show 6*(m'+1)*(m'+1) + 21*(m'+1) + 14
          = (4*m' + 11) + (2 + (2*(4*m' + 7) + (6*m'*m' + 21*m' + 14))) from by ring,
        srun_add,
        show (4*m' + 11 : ℕ) = 4*(m'+1) + 7 from by ring,
        subcycle_close (m'+1) i, srun_add,
        peel m' (i+1), srun_add,
        subcycle_iter m' (i+1) 2, ih (i+1+2)]
    congr 2; ring

/-- **Rule R2** (`dt = 6m² + 21m + 14 + 4mk + 7k`).
`A(2m+2, k+1) → A(3m+k+3, 2)`.  Left block of size `2m+2` gets consumed;
right block snaps back to the minimum size 2.

Step-count: the original wiki formula is `dt = 6m² + 17m + 7 + 4mn + 7n`
with `n = k + 1`; expanding gives `6m² + 21m + 14 + 4mk + 7k`.  Verified
for `m, k ∈ 0..7` exhaustively by `verify_dt.py`.

**Proof structure**: (`k` sub-cycles) + (closing phase).  Each sub-cycle
takes 4m+7 steps and pushes a `[false] *> ones 1` pattern into the
left "inner" block while consuming one right-block one.  The closing
phase (`cp_R2`) is independent of the initial right-block size; its cost
`6m²+21m+14` arises from a recursive peeling of the outer left block
(`cp_R2(m+1) = cp_R2(m) + 12m+27` overhead per level).

**Dispatches via**:
* `A_on (2m+2) k = IntermOn m 0 k` (bridge: `cons false blank = blank`).
* `subcycle_iter m 0 k` : `k` subcycles, cost `k*(4m+7)`.
* `cp_R2 m k` : closing phase, cost `6m²+21m+14`. -/
theorem rule_R2 (m k : ℕ) :
    srun tm (A_on (2*m + 2) k) (6*m*m + 21*m + 14 + 4*m*k + 7*k) =
      A_on (3*m + k + 3) 1 := by
  -- Bridge: A_on (2m+2) k = IntermOn m 0 k via cons_false_blank.
  have hbridge : A_on (2*m + 2) k = IntermOn m 0 k := by
    unfold A_on IntermOn; simp
  rw [hbridge,
      show 6*m*m + 21*m + 14 + 4*m*k + 7*k = k*(4*m + 7) + (6*m*m + 21*m + 14) from by ring,
      srun_add, subcycle_iter m 0 k,
      show (0 + k : ℕ) = k from by ring,
      cp_R2 m k]

-- ============================================================
-- Infrastructure for Rule R3
-- ============================================================

/-- Intermediate macro config for R3's recursion.  Outer ones block has
ODD length `2s+1` (vs R2's even `2m+2`).  The recursion descends on `s`
while growing `i` and `k`. -/
private def IntermOn_odd (s i k : ℕ) : SConfig 6 :=
  { state := some stE, head := true,
    left := ones (2*s + 1) *> Side.cons false (ones i *> blank∞),
    right := ones k *> blank∞ }

/-- **CD half-sweep**: companion to R2's `CD_sweep`.  Handles the case
where 2s+2 CD-alternations land on state C (rather than D), so the final
0-read is C,0 dir L (not D,0 dir R).  Takes `2s+3` steps.  Works for any
prefix `L` (proven by induction on `s` with a generalized statement). -/
private lemma CD_halfsweep (s : ℕ) (L R : Side) :
    srun tm
      ({state := some stC, head := true,
        left := L,
        right := ones (2*s + 1) *> Side.cons false R} : SConfig 6) (2*s + 3)
    = {state := some stE, head := true,
       left := ones (2*s + 1) *> L,
       right := Side.cons true R} := by
  induction s generalizing L with
  | zero => simp [srun, sstep, tm]
  | succ s' ih =>
    rw [show 2*(s'+1)+3 = 2 + (2*s'+3) from by ring, srun_add]
    have h : srun tm
        ({state := some stC, head := true,
          left := L,
          right := ones (2*(s'+1)+1) *> Side.cons false R} : SConfig 6) 2
        = {state := some stC, head := true,
           left := ones 2 *> L,
           right := ones (2*s'+1) *> Side.cons false R} := by
      rw [show (2*(s'+1)+1 : ℕ) = 2 + (2*s'+1) from by ring,
          show ones (2 + (2*s'+1)) = ones 2 ++ ones (2*s'+1) from (ones_append _ _).symm,
          Side.prepend_append]
      simp [srun, sstep, tm]
    rw [h, ih (ones 2 *> L)]
    congr 1
    rw [← Side.prepend_append, ones_append,
        show (2*s'+1 + 2 : ℕ) = 2*(s'+1) + 1 from by ring]

/-- **Descent lemma**: `IntermOn_odd (s+1) i k → IntermOn_odd s (i+1) (k+1)`
in `4s+9` steps.  Phase decomposition:
* E,1 (1 step)
* AL_sweep with j=2s+2 (2s+3 steps)
* A,0 (1 step)
* B,1 (1 step)
* CD_halfsweep s (2s+3 steps)

Total: 1 + (2s+3) + 1 + 1 + (2s+3) = 4s+9. -/
private lemma descent (s i k : ℕ) :
    srun tm (IntermOn_odd (s+1) i k) (4*s + 9) = IntermOn_odd s (i+1) (k+1) := by
  have hleft : (ones (2*(s+1) + 1) : List Sym) = true :: ones (2*s + 2) := by
    show ones ((2*s + 2) + 1) = true :: ones (2*s + 2)
    rfl
  rw [show (4*s + 9 : ℕ) = 1 + ((2*s + 3) + (1 + (1 + (2*s + 3)))) from by ring, srun_add]
  have h1 : srun tm (IntermOn_odd (s+1) i k) 1
      = {state := some stA, head := true,
         left := ones (2*s + 2) *> Side.cons false (ones i *> blank∞),
         right := Side.cons false (ones k *> blank∞)} := by
    unfold IntermOn_odd; rw [hleft]; simp [srun, sstep, tm]
  rw [h1, srun_add, AL_sweep (2*s + 2), srun_add]
  have h2 : srun tm
      ({state := some stA, head := false,
        left := ones i *> blank∞,
        right := ones (2*s + 2 + 1) *> Side.cons false (ones k *> blank∞)} : SConfig 6) 1
    = {state := some stB, head := true,
       left := ones (i + 1) *> blank∞,
       right := ones (2*s + 2) *> Side.cons false (ones k *> blank∞)} := by
    simp [srun, sstep, tm]
  rw [h2, srun_add]
  have h3 : srun tm
      ({state := some stB, head := true,
        left := ones (i + 1) *> blank∞,
        right := ones (2*s + 2) *> Side.cons false (ones k *> blank∞)} : SConfig 6) 1
    = {state := some stC, head := true,
       left := Side.cons false (ones (i + 1) *> blank∞),
       right := ones (2*s + 1) *> Side.cons false (ones k *> blank∞)} := by
    simp [srun, sstep, tm]
  rw [h3, CD_halfsweep s (Side.cons false (ones (i + 1) *> blank∞)) (ones k *> blank∞)]
  unfold IntermOn_odd; simp

/-- Iterated descent from source `m+1` down to `0`: `m+1` descents total.
Step count `Σ_{s=0}^{m} (4s + 9) = (m+1)(2m+9) = 2m² + 11m + 9`. -/
private lemma descent_from (m i k : ℕ) :
    srun tm (IntermOn_odd (m+1) i k) (2*m*m + 11*m + 9) =
      IntermOn_odd 0 (i + m + 1) (k + m + 1) := by
  induction m generalizing i k with
  | zero =>
    rw [show 2*0*0 + 11*0 + 9 = 4*0 + 9 from by ring]
    exact descent 0 i k
  | succ m' ih =>
    rw [show 2*(m'+1)*(m'+1) + 11*(m'+1) + 9
          = (4*(m'+1) + 9) + (2*m'*m' + 11*m' + 9) from by ring,
        srun_add, descent (m'+1) i k, ih (i+1) (k+1),
        show (i + 1 + m' + 1 : ℕ) = i + (m'+1) + 1 from by ring,
        show (k + 1 + m' + 1 : ℕ) = k + (m'+1) + 1 from by ring]

/-- **Base case** for R3: `IntermOn_odd 0 (i+1) k → A_on i (k+3)` in 7 steps.
Simp unfolds all 7 transitions over the concrete left pattern
`ones 1 *> [false] *> ones (i+1) *> blank∞`. -/
private lemma base_R3 (i k : ℕ) :
    srun tm (IntermOn_odd 0 (i + 1) k) 7 = A_on i (k + 3) := by
  unfold IntermOn_odd A_on
  simp [srun, sstep, tm]

/-- **Rule R3** (`dt = 2m² + 11m + 16`, independent of `k`).
`A(2m+3, k+1) → A(m, m+k+5)`.  Left block of size `2m+3` shrinks to `m`;
the right block gains `m + 4` ones.

Independence of `k` is notable — the step count does not scale with the
right-block size, only with the left-block size.  Verified for
`m, k ∈ 0..7` exhaustively by `verify_dt.py`.

**Proof structure**: `(m+1)` descents of variable length `4s+9`, then
a `7`-step base.  Each descent halves the "outer" ones count
(2s+3 → 2s+1) while incrementing the "inner" and right counts. -/
theorem rule_R3 (m k : ℕ) :
    srun tm (A_on (2*m + 3) k) (2*m*m + 11*m + 16) =
      A_on m (m + k + 4) := by
  have hbridge : A_on (2*m + 3) k = IntermOn_odd (m+1) 0 k := by
    unfold A_on IntermOn_odd
    simp only [show (2*(m+1) + 1 : ℕ) = 2*m + 3 from by ring]
    simp
  rw [hbridge,
      show 2*m*m + 11*m + 16 = (2*m*m + 11*m + 9) + 7 from by ring,
      srun_add, descent_from m 0 k,
      show (0 + m + 1 : ℕ) = m + 1 from by ring,
      base_R3 m (k + m + 1),
      show (k + m + 1 + 3 : ℕ) = m + k + 4 from by ring]

/-- **Rule R4** (`dt = 2`).  Degenerate n = 0 case:
`A(m+2, 0) → A(m, 3)`.  Two steps `E,0 → 1LF; F,1 → 1LE` convert the
right-blank into a length-3 ones block and re-establish state E with a
1-head, effectively moving the head two cells left into the left block. -/
theorem rule_R4 (m : ℕ) :
    srun tm (A_off (m + 2)) 2 = A_on m 2 := by
  simp [A_off, A_on, srun, sstep, tm]

-- ============================================================
-- Halt cases
-- ============================================================

/-- `A(0, 0)` halts.  Empty tape (state E on blank with blank to left):
  E,0→F (dir L, writes 1 to right)
  F,0→HALT
-/
theorem halt_A_off_0 :
    (srun tm (A_off 0) 2).state = none := by
  simp [A_off, srun, sstep, tm]

/-- `A(1, 0)` halts.  Single 1 on left, state E on blank:
  E,0→F; F,1→E; E,0→F; F,0→HALT -/
theorem halt_A_off_1 :
    (srun tm (A_off 1) 4).state = none := by
  simp [A_off, srun, sstep, tm]

/-- `A(1, n+1)` halts in 9 steps for every `n ≥ 0`.  The right block is
consumed regardless of its size (the TM halts before re-reading the
rightmost 1s), so the step count is independent of `n`. -/
theorem halt_A_on_1 (n : ℕ) :
    (srun tm (A_on 1 n) 9).state = none := by
  simp [A_on, srun, sstep, tm]

-- ============================================================
-- Initial configuration
-- ============================================================

/- From the blank tape, in 4 steps we reach `A_off 2` (= Yuan's `A(2, 0)`):
  A,0→B; B,0→C; C,1→D; D,0→E
leaves the tape `1 1 [E] 0` with all else blank. -/

/-- Config-form initial run target (matches `A_off 2` under `.toSConfig`). -/
private def Init_Config_A_off_2 : Config 6 :=
  { state := some stE,
    head := false,
    left := ones 2,
    right := [] }

private lemma init_to_Init_Config_A_off_2 :
    run tm (initConfig 6) 4 = Init_Config_A_off_2 := by
  decide

private lemma Init_Config_A_off_2_toSConfig :
    Init_Config_A_off_2.toSConfig = A_off 2 := by
  simp [Init_Config_A_off_2, A_off, Config.toSConfig]

theorem init_to_A_off_2 :
    srun tm (sinitConfig 6) 4 = A_off 2 := by
  have h := congrArg Config.toSConfig init_to_Init_Config_A_off_2
  rw [toSConfig_run, toSConfig_initConfig, Init_Config_A_off_2_toSConfig] at h
  exact h

-- ============================================================
-- Halting equivalence theorem
-- ============================================================

/-- Mathematical state representing Yuan's `A(m, n) = 1^m E> 1^n`. -/
structure MathState where
  m : ℕ
  n : ℕ
deriving Repr, DecidableEq, Inhabited

/-- Embed a `MathState` as an SConfig: `A(m, 0) = A_off m`, `A(m, n+1) = A_on m n`. -/
def MathState.toSConfig : MathState → SConfig 6
  | ⟨m, 0⟩   => A_off m
  | ⟨m, n+1⟩ => A_on m n

/-- One-step math transition.  `none` marks the three halt configurations
`(0, 0)`, `(1, 0)`, `(1, n+1)`; other states dispatch to R1/R2/R3/R4 based
on parity of the left block. -/
def nextMathState : MathState → Option MathState
  | ⟨0, 0⟩     => none                                   -- (0, 0) halts (R/halt_A_off_0)
  | ⟨0, n+1⟩   => some ⟨2, n⟩                            -- R1: (0, n+1) → (2, n)
  | ⟨1, 0⟩     => none                                   -- (1, 0) halts (halt_A_off_1)
  | ⟨1, _+1⟩   => none                                   -- (1, n+1) halts (halt_A_on_1)
  | ⟨m+2, 0⟩   => some ⟨m, 3⟩                            -- R4: (m+2, 0) → (m, 3)
  | ⟨m+2, n+1⟩ =>
    if m % 2 = 0 then some ⟨3*(m/2) + n + 3, 2⟩         -- R2: (2m'+2, n+1) → (3m'+n+3, 2)
    else some ⟨m/2, m/2 + n + 5⟩                        -- R3: (2m'+3, n+1) → (m', m'+n+5)

/-- Inductive halting: either a direct halt or a halt of a successor state. -/
inductive mathHalts : MathState → Prop where
  | haltStep (s : MathState) (h : nextMathState s = none) : mathHalts s
  | nextStep (s s' : MathState) (h : nextMathState s = some s')
      (h' : mathHalts s') : mathHalts s

/-- Simulation of halting: any halt-state math config corresponds to a TM halt. -/
theorem tm_sim_halt : ∀ (s : MathState),
    nextMathState s = none → ∃ k, k > 0 ∧ (srun tm s.toSConfig k).state = none := by
  rintro ⟨m, n⟩ h
  match m, n with
  | 0, 0 => exact ⟨2, by omega, halt_A_off_0⟩
  | 1, 0 => exact ⟨4, by omega, halt_A_off_1⟩
  | 1, n'+1 => exact ⟨9, by omega, halt_A_on_1 n'⟩
  | 0, n'+1 => simp [nextMathState] at h
  | m'+2, 0 => simp [nextMathState] at h
  | m'+2, n'+1 =>
    simp only [nextMathState] at h
    split_ifs at h

/-- Simulation of a non-halting step: reaches the successor's SConfig. -/
theorem tm_sim_step : ∀ (s s' : MathState),
    nextMathState s = some s' → ∃ k, k > 0 ∧ srun tm s.toSConfig k = s'.toSConfig := by
  rintro ⟨m, n⟩ s' h
  match m, n with
  | 0, 0 => simp [nextMathState] at h
  | 0, n'+1 =>
    simp only [nextMathState, Option.some.injEq] at h; subst h
    refine ⟨5, by omega, ?_⟩
    show srun tm (A_on 0 n') 5 = (⟨2, n'⟩ : MathState).toSConfig
    match n' with
    | 0 => exact rule_R1b
    | n''+1 => exact rule_R1a n''
  | 1, 0 => simp [nextMathState] at h
  | 1, n'+1 => simp [nextMathState] at h
  | m'+2, 0 =>
    simp only [nextMathState, Option.some.injEq] at h; subst h
    refine ⟨2, by omega, ?_⟩
    show srun tm (A_off (m'+2)) 2 = A_on m' 2
    exact rule_R4 m'
  | m'+2, n'+1 =>
    simp only [nextMathState] at h
    by_cases hp : m' % 2 = 0
    · rw [if_pos hp] at h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨m'', rfl⟩ : ∃ m'', m' = 2*m'' := ⟨m'/2, by omega⟩
      refine ⟨6*m''*m'' + 21*m'' + 14 + 4*m''*n' + 7*n', by omega, ?_⟩
      show srun tm (A_on (2*m''+2) n') _ = (⟨3*((2*m'')/2) + n' + 3, 2⟩ : MathState).toSConfig
      rw [show ((2*m'')/2 : ℕ) = m'' from by omega]
      show srun tm (A_on (2*m''+2) n') _ = A_on (3*m'' + n' + 3) 1
      exact rule_R2 m'' n'
    · rw [if_neg hp] at h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨m'', rfl⟩ : ∃ m'', m' = 2*m'' + 1 := ⟨m'/2, by omega⟩
      refine ⟨2*m''*m'' + 11*m'' + 16, by omega, ?_⟩
      show srun tm (A_on (2*m''+1+2) n') _
         = (⟨(2*m''+1)/2, (2*m''+1)/2 + n' + 5⟩ : MathState).toSConfig
      rw [show ((2*m''+1)/2 : ℕ) = m'' from by omega,
          show (2*m''+1+2 : ℕ) = 2*m''+3 from by ring]
      show srun tm (A_on (2*m''+3) n') _ = A_on m'' (m'' + n' + 4)
      exact rule_R3 m'' n'

/-- SConfig-level halting equivalence: the TM halts starting from any
MathState's toSConfig iff the math model halts from that state.

Forward direction uses strong induction on TM step count, invoking the
simulation theorem to identify the next math state.  Backward direction
inducts on `mathHalts`. -/
theorem stm_halts_iff_mathHalts (s : MathState) :
    (∃ k, (srun tm s.toSConfig k).state = none) ↔ mathHalts s := by
  constructor
  · -- Forward: TM halts → mathHalts (strong induction on step count).
    intro ⟨k, hk⟩
    suffices ∀ (n : ℕ) (s : MathState), (srun tm s.toSConfig n).state = none →
        mathHalts s from this k s hk
    intro n; induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro s hk
      cases h_next : nextMathState s with
      | none => exact mathHalts.haltStep s h_next
      | some s' =>
        have ⟨k_sim, hk_pos, h_sim⟩ := tm_sim_step s s' h_next
        by_cases h_lt : n < k_sim
        · exfalso
          have h_still : (srun tm s.toSConfig k_sim).state = none := by
            rw [show k_sim = n + (k_sim - n) from by omega, srun_add,
                srun_halted _ _ hk]
            exact hk
          rw [h_sim] at h_still
          have h_ne : s'.toSConfig.state ≠ none := by
            rcases s' with ⟨m', n'⟩
            cases n' <;> simp [MathState.toSConfig, A_on, A_off]
          exact h_ne h_still
        · rw [show n = k_sim + (n - k_sim) from by omega, srun_add, h_sim] at hk
          exact mathHalts.nextStep s s' h_next (ih (n - k_sim) (by omega) s' hk)
  · -- Backward: mathHalts → TM halts (induction on mathHalts).
    intro hmh
    induction hmh with
    | haltStep s h =>
      have ⟨k, _, h_sim⟩ := tm_sim_halt s h
      exact ⟨k, h_sim⟩
    | nextStep s s' h_some _ ih =>
      have ⟨k, _, h_sim⟩ := tm_sim_step s s' h_some
      obtain ⟨k', hk'⟩ := ih
      refine ⟨k + k', ?_⟩
      rw [srun_add, h_sim]; exact hk'

/-- **Main halting equivalence theorem**: the TM halts starting from the
blank tape iff the math model halts starting from `A(2, 0)`.

Combines `init_to_A_off_2` (blank tape reaches `A_off 2 = ⟨2, 0⟩.toSConfig`
in 4 steps) with `stm_halts_iff_mathHalts`. -/
theorem tm_halts_iff :
    (∃ k, (run tm (initConfig 6) k).state = none) ↔ mathHalts ⟨2, 0⟩ := by
  rw [← stm_halts_iff_mathHalts]
  -- (⟨2, 0⟩ : MathState).toSConfig = A_off 2 by rfl
  have h_toSConfig : (⟨2, 0⟩ : MathState).toSConfig = A_off 2 := rfl
  rw [h_toSConfig]
  -- Now: (∃ k, (run tm (initConfig 6) k).state = none) ↔ ∃ k, (srun tm (A_off 2) k).state = none.
  have h_eq : ∀ k, (run tm (initConfig 6) k).state =
                    (srun tm (sinitConfig 6) k).state := fun k => by
    change _ = (srun tm (initConfig 6).toSConfig k).state
    rw [← toSConfig_run]; rfl
  constructor
  · rintro ⟨k, hk⟩
    by_cases hge : 4 ≤ k
    · refine ⟨k - 4, ?_⟩
      rw [h_eq, show k = 4 + (k - 4) from by omega, srun_add, init_to_A_off_2] at hk
      exact hk
    · -- k < 4: TM hasn't reached halt yet at this point.
      exfalso
      have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> revert hk <;> decide
  · rintro ⟨k, hk⟩
    refine ⟨4 + k, ?_⟩
    rw [h_eq, srun_add, init_to_A_off_2]
    exact hk

-- ============================================================
-- Hipparcos reformulation: single-argument iteration
-- ============================================================

/-!
## Hipparcos reformulation

Daniel Yuan observed that in the A-level dynamics (single-parameter form
`A(b) := (b, 2)` in converted coordinates), the main rule is
`A((2a+1)·2^k) → A((2a+1)·2^k + k + a)` for `a ≥ 2`.  Hipparcos
simplified this to: define `f(b) := b + k + a` where `b = (2a+1)·2^k`
(a, k ≥ 0 uniquely determined).  Then the BB(6) halting question
reduces to:

> **Does there exist `n : ℕ` such that `f^n(5)` is a power of 2
>   or 3 times a power of 2?**

The TM's initial config reaches `A(5)` in the converted notation, which
is our `⟨2, 2⟩` in original-coordinate MathState (reached after 2
nextMathState steps from `⟨2, 0⟩`).  Hipparcos's `f` matches Yuan's
A-level rule **exactly for `a ≥ 2`**; at `a = 1` (b = 3·2^k) the TM
follows `A(b) → A(b + 3 + k)` (different from Hipparcos's `b + k + 1`),
and at `a = 0` (b = 2^k) the TM halts.  Hence the orbit of Hipparcos's
`f` matches the TM's A-level orbit only while `a ≥ 2`.
-/

/-- Number of times 2 divides `b` (2-adic valuation), via `Nat.factorization`. -/
noncomputable def ord2 (b : ℕ) : ℕ := b.factorization 2

/-- The A-level TM step function.  Given `b = (2a+1) · 2^k`:

* `a = 0` (`b = 2^k`): the TM halts at `A(b)` — returns `none`.
* `a = 1` (`b = 3·2^k`): Yuan's rule gives `A(b) → A(b + k + 3)`.
* `a ≥ 2`: Hipparcos's rule gives `A(b) → A(b + k + a)`.

**Note on Hipparcos's simplification**: the formula `f(b) = b + k + a`
(in the original wiki question) is **Hipparcos's** simplification that
coincides with the actual TM dynamics *only for `a ≥ 2`*.  At `a = 1`
(i.e., `b = 3·2^k`) Yuan's actual TM rule gives `b + k + 3` whereas
Hipparcos's formula gives `b + k + 1`.  Hipparcos conjectured the orbit
never reaches `a = 1`, making the formulas agree in practice — but the
conjecture is part of the open BB(6) problem.

To obtain a genuine iff with TM halting, we use the *true* A-level step
`fA` rather than Hipparcos's simplification. -/
noncomputable def fA (b : ℕ) : Option ℕ :=
  if b = 0 then none
  else
    let k := ord2 b
    let odd := b / 2^k
    let a := (odd - 1) / 2
    if a = 0 then none                       -- halt: b = 2^k
    else if a = 1 then some (b + k + 3)      -- Yuan's rule: b = 3·2^k
    else some (b + k + a)                    -- Hipparcos's rule: a ≥ 2

/-- Iterate `fA` propagating `none` on halt. -/
noncomputable def fAIter : ℕ → Option ℕ → Option ℕ
  | 0, s => s
  | n+1, s => (fAIter n s).bind fA

/-- Iterate nextMathState n times, propagating `none` on halt. -/
def mathIter : ℕ → Option MathState → Option MathState
  | 0, s => s
  | n+1, s => (mathIter n s).bind nextMathState

private lemma mathIter_succ (n : ℕ) (s : MathState) :
    mathIter (n + 1) (some s) = mathIter n (nextMathState s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n' ih => rw [mathIter, ih, mathIter]

/-- `mathHalts s` is equivalent to some `mathIter` returning `none`. -/
theorem mathHalts_iff_mathIter (s : MathState) :
    mathHalts s ↔ ∃ n, mathIter n (some s) = none := by
  constructor
  · intro h
    induction h with
    | haltStep s hs => exact ⟨1, by rw [mathIter_succ]; simp [mathIter, hs]⟩
    | nextStep s s' hss' _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, by rw [mathIter_succ, hss']; exact hn⟩
  · rintro ⟨n, hn⟩
    induction n generalizing s with
    | zero => simp [mathIter] at hn
    | succ n' ih =>
      rw [mathIter_succ] at hn
      cases hs : nextMathState s with
      | none => exact mathHalts.haltStep s hs
      | some s' =>
        rw [hs] at hn
        exact mathHalts.nextStep s s' hs (ih s' hn)

/-- Directly-provable companion iff via `nextMathState` iteration:
the TM halts iff some iterate of `nextMathState` from `⟨2, 0⟩` is `none`.
Unlike `tm_halts_iff_exists` (Hipparcos reformulation), this iff doesn't
depend on any open conjectures. -/
theorem tm_halts_iff_mathIter :
    (∃ k, (run tm (initConfig 6) k).state = none) ↔
    ∃ n, mathIter n (some ⟨2, 0⟩) = none := by
  rw [tm_halts_iff]; exact mathHalts_iff_mathIter _

/-- Inductive halting predicate for `fA`: either `fA b = none` directly,
or `fA b = some b'` and `b'` halts. -/
inductive fAHalts : ℕ → Prop where
  | haltStep (b : ℕ) (h : fA b = none) : fAHalts b
  | nextStep (b b' : ℕ) (h : fA b = some b') (h' : fAHalts b') : fAHalts b

private lemma fAIter_succ (n : ℕ) (b : ℕ) :
    fAIter (n + 1) (some b) = fAIter n (fA b) := by
  induction n generalizing b with
  | zero => rfl
  | succ n' ih => rw [fAIter, ih, fAIter]

/-- Analogue of `mathHalts_iff_mathIter` for `fA`. -/
theorem fAHalts_iff_fAIter (b : ℕ) :
    fAHalts b ↔ ∃ n, fAIter n (some b) = none := by
  constructor
  · intro h
    induction h with
    | haltStep b hb => exact ⟨1, by rw [fAIter_succ]; simp [fAIter, hb]⟩
    | nextStep b b' hb _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, by rw [fAIter_succ, hb]; exact hn⟩
  · rintro ⟨n, hn⟩
    induction n generalizing b with
    | zero => simp [fAIter] at hn
    | succ n' ih =>
      rw [fAIter_succ] at hn
      cases hb : fA b with
      | none => exact fAHalts.haltStep b hb
      | some b' =>
        rw [hb] at hn
        exact fAHalts.nextStep b b' hb (ih b' hn)

-- ============================================================
-- Helper lemmas for the correspondence between fA and nextMathState
-- ============================================================

/-- Single R3 step: `⟨2q+3, n'+1⟩ → ⟨q, q+n'+5⟩`. -/
private lemma nextMathState_R3_form (q n' : ℕ) :
    nextMathState ⟨2*q + 3, n' + 1⟩ = some ⟨q, q + n' + 5⟩ := by
  show nextMathState ⟨(2*q + 1) + 2, n' + 1⟩ = some ⟨q, q + n' + 5⟩
  simp only [nextMathState]
  rw [if_neg (by omega : ¬((2*q + 1) % 2 = 0))]
  congr 2
  · omega
  · omega

/-- R3 step on `⟨(2a+1)·2^{k+1} - 3, n'+1⟩`: reduces the exponent by 1. -/
private lemma R3_step_pow2 (a k n' : ℕ) (ha : a ≥ 1) :
    nextMathState ⟨(2*a + 1) * 2^(k+1) - 3, n' + 1⟩ =
      some ⟨(2*a + 1) * 2^k - 3, (2*a + 1) * 2^k + n' + 2⟩ := by
  have h1 : (2*a + 1) ≥ 3 := by omega
  have hpow : 2^k ≥ 1 := Nat.one_le_two_pow
  have h2 : (2*a + 1) * 2^k ≥ 3 := by
    have := Nat.mul_le_mul h1 hpow
    omega
  have hfact : (2*a + 1) * 2^(k+1) - 3 = 2 * ((2*a + 1) * 2^k - 3) + 3 := by
    have : (2*a + 1) * 2^(k+1) = 2 * ((2*a + 1) * 2^k) := by ring
    omega
  rw [hfact, nextMathState_R3_form]
  congr 2
  omega

/-- Iterated R3 steps (a ≥ 1): `k` applications take `⟨(2a+1)·2^k - 3, n'+1⟩`
to `⟨2a-2, (2a+1)·(2^k - 1) + k + n' + 1⟩`. -/
private lemma R3_chain_pow2 (a : ℕ) (ha : a ≥ 1) :
    ∀ (k n' : ℕ),
      mathIter k (some ⟨(2*a + 1) * 2^k - 3, n' + 1⟩) =
        some ⟨(2*a + 1) - 3, (2*a + 1) * (2^k - 1) + k + n' + 1⟩ := by
  intro k
  induction k with
  | zero =>
    intro n'
    show mathIter 0 _ = _
    rw [show mathIter 0 (some ⟨(2*a+1) * 2^0 - 3, n'+1⟩) = some ⟨(2*a+1) * 2^0 - 3, n'+1⟩ from rfl]
    rw [show (2^0 : ℕ) = 1 from rfl]
    congr 2
    · show (2*a+1) * 1 - 3 = 2*a+1 - 3
      rw [Nat.mul_one]
    · show n' + 1 = (2*a+1) * (1 - 1) + 0 + n' + 1
      omega
  | succ k' ih =>
    intro n'
    rw [mathIter_succ, R3_step_pow2 a k' n' ha]
    have hie := ih ((2*a + 1) * 2^k' + n' + 1)
    rw [show (2*a + 1) * 2^k' + n' + 2 = ((2*a + 1) * 2^k' + n' + 1) + 1 from rfl] at hie
    rw [hie]
    congr 2
    have hpow : 2^k' ≥ 1 := Nat.one_le_two_pow
    -- Goal: (2a+1)*(2^k' - 1) + k' + ((2a+1)*2^k' + n' + 1) + 1 = (2a+1)*(2^(k'+1) - 1) + (k'+1) + n' + 1
    have hX : (2*a+1) * (2^k' - 1) = (2*a+1) * 2^k' - (2*a+1) := by
      have hk : 2^k' = (2^k' - 1) + 1 := by omega
      have : (2*a+1) * 2^k' = (2*a+1) * (2^k' - 1) + (2*a+1) := by
        calc (2*a+1) * 2^k'
            = (2*a+1) * ((2^k' - 1) + 1) := by rw [← hk]
          _ = (2*a+1) * (2^k' - 1) + (2*a+1) * 1 := Nat.mul_add _ _ _
          _ = (2*a+1) * (2^k' - 1) + (2*a+1) := by rw [Nat.mul_one]
      omega
    have hY : (2*a+1) * (2^(k'+1) - 1) = 2 * (2*a+1) * 2^k' - (2*a+1) := by
      have h2 : (2^(k'+1) : ℕ) = 2 * 2^k' := by ring
      rw [h2]
      have hk : 2 * 2^k' = (2 * 2^k' - 1) + 1 := by omega
      have : (2*a+1) * (2 * 2^k') = (2*a+1) * (2 * 2^k' - 1) + (2*a+1) := by
        calc (2*a+1) * (2 * 2^k')
            = (2*a+1) * ((2 * 2^k' - 1) + 1) := by rw [← hk]
          _ = (2*a+1) * (2 * 2^k' - 1) + (2*a+1) * 1 := Nat.mul_add _ _ _
          _ = (2*a+1) * (2 * 2^k' - 1) + (2*a+1) := by rw [Nat.mul_one]
      have h22 : (2*a+1) * (2 * 2^k') = 2 * (2*a+1) * 2^k' := by ring
      omega
    rw [hX, hY]
    have h3 : (2*a+1) ≤ (2*a+1) * 2^k' := Nat.le_mul_of_pos_right (2*a+1) hpow
    have h4 : (2*a+1) ≤ 2 * (2*a+1) * 2^k' := by
      have heq : 2 * (2*a+1) * 2^k' = (2*a+1) * (2 * 2^k') := by ring
      rw [heq]
      exact Nat.le_mul_of_pos_right (2*a+1) (by have := hpow; omega)
    have h5 : 2 * (2*a+1) * 2^k' = (2*a+1) * 2^k' + (2*a+1) * 2^k' := by ring
    rw [h5]
    omega

/-- Base halt: `⟨1, n+1⟩` halts directly. -/
private lemma halt_at_1 (n' : ℕ) : mathHalts ⟨1, n' + 1⟩ :=
  mathHalts.haltStep _ rfl

/-- The a = 0 case: `⟨2^k - 3, n+1⟩` halts for `k ≥ 2`. -/
private lemma halt_case_pow2 :
    ∀ (k : ℕ), k ≥ 2 → ∀ (n' : ℕ), mathHalts ⟨2^k - 3, n' + 1⟩ := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro n'
    show mathHalts ⟨2^2 - 3, n' + 1⟩
    have : (2^2 - 3 : ℕ) = 1 := by norm_num
    rw [this]
    exact halt_at_1 n'
  | succ k hk ih =>
    intro n'
    -- 2^(k+1) - 3 = 2*(2^k - 3) + 3 where 2^k ≥ 4 ≥ 3.
    have hpow : 2^k ≥ 4 := by
      calc 2^k ≥ 2^2 := Nat.pow_le_pow_right (by omega) hk
        _ = 4 := by norm_num
    have hfact : (2^(k+1) - 3 : ℕ) = 2 * (2^k - 3) + 3 := by
      have : (2:ℕ)^(k+1) = 2 * 2^k := by ring
      omega
    rw [hfact]
    refine mathHalts.nextStep _ ⟨2^k - 3, (2^k - 3) + n' + 5⟩ ?_ ?_
    · exact nextMathState_R3_form (2^k - 3) n'
    · have : (2^k - 3) + n' + 5 = ((2^k - 3) + n' + 4) + 1 := by omega
      rw [this]
      exact ih ((2^k - 3) + n' + 4)

/-- The a ≥ 2 case: `⟨(2a+1)·2^k - 3, 2⟩` reaches `⟨(2a+1)·2^k + k + a - 3, 2⟩`
in `k+1` nextMathState steps. -/
private lemma fA_sim_a_ge_2 (a k : ℕ) (ha : a ≥ 2) :
    mathIter (k + 1) (some ⟨(2*a + 1) * 2^k - 3, 2⟩) =
      some ⟨(2*a + 1) * 2^k + k + a - 3, 2⟩ := by
  show (mathIter k (some ⟨(2*a+1)*2^k - 3, 2⟩)).bind nextMathState = _
  have hR3 := R3_chain_pow2 a (by omega : a ≥ 1) k 1
  simp only [show (1 + 1 : ℕ) = 2 from rfl] at hR3
  rw [hR3]
  show (some ⟨(2*a+1) - 3, (2*a+1)*(2^k - 1) + k + 1 + 1⟩).bind nextMathState = _
  simp only [Option.bind]
  have ha1 : (2*a + 1 : ℕ) - 3 = 2*a - 2 := by omega
  rw [ha1]
  have h2am2 : (2*a : ℕ) - 2 = 2*(a-2) + 2 := by omega
  rw [h2am2]
  obtain ⟨N', hN'⟩ : ∃ N', (2*a+1)*(2^k - 1) + k + 1 + 1 = N' + 1 :=
    ⟨(2*a+1)*(2^k - 1) + k + 1, rfl⟩
  rw [hN']
  show nextMathState ⟨2*(a-2) + 2, N' + 1⟩ = _
  simp only [nextMathState]
  rw [show (2*(a-2) : ℕ) % 2 = 0 from by omega]
  simp only [if_true]
  congr 2
  have hpow : (2^k : ℕ) ≥ 1 := Nat.one_le_two_pow
  have h2div : 3 * (2*(a-2) / 2) = 3 * (a-2) := by congr 1; omega
  rw [h2div]
  have hexp : (2*a+1) * (2^k - 1) = (2*a+1) * 2^k - (2*a+1) := by
    have hk : 2^k = (2^k - 1) + 1 := by omega
    have hE : (2*a+1) * 2^k = (2*a+1) * (2^k - 1) + (2*a+1) := by
      calc (2*a+1) * 2^k
          = (2*a+1) * ((2^k - 1) + 1) := by rw [← hk]
        _ = (2*a+1) * (2^k - 1) + (2*a+1) * 1 := Nat.mul_add _ _ _
        _ = (2*a+1) * (2^k - 1) + (2*a+1) := by rw [Nat.mul_one]
    omega
  have hN'' : N' = (2*a+1)*(2^k - 1) + k + 1 := by omega
  rw [hN'', hexp]
  have hX : (2*a+1) ≤ (2*a+1) * 2^k :=
    Nat.le_mul_of_pos_right (2*a+1) hpow
  omega

/-- The a = 1 case: `⟨3·2^k - 3, 2⟩` reaches `⟨3·2^k + k, 2⟩`
in `k+2` nextMathState steps.  (`fA(3·2^k) = 3·2^k + k + 3`, so the
target is `fA b - 3 = 3·2^k + k`.) -/
private lemma fA_sim_a_eq_1 (k : ℕ) :
    mathIter (k + 2) (some ⟨3 * 2^k - 3, 2⟩) =
      some ⟨3 * 2^k + k, 2⟩ := by
  have hpow : (2:ℕ)^k ≥ 1 := Nat.one_le_two_pow
  -- k+2 = k+1+1
  show ((mathIter k (some ⟨3 * 2^k - 3, 2⟩)).bind nextMathState).bind nextMathState = _
  have hchain := R3_chain_pow2 1 (by omega : 1 ≥ 1) k 1
  -- Simplify hchain to express in terms of 3 and 2.
  have hchain' : mathIter k (some ⟨3 * 2^k - 3, 2⟩) =
      some ⟨0, 3 * (2^k - 1) + k + 2⟩ := by
    have h1 : (2*1 + 1 : ℕ) = 3 := rfl
    have h2 : (1 + 1 : ℕ) = 2 := rfl
    have h3 : ((2*1 + 1 : ℕ) * 2^k - 3) = 3 * 2^k - 3 := by rw [h1]
    have h4 : ((2*1 + 1 : ℕ) * (2^k - 1) + k + 1 + 1) = 3 * (2^k - 1) + k + 2 := rfl
    have h5 : ((2*1 + 1 : ℕ) - 3) = 0 := rfl
    rw [h3, h2, h5, h4] at hchain
    exact hchain
  rw [hchain']
  -- Now: (some ⟨0, 3*(2^k-1) + k + 2⟩).bind nextMathState |>.bind nextMathState = some ⟨3*2^k+k, 2⟩
  show (nextMathState ⟨0, 3*(2^k-1) + k + 2⟩).bind nextMathState = _
  have hN : 3*(2^k-1) + k + 2 ≥ 1 := by omega
  obtain ⟨N', hN'⟩ : ∃ N', 3*(2^k-1) + k + 2 = N' + 1 :=
    ⟨3*(2^k-1) + k + 1, by omega⟩
  rw [hN']
  -- nextMathState ⟨0, N'+1⟩ = some ⟨2, N'⟩ (R1 rule)
  rw [show nextMathState ⟨0, N'+1⟩ = some ⟨2, N'⟩ from rfl]
  show nextMathState ⟨2, N'⟩ = _
  -- N' ≥ 1 since hN'.
  have hN'ge : N' ≥ 1 := by omega
  obtain ⟨N'', hN''⟩ : ∃ N'', N' = N'' + 1 := ⟨N' - 1, by omega⟩
  rw [hN'']
  show nextMathState ⟨0 + 2, N'' + 1⟩ = _
  have hR2 : nextMathState ⟨0 + 2, N'' + 1⟩ = some ⟨3*(0/2) + N'' + 3, 2⟩ := rfl
  rw [hR2]
  congr 2
  show 3 * (0/2) + N'' + 3 = 3 * 2^k + k
  have hN''eq : N'' = 3*(2^k-1) + k := by omega
  rw [hN''eq]
  -- Goal: 3*(2^k-1) + k + 3 = 3*2^k + k
  have hexp : 3 * (2^k - 1) + 3 = 3 * 2^k := by
    have hk : 2^k = (2^k - 1) + 1 := by omega
    calc 3 * (2^k - 1) + 3
        = 3 * (2^k - 1) + 3 * 1 := by rw [Nat.mul_one]
      _ = 3 * ((2^k - 1) + 1) := (Nat.mul_add _ _ _).symm
      _ = 3 * 2^k := by rw [← hk]
  omega

/-- The a = 0 case: `⟨2^k - 3, 2⟩` halts for `k ≥ 2`. -/
private lemma fA_sim_a_eq_0 (k : ℕ) (hk : k ≥ 2) :
    mathHalts ⟨2^k - 3, 2⟩ := by
  exact halt_case_pow2 k hk 1

/-- `none` propagates through `mathIter`. -/
private lemma mathIter_none (n : ℕ) : mathIter n none = none := by
  induction n with
  | zero => rfl
  | succ n' ih => rw [mathIter]; rw [ih]; rfl

/-- `mathIter` respects addition of step counts. -/
private lemma mathIter_add (m n : ℕ) (s : Option MathState) :
    mathIter (m + n) s = mathIter n (mathIter m s) := by
  induction m generalizing s with
  | zero => simp [mathIter]
  | succ m' ih =>
    cases s with
    | none =>
      rw [mathIter_none, mathIter_none, mathIter_none]
    | some s' =>
      rw [show (m' + 1 + n = (m' + n) + 1) from by ring, mathIter_succ, ih, mathIter_succ]

/-- If `b = 2^k` and `b ≥ 3`, then `k ≥ 2`. -/
private lemma pow2_ge_three (k : ℕ) (h : (2:ℕ)^k ≥ 3) : k ≥ 2 := by
  match k with
  | 0 => simp at h
  | 1 => omega
  | k' + 2 => omega

/-- `2^(ord2 b)` divides `b`.  Follows from `Nat.ordProj_dvd`. -/
private lemma ord2_dvd (b : ℕ) : 2^(ord2 b) ∣ b := Nat.ordProj_dvd b 2

/-- For `b ≥ 1`, `b / 2^(ord2 b)` is odd.  Follows from `Nat.not_dvd_ordCompl`. -/
private lemma ord2_div_odd (b : ℕ) (hb : 1 ≤ b) : b / 2^(ord2 b) % 2 = 1 := by
  have hne : b ≠ 0 := by omega
  have h : ¬ (2 : ℕ) ∣ (b / 2^(ord2 b)) :=
    Nat.not_dvd_ordCompl (p := 2) Nat.prime_two hne
  have : (b / 2^(ord2 b)) % 2 ≠ 0 := fun hc => h (Nat.dvd_of_mod_eq_zero hc)
  omega

/-- For `b ≥ 1`, `b = (2a + 1) * 2^(ord2 b)` where `a = (b / 2^(ord2 b) - 1) / 2`. -/
private lemma ord2_factor (b : ℕ) (hb : 1 ≤ b) :
    b = (2 * ((b / 2^(ord2 b) - 1) / 2) + 1) * 2^(ord2 b) := by
  have hodd := ord2_div_odd b hb
  have hdvd := ord2_dvd b
  have h1 : b / 2^(ord2 b) = 2 * ((b / 2^(ord2 b) - 1) / 2) + 1 := by
    have := Nat.div_add_mod (b / 2^(ord2 b)) 2
    omega
  calc b = b / 2^(ord2 b) * 2^(ord2 b) := (Nat.div_mul_cancel hdvd).symm
    _ = (2 * ((b / 2^(ord2 b) - 1) / 2) + 1) * 2^(ord2 b) := by rw [← h1]

/-- Combining a reach lemma with mathHalts of target gives mathHalts of source. -/
private lemma mathHalts_of_reaches (s s' : MathState) (m : ℕ)
    (hreach : mathIter m (some s) = some s') (hhalt : mathHalts s') : mathHalts s := by
  rw [mathHalts_iff_mathIter]
  rw [mathHalts_iff_mathIter] at hhalt
  obtain ⟨n, hn⟩ := hhalt
  exact ⟨m + n, by rw [mathIter_add, hreach]; exact hn⟩

/-- `fA b = none` and `b ≥ 3` implies `b = 2^k` with `k ≥ 2`. -/
private lemma fA_none_pow2 (b : ℕ) (hb : b ≥ 3) (hfa : fA b = none) :
    ∃ k ≥ 2, b = 2^k := by
  have hb0 : b ≠ 0 := by omega
  have hb1 : 1 ≤ b := by omega
  simp only [fA] at hfa
  rw [if_neg hb0] at hfa
  split_ifs at hfa with ha0 _ha1
  · -- a = 0 case
    have hodd := ord2_div_odd b hb1
    have hN : ∀ n : ℕ, (n - 1) / 2 = 0 → n % 2 = 1 → n = 1 := by
      intro n h1 h2
      have h3 : n - 1 < 2 := by
        by_contra hc
        push_neg at hc
        have := Nat.div_mul_le_self (n-1) 2
        omega
      omega
    have hquot : b / 2^(ord2 b) = 1 := hN _ ha0 hodd
    have hbeq : b = 2^(ord2 b) := by
      calc b = b / 2^(ord2 b) * 2^(ord2 b) := (Nat.div_mul_cancel (ord2_dvd b)).symm
        _ = 1 * 2^(ord2 b) := by rw [hquot]
        _ = 2^(ord2 b) := Nat.one_mul _
    refine ⟨ord2 b, ?_, hbeq⟩
    rw [hbeq] at hb
    exact pow2_ge_three _ hb

/-- `fA b = some b'` with `a_internal = 1` implies `b = 3 * 2^k` and `b' = b + k + 3`. -/
private lemma fA_some_a_eq_1 (b : ℕ) (hb : b ≥ 3) (b' : ℕ)
    (hfa : fA b = some b') (ha1 : (b / 2^(ord2 b) - 1) / 2 = 1) :
    ∃ k, b = 3 * 2^k ∧ b' = b + k + 3 := by
  have hb0 : b ≠ 0 := by omega
  have hb1 : 1 ≤ b := by omega
  simp only [fA] at hfa
  rw [if_neg hb0] at hfa
  have ha0 : (b / 2^(ord2 b) - 1) / 2 ≠ 0 := by omega
  rw [if_neg ha0, if_pos ha1] at hfa
  have hodd := ord2_div_odd b hb1
  have hquot : b / 2^(ord2 b) = 3 := by omega
  refine ⟨ord2 b, ?_, ?_⟩
  · calc b = b / 2^(ord2 b) * 2^(ord2 b) := (Nat.div_mul_cancel (ord2_dvd b)).symm
      _ = 3 * 2^(ord2 b) := by rw [hquot]
  · injection hfa with h; omega

/-- `fA b = some b'` with `a_internal ≥ 2` implies `b = (2a+1) * 2^k` and `b' = b + k + a`. -/
private lemma fA_some_a_ge_2 (b : ℕ) (hb : b ≥ 3) (b' : ℕ)
    (hfa : fA b = some b')
    (ha_ne_0 : (b / 2^(ord2 b) - 1) / 2 ≠ 0)
    (ha_ne_1 : (b / 2^(ord2 b) - 1) / 2 ≠ 1) :
    ∃ a k, a ≥ 2 ∧ b = (2*a + 1) * 2^k ∧ b' = b + k + a := by
  have hb0 : b ≠ 0 := by omega
  have hb1 : 1 ≤ b := by omega
  simp only [fA] at hfa
  rw [if_neg hb0, if_neg ha_ne_0, if_neg ha_ne_1] at hfa
  have hodd := ord2_div_odd b hb1
  let a := (b / 2^(ord2 b) - 1) / 2
  have ha2 : a ≥ 2 := by show (b / 2^(ord2 b) - 1) / 2 ≥ 2; omega
  have hquot : b / 2^(ord2 b) = 2 * a + 1 := by
    show b / 2^(ord2 b) = 2 * ((b / 2^(ord2 b) - 1) / 2) + 1
    omega
  refine ⟨a, ord2 b, ha2, ?_, ?_⟩
  · calc b = b / 2^(ord2 b) * 2^(ord2 b) := (Nat.div_mul_cancel (ord2_dvd b)).symm
      _ = (2*a + 1) * 2^(ord2 b) := by rw [hquot]
  · injection hfa with h; omega

/-- **Correspondence lemma**: for `b ≥ 3`, the `fA` halting of `b`
equivalent to `mathHalts` of `⟨b - 3, 2⟩`. -/
theorem fAHalts_iff_mathHalts_at_2 (b : ℕ) (hb : b ≥ 3) :
    fAHalts b ↔ mathHalts ⟨b - 3, 2⟩ := by
  constructor
  · -- Forward: fAHalts b → mathHalts ⟨b-3, 2⟩.
    intro h
    suffices H : ∀ b, fAHalts b → b ≥ 3 → mathHalts ⟨b - 3, 2⟩ from H b h hb
    intro b' h'
    induction h' with
    | haltStep b'' hfa =>
      intro hb''
      obtain ⟨k, hk, hbeq⟩ := fA_none_pow2 b'' hb'' hfa
      rw [hbeq]
      exact fA_sim_a_eq_0 k hk
    | nextStep b'' b''' hfa _h'' ih =>
      intro hb''
      by_cases ha0 : (b'' / 2^(ord2 b'') - 1) / 2 = 0
      · -- Contradicts fA b'' = some _
        have : fA b'' = none := by
          have hb0 : b'' ≠ 0 := by omega
          simp only [fA]
          rw [if_neg hb0, if_pos ha0]
        rw [this] at hfa; exact absurd hfa (by simp)
      by_cases ha1 : (b'' / 2^(ord2 b'') - 1) / 2 = 1
      · obtain ⟨k, hbeq, hb'eq⟩ := fA_some_a_eq_1 b'' hb'' b''' hfa ha1
        have hb'ge : b''' ≥ 3 := by omega
        refine mathHalts_of_reaches ⟨b'' - 3, 2⟩ ⟨b''' - 3, 2⟩ (k + 2) ?_ (ih hb'ge)
        rw [hb'eq, hbeq]
        have hsim := fA_sim_a_eq_1 k
        have heq2 : (3 * 2^k + k + 3 - 3 : ℕ) = 3 * 2^k + k := by omega
        rw [heq2]
        exact hsim
      · obtain ⟨a, k, ha2, hbeq, hb'eq⟩ := fA_some_a_ge_2 b'' hb'' b''' hfa ha0 ha1
        have hb'ge : b''' ≥ 3 := by omega
        refine mathHalts_of_reaches ⟨b'' - 3, 2⟩ ⟨b''' - 3, 2⟩ (k + 1) ?_ (ih hb'ge)
        rw [hb'eq, hbeq]
        exact fA_sim_a_ge_2 a k ha2
  · -- Backward: mathHalts ⟨b-3, 2⟩ → fAHalts b.
    rw [fAHalts_iff_fAIter, mathHalts_iff_mathIter]
    rintro ⟨m, hm⟩
    revert b
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intros b hb hm
      cases hfa : fA b with
      | none => exact ⟨1, by rw [fAIter_succ]; simp [fAIter, hfa]⟩
      | some b' =>
        by_cases ha0 : (b / 2^(ord2 b) - 1) / 2 = 0
        · -- Contradicts fA b = some b'
          simp only [fA] at hfa
          rw [if_neg (by omega : b ≠ 0), if_pos ha0] at hfa
          exact absurd hfa (by simp)
        by_cases ha1 : (b / 2^(ord2 b) - 1) / 2 = 1
        · obtain ⟨k, hbeq, hb'eq⟩ := fA_some_a_eq_1 b hb b' hfa ha1
          have hb'ge : b' ≥ 3 := by omega
          have hsim : mathIter (k + 2) (some ⟨b - 3, 2⟩) = some ⟨b' - 3, 2⟩ := by
            rw [hb'eq, hbeq]
            have heq2 : (3 * 2^k + k + 3 - 3 : ℕ) = 3 * 2^k + k := by omega
            rw [heq2]
            exact fA_sim_a_eq_1 k
          have hmge : m ≥ k + 2 := by
            by_contra hmlt
            push_neg at hmlt
            have hh : mathIter (k + 2) (some ⟨b - 3, 2⟩) = none := by
              rw [show (k + 2 : ℕ) = m + (k + 2 - m) from by omega,
                  mathIter_add, hm, mathIter_none]
            rw [hsim] at hh
            exact Option.some_ne_none _ hh
          have hrem : mathIter (m - (k + 2)) (some ⟨b' - 3, 2⟩) = none := by
            have hm' := hm
            rw [show m = (k + 2) + (m - (k + 2)) from by omega, mathIter_add, hsim] at hm'
            exact hm'
          obtain ⟨n, hn⟩ := ih (m - (k + 2)) (by omega) b' hb'ge hrem
          refine ⟨n + 1, ?_⟩
          rw [fAIter_succ, hfa]; exact hn
        · obtain ⟨a, k, ha2, hbeq, hb'eq⟩ := fA_some_a_ge_2 b hb b' hfa ha0 ha1
          have hb'ge : b' ≥ 3 := by omega
          have hsim : mathIter (k + 1) (some ⟨b - 3, 2⟩) = some ⟨b' - 3, 2⟩ := by
            rw [hb'eq, hbeq]
            exact fA_sim_a_ge_2 a k ha2
          have hmge : m ≥ k + 1 := by
            by_contra hmlt
            push_neg at hmlt
            have hh : mathIter (k + 1) (some ⟨b - 3, 2⟩) = none := by
              rw [show (k + 1 : ℕ) = m + (k + 1 - m) from by omega,
                  mathIter_add, hm, mathIter_none]
            rw [hsim] at hh
            exact Option.some_ne_none _ hh
          have hrem : mathIter (m - (k + 1)) (some ⟨b' - 3, 2⟩) = none := by
            have hm' := hm
            rw [show m = (k + 1) + (m - (k + 1)) from by omega, mathIter_add, hsim] at hm'
            exact hm'
          obtain ⟨n, hn⟩ := ih (m - (k + 1)) (by omega) b' hb'ge hrem
          refine ⟨n + 1, ?_⟩
          rw [fAIter_succ, hfa]; exact hn

/-- Initialization: `mathHalts ⟨2, 0⟩ ↔ mathHalts ⟨2, 2⟩`.
The TM's first two macro steps from the blank tape are R4 (`⟨2, 0⟩ →
⟨0, 3⟩`) then R1 (`⟨0, 3⟩ → ⟨2, 2⟩`). -/
theorem mathHalts_init_iff_A5 :
    mathHalts ⟨2, 0⟩ ↔ mathHalts ⟨2, 2⟩ := by
  constructor
  · intro h
    cases h with
    | haltStep _ hs => simp [nextMathState] at hs
    | nextStep _ s' hs hs' =>
      have heq : s' = ⟨0, 3⟩ := by
        have hn : nextMathState ⟨2, 0⟩ = some ⟨0, 3⟩ := rfl
        rw [hn] at hs; exact (Option.some.inj hs).symm
      subst heq
      cases hs' with
      | haltStep _ hs'' => simp [nextMathState] at hs''
      | nextStep _ s''' hs'' hs''' =>
        have heq' : s''' = ⟨2, 2⟩ := by
          have hn : nextMathState ⟨0, 3⟩ = some ⟨2, 2⟩ := rfl
          rw [hn] at hs''; exact (Option.some.inj hs'').symm
        subst heq'
        exact hs'''
  · intro h
    exact mathHalts.nextStep _ _ rfl
      (mathHalts.nextStep _ _ rfl h)

/-- **Hipparcos-style reformulation of BB(6)** (corrected).  The TM
halts iff the orbit of the A-level step function `fA` starting at `5`
eventually reaches a halt (i.e., lands on a power of 2).

The corrected `fA` matches the actual TM A-level dynamics exactly at
all points (including `a = 1`, using Yuan's `b + k + 3` rather than
Hipparcos's `b + k + 1`).

Combines `tm_halts_iff` (TM ↔ `mathHalts ⟨2, 0⟩`),
`mathHalts_init_iff_A5` (initial two macro steps to A(5)), the
correspondence lemma `fAHalts_iff_mathHalts_at_2`, and
`fAHalts_iff_fAIter`. -/
theorem tm_halts_iff_exists :
    (∃ k, (run tm (initConfig 6) k).state = none) ↔
    ∃ n : ℕ, fAIter n (some 5) = none := by
  rw [tm_halts_iff, mathHalts_init_iff_A5,
      ← fAHalts_iff_mathHalts_at_2 5 (by omega),
      fAHalts_iff_fAIter]

-- ============================================================
-- Summary
-- ============================================================
/-
This file contains a sorry-free proof of the following chain of equivalences
for the BB(6) candidate `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`:

    TM halts from blank tape
  ↔ mathHalts ⟨2, 0⟩                            (`tm_halts_iff`)
  ↔ ∃ n, mathIter n (some ⟨2, 0⟩) = none        (`tm_halts_iff_mathIter`)
  ↔ ∃ n, fAIter n (some 5) = none               (`tm_halts_iff_exists`)

where `fA` is the true A-level step function (halt at `2^k`; Yuan's
`b + k + 3` at `3·2^k`; Hipparcos's `b + k + a` for `a ≥ 2`).

The four macro rules (R1a, R1b, R2, R3, R4), the halt cases, and the
initial-config reach are each proved.  R2 and R3 are the major ones;
both use a phase decomposition (sweep + inner cycle + finalize).

Step counts verified empirically in `verify_dt.py` for m, k ∈ 0..7:
    R1    dt = 5
    R2    dt = 6m² + 21m + 14 + 4mk + 7k
    R3    dt = 2m² + 11m + 16                   (independent of k)
    R4    dt = 2

The correspondence `fAHalts b ↔ mathHalts ⟨b-3, 2⟩` (for b ≥ 3) is the
bridge between the pure-arithmetic orbit of `fA` and the TM's macro
dynamics.  `ord2 = b.factorization 2` uses Mathlib's 2-adic valuation.
-/

end Shifty6
