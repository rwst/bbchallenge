import BusyLean
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open BusyLean

namespace RachelineII

/-!
# 6-state TM `1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE`

A BB(6) holdout / Collatz-like candidate.  Halt/nonhalt is **not** the
target; this file records the macro rules empirically observed in
`sim.py` and stated in the wiki under "Analysis by Racheline"
(see `previous-work/wiki.txt`).

## Transition table
|   | 0   | 1   |
|---|-----|-----|
| A | 1RB | 1LE |
| B | 0LC | 0LB |
| C | 1RD | 1LC |
| D | 1RD | 1RA |
| E | 1RF | 0LA |
| F | --- | 1RE |

The only halting transition is `F,0 → ---`.  F is reached only from
`E,0 → 1RF`, so halting requires E to fire on a `0` whose neighbour to
the right (the cell F lands on) is itself `0`.

## Macro configuration  (Racheline)

```
A(N, m) = 0^∞ <C (10)^{N-6} 1^m 0^∞    for N ≥ 6, m ≥ 0
```

State C, head=0 (head sits on a blank cell to the LEFT of the pattern),
all blanks to the head's left, then `(10)^{N-6} 1^m` to the right
followed by blanks.

We parameterise by `n := N - 6` so `M n m` represents `A(n+6, m)`.  The
TM rules are stated below in terms of `n` (the wiki's parameterisation
uses `N` directly, with implicit constraints `N ≥ 6`).

## Macro rules  (verified by `sim.py dt`, n=3..10 for each rule)

For the wiki's `n` (= half of the first argument, with N ≥ 6):

```
  R_even   m≥3, n≥3:  A(2n,   m) → A(3n,   m-3)   dt = 6n² - 10n - 7
  R_odd    m≥3, n≥3:  A(2n+1, m) → A(3n+1, m-2)   dt = 6n² - 10n + 2
  R_odd_0      n≥3:   A(2n+1, 0) → A(6, 6n-15)    dt = 6n² - 22n + 19
  R_even_0     n≥4:   A(2n,   0) → A(6, 0)        dt = 6n² - 34n + 48
  R_even_2     n≥3:   A(2n,   2) → halt           dt = 6n² - 16n + 4
  R_odd_2      n≥3:   A(2n+1, 2) → A(6, 6n-10)    dt = 6n² - 10n + 1
  A(N, 1) = A(N+1, 0)                             (notational equivalence)
  A(6, 0)  → translated cycler (same config recurs shifted; never returns
                                to a finite-tape A(N, m) macro config)
```

In our `M n m` parameterisation (so `M n m = A(n+6, m)`), with `j := n - 3`
or `j := n - 4` so that `j ≥ 0`:

```
  R_even    M (2j)   (m+3) → M (3j+3) m,    dt = 6j² + 26j + 17       [j≥0]
  R_odd     M (2j+1) (m+3) → M (3j+4) (m+1), dt = 6j² + 26j + 26       [j≥0]
  R_odd_0   M (2j+1) 0     → M 0      (6j+3), dt = 6j² + 14j + 7        [j≥0]
  R_even_0  M (2j+2) 0     → M 0      0,     dt = 6j² + 14j + 8        [j≥0]
  R_even_2  M (2j)   2     → halt,           dt = 6j² + 20j + 10       [j≥0]
  R_odd_2   M (2j+1) 2     → M 0      (6j+8), dt = 6j² + 26j + 25       [j≥0]
```

(The sanity-check at the boundary `j = 0` is documented at each lemma.)

## Initial reach

Blank tape → `A(7, 0)` in 3 steps (state C, head on the blank just left
of a single `1`).  Then `A(7, 0)` is `M 1 0`; by the m=1 / m=0 collapse
this equals `M 0 1 = A(6, 1)`.  Applying R_odd_0 with `j = 0` gives
`A(7, 0) → A(6, 3)` in 7 more steps.  Total 10 steps from blank to
`A(6, 3) = M 0 3`, which is the wiki's stated starting macro config.

## Orbit (from `sim.py orbit`)

```
  i      N      m         dt          total
  0      6      3         17             17  → A(9, 0)
  1      9      0         27             44  → A(6, 9)
  2      6      9         17             61  → A(9, 6)
  3      9      6         58            119  → A(13, 4)
  4     13      4        158            277  → A(19, 2)
  5     19      2        397            674  → A(6, 44)
  ...
 22   3597      4   10000000+      timeout
```

The trajectory grows roughly geometrically; whether it ever halts is
the BB(6) question for this machine.
-/

def tm : TM 6 := tm! "1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE"

-- Transition simp lemmas: evaluate `tm.tr st sym` without unfolding the literal.
@[simp] private theorem tr_A0 : tm.tr stA false = some (stB, true,  Dir.R) := rfl
@[simp] private theorem tr_A1 : tm.tr stA true  = some (stE, true,  Dir.L) := rfl
@[simp] private theorem tr_B0 : tm.tr stB false = some (stC, false, Dir.L) := rfl
@[simp] private theorem tr_B1 : tm.tr stB true  = some (stB, false, Dir.L) := rfl
@[simp] private theorem tr_C0 : tm.tr stC false = some (stD, true,  Dir.R) := rfl
@[simp] private theorem tr_C1 : tm.tr stC true  = some (stC, true,  Dir.L) := rfl
@[simp] private theorem tr_D0 : tm.tr stD false = some (stD, true,  Dir.R) := rfl
@[simp] private theorem tr_D1 : tm.tr stD true  = some (stA, true,  Dir.R) := rfl
@[simp] private theorem tr_E0 : tm.tr stE false = some (stF, true,  Dir.R) := rfl
@[simp] private theorem tr_E1 : tm.tr stE true  = some (stA, false, Dir.L) := rfl
@[simp] private theorem tr_F0 : tm.tr stF false = none := rfl
@[simp] private theorem tr_F1 : tm.tr stF true  = some (stE, true,  Dir.R) := rfl

-- ============================================================
-- `tenpow` : the list `[1, 0, 1, 0, ..., 1, 0]` of length `2n`.
-- ============================================================

/-- `tenpow n` is the alternating list `[1, 0]` repeated `n` times.
Encodes the `(10)^n` block from the wiki's macro shape. -/
def tenpow : Nat → List Sym
  | 0     => []
  | n + 1 => true :: false :: tenpow n

@[simp] lemma tenpow_zero : tenpow 0 = [] := rfl
@[simp] lemma tenpow_succ (n : Nat) :
    tenpow (n + 1) = true :: false :: tenpow n := rfl

lemma tenpow_append (a b : Nat) :
    tenpow (a + b) = tenpow a ++ tenpow b := by
  induction a with
  | zero => simp
  | succ a' ih => simp [tenpow, ih, Nat.succ_add]

-- ============================================================
-- Macro configuration
-- ============================================================

/-- `M n m` — the wiki's `A(n+6, m)`: state C, head on `0`, blank tape
to the left, `(10)^n 1^m` followed by blanks to the right. -/
def M (n m : Nat) : SConfig 6 :=
  { state := some stC,
    head := false,
    left := blank∞,
    right := tenpow n *> ones m *> blank∞ }

private lemma tenpow_succ_append (n : Nat) :
    tenpow (n + 1) = tenpow n ++ [true, false] := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    show true :: false :: tenpow (n' + 1) = (true :: false :: tenpow n') ++ [true, false]
    rw [ih]; rfl

/-- **Notational equivalence**: `A(N, 1) = A(N+1, 0)` — the tape
`(10)^n 1 0^∞` equals `(10)^{n+1} 0^∞` because the trailing `0` of the
extra `(10)` block merges with `blank∞`.  In our parameterisation:
`M n 1 = M (n+1) 0`. -/
theorem M_collapse (n : Nat) : M n 1 = M (n + 1) 0 := by
  show ({ state := some stC, head := false, left := blank∞,
          right := tenpow n *> ones 1 *> blank∞ } : SConfig 6) = _
  congr 1
  rw [tenpow_succ_append n, Side.prepend_append]
  show Side.prepend (tenpow n) (Side.prepend (ones 1) blank∞)
     = Side.prepend (tenpow n) (Side.prepend [true, false] (Side.prepend (ones 0) blank∞))
  congr 1
  show Side.cons true blank∞ = Side.cons true (Side.cons false blank∞)
  rw [Side.cons_false_blank]

-- ============================================================
-- Macro rules (all sorried; verified by `sim.py dt`, n = 3..10)
-- ============================================================

/- **Rule R_even** is proved later, after the `IM_R_e` framework.
Wiki: `A(2n, m+3) → A(3n, m)`; in `M`-form: `M (2j) (m+3) → M (3j+3) m`
in `6j² + 26j + 17` steps. -/

/- **Rule R_odd** (`dt = 6j² + 26j + 26`) is proved later, after the
`IM_R_o` framework — see `rule_R_odd` below `IM_R_o_chain_gen`. -/

/- **Rule R_odd_0** (`dt = 6j² + 14j + 7`) is proved later, after the
`IM_e0` framework — see `rule_R_odd_0` below `IM_e0_chain`. -/

/-- Intermediate config for `rule_R_even_0`: state C, head on `0`, blank
left, right tape `(zeros 6i) *> tenpow (2j) *> blank∞`.

Boundary cases:
* `IM_e0 0 (j+1)` equals `M (2j+2) 0` (no leading zeros — initial config).
* `IM_e0 (j+1) 0` reduces to `M 0 0` semantically (trailing zeros collapse
  into blank, and `tenpow 0 = []`).

The transition `IM_e0 i (j+1) → IM_e0 (i+1) j` takes `12i + 8` steps
(verified by `sim.py`); summing for `i = 0..j` recovers
`6j² + 14j + 8`. -/
private def IM_e0 (i j : Nat) : SConfig 6 :=
  { state := some stC,
    head := false,
    left := blank∞,
    right := zeros (6*i) *> tenpow (2*j) *> blank∞ }

/-- Boundary 1: `M (2j+2) 0` is the same `SConfig` as `IM_e0 0 (j+1)`. -/
private lemma M_eq_IM_e0 (j : Nat) :
    M (2*j + 2) 0 = IM_e0 0 (j + 1) := by
  simp [M, IM_e0, show (6*0 : Nat) = 0 from rfl,
        show (2*(j+1) : Nat) = 2*j + 2 from by ring]

/-- **Shift lemma D-zeros**: state D with head=`F` consuming a `zeros k`
prefix in `k` steps; head stays `F` throughout, accumulating `ones k`
on the left. -/
private lemma D_zeros_shift (k : Nat) (L R : Side) :
    srun tm
      ({state := some stD, head := false, left := L,
        right := zeros k *> R} : SConfig 6) k
    = {state := some stD, head := false,
       left := ones k *> L, right := R} := by
  induction k generalizing L with
  | zero => simp [srun]
  | succ k' ih =>
    show srun tm _ (k' + 1) = _
    rw [show (k' + 1 : Nat) = k' + 1 from rfl,
        show srun tm
            ({state := some stD, head := false, left := L,
              right := zeros (k' + 1) *> R} : SConfig 6) (k' + 1)
          = srun tm (sstep tm
            ({state := some stD, head := false, left := L,
              right := zeros (k' + 1) *> R} : SConfig 6)) k' from rfl]
    have hstep : sstep tm
        ({state := some stD, head := false, left := L,
          right := zeros (k' + 1) *> R} : SConfig 6)
        = {state := some stD, head := false,
           left := Side.cons true L, right := zeros k' *> R} := by
      simp [sstep, tm, zeros]
    rw [hstep, ih (Side.cons true L)]
    congr 1
    show Side.prepend (ones k') (Side.cons true L)
       = Side.prepend (ones (k' + 1)) L
    show Side.prepend (ones k') (Side.prepend [true] L)
       = Side.prepend (ones (k' + 1)) L
    rw [← Side.prepend_append]
    congr 1
    show ones k' ++ ones 1 = ones (k' + 1)
    rw [ones_append]

/-- **Shift lemma B-drain**: state B with head=`T` draining `ones k` on
the left in `k` steps; head stays `T`, right accumulates `zeros k`. -/
private lemma B_drain_ones_shift (k : Nat) (R : Side) :
    srun tm
      ({state := some stB, head := true,
        left := ones k *> blank∞, right := R} : SConfig 6) k
    = {state := some stB, head := true,
       left := blank∞, right := zeros k *> R} := by
  induction k generalizing R with
  | zero => simp [srun]
  | succ k' ih =>
    show srun tm _ (k' + 1) = _
    rw [show srun tm
            ({state := some stB, head := true,
              left := ones (k' + 1) *> blank∞, right := R} : SConfig 6) (k' + 1)
          = srun tm (sstep tm
            ({state := some stB, head := true,
              left := ones (k' + 1) *> blank∞, right := R} : SConfig 6)) k' from rfl]
    have hstep : sstep tm
        ({state := some stB, head := true,
          left := ones (k' + 1) *> blank∞, right := R} : SConfig 6)
        = {state := some stB, head := true,
           left := ones k' *> blank∞, right := Side.cons false R} := by
      simp [sstep, tm, ones]
    rw [hstep, ih (Side.cons false R)]
    congr 1
    show Side.prepend (zeros k') (Side.cons false R)
       = Side.prepend (zeros (k' + 1)) R
    show Side.prepend (zeros k') (Side.prepend [false] R)
       = Side.prepend (zeros (k' + 1)) R
    rw [← Side.prepend_append]
    congr 1
    show zeros k' ++ zeros 1 = zeros (k' + 1)
    rw [zeros_append]

/-- Boundary 2: `IM_e0 i 0` reduces to `M 0 0` (right tape collapses to
blank because `tenpow 0 = []` and trailing `zeros k *> blank = blank`). -/
private lemma IM_e0_eq_M_0_0 (i : Nat) :
    IM_e0 i 0 = M 0 0 := by
  simp [IM_e0, M, tenpow]

/-- **Transition lemma** (UNPROVED): `IM_e0 i (j+1) → IM_e0 (i+1) j`
in `12i + 8` steps.

Phase decomposition (verified by `sim.py`):
* Phase A — C,0 fire (1 step):
  `{C, F, blank, zeros (6i) *> tenpow (2j+2)} →
   {D, head=tenpow's first cell or zeros' first F, ones 1, ...}`
* Phase B — D,0 right-sweep through zeros (`6i` steps for `i ≥ 0`):
  consumes the remaining `6i-1` zeros (for i ≥ 1) plus 1 cell into the
  start of `tenpow (2j+2)`; for `i = 0` consists of zero D,0 fires (the
  C-fire already lands on `tenpow`'s first `T`).  Total uniformly `6i`.
* Phase C — D,1 fire + A,0 fire (2 steps):
  state advances `D → A → B`, head ends on the second `T` of the
  `(10)`-pair, left = `ones (6i+3)`, right = `cons F (tenpow (2j))`.
* Phase D — B,1 drain through left ones (`6i+3` steps):
  drains `ones (6i+3) → blank`; right accumulates `(6i+3)` extra `F`s.
* Phase E — B,1 fire on blank (1 step): head `T → F` (left stays blank).
* Phase F — B,0 → C fire (1 step): state returns to `C`.

Total: `1 + 6i + 2 + (6i+3) + 1 + 1 = 12i + 8`.

Implementation requires shift lemmas `D_zeros_shift` (state D consumes
`k` leading `F`s in `k` steps) and `B_drain_ones_shift` (state B drains
`k` leading `T`s in `k` steps), plus careful tape rewriting via
`Side.prepend_append`, `cons_false_blank`, and `zeros_append`. -/
private lemma IM_e0_trans (i j : Nat) :
    srun tm (IM_e0 i (j + 1)) (12*i + 8) = IM_e0 (i + 1) j := by
  match i with
  | 0 =>
    -- i = 0: 8-step direct simp.
    simp [IM_e0, srun, sstep, tm, tenpow, zeros]
  | i' + 1 =>
    -- i = i'+1: 12i' + 20 = 1 + (6i'+5) + 1 + 1 + 1 + (6i'+9) + 1 + 1.
    -- Phases: C-fire + D-zeros-shift + D,0 (enter tenpow) + D,1 + A,0
    --       + B-drain + B,1-on-blank + B,0 → C.
    show srun tm (IM_e0 (i'+1) (j+1)) (12*(i'+1) + 8) = IM_e0 (i'+2) j
    rw [show (12*(i'+1) + 8 : Nat)
          = 1 + ((6*i'+5) + (1 + (1 + (1 + ((6*i'+9) + (1 + 1)))))) from by ring]
    -- Phase A: C-fire (1 step).
    rw [srun_add]
    have hA : srun tm (IM_e0 (i'+1) (j+1)) 1
        = ({state := some stD, head := false,
            left := ones 1 *> blank∞,
            right := zeros (6*i'+5) *> tenpow (2*j+2) *> blank∞} : SConfig 6) := by
      simp [IM_e0, srun, sstep, tm, zeros, ones,
            show (6*(i'+1) : Nat) = (6*i'+5) + 1 from by ring,
            show (2*(j+1) : Nat) = 2*j + 2 from by ring]
    rw [hA, srun_add, D_zeros_shift (6*i'+5) (ones 1 *> blank∞) (tenpow (2*j+2) *> blank∞)]
    -- After Phase B: state D, F, ones (6i'+6), tenpow (2j+2) *> blank.
    -- Combine left: ones (6i'+5) *> ones 1 *> blank = ones (6i'+6) *> blank.
    have hLcombine : Side.prepend (ones (6*i'+5)) (Side.prepend (ones 1) blank∞)
        = Side.prepend (ones (6*i'+6)) blank∞ := by
      rw [← Side.prepend_append, ones_append,
          show (6*i'+5 + 1 : Nat) = 6*i'+6 from by ring]
    rw [hLcombine, srun_add]
    -- Phase C: 1 D,0 fire (head F → T entering tenpow).
    have hC : srun tm
        ({state := some stD, head := false,
          left := ones (6*i'+6) *> blank∞,
          right := tenpow (2*j+2) *> blank∞} : SConfig 6) 1
        = {state := some stD, head := true,
           left := ones (6*i'+7) *> blank∞,
           right := Side.cons false (tenpow (2*j+1) *> blank∞)} := by
      simp [srun, sstep, tm, tenpow, ones,
            show (6*i'+7 : Nat) = (6*i'+6) + 1 from by ring]
    rw [hC, srun_add]
    -- Phase D: D,1 fire (1 step).
    have hD : srun tm
        ({state := some stD, head := true,
          left := ones (6*i'+7) *> blank∞,
          right := Side.cons false (tenpow (2*j+1) *> blank∞)} : SConfig 6) 1
        = {state := some stA, head := false,
           left := ones (6*i'+8) *> blank∞,
           right := tenpow (2*j+1) *> blank∞} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+8 : Nat) = (6*i'+7) + 1 from by ring]
    rw [hD, srun_add]
    -- Phase E: A,0 fire (1 step).
    have hE : srun tm
        ({state := some stA, head := false,
          left := ones (6*i'+8) *> blank∞,
          right := tenpow (2*j+1) *> blank∞} : SConfig 6) 1
        = {state := some stB, head := true,
           left := ones (6*i'+9) *> blank∞,
           right := Side.cons false (tenpow (2*j) *> blank∞)} := by
      simp [srun, sstep, tm, tenpow, ones,
            show (6*i'+9 : Nat) = (6*i'+8) + 1 from by ring]
    rw [hE, srun_add,
        B_drain_ones_shift (6*i'+9) (Side.cons false (tenpow (2*j) *> blank∞)),
        srun_add]
    -- Phase G: B,1 on blank (head T → F).
    have hG : srun tm
        ({state := some stB, head := true,
          left := blank∞,
          right := zeros (6*i'+9) *> Side.cons false (tenpow (2*j) *> blank∞)}
          : SConfig 6) 1
        = {state := some stB, head := false,
           left := blank∞,
           right := zeros (6*i'+10) *> Side.cons false (tenpow (2*j) *> blank∞)} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+10 : Nat) = (6*i'+9) + 1 from by ring,
            show zeros ((6*i'+9) + 1) = zeros 1 ++ zeros (6*i'+9) from by
              rw [Nat.add_comm, ← zeros_append]]
    rw [hG]
    -- Phase H: B,0 → C (1 step).
    show srun tm
        ({state := some stB, head := false,
          left := blank∞,
          right := zeros (6*i'+10) *> Side.cons false (tenpow (2*j) *> blank∞)}
          : SConfig 6) 1
        = IM_e0 (i'+2) j
    have hH : srun tm
        ({state := some stB, head := false,
          left := blank∞,
          right := zeros (6*i'+10) *> Side.cons false (tenpow (2*j) *> blank∞)}
          : SConfig 6) 1
        = {state := some stC, head := false,
           left := blank∞,
           right := zeros (6*i'+11) *> Side.cons false (tenpow (2*j) *> blank∞)} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+11 : Nat) = (6*i'+10) + 1 from by ring,
            show zeros ((6*i'+10) + 1) = zeros 1 ++ zeros (6*i'+10) from by
              rw [Nat.add_comm, ← zeros_append]]
    rw [hH]
    -- Final: zeros (6i'+11) *> cons F (tenpow (2j) *> blank) = zeros (6i'+12) *> tenpow (2j) *> blank.
    show ({state := some stC, head := false,
           left := blank∞,
           right := zeros (6*i'+11) *> Side.cons false (tenpow (2*j) *> blank∞)}
          : SConfig 6) = IM_e0 (i'+2) j
    simp [IM_e0, show (6*(i'+2) : Nat) = 6*i'+12 from by ring]
    show Side.prepend (zeros (6*i'+11)) (Side.cons false (Side.prepend (tenpow (2*j)) blank∞))
       = Side.prepend (zeros (6*i'+12)) (Side.prepend (tenpow (2*j)) blank∞)
    show Side.prepend (zeros (6*i'+11)) (Side.prepend [false] (Side.prepend (tenpow (2*j)) blank∞))
       = Side.prepend (zeros (6*i'+12)) (Side.prepend (tenpow (2*j)) blank∞)
    rw [← Side.prepend_append]
    congr 1
    show zeros (6*i'+11) ++ zeros 1 = zeros (6*i'+12)
    rw [zeros_append]

/-- **Chain lemma**: `IM_e0 0 (j+1) → IM_e0 (j+1) 0` in `6j² + 14j + 8`
steps, by induction on `j` using `IM_e0_trans`.

The chain is `IM_e0 0 (j+1) →[8] IM_e0 1 j →[20] IM_e0 2 (j-1) →[32]
... →[12j+8] IM_e0 (j+1) 0`.  Step count `∑_{i=0..j} (12i + 8) =
6j² + 14j + 8`. -/
private lemma IM_e0_chain_gen : ∀ (i j : Nat),
    srun tm (IM_e0 i j) (12*i*j + 6*j*j + 2*j) = IM_e0 (i + j) 0 := by
  intro i j
  induction j generalizing i with
  | zero =>
    simp [IM_e0, tenpow, show (i + 0 : Nat) = i from by ring]
  | succ j' ih =>
    rw [show (12*i*(j'+1) + 6*(j'+1)*(j'+1) + 2*(j'+1) : Nat)
          = (12*i + 8) + (12*(i+1)*j' + 6*j'*j' + 2*j') from by ring,
        srun_add, IM_e0_trans i j', ih (i+1),
        show (i + 1 + j' : Nat) = i + (j' + 1) from by ring]

private lemma IM_e0_chain (j : Nat) :
    srun tm (IM_e0 0 (j + 1)) (6*j*j + 14*j + 8) = IM_e0 (j + 1) 0 := by
  have h := IM_e0_chain_gen 0 (j + 1)
  rw [show (12*0*(j+1) + 6*(j+1)*(j+1) + 2*(j+1) : Nat) = 6*j*j + 14*j + 8 from by ring,
      show (0 + (j + 1) : Nat) = j + 1 from by ring] at h
  exact h

theorem rule_R_even_0 (j : Nat) :
    srun tm (M (2*j + 2) 0) (6*j*j + 14*j + 8) = M 0 0 := by
  rw [M_eq_IM_e0 j, IM_e0_chain j, IM_e0_eq_M_0_0 (j + 1)]

-- ============================================================
-- Infrastructure for `rule_R_odd_0`: parallel `IM_o` framework
-- ============================================================

/-- Intermediate config for `rule_R_odd_0`: state C, head on `0`, blank
left, right tape `(zeros 6i) *> tenpow (2j+1) *> blank∞`.

Boundary cases:
* `IM_o 0 j` equals `M (2j+1) 0` (initial config for the rule).
* `IM_o i 0` has right tape `zeros (6i) *> tenpow 1 *> blank∞`; the
  "final phase" lemma `IM_o_final` reduces it to `M 0 (6i+3)` in
  `12i + 7` steps.

Transition lemma `IM_o_trans` mirrors `IM_e0_trans`: the same 7-phase
decomposition (C-fire + D-zeros-shift + D,0 enter tenpow + D,1 + A,0 +
B-drain + B,1-on-blank + B,0→C) takes `12i + 8` steps from
`IM_o i (j+1)` to `IM_o (i+1) j`. -/
private def IM_o (i j : Nat) : SConfig 6 :=
  { state := some stC,
    head := false,
    left := blank∞,
    right := zeros (6*i) *> tenpow (2*j + 1) *> blank∞ }

private lemma M_eq_IM_o (j : Nat) :
    M (2*j + 1) 0 = IM_o 0 j := by
  simp [M, IM_o, show (6*0 : Nat) = 0 from rfl]

/-- **Shift lemma C-walk-left**: state C with head=`T` walking left
through `ones k` for `k` steps; head stays `T`, right accumulates
`ones k`. -/
private lemma C_walk_left (k : Nat) (R : Side) :
    srun tm
      ({state := some stC, head := true,
        left := ones k *> blank∞, right := R} : SConfig 6) k
    = {state := some stC, head := true,
       left := blank∞, right := ones k *> R} := by
  induction k generalizing R with
  | zero => simp [srun]
  | succ k' ih =>
    show srun tm _ (k' + 1) = _
    rw [show srun tm
            ({state := some stC, head := true,
              left := ones (k' + 1) *> blank∞, right := R} : SConfig 6) (k' + 1)
          = srun tm (sstep tm
            ({state := some stC, head := true,
              left := ones (k' + 1) *> blank∞, right := R} : SConfig 6)) k' from rfl]
    have hstep : sstep tm
        ({state := some stC, head := true,
          left := ones (k' + 1) *> blank∞, right := R} : SConfig 6)
        = {state := some stC, head := true,
           left := ones k' *> blank∞, right := Side.cons true R} := by
      simp [sstep, tm, ones]
    rw [hstep, ih (Side.cons true R)]
    congr 1
    show Side.prepend (ones k') (Side.cons true R)
       = Side.prepend (ones (k' + 1)) R
    show Side.prepend (ones k') (Side.prepend [true] R)
       = Side.prepend (ones (k' + 1)) R
    rw [← Side.prepend_append]
    congr 1
    show ones k' ++ ones 1 = ones (k' + 1)
    rw [ones_append]

/-- **Transition lemma**: `IM_o i (j+1) → IM_o (i+1) j` in `12i + 8`
steps.  Same 7-phase decomposition as `IM_e0_trans`, with `tenpow (2j+3)`
replacing `tenpow (2j+2)`. -/
private lemma IM_o_trans (i j : Nat) :
    srun tm (IM_o i (j + 1)) (12*i + 8) = IM_o (i + 1) j := by
  match i with
  | 0 =>
    simp [IM_o, srun, sstep, tm, tenpow, zeros]
  | i' + 1 =>
    show srun tm (IM_o (i'+1) (j+1)) (12*(i'+1) + 8) = IM_o (i'+2) j
    rw [show (12*(i'+1) + 8 : Nat)
          = 1 + ((6*i'+5) + (1 + (1 + (1 + ((6*i'+9) + (1 + 1)))))) from by ring]
    rw [srun_add]
    have hA : srun tm (IM_o (i'+1) (j+1)) 1
        = ({state := some stD, head := false,
            left := ones 1 *> blank∞,
            right := zeros (6*i'+5) *> tenpow (2*j+3) *> blank∞} : SConfig 6) := by
      simp [IM_o, srun, sstep, tm, zeros, ones,
            show (6*(i'+1) : Nat) = (6*i'+5) + 1 from by ring,
            show (2*(j+1) + 1 : Nat) = 2*j + 3 from by ring]
    rw [hA, srun_add, D_zeros_shift (6*i'+5) (ones 1 *> blank∞) (tenpow (2*j+3) *> blank∞)]
    have hLcombine : Side.prepend (ones (6*i'+5)) (Side.prepend (ones 1) blank∞)
        = Side.prepend (ones (6*i'+6)) blank∞ := by
      rw [← Side.prepend_append, ones_append,
          show (6*i'+5 + 1 : Nat) = 6*i'+6 from by ring]
    rw [hLcombine, srun_add]
    have hC : srun tm
        ({state := some stD, head := false,
          left := ones (6*i'+6) *> blank∞,
          right := tenpow (2*j+3) *> blank∞} : SConfig 6) 1
        = {state := some stD, head := true,
           left := ones (6*i'+7) *> blank∞,
           right := Side.cons false (tenpow (2*j+2) *> blank∞)} := by
      simp [srun, sstep, tm, tenpow, ones,
            show (6*i'+7 : Nat) = (6*i'+6) + 1 from by ring]
    rw [hC, srun_add]
    have hD : srun tm
        ({state := some stD, head := true,
          left := ones (6*i'+7) *> blank∞,
          right := Side.cons false (tenpow (2*j+2) *> blank∞)} : SConfig 6) 1
        = {state := some stA, head := false,
           left := ones (6*i'+8) *> blank∞,
           right := tenpow (2*j+2) *> blank∞} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+8 : Nat) = (6*i'+7) + 1 from by ring]
    rw [hD, srun_add]
    have hE : srun tm
        ({state := some stA, head := false,
          left := ones (6*i'+8) *> blank∞,
          right := tenpow (2*j+2) *> blank∞} : SConfig 6) 1
        = {state := some stB, head := true,
           left := ones (6*i'+9) *> blank∞,
           right := Side.cons false (tenpow (2*j+1) *> blank∞)} := by
      simp [srun, sstep, tm, tenpow, ones,
            show (6*i'+9 : Nat) = (6*i'+8) + 1 from by ring]
    rw [hE, srun_add,
        B_drain_ones_shift (6*i'+9) (Side.cons false (tenpow (2*j+1) *> blank∞)),
        srun_add]
    have hG : srun tm
        ({state := some stB, head := true,
          left := blank∞,
          right := zeros (6*i'+9) *> Side.cons false (tenpow (2*j+1) *> blank∞)}
          : SConfig 6) 1
        = {state := some stB, head := false,
           left := blank∞,
           right := zeros (6*i'+10) *> Side.cons false (tenpow (2*j+1) *> blank∞)} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+10 : Nat) = (6*i'+9) + 1 from by ring,
            show zeros ((6*i'+9) + 1) = zeros 1 ++ zeros (6*i'+9) from by
              rw [Nat.add_comm, ← zeros_append]]
    rw [hG]
    have hH : srun tm
        ({state := some stB, head := false,
          left := blank∞,
          right := zeros (6*i'+10) *> Side.cons false (tenpow (2*j+1) *> blank∞)}
          : SConfig 6) 1
        = {state := some stC, head := false,
           left := blank∞,
           right := zeros (6*i'+11) *> Side.cons false (tenpow (2*j+1) *> blank∞)} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+11 : Nat) = (6*i'+10) + 1 from by ring,
            show zeros ((6*i'+10) + 1) = zeros 1 ++ zeros (6*i'+10) from by
              rw [Nat.add_comm, ← zeros_append]]
    rw [hH]
    show ({state := some stC, head := false,
           left := blank∞,
           right := zeros (6*i'+11) *> Side.cons false (tenpow (2*j+1) *> blank∞)}
          : SConfig 6) = IM_o (i'+2) j
    simp [IM_o, show (6*(i'+2) : Nat) = 6*i'+12 from by ring]
    show Side.prepend (zeros (6*i'+11))
            (Side.cons false (Side.prepend (tenpow (2*j+1)) blank∞))
       = Side.prepend (zeros (6*i'+12)) (Side.prepend (tenpow (2*j+1)) blank∞)
    show Side.prepend (zeros (6*i'+11))
            (Side.prepend [false] (Side.prepend (tenpow (2*j+1)) blank∞))
       = Side.prepend (zeros (6*i'+12)) (Side.prepend (tenpow (2*j+1)) blank∞)
    rw [← Side.prepend_append]
    congr 1
    show zeros (6*i'+11) ++ zeros 1 = zeros (6*i'+12)
    rw [zeros_append]

/-- **Final phase lemma**: `IM_o i 0 → M 0 (6i + 3)` in `12i + 7` steps.
At this point the right tape has `zeros (6i) *> tenpow 1 *> blank` =
`zeros (6i) *> [T, F] *> blank`.  Phases:
C-fire + D-zeros-shift + D,0 (read T of tenpow 1) + D,1 + A,0 + B,0→C
+ C-walk-left + final C,1 on blank. -/
private lemma IM_o_final (i : Nat) :
    srun tm (IM_o i 0) (12*i + 7) = M 0 (6*i + 3) := by
  match i with
  | 0 =>
    simp [IM_o, M, srun, sstep, tm, tenpow, ones, zeros]
  | i' + 1 =>
    show srun tm (IM_o (i'+1) 0) (12*(i'+1) + 7) = M 0 (6*(i'+1) + 3)
    rw [show (12*(i'+1) + 7 : Nat)
          = 1 + ((6*i'+5) + (1 + (1 + (1 + (1 + ((6*i'+8) + 1)))))) from by ring]
    rw [srun_add]
    have hA : srun tm (IM_o (i'+1) 0) 1
        = ({state := some stD, head := false,
            left := ones 1 *> blank∞,
            right := zeros (6*i'+5) *> tenpow 1 *> blank∞} : SConfig 6) := by
      simp [IM_o, srun, sstep, tm, zeros, ones,
            show (6*(i'+1) : Nat) = (6*i'+5) + 1 from by ring]
    rw [hA, srun_add,
        D_zeros_shift (6*i'+5) (ones 1 *> blank∞) (tenpow 1 *> blank∞)]
    have hLcombine : Side.prepend (ones (6*i'+5)) (Side.prepend (ones 1) blank∞)
        = Side.prepend (ones (6*i'+6)) blank∞ := by
      rw [← Side.prepend_append, ones_append,
          show (6*i'+5 + 1 : Nat) = 6*i'+6 from by ring]
    rw [hLcombine, srun_add]
    have hC : srun tm
        ({state := some stD, head := false,
          left := ones (6*i'+6) *> blank∞,
          right := tenpow 1 *> blank∞} : SConfig 6) 1
        = {state := some stD, head := true,
           left := ones (6*i'+7) *> blank∞,
           right := Side.cons false blank∞} := by
      simp [srun, sstep, tm, tenpow, ones,
            show (6*i'+7 : Nat) = (6*i'+6) + 1 from by ring]
    rw [hC, srun_add]
    have hD : srun tm
        ({state := some stD, head := true,
          left := ones (6*i'+7) *> blank∞,
          right := Side.cons false blank∞} : SConfig 6) 1
        = {state := some stA, head := false,
           left := ones (6*i'+8) *> blank∞,
           right := blank∞} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+8 : Nat) = (6*i'+7) + 1 from by ring]
    rw [hD, srun_add]
    have hE : srun tm
        ({state := some stA, head := false,
          left := ones (6*i'+8) *> blank∞,
          right := blank∞} : SConfig 6) 1
        = {state := some stB, head := false,
           left := ones (6*i'+9) *> blank∞,
           right := blank∞} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+9 : Nat) = (6*i'+8) + 1 from by ring]
    rw [hE, srun_add]
    have hF : srun tm
        ({state := some stB, head := false,
          left := ones (6*i'+9) *> blank∞,
          right := blank∞} : SConfig 6) 1
        = {state := some stC, head := true,
           left := ones (6*i'+8) *> blank∞,
           right := blank∞} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+9 : Nat) = (6*i'+8) + 1 from by ring]
    rw [hF, srun_add, C_walk_left (6*i'+8) blank∞]
    have hH : srun tm
        ({state := some stC, head := true,
          left := blank∞,
          right := ones (6*i'+8) *> blank∞} : SConfig 6) 1
        = {state := some stC, head := false,
           left := blank∞,
           right := ones (6*i'+9) *> blank∞} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+9 : Nat) = (6*i'+8) + 1 from by ring]
    rw [hH]
    show ({state := some stC, head := false,
           left := blank∞,
           right := ones (6*i'+9) *> blank∞} : SConfig 6) = M 0 (6*(i'+1) + 3)
    simp [M, tenpow, show (6*(i'+1) + 3 : Nat) = 6*i'+9 from by ring]

/-- Chain lemma: from `IM_o 0 j`, in `6j² + 14j + 7` steps reach
`M 0 (6j + 3)`.  Strong induction on `j` using `IM_o_trans` and
`IM_o_final`. -/
private lemma IM_o_chain_gen : ∀ (i j : Nat),
    srun tm (IM_o i j) (12*i*j + 6*j*j + 2*j + (12*(i+j) + 7))
    = M 0 (6*(i+j) + 3) := by
  intro i j
  induction j generalizing i with
  | zero =>
    simp only [Nat.zero_mul, Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    exact IM_o_final i
  | succ j' ih =>
    rw [show (12*i*(j'+1) + 6*(j'+1)*(j'+1) + 2*(j'+1) + (12*(i+(j'+1)) + 7) : Nat)
          = (12*i + 8) + (12*(i+1)*j' + 6*j'*j' + 2*j' + (12*((i+1)+j') + 7)) from by ring,
        srun_add, IM_o_trans i j', ih (i+1),
        show (i + 1 + j' : Nat) = i + (j' + 1) from by ring]

/-- **Rule R_odd_0** (`dt = 6j² + 14j + 7`).
Wiki: `A(2n+1, 0) → A(6, 6n-15)` for `n ≥ 3`.
With `j := n - 3`: `M (2j+1) 0 → M 0 (6j+3)` in `6j² + 14j + 7` steps.

Sanity check at `j = 0`: `M 1 0 → M 0 3` in 7 steps. -/
theorem rule_R_odd_0 (j : Nat) :
    srun tm (M (2*j + 1) 0) (6*j*j + 14*j + 7) = M 0 (6*j + 3) := by
  rw [M_eq_IM_o j]
  have h := IM_o_chain_gen 0 j
  rw [show (12*0*j + 6*j*j + 2*j + (12*(0+j) + 7) : Nat) = 6*j*j + 14*j + 7 from by ring,
      show (0 + j : Nat) = j from by ring] at h
  exact h

/- **Rule R_even_2** (halt; `dt = 6j² + 20j + 11` Lean-counted; sim
reports `dt = 6j² + 20j + 10` because sim's count excludes the
halt-firing step itself).  Proved later, after the `IM_e_t` framework. -/

-- ============================================================
-- Infrastructure for `rule_R_odd_2`: `IM_o2` framework
-- ============================================================

/-- Intermediate config for `rule_R_odd_2`: state C, head on `0`, blank
left, right tape `(zeros 6i) *> tenpow (2j+1) *> ones 2 *> blank∞`.
Same shape as `IM_o` but with an `ones 2` trailer (encoding the `m = 2`
input of rule R_odd_2). -/
private def IM_o2 (i j : Nat) : SConfig 6 :=
  { state := some stC,
    head := false,
    left := blank∞,
    right := zeros (6*i) *> tenpow (2*j + 1) *> ones 2 *> blank∞ }

/-- Boundary: `M (2j+1) 2 = IM_o2 0 j`. -/
private lemma M_eq_IM_o2 (j : Nat) :
    M (2*j + 1) 2 = IM_o2 0 j := by
  simp [M, IM_o2, show (6*0 : Nat) = 0 from rfl]

/-- "Almost-final" intermediate: state C, head=0, blank left, right
tape `zeros k *> ones 1 *> blank∞`.  Reached at the end of the
`IM_o2 i 0` bridge (with `k = 6i + 5`). -/
private def IM_a (k : Nat) : SConfig 6 :=
  { state := some stC,
    head := false,
    left := blank∞,
    right := zeros k *> ones 1 *> blank∞ }

/-- **Transition lemma**: `IM_o2 i (j+1) → IM_o2 (i+1) j` in `12i + 8`
steps.  Same 7-phase decomposition as `IM_o_trans`, with the right
tape carrying an extra `*> ones 2 *> blank∞` trailer. -/
private lemma IM_o2_trans (i j : Nat) :
    srun tm (IM_o2 i (j + 1)) (12*i + 8) = IM_o2 (i + 1) j := by
  match i with
  | 0 =>
    simp [IM_o2, srun, sstep, tm, tenpow, ones, zeros]
  | i' + 1 =>
    show srun tm (IM_o2 (i'+1) (j+1)) (12*(i'+1) + 8) = IM_o2 (i'+2) j
    rw [show (12*(i'+1) + 8 : Nat)
          = 1 + ((6*i'+5) + (1 + (1 + (1 + ((6*i'+9) + (1 + 1)))))) from by ring]
    rw [srun_add]
    have hA : srun tm (IM_o2 (i'+1) (j+1)) 1
        = ({state := some stD, head := false,
            left := ones 1 *> blank∞,
            right := zeros (6*i'+5) *> tenpow (2*j+3) *> ones 2 *> blank∞}
           : SConfig 6) := by
      simp [IM_o2, srun, sstep, tm, zeros, ones,
            show (6*(i'+1) : Nat) = (6*i'+5) + 1 from by ring,
            show (2*(j+1) + 1 : Nat) = 2*j + 3 from by ring]
    rw [hA, srun_add,
        D_zeros_shift (6*i'+5) (ones 1 *> blank∞) (tenpow (2*j+3) *> ones 2 *> blank∞)]
    have hLcombine : Side.prepend (ones (6*i'+5)) (Side.prepend (ones 1) blank∞)
        = Side.prepend (ones (6*i'+6)) blank∞ := by
      rw [← Side.prepend_append, ones_append,
          show (6*i'+5 + 1 : Nat) = 6*i'+6 from by ring]
    rw [hLcombine, srun_add]
    have hC : srun tm
        ({state := some stD, head := false,
          left := ones (6*i'+6) *> blank∞,
          right := tenpow (2*j+3) *> ones 2 *> blank∞} : SConfig 6) 1
        = {state := some stD, head := true,
           left := ones (6*i'+7) *> blank∞,
           right := Side.cons false (tenpow (2*j+2) *> ones 2 *> blank∞)} := by
      simp [srun, sstep, tm, tenpow, ones,
            show (6*i'+7 : Nat) = (6*i'+6) + 1 from by ring]
    rw [hC, srun_add]
    have hD : srun tm
        ({state := some stD, head := true,
          left := ones (6*i'+7) *> blank∞,
          right := Side.cons false (tenpow (2*j+2) *> ones 2 *> blank∞)}
          : SConfig 6) 1
        = {state := some stA, head := false,
           left := ones (6*i'+8) *> blank∞,
           right := tenpow (2*j+2) *> ones 2 *> blank∞} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+8 : Nat) = (6*i'+7) + 1 from by ring]
    rw [hD, srun_add]
    have hE : srun tm
        ({state := some stA, head := false,
          left := ones (6*i'+8) *> blank∞,
          right := tenpow (2*j+2) *> ones 2 *> blank∞} : SConfig 6) 1
        = {state := some stB, head := true,
           left := ones (6*i'+9) *> blank∞,
           right := Side.cons false (tenpow (2*j+1) *> ones 2 *> blank∞)} := by
      simp [srun, sstep, tm, tenpow, ones,
            show (6*i'+9 : Nat) = (6*i'+8) + 1 from by ring]
    rw [hE, srun_add,
        B_drain_ones_shift (6*i'+9)
          (Side.cons false (tenpow (2*j+1) *> ones 2 *> blank∞)),
        srun_add]
    have hG : srun tm
        ({state := some stB, head := true,
          left := blank∞,
          right := zeros (6*i'+9) *>
            Side.cons false (tenpow (2*j+1) *> ones 2 *> blank∞)} : SConfig 6) 1
        = {state := some stB, head := false,
           left := blank∞,
           right := zeros (6*i'+10) *>
             Side.cons false (tenpow (2*j+1) *> ones 2 *> blank∞)} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+10 : Nat) = (6*i'+9) + 1 from by ring,
            show zeros ((6*i'+9) + 1) = zeros 1 ++ zeros (6*i'+9) from by
              rw [Nat.add_comm, ← zeros_append]]
    rw [hG]
    have hH : srun tm
        ({state := some stB, head := false,
          left := blank∞,
          right := zeros (6*i'+10) *>
            Side.cons false (tenpow (2*j+1) *> ones 2 *> blank∞)} : SConfig 6) 1
        = {state := some stC, head := false,
           left := blank∞,
           right := zeros (6*i'+11) *>
             Side.cons false (tenpow (2*j+1) *> ones 2 *> blank∞)} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+11 : Nat) = (6*i'+10) + 1 from by ring,
            show zeros ((6*i'+10) + 1) = zeros 1 ++ zeros (6*i'+10) from by
              rw [Nat.add_comm, ← zeros_append]]
    rw [hH]
    show ({state := some stC, head := false,
           left := blank∞,
           right := zeros (6*i'+11) *>
             Side.cons false (tenpow (2*j+1) *> ones 2 *> blank∞)} : SConfig 6)
       = IM_o2 (i'+2) j
    simp [IM_o2, show (6*(i'+2) : Nat) = 6*i'+12 from by ring]
    show Side.prepend (zeros (6*i'+11))
            (Side.cons false (Side.prepend (tenpow (2*j+1))
              (Side.prepend (ones 2) blank∞)))
       = Side.prepend (zeros (6*i'+12))
           (Side.prepend (tenpow (2*j+1)) (Side.prepend (ones 2) blank∞))
    show Side.prepend (zeros (6*i'+11))
            (Side.prepend [false] (Side.prepend (tenpow (2*j+1))
              (Side.prepend (ones 2) blank∞)))
       = Side.prepend (zeros (6*i'+12))
           (Side.prepend (tenpow (2*j+1)) (Side.prepend (ones 2) blank∞))
    rw [← Side.prepend_append]
    congr 1
    show zeros (6*i'+11) ++ zeros 1 = zeros (6*i'+12)
    rw [zeros_append]

/-- **Bridge lemma** (= "IM_o2 final phase, part 1"):
`IM_o2 i 0 → IM_a (6i + 5)` in `12i + 8` steps.  Same 7-phase shape as
`IM_o2_trans` but starting from `tenpow 1 *> ones 2 *> blank` and
ending in `ones 1 *> blank` (since `tenpow 1 *> ones 2 = [T,F,T,T]`
and after the C/D/A/B advance through 4 cells the leftover is just the
last `T` of `ones 2`). -/
private lemma IM_o2_bridge (i : Nat) :
    srun tm (IM_o2 i 0) (12*i + 8) = IM_a (6*i + 5) := by
  match i with
  | 0 =>
    simp [IM_o2, IM_a, srun, sstep, tm, tenpow, ones, zeros]
  | i' + 1 =>
    show srun tm (IM_o2 (i'+1) 0) (12*(i'+1) + 8) = IM_a (6*(i'+1) + 5)
    rw [show (12*(i'+1) + 8 : Nat)
          = 1 + ((6*i'+5) + (1 + (1 + (1 + ((6*i'+9) + (1 + 1)))))) from by ring]
    rw [srun_add]
    have hA : srun tm (IM_o2 (i'+1) 0) 1
        = ({state := some stD, head := false,
            left := ones 1 *> blank∞,
            right := zeros (6*i'+5) *> tenpow 1 *> ones 2 *> blank∞} : SConfig 6) := by
      simp [IM_o2, srun, sstep, tm, zeros, ones,
            show (6*(i'+1) : Nat) = (6*i'+5) + 1 from by ring]
    rw [hA, srun_add,
        D_zeros_shift (6*i'+5) (ones 1 *> blank∞) (tenpow 1 *> ones 2 *> blank∞)]
    have hLcombine : Side.prepend (ones (6*i'+5)) (Side.prepend (ones 1) blank∞)
        = Side.prepend (ones (6*i'+6)) blank∞ := by
      rw [← Side.prepend_append, ones_append,
          show (6*i'+5 + 1 : Nat) = 6*i'+6 from by ring]
    rw [hLcombine, srun_add]
    have hC : srun tm
        ({state := some stD, head := false,
          left := ones (6*i'+6) *> blank∞,
          right := tenpow 1 *> ones 2 *> blank∞} : SConfig 6) 1
        = {state := some stD, head := true,
           left := ones (6*i'+7) *> blank∞,
           right := Side.cons false (ones 2 *> blank∞)} := by
      simp [srun, sstep, tm, tenpow, ones,
            show (6*i'+7 : Nat) = (6*i'+6) + 1 from by ring]
    rw [hC, srun_add]
    have hD : srun tm
        ({state := some stD, head := true,
          left := ones (6*i'+7) *> blank∞,
          right := Side.cons false (ones 2 *> blank∞)} : SConfig 6) 1
        = {state := some stA, head := false,
           left := ones (6*i'+8) *> blank∞,
           right := ones 2 *> blank∞} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+8 : Nat) = (6*i'+7) + 1 from by ring]
    rw [hD, srun_add]
    have hE : srun tm
        ({state := some stA, head := false,
          left := ones (6*i'+8) *> blank∞,
          right := ones 2 *> blank∞} : SConfig 6) 1
        = {state := some stB, head := true,
           left := ones (6*i'+9) *> blank∞,
           right := ones 1 *> blank∞} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+9 : Nat) = (6*i'+8) + 1 from by ring]
    rw [hE, srun_add,
        B_drain_ones_shift (6*i'+9) (ones 1 *> blank∞),
        srun_add]
    have hG : srun tm
        ({state := some stB, head := true,
          left := blank∞,
          right := zeros (6*i'+9) *> ones 1 *> blank∞} : SConfig 6) 1
        = {state := some stB, head := false,
           left := blank∞,
           right := zeros (6*i'+10) *> ones 1 *> blank∞} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+10 : Nat) = (6*i'+9) + 1 from by ring,
            show zeros ((6*i'+9) + 1) = zeros 1 ++ zeros (6*i'+9) from by
              rw [Nat.add_comm, ← zeros_append]]
    rw [hG]
    have hH : srun tm
        ({state := some stB, head := false,
          left := blank∞,
          right := zeros (6*i'+10) *> ones 1 *> blank∞} : SConfig 6) 1
        = {state := some stC, head := false,
           left := blank∞,
           right := zeros (6*i'+11) *> ones 1 *> blank∞} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+11 : Nat) = (6*i'+10) + 1 from by ring,
            show zeros ((6*i'+10) + 1) = zeros 1 ++ zeros (6*i'+10) from by
              rw [Nat.add_comm, ← zeros_append]]
    rw [hH]
    show ({state := some stC, head := false,
           left := blank∞,
           right := zeros (6*i'+11) *> ones 1 *> blank∞} : SConfig 6)
       = IM_a (6*(i'+1) + 5)
    simp [IM_a, show (6*(i'+1) + 5 : Nat) = 6*i'+11 from by ring]

/-- **Final phase lemma**: `IM_a k → M 0 (k + 3)` in `2k + 7` steps.
Phases: C-fire + D-shift through `k` zeros + D,1 + A,0 + B,0→C + C-walk
+ final C,1 on blank. -/
private lemma IM_a_final (k : Nat) :
    srun tm (IM_a k) (2*k + 7) = M 0 (k + 3) := by
  match k with
  | 0 =>
    simp [IM_a, M, srun, sstep, tm, tenpow, ones, zeros]
  | k' + 1 =>
    show srun tm (IM_a (k'+1)) (2*(k'+1) + 7) = M 0 ((k'+1) + 3)
    rw [show (2*(k'+1) + 7 : Nat) = 1 + (k' + (1 + (1 + (1 + (1 + ((k'+3) + 1)))))) from by ring]
    rw [srun_add]
    have hA : srun tm (IM_a (k'+1)) 1
        = ({state := some stD, head := false,
            left := ones 1 *> blank∞,
            right := zeros k' *> ones 1 *> blank∞} : SConfig 6) := by
      simp [IM_a, srun, sstep, tm, zeros, ones]
    rw [hA, srun_add, D_zeros_shift k' (ones 1 *> blank∞) (ones 1 *> blank∞)]
    have hLcombine : Side.prepend (ones k') (Side.prepend (ones 1) blank∞)
        = Side.prepend (ones (k'+1)) blank∞ := by
      rw [← Side.prepend_append, ones_append]
    rw [hLcombine, srun_add]
    have hC : srun tm
        ({state := some stD, head := false,
          left := ones (k'+1) *> blank∞,
          right := ones 1 *> blank∞} : SConfig 6) 1
        = {state := some stD, head := true,
           left := ones (k'+2) *> blank∞,
           right := blank∞} := by
      simp [srun, sstep, tm, ones,
            show (k'+2 : Nat) = (k'+1) + 1 from by ring]
    rw [hC, srun_add]
    have hD : srun tm
        ({state := some stD, head := true,
          left := ones (k'+2) *> blank∞,
          right := blank∞} : SConfig 6) 1
        = {state := some stA, head := false,
           left := ones (k'+3) *> blank∞,
           right := blank∞} := by
      simp [srun, sstep, tm, ones,
            show (k'+3 : Nat) = (k'+2) + 1 from by ring]
    rw [hD, srun_add]
    have hE : srun tm
        ({state := some stA, head := false,
          left := ones (k'+3) *> blank∞,
          right := blank∞} : SConfig 6) 1
        = {state := some stB, head := false,
           left := ones (k'+4) *> blank∞,
           right := blank∞} := by
      simp [srun, sstep, tm, ones,
            show (k'+4 : Nat) = (k'+3) + 1 from by ring]
    rw [hE, srun_add]
    have hF : srun tm
        ({state := some stB, head := false,
          left := ones (k'+4) *> blank∞,
          right := blank∞} : SConfig 6) 1
        = {state := some stC, head := true,
           left := ones (k'+3) *> blank∞,
           right := blank∞} := by
      simp [srun, sstep, tm, ones,
            show (k'+4 : Nat) = (k'+3) + 1 from by ring]
    rw [hF, srun_add, C_walk_left (k'+3) blank∞]
    have hH : srun tm
        ({state := some stC, head := true,
          left := blank∞,
          right := ones (k'+3) *> blank∞} : SConfig 6) 1
        = {state := some stC, head := false,
           left := blank∞,
           right := ones (k'+4) *> blank∞} := by
      simp [srun, sstep, tm, ones,
            show (k'+4 : Nat) = (k'+3) + 1 from by ring]
    rw [hH]
    show ({state := some stC, head := false,
           left := blank∞,
           right := ones (k'+4) *> blank∞} : SConfig 6) = M 0 ((k'+1) + 3)
    simp [M, tenpow, show ((k'+1) + 3 : Nat) = k'+4 from by ring]

/-- Combined final phase: `IM_o2 i 0 → M 0 (6i + 8)` in `24i + 25`
steps.  `IM_o2_bridge` (12i+8) + `IM_a_final` at `k = 6i+5` (2(6i+5)+7
= 12i + 17). -/
private lemma IM_o2_final (i : Nat) :
    srun tm (IM_o2 i 0) (24*i + 25) = M 0 (6*i + 8) := by
  rw [show (24*i + 25 : Nat) = (12*i + 8) + (2*(6*i+5) + 7) from by ring,
      srun_add, IM_o2_bridge i, IM_a_final (6*i + 5),
      show (6*i + 5 + 3 : Nat) = 6*i + 8 from by ring]

/-- Chain: `IM_o2 i j → M 0 (6(i+j) + 8)` in
`12·i·j + 6j² + 2j + 24(i+j) + 25` steps.  Strong induction on `j`. -/
private lemma IM_o2_chain_gen : ∀ (i j : Nat),
    srun tm (IM_o2 i j) (12*i*j + 6*j*j + 2*j + (24*(i+j) + 25))
    = M 0 (6*(i+j) + 8) := by
  intro i j
  induction j generalizing i with
  | zero =>
    simp only [Nat.zero_mul, Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    exact IM_o2_final i
  | succ j' ih =>
    rw [show (12*i*(j'+1) + 6*(j'+1)*(j'+1) + 2*(j'+1) + (24*(i+(j'+1)) + 25) : Nat)
          = (12*i + 8) + (12*(i+1)*j' + 6*j'*j' + 2*j' + (24*((i+1)+j') + 25)) from by ring,
        srun_add, IM_o2_trans i j', ih (i+1),
        show (i + 1 + j' : Nat) = i + (j' + 1) from by ring]

/-- **Rule R_odd_2** (`dt = 6j² + 26j + 25`).
Wiki: `A(2n+1, 2) → A(6, 6n-10)` for `n ≥ 3`.
With `j := n - 3`: `M (2j+1) 2 → M 0 (6j+8)` in `6j² + 26j + 25` steps.

Sanity check at `j = 0`: `M 1 2 → M 0 8` in 25 steps
(i.e. `A(7, 2) → A(6, 8)` in 25 steps). -/
theorem rule_R_odd_2 (j : Nat) :
    srun tm (M (2*j + 1) 2) (6*j*j + 26*j + 25) = M 0 (6*j + 8) := by
  rw [M_eq_IM_o2 j]
  have h := IM_o2_chain_gen 0 j
  rw [show (12*0*j + 6*j*j + 2*j + (24*(0+j) + 25) : Nat) = 6*j*j + 26*j + 25 from by ring,
      show (0 + j : Nat) = j from by ring] at h
  exact h

-- ============================================================
-- Infrastructure for `rule_R_even_2`: `IM_e_t` framework
-- ============================================================

/-- Intermediate config for `rule_R_even_2`: state C, head on `0`, blank
left, right tape `(zeros 6i) *> tenpow (2j) *> ones 2 *> blank∞`.  Same
shape as `IM_o2` but with EVEN `tenpow` exponent (the rule starts from
`M (2j) 2` whose right tape is `tenpow (2j) *> ones 2 *> blank`). -/
private def IM_e_t (i j : Nat) : SConfig 6 :=
  { state := some stC,
    head := false,
    left := blank∞,
    right := zeros (6*i) *> tenpow (2*j) *> ones 2 *> blank∞ }

private lemma M_eq_IM_e_t (j : Nat) :
    M (2*j) 2 = IM_e_t 0 j := by
  simp [M, IM_e_t, show (6*0 : Nat) = 0 from rfl]

/-- Drain config: state A, head=`T`, left = `ones (2m+2) *> blank∞`,
right = blank.  Reached at the end of the `IM_e_t i 0` C+D phase
(with `m = 3i`). -/
private def IM_drain (m : Nat) : SConfig 6 :=
  { state := some stA, head := true,
    left := ones (2*m + 2) *> blank∞,
    right := blank∞ }

/-- **Transition lemma**: `IM_e_t i (j+1) → IM_e_t (i+1) j` in `12i + 8`
steps.  Same 7-phase decomposition as `IM_o2_trans`, with `tenpow (2j+2)`
(even exponent) replacing `tenpow (2j+3)` (odd). -/
private lemma IM_e_t_trans (i j : Nat) :
    srun tm (IM_e_t i (j + 1)) (12*i + 8) = IM_e_t (i + 1) j := by
  match i with
  | 0 =>
    simp [IM_e_t, srun, sstep, tm, tenpow, ones, zeros]
  | i' + 1 =>
    show srun tm (IM_e_t (i'+1) (j+1)) (12*(i'+1) + 8) = IM_e_t (i'+2) j
    rw [show (12*(i'+1) + 8 : Nat)
          = 1 + ((6*i'+5) + (1 + (1 + (1 + ((6*i'+9) + (1 + 1)))))) from by ring]
    rw [srun_add]
    have hA : srun tm (IM_e_t (i'+1) (j+1)) 1
        = ({state := some stD, head := false,
            left := ones 1 *> blank∞,
            right := zeros (6*i'+5) *> tenpow (2*j+2) *> ones 2 *> blank∞}
           : SConfig 6) := by
      simp [IM_e_t, srun, sstep, tm, zeros, ones,
            show (6*(i'+1) : Nat) = (6*i'+5) + 1 from by ring,
            show (2*(j+1) : Nat) = 2*j + 2 from by ring]
    rw [hA, srun_add,
        D_zeros_shift (6*i'+5) (ones 1 *> blank∞) (tenpow (2*j+2) *> ones 2 *> blank∞)]
    have hLcombine : Side.prepend (ones (6*i'+5)) (Side.prepend (ones 1) blank∞)
        = Side.prepend (ones (6*i'+6)) blank∞ := by
      rw [← Side.prepend_append, ones_append,
          show (6*i'+5 + 1 : Nat) = 6*i'+6 from by ring]
    rw [hLcombine, srun_add]
    have hC : srun tm
        ({state := some stD, head := false,
          left := ones (6*i'+6) *> blank∞,
          right := tenpow (2*j+2) *> ones 2 *> blank∞} : SConfig 6) 1
        = {state := some stD, head := true,
           left := ones (6*i'+7) *> blank∞,
           right := Side.cons false (tenpow (2*j+1) *> ones 2 *> blank∞)} := by
      simp [srun, sstep, tm, tenpow, ones,
            show (6*i'+7 : Nat) = (6*i'+6) + 1 from by ring]
    rw [hC, srun_add]
    have hD : srun tm
        ({state := some stD, head := true,
          left := ones (6*i'+7) *> blank∞,
          right := Side.cons false (tenpow (2*j+1) *> ones 2 *> blank∞)}
          : SConfig 6) 1
        = {state := some stA, head := false,
           left := ones (6*i'+8) *> blank∞,
           right := tenpow (2*j+1) *> ones 2 *> blank∞} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+8 : Nat) = (6*i'+7) + 1 from by ring]
    rw [hD, srun_add]
    have hE : srun tm
        ({state := some stA, head := false,
          left := ones (6*i'+8) *> blank∞,
          right := tenpow (2*j+1) *> ones 2 *> blank∞} : SConfig 6) 1
        = {state := some stB, head := true,
           left := ones (6*i'+9) *> blank∞,
           right := Side.cons false (tenpow (2*j) *> ones 2 *> blank∞)} := by
      simp [srun, sstep, tm, tenpow, ones,
            show (6*i'+9 : Nat) = (6*i'+8) + 1 from by ring]
    rw [hE, srun_add,
        B_drain_ones_shift (6*i'+9)
          (Side.cons false (tenpow (2*j) *> ones 2 *> blank∞)),
        srun_add]
    have hG : srun tm
        ({state := some stB, head := true,
          left := blank∞,
          right := zeros (6*i'+9) *>
            Side.cons false (tenpow (2*j) *> ones 2 *> blank∞)} : SConfig 6) 1
        = {state := some stB, head := false,
           left := blank∞,
           right := zeros (6*i'+10) *>
             Side.cons false (tenpow (2*j) *> ones 2 *> blank∞)} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+10 : Nat) = (6*i'+9) + 1 from by ring,
            show zeros ((6*i'+9) + 1) = zeros 1 ++ zeros (6*i'+9) from by
              rw [Nat.add_comm, ← zeros_append]]
    rw [hG]
    have hH : srun tm
        ({state := some stB, head := false,
          left := blank∞,
          right := zeros (6*i'+10) *>
            Side.cons false (tenpow (2*j) *> ones 2 *> blank∞)} : SConfig 6) 1
        = {state := some stC, head := false,
           left := blank∞,
           right := zeros (6*i'+11) *>
             Side.cons false (tenpow (2*j) *> ones 2 *> blank∞)} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+11 : Nat) = (6*i'+10) + 1 from by ring,
            show zeros ((6*i'+10) + 1) = zeros 1 ++ zeros (6*i'+10) from by
              rw [Nat.add_comm, ← zeros_append]]
    rw [hH]
    show ({state := some stC, head := false,
           left := blank∞,
           right := zeros (6*i'+11) *>
             Side.cons false (tenpow (2*j) *> ones 2 *> blank∞)} : SConfig 6)
       = IM_e_t (i'+2) j
    simp [IM_e_t, show (6*(i'+2) : Nat) = 6*i'+12 from by ring]
    show Side.prepend (zeros (6*i'+11))
            (Side.cons false (Side.prepend (tenpow (2*j))
              (Side.prepend (ones 2) blank∞)))
       = Side.prepend (zeros (6*i'+12))
           (Side.prepend (tenpow (2*j)) (Side.prepend (ones 2) blank∞))
    show Side.prepend (zeros (6*i'+11))
            (Side.prepend [false] (Side.prepend (tenpow (2*j))
              (Side.prepend (ones 2) blank∞)))
       = Side.prepend (zeros (6*i'+12))
           (Side.prepend (tenpow (2*j)) (Side.prepend (ones 2) blank∞))
    rw [← Side.prepend_append]
    congr 1
    show zeros (6*i'+11) ++ zeros 1 = zeros (6*i'+12)
    rw [zeros_append]

/-- **Bridge**: `IM_e_t i 0 → IM_drain (3i)` in `6i + 2` steps.
For `i = 0`: M 0 2 → IM_drain 0 in 2 steps (C,0 + D,1).
For `i ≥ 1`: C-fire + D-zeros-shift + 1 D,0 entering ones 2 + 1 D,1 fire. -/
private lemma IM_e_t_to_drain (i : Nat) :
    srun tm (IM_e_t i 0) (6*i + 2) = IM_drain (3*i) := by
  match i with
  | 0 =>
    simp [IM_e_t, IM_drain, srun, sstep, tm, tenpow, ones, zeros]
  | i' + 1 =>
    show srun tm (IM_e_t (i'+1) 0) (6*(i'+1) + 2) = IM_drain (3*(i'+1))
    rw [show (6*(i'+1) + 2 : Nat) = 1 + ((6*i'+5) + (1 + 1)) from by ring]
    rw [srun_add]
    have hA : srun tm (IM_e_t (i'+1) 0) 1
        = ({state := some stD, head := false,
            left := ones 1 *> blank∞,
            right := zeros (6*i'+5) *> ones 2 *> blank∞} : SConfig 6) := by
      simp [IM_e_t, srun, sstep, tm, zeros, ones, tenpow,
            show (6*(i'+1) : Nat) = (6*i'+5) + 1 from by ring]
    rw [hA, srun_add,
        D_zeros_shift (6*i'+5) (ones 1 *> blank∞) (ones 2 *> blank∞)]
    have hLcombine : Side.prepend (ones (6*i'+5)) (Side.prepend (ones 1) blank∞)
        = Side.prepend (ones (6*i'+6)) blank∞ := by
      rw [← Side.prepend_append, ones_append,
          show (6*i'+5 + 1 : Nat) = 6*i'+6 from by ring]
    rw [hLcombine, srun_add]
    have hC : srun tm
        ({state := some stD, head := false,
          left := ones (6*i'+6) *> blank∞,
          right := ones 2 *> blank∞} : SConfig 6) 1
        = {state := some stD, head := true,
           left := ones (6*i'+7) *> blank∞,
           right := ones 1 *> blank∞} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+7 : Nat) = (6*i'+6) + 1 from by ring]
    rw [hC]
    have hD : srun tm
        ({state := some stD, head := true,
          left := ones (6*i'+7) *> blank∞,
          right := ones 1 *> blank∞} : SConfig 6) 1
        = {state := some stA, head := true,
           left := ones (6*i'+8) *> blank∞,
           right := blank∞} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+8 : Nat) = (6*i'+7) + 1 from by ring]
    rw [hD]
    show ({state := some stA, head := true,
           left := ones (6*i'+8) *> blank∞,
           right := blank∞} : SConfig 6) = IM_drain (3*(i'+1))
    simp [IM_drain, show (2*(3*(i'+1)) + 2 : Nat) = 6*i'+8 from by ring]

/-- **A-E drain shift**: from state A, head=`T`, left = `ones (2k) *> L`,
in `2k` steps (alternating A,1 and E,1 fires) reach state A, head=`T`,
left = `L`, right grew by `zebra k` (= `[F,T]` repeated `k` times). -/
private lemma A_E_drain (k : Nat) (L R : Side) :
    srun tm
      ({state := some stA, head := true,
        left := ones (2*k) *> L, right := R} : SConfig 6) (2*k)
    = {state := some stA, head := true,
       left := L, right := zebra k *> R} := by
  induction k generalizing R with
  | zero => simp [srun]
  | succ k' ih =>
    -- 2*(k'+1) = (2*k' + 1) + 1 = (2*k') + 2 by rfl, so
    --   srun tm c (2*(k'+1)) = srun tm (sstep tm (sstep tm c)) (2*k') by rfl.
    show srun tm
      ({state := some stA, head := true,
        left := ones (2*(k'+1)) *> L, right := R} : SConfig 6) (2*(k'+1)) = _
    rw [show srun tm
          ({state := some stA, head := true,
            left := ones (2*(k'+1)) *> L, right := R} : SConfig 6) (2*(k'+1))
        = srun tm (sstep tm (sstep tm
          ({state := some stA, head := true,
            left := ones (2*(k'+1)) *> L, right := R} : SConfig 6))) (2*k') from rfl]
    have hsstep : sstep tm (sstep tm
        ({state := some stA, head := true,
          left := ones (2*(k'+1)) *> L, right := R} : SConfig 6))
        = {state := some stA, head := true,
           left := ones (2*k') *> L,
           right := Side.cons false (Side.cons true R)} := by
      simp [sstep, tm, ones,
            show (2*(k'+1) : Nat) = (2*k' + 1) + 1 from by ring,
            show (2*k' + 1 : Nat) = 2*k' + 1 from rfl]
    rw [hsstep, ih (Side.cons false (Side.cons true R))]
    congr 1
    show Side.prepend (zebra k') (Side.cons false (Side.cons true R))
       = Side.prepend (zebra (k'+1)) R
    show Side.prepend (zebra k') (Side.prepend [false, true] R)
       = Side.prepend (zebra (k'+1)) R
    rw [← Side.prepend_append, zebra_succ_append]

/-- **F walk shift**: from state F, head=`T`, with right = `zebra k *> blank∞`,
in `2k` steps (alternating F,1 and E,0 fires) reach state F, head=`T`,
left grew by `ones (2k)`, right = `blank∞`. -/
private lemma F_walk (k : Nat) (L : Side) :
    srun tm
      ({state := some stF, head := true,
        left := L, right := zebra k *> blank∞} : SConfig 6) (2*k)
    = {state := some stF, head := true,
       left := ones (2*k) *> L, right := blank∞} := by
  induction k generalizing L with
  | zero => simp [srun]
  | succ k' ih =>
    show srun tm
      ({state := some stF, head := true,
        left := L, right := zebra (k'+1) *> blank∞} : SConfig 6) (2*(k'+1)) = _
    rw [show srun tm
          ({state := some stF, head := true,
            left := L, right := zebra (k'+1) *> blank∞} : SConfig 6) (2*(k'+1))
        = srun tm (sstep tm (sstep tm
          ({state := some stF, head := true,
            left := L, right := zebra (k'+1) *> blank∞} : SConfig 6))) (2*k') from rfl]
    have hsstep : sstep tm (sstep tm
        ({state := some stF, head := true,
          left := L, right := zebra (k'+1) *> blank∞} : SConfig 6))
        = {state := some stF, head := true,
           left := ones 2 *> L, right := zebra k' *> blank∞} := by
      simp [sstep, tm, zebra, ones]
    rw [hsstep, ih (ones 2 *> L)]
    congr 1
    show Side.prepend (ones (2*k')) (Side.prepend (ones 2) L)
       = Side.prepend (ones (2*(k'+1))) L
    rw [← Side.prepend_append, ones_append,
        show (2*k' + 2 : Nat) = 2*(k'+1) from by ring]

/-- **Halt phase**: `IM_drain m` halts in `4m + 9` steps.
Phases: A_E_drain (drain `ones (2m+2)`, `2m+2` steps) +
1 step (A,1 fire on blank-listHead F) +
1 step (E,0 fire entering the built-up zebra) +
F_walk (`2(m+1)` steps consuming `zebra (m+1)`) +
3 steps (F,1 + E,0 + F,0 → halt). -/
private lemma IM_drain_halts (m : Nat) :
    (srun tm (IM_drain m) (4*m + 9)).state = none := by
  rw [show (4*m + 9 : Nat)
        = (2*(m+1)) + (1 + (1 + (2*(m+1) + (1 + (1 + 1))))) from by ring,
      srun_add]
  -- Phase 1: A_E_drain (m+1).
  have h1 : srun tm (IM_drain m) (2*(m+1))
      = ({state := some stA, head := true, left := blank∞,
          right := zebra (m+1) *> blank∞} : SConfig 6) := by
    have h := A_E_drain (m+1) blank∞ blank∞
    rw [show (2*(m+1) : Nat) = 2*(m+1) from rfl] at h
    show srun tm
      ({state := some stA, head := true,
        left := ones (2*m+2) *> blank∞, right := blank∞} : SConfig 6) (2*(m+1)) = _
    rw [show (2*m+2 : Nat) = 2*(m+1) from by ring]
    exact h
  rw [h1, srun_add]
  -- Phase 2: A,1 fire (h=T from listHead blank=F, but state A reads h=T).
  have h2 : srun tm
      ({state := some stA, head := true, left := blank∞,
        right := zebra (m+1) *> blank∞} : SConfig 6) 1
      = {state := some stE, head := false, left := blank∞,
         right := Side.cons true (zebra (m+1) *> blank∞)} := by
    simp [srun, sstep, tm]
  rw [h2, srun_add]
  -- Phase 3: E,0 fire (h=F).
  have h3 : srun tm
      ({state := some stE, head := false, left := blank∞,
        right := Side.cons true (zebra (m+1) *> blank∞)} : SConfig 6) 1
      = {state := some stF, head := true, left := ones 1 *> blank∞,
         right := zebra (m+1) *> blank∞} := by
    simp [srun, sstep, tm, ones]
  rw [h3, srun_add, F_walk (m+1) (ones 1 *> blank∞)]
  -- Combine left: ones (2(m+1)) *> ones 1 *> blank = ones (2m+3) *> blank.
  have hLcombine : Side.prepend (ones (2*(m+1))) (Side.prepend (ones 1) blank∞)
      = Side.prepend (ones (2*m+3)) blank∞ := by
    rw [← Side.prepend_append, ones_append,
        show (2*(m+1) + 1 : Nat) = 2*m+3 from by ring]
  rw [hLcombine, srun_add]
  -- Phase 4: F,1 fire on blank.
  have h4 : srun tm
      ({state := some stF, head := true,
        left := ones (2*m+3) *> blank∞, right := blank∞} : SConfig 6) 1
      = {state := some stE, head := false,
         left := ones (2*m+4) *> blank∞, right := blank∞} := by
    simp [srun, sstep, tm, ones,
          show (2*m+4 : Nat) = (2*m+3) + 1 from by ring]
  rw [h4, srun_add]
  -- Phase 5: E,0 fire on blank.
  have h5 : srun tm
      ({state := some stE, head := false,
        left := ones (2*m+4) *> blank∞, right := blank∞} : SConfig 6) 1
      = {state := some stF, head := false,
         left := ones (2*m+5) *> blank∞, right := blank∞} := by
    simp [srun, sstep, tm, ones,
          show (2*m+5 : Nat) = (2*m+4) + 1 from by ring]
  rw [h5]
  -- Phase 6: F,0 → halt.
  show (srun tm
      ({state := some stF, head := false,
        left := ones (2*m+5) *> blank∞, right := blank∞} : SConfig 6) 1).state = none
  simp [srun, sstep, tm]

/-- Combined final phase: `IM_e_t i 0` halts in `18i + 11` steps.
`IM_e_t_to_drain` (`6i+2` steps to `IM_drain (3i)`) +
`IM_drain_halts` at `m = 3i` (`12i + 9` steps to halt). -/
private lemma IM_e_t_final (i : Nat) :
    (srun tm (IM_e_t i 0) (18*i + 11)).state = none := by
  rw [show (18*i + 11 : Nat) = (6*i + 2) + (4*(3*i) + 9) from by ring,
      srun_add, IM_e_t_to_drain i]
  exact IM_drain_halts (3*i)

/-- Chain: `IM_e_t i j` halts in `12·i·j + 6j² + 2j + 18(i+j) + 11`
steps.  Strong induction on `j`. -/
private lemma IM_e_t_chain_gen : ∀ (i j : Nat),
    (srun tm (IM_e_t i j) (12*i*j + 6*j*j + 2*j + (18*(i+j) + 11))).state = none := by
  intro i j
  induction j generalizing i with
  | zero =>
    simp only [Nat.zero_mul, Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    exact IM_e_t_final i
  | succ j' ih =>
    rw [show (12*i*(j'+1) + 6*(j'+1)*(j'+1) + 2*(j'+1) + (18*(i+(j'+1)) + 11) : Nat)
          = (12*i + 8) + (12*(i+1)*j' + 6*j'*j' + 2*j' + (18*((i+1)+j') + 11)) from by ring,
        srun_add, IM_e_t_trans i j']
    exact ih (i+1)

/-- **Rule R_even_2** (halt; Lean step count `6j² + 20j + 11`).
Wiki: `A(2n, 2) → halt` for `n ≥ 3`.
With `j := n - 3`: `M (2j) 2` halts in `6j² + 20j + 11` Lean steps.

Note on step count: the literature (Racheline / `sim.py`) reports
`dt = 6j² + 20j + 10` because `sim` counts non-halt transitions only;
the halt-firing step itself is excluded.  Lean's `sstep` semantics
treat the halt transition as a regular step that produces `state =
none`, hence the off-by-one (`+11` instead of `+10`).

Sanity check at `j = 0`: `M 0 2` halts in 11 Lean steps. -/
theorem rule_R_even_2 (j : Nat) :
    (srun tm (M (2*j) 2) (6*j*j + 20*j + 11)).state = none := by
  rw [M_eq_IM_e_t j]
  have h := IM_e_t_chain_gen 0 j
  rw [show (12*0*j + 6*j*j + 2*j + (18*(0+j) + 11) : Nat) = 6*j*j + 20*j + 11 from by ring]
    at h
  exact h

-- ============================================================
-- Infrastructure for `rule_R_even`: `IM_R_e` framework
-- ============================================================

/-- Intermediate config for `rule_R_even`: state C, head on `0`, blank
left, right tape `(zeros 6i) *> tenpow (2j) *> ones (m+3) *> blank∞`.
Same shape as `IM_e_t` but with `ones (m+3)` instead of `ones 2`. -/
private def IM_R_e (i j m : Nat) : SConfig 6 :=
  { state := some stC,
    head := false,
    left := blank∞,
    right := zeros (6*i) *> tenpow (2*j) *> ones (m + 3) *> blank∞ }

/-- After-iterations intermediate: `zeros (6i) *> ones (m+3) *> blank`.
Equal to `IM_R_e i 0 m`. -/
private def IM_R_e_post (i m : Nat) : SConfig 6 :=
  { state := some stC,
    head := false,
    left := blank∞,
    right := zeros (6*i) *> ones (m + 3) *> blank∞ }

private lemma M_eq_IM_R_e (j m : Nat) :
    M (2*j) (m + 3) = IM_R_e 0 j m := by
  simp [M, IM_R_e, show (6*0 : Nat) = 0 from rfl]

private lemma IM_R_e_post_eq (i m : Nat) : IM_R_e i 0 m = IM_R_e_post i m := by
  simp [IM_R_e, IM_R_e_post, tenpow]

/-- **Transition lemma**: `IM_R_e i (j+1) m → IM_R_e (i+1) j m` in
`12i + 8` steps.  Same proof structure as `IM_e_t_trans`/`IM_o2_trans`,
with `ones (m+3)` trailer (the trailer commutes through all phases). -/
private lemma IM_R_e_trans (i j m : Nat) :
    srun tm (IM_R_e i (j + 1) m) (12*i + 8) = IM_R_e (i + 1) j m := by
  match i with
  | 0 =>
    simp [IM_R_e, srun, sstep, tm, tenpow, ones, zeros]
  | i' + 1 =>
    show srun tm (IM_R_e (i'+1) (j+1) m) (12*(i'+1) + 8) = IM_R_e (i'+2) j m
    rw [show (12*(i'+1) + 8 : Nat)
          = 1 + ((6*i'+5) + (1 + (1 + (1 + ((6*i'+9) + (1 + 1)))))) from by ring]
    rw [srun_add]
    have hA : srun tm (IM_R_e (i'+1) (j+1) m) 1
        = ({state := some stD, head := false,
            left := ones 1 *> blank∞,
            right := zeros (6*i'+5) *> tenpow (2*j+2) *> ones (m+3) *> blank∞}
           : SConfig 6) := by
      simp [IM_R_e, srun, sstep, tm, zeros, ones,
            show (6*(i'+1) : Nat) = (6*i'+5) + 1 from by ring,
            show (2*(j+1) : Nat) = 2*j + 2 from by ring]
    rw [hA, srun_add,
        D_zeros_shift (6*i'+5) (ones 1 *> blank∞)
          (tenpow (2*j+2) *> ones (m+3) *> blank∞)]
    have hLcombine : Side.prepend (ones (6*i'+5)) (Side.prepend (ones 1) blank∞)
        = Side.prepend (ones (6*i'+6)) blank∞ := by
      rw [← Side.prepend_append, ones_append,
          show (6*i'+5 + 1 : Nat) = 6*i'+6 from by ring]
    rw [hLcombine, srun_add]
    have hC : srun tm
        ({state := some stD, head := false,
          left := ones (6*i'+6) *> blank∞,
          right := tenpow (2*j+2) *> ones (m+3) *> blank∞} : SConfig 6) 1
        = {state := some stD, head := true,
           left := ones (6*i'+7) *> blank∞,
           right := Side.cons false (tenpow (2*j+1) *> ones (m+3) *> blank∞)} := by
      simp [srun, sstep, tm, tenpow, ones,
            show (6*i'+7 : Nat) = (6*i'+6) + 1 from by ring]
    rw [hC, srun_add]
    have hD : srun tm
        ({state := some stD, head := true,
          left := ones (6*i'+7) *> blank∞,
          right := Side.cons false (tenpow (2*j+1) *> ones (m+3) *> blank∞)}
          : SConfig 6) 1
        = {state := some stA, head := false,
           left := ones (6*i'+8) *> blank∞,
           right := tenpow (2*j+1) *> ones (m+3) *> blank∞} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+8 : Nat) = (6*i'+7) + 1 from by ring]
    rw [hD, srun_add]
    have hE : srun tm
        ({state := some stA, head := false,
          left := ones (6*i'+8) *> blank∞,
          right := tenpow (2*j+1) *> ones (m+3) *> blank∞} : SConfig 6) 1
        = {state := some stB, head := true,
           left := ones (6*i'+9) *> blank∞,
           right := Side.cons false (tenpow (2*j) *> ones (m+3) *> blank∞)} := by
      simp [srun, sstep, tm, tenpow, ones,
            show (6*i'+9 : Nat) = (6*i'+8) + 1 from by ring]
    rw [hE, srun_add,
        B_drain_ones_shift (6*i'+9)
          (Side.cons false (tenpow (2*j) *> ones (m+3) *> blank∞)),
        srun_add]
    have hG : srun tm
        ({state := some stB, head := true,
          left := blank∞,
          right := zeros (6*i'+9) *>
            Side.cons false (tenpow (2*j) *> ones (m+3) *> blank∞)} : SConfig 6) 1
        = {state := some stB, head := false,
           left := blank∞,
           right := zeros (6*i'+10) *>
             Side.cons false (tenpow (2*j) *> ones (m+3) *> blank∞)} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+10 : Nat) = (6*i'+9) + 1 from by ring,
            show zeros ((6*i'+9) + 1) = zeros 1 ++ zeros (6*i'+9) from by
              rw [Nat.add_comm, ← zeros_append]]
    rw [hG]
    have hH : srun tm
        ({state := some stB, head := false,
          left := blank∞,
          right := zeros (6*i'+10) *>
            Side.cons false (tenpow (2*j) *> ones (m+3) *> blank∞)} : SConfig 6) 1
        = {state := some stC, head := false,
           left := blank∞,
           right := zeros (6*i'+11) *>
             Side.cons false (tenpow (2*j) *> ones (m+3) *> blank∞)} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+11 : Nat) = (6*i'+10) + 1 from by ring,
            show zeros ((6*i'+10) + 1) = zeros 1 ++ zeros (6*i'+10) from by
              rw [Nat.add_comm, ← zeros_append]]
    rw [hH]
    show ({state := some stC, head := false,
           left := blank∞,
           right := zeros (6*i'+11) *>
             Side.cons false (tenpow (2*j) *> ones (m+3) *> blank∞)} : SConfig 6)
       = IM_R_e (i'+2) j m
    simp [IM_R_e, show (6*(i'+2) : Nat) = 6*i'+12 from by ring]
    show Side.prepend (zeros (6*i'+11))
            (Side.cons false (Side.prepend (tenpow (2*j))
              (Side.prepend (ones (m+3)) blank∞)))
       = Side.prepend (zeros (6*i'+12))
           (Side.prepend (tenpow (2*j))
             (Side.prepend (ones (m+3)) blank∞))
    show Side.prepend (zeros (6*i'+11))
            (Side.prepend [false] (Side.prepend (tenpow (2*j))
              (Side.prepend (ones (m+3)) blank∞)))
       = Side.prepend (zeros (6*i'+12))
           (Side.prepend (tenpow (2*j))
             (Side.prepend (ones (m+3)) blank∞))
    rw [← Side.prepend_append]
    congr 1
    show zeros (6*i'+11) ++ zeros 1 = zeros (6*i'+12)
    rw [zeros_append]

/-- **EF tenpow walk**: state E with head=`F`, walking right through
`tenpow k` (interleaved T, F starting with T).  Each pair of trans
(E,0 + F,1) consumes 2 cells (T then F), adds 2 ones to left. -/
private lemma EF_tenpow_walk (k : Nat) (L T : Side) :
    srun tm
      ({state := some stE, head := false,
        left := L, right := tenpow k *> T} : SConfig 6) (2*k)
    = {state := some stE, head := false,
       left := ones (2*k) *> L, right := T} := by
  induction k generalizing L with
  | zero => simp [srun, tenpow]
  | succ k' ih =>
    show srun tm
      ({state := some stE, head := false,
        left := L, right := tenpow (k'+1) *> T} : SConfig 6) (2*(k'+1)) = _
    rw [show srun tm
          ({state := some stE, head := false,
            left := L, right := tenpow (k'+1) *> T} : SConfig 6) (2*(k'+1))
        = srun tm (sstep tm (sstep tm
          ({state := some stE, head := false,
            left := L, right := tenpow (k'+1) *> T} : SConfig 6))) (2*k') from rfl]
    have hsstep : sstep tm (sstep tm
        ({state := some stE, head := false,
          left := L, right := tenpow (k'+1) *> T} : SConfig 6))
        = {state := some stE, head := false,
           left := ones 2 *> L, right := tenpow k' *> T} := by
      simp [sstep, tm, tenpow, ones]
    rw [hsstep, ih (ones 2 *> L)]
    congr 1
    show Side.prepend (ones (2*k')) (Side.prepend (ones 2) L)
       = Side.prepend (ones (2*(k'+1))) L
    rw [← Side.prepend_append, ones_append,
        show (2*k' + 2 : Nat) = 2*(k'+1) from by ring]

/-- **EA drain**: state E with head=`T`, draining `ones (2k)` from
left.  Each pair (E,1 + A,1) drains 2 ones, accumulates `[T, F]`
(= `tenpow 1`) on right. -/
private lemma EA_drain (k : Nat) (L R : Side) :
    srun tm
      ({state := some stE, head := true,
        left := ones (2*k) *> L, right := R} : SConfig 6) (2*k)
    = {state := some stE, head := true,
       left := L, right := tenpow k *> R} := by
  induction k generalizing R with
  | zero => simp [srun, tenpow]
  | succ k' ih =>
    show srun tm
      ({state := some stE, head := true,
        left := ones (2*(k'+1)) *> L, right := R} : SConfig 6) (2*(k'+1)) = _
    rw [show srun tm
          ({state := some stE, head := true,
            left := ones (2*(k'+1)) *> L, right := R} : SConfig 6) (2*(k'+1))
        = srun tm (sstep tm (sstep tm
          ({state := some stE, head := true,
            left := ones (2*(k'+1)) *> L, right := R} : SConfig 6))) (2*k') from rfl]
    have hsstep : sstep tm (sstep tm
        ({state := some stE, head := true,
          left := ones (2*(k'+1)) *> L, right := R} : SConfig 6))
        = {state := some stE, head := true,
           left := ones (2*k') *> L,
           right := Side.cons true (Side.cons false R)} := by
      simp [sstep, tm, ones,
            show (2*(k'+1) : Nat) = (2*k'+1) + 1 from by ring]
    rw [hsstep, ih (Side.cons true (Side.cons false R))]
    congr 1
    show Side.prepend (tenpow k') (Side.cons true (Side.cons false R))
       = Side.prepend (tenpow (k'+1)) R
    show Side.prepend (tenpow k') (Side.prepend [true, false] R)
       = Side.prepend (tenpow (k'+1)) R
    rw [← Side.prepend_append]
    congr 1
    show tenpow k' ++ [true, false] = tenpow (k'+1)
    rw [← tenpow_succ_append]

/-- Helper list identity: `[T] ++ zebra k = tenpow k ++ [T]`.
Both sides equal `[T, F, T, F, …, F, T]` of length `2k+1`. -/
private lemma cons_T_zebra (k : Nat) :
    true :: zebra k = tenpow k ++ [true] := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    show true :: false :: true :: zebra k' = true :: false :: tenpow k' ++ [true]
    rw [ih]; rfl

/-- **Phase A** of `IM_R_e_post_to_M`: 6i+2 steps to state A. -/
private lemma IM_R_e_phase_A (i m : Nat) :
    srun tm (IM_R_e_post i m) (6*i + 2)
    = ({state := some stA, head := true,
        left := ones (6*i + 2) *> blank∞,
        right := ones (m + 1) *> blank∞} : SConfig 6) := by
  match i with
  | 0 =>
    simp [IM_R_e_post, srun, sstep, tm, zeros, ones, tenpow,
          show (m + 3 : Nat) = m + 1 + 1 + 1 from by ring]
  | i' + 1 =>
    show srun tm (IM_R_e_post (i'+1) m) (6*(i'+1) + 2) = _
    rw [show (6*(i'+1) + 2 : Nat) = 1 + ((6*i'+5) + (1 + 1)) from by ring, srun_add]
    have h1 : srun tm (IM_R_e_post (i'+1) m) 1
        = ({state := some stD, head := false,
            left := ones 1 *> blank∞,
            right := zeros (6*i'+5) *> ones (m+3) *> blank∞} : SConfig 6) := by
      simp [IM_R_e_post, srun, sstep, tm, zeros, ones,
            show (6*(i'+1) : Nat) = (6*i'+5) + 1 from by ring]
    rw [h1, srun_add,
        D_zeros_shift (6*i'+5) (ones 1 *> blank∞) (ones (m+3) *> blank∞)]
    have hLcombine : Side.prepend (ones (6*i'+5)) (Side.prepend (ones 1) blank∞)
        = Side.prepend (ones (6*i'+6)) blank∞ := by
      rw [← Side.prepend_append, ones_append,
          show (6*i'+5 + 1 : Nat) = 6*i'+6 from by ring]
    rw [hLcombine, srun_add]
    have h2 : srun tm
        ({state := some stD, head := false,
          left := ones (6*i'+6) *> blank∞,
          right := ones (m+3) *> blank∞} : SConfig 6) 1
        = {state := some stD, head := true,
           left := ones (6*i'+7) *> blank∞,
           right := ones (m+2) *> blank∞} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+7 : Nat) = (6*i'+6) + 1 from by ring,
            show (m+3 : Nat) = (m+2) + 1 from by ring]
    rw [h2]
    have h3 : srun tm
        ({state := some stD, head := true,
          left := ones (6*i'+7) *> blank∞,
          right := ones (m+2) *> blank∞} : SConfig 6) 1
        = {state := some stA, head := true,
           left := ones (6*i'+8) *> blank∞,
           right := ones (m+1) *> blank∞} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+8 : Nat) = (6*i'+7) + 1 from by ring,
            show (m+2 : Nat) = (m+1) + 1 from by ring]
    rw [h3]
    -- Bridge: ones (6*i'+8) ↔ ones (1 + ((6*i'+5)+(1+1))) on RHS.
    simp [show (1 + ((6*i'+5)+(1+1)) : Nat) = 6*i'+8 from by ring]

/-- **Phase B** of `IM_R_e_post_to_M`: 6i+3 steps.  A_E_drain (3i+1)
followed by 1 A,1 fire on blank, building `tenpow (3i+1) *> ones (m+2)`
on right via `cons_T_zebra`. -/
private lemma IM_R_e_phase_B (i m : Nat) :
    srun tm
      ({state := some stA, head := true,
        left := ones (6*i + 2) *> blank∞,
        right := ones (m + 1) *> blank∞} : SConfig 6) (6*i + 3)
    = ({state := some stE, head := false,
        left := blank∞,
        right := tenpow (3*i + 1) *> ones (m + 2) *> blank∞} : SConfig 6) := by
  rw [show (6*i + 3 : Nat) = 2*(3*i + 1) + 1 from by ring, srun_add,
      show (6*i + 2 : Nat) = 2*(3*i + 1) from by ring,
      A_E_drain (3*i + 1) blank∞ (ones (m + 1) *> blank∞)]
  have h_step : sstep tm
      ({state := some stA, head := true, left := blank∞,
        right := zebra (3*i+1) *> ones (m+1) *> blank∞} : SConfig 6)
      = {state := some stE, head := false, left := blank∞,
         right := tenpow (3*i+1) *> ones (m+2) *> blank∞} := by
    simp [sstep, tm]
    show Side.cons true (Side.prepend (zebra (3*i+1)) (Side.prepend (ones (m+1)) blank∞))
       = Side.prepend (tenpow (3*i+1)) (Side.prepend (ones (m+2)) blank∞)
    show Side.prepend [true] (Side.prepend (zebra (3*i+1)) (Side.prepend (ones (m+1)) blank∞))
       = Side.prepend (tenpow (3*i+1)) (Side.prepend (ones (m+2)) blank∞)
    simp only [← Side.prepend_append]
    congr 1
    show true :: zebra (3*i+1) ++ ones (m+1) = tenpow (3*i+1) ++ ones (m+2)
    rw [cons_T_zebra, List.append_assoc]
    rfl
  show srun tm _ 1 = _
  rw [show srun tm
        ({state := some stA, head := true, left := blank∞,
          right := zebra (3*i+1) *> ones (m+1) *> blank∞} : SConfig 6) 1
      = sstep tm
        ({state := some stA, head := true, left := blank∞,
          right := zebra (3*i+1) *> ones (m+1) *> blank∞} : SConfig 6) from rfl]
  exact h_step

/-- **Phase C** of `IM_R_e_post_to_M`: 6i+4 steps.  EF_tenpow_walk on
`tenpow (3i+1)` (6i+2 steps) followed by 2 explicit trans walking
through 2 cells of `ones (m+2)`. -/
private lemma IM_R_e_phase_C (i m : Nat) :
    srun tm
      ({state := some stE, head := false,
        left := blank∞,
        right := tenpow (3*i + 1) *> ones (m + 2) *> blank∞} : SConfig 6) (6*i + 4)
    = ({state := some stE, head := true,
        left := ones (6*i + 4) *> blank∞,
        right := ones m *> blank∞} : SConfig 6) := by
  rw [show (6*i + 4 : Nat) = 2*(3*i + 1) + (1 + 1) from by ring, srun_add,
      EF_tenpow_walk (3*i + 1) blank∞ (ones (m + 2) *> blank∞)]
  rw [srun_add]
  have h1 : sstep tm
      ({state := some stE, head := false,
        left := ones (2*(3*i+1)) *> blank∞,
        right := ones (m+2) *> blank∞} : SConfig 6)
      = {state := some stF, head := true,
         left := ones (2*(3*i+1) + 1) *> blank∞,
         right := ones (m+1) *> blank∞} := by
    simp [sstep, tm, ones,
          show (m+2 : Nat) = (m+1) + 1 from by ring]
  rw [show srun tm
        ({state := some stE, head := false,
          left := ones (2*(3*i+1)) *> blank∞,
          right := ones (m+2) *> blank∞} : SConfig 6) 1
      = sstep tm
        ({state := some stE, head := false,
          left := ones (2*(3*i+1)) *> blank∞,
          right := ones (m+2) *> blank∞} : SConfig 6) from rfl, h1]
  have h2 : sstep tm
      ({state := some stF, head := true,
        left := ones (2*(3*i+1) + 1) *> blank∞,
        right := ones (m+1) *> blank∞} : SConfig 6)
      = {state := some stE, head := true,
         left := ones (2*(3*i+1) + 2) *> blank∞,
         right := ones m *> blank∞} := by
    simp [sstep, tm, ones,
          show (2*(3*i+1) + 2 : Nat) = (2*(3*i+1) + 1) + 1 from rfl,
          show (m+1 : Nat) = m + 1 from rfl]
  rw [show srun tm
        ({state := some stF, head := true,
          left := ones (2*(3*i+1) + 1) *> blank∞,
          right := ones (m+1) *> blank∞} : SConfig 6) 1
      = sstep tm
        ({state := some stF, head := true,
          left := ones (2*(3*i+1) + 1) *> blank∞,
          right := ones (m+1) *> blank∞} : SConfig 6) from rfl, h2]

/-- **Phase D** of `IM_R_e_post_to_M`: 6i+5 steps.  EA_drain (3i+2)
followed by 1 E,1 fire on blank. -/
private lemma IM_R_e_phase_D (i m : Nat) :
    srun tm
      ({state := some stE, head := true,
        left := ones (6*i + 4) *> blank∞,
        right := ones m *> blank∞} : SConfig 6) (6*i + 5)
    = ({state := some stA, head := false,
        left := blank∞,
        right := Side.cons false (tenpow (3*i + 2) *> ones m *> blank∞)} : SConfig 6) := by
  rw [show (6*i + 5 : Nat) = 2*(3*i + 2) + 1 from by ring, srun_add,
      show (6*i + 4 : Nat) = 2*(3*i + 2) from by ring,
      EA_drain (3*i + 2) blank∞ (ones m *> blank∞)]
  -- After EA_drain: srun tm {E, T, blank, tenpow (3i+2) *> ones m *> blank} 1 = RHS
  have h_step : sstep tm
      ({state := some stE, head := true, left := blank∞,
        right := tenpow (3*i+2) *> ones m *> blank∞} : SConfig 6)
      = {state := some stA, head := false, left := blank∞,
         right := Side.cons false (tenpow (3*i+2) *> ones m *> blank∞)} := by
    simp [sstep, tm]
  rw [show srun tm
        ({state := some stE, head := true, left := blank∞,
          right := tenpow (3*i+2) *> ones m *> blank∞} : SConfig 6) 1
      = sstep tm
        ({state := some stE, head := true, left := blank∞,
          right := tenpow (3*i+2) *> ones m *> blank∞} : SConfig 6) from rfl, h_step]

/-- **Phase Final** of `IM_R_e_post_to_M`: 3 steps (A,0 + B,0 + C,1)
producing `M (3i+3) m`. -/
private lemma IM_R_e_phase_Final (i m : Nat) :
    srun tm
      ({state := some stA, head := false,
        left := blank∞,
        right := Side.cons false (tenpow (3*i + 2) *> ones m *> blank∞)} : SConfig 6) 3
    = M (3*i + 3) m := by
  -- 3 trans: A,0 + B,0 + C,1.
  show srun tm _ 3 = _
  rw [show (3 : Nat) = 1 + (1 + 1) from rfl, srun_add]
  have h1 : sstep tm
      ({state := some stA, head := false, left := blank∞,
        right := Side.cons false (tenpow (3*i+2) *> ones m *> blank∞)} : SConfig 6)
      = {state := some stB, head := false, left := ones 1 *> blank∞,
         right := tenpow (3*i+2) *> ones m *> blank∞} := by
    simp [sstep, tm, ones]
  rw [show srun tm
        ({state := some stA, head := false, left := blank∞,
          right := Side.cons false (tenpow (3*i+2) *> ones m *> blank∞)} : SConfig 6) 1
      = sstep tm
        ({state := some stA, head := false, left := blank∞,
          right := Side.cons false (tenpow (3*i+2) *> ones m *> blank∞)} : SConfig 6) from rfl, h1]
  rw [srun_add]
  have h2 : sstep tm
      ({state := some stB, head := false, left := ones 1 *> blank∞,
        right := tenpow (3*i+2) *> ones m *> blank∞} : SConfig 6)
      = {state := some stC, head := true, left := blank∞,
         right := Side.cons false (tenpow (3*i+2) *> ones m *> blank∞)} := by
    simp [sstep, tm, ones]
  rw [show srun tm
        ({state := some stB, head := false, left := ones 1 *> blank∞,
          right := tenpow (3*i+2) *> ones m *> blank∞} : SConfig 6) 1
      = sstep tm
        ({state := some stB, head := false, left := ones 1 *> blank∞,
          right := tenpow (3*i+2) *> ones m *> blank∞} : SConfig 6) from rfl, h2]
  have h3 : sstep tm
      ({state := some stC, head := true, left := blank∞,
        right := Side.cons false (tenpow (3*i+2) *> ones m *> blank∞)} : SConfig 6)
      = {state := some stC, head := false, left := blank∞,
         right := tenpow (3*i + 3) *> ones m *> blank∞} := by
    simp [sstep, tm, tenpow]
  rw [show srun tm
        ({state := some stC, head := true, left := blank∞,
          right := Side.cons false (tenpow (3*i+2) *> ones m *> blank∞)} : SConfig 6) 1
      = sstep tm
        ({state := some stC, head := true, left := blank∞,
          right := Side.cons false (tenpow (3*i+2) *> ones m *> blank∞)} : SConfig 6) from rfl, h3]
  -- Final: result = M (3i+3) m
  show ({state := some stC, head := false, left := blank∞,
         right := tenpow (3*i+3) *> ones m *> blank∞} : SConfig 6) = M (3*i + 3) m
  simp [M]

/-- **Final-phase lemma**: `IM_R_e_post i m → M (3i + 3) m` in
`24i + 17` steps.  Composes Phases A, B, C, D, Final. -/
private lemma IM_R_e_post_to_M (i m : Nat) :
    srun tm (IM_R_e_post i m) (24*i + 17) = M (3*i + 3) m := by
  rw [show (24*i + 17 : Nat)
        = (6*i + 2) + ((6*i + 3) + ((6*i + 4) + ((6*i + 5) + 3))) from by ring,
      srun_add, IM_R_e_phase_A i m,
      srun_add, IM_R_e_phase_B i m,
      srun_add, IM_R_e_phase_C i m,
      srun_add, IM_R_e_phase_D i m,
      IM_R_e_phase_Final i m]

private lemma IM_R_e_chain_gen : ∀ (i j m : Nat),
    srun tm (IM_R_e i j m) (12*i*j + 6*j*j + 2*j + (24*(i+j) + 17))
    = M (3*(i+j) + 3) m := by
  intro i j m
  induction j generalizing i with
  | zero =>
    simp only [Nat.zero_mul, Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    rw [IM_R_e_post_eq]
    exact IM_R_e_post_to_M i m
  | succ j' ih =>
    rw [show (12*i*(j'+1) + 6*(j'+1)*(j'+1) + 2*(j'+1) + (24*(i+(j'+1)) + 17) : Nat)
          = (12*i + 8) + (12*(i+1)*j' + 6*j'*j' + 2*j' + (24*((i+1)+j') + 17)) from by ring,
        srun_add, IM_R_e_trans i j' m,
        show (3*(i+(j'+1)) + 3 : Nat) = 3*((i+1)+j') + 3 from by ring]
    exact ih (i+1)

/-- **Rule R_even** (`dt = 6j² + 26j + 17`).
Wiki: `A(2n, m+3) → A(3n, m)` for `n ≥ 3, m ≥ 0`.
With `j := n - 3`: `M (2j) (m+3) → M (3j+3) m` in `6j² + 26j + 17`
steps (independent of `m`).

Sanity check at `j = 0`: `M 0 (m+3) → M 3 m` in 17 steps. -/
theorem rule_R_even (j m : Nat) :
    srun tm (M (2*j) (m + 3)) (6*j*j + 26*j + 17) = M (3*j + 3) m := by
  rw [M_eq_IM_R_e j m]
  have h := IM_R_e_chain_gen 0 j m
  rw [show (12*0*j + 6*j*j + 2*j + (24*(0+j) + 17) : Nat) = 6*j*j + 26*j + 17 from by ring,
      show (3*(0+j) + 3 : Nat) = 3*j + 3 from by ring] at h
  exact h

-- ============================================================
-- Infrastructure for `rule_R_odd`: `IM_R_o` framework
-- ============================================================

/-- Intermediate config for `rule_R_odd`: state C, head on `0`, blank
left, right tape `(zeros 6i) *> tenpow (2j+1) *> ones (m+3) *> blank∞`.
Same shape as `IM_R_e` but with ODD `tenpow` exponent. -/
private def IM_R_o (i j m : Nat) : SConfig 6 :=
  { state := some stC,
    head := false,
    left := blank∞,
    right := zeros (6*i) *> tenpow (2*j + 1) *> ones (m + 3) *> blank∞ }

/-- Stage-A intermediate: state C with right `zeros (6i+5) *> ones (m+2) *> blank`.
Reached after `12i+8` steps from `IM_R_o i 0 m`. -/
private def IM_R_o_post (i m : Nat) : SConfig 6 :=
  { state := some stC,
    head := false,
    left := blank∞,
    right := zeros (6*i + 5) *> ones (m + 2) *> blank∞ }

private lemma M_eq_IM_R_o (j m : Nat) :
    M (2*j + 1) (m + 3) = IM_R_o 0 j m := by
  simp [M, IM_R_o, show (6*0 : Nat) = 0 from rfl]

/-- **Iteration**: `IM_R_o i (j+1) m → IM_R_o (i+1) j m` in `12i + 8`
steps.  Same proof structure as `IM_R_e_trans`, with `tenpow (2j+3)`
replaced by `tenpow (2j+3)` (still — the iteration reduces by 2). -/
private lemma IM_R_o_trans (i j m : Nat) :
    srun tm (IM_R_o i (j + 1) m) (12*i + 8) = IM_R_o (i + 1) j m := by
  match i with
  | 0 =>
    simp [IM_R_o, srun, sstep, tm, tenpow, ones, zeros]
  | i' + 1 =>
    show srun tm (IM_R_o (i'+1) (j+1) m) (12*(i'+1) + 8) = IM_R_o (i'+2) j m
    rw [show (12*(i'+1) + 8 : Nat)
          = 1 + ((6*i'+5) + (1 + (1 + (1 + ((6*i'+9) + (1 + 1)))))) from by ring]
    rw [srun_add]
    have hA : srun tm (IM_R_o (i'+1) (j+1) m) 1
        = ({state := some stD, head := false,
            left := ones 1 *> blank∞,
            right := zeros (6*i'+5) *> tenpow (2*j+3) *> ones (m+3) *> blank∞}
           : SConfig 6) := by
      simp [IM_R_o, srun, sstep, tm, zeros, ones,
            show (6*(i'+1) : Nat) = (6*i'+5) + 1 from by ring,
            show (2*(j+1) + 1 : Nat) = 2*j + 3 from by ring]
    rw [hA, srun_add,
        D_zeros_shift (6*i'+5) (ones 1 *> blank∞)
          (tenpow (2*j+3) *> ones (m+3) *> blank∞)]
    have hLcombine : Side.prepend (ones (6*i'+5)) (Side.prepend (ones 1) blank∞)
        = Side.prepend (ones (6*i'+6)) blank∞ := by
      rw [← Side.prepend_append, ones_append,
          show (6*i'+5 + 1 : Nat) = 6*i'+6 from by ring]
    rw [hLcombine, srun_add]
    have hC : srun tm
        ({state := some stD, head := false,
          left := ones (6*i'+6) *> blank∞,
          right := tenpow (2*j+3) *> ones (m+3) *> blank∞} : SConfig 6) 1
        = {state := some stD, head := true,
           left := ones (6*i'+7) *> blank∞,
           right := Side.cons false (tenpow (2*j+2) *> ones (m+3) *> blank∞)} := by
      simp [srun, sstep, tm, tenpow, ones,
            show (6*i'+7 : Nat) = (6*i'+6) + 1 from by ring]
    rw [hC, srun_add]
    have hD : srun tm
        ({state := some stD, head := true,
          left := ones (6*i'+7) *> blank∞,
          right := Side.cons false (tenpow (2*j+2) *> ones (m+3) *> blank∞)}
          : SConfig 6) 1
        = {state := some stA, head := false,
           left := ones (6*i'+8) *> blank∞,
           right := tenpow (2*j+2) *> ones (m+3) *> blank∞} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+8 : Nat) = (6*i'+7) + 1 from by ring]
    rw [hD, srun_add]
    have hE : srun tm
        ({state := some stA, head := false,
          left := ones (6*i'+8) *> blank∞,
          right := tenpow (2*j+2) *> ones (m+3) *> blank∞} : SConfig 6) 1
        = {state := some stB, head := true,
           left := ones (6*i'+9) *> blank∞,
           right := Side.cons false (tenpow (2*j+1) *> ones (m+3) *> blank∞)} := by
      simp [srun, sstep, tm, tenpow, ones,
            show (6*i'+9 : Nat) = (6*i'+8) + 1 from by ring]
    rw [hE, srun_add,
        B_drain_ones_shift (6*i'+9)
          (Side.cons false (tenpow (2*j+1) *> ones (m+3) *> blank∞)),
        srun_add]
    have hG : srun tm
        ({state := some stB, head := true,
          left := blank∞,
          right := zeros (6*i'+9) *>
            Side.cons false (tenpow (2*j+1) *> ones (m+3) *> blank∞)} : SConfig 6) 1
        = {state := some stB, head := false,
           left := blank∞,
           right := zeros (6*i'+10) *>
             Side.cons false (tenpow (2*j+1) *> ones (m+3) *> blank∞)} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+10 : Nat) = (6*i'+9) + 1 from by ring,
            show zeros ((6*i'+9) + 1) = zeros 1 ++ zeros (6*i'+9) from by
              rw [Nat.add_comm, ← zeros_append]]
    rw [hG]
    have hH : srun tm
        ({state := some stB, head := false,
          left := blank∞,
          right := zeros (6*i'+10) *>
            Side.cons false (tenpow (2*j+1) *> ones (m+3) *> blank∞)} : SConfig 6) 1
        = {state := some stC, head := false,
           left := blank∞,
           right := zeros (6*i'+11) *>
             Side.cons false (tenpow (2*j+1) *> ones (m+3) *> blank∞)} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+11 : Nat) = (6*i'+10) + 1 from by ring,
            show zeros ((6*i'+10) + 1) = zeros 1 ++ zeros (6*i'+10) from by
              rw [Nat.add_comm, ← zeros_append]]
    rw [hH]
    show ({state := some stC, head := false,
           left := blank∞,
           right := zeros (6*i'+11) *>
             Side.cons false (tenpow (2*j+1) *> ones (m+3) *> blank∞)} : SConfig 6)
       = IM_R_o (i'+2) j m
    simp [IM_R_o, show (6*(i'+2) : Nat) = 6*i'+12 from by ring]
    show Side.prepend (zeros (6*i'+11))
            (Side.cons false (Side.prepend (tenpow (2*j+1))
              (Side.prepend (ones (m+3)) blank∞)))
       = Side.prepend (zeros (6*i'+12))
           (Side.prepend (tenpow (2*j+1))
             (Side.prepend (ones (m+3)) blank∞))
    show Side.prepend (zeros (6*i'+11))
            (Side.prepend [false] (Side.prepend (tenpow (2*j+1))
              (Side.prepend (ones (m+3)) blank∞)))
       = Side.prepend (zeros (6*i'+12))
           (Side.prepend (tenpow (2*j+1))
             (Side.prepend (ones (m+3)) blank∞))
    rw [← Side.prepend_append]
    congr 1
    show zeros (6*i'+11) ++ zeros 1 = zeros (6*i'+12)
    rw [zeros_append]

/-- **Stage A**: `IM_R_o i 0 m → IM_R_o_post i m` in `12i + 8` steps.
Phases: C-fire + D-zeros-shift through `6i` zeros + D,1 fire entering
`tenpow 1`'s T + A,0 fire + B,1 drain + B,0 → C. -/
private lemma IM_R_o_to_post (i m : Nat) :
    srun tm (IM_R_o i 0 m) (12*i + 8) = IM_R_o_post i m := by
  match i with
  | 0 =>
    simp [IM_R_o, IM_R_o_post, srun, sstep, tm, tenpow, ones, zeros]
  | i' + 1 =>
    show srun tm (IM_R_o (i'+1) 0 m) (12*(i'+1) + 8) = IM_R_o_post (i'+1) m
    rw [show (12*(i'+1) + 8 : Nat)
          = 1 + ((6*i'+5) + (1 + (1 + (1 + ((6*i'+9) + (1 + 1)))))) from by ring]
    rw [srun_add]
    have hA : srun tm (IM_R_o (i'+1) 0 m) 1
        = ({state := some stD, head := false,
            left := ones 1 *> blank∞,
            right := zeros (6*i'+5) *> tenpow 1 *> ones (m+3) *> blank∞}
           : SConfig 6) := by
      simp [IM_R_o, srun, sstep, tm, zeros, ones,
            show (6*(i'+1) : Nat) = (6*i'+5) + 1 from by ring]
    rw [hA, srun_add,
        D_zeros_shift (6*i'+5) (ones 1 *> blank∞)
          (tenpow 1 *> ones (m+3) *> blank∞)]
    have hLcombine : Side.prepend (ones (6*i'+5)) (Side.prepend (ones 1) blank∞)
        = Side.prepend (ones (6*i'+6)) blank∞ := by
      rw [← Side.prepend_append, ones_append,
          show (6*i'+5 + 1 : Nat) = 6*i'+6 from by ring]
    rw [hLcombine, srun_add]
    have hC : srun tm
        ({state := some stD, head := false,
          left := ones (6*i'+6) *> blank∞,
          right := tenpow 1 *> ones (m+3) *> blank∞} : SConfig 6) 1
        = {state := some stD, head := true,
           left := ones (6*i'+7) *> blank∞,
           right := Side.cons false (ones (m+3) *> blank∞)} := by
      simp [srun, sstep, tm, tenpow, ones,
            show (6*i'+7 : Nat) = (6*i'+6) + 1 from by ring]
    rw [hC, srun_add]
    have hD : srun tm
        ({state := some stD, head := true,
          left := ones (6*i'+7) *> blank∞,
          right := Side.cons false (ones (m+3) *> blank∞)} : SConfig 6) 1
        = {state := some stA, head := false,
           left := ones (6*i'+8) *> blank∞,
           right := ones (m+3) *> blank∞} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+8 : Nat) = (6*i'+7) + 1 from by ring]
    rw [hD, srun_add]
    have hE : srun tm
        ({state := some stA, head := false,
          left := ones (6*i'+8) *> blank∞,
          right := ones (m+3) *> blank∞} : SConfig 6) 1
        = {state := some stB, head := true,
           left := ones (6*i'+9) *> blank∞,
           right := ones (m+2) *> blank∞} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+9 : Nat) = (6*i'+8) + 1 from by ring,
            show (m+3 : Nat) = (m+2) + 1 from by ring]
    rw [hE, srun_add,
        B_drain_ones_shift (6*i'+9) (ones (m+2) *> blank∞), srun_add]
    have hG : srun tm
        ({state := some stB, head := true, left := blank∞,
          right := zeros (6*i'+9) *> ones (m+2) *> blank∞} : SConfig 6) 1
        = {state := some stB, head := false, left := blank∞,
           right := zeros (6*i'+10) *> ones (m+2) *> blank∞} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+10 : Nat) = (6*i'+9) + 1 from by ring,
            show zeros ((6*i'+9) + 1) = zeros 1 ++ zeros (6*i'+9) from by
              rw [Nat.add_comm, ← zeros_append]]
    rw [hG]
    have hH : srun tm
        ({state := some stB, head := false, left := blank∞,
          right := zeros (6*i'+10) *> ones (m+2) *> blank∞} : SConfig 6) 1
        = {state := some stC, head := false, left := blank∞,
           right := zeros (6*i'+11) *> ones (m+2) *> blank∞} := by
      simp [srun, sstep, tm, ones,
            show (6*i'+11 : Nat) = (6*i'+10) + 1 from by ring,
            show zeros ((6*i'+10) + 1) = zeros 1 ++ zeros (6*i'+10) from by
              rw [Nat.add_comm, ← zeros_append]]
    rw [hH]
    show ({state := some stC, head := false, left := blank∞,
           right := zeros (6*i'+11) *> ones (m+2) *> blank∞} : SConfig 6)
       = IM_R_o_post (i'+1) m
    simp [IM_R_o_post, show (6*(i'+1) + 5 : Nat) = 6*i'+11 from by ring]

/-- **Stage B Phase 1** of `IM_R_o_post_to_M`: 6i+7 steps, ending at
state A with `ones (6i+7)` left, `ones m *> blank` right. -/
private lemma IM_R_o_phase_B1 (i m : Nat) :
    srun tm (IM_R_o_post i m) (6*i + 7)
    = ({state := some stA, head := true,
        left := ones (6*i + 7) *> blank∞,
        right := ones m *> blank∞} : SConfig 6) := by
  show srun tm (IM_R_o_post i m) (6*i + 7) = _
  rw [show (6*i + 7 : Nat) = 1 + ((6*i + 4) + (1 + 1)) from by ring, srun_add]
  have hA : srun tm (IM_R_o_post i m) 1
      = ({state := some stD, head := false,
          left := ones 1 *> blank∞,
          right := zeros (6*i + 4) *> ones (m+2) *> blank∞} : SConfig 6) := by
    simp [IM_R_o_post, srun, sstep, tm, zeros, ones,
          show (6*i + 5 : Nat) = (6*i + 4) + 1 from by ring]
  rw [hA, srun_add,
      D_zeros_shift (6*i + 4) (ones 1 *> blank∞) (ones (m+2) *> blank∞)]
  have hLcombine : Side.prepend (ones (6*i + 4)) (Side.prepend (ones 1) blank∞)
      = Side.prepend (ones (6*i + 5)) blank∞ := by
    rw [← Side.prepend_append, ones_append,
        show (6*i + 4 + 1 : Nat) = 6*i + 5 from by ring]
  rw [hLcombine, srun_add]
  have h2 : srun tm
      ({state := some stD, head := false,
        left := ones (6*i + 5) *> blank∞,
        right := ones (m+2) *> blank∞} : SConfig 6) 1
      = {state := some stD, head := true,
         left := ones (6*i + 6) *> blank∞,
         right := ones (m+1) *> blank∞} := by
    simp [srun, sstep, tm, ones,
          show (6*i + 6 : Nat) = (6*i + 5) + 1 from by ring,
          show (m+2 : Nat) = (m+1) + 1 from by ring]
  rw [h2]
  have h3 : srun tm
      ({state := some stD, head := true,
        left := ones (6*i + 6) *> blank∞,
        right := ones (m+1) *> blank∞} : SConfig 6) 1
      = {state := some stA, head := true,
         left := ones (6*i + 7) *> blank∞,
         right := ones m *> blank∞} := by
    simp [srun, sstep, tm, ones,
          show (6*i + 7 : Nat) = (6*i + 6) + 1 from by ring,
          show (m+1 : Nat) = m + 1 from by ring]
  rw [h3]
  simp [show (1 + (6*i + 4 + (1 + 1)) : Nat) = 6*i + 7 from by ring]

/-- **Stage B Phase 2** of `IM_R_o_post_to_M`: 6i+8 steps drain via
A↔E to state A head=F.  Builds `tenpow (3i+3) ++ ones (m+1)` on right,
then prepends `[F]` via final E,1 fire. -/
private lemma IM_R_o_phase_B2 (i m : Nat) :
    srun tm
      ({state := some stA, head := true,
        left := ones (6*i + 7) *> blank∞,
        right := ones m *> blank∞} : SConfig 6) (6*i + 8)
    = ({state := some stA, head := false,
        left := blank∞,
        right := Side.cons false (tenpow (3*i + 3) *> ones (m + 1) *> blank∞)}
       : SConfig 6) := by
  rw [show (6*i + 8 : Nat) = 2*(3*i + 3) + 2 from by ring,
      show (6*i + 7 : Nat) = 2*(3*i + 3) + 1 from by ring]
  -- Split ones (2*(3i+3) + 1) = ones (2*(3i+3)) ++ ones 1.
  have hsplit : Side.prepend (ones (2*(3*i + 3) + 1)) blank∞
      = Side.prepend (ones (2*(3*i + 3))) (Side.prepend (ones 1) blank∞) := by
    rw [← Side.prepend_append, ones_append]
  rw [hsplit, srun_add,
      A_E_drain (3*i + 3) (ones 1 *> blank∞) (ones m *> blank∞)]
  -- Now: srun tm {A, T, ones 1, zebra (3i+3) *> ones m *> blank} 2 = ...
  rw [show (2 : Nat) = 1 + 1 from rfl, srun_add]
  have h1 : sstep tm
      ({state := some stA, head := true,
        left := ones 1 *> blank∞,
        right := zebra (3*i+3) *> ones m *> blank∞} : SConfig 6)
      = {state := some stE, head := true,
         left := blank∞,
         right := Side.cons true (zebra (3*i+3) *> ones m *> blank∞)} := by
    simp [sstep, tm, ones]
  rw [show srun tm
        ({state := some stA, head := true,
          left := ones 1 *> blank∞,
          right := zebra (3*i+3) *> ones m *> blank∞} : SConfig 6) 1
      = sstep tm
        ({state := some stA, head := true,
          left := ones 1 *> blank∞,
          right := zebra (3*i+3) *> ones m *> blank∞} : SConfig 6) from rfl, h1]
  have h2 : sstep tm
      ({state := some stE, head := true,
        left := blank∞,
        right := Side.cons true (zebra (3*i+3) *> ones m *> blank∞)} : SConfig 6)
      = {state := some stA, head := false,
         left := blank∞,
         right := Side.cons false (Side.cons true (zebra (3*i+3) *> ones m *> blank∞))} := by
    simp [sstep, tm]
  rw [show srun tm
        ({state := some stE, head := true,
          left := blank∞,
          right := Side.cons true (zebra (3*i+3) *> ones m *> blank∞)} : SConfig 6) 1
      = sstep tm
        ({state := some stE, head := true,
          left := blank∞,
          right := Side.cons true (zebra (3*i+3) *> ones m *> blank∞)} : SConfig 6) from rfl, h2]
  -- Bridge: cons F (cons T (zebra (3i+3) *> ones m *> blank))
  --       = cons F (tenpow (3i+3) *> ones (m+1) *> blank).
  congr 1
  show Side.cons false (Side.cons true (Side.prepend (zebra (3*i+3)) (Side.prepend (ones m) blank∞)))
     = Side.cons false (Side.prepend (tenpow (3*i+3)) (Side.prepend (ones (m+1)) blank∞))
  congr 1
  show Side.cons true (Side.prepend (zebra (3*i+3)) (Side.prepend (ones m) blank∞))
     = Side.prepend (tenpow (3*i+3)) (Side.prepend (ones (m+1)) blank∞)
  show Side.prepend [true] (Side.prepend (zebra (3*i+3)) (Side.prepend (ones m) blank∞))
     = Side.prepend (tenpow (3*i+3)) (Side.prepend (ones (m+1)) blank∞)
  simp only [← Side.prepend_append]
  congr 1
  show true :: zebra (3*i+3) ++ ones m = tenpow (3*i+3) ++ ones (m+1)
  rw [cons_T_zebra, List.append_assoc]
  rfl

/-- **Stage B Phase 3** of `IM_R_o_post_to_M`: 3 steps (A,0 + B,0 + C,1)
producing `M (3i+4) (m+1)`. -/
private lemma IM_R_o_phase_B3 (i m : Nat) :
    srun tm
      ({state := some stA, head := false,
        left := blank∞,
        right := Side.cons false (tenpow (3*i + 3) *> ones (m + 1) *> blank∞)}
       : SConfig 6) 3
    = M (3*i + 4) (m + 1) := by
  rw [show (3 : Nat) = 1 + (1 + 1) from rfl, srun_add]
  have h1 : sstep tm
      ({state := some stA, head := false, left := blank∞,
        right := Side.cons false (tenpow (3*i+3) *> ones (m+1) *> blank∞)} : SConfig 6)
      = {state := some stB, head := false, left := ones 1 *> blank∞,
         right := tenpow (3*i+3) *> ones (m+1) *> blank∞} := by
    simp [sstep, tm, ones]
  rw [show srun tm
        ({state := some stA, head := false, left := blank∞,
          right := Side.cons false (tenpow (3*i+3) *> ones (m+1) *> blank∞)} : SConfig 6) 1
      = sstep tm
        ({state := some stA, head := false, left := blank∞,
          right := Side.cons false (tenpow (3*i+3) *> ones (m+1) *> blank∞)} : SConfig 6) from rfl, h1]
  rw [srun_add]
  have h2 : sstep tm
      ({state := some stB, head := false, left := ones 1 *> blank∞,
        right := tenpow (3*i+3) *> ones (m+1) *> blank∞} : SConfig 6)
      = {state := some stC, head := true, left := blank∞,
         right := Side.cons false (tenpow (3*i+3) *> ones (m+1) *> blank∞)} := by
    simp [sstep, tm, ones]
  rw [show srun tm
        ({state := some stB, head := false, left := ones 1 *> blank∞,
          right := tenpow (3*i+3) *> ones (m+1) *> blank∞} : SConfig 6) 1
      = sstep tm
        ({state := some stB, head := false, left := ones 1 *> blank∞,
          right := tenpow (3*i+3) *> ones (m+1) *> blank∞} : SConfig 6) from rfl, h2]
  have h3 : sstep tm
      ({state := some stC, head := true, left := blank∞,
        right := Side.cons false (tenpow (3*i+3) *> ones (m+1) *> blank∞)} : SConfig 6)
      = {state := some stC, head := false, left := blank∞,
         right := tenpow (3*i + 4) *> ones (m + 1) *> blank∞} := by
    simp [sstep, tm, tenpow]
  rw [show srun tm
        ({state := some stC, head := true, left := blank∞,
          right := Side.cons false (tenpow (3*i+3) *> ones (m+1) *> blank∞)} : SConfig 6) 1
      = sstep tm
        ({state := some stC, head := true, left := blank∞,
          right := Side.cons false (tenpow (3*i+3) *> ones (m+1) *> blank∞)} : SConfig 6) from rfl, h3]
  show ({state := some stC, head := false, left := blank∞,
         right := tenpow (3*i+4) *> ones (m+1) *> blank∞} : SConfig 6)
     = M (3*i + 4) (m + 1)
  simp [M]

/-- **Stage B**: `IM_R_o_post i m → M (3i + 4) (m + 1)` in `12i + 18`
steps.  Composes Phases B1, B2, B3. -/
private lemma IM_R_o_post_to_M (i m : Nat) :
    srun tm (IM_R_o_post i m) (12*i + 18) = M (3*i + 4) (m + 1) := by
  rw [show (12*i + 18 : Nat) = (6*i + 7) + ((6*i + 8) + 3) from by ring,
      srun_add, IM_R_o_phase_B1 i m,
      srun_add, IM_R_o_phase_B2 i m,
      IM_R_o_phase_B3 i m]

/-- **Final phase** of `rule_R_odd`: `IM_R_o i 0 m → M (3i+4) (m+1)`
in `24i + 26` steps.  Stage A + Stage B. -/
private lemma IM_R_o_final (i m : Nat) :
    srun tm (IM_R_o i 0 m) (24*i + 26) = M (3*i + 4) (m + 1) := by
  rw [show (24*i + 26 : Nat) = (12*i + 8) + (12*i + 18) from by ring,
      srun_add, IM_R_o_to_post i m, IM_R_o_post_to_M i m]

/-- Chain: `IM_R_o i j m → M (3*(i+j)+4) (m+1)` in
`12·i·j + 6j² + 2j + 24*(i+j) + 26` steps. -/
private lemma IM_R_o_chain_gen : ∀ (i j m : Nat),
    srun tm (IM_R_o i j m) (12*i*j + 6*j*j + 2*j + (24*(i+j) + 26))
    = M (3*(i+j) + 4) (m + 1) := by
  intro i j m
  induction j generalizing i with
  | zero =>
    simp only [Nat.zero_mul, Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    exact IM_R_o_final i m
  | succ j' ih =>
    rw [show (12*i*(j'+1) + 6*(j'+1)*(j'+1) + 2*(j'+1) + (24*(i+(j'+1)) + 26) : Nat)
          = (12*i + 8) + (12*(i+1)*j' + 6*j'*j' + 2*j' + (24*((i+1)+j') + 26)) from by ring,
        srun_add, IM_R_o_trans i j' m,
        show (3*(i+(j'+1)) + 4 : Nat) = 3*((i+1)+j') + 4 from by ring]
    exact ih (i+1)

/-- **Rule R_odd** (`dt = 6j² + 26j + 26`).
Wiki: `A(2n+1, m+3) → A(3n+1, m+1)` for `n ≥ 3, m ≥ 0`.
With `j := n - 3`: `M (2j+1) (m+3) → M (3j+4) (m+1)` in
`6j² + 26j + 26` steps (independent of `m`). -/
theorem rule_R_odd (j m : Nat) :
    srun tm (M (2*j + 1) (m + 3)) (6*j*j + 26*j + 26) = M (3*j + 4) (m + 1) := by
  rw [M_eq_IM_R_o j m]
  have h := IM_R_o_chain_gen 0 j m
  rw [show (12*0*j + 6*j*j + 2*j + (24*(0+j) + 26) : Nat) = 6*j*j + 26*j + 26 from by ring,
      show (3*(0+j) + 4 : Nat) = 3*j + 4 from by ring] at h
  exact h

-- ============================================================
-- Initial configuration
-- ============================================================

/-- From the blank tape, in 3 steps we reach `A(7, 0) = M 1 0` (state C,
head on the blank just left of a single `1`).

Trace:
```
  step 0: state A, blank        -> A,0→1RB
  step 1: state B, on blank R   -> B,0→0LC
  step 2: state C, on `1` (just written) -> C,1→1LC
  step 3: state C, on blank L of `1`     ← this is M 1 0 = A(7, 0).
```
-/
private def Init_Config_M_1_0 : Config 6 :=
  { state := some stC, head := false, left := [], right := [true, false] }

private lemma init_to_Init_Config_M_1_0 :
    run tm (initConfig 6) 3 = Init_Config_M_1_0 := by decide

private lemma Init_Config_M_1_0_toSConfig :
    Init_Config_M_1_0.toSConfig = M 1 0 := by
  simp [Init_Config_M_1_0, M, Config.toSConfig, tenpow]

theorem init_to_A_7_0 :
    srun tm (sinitConfig 6) 3 = M 1 0 := by
  have h := congrArg Config.toSConfig init_to_Init_Config_M_1_0
  rw [toSConfig_run, toSConfig_initConfig, Init_Config_M_1_0_toSConfig] at h
  exact h

/-- Composition: from blank tape, in 10 steps we reach the wiki's
starting macro config `A(6, 3) = M 0 3`.  Combines `init_to_A_7_0` with
`rule_R_odd_0` at `j = 0` (7 more steps). -/
private def Init_Config_M_0_3 : Config 6 :=
  { state := some stC, head := false, left := [], right := [true, true, true, false] }

private lemma init_to_Init_Config_M_0_3 :
    run tm (initConfig 6) 10 = Init_Config_M_0_3 := by decide

private lemma Init_Config_M_0_3_toSConfig :
    Init_Config_M_0_3.toSConfig = M 0 3 := by
  simp [Init_Config_M_0_3, M, Config.toSConfig, tenpow]

theorem init_to_A_6_3 :
    srun tm (sinitConfig 6) 10 = M 0 3 := by
  have h := congrArg Config.toSConfig init_to_Init_Config_M_0_3
  rw [toSConfig_run, toSConfig_initConfig, Init_Config_M_0_3_toSConfig] at h
  exact h

-- ============================================================
-- Halting equivalence: TM halt ↔ math model halt
-- ============================================================

/-- Mathematical state: `⟨n, m⟩` represents the macro config `M n m`,
which is the wiki's `A(n+6, m)`. -/
structure MathState where
  n : Nat
  m : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Embed a `MathState` as the corresponding `SConfig`. -/
def MathState.toSConfig (s : MathState) : SConfig 6 := M s.n s.m

/-- One math step encoding all macro rules.

The `m = 1` case is INLINED via `M_collapse` (`A(N,1) = A(N+1,0)`)
followed by the matching `m = 0` rule, producing a single `>0`-step
TM simulation rather than a 0-step renaming.

* `m = 2 ∧ n` even: **R_even_2** (halt) — `nextMathState = none`.
* `m = 1 ∧ n` even (so `n+1` odd): M_collapse + R_odd_0
  → `⟨0, 6·(n/2)+3⟩`.
* `m = 1 ∧ n` odd (so `n+1` even ≥ 2): M_collapse + R_even_0
  → `⟨0, 0⟩`.
* `m = 0 ∧ n` even: R_even_0 → `⟨0, 0⟩` (or self-loop for `⟨0,0⟩`).
* `m = 0 ∧ n` odd: R_odd_0 → `⟨0, 6·((n-1)/2)+3⟩`.
* `m = 2 ∧ n` odd: **R_odd_2** → `⟨0, 6·((n-1)/2)+8⟩`.
* `m ≥ 3, n` even: **R_even** → `⟨3·(n/2)+3, m-3⟩`.
* `m ≥ 3, n` odd: **R_odd** → `⟨3·((n-1)/2)+4, m-2⟩`. -/
def nextMathState : MathState → Option MathState
  | ⟨n, m⟩ =>
    if m = 2 ∧ n % 2 = 0 then none
    else if m = 1 ∧ n % 2 = 0 then some ⟨0, 6 * (n / 2) + 3⟩
    else if m = 1 then some ⟨0, 0⟩
    else if m = 0 ∧ n % 2 = 0 then some ⟨0, 0⟩
    else if m = 0 then some ⟨0, 6 * ((n - 1) / 2) + 3⟩
    else if m = 2 then some ⟨0, 6 * ((n - 1) / 2) + 8⟩
    else if n % 2 = 0 then some ⟨3 * (n / 2) + 3, m - 3⟩
    else some ⟨3 * ((n - 1) / 2) + 4, m - 2⟩

/-- Inductive halting predicate on `MathState`. -/
inductive mathHalts : MathState → Prop where
  | haltStep (s : MathState) (h : nextMathState s = none) : mathHalts s
  | nextStep (s s' : MathState) (h : nextMathState s = some s')
      (h' : mathHalts s') : mathHalts s

/-- The TM never halts from `M 0 0` (translated cycler).  After 1 step
the head enters state D and stays there with `head = false`,
advancing right indefinitely while writing `1`s. -/
private lemma srun_M_0_0_state_D (k : Nat) :
    srun tm (M 0 0) (k + 1)
    = ({state := some stD, head := false,
        left := ones (k + 1) *> blank∞, right := blank∞} : SConfig 6) := by
  induction k with
  | zero => simp [M, srun, sstep, tm, tenpow, ones]
  | succ k' ih =>
    show srun tm (M 0 0) ((k' + 1) + 1) = _
    rw [show ((k' + 1) + 1 : Nat) = (k' + 1) + 1 from rfl, srun_add, ih]
    simp [srun, sstep, tm, ones,
          show (k' + 1 + 1 : Nat) = (k' + 1) + 1 from rfl]

lemma M_0_0_nonhalt : ∀ k, (srun tm (M 0 0) k).state ≠ none := by
  intro k
  match k with
  | 0 => simp [M]
  | k' + 1 => rw [srun_M_0_0_state_D k']; simp

/-- Simulation of one macro rule (when math step is `none` = halt).
The only halt case is `m = 2 ∧ n` even, handled by `rule_R_even_2`. -/
theorem tm_sim_halt (s : MathState) (h : nextMathState s = none) :
    ∃ k, k > 0 ∧ (srun tm s.toSConfig k).state = none := by
  rcases s with ⟨n, m⟩
  -- nextMathState = none iff m = 2 ∧ n even.
  by_cases hcase : m = 2 ∧ n % 2 = 0
  · obtain ⟨hm, hn⟩ := hcase
    obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j := ⟨n / 2, by omega⟩
    subst hm
    refine ⟨6*j*j + 20*j + 11, by positivity, ?_⟩
    show (srun tm (M (2*j) 2) (6*j*j + 20*j + 11)).state = none
    exact rule_R_even_2 j
  · -- nextMathState ⟨n, m⟩ never returns none unless m=2 ∧ n even.
    exfalso
    unfold nextMathState at h
    simp [hcase] at h
    split_ifs at h

/-- Simulation of one macro rule (when math step is `some s'`).
Excludes the `⟨0, 0⟩ → ⟨0, 0⟩` self-loop (translated cycler).
The case-split mirrors the structure of `nextMathState`; for each
non-trivial branch the corresponding `rule_R_*` lemma supplies the
TM simulation.  The `m = 1` branches additionally invoke `M_collapse`
to bridge `M n 1 = M (n+1) 0`. -/
theorem tm_sim_step (s s' : MathState)
    (h : nextMathState s = some s') (h0 : s ≠ ⟨0, 0⟩) :
    ∃ k, k > 0 ∧ srun tm s.toSConfig k = s'.toSConfig := by
  rcases s with ⟨n, m⟩
  rcases s' with ⟨n', m'⟩
  unfold nextMathState at h
  -- Case 1: halt branch (m = 2 ∧ n even). Doesn't yield `some`.
  by_cases hH : m = 2 ∧ n % 2 = 0
  · simp [hH] at h
  simp [hH] at h
  -- Case 2: m = 1 ∧ n even. M_collapse + R_odd_0.
  by_cases hm1even : m = 1 ∧ n % 2 = 0
  · obtain ⟨hm1, hn_even⟩ := hm1even
    subst hm1
    simp [hn_even] at h
    obtain ⟨rfl, rfl⟩ := h
    show ∃ k, k > 0 ∧ srun tm (M n 1) k = M 0 (6 * (n / 2) + 3)
    -- M n 1 = M (n+1) 0 via M_collapse, then R_odd_0 with j = n/2.
    obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j := ⟨n / 2, by omega⟩
    refine ⟨6*j*j + 14*j + 7, by positivity, ?_⟩
    rw [M_collapse (2*j),
        show (2*j + 1 : Nat) = 2*j + 1 from rfl,
        show ((2*j) / 2 : Nat) = j from by omega]
    exact rule_R_odd_0 j
  simp [hm1even] at h
  -- Case 3: m = 1 ∧ n odd. M_collapse + R_even_0.
  by_cases hm1odd : m = 1
  · subst hm1odd
    have hn_odd : ¬ n % 2 = 0 := by
      intro hh; exact hm1even ⟨rfl, hh⟩
    simp [hn_odd] at h
    obtain ⟨rfl, rfl⟩ := h
    show ∃ k, k > 0 ∧ srun tm (M n 1) k = M 0 0
    -- M n 1 = M (n+1) 0 via M_collapse. n odd ⇒ n+1 = 2j+2 with j = (n-1)/2.
    obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 1 := ⟨(n - 1) / 2, by omega⟩
    refine ⟨6*j*j + 14*j + 8, by positivity, ?_⟩
    rw [M_collapse (2*j + 1),
        show (2*j + 1 + 1 : Nat) = 2*j + 2 from by ring]
    exact rule_R_even_0 j
  simp [hm1odd] at h
  -- Case 4: m = 0 ∧ n even. R_even_0 (or self-loop).
  by_cases hm0even : m = 0 ∧ n % 2 = 0
  · obtain ⟨hm0, hn_even⟩ := hm0even
    subst hm0
    simp [hn_even] at h
    obtain ⟨rfl, rfl⟩ := h
    show ∃ k, k > 0 ∧ srun tm (M n 0) k = M 0 0
    -- n is even and not 0 (since s ≠ ⟨0, 0⟩).
    have hn_pos : n ≥ 2 := by
      by_contra hlt
      push_neg at hlt
      have : n = 0 := by omega
      apply h0; subst this; rfl
    obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 2 := ⟨(n - 2) / 2, by omega⟩
    refine ⟨6*j*j + 14*j + 8, by positivity, ?_⟩
    exact rule_R_even_0 j
  simp [hm0even] at h
  -- Case 5: m = 0 ∧ n odd. R_odd_0.
  by_cases hm0odd : m = 0
  · subst hm0odd
    have hn_odd : ¬ n % 2 = 0 := by
      intro hh; exact hm0even ⟨rfl, hh⟩
    simp [hn_odd] at h
    obtain ⟨rfl, rfl⟩ := h
    show ∃ k, k > 0 ∧ srun tm (M n 0) k = M 0 (6 * ((n - 1) / 2) + 3)
    obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 1 := ⟨(n - 1) / 2, by omega⟩
    refine ⟨6*j*j + 14*j + 7, by positivity, ?_⟩
    rw [show ((2*j + 1 - 1) / 2 : Nat) = j from by omega]
    exact rule_R_odd_0 j
  simp [hm0odd] at h
  -- Case 6: m = 2 ∧ n odd. R_odd_2.
  by_cases hm2 : m = 2
  · subst hm2
    have hn_odd : ¬ n % 2 = 0 := by
      intro hh; exact hH ⟨rfl, hh⟩
    simp [hn_odd] at h
    obtain ⟨rfl, rfl⟩ := h
    show ∃ k, k > 0 ∧ srun tm (M n 2) k = M 0 (6 * ((n - 1) / 2) + 8)
    obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 1 := ⟨(n - 1) / 2, by omega⟩
    refine ⟨6*j*j + 26*j + 25, by positivity, ?_⟩
    rw [show ((2*j + 1 - 1) / 2 : Nat) = j from by omega]
    exact rule_R_odd_2 j
  simp [hm2] at h
  -- m ≥ 3.
  have hm_ge : m ≥ 3 := by omega
  by_cases h_neven : n % 2 = 0
  · -- Case 7: m ≥ 3, n even. R_even.
    simp [h_neven] at h
    obtain ⟨rfl, rfl⟩ := h
    show ∃ k, k > 0 ∧ srun tm (M n m) k = M (3 * (n / 2) + 3) (m - 3)
    obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j := ⟨n / 2, by omega⟩
    obtain ⟨m'', rfl⟩ : ∃ m'', m = m'' + 3 := ⟨m - 3, by omega⟩
    refine ⟨6*j*j + 26*j + 17, by positivity, ?_⟩
    rw [show ((2*j) / 2 : Nat) = j from by omega,
        show (m'' + 3 - 3 : Nat) = m'' from by omega]
    exact rule_R_even j m''
  · -- Case 8: m ≥ 3, n odd. R_odd.
    simp [h_neven] at h
    obtain ⟨rfl, rfl⟩ := h
    show ∃ k, k > 0 ∧ srun tm (M n m) k = M (3 * ((n - 1) / 2) + 4) (m - 2)
    obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 1 := ⟨(n - 1) / 2, by omega⟩
    obtain ⟨m'', rfl⟩ : ∃ m'', m = m'' + 3 := ⟨m - 3, by omega⟩
    refine ⟨6*j*j + 26*j + 26, by positivity, ?_⟩
    rw [show ((2*j + 1 - 1) / 2 : Nat) = j from by omega,
        show (m'' + 3 - 2 : Nat) = m'' + 1 from by omega]
    exact rule_R_odd j m''

/-- Halting equivalence at the SConfig level: TM halts from `s.toSConfig`
iff `mathHalts s`.  The `⟨0, 0⟩` translated-cycler case is handled via
`M_0_0_nonhalt`: both sides are false. -/
theorem stm_halts_iff_mathHalts (s : MathState) :
    (∃ k, (srun tm s.toSConfig k).state = none) ↔ mathHalts s := by
  constructor
  · -- Forward: TM halts → mathHalts.  Strong induction on step count.
    intro ⟨k, hk⟩
    suffices ∀ (n : Nat) (s : MathState),
        (srun tm s.toSConfig n).state = none → mathHalts s from
      this k s hk
    intro n; induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro s hk
      cases h_next : nextMathState s with
      | none => exact mathHalts.haltStep s h_next
      | some s' =>
        by_cases h_zero : s = ⟨0, 0⟩
        · -- s = ⟨0, 0⟩: TM doesn't halt, contradiction.
          subst h_zero
          exact absurd hk (M_0_0_nonhalt n)
        · have ⟨k_sim, hk_pos, h_sim⟩ := tm_sim_step s s' h_next h_zero
          by_cases h_lt : n < k_sim
          · exfalso
            have h_still : (srun tm s.toSConfig k_sim).state = none := by
              rw [show k_sim = n + (k_sim - n) from by omega, srun_add,
                  srun_halted _ _ hk]
              exact hk
            rw [h_sim] at h_still
            -- s'.toSConfig.state = some _, contradiction.
            rcases s' with ⟨n', m'⟩
            simp [MathState.toSConfig, M] at h_still
          · rw [show n = k_sim + (n - k_sim) from by omega, srun_add, h_sim] at hk
            exact mathHalts.nextStep s s' h_next
              (ih (n - k_sim) (by omega) s' hk)
  · -- Backward: mathHalts → TM halts.  Induction on mathHalts.
    intro hmh
    induction hmh with
    | haltStep s h_none =>
      have ⟨k, _, h_sim⟩ := tm_sim_halt s h_none
      exact ⟨k, h_sim⟩
    | nextStep s s' h_some _ ih =>
      by_cases h_zero : s = ⟨0, 0⟩
      · -- s = ⟨0, 0⟩: by IH, ∃ k, halt from s'.toSConfig.
        -- nextMathState ⟨0, 0⟩ = some ⟨0, 0⟩, so s' = ⟨0, 0⟩.
        subst h_zero
        simp [nextMathState] at h_some
        rcases s' with ⟨n', m'⟩
        have hn' : n' = 0 := by
          have := congrArg MathState.n h_some; simp at this; omega
        have hm' : m' = 0 := by
          have := congrArg MathState.m h_some; simp at this; omega
        subst hn'; subst hm'
        -- ih gives ∃ k, halt from M 0 0. Contradiction.
        obtain ⟨k, hk⟩ := ih
        exact absurd hk (M_0_0_nonhalt k)
      · have ⟨k_sim, _, h_sim⟩ := tm_sim_step s s' h_some h_zero
        obtain ⟨k', hk'⟩ := ih
        refine ⟨k_sim + k', ?_⟩
        rw [srun_add, h_sim]; exact hk'

private lemma init_no_halt_before_3 :
    ∀ n < 3, (run tm (initConfig 6) n).state ≠ none := by decide

/-- **Halting equivalence theorem**: the TM halts from the blank tape
iff the math model halts starting from `⟨1, 0⟩` (= `M 1 0 = A(7, 0)`,
the first macro config reached from the blank tape, in 3 TM steps).

By `init_to_A_7_0`, the blank tape evolves into `M 1 0` after 3 steps;
combined with `stm_halts_iff_mathHalts`, this yields the iff.

For the wiki's start `A(6, 3) = M 0 3` (reached at step 10 from blank),
note `mathHalts ⟨1, 0⟩ ↔ mathHalts ⟨0, 3⟩` follows from
`nextMathState ⟨1, 0⟩ = some ⟨0, 3⟩` (one math step). -/
theorem tm_halt_iff :
    (∃ k, (run tm (initConfig 6) k).state = none) ↔ mathHalts ⟨1, 0⟩ := by
  rw [← stm_halts_iff_mathHalts]
  -- ⟨1, 0⟩.toSConfig = M 1 0 by rfl.
  have h_toSConfig : (⟨1, 0⟩ : MathState).toSConfig = M 1 0 := rfl
  rw [h_toSConfig]
  -- Bridge initConfig → M 1 0 via init_to_A_7_0.
  have h_eq : ∀ k, (run tm (initConfig 6) k).state =
                    (srun tm (sinitConfig 6) k).state := fun k => by
    change _ = (srun tm (initConfig 6).toSConfig k).state
    rw [← toSConfig_run]; rfl
  constructor
  · rintro ⟨k, hk⟩
    by_cases h : 3 ≤ k
    · refine ⟨k - 3, ?_⟩
      rw [h_eq, show k = 3 + (k - 3) from by omega, srun_add, init_to_A_7_0] at hk
      exact hk
    · -- k < 3: TM hasn't halted yet (no halt before step 3 from blank).
      exact absurd hk (init_no_halt_before_3 k (by omega))
  · rintro ⟨k, hk⟩
    refine ⟨3 + k, ?_⟩
    rw [h_eq (3 + k), srun_add, init_to_A_7_0]
    exact hk

-- ============================================================
-- Wiki-style halting statement: explicit `f : ℕ × ℕ → Option (ℕ × ℕ)`
-- ============================================================

/-- The wiki function `f` from `wiki.txt`: state encoded as `(n, m)`.
Same partial function as `nextMathState`, in compact form using
`m + n` parity to merge the four `m ∈ {0,1}` sub-cases. -/
def f : Nat × Nat → Option (Nat × Nat)
  | (n, m) =>
    if m = 2 ∧ n % 2 = 0 then none
    else if m ≤ 1 ∧ (m + n) % 2 = 0 then some (0, 0)
    else if m ≤ 1 then some (0, 3 * (m + n))
    else if m = 2 then some (0, 3 * n + 5)
    else if n % 2 = 0 then some (3 * n / 2 + 3, m - 3)
    else some ((3 * n + 5) / 2, m - 2)

/-- Iterated `f`. -/
def fIter : Nat → Nat × Nat → Option (Nat × Nat)
  | 0,     s => some s
  | k + 1, s => (f s).bind (fIter k)

/-- `f` and `nextMathState` are the same partial function (up to the
record / pair encoding of states). -/
private lemma f_eq_nextMathState (n m : Nat) :
    f (n, m) = (nextMathState ⟨n, m⟩).map (fun s => (s.n, s.m)) := by
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j := ⟨n / 2, by omega⟩
    have hn' : (2 * j) % 2 = 0 := by omega
    rcases m with _ | _ | _ | m' <;>
      simp [f, nextMathState, hn'] <;> omega
  · obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 1 := ⟨n / 2, by omega⟩
    have hn' : (2 * j + 1) % 2 = 1 := by omega
    rcases m with _ | _ | _ | m' <;>
      simp [f, nextMathState, hn'] <;> omega

/-- For any `MathState s`, `mathHalts s` is equivalent to iterating `f`
from `(s.n, s.m)` ever returning `none`. -/
private lemma mathHalts_iff_fIter (s : MathState) :
    mathHalts s ↔ ∃ k, fIter k (s.n, s.m) = none := by
  constructor
  · intro h
    induction h with
    | haltStep s' h_none =>
      rcases s' with ⟨n, m⟩
      refine ⟨1, ?_⟩
      simp [fIter, f_eq_nextMathState, h_none]
    | nextStep s' s'' h_some _ ih =>
      rcases s' with ⟨n, m⟩
      rcases s'' with ⟨n', m'⟩
      obtain ⟨k, hk⟩ := ih
      refine ⟨k + 1, ?_⟩
      simp [fIter, f_eq_nextMathState, h_some]
      exact hk
  · rintro ⟨k, hk⟩
    induction k generalizing s with
    | zero => simp [fIter] at hk
    | succ k ih =>
      rcases s with ⟨n, m⟩
      simp only [fIter] at hk
      cases h_next : nextMathState ⟨n, m⟩ with
      | none => exact mathHalts.haltStep _ h_next
      | some s' =>
        rw [f_eq_nextMathState, h_next] at hk
        simp at hk
        rcases s' with ⟨n', m'⟩
        exact mathHalts.nextStep _ _ h_next (ih ⟨n', m'⟩ hk)

/-- **Halting equivalence (wiki form)**: the TM halts from the blank
tape iff iterating `f` from `(1, 0)` eventually returns `none`. -/
theorem tm_halt_iff_math :
    (∃ k, (run tm (initConfig 6) k).state = none) ↔
    ∃ k, fIter k (1, 0) = none := by
  rw [tm_halt_iff, mathHalts_iff_fIter]

end RachelineII
