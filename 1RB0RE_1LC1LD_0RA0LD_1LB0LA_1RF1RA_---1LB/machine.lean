import BusyLean
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify

open BusyLean

namespace Racheline6

/-!
# 6-state TM `1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB`

BB(6) holdout candidate.  Halt/nonhalt is **not** the target; this file
records observed macro rules.

## Transition table
|   | 0   | 1   |
|---|-----|-----|
| A | 1RB | 0RE |
| B | 1LC | 1LD |
| C | 0RA | 0LD |
| D | 1LB | 0LA |
| E | 1RF | 1RA |
| F | --- | 1LB |

The only halting transition is `F,0 → ---`.  F is entered only from
`E,0 → 1RF`.

## Macro configuration (from previous-work/wiki.txt, Racheline)

`A(n, m) := 0^∞ (01)^(3n−4) [A>] (01)^m 0^∞`
— state A moving right, head on the first cell of the right (01)-block
(reading 0), left tape is `(01)^(3n−4)` followed by blanks, right tape
is `(01)^m` followed by blanks.  Requires `n ≥ 2` (so `3n−4 ≥ 2`).

Macro rules (all verified empirically in `sim.py` for `n ≤ 11`,
`m ≤ 5`; see `LOG.md`):

```
  A(n, 0)    → A(2, 3n−4)                dt = 12n + 6
  A(2n, m)   → A(3n, m−2)     (m ≥ 2)    dt = 72n² + 12n − 30
  A(2n+1, m) → A(3n+1, m−1)   (m ≥ 1)    dt = 72n² + 48n − 10
  A(2n, 1)   → halt                      dt = 72n² − 24n − 15
```

Initial reach: from blank tape, the machine enters `A(2, 0)` after 22
steps (verified by `sim.py init`).

## Representation (Lean / SConfig)

To sidestep natural-number subtraction we parametrize by `n' := n − 2`:
`A_Config n' m` represents the wiki's `A(n' + 2, m)`.

The right side of the tape has a non-uniform shape:
- `m = 0`: right stream is blank.
- `m ≥ 1`: right stream is `1 :: (01)^(m−1) :: blank∞`
  (length `2m − 1`, `m` ones and `m−1` zeros alternating starting with 1).

## Proof status (2026-04-24)

**Fully proved:**
- `rule_reset` (R1) — `A(n, 0) → A(2, 3n−4)` in `12n + 6` steps, any `n ≥ 2`.
- `init_to_A_20` — blank tape reaches `A(2, 0)` in 22 steps.
- Base cases `rule_even_base`, `rule_odd_base`, `rule_halt_base` — the
  three quadratic rules at `k = 0`, via direct `simp` on abstract tails.

**Shared shift-rule infrastructure:**
- `left_cycle`, `left_cycle_iter` — 4-step cycle and its iteration
  used by R1 (consumes `oz k` on left, deposits `cons false (zebra k)`
  on right).
- `phase2` — 22-step R1 tail, uniform in any right tail.
- `ae_cycle`, `ae_sweep` — A-E 2-step cycle and its iteration (right
  `ones` → left `oz`).  Used by R2/R3 endgames.
- `bd_cycle`, `bd_sweep` — D-B 2-step cycle and its iteration (left
  `oz` → right `ones`).  The mirror-image of AE.
- `setup_phase_R2_k0` — explicit R2 setup phase for `k = 0`
  (44 steps, uniform in tail).

**Open (3 sorries):**
- `rule_even`, `rule_odd`, `rule_halt` for general `k`.  Each decomposes
  into a quadratic setup phase + an `ae_sweep` endgame, but the setup
  phase's outer-loop induction is not yet formalized.  See `LOG.md`
  for the full Shifty6-style architecture plan.
-/

def tm : TM 6 := tm! "1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB"

-- Transition simp lemmas: evaluate `tm.tr st sym` without unfolding the literal.
@[simp] private theorem tr_A0 : tm.tr stA false = some (stB, true,  Dir.R) := rfl
@[simp] private theorem tr_A1 : tm.tr stA true  = some (stE, false, Dir.R) := rfl
@[simp] private theorem tr_B0 : tm.tr stB false = some (stC, true,  Dir.L) := rfl
@[simp] private theorem tr_B1 : tm.tr stB true  = some (stD, true,  Dir.L) := rfl
@[simp] private theorem tr_C0 : tm.tr stC false = some (stA, false, Dir.R) := rfl
@[simp] private theorem tr_C1 : tm.tr stC true  = some (stD, false, Dir.L) := rfl
@[simp] private theorem tr_D0 : tm.tr stD false = some (stB, true,  Dir.L) := rfl
@[simp] private theorem tr_D1 : tm.tr stD true  = some (stA, false, Dir.L) := rfl
@[simp] private theorem tr_E0 : tm.tr stE false = some (stF, true,  Dir.R) := rfl
@[simp] private theorem tr_E1 : tm.tr stE true  = some (stA, true,  Dir.R) := rfl
@[simp] private theorem tr_F0 : tm.tr stF false = none := rfl
@[simp] private theorem tr_F1 : tm.tr stF true  = some (stB, true,  Dir.L) := rfl

-- ============================================================
-- Macro configuration
-- ============================================================

/-- Pattern `1, 0` repeated `k` times, as a List.  Used for the
left-outward stream: reading head−1, head−2, ... in an `A(n, m)` config,
the cells alternate `1, 0, 1, 0, …` for `2·(3n−4)` positions.  This is
the reverse of `zebra (3n−4)` as a list. -/
def oz : ℕ → List Sym
  | 0 => []
  | k + 1 => true :: false :: oz k

@[simp] theorem oz_zero : oz 0 = [] := rfl
@[simp] theorem oz_succ (k : ℕ) : oz (k + 1) = true :: false :: oz k := rfl

theorem oz_append (a b : ℕ) : oz a ++ oz b = oz (a + b) := by
  induction a with
  | zero => simp
  | succ a ih =>
    simp only [oz_succ, List.cons_append, ih,
      show a + 1 + b = (a + b) + 1 from by omega]

/-- `oz` grows from the right: `oz (k + 1) = oz k ++ [true, false]`.
Dual of the defining `oz_succ = [true, false] ++ oz k`. -/
theorem oz_succ_append (k : ℕ) : oz (k + 1) = oz k ++ [true, false] := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    show true :: false :: oz (k' + 1) = (true :: false :: oz k') ++ [true, false]
    rw [ih]; rfl

/-- Right-side list for `A(n, m)`: cells at positions head+1, head+2, …,
head+2m−1, reading outward from the head.  When `m = 0`, empty; when
`m ≥ 1`, `1 :: zebra (m−1)` (pattern `1,0,1,0,…,0,1` of length `2m−1`,
with `m` ones and `m−1` zeros).  Note `zebra k = [false, true]^k`. -/
def rightPat : ℕ → List Sym
  | 0 => []
  | m + 1 => true :: zebra m

@[simp] theorem rightPat_zero : rightPat 0 = [] := rfl
@[simp] theorem rightPat_succ (m : ℕ) : rightPat (m + 1) = true :: zebra m := rfl

/-- Macro configuration `A(n' + 2, m)` as an `SConfig 6`.
- State A, head on the first cell of `(01)^m` (a `0`).
- Left outward stream: `oz (3n' + 2)` followed by blank.
- Right outward stream: `rightPat m` followed by blank. -/
def A_Config (n' m : ℕ) : SConfig 6 :=
  { state := some stA,
    head := false,
    left := oz (3 * n' + 2) *> blank∞,
    right := rightPat m *> blank∞ }

-- ============================================================
-- Shared infrastructure  (used by R1; needed for R2/R3)
-- ============================================================

/-- **2-step A-E cycle over a `1`.**  `A,1→0RE` then `E,1→1RA` consumes
one `true` from the front of the right stream, and prepends `(true, false)`
(reading outward) to the left — i.e., extends `oz` on the left by one pair.
The cycle can continue as long as the next right cell is `true`. -/
private lemma ae_cycle (L R : Side) :
    srun tm
      ({ state := some stA, head := true, left := L,
         right := Side.cons true R } : SConfig 6) 2
    = { state := some stA, head := R.head,
        left := Side.cons true (Side.cons false L),
        right := R.tail } := by
  simp [srun, sstep, tm]

/-- **Iterated A-E sweep.**  A run of `k+1` cycles over `2k+1` consecutive
`true`s on the right, ending at whatever cell follows.  Deposits
`oz (k+1)` on the left.  Used by R2/R3 endgames. -/
private lemma ae_sweep (k : ℕ) (L R : Side) :
    srun tm
      ({ state := some stA, head := true, left := L,
         right := ones (2 * k + 1) *> R } : SConfig 6) (2 * k + 2)
    = { state := some stA, head := R.head,
        left := oz (k + 1) *> L,
        right := R.tail } := by
  induction k generalizing L R with
  | zero =>
    rw [show (ones (2 * 0 + 1) *> R : Side) = Side.cons true R from rfl]
    rw [ae_cycle L R]; rfl
  | succ k' ih =>
    rw [show (2 * (k' + 1) + 2 : ℕ) = 2 + (2 * k' + 2) from by ring, srun_add]
    rw [show (ones (2 * (k' + 1) + 1) *> R : Side)
          = Side.cons true (Side.cons true (ones (2 * k' + 1) *> R)) from rfl]
    rw [ae_cycle L (Side.cons true (ones (2 * k' + 1) *> R))]
    simp only [Side.head_cons, Side.tail_cons]
    rw [ih (Side.cons true (Side.cons false L)) R]
    congr 1
    show Side.prepend (oz (k' + 1)) (Side.cons true (Side.cons false L))
       = Side.prepend (oz (k' + 1 + 1)) L
    rw [show (Side.cons true (Side.cons false L) : Side)
          = Side.prepend [true, false] L from rfl,
        ← Side.prepend_append]
    congr 1
    -- Goal: oz (k'+1) ++ [true, false] = oz (k'+1+1)
    rw [show (k' + 1 + 1 : ℕ) = (k' + 1) + 1 from rfl]
    exact (oz_succ_append (k' + 1)).symm

/-- **2-step B-D cycle over an oz pair.**  `D,0→1LB` then `B,1→1LD` consumes
one outward `(true, false)` pair from the left (the mirror of `ae_cycle`'s
right consumption), and prepends two `true`s to the right.  The sweep
continues as long as the left next starts with `cons true (cons false _)`. -/
private lemma bd_cycle (L R : Side) :
    srun tm
      ({ state := some stD, head := false,
         left := Side.cons true (Side.cons false L),
         right := R } : SConfig 6) 2
    = { state := some stD, head := false,
        left := L,
        right := Side.cons true (Side.cons true R) } := by
  simp [srun, sstep, tm]

/-- **Iterated B-D sweep.**  `k+1` applications of `bd_cycle`: consumes
`oz (k+1)` from the left and deposits `ones (2k+2)` on the right. -/
private lemma bd_sweep (k : ℕ) (L R : Side) :
    srun tm
      ({ state := some stD, head := false,
         left := oz k *> Side.cons true (Side.cons false L),
         right := R } : SConfig 6) (2 * k + 2)
    = { state := some stD, head := false,
        left := L,
        right := ones (2 * k + 2) *> R } := by
  induction k generalizing L R with
  | zero =>
    rw [show (oz 0 *> Side.cons true (Side.cons false L) : Side)
          = Side.cons true (Side.cons false L) from rfl,
        show (2 * 0 + 2 : ℕ) = 2 from rfl,
        bd_cycle L R]
    rfl
  | succ k' ih =>
    rw [show (oz (k' + 1) *> Side.cons true (Side.cons false L) : Side)
          = Side.cons true (Side.cons false
              (oz k' *> Side.cons true (Side.cons false L))) from rfl,
        show (2 * (k' + 1) + 2 : ℕ) = 2 + (2 * k' + 2) from by ring,
        srun_add,
        bd_cycle (oz k' *> Side.cons true (Side.cons false L)) R,
        ih L (Side.cons true (Side.cons true R))]
    congr 1
    rw [show (Side.cons true (Side.cons true R) : Side) = Side.prepend (ones 2) R from rfl,
        ← Side.prepend_append, ones_append,
        show (2 * k' + 2 + 2 : ℕ) = 2 + (2 * k' + 2) from by ring]

-- ============================================================
-- Rule R1 infrastructure
-- ============================================================

/-- **4-step left cycle.**  From state A head=0 with left-outward starting
with a `(1, 0)` pair and right-outward starting with a `0`, after 4 steps
we land back in state A head=0, with:
- the `(1, 0)` prefix consumed from the left (`L` unchanged below),
- a `(0, 0, 1)` prefix added to the right (before the original tail `R`).

Empirically: the 4-step sequence `A,0→B,0→C,1→D,1→A` maps
```
  … 1 0 [A>0] 0 …  →  … [A>0] 0 0 1 …
```
shifting the head 2 cells left and pushing `0 0 1` onto the right side.
The lemma is local in any `L` (left-tail) and `R` (right-tail). -/
private lemma left_cycle (L R : Side) :
    srun tm
      ({ state := some stA, head := false,
         left := Side.cons true (Side.cons false L),
         right := Side.cons false R } : SConfig 6) 4
    = { state := some stA, head := false,
        left := L,
        right := Side.cons false (Side.cons false (Side.cons true R)) } := by
  simp [srun, sstep, tm]

/-- **Iterated left cycle.**  Applying `left_cycle` `k` times from a left of
`oz k *> L` and right of `cons false R` consumes `oz k` from the left and
prepends `cons false (zebra k *> _)` to the right. -/
private lemma left_cycle_iter (k : ℕ) (L R : Side) :
    srun tm
      ({ state := some stA, head := false,
         left := oz k *> L,
         right := Side.cons false R } : SConfig 6) (4 * k)
    = { state := some stA, head := false,
        left := L,
        right := Side.cons false (zebra k *> R) } := by
  induction k generalizing R with
  | zero => simp [srun]
  | succ k' ih =>
    -- Unfold `oz (k'+1) = true :: false :: oz k'` on the left.
    show srun tm
      ({ state := some stA, head := false,
         left := Side.prepend (true :: false :: oz k') L,
         right := Side.cons false R } : SConfig 6) (4 * (k' + 1))
    = _
    rw [show (Side.prepend (true :: false :: oz k') L : Side)
          = Side.cons true (Side.cons false (oz k' *> L)) from rfl,
        show 4 * (k' + 1) = 4 + 4 * k' from by ring,
        srun_add, left_cycle (oz k' *> L) R, ih (Side.cons false (Side.cons true R))]
    -- Remaining: reconcile the right tails.
    congr 1
    -- Goal: cons false (zebra k' *> cons false (cons true R))
    --     = cons false (zebra (k'+1) *> R)
    congr 1
    -- zebra k' *> cons false (cons true R) = zebra (k'+1) *> R
    show Side.prepend (zebra k') (Side.prepend [false, true] R)
       = Side.prepend (zebra (k' + 1)) R
    rw [← Side.prepend_append, zebra_succ_append]

/-- **Phase-2 tail (22 steps).**  From the configuration reached after all
the left cycles — state A head=0 with blank left and right starting `0 0 T`
for arbitrary `T` — the TM runs 22 more steps to `A(2, k)`-shape: state A
head=0 with `(1,0,1,0)` on left and the tail `T` preserved on the right.

Verified empirically (`sim.py`): head excursion during these 22 steps is
strictly bounded (3 left, 2 right), so the proof is uniform in `T`. -/
private lemma phase2 (T : Side) :
    srun tm
      ({ state := some stA, head := false,
         left := blank∞,
         right := Side.cons false (Side.cons false T) } : SConfig 6) 22
    = { state := some stA, head := false,
        left := oz 2 *> blank∞,
        right := T } := by
  simp [srun, sstep, tm, oz, Side.prepend]

-- ============================================================
-- R2 inner-loop infrastructure
-- ============================================================

/-- **`cyclic_rest` lemma**: the closing phase of one inner-loop
iteration.  Given state D at the leftmost position with `oz p` on the
left and `ones q` (possibly empty) at the front of the right (before a
`cons false`), runs `2p + 3` steps to the next `A,1,left-blank` event,
accumulating `2p + q + 1` ones at the front of the right.

Proved by induction on `p`: each outer oz-pair on the left adds 2
ones to the right via `bd_cycle`; the final 3 steps are the D→B→C→A
transition that consumes blank on the left and reads the first cell
of the ones-block as the new head. -/
private lemma cyclic_rest (p q : ℕ) (R : Side) :
    srun tm
      ({ state := some stD, head := false,
         left := Side.prepend (oz p) blank∞,
         right := Side.prepend (ones q) (Side.cons false R) } : SConfig 6)
      (2 * p + 3)
    = { state := some stA, head := true,
        left := blank∞,
        right := Side.prepend (ones (2 * p + q + 1)) (Side.cons false R) } := by
  induction p generalizing q with
  | zero =>
    rw [show (Side.prepend (oz 0) blank∞ : Side) = blank∞ from rfl]
    simp [srun, sstep, tm, ones]
  | succ p' ih =>
    rw [show (Side.prepend (oz (p'+1)) blank∞ : Side)
          = Side.cons true (Side.cons false (Side.prepend (oz p') blank∞)) from rfl,
        show (2 * (p'+1) + 3 : ℕ) = 2 + (2 * p' + 3) from by ring,
        srun_add,
        bd_cycle (Side.prepend (oz p') blank∞) (Side.prepend (ones q) (Side.cons false R))]
    rw [show (Side.cons true (Side.cons true (Side.prepend (ones q) (Side.cons false R))) : Side)
          = Side.prepend (ones (q+2)) (Side.cons false R) from by
          show Side.cons true (Side.cons true _) = _
          rw [show (q+2 : ℕ) = 2 + q from by ring, ← ones_append]
          rfl]
    rw [ih (q + 2)]
    congr 1
    rw [show (2 * p' + (q + 2) + 1 : ℕ) = 2 * (p'+1) + q + 1 from by ring]

/-- **`middle_R2` lemma**: 9 fixed steps of the inner-step middle phase.
Transforms state A head=0 post-AE-sweep with `oz (p+2)` on left and
`ones (m+1)` inner-block on right, into state C head=1 with
`cons false (oz p)` on left and `ones (m+4)` inner-block on right.
The trajectory is a fixed 9-step dance through B, D, A, E, F, B, D, B, C
transitions, uniform in `p` and `m` (requires `m ≥ 0`, hence `M ≥ 1`). -/
private lemma middle_R2 (p m : ℕ) (Y : Side) :
    srun tm
      ({ state := some stA, head := false,
         left := Side.prepend (oz (p+2)) blank∞,
         right := Side.prepend (ones (m+1)) Y } : SConfig 6) 9
    = { state := some stC, head := true,
        left := Side.cons false (Side.prepend (oz p) blank∞),
        right := Side.prepend (ones (m+4)) Y } := by
  show srun tm
    ({ state := some stA, head := false,
       left := Side.cons true (Side.cons false (Side.cons true (Side.cons false
               (Side.prepend (oz p) blank∞)))),
       right := Side.cons true (Side.prepend (ones m) Y) } : SConfig 6) 9
    = _
  simp [srun, sstep, tm, ones, Side.prepend]

/-- **`inner_step` lemma**: one inner-loop iteration.

Given a state at the "A,1,left-blank" event with `ones (2p+3)` leading
on the right and `ones (m+1)` inner-block after a `cons false` separator,
runs `4p + 17` steps (= `2(2p+3) + 11` for leading ones count `2p+3`)
to reach the next event with `ones (2p+1)` leading and `ones (m+4)`
inner-block.  Decomposition: `ae_sweep (p+1)` (`2p+4` steps) + `middle_R2`
(9 steps) + C,1→0LD transition (1 step) + `cyclic_rest p 0` (`2p+3` steps).
Total: `(2p+4) + 9 + 1 + (2p+3) = 4p + 17`. -/
private lemma inner_step (p m : ℕ) (Y : Side) :
    srun tm
      ({ state := some stA, head := true, left := blank∞,
         right := Side.prepend (ones (2*p+3)) (Side.cons false
                  (Side.prepend (ones (m+1)) Y)) } : SConfig 6)
      (4 * p + 17)
    = { state := some stA, head := true, left := blank∞,
        right := Side.prepend (ones (2*p+1)) (Side.cons false
                 (Side.prepend (ones (m+4)) Y)) } := by
  rw [show (4*p + 17 : ℕ) = (2*(p+1) + 2) + (9 + (1 + (2*p + 3))) from by ring,
      show (2*p + 3 : ℕ) = 2*(p+1) + 1 from by ring, srun_add,
      ae_sweep (p+1) blank∞ (Side.cons false
                 (Side.prepend (ones (m+1)) Y))]
  simp only [Side.head_cons, Side.tail_cons]
  rw [srun_add, middle_R2 p m Y, srun_add]
  have hCD : srun tm
      ({ state := some stC, head := true,
         left := Side.cons false (Side.prepend (oz p) blank∞),
         right := Side.prepend (ones (m+4)) Y } : SConfig 6) 1
      = { state := some stD, head := false,
          left := Side.prepend (oz p) blank∞,
          right := Side.cons false (Side.prepend (ones (m+4)) Y) } := by
    simp [srun, sstep, tm]
  rw [hCD]
  rw [show (Side.cons false (Side.prepend (ones (m+4)) Y) : Side)
        = Side.prepend (ones 0) (Side.cons false
            (Side.prepend (ones (m+4)) Y)) from rfl,
      show (2*(p+1) + 1 : ℕ) = 2*p + 3 from by ring,
      cyclic_rest p 0 (Side.prepend (ones (m+4)) Y)]
  show ({ state := _, left := _, head := _,
          right := Side.prepend (ones (2*p + 0 + 1)) _ } : SConfig 6) = _
  rw [show (2*p + 0 + 1 : ℕ) = 2*p + 1 from by ring,
      show (Side.prepend (ones (2*p + 1)) (Side.prepend (ones 0) (Side.cons false
             (Side.prepend (ones (m+4)) Y))) : Side)
        = Side.prepend (ones (2*p + 1)) (Side.cons false
             (Side.prepend (ones (m+4)) Y)) from by
        show Side.prepend (ones (2*p+1)) (Side.prepend [] _) = _
        rw [Side.prepend_nil]]

/-- **Iterated inner-step.**  After `I` iterations of `inner_step` starting
from an "event" state with `ones (2P+3)` leading, reaches state with
`ones (2P+3-2I)` leading and `m` bumped by `3I`.  Requires `I ≤ P+1`.
Step count: `4PI + 19I - 2I²`. -/
private lemma inner_loop_iter (I P m : ℕ) (h : I ≤ P + 1) (Y : Side) :
    srun tm
      ({ state := some stA, head := true, left := blank∞,
         right := Side.prepend (ones (2*P+3)) (Side.cons false
                  (Side.prepend (ones (m+1)) Y)) } : SConfig 6)
      (4 * P * I + 19 * I - 2 * I * I)
    = { state := some stA, head := true, left := blank∞,
        right := Side.prepend (ones (2*P + 3 - 2*I)) (Side.cons false
                 (Side.prepend (ones (m + 3*I + 1)) Y)) } := by
  induction I generalizing m with
  | zero => simp [srun]
  | succ I' ih =>
    have hI'P : I' ≤ P := Nat.le_of_succ_le_succ h
    have hI' : I' ≤ P + 1 := Nat.le_of_succ_le h
    have hstep : (4 * P * (I'+1) + 19 * (I'+1) - 2 * (I'+1) * (I'+1) : ℕ)
          = (4 * P * I' + 19 * I' - 2 * I' * I') + (4 * (P - I') + 17) := by
      have h1 : 2 * I' * I' ≤ 4 * P * I' + 19 * I' := by nlinarith
      have h2 : 2 * (I'+1) * (I'+1) ≤ 4 * P * (I'+1) + 19 * (I'+1) := by nlinarith
      zify [h1, h2, hI'P]; ring
    rw [hstep, srun_add, ih m hI']
    rw [show (2 * P + 3 - 2 * I' : ℕ) = 2 * (P - I') + 3 from by omega]
    rw [inner_step (P - I') (m + 3*I') Y]
    congr 2
    congr 1; omega

-- ============================================================
-- R2 prelude infrastructure
-- ============================================================

/-- **Initial 9-step sequence** of R2/R4's prelude: from the `A_Config`-like
initial state (with abstract left tail `L` and abstract right cell-2+ tail
`Y2`), reaches a state C that is the input to the `cyclic_rest` sweep.
Uniform in `L`, `Y2` (head excursion only reaches cells 0, 1 on the right).
For R2 applications `Y2 = cons true (cons false X)`; for R4, `Y2 = blank`. -/
private lemma initial_9 (L Y2 : Side) :
    srun tm
      ({ state := some stA, head := false,
         left := Side.cons true (Side.cons false (Side.cons true (Side.cons false L))),
         right := Side.cons true (Side.cons false Y2) } : SConfig 6) 9
    = { state := some stC, head := true,
        left := Side.cons false L,
        right := Side.prepend (ones 4) (Side.cons false Y2) } := by
  simp [srun, sstep, tm, ones]

/-- **R2 prelude.**  `12k + 13` steps from R2's initial config to the
first "A,1,left-blank" event state, with ones count `12k+1` leading
and `ones 4` in the inner block.  Decomposes as `initial_9` (9 steps)
+ `C,1→0LD` (1 step) + `cyclic_rest (6k) 0` (`12k + 3` steps). -/
private lemma prelude_R2 (k : ℕ) (X : Side) :
    srun tm
      ({ state := some stA, head := false,
         left := oz (6*k+2) *> blank∞,
         right := oz 2 *> X } : SConfig 6) (12*k + 13)
    = { state := some stA, head := true, left := blank∞,
        right := Side.prepend (ones (12*k+1)) (Side.cons false
                 (Side.prepend (ones 4) (Side.cons false (Side.cons true (Side.cons false X))))) } := by
  have hL : (oz (6*k+2) *> blank∞ : Side)
        = Side.cons true (Side.cons false (Side.cons true (Side.cons false
          (oz (6*k) *> blank∞)))) := by
    show Side.prepend (oz (6*k+2)) blank∞ = _
    rw [show (6*k+2 : ℕ) = (6*k) + 2 from by ring]; rfl
  rw [hL, show (oz 2 *> X : Side)
        = Side.cons true (Side.cons false (Side.cons true (Side.cons false X))) from rfl,
      show (12*k + 13 : ℕ) = 9 + (1 + (2*(6*k) + 3)) from by ring,
      srun_add, initial_9 (oz (6*k) *> blank∞) (Side.cons true (Side.cons false X)), srun_add]
  have hCD : srun tm
      ({ state := some stC, head := true,
         left := Side.cons false (oz (6*k) *> blank∞),
         right := Side.prepend (ones 4) (Side.cons false (Side.cons true (Side.cons false X))) } : SConfig 6) 1
      = { state := some stD, head := false,
          left := oz (6*k) *> blank∞,
          right := Side.cons false (Side.prepend (ones 4) (Side.cons false (Side.cons true (Side.cons false X)))) } := by
    simp [srun, sstep, tm]
  rw [hCD,
      show (Side.cons false (Side.prepend (ones 4) (Side.cons false (Side.cons true (Side.cons false X)))) : Side)
        = Side.prepend (ones 0) (Side.cons false (Side.prepend (ones 4) (Side.cons false (Side.cons true (Side.cons false X))))) from rfl,
      cyclic_rest (6*k) 0 (Side.prepend (ones 4) (Side.cons false (Side.cons true (Side.cons false X))))]
  congr 1
  show Side.prepend (ones (2 * (6 * k) + 0 + 1)) _ = Side.prepend (ones (12*k+1)) _
  rw [show (2 * (6 * k) + 0 + 1 : ℕ) = 12*k + 1 from by ring,
      show (Side.prepend (ones (12*k+1)) (Side.prepend (ones 0) (Side.cons false
             (Side.prepend (ones 4) (Side.cons false (Side.cons true (Side.cons false X)))))) : Side)
        = Side.prepend (ones (12*k+1)) (Side.cons false
             (Side.prepend (ones 4) (Side.cons false (Side.cons true (Side.cons false X))))) from by
        show Side.prepend (ones (12*k+1)) (Side.prepend [] _) = _
        rw [Side.prepend_nil]]

-- ============================================================
-- R2 post-inner-loop infrastructure
-- ============================================================

/-- **Phase A** of post-inner-loop (5 steps, generic `Y2` tail): consumes the
leading `ones 1`, strips the first `cons false` separator. -/
private lemma phase_A (m : ℕ) (Y2 : Side) :
    srun tm
      ({ state := some stA, head := true, left := blank∞,
         right := Side.cons true (Side.cons false (Side.prepend (ones (m+1)) Y2)) } : SConfig 6) 5
    = { state := some stA, head := true, left := blank∞,
        right := Side.cons false (Side.prepend (ones (m+1)) Y2) } := by
  simp [srun, sstep, tm, ones]

/-- **Phase B** of post-inner-loop (7 steps, generic `Y2`): bumps leading ones
count from `0` to `m+3`. -/
private lemma phase_B (m : ℕ) (Y2 : Side) :
    srun tm
      ({ state := some stA, head := true, left := blank∞,
         right := Side.cons false (Side.prepend (ones (m+1)) Y2) } : SConfig 6) 7
    = { state := some stA, head := true, left := blank∞,
        right := Side.prepend (ones (m+3)) Y2 } := by
  simp [srun, sstep, tm, ones]

/-- **Phase C** of post-inner-loop (`4q+11` steps): final expansion that
takes `ones (2q+2)` + separator + `cons true (cons false X)` to
`ones (2q+5)` + `cons false X`, absorbing the trailing `cons true` into
the ones block.  Decomposes as `ae_sweep q` + 4 fixed transitions +
`cyclic_rest (q+1) 2`. -/
private lemma phase_C (q : ℕ) (X : Side) :
    srun tm
      ({ state := some stA, head := true, left := blank∞,
         right := Side.prepend (ones (2*(q+1))) (Side.cons false
                  (Side.cons true (Side.cons false X))) } : SConfig 6) (4*q + 11)
    = { state := some stA, head := true, left := blank∞,
        right := Side.prepend (ones (2*(q+1)+3)) (Side.cons false X) } := by
  rw [show (4*q + 11 : ℕ) = (2*q + 2) + (4 + (2*(q+1) + 3)) from by ring,
      show (Side.prepend (ones (2*(q+1))) (Side.cons false (Side.cons true (Side.cons false X))) : Side)
        = Side.prepend (ones (2*q+1)) (Side.cons true
          (Side.cons false (Side.cons true (Side.cons false X)))) from by
        rw [show (2*(q+1) : ℕ) = (2*q+1) + 1 from by ring,
            show ones ((2*q+1)+1) = ones (2*q+1) ++ [true] from by
              rw [show ones ((2*q+1)+1) = ones (2*q+1) ++ ones 1 from (ones_append _ _).symm]; rfl,
            Side.prepend_append]; rfl,
      srun_add,
      ae_sweep q blank∞ (Side.cons true (Side.cons false (Side.cons true (Side.cons false X))))]
  simp only [Side.head_cons, Side.tail_cons]
  rw [srun_add]
  have hfix : srun tm
      ({ state := some stA, head := true, left := oz (q+1) *> blank∞,
         right := Side.cons false (Side.cons true (Side.cons false X)) } : SConfig 6) 4
      = { state := some stD, head := false, left := oz (q+1) *> blank∞,
          right := Side.cons true (Side.cons true (Side.cons false X)) } := by
    simp [srun, sstep, tm]
  rw [hfix,
      show (Side.cons true (Side.cons true (Side.cons false X)) : Side)
        = Side.prepend (ones 2) (Side.cons false X) from rfl,
      cyclic_rest (q+1) 2 X]

/-- **R2 post-inner-loop** (`36k + 31` steps): from the final inner-loop
state (`ones 1` leading, `ones (18k+4)` inner) to the AE-sweep-input
state (`ones (18k+9)` leading, tail `cons false X`).  Composition of
`phase_A` + `phase_B` + `phase_C (9k+2)`. -/
private lemma post_inner_loop (k : ℕ) (X : Side) :
    srun tm
      ({ state := some stA, head := true, left := blank∞,
         right := Side.prepend (ones 1) (Side.cons false
                  (Side.prepend (ones (18*k+4)) (Side.cons false (Side.cons true
                  (Side.cons false X))))) } : SConfig 6) (36*k + 31)
    = { state := some stA, head := true, left := blank∞,
        right := Side.prepend (ones (18*k+9)) (Side.cons false X) } := by
  rw [show (36*k + 31 : ℕ) = 5 + (7 + (4*(9*k+2) + 11)) from by ring,
      show (Side.prepend (ones 1) (Side.cons false _) : Side)
        = Side.cons true (Side.cons false
          (Side.prepend (ones (18*k+4)) (Side.cons false (Side.cons true
          (Side.cons false X))))) from rfl,
      srun_add,
      show (18*k+4 : ℕ) = (18*k+3) + 1 from by ring,
      phase_A (18*k+3) (Side.cons false (Side.cons true (Side.cons false X))),
      srun_add,
      phase_B (18*k+3) (Side.cons false (Side.cons true (Side.cons false X))),
      show (18*k+3 + 3 : ℕ) = 2 * ((9*k+2) + 1) from by ring,
      phase_C (9*k+2) X]
  congr 1
  show Side.prepend (ones (2 * (9*k+2 + 1) + 3)) _ = _
  rw [show (2 * (9*k+2 + 1) + 3 : ℕ) = 18*k + 9 from by ring]

-- ============================================================
-- `setup_phase_R2` — general-`k` setup
-- ============================================================

/-- **R2 setup phase for general `k`** (`72k² + 138k + 44` steps).
Transforms the initial R2 config (left `oz (6k+2)`, right `oz 2 *> X`)
into the AE-sweep input: state A head=true, blank left, right = `ones
(18k+9) *> cons false X`.

**Structural decomposition** (from empirical analysis, see `LOG.md`):
- **Prelude** (~`12k + 25` steps): initial right `oz 2 *> X` block
  and the first bounce into leftmost-blank-boundary A-events.  Ends
  with state A head=1 at leftmost blank, right = `ones (12k+1) *>
  cons false (ones 4 *> cons false (cons true X))`.
- **Inner loop** (`6k` iterations of `inner_step_R2`): each iteration
  takes `2N + 11` steps (where `N` is the current leading ones count),
  with `N` starting at `12k+1` and decreasing by 2 each iteration.
  Total inner-loop steps: `∑ᵢ₌₀^{6k-1} (2(12k+1-2i) + 11) = 72k² + 90k`.
- **Turnaround** (constant steps): final transitions when ones-count
  reaches 1, reorganizing into the "big ones block".
- **Buildup** (~`24k + 19` steps): accumulates final `ones (18k+9)`
  count on right.

Total: `(12k+25) + (72k²+90k) + (small const + 24k + 19) = 72k² + 138k + 44`.

For `k = 0` this reduces to `setup_phase_R2_k0` directly
(no inner iterations, just prelude + direct buildup).

Base case `k = 0` is proved via `setup_phase_R2_k0`; general `k`
requires the `inner_step_R2` invariant plus the prelude/buildup
characterizations (open). -/
private lemma setup_phase_R2 (k : ℕ) (X : Side) :
    srun tm
      ({ state := some stA, head := false,
         left := oz (6 * k + 2) *> blank∞,
         right := oz 2 *> X } : SConfig 6)
      (72 * k * k + 138 * k + 44)
    = { state := some stA, head := true,
        left := blank∞,
        right := ones (18 * k + 9) *> Side.cons false X } := by
  match k with
  | 0 =>
    rw [show (72*0*0 + 138*0 + 44 : ℕ) = (12*0 + 13) + (36*0 + 31) from by ring,
        srun_add, prelude_R2 0 X]
    exact post_inner_loop 0 X
  | k' + 1 =>
    have h1 : 72*(k'+1)*(k'+1) + 138*(k'+1) + 44
           = (12*(k'+1) + 13)
           + (4 * (6*k'+5) * (6*k'+6) + 19 * (6*k'+6) - 2 * (6*k'+6) * (6*k'+6))
           + (36*(k'+1) + 31) := by
      have hle : 2*(6*k'+6)*(6*k'+6) ≤ 4*(6*k'+5)*(6*k'+6) + 19*(6*k'+6) := by nlinarith
      zify [hle]; ring
    rw [h1]
    rw [show ((12*(k'+1) + 13)
            + (4 * (6*k'+5) * (6*k'+6) + 19 * (6*k'+6) - 2 * (6*k'+6) * (6*k'+6))
            + (36*(k'+1) + 31) : ℕ)
          = (12*(k'+1) + 13) +
            ((4 * (6*k'+5) * (6*k'+6) + 19 * (6*k'+6) - 2 * (6*k'+6) * (6*k'+6))
            + (36*(k'+1) + 31)) from by omega]
    rw [srun_add, prelude_R2 (k'+1) X, srun_add]
    have hI : (6*k'+6) ≤ (6*k'+5) + 1 := by omega
    rw [show (12*(k'+1) + 1 : ℕ) = 2*(6*k'+5) + 3 from by ring,
        show (4 : ℕ) = 3 + 1 from rfl,
        inner_loop_iter (6*k'+6) (6*k'+5) 3 hI (Side.cons false (Side.cons true (Side.cons false X)))]
    rw [show (2 * (6*k'+5) + 3 - 2 * (6*k'+6) : ℕ) = 1 from by omega,
        show (3 + 3 * (6*k'+6) + 1 : ℕ) = 18*(k'+1) + 4 from by ring]
    exact post_inner_loop (k'+1) X

set_option maxRecDepth 4000 in
/-- **Concrete base case `k = 1`** of `setup_phase_R2` (254 steps, abstract
tail `X`).  Closed by direct `simp` — the trajectory is uniform in the
tail since head right excursion = 4 = length of the initial `oz 2` prefix.
Same approach works for any fixed `k`; provides empirical validation and
could serve as a base case for an inductive proof of the general lemma. -/
private lemma setup_phase_R2_k1 (X : Side) :
    srun tm
      ({ state := some stA, head := false,
         left := oz 8 *> blank∞,
         right := oz 2 *> X } : SConfig 6) 254
    = { state := some stA, head := true,
        left := blank∞,
        right := ones 27 *> Side.cons false X } := by
  show srun tm
    ({ state := some stA, head := false,
       left := Side.prepend (oz 8) blank∞,
       right := Side.prepend (oz 2) X } : SConfig 6) 254
    = _
  simp only [oz, Side.prepend]
  simp [srun, sstep, tm, ones, Side.prepend]

-- ============================================================
-- Macro rules
-- ============================================================

/-- **Rule R1 — reset** (`dt = 12 n' + 30`, i.e. `12·(n'+2) + 6`).
`A(n, 0) → A(2, 3n − 4)`, for `n ≥ 2`.

Proof structure (total `12 n' + 30 = 4·(3 n' + 2) + 22`):
- `4·(3 n' + 2)` steps of `left_cycle_iter` consume the left `(01)^(3n'+2)`
  and deposit `cons false (zebra (3n'+2) *> blank)` on the right.
- Rewrite this as `cons false (cons false (cons true (zebra (3n'+1) *> blank)))`
  (peeling `zebra (3n'+2)` via `zebra_succ` and `zebra_succ_append`).
- `22` steps of `phase2` with `T := cons true (zebra (3n'+1) *> blank)` =
  `rightPat (3n'+2) *> blank∞` land us in `A_Config 0 (3n'+2)`. -/
theorem rule_reset (n' : ℕ) :
    srun tm (A_Config n' 0) (12 * n' + 30) = A_Config 0 (3 * n' + 2) := by
  -- The left block is `oz (3n'+2)`, which has `3n'+2 ≥ 2` pairs.
  -- Split the step count: `12 n' + 30 = 4 * (3 n' + 2) + 22`.
  rw [show (12 * n' + 30 : ℕ) = 4 * (3 * n' + 2) + 22 from by ring]
  -- Unfold `A_Config n' 0` and pattern-match the right side with `cons false`.
  show srun tm
    ({ state := some stA, head := false,
       left := oz (3 * n' + 2) *> blank∞,
       right := rightPat 0 *> blank∞ } : SConfig 6) _
    = _
  rw [show (rightPat 0 *> blank∞ : Side) = Side.cons false blank∞ from by
        simp [rightPat, Side.cons_false_blank]]
  rw [srun_add, left_cycle_iter (3 * n' + 2) blank∞ blank∞]
  -- Rewrite the right as `cons false (cons false (cons true (zebra (3n'+1) *> blank∞)))`.
  rw [show (zebra (3 * n' + 2) : List Sym) = false :: true :: zebra (3 * n' + 1) from by
        show zebra ((3 * n' + 1) + 1) = _
        rw [zebra_succ]]
  rw [show (Side.prepend (false :: true :: zebra (3 * n' + 1)) blank∞ : Side)
        = Side.cons false (Side.cons true (zebra (3 * n' + 1) *> blank∞)) from rfl]
  rw [phase2 (Side.cons true (zebra (3 * n' + 1) *> blank∞))]
  -- Goal is now `_ = A_Config 0 (3 n' + 2)`, closed by definitional unfolding
  -- of `rightPat (3 n' + 2) = true :: zebra (3 n' + 1)`.
  show _ = ({state := some stA, head := false,
             left := oz 2 *> blank∞,
             right := Side.prepend (rightPat (3 * n' + 1 + 1)) blank∞} : SConfig 6)
  rfl

/-- **Rule R2 — even** (`dt = 72 k² + 156 k + 54`, i.e.
`72·(k+1)² + 12·(k+1) − 30`).  `A(2n, m) → A(3n, m − 2)` for `n = k + 1 ≥ 1`,
`m ≥ 2`.  Independent of `m`.

**Proof structure** (reduces to the single open lemma `setup_phase_R2`):
- Total `dt = 72k² + 156k + 54 = (72k² + 138k + 44) + (18k + 10)`.
- First `72k² + 138k + 44` steps: `setup_phase_R2` transforms the
  initial A_Config into the AE-sweep input shape.
- Last `18k + 10` steps: `ae_sweep (9k + 4)` consumes `ones (18k+9)`
  and deposits `oz (9k+5) = oz (3(3k+1)+2)` on the left, giving
  `A_Config (3k+1) m`. -/
theorem rule_even (k m : ℕ) :
    srun tm (A_Config (2 * k) (m + 2)) (72 * k * k + 156 * k + 54)
      = A_Config (3 * k + 1) m := by
  -- Split `dt = (72k² + 138k + 44) + (18k + 10)`.
  rw [show (72 * k * k + 156 * k + 54 : ℕ)
        = (72 * k * k + 138 * k + 44) + (18 * k + 10) from by ring]
  -- Decompose `rightPat (m + 2) = oz 2 ++ rightPat m` on the right.
  have hR : (rightPat (m + 2) *> blank∞ : Side)
          = Side.prepend (oz 2) (rightPat m *> blank∞) := by
    cases m with
    | zero => simp [rightPat, oz, Side.cons_false_blank]
    | succ m' =>
      show Side.prepend (true :: zebra (m' + 2)) blank∞ = _
      rw [show zebra (m' + 2) = [false, true, false, true] ++ zebra m' from by
            show zebra ((m' + 1) + 1) = _; rw [zebra_succ, zebra_succ]; rfl]
      rfl
  show srun tm
    ({ state := some stA, head := false,
       left := oz (3 * (2 * k) + 2) *> blank∞,
       right := rightPat (m + 2) *> blank∞ } : SConfig 6)
    ((72 * k * k + 138 * k + 44) + (18 * k + 10))
    = { state := some stA, head := false,
        left := oz (3 * (3 * k + 1) + 2) *> blank∞,
        right := rightPat m *> blank∞ }
  rw [show (3 * (2 * k) + 2 : ℕ) = 6 * k + 2 from by ring, hR]
  rw [srun_add, setup_phase_R2 k (rightPat m *> blank∞)]
  -- Now apply ae_sweep (9k + 4).  Need `18k + 10 = 2 * (9k + 4) + 2`
  -- and `ones (18k + 9) = ones (2 * (9k + 4) + 1)`.
  rw [show (18 * k + 10 : ℕ) = 2 * (9 * k + 4) + 2 from by ring,
      show (18 * k + 9 : ℕ) = 2 * (9 * k + 4) + 1 from by ring,
      ae_sweep (9 * k + 4) blank∞ (Side.cons false (rightPat m *> blank∞))]
  -- Match final config.
  simp only [Side.head_cons, Side.tail_cons]
  show _ = ({ state := some stA, head := false,
              left := oz (3 * (3 * k + 1) + 2) *> blank∞,
              right := rightPat m *> blank∞ } : SConfig 6)
  rw [show (3 * (3 * k + 1) + 2 : ℕ) = 9 * k + 4 + 1 from by ring]

/-- **R2 setup phase (k = 0).**  44 steps transform the initial R2 `k=0`
config (left `oz 2`, right `[T,F,T,F] *> X`) into the canonical
AE-sweep input: state A head=true, blank left, right = `ones 9 *>
cons false X`.  Uniform in the tail `X`.  Used by `rule_even_base`.

The analogous `setup_phase_R2_k` for general `k` takes `72k²+138k+44`
steps, produces `ones (18k+9) *> cons false X` on the right, and is
the critical open lemma for `rule_even`. -/
private lemma setup_phase_R2_k0 (X : Side) :
    srun tm
      ({ state := some stA, head := false,
         left := Side.cons true (Side.cons false (Side.cons true (Side.cons false blank∞))),
         right := Side.cons true (Side.cons false
                    (Side.cons true (Side.cons false X))) } : SConfig 6) 44
    = { state := some stA, head := true,
        left := blank∞,
        right := ones 9 *> Side.cons false X } := by
  simp [srun, sstep, tm, ones, Side.prepend]

/-- Base case `k = 0`: `A(2, m+2) → A(3, m)` in 54 steps, any `m`.

Decomposition: 44 steps of `setup_phase_R2_k0` + 10 steps of
`ae_sweep 4`.  Tail-uniform proof: the head excursion during these 54
steps is bounded, so the trajectory depends only on the first
`[true, false, true, false]` prefix of the right tape (uniform across
`m`) and leaves the rest intact. -/
theorem rule_even_base (m : ℕ) :
    srun tm (A_Config 0 (m + 2)) 54 = A_Config 1 m := by
  -- `rightPat (m + 2) = T :: F :: T :: F :: rightPat m` as lists.
  have hR : (rightPat (m + 2) *> blank∞ : Side)
          = Side.cons true (Side.cons false (Side.cons true (Side.cons false
              (rightPat m *> blank∞)))) := by
    cases m with
    | zero => simp [rightPat, Side.prepend, Side.cons_false_blank]
    | succ m' =>
      simp only [rightPat]
      show Side.prepend (true :: zebra (m' + 2)) blank∞ = _
      rw [show zebra (m' + 2) = [false, true, false, true] ++ zebra m' from by
            show zebra (m' + 1 + 1) = _; rw [zebra_succ, zebra_succ]; rfl]
      rfl
  -- Left: oz 2 *> blank = [T,F,T,F] *> blank.
  show srun tm ({ state := some stA, head := false,
                  left := oz (3 * 0 + 2) *> blank∞,
                  right := rightPat (m + 2) *> blank∞ } : SConfig 6) 54
     = { state := some stA, head := false,
         left := oz (3 * 1 + 2) *> blank∞,
         right := rightPat m *> blank∞ }
  rw [show (oz (3 * 0 + 2) *> blank∞ : Side)
        = Side.cons true (Side.cons false (Side.cons true (Side.cons false blank∞))) from rfl]
  rw [hR]
  -- Split 54 = 44 + 10 and apply setup + ae_sweep 4.
  rw [show (54 : ℕ) = 44 + (2 * 4 + 2) from rfl, srun_add,
      setup_phase_R2_k0 (rightPat m *> blank∞),
      ae_sweep 4 blank∞ (Side.cons false (rightPat m *> blank∞))]
  simp [Side.tail_cons]

-- ============================================================
-- R3 infrastructure
-- ============================================================

/-- `oz (a+b) = oz a ++ oz b` (as lists).  Matches `oz_append`. -/
private lemma oz_split (a b : ℕ) : oz (a + b) = oz a ++ oz b :=
  (oz_append a b).symm

/-- **R3 initial 16 steps.**  From `A_Config (2k+1) (m+1)`-like initial
(with `oz 5` prefix on left over abstract tail `L` and abstract right
tail `Y`), reaches state D with `L` on left and `ones 6 *> cons false
(ones 4 *> cons false Y)` on right. -/
private lemma initial_16_R3 (L Y : Side) :
    srun tm
      ({ state := some stA, head := false,
         left := Side.prepend (oz 5) L,
         right := Side.cons true (Side.cons false Y) } : SConfig 6) 16
    = { state := some stD, head := false,
        left := L,
        right := Side.prepend (ones 6) (Side.cons false
                 (Side.prepend (ones 4) (Side.cons false Y))) } := by
  simp [srun, sstep, tm, ones, oz]

/-- **R3 prelude.**  `12k + 19` steps from R3's initial config to the
first "A,1,left-blank" event state.  Decomposes as `initial_16_R3` +
`cyclic_rest (6k) 6`. -/
private lemma prelude_R3 (k : ℕ) (Y : Side) :
    srun tm
      ({ state := some stA, head := false,
         left := oz (6*k+5) *> blank∞,
         right := Side.cons true (Side.cons false Y) } : SConfig 6) (12*k + 19)
    = { state := some stA, head := true, left := blank∞,
        right := Side.prepend (ones (12*k+7)) (Side.cons false
                 (Side.prepend (ones 4) (Side.cons false Y))) } := by
  have hL : (oz (6*k+5) *> blank∞ : Side)
          = Side.prepend (oz 5) (oz (6*k) *> blank∞) := by
    show Side.prepend (oz (6*k+5)) blank∞ = _
    rw [show (6*k+5 : ℕ) = 5 + (6*k) from by ring,
        show oz (5 + 6*k) = oz 5 ++ oz (6*k) from oz_split 5 (6*k),
        Side.prepend_append]
  rw [hL,
      show (12*k + 19 : ℕ) = 16 + (2*(6*k) + 3) from by ring,
      srun_add, initial_16_R3 (oz (6*k) *> blank∞) Y,
      cyclic_rest (6*k) 6 (Side.prepend (ones 4) (Side.cons false Y))]
  show ({ state := _, left := _, head := _,
          right := Side.prepend (ones (2*(6*k) + 6 + 1)) _ } : SConfig 6) = _
  rw [show (2 * (6*k) + 6 + 1 : ℕ) = 12*k + 7 from by ring]

/-- **R3 post-inner-loop phase 1.**  12 steps from last inner-loop event
`ones 1 *> cons false (ones (m+1) *> cons false X)` to `ones (m+3) *>
cons false X`.  Uniform in `m`, `X`. -/
private lemma phase_post_R3_1 (m : ℕ) (X : Side) :
    srun tm
      ({ state := some stA, head := true, left := blank∞,
         right := Side.cons true (Side.cons false
                  (Side.prepend (ones (m+1)) (Side.cons false X))) } : SConfig 6) 12
    = { state := some stA, head := true, left := blank∞,
        right := Side.prepend (ones (m+3)) (Side.cons false X) } := by
  simp [srun, sstep, tm, ones]

/-- **R3 post-inner-loop.**  `18k + 28` steps from last inner-loop event
(`ones 1` leading, `ones (18k+13)` inner, tail `cons false X`) to the
final `A_Config` shape (state A head=0, left `oz (9k+8)`, right `X`).
Decomposition: `phase_post_R3_1` (12 steps) + `ae_sweep (9k+7)`
(`18k+16` steps) to absorb the big ones block and produce the final
oz on left. -/
private lemma post_inner_loop_R3 (k : ℕ) (X : Side) :
    srun tm
      ({ state := some stA, head := true, left := blank∞,
         right := Side.prepend (ones 1) (Side.cons false
                  (Side.prepend (ones (18*k+13)) (Side.cons false X))) } : SConfig 6) (18*k + 28)
    = { state := some stA, head := false,
        left := oz (9*k+8) *> blank∞,
        right := X } := by
  rw [show (Side.prepend (ones 1) (Side.cons false _) : Side)
        = Side.cons true (Side.cons false
          (Side.prepend (ones (18*k+13)) (Side.cons false X))) from rfl,
      show (18*k + 28 : ℕ) = 12 + (2*(9*k+7) + 2) from by ring,
      srun_add,
      show (18*k+13 : ℕ) = (18*k+12) + 1 from by ring,
      phase_post_R3_1 (18*k+12) X,
      show (18*k+12 + 3 : ℕ) = 2*(9*k+7) + 1 from by ring,
      ae_sweep (9*k+7) blank∞ (Side.cons false X)]
  simp only [Side.head_cons, Side.tail_cons]

/-- **R3 setup** (composes prelude_R3 + inner_loop_iter + post_inner_loop_R3).
Takes `A_Config (2k+1) (m+1)`-like input with abstract tail `X` and
produces the `A_Config (3k+2) m`-shape output in `72k² + 192k + 110`
steps. -/
private lemma setup_phase_R3 (k : ℕ) (X : Side) :
    srun tm
      ({ state := some stA, head := false,
         left := oz (6*k+5) *> blank∞,
         right := Side.cons true (Side.cons false X) } : SConfig 6) (72*k*k + 192*k + 110)
    = { state := some stA, head := false,
        left := oz (9*k+8) *> blank∞,
        right := X } := by
  have h1 : 72*k*k + 192*k + 110
         = (12*k + 19) + (4*(6*k+2)*(6*k+3) + 19*(6*k+3) - 2*(6*k+3)*(6*k+3))
         + (18*k + 28) := by
    have hle : 2*(6*k+3)*(6*k+3) ≤ 4*(6*k+2)*(6*k+3) + 19*(6*k+3) := by nlinarith
    zify [hle]; ring
  rw [h1]
  rw [show ((12*k + 19) + (4*(6*k+2)*(6*k+3) + 19*(6*k+3) - 2*(6*k+3)*(6*k+3))
         + (18*k + 28) : ℕ)
        = (12*k + 19) + ((4*(6*k+2)*(6*k+3) + 19*(6*k+3) - 2*(6*k+3)*(6*k+3))
          + (18*k + 28)) from by omega]
  rw [srun_add, prelude_R3 k X, srun_add]
  have hI : (6*k+3) ≤ (6*k+2) + 1 := by omega
  rw [show (12*k + 7 : ℕ) = 2*(6*k+2) + 3 from by ring,
      show (4 : ℕ) = 3 + 1 from rfl,
      inner_loop_iter (6*k+3) (6*k+2) 3 hI (Side.cons false X)]
  rw [show (2 * (6*k+2) + 3 - 2 * (6*k+3) : ℕ) = 1 from by omega,
      show (3 + 3 * (6*k+3) + 1 : ℕ) = 18*k + 13 from by ring]
  exact post_inner_loop_R3 k X

/-- **Rule R3 — odd** (`dt = 72 k² + 192 k + 110`).  Fully proved via
`setup_phase_R3`.  `A(2n + 1, m) → A(3n + 1, m − 1)` for `n = k + 1 ≥ 1`,
`m ≥ 1`. -/
theorem rule_odd (k m : ℕ) :
    srun tm (A_Config (2 * k + 1) (m + 1)) (72 * k * k + 192 * k + 110)
      = A_Config (3 * k + 2) m := by
  have hR : (rightPat (m + 1) *> blank∞ : Side)
          = Side.cons true (Side.cons false (rightPat m *> blank∞)) := by
    cases m with
    | zero => simp [rightPat, Side.cons_false_blank]
    | succ m' =>
      show Side.prepend (true :: zebra (m' + 1)) blank∞ = _
      rw [show zebra (m' + 1) = [false, true] ++ zebra m' from by rw [zebra_succ]; rfl]
      rfl
  show srun tm ({ state := some stA, head := false,
                  left := oz (3 * (2*k+1) + 2) *> blank∞,
                  right := rightPat (m + 1) *> blank∞ } : SConfig 6) (72 * k * k + 192 * k + 110)
     = { state := some stA, head := false,
         left := oz (3 * (3*k+2) + 2) *> blank∞,
         right := rightPat m *> blank∞ }
  rw [show (3 * (2*k+1) + 2 : ℕ) = 6*k+5 from by ring,
      show (3 * (3*k+2) + 2 : ℕ) = 9*k+8 from by ring, hR]
  exact setup_phase_R3 k (rightPat m *> blank∞)

set_option maxRecDepth 2000 in
/-- Base case `k = 0`: `A(3, m+1) → A(4, m)` in 110 steps, any `m`.

Tail-uniform proof (right excursion = 2): the first two cells of right
`[true, false]` are uniform across `m`; the rest is `rightPat m` which
is preserved. -/
theorem rule_odd_base (m : ℕ) :
    srun tm (A_Config 1 (m + 1)) 110 = A_Config 2 m := by
  have hR : (rightPat (m + 1) *> blank∞ : Side)
          = Side.cons true (Side.cons false (rightPat m *> blank∞)) := by
    cases m with
    | zero => simp [rightPat, Side.prepend, Side.cons_false_blank]
    | succ m' =>
      simp only [rightPat]
      show Side.prepend (true :: zebra (m' + 1)) blank∞ = _
      rw [show zebra (m' + 1) = [false, true] ++ zebra m' from by
            rw [zebra_succ]; rfl]
      rfl
  show srun tm ({ state := some stA, head := false,
                  left := oz (3 * 1 + 2) *> blank∞,
                  right := rightPat (m + 1) *> blank∞ } : SConfig 6) 110
     = { state := some stA, head := false,
         left := oz (3 * 2 + 2) *> blank∞,
         right := rightPat m *> blank∞ }
  rw [hR]
  show srun tm ({ state := some stA, head := false,
                  left := Side.prepend (oz 5) blank∞,
                  right := _ } : SConfig 6) 110
     = { state := some stA, head := false,
         left := Side.prepend (oz 8) blank∞,
         right := _ }
  simp only [oz, Side.prepend]
  simp [srun, sstep, tm]

-- ============================================================
-- R4 infrastructure
-- ============================================================

/-- **R4 prelude (takes abstract `Y2`).**  Same trajectory as `prelude_R2`
(12k+13 steps) but with abstract right-side-2+ tail `Y2`.  For R4's input
the right is `cons true blank = cons true (cons false blank)`, matching
this form with `Y2 = blank`. -/
private lemma prelude_R2_gen (k : ℕ) (Y2 : Side) :
    srun tm
      ({ state := some stA, head := false,
         left := oz (6*k+2) *> blank∞,
         right := Side.cons true (Side.cons false Y2) } : SConfig 6) (12*k + 13)
    = { state := some stA, head := true, left := blank∞,
        right := Side.prepend (ones (12*k+1)) (Side.cons false
                 (Side.prepend (ones 4) (Side.cons false Y2))) } := by
  have hL : (oz (6*k+2) *> blank∞ : Side)
          = Side.cons true (Side.cons false (Side.cons true (Side.cons false
          (oz (6*k) *> blank∞)))) := by
    show Side.prepend (oz (6*k+2)) blank∞ = _
    rw [show (6*k+2 : ℕ) = (6*k) + 2 from by ring]; rfl
  rw [hL,
      show (12*k + 13 : ℕ) = 9 + (1 + (2*(6*k) + 3)) from by ring,
      srun_add, initial_9 (oz (6*k) *> blank∞) Y2, srun_add]
  have hCD : srun tm
      ({ state := some stC, head := true,
         left := Side.cons false (oz (6*k) *> blank∞),
         right := Side.prepend (ones 4) (Side.cons false Y2) } : SConfig 6) 1
      = { state := some stD, head := false,
          left := oz (6*k) *> blank∞,
          right := Side.cons false (Side.prepend (ones 4) (Side.cons false Y2)) } := by
    simp [srun, sstep, tm]
  rw [hCD,
      show (Side.cons false (Side.prepend (ones 4) (Side.cons false Y2)) : Side)
        = Side.prepend (ones 0) (Side.cons false (Side.prepend (ones 4) (Side.cons false Y2))) from rfl,
      cyclic_rest (6*k) 0 (Side.prepend (ones 4) (Side.cons false Y2))]
  congr 1
  show Side.prepend (ones (2 * (6 * k) + 0 + 1)) _ = Side.prepend (ones (12*k+1)) _
  rw [show (2 * (6 * k) + 0 + 1 : ℕ) = 12*k + 1 from by ring,
      show (Side.prepend (ones (12*k+1)) (Side.prepend (ones 0) (Side.cons false
             (Side.prepend (ones 4) (Side.cons false Y2)))) : Side)
        = Side.prepend (ones (12*k+1)) (Side.cons false
             (Side.prepend (ones 4) (Side.cons false Y2))) from by
        show Side.prepend (ones (12*k+1)) (Side.prepend [] _) = _
        rw [Side.prepend_nil]]

/-- **R4 halt endgame** (`18k + 21` steps, including the halt step): from
the last inner-loop event state (`ones 1` leading, `ones (18k+4)` inner,
trailing blank), reaches halt state via `phase_A` + `phase_B` +
`ae_sweep (9k+2)` + 3 fixed transitions ending in `F,0 → ---`. -/
private lemma halt_endgame_R4 (k : ℕ) :
    (srun tm
      ({ state := some stA, head := true, left := blank∞,
         right := Side.prepend (ones 1) (Side.cons false
                  (Side.prepend (ones (18*k+4)) blank∞)) } : SConfig 6) (18*k + 21)).state = none := by
  rw [show (18*k + 21 : ℕ) = 5 + (7 + ((2*(9*k+2) + 2) + 3)) from by ring,
      show (Side.prepend (ones 1) (Side.cons false _) : Side)
        = Side.cons true (Side.cons false
          (Side.prepend (ones (18*k+4)) blank∞)) from rfl,
      srun_add,
      show (18*k+4 : ℕ) = (18*k+3) + 1 from by ring,
      phase_A (18*k+3) blank∞,
      srun_add,
      phase_B (18*k+3) blank∞]
  -- Now: {A, true, blank, ones (18k+6) *> blank}. ones (18k+6) = ones (2*(9k+2)+1) *> cons true blank.
  rw [show (Side.prepend (ones (18*k+3 + 3)) blank∞ : Side)
        = Side.prepend (ones (2*(9*k+2) + 1)) (Side.cons true blank∞) from by
        rw [show (18*k+3 + 3 : ℕ) = (2*(9*k+2)+1) + 1 from by ring,
            show ones ((2*(9*k+2)+1)+1) = ones (2*(9*k+2)+1) ++ [true] from by
              rw [show ones ((2*(9*k+2)+1)+1) = ones (2*(9*k+2)+1) ++ ones 1 from (ones_append _ _).symm]; rfl,
            Side.prepend_append]; rfl,
      srun_add, ae_sweep (9*k+2) blank∞ (Side.cons true blank∞)]
  simp only [Side.head_cons, Side.tail_cons]
  -- After ae_sweep: {A, true, oz (9k+3) *> blank, blank}.
  -- 3 steps: A,1→0RE, E,0→1RF, F,0→HALT.
  show (srun tm ({ state := some stA, head := true,
                   left := oz (9*k+2 + 1) *> blank∞, right := blank∞ } : SConfig 6) 3).state = none
  simp [srun, sstep, tm, ones]

/-- **Rule R4 — halt** (`dt + 1 = 72 k² + 120 k + 34`, where `dt` is the
last-alive-step count and the halt step registers `state = none`).
Fully proved via `prelude_R2_gen` (generalized prelude with `Y2 = blank`)
+ `inner_loop_iter` + `halt_endgame_R4`. -/
theorem rule_halt (k : ℕ) :
    (srun tm (A_Config (2 * k) 1) (72 * k * k + 120 * k + 34)).state = none := by
  -- A_Config (2k) 1 has left = oz (6k+2), right = rightPat 1 = cons true blank
  --                           = cons true (cons false blank) (simp), matching prelude_R2_gen with Y2 = blank.
  have hR1 : (rightPat 1 *> blank∞ : Side) = Side.cons true (Side.cons false blank∞) := by
    simp [rightPat, Side.cons_false_blank]
  show (srun tm ({ state := some stA, head := false,
                   left := oz (3 * (2*k) + 2) *> blank∞,
                   right := rightPat 1 *> blank∞ } : SConfig 6) (72*k*k + 120*k + 34)).state = none
  rw [show (3 * (2*k) + 2 : ℕ) = 6*k + 2 from by ring, hR1]
  -- Case on k.
  match k with
  | 0 =>
    -- k=0: 34 steps = 13 prelude + 0 inner + 21 halt.
    rw [show (72*0*0 + 120*0 + 34 : ℕ) = (12*0 + 13) + (18*0 + 21) from by ring,
        srun_add, prelude_R2_gen 0 blank∞]
    simp only [Side.cons_false_blank]
    exact halt_endgame_R4 0
  | k' + 1 =>
    -- k'+1 case: prelude + inner_loop + halt_endgame.
    have h1 : 72*(k'+1)*(k'+1) + 120*(k'+1) + 34
           = (12*(k'+1) + 13)
           + (4 * (6*k'+5) * (6*k'+6) + 19 * (6*k'+6) - 2 * (6*k'+6) * (6*k'+6))
           + (18*(k'+1) + 21) := by
      have hle : 2*(6*k'+6)*(6*k'+6) ≤ 4*(6*k'+5)*(6*k'+6) + 19*(6*k'+6) := by nlinarith
      zify [hle]; ring
    rw [h1,
        show ((12*(k'+1) + 13)
            + (4 * (6*k'+5) * (6*k'+6) + 19 * (6*k'+6) - 2 * (6*k'+6) * (6*k'+6))
            + (18*(k'+1) + 21) : ℕ)
          = (12*(k'+1) + 13) +
            ((4 * (6*k'+5) * (6*k'+6) + 19 * (6*k'+6) - 2 * (6*k'+6) * (6*k'+6))
            + (18*(k'+1) + 21)) from by omega]
    rw [srun_add, prelude_R2_gen (k'+1) blank∞]
    simp only [Side.cons_false_blank]
    rw [srun_add]
    have hI : (6*k'+6) ≤ (6*k'+5) + 1 := by omega
    rw [show (12*(k'+1) + 1 : ℕ) = 2*(6*k'+5) + 3 from by ring,
        show (4 : ℕ) = 3 + 1 from rfl,
        inner_loop_iter (6*k'+6) (6*k'+5) 3 hI blank∞]
    rw [show (2 * (6*k'+5) + 3 - 2 * (6*k'+6) : ℕ) = 1 from by omega,
        show (3 + 3 * (6*k'+6) + 1 : ℕ) = 18*(k'+1) + 4 from by ring]
    exact halt_endgame_R4 (k'+1)

/-- Base case `k = 0`: `A(2, 1) → halt` in 34 steps. -/
theorem rule_halt_base :
    (srun tm (A_Config 0 1) 34).state = none := by
  show (srun tm ({ state := some stA, head := false,
                   left := oz (3 * 0 + 2) *> blank∞,
                   right := rightPat 1 *> blank∞ } : SConfig 6) 34).state = none
  show (srun tm ({ state := some stA, head := false,
                   left := Side.prepend (oz 2) blank∞,
                   right := Side.prepend (rightPat 1) blank∞ } : SConfig 6) 34).state = none
  simp only [oz, rightPat, zebra, Side.prepend]
  simp [srun, sstep, tm]

-- ============================================================
-- Initial reach from blank
-- ============================================================

/-- From the blank tape, in 22 steps the machine reaches `A(2, 0)`.  Immediate
corollary of `phase2` with `T := blank∞`, since `sinitConfig 6` differs from
`phase2`'s input only by the simp-absorbable identity `cons false blank = blank`. -/
theorem init_to_A_20 :
    srun tm (sinitConfig 6) 22 = A_Config 0 0 := by
  show srun tm
    ({ state := some stA, head := false,
       left := blank∞,
       right := blank∞ } : SConfig 6) 22 = A_Config 0 0
  have h := phase2 blank∞
  simp only [Side.cons_false_blank] at h
  unfold A_Config
  simp only [show (rightPat 0 *> blank∞ : Side) = blank∞ from by simp [rightPat]]
  exact h

-- ============================================================
-- Correspondence: TM halting ↔ macro-rule iteration
-- ============================================================

/-- TM doesn't halt in fewer than 22 steps (= init-reach step count). -/
private lemma no_halt_before_22 : ∀ k < 22, (run tm (initConfig 6) k).state ≠ none := by
  decide


/-- Abstract "macro" state corresponding to wiki's `A(n' + 2, m)`. -/
structure MacroState where
  n' : ℕ
  m : ℕ
  deriving Repr, Inhabited, DecidableEq

/-- One macro-level step.  Returns `none` exactly when the wiki rule
triggers halt (`A(2n, 1) → halt`, i.e., `m = 1` and `n'` even). -/
def nextMacro (s : MacroState) : Option MacroState :=
  if s.m = 0 then
    some { n' := 0, m := 3 * s.n' + 2 }                        -- R1 reset
  else if s.m = 1 ∧ s.n' % 2 = 0 then
    none                                                         -- R4 halt
  else if s.n' % 2 = 0 then
    some { n' := 3 * (s.n' / 2) + 1, m := s.m - 2 }             -- R2 even (m ≥ 2)
  else
    some { n' := 3 * (s.n' / 2) + 2, m := s.m - 1 }             -- R3 odd (m ≥ 1)

/-- Macro-level halting: inductive closure of `nextMacro`. -/
inductive macroHalts : MacroState → Prop where
  | halt (s : MacroState) (h : nextMacro s = none) : macroHalts s
  | step (s s' : MacroState) (h : nextMacro s = some s') (h' : macroHalts s') : macroHalts s

/-- **Simulation theorem.**  For each macro state, running the TM for
specifically many (positive) steps either reaches the next macro state
(if `nextMacro` returns `some`) or halts (if `nextMacro` returns `none`). -/
theorem stm_simulates_macro (n' m : ℕ) :
    ∃ k, k > 0 ∧ (
      match nextMacro ⟨n', m⟩ with
      | some s' => srun tm (A_Config n' m) k = A_Config s'.n' s'.m
      | none    => (srun tm (A_Config n' m) k).state = none) := by
  by_cases h_m0 : m = 0
  · -- R1: reset.
    subst h_m0
    refine ⟨12 * n' + 30, by omega, ?_⟩
    show match nextMacro ⟨n', 0⟩ with | _ => _
    unfold nextMacro
    simp only [if_pos rfl]
    exact rule_reset n'
  · -- m ≥ 1
    have h_m_pos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr h_m0
    by_cases h_m1 : m = 1
    · subst h_m1
      by_cases h_even : n' % 2 = 0
      · -- R4: halt.
        obtain ⟨k, rfl⟩ : ∃ k, n' = 2 * k := ⟨n'/2, by omega⟩
        refine ⟨72 * k * k + 120 * k + 34, by omega, ?_⟩
        show match nextMacro ⟨2 * k, 1⟩ with | _ => _
        unfold nextMacro
        simp only [show ¬((1 : ℕ) = 0) from by decide, if_false,
                   show (2 * k) % 2 = 0 from by omega, and_true, if_pos rfl]
        exact rule_halt k
      · -- R3: odd case, m = 1 going to m = 0.
        obtain ⟨k, rfl⟩ : ∃ k, n' = 2 * k + 1 := ⟨n'/2, by omega⟩
        refine ⟨72 * k * k + 192 * k + 110, by omega, ?_⟩
        show match nextMacro ⟨2 * k + 1, 1⟩ with | _ => _
        unfold nextMacro
        simp only [show ¬((1 : ℕ) = 0) from by decide, if_false,
                   show ¬((2 * k + 1) % 2 = 0) from by omega, and_false, if_false,
                   show (2 * k + 1) / 2 = k from by omega]
        show srun tm (A_Config (2 * k + 1) 1) (72 * k * k + 192 * k + 110)
             = A_Config (3 * k + 2) (1 - 1)
        simpa using rule_odd k 0
    · -- m ≥ 2
      have h_m_ge_2 : 2 ≤ m := by omega
      by_cases h_even : n' % 2 = 0
      · -- R2: even.
        obtain ⟨k, rfl⟩ : ∃ k, n' = 2 * k := ⟨n'/2, by omega⟩
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
        refine ⟨72 * k * k + 156 * k + 54, by omega, ?_⟩
        show match nextMacro ⟨2 * k, m' + 2⟩ with | _ => _
        unfold nextMacro
        simp only [show ¬(m' + 2 = 0) from by omega, if_false,
                   show ¬(m' + 2 = 1) from by omega, false_and, if_false,
                   show (2 * k) % 2 = 0 from by omega, if_pos rfl,
                   show (2 * k) / 2 = k from by omega,
                   show (m' + 2) - 2 = m' from by omega]
        exact rule_even k m'
      · -- R3: odd, m ≥ 2.
        obtain ⟨k, rfl⟩ : ∃ k, n' = 2 * k + 1 := ⟨n'/2, by omega⟩
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        refine ⟨72 * k * k + 192 * k + 110, by omega, ?_⟩
        show match nextMacro ⟨2 * k + 1, m' + 1⟩ with | _ => _
        unfold nextMacro
        simp only [show ¬(m' + 1 = 0) from by omega, if_false,
                   show ¬(m' + 1 = 1) from by omega, false_and, if_false,
                   show ¬((2 * k + 1) % 2 = 0) from by omega, if_false,
                   show (2 * k + 1) / 2 = k from by omega,
                   show (m' + 1) - 1 = m' from by omega]
        exact rule_odd k m'

/-- **SConfig halt equivalence** at macro-config level. -/
theorem stm_halt_iff_macroHalts (n' m : ℕ) :
    (∃ k, (srun tm (A_Config n' m) k).state = none) ↔ macroHalts ⟨n', m⟩ := by
  constructor
  · -- Forward: TM halts (in some k steps) ⇒ macroHalts (strong induction on k).
    rintro ⟨k, hk⟩
    suffices ∀ (n : ℕ) (n' m : ℕ),
        (srun tm (A_Config n' m) n).state = none → macroHalts ⟨n', m⟩ from
      this k n' m hk
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro n' m hk
      have ⟨k_sim, _, h_sim⟩ := stm_simulates_macro n' m
      cases h_next : nextMacro ⟨n', m⟩ with
      | none => exact macroHalts.halt _ h_next
      | some s' =>
        rw [h_next] at h_sim
        -- Reduce the match.
        change srun tm (A_Config n' m) k_sim = A_Config s'.n' s'.m at h_sim
        by_cases h_lt : n < k_sim
        · -- Can't have halted before the simulation step completes.
          exfalso
          have h_alive : (srun tm (A_Config n' m) k_sim).state = some stA := by
            rw [h_sim]; rfl
          have h_halted : (srun tm (A_Config n' m) k_sim).state = none := by
            rw [show k_sim = n + (k_sim - n) from by omega, srun_add, srun_halted _ _ hk]
            exact hk
          exact absurd (h_halted.symm.trans h_alive) (by simp)
        · rw [show n = k_sim + (n - k_sim) from by omega, srun_add, h_sim] at hk
          exact macroHalts.step _ _ h_next (ih (n - k_sim) (by omega) s'.n' s'.m hk)
  · -- Backward: macroHalts ⇒ TM halts (induction on macroHalts).
    intro hmh
    -- Generalize to all macro states, then specialize.
    suffices ∀ s : MacroState, macroHalts s → ∃ k, (srun tm (A_Config s.n' s.m) k).state = none
      from this ⟨n', m⟩ hmh
    intro s hmh'
    induction hmh' with
    | halt s h_none =>
      have ⟨k, _, h_sim⟩ := stm_simulates_macro s.n' s.m
      rw [h_none] at h_sim
      change (srun tm (A_Config s.n' s.m) k).state = none at h_sim
      exact ⟨k, h_sim⟩
    | step s s' h_some _ ih =>
      have ⟨k, _, h_sim⟩ := stm_simulates_macro s.n' s.m
      rw [h_some] at h_sim
      change srun tm (A_Config s.n' s.m) k = A_Config s'.n' s'.m at h_sim
      obtain ⟨k', hk'⟩ := ih
      exact ⟨k + k', by rw [srun_add, h_sim]; exact hk'⟩

/-- **Main correspondence lemma.**  The TM halts from the blank tape
if and only if the macro iteration (starting from `A(2, 0) = A_Config 0 0`)
eventually reaches a halt state (`A(2n, 1)` for some `n ≥ 1`). -/
theorem tm_halt_iff :
    (∃ k, (run tm (initConfig 6) k).state = none) ↔ macroHalts ⟨0, 0⟩ := by
  -- Bridge run/srun.
  have h_bridge : ∀ k, (run tm (initConfig 6) k).state =
                        (srun tm (sinitConfig 6) k).state := fun k => by
    change _ = (srun tm (initConfig 6).toSConfig k).state
    rw [← toSConfig_run]; rfl
  -- TM halts from blank ↔ TM halts from A_Config 0 0 (via init_to_A_20, 22 steps).
  have h_init_iff : (∃ k, (run tm (initConfig 6) k).state = none) ↔
                    (∃ k, (srun tm (A_Config 0 0) k).state = none) := by
    constructor
    · rintro ⟨k, hk⟩
      rw [h_bridge] at hk
      by_cases h_le : 22 ≤ k
      · refine ⟨k - 22, ?_⟩
        rw [show k = 22 + (k - 22) from by omega, srun_add, init_to_A_20] at hk
        exact hk
      · -- Can't have halted in fewer than 22 steps.
        exact absurd (show (run tm (initConfig 6) k).state = none from by
                        rw [h_bridge]; exact hk)
                     (no_halt_before_22 k (by omega))
    · rintro ⟨k, hk⟩
      refine ⟨22 + k, ?_⟩
      rw [h_bridge, srun_add, init_to_A_20]
      exact hk
  rw [h_init_iff, stm_halt_iff_macroHalts 0 0]

/-!
## Wiki-style single-function formulation

The macro map can be packaged as a single partial function
`f : ℕ² → ℕ² ∪ {HALT}` on *wiki coordinates* `(n, m)` (with `n ≥ 2`
on-orbit).  The internal parametrization uses `n' = n - 2`; the
correspondence is shown by `nextMacro_f` below.
-/

/-- Wiki-style macro map.  `none` encodes `HALT`.  See `wiki.txt`. -/
def f : ℕ × ℕ → Option (ℕ × ℕ) := fun ⟨n, m⟩ =>
  if m = 1 ∧ n % 2 = 0 then none
  else if m = 0 then some (2, 3 * n - 4)
  else if n % 2 = 0 then some (3 * n / 2, m - 2)
  else some (3 * (n - 1) / 2 + 1, m - 1)

/-- `k`-fold iteration of `f`; halts (returns `none`) if any step halts. -/
def fIter : ℕ → ℕ × ℕ → Option (ℕ × ℕ)
  | 0,     nm => some nm
  | k + 1, nm => (f nm).bind (fIter k)

/-- **Bridge lemma.**  On wiki coordinates `n = n' + 2`, the wiki map
`f` equals `nextMacro` (up to the `+2` shift on the first component). -/
lemma nextMacro_f (n' m : ℕ) :
    f (n' + 2, m) = (nextMacro ⟨n', m⟩).map (fun s' => (s'.n' + 2, s'.m)) := by
  unfold f nextMacro
  by_cases hm0 : m = 0
  · subst hm0
    simp
    omega
  · by_cases hm1 : m = 1
    · subst hm1
      by_cases hev : n' % 2 = 0
      · have h2ev : (n' + 2) % 2 = 0 := by omega
        simp [h2ev, hev]
      · have h2ev : (n' + 2) % 2 ≠ 0 := by omega
        simp [hev]
        omega
    · have h_m_ge_2 : 2 ≤ m := by omega
      by_cases hev : n' % 2 = 0
      · have h2ev : (n' + 2) % 2 = 0 := by omega
        simp [hm0, hm1, hev]
        omega
      · have h2ev : (n' + 2) % 2 ≠ 0 := by omega
        simp [hm0, hm1, hev]
        omega

/-- Forward direction: `macroHalts ⇒ fIter` hits `none`. -/
private lemma fIter_none_of_macroHalts (s : MacroState) (h : macroHalts s) :
    ∃ k, fIter k (s.n' + 2, s.m) = none := by
  induction h with
  | halt s h_nm =>
    refine ⟨1, ?_⟩
    have hb := nextMacro_f s.n' s.m
    rw [h_nm] at hb
    change f (s.n' + 2, s.m) = none at hb
    show (f (s.n' + 2, s.m)).bind (fIter 0) = none
    rw [hb]; rfl
  | step s s' h_nm _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + 1, ?_⟩
    have hb := nextMacro_f s.n' s.m
    rw [h_nm] at hb
    change f (s.n' + 2, s.m) = some (s'.n' + 2, s'.m) at hb
    show (f (s.n' + 2, s.m)).bind (fIter k) = none
    rw [hb]
    exact hk

/-- Backward direction: `fIter` hits `none` ⇒ `macroHalts`. -/
private lemma macroHalts_of_fIter_none :
    ∀ (k : ℕ) (s : MacroState), fIter k (s.n' + 2, s.m) = none → macroHalts s := by
  intro k
  induction k with
  | zero =>
    intro s h
    exact absurd h (by simp [fIter])
  | succ k ih =>
    intro s h
    have hb := nextMacro_f s.n' s.m
    cases h_nm : nextMacro s with
    | none => exact macroHalts.halt _ h_nm
    | some s' =>
      rw [h_nm] at hb
      change f (s.n' + 2, s.m) = some (s'.n' + 2, s'.m) at hb
      have h' : fIter k (s'.n' + 2, s'.m) = none := by
        have h2 : (f (s.n' + 2, s.m)).bind (fIter k) = none := h
        rw [hb] at h2
        exact h2
      exact macroHalts.step s s' h_nm (ih s' h')

/-- `macroHalts` is equivalent to `fIter` eventually returning `none`
(on wiki coordinates). -/
lemma macroHalts_iff_fIter (s : MacroState) :
    macroHalts s ↔ ∃ k, fIter k (s.n' + 2, s.m) = none := by
  refine ⟨fIter_none_of_macroHalts s, ?_⟩
  rintro ⟨k, hk⟩
  exact macroHalts_of_fIter_none k s hk

/-- **Main correspondence (wiki form).**  The TM halts from the blank
tape iff the wiki iteration of `f` starting at `(2, 0)` eventually
reaches `HALT`. -/
theorem tm_halt_iff_math :
    (∃ k, (run tm (initConfig 6) k).state = none) ↔ ∃ k, fIter k (2, 0) = none := by
  rw [tm_halt_iff]
  exact macroHalts_iff_fIter ⟨0, 0⟩

/-
## Macro orbit (from `sim.py orbit 12`)

  i   n   m   dt         total
  0   2   0   30         30
  1   2   2   54         84      (R1: A(2,0)→A(2,2))
  2   3   0  110        194      (R2: A(2,2)→A(3,0))  wait — check
  …

Wiki starting point: `A(2, 0)`.  Iterate: the next macro configs as
produced by the rules above are exactly the `p = [a, b]` orbit of the
Python recurrence
```
  while b >= 0:
    if b == 0:      p = [2, 3a - 4]
    elif a odd:     p[0] = a//2 * 3 + 1;  p[1] -= 1
    else:           p[0] = a//2 * 3;      p[1] -= 2
```
with `a_0 = 2`, `b_0 = 0`.  Halt iff `b` becomes negative (i.e., `a`
reaches some even value with `b = 1` before a reset fires).

Racheline's Hydra-style reformulation (see `previous-work/wiki.txt`):
```
  a_0 = 2,  a_{i+1} = HydraMap(a_i)  where
    HydraMap(a) = a/2 * 3    if a even
    HydraMap(a) = a/2 * 3+1  if a odd
  b_0 = 0,  b_{i+1} = b_i + (1 if a_i odd else 2)
  c_0 = 0,  c_{i+1} = 3 a_j − 4  where  b_j = c_i
```
i.e. the TM halts iff there exists `i` with `b_i - c_j` hitting `1` on
some even-`a` step that cannot be absorbed by the periodic reset.  In
practice `c` grows super-exponentially — `c_5 ≈ 2.2 × 10^22` — so
finite simulation cannot settle halt/nonhalt.
-/

end Racheline6
