import BusyLean
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open BusyLean

namespace ShiftOv6

/-!
# Shift-overflow 6-state TM `1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE`

Halt/non-halt is **not** the target here; this file collects observed
macro rules for the machine.

## Transition table
|   | 0   | 1   |
|---|-----|-----|
| A | 1RB | 0LC |
| B | 1LC | 0RD |
| C | 1LF | 1LA |
| D | 1LB | 1RE |
| E | 1RB | 1LE |
| F | --- | 0LE |

The only halting transition is `F,0 → ---`, and F is reached only via
`C,0 → 1LF`; halt therefore requires `C` to fire on a `0` with the cell
one to the left also `0`.

## Observed dynamics (from `sim.py`)

The dominant step cycle is `E → B → D → E` (≈ 16k times per 50k
steps), with `E` runs of length 3 (E sweeps left over 2 ones then
fires).  Between rare **E-turnaround** events at the right blank, the
active-region tape block structure evolves:

  step     6:  blocks=[1, 1]
  step    26:  blocks=[2, 2, 1]        (dt =     20)
  step    76:  blocks=[6, 2, 1]        (dt =     50)
  step   190:  blocks=[2, 10, 2, 1]    (dt =    114)
  step   752:  blocks=[2, 25, 2, 1]    (dt =    562)
  step 18240:  blocks=[2, 124, 4, 2, 1] (dt =  17488)

## The local 5-step bump

Zooming in (e.g. steps 48..73), the active tape has the shape
    `… L' 0 1^K 0 1 [E]1 1^j 0 1^M 0 blank∞`
— state E, head on the 2nd cell of the middle 1-block (block 2), with
`j` further 1s in block 2 to the right of head.  Block 2 therefore has
size `j + 2`.  Schematic block sizes: `[K, j+2, M]`.

The 5-step loop transfers one 1 from block 2 to block 1 (via an
E-sweep + E→B→D→E local cycle).  There are two behaviors:

  * **Inner bump** (`j ≥ 1`): `[K, j+2, M] → [K+1, j+1, M]`
     (head stays on 2nd cell of block 2).

  * **Terminal bump** (`j = 0`, block 2 size 2): `[K, 2, M] → [K+1, 1,
     M]` but the head lands on the 0-separator between block 2 and
     block 3 (state E, head = 0).  Captured by `S_Config`.

From the terminal state, a 3-step "finish" (specialised to `M = 2`)
produces the right-blank E-turnaround with blocks `[K+1, 2, 1]`.
-/

def tm : TM 6 := tm! "1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE"

-- Transition simp lemmas
@[simp] private theorem tr_A0 : tm.tr stA false = some (stB, true,  Dir.R) := rfl
@[simp] private theorem tr_A1 : tm.tr stA true  = some (stC, false, Dir.L) := rfl
@[simp] private theorem tr_B0 : tm.tr stB false = some (stC, true,  Dir.L) := rfl
@[simp] private theorem tr_B1 : tm.tr stB true  = some (stD, false, Dir.R) := rfl
@[simp] private theorem tr_C0 : tm.tr stC false = some (stF, true,  Dir.L) := rfl
@[simp] private theorem tr_C1 : tm.tr stC true  = some (stA, true,  Dir.L) := rfl
@[simp] private theorem tr_D0 : tm.tr stD false = some (stB, true,  Dir.L) := rfl
@[simp] private theorem tr_D1 : tm.tr stD true  = some (stE, true,  Dir.R) := rfl
@[simp] private theorem tr_E0 : tm.tr stE false = some (stB, true,  Dir.R) := rfl
@[simp] private theorem tr_E1 : tm.tr stE true  = some (stE, true,  Dir.L) := rfl
@[simp] private theorem tr_F0 : tm.tr stF false = none := rfl
@[simp] private theorem tr_F1 : tm.tr stF true  = some (stE, false, Dir.L) := rfl

-- ============================================================
-- Macro configurations
-- ============================================================

/-- **Inner macro config**: state E, head = 1 on the 2nd cell from left of
    the middle block (block 2).  `K` is block 1's size, `j` is the number
    of 1s in block 2 to the right of head (so block 2 size = `j + 2`),
    `M` is block 3's size, and `L` is the far-left context.

    Tape (L-to-R):  `L' 0 1^K 0 1 [E=1] 1^j 0 1^M 0 blank∞`. -/
def M_Config (L : Side) (K j M : Nat) : SConfig 6 :=
  { state := some stE,
    head  := true,
    left  := [true] *> [false] *> ones K *> [false] *> L,
    right := ones j *> [false] *> ones M *> blank∞ }

/-- **Separator macro config**: state E, head = 0 on the 0 between a
    size-1 block 2 and block 3.

    Tape (L-to-R):  `L' 0 1^K 0 1 [E=0] 1^M 0 blank∞`. -/
def S_Config (L : Side) (K M : Nat) : SConfig 6 :=
  { state := some stE,
    head  := false,
    left  := [true] *> [false] *> ones K *> [false] *> L,
    right := ones M *> blank∞ }

-- ============================================================
-- Simple local shift rules
-- ============================================================

/-- **E-left-sweep over `ones k`**: E,1→1LE loop moves the head left
    across a block of `k` ones in `k` steps, ending on whatever cell
    follows (popped from `L`). -/
lemma E_sweep (k : Nat) (L R : Side) :
    srun tm
      { state := some stE, head := true,
        left  := ones k *> L,
        right := R } (k + 1)
    = { state := some stE, head := Side.head L,
        left  := Side.tail L,
        right := ones (k + 1) *> R } := by
  induction k generalizing L R with
  | zero => simp [srun, sstep, tm]
  | succ k' ih =>
    rw [show (k' + 1 + 1 : Nat) = 1 + (k' + 1) from by ring,
        srun_add]
    have h1 : srun tm
        { state := some stE, head := true,
          left := ones (k' + 1) *> L, right := R } 1
        = { state := some stE, head := true,
            left := ones k' *> L,
            right := Side.cons true R } := by
      simp [srun, sstep, tm]
    rw [h1, ih L (Side.cons true R)]
    congr 1
    show Side.prepend (ones (k' + 1)) (Side.cons true R) =
         Side.prepend (ones (1 + (k' + 1))) R
    rw [show (1 + (k' + 1) : Nat) = (k' + 1) + 1 from by ring,
        show ones (k' + 1 + 1) = ones (k' + 1) ++ [true] from by
          simp [ones, List.replicate_succ'],
        Side.prepend_append]
    rfl

/-- **3-step BDE-cycle**: state E head=0 with two 1s to the right →
    write `1 0 1` leftward of the new head position, state E at the
    following cell. -/
lemma BDE_cycle3 (L R : Side) :
    srun tm
      { state := some stE, head := false,
        left  := L,
        right := [true, true] *> R } 3
    = { state := some stE, head := Side.head R,
        left  := [true, false, true] *> L,
        right := Side.tail R } := by
  simp [srun, sstep, tm]

-- ============================================================
-- 5-step bump: inner and terminal cases
-- ============================================================

/-- **Inner bump** (`j ≥ 1`): one full 5-step cycle.  Transfers a 1
    from block 2 to block 1, head stays on the 2nd cell of the new
    block 2.

    Block count: `[K, j+2, M] → [K+1, j+1, M]` in 5 steps.

    Proof: direct 5-step simp.  The only reason we need `j + 1` (not
    an arbitrary `j`) is that in the 5th step (D,1→1RE) the head must
    find a `1` to the right of block 2's new boundary — which is there
    iff `j ≥ 1` (equivalently the middle block has size ≥ 3). -/
theorem bump5 (L : Side) (K j M : Nat) :
    srun tm (M_Config L K (j + 1) M) 5
    = M_Config L (K + 1) j M := by
  simp [M_Config, srun, sstep, tm]

/-- **Terminal bump**: the last 5-step cycle when block 2 has size 2
    (i.e. `j = 0`).  The head lands on the 0 between the size-1 block 2
    and block 3.

    Block count: `[K, 2, M] → [K+1, 1, M]` in 5 steps. -/
theorem bump5_term (L : Side) (K M : Nat) :
    srun tm (M_Config L K 0 M) 5
    = S_Config L (K + 1) M := by
  simp [M_Config, S_Config, srun, sstep, tm]

-- ============================================================
-- Iterated inner bump
-- ============================================================

/-- **Iterated inner bump**: applying `bump5` `n` times transfers `n`
    ones from block 2 to block 1.  `[K, j+n+2, M] → [K+n, j+2, M]`
    in `5n` steps. -/
theorem bump5_iter (L : Side) (K j M n : Nat) :
    srun tm (M_Config L K (j + n) M) (5 * n)
    = M_Config L (K + n) j M := by
  induction n generalizing K j with
  | zero => simp [M_Config]
  | succ n' ih =>
    rw [show j + (n' + 1) = (j + n') + 1 from by ring,
        show 5 * (n' + 1) = 5 + 5 * n' from by ring,
        srun_add, bump5, ih (K + 1) j,
        show K + 1 + n' = K + (n' + 1) from by ring]

/-- Combined iteration + terminal: from `M_Config L K n M` (block 2
    size `n + 2`), iterate `n` inner bumps and then the terminal to
    reach `S_Config L (K + n + 1) M` in `5(n+1)` steps. -/
theorem bump5_iter_term (L : Side) (K M n : Nat) :
    srun tm (M_Config L K n M) (5 * (n + 1))
    = S_Config L (K + n + 1) M := by
  rw [show 5 * (n + 1) = 5 * n + 5 from by ring, srun_add]
  have h := bump5_iter L K 0 M n
  rw [show (0 + n : Nat) = n from by ring] at h
  rw [h, bump5_term]

-- ============================================================
-- First E-turnaround from the blank tape
-- ============================================================

/-- Config-form at step 6 from the blank tape. -/
def Init_Config_6 : Config 6 :=
  { state := some stE,
    head  := false,
    left  := [true, false, true],
    right := [] }

/-- From blank, in 6 steps we reach the first E-right-blank event. -/
lemma init_to_Init_Config_6 :
    run tm (initConfig 6) 6 = Init_Config_6 := by
  decide

def SInit_6 : SConfig 6 :=
  { state := some stE,
    head  := false,
    left  := [true, false, true] *> blank∞,
    right := blank∞ }

lemma Init_Config_6_toSConfig :
    Init_Config_6.toSConfig = SInit_6 := by
  simp [Init_Config_6, SInit_6, Config.toSConfig]

/-- Stream version: from blank, 6 steps reach `SInit_6` (blocks `[1, 1]`,
    E at right blank). -/
theorem init_to_SInit_6 :
    srun tm (sinitConfig 6) 6 = SInit_6 := by
  have h := congrArg Config.toSConfig init_to_Init_Config_6
  rw [toSConfig_run, toSConfig_initConfig, Init_Config_6_toSConfig] at h
  exact h

-- ============================================================
-- Bridge: blank tape → first M_Config
-- ============================================================

/-- Config-form at step 48: the first moment the tape matches the
    `M_Config` macro shape.  Tape reads
        `blank∞ 1 0 1 [E=1]1 1 1 1 0 1 1 blank∞`
    (blocks `[1, 6, 2]`, head on 2nd cell of block 2). -/
def Init_Config_48 : Config 6 :=
  { state := some stE,
    head  := true,
    left  := [true, false, true],
    right := [true, true, true, true, false, true, true] }

/-- From the blank tape, in 48 steps we reach `Init_Config_48`. -/
lemma init_to_Init_Config_48 :
    run tm (initConfig 6) 48 = Init_Config_48 := by
  decide

/-- The corresponding `M_Config`: `K = 1`, `j = 4`, `M = 2`, with
    `L = blank∞`. -/
lemma Init_Config_48_toSConfig :
    Init_Config_48.toSConfig = M_Config blank∞ 1 4 2 := by
  simp [Init_Config_48, M_Config, Config.toSConfig]

/-- **Entry bridge**: from the blank tape, in 48 steps the stream-TM
    reaches `M_Config blank∞ 1 4 2` (blocks `[1, 6, 2]`, head on 2nd
    cell of block 2). -/
theorem init_to_M_Config :
    srun tm (sinitConfig 6) 48 = M_Config blank∞ 1 4 2 := by
  have h := congrArg Config.toSConfig init_to_Init_Config_48
  rw [toSConfig_run, toSConfig_initConfig, Init_Config_48_toSConfig] at h
  exact h

-- ============================================================
-- Finish-from-separator: the 3-step ending at M = 2
-- ============================================================

/-- **Right-blank E-turnaround config** (blocks `[K, 2, 1]`).  State E,
    head = 0 at the right blank, with tape reading
        `L' 0 1^K 0 1 1 0 1 [E=0] blank∞`. -/
def R_Config (L : Side) (K : Nat) : SConfig 6 :=
  { state := some stE,
    head  := false,
    left  := [true] *> [false] *> ones 2 *> [false] *> ones K *> [false] *> L,
    right := blank∞ }

/-- **3-step finish at `M = 2`**: from `S_Config L K 2` (head on
    0-sep, block 3 size 2), the E→B→D→E mini-cycle lands the head at
    the right blank with blocks `[K, 2, 1]`.

    Proof: direct 3-step simp. -/
theorem finish3_M2 (L : Side) (K : Nat) :
    srun tm (S_Config L K 2) 3 = R_Config L K := by
  simp [S_Config, R_Config, srun, sstep, tm]

-- ============================================================
-- Full 5(n+1)+3 macro: M_Config → right-blank E-turnaround
-- ============================================================

/-- **Full macro** (combines `bump5_iter_term` + `finish3_M2`).  From
    `M_Config L K n 2` (block 2 size `n + 2`, block 3 size 2), the
    machine reaches the right-blank E-turnaround config
    `R_Config L (K + n + 1)` (blocks `[K + n + 1, 2, 1]`) in
    `5(n+1) + 3 = 5n + 8` steps. -/
theorem macro_to_R (L : Side) (K n : Nat) :
    srun tm (M_Config L K n 2) (5 * (n + 1) + 3)
    = R_Config L (K + n + 1) := by
  rw [srun_add, bump5_iter_term, finish3_M2]

/-- **End-to-end** from blank to the second observed E-turnaround
    (step 76, blocks `[6, 2, 1]`).  Composition of `init_to_M_Config`
    (48 steps) with `macro_to_R` at `K = 1, n = 4` (28 steps). -/
theorem init_to_R_Config_6 :
    srun tm (sinitConfig 6) 76 = R_Config blank∞ 6 := by
  rw [show (76 : Nat) = 48 + 28 from rfl, srun_add, init_to_M_Config]
  have h := macro_to_R blank∞ 1 4
  rw [show 5 * (4 + 1) + 3 = 28 from rfl,
      show (1 + 4 + 1 : Nat) = 6 from rfl] at h
  exact h

-- ============================================================
-- 4-block E-turnaround (step 190: blocks [2, K, 2, 1])
-- ============================================================

/-- **4-block right-blank E-turnaround**.  State E, head = 0 at the
    right blank, with tape reading
        `L' 0 1^2 0 1^K 0 1^2 0 1 [E=0] blank∞`
    Blocks `[2, K, 2, 1]` (assuming the L-prefix contributes a 0 on
    the immediate left of the size-2 block). -/
def R4_Config (L : Side) (K : Nat) : SConfig 6 :=
  { state := some stE,
    head  := false,
    left  := [true] *> [false] *> ones 2 *> [false] *> ones K *>
             [false] *> ones 2 *> [false] *> L,
    right := blank∞ }

/-- Config-form at step 190 (the third E-turnaround).  Blocks
    `[2, 10, 2, 1]`. -/
def Init_Config_190 : Config 6 :=
  { state := some stE,
    head  := false,
    left  := [true, false, true, true, false,
              true, true, true, true, true, true, true, true, true, true,
              false, true, true],
    right := [] }

set_option maxRecDepth 3000 in
/-- From blank, 190 steps reach `Init_Config_190`.  Verified by `decide`. -/
lemma init_to_Init_Config_190 :
    run tm (initConfig 6) 190 = Init_Config_190 := by
  decide

/-- `Init_Config_190` lifts to `R4_Config blank∞ 10`. -/
lemma Init_Config_190_toSConfig :
    Init_Config_190.toSConfig = R4_Config blank∞ 10 := by
  simp [Init_Config_190, R4_Config, Config.toSConfig]

/-- **Entry into the 4-block regime** (stream-level): from blank, in
    190 steps we reach `R4_Config blank∞ 10` (blocks `[2, 10, 2, 1]`). -/
theorem init_to_R4_Config_10 :
    srun tm (sinitConfig 6) 190 = R4_Config blank∞ 10 := by
  have h := congrArg Config.toSConfig init_to_Init_Config_190
  rw [toSConfig_run, toSConfig_initConfig, Init_Config_190_toSConfig] at h
  exact h

/-- **Restructure step**: from `R_Config blank∞ 6` (step 76) the
    machine reaches `R4_Config blank∞ 10` (step 190) in 114 steps.

    Specific to `L = blank∞`.  The head travels 16 cells left of its
    step-76 position during the restructure, reading 5 cells beyond
    the original leftmost 1; correctness for other `L` would require
    sufficient blank prefix.  Obtained via determinism of `srun` from
    `init_to_R_Config_6` + `init_to_R4_Config_10`. -/
theorem R_Config_6_to_R4_Config_10 :
    srun tm (R_Config blank∞ 6) 114 = R4_Config blank∞ 10 := by
  have h1 := init_to_R_Config_6
  have h2 := init_to_R4_Config_10
  have h3 : srun tm (sinitConfig 6) (76 + 114) = R4_Config blank∞ 10 := by
    rw [show (76 + 114 : Nat) = 190 from rfl]; exact h2
  rw [srun_add, h1] at h3
  exact h3

-- ============================================================
-- Fourth E-turnaround (step 752: blocks [2, 25, 2, 1])
-- ============================================================

/-- Config-form at step 752.  Blocks `[2, 25, 2, 1]`. -/
def Init_Config_752 : Config 6 :=
  { state := some stE,
    head  := false,
    left  := [true, false, true, true, false] ++
             List.replicate 25 true ++
             [false, true, true],
    right := [] }

set_option maxRecDepth 8000 in
/-- From blank, 752 steps reach `Init_Config_752`.  Verified by `decide`. -/
lemma init_to_Init_Config_752 :
    run tm (initConfig 6) 752 = Init_Config_752 := by
  decide

/-- `Init_Config_752` lifts to `R4_Config blank∞ 25`. -/
lemma Init_Config_752_toSConfig :
    Init_Config_752.toSConfig = R4_Config blank∞ 25 := by
  simp [Init_Config_752, R4_Config, Config.toSConfig, ones]

/-- From blank, in 752 steps we reach `R4_Config blank∞ 25`
    (blocks `[2, 25, 2, 1]`). -/
theorem init_to_R4_Config_25 :
    srun tm (sinitConfig 6) 752 = R4_Config blank∞ 25 := by
  have h := congrArg Config.toSConfig init_to_Init_Config_752
  rw [toSConfig_run, toSConfig_initConfig, Init_Config_752_toSConfig] at h
  exact h

/-- **Second restructure step**: from `R4_Config blank∞ 10` (step 190)
    the machine reaches `R4_Config blank∞ 25` (step 752) in 562
    steps.  Specific to `L = blank∞`. -/
theorem R4_Config_10_to_R4_Config_25 :
    srun tm (R4_Config blank∞ 10) 562 = R4_Config blank∞ 25 := by
  have h1 := init_to_R4_Config_10
  have h2 := init_to_R4_Config_25
  have h3 : srun tm (sinitConfig 6) (190 + 562) = R4_Config blank∞ 25 := by
    rw [show (190 + 562 : Nat) = 752 from rfl]; exact h2
  rw [srun_add, h1] at h3
  exact h3

end ShiftOv6
