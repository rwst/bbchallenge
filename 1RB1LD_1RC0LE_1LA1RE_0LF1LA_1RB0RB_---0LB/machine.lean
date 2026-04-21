import BusyLean
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open BusyLean

namespace Chaotic6

/-!
# Chaotic 6-state TM `1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_---0LB`

The BB(6) candidate known from the wiki as a "shift-overflow counter" with
chaotic block restructuring.  Halt/nonhalt is **not** the target; this file
records observed macro rules.

## Transition table
|   | 0   | 1   |
|---|-----|-----|
| A | 1RB | 1LD |
| B | 1RC | 0LE |
| C | 1LA | 1RE |
| D | 0LF | 1LA |
| E | 1RB | 0RB |
| F | --- | 0LB |

The only halting transition is `F,0 → ---`.  F is reached only from
`D,0 → 0LF`, so halting requires the D-left-sweep to land on a 0.

## Observed macro structure (see `sim.py`)

At key moments the head rests at the right blank, state E, with a tape
looking like
  `blank∞ 1^{s₁} 0 1^{s₂} 0 ... 0 1^{sₙ} [E] 0 blank∞`
for some block sizes `sᵢ ≥ 1`, each `sᵢ ≡ 2 (mod 3)` (so `sᵢ ∈ {2, 5, 8, 11, …}`).

Events from the blank tape (block sizes L-to-R at each E-turnaround):
  s=59    [5, 2]
  s=76    [5, 5]        (simple bump: 2 → 5, dt = 17)
  s=175   [2, 5, 2, 2, 2]       (restructure)
  s=192   [2, 5, 2, 2, 5]       (simple bump, dt = 17)
  s=237   [2, 5, 5, 8]          (restructure)
  s=270   [2, 5, 5, 11]         (simple bump: 8 → 11, dt = 33)
  ...

The rightmost block always grows by 3 between E-turnarounds.
When the second-to-last block is ≥ 2 AND the rightmost block `k` satisfies
`k ≡ 2 (mod 6)`, the step is a **simple bump** with no restructuring.
When `k ≡ 5 (mod 6)`, a **restructure** happens whose exact form depends
on the entire left tape.  This is the chaotic shift-overflow behavior.

Simple-bump step counts: `dt(k) = 16j + 17` for `k = 6j + 2`.
-/

def tm : TM 6 := tm! "1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_---0LB"

-- Transition simp lemmas: evaluate `tm.tr st sym` without unfolding the literal.
@[simp] private theorem tr_A0 : tm.tr stA false = some (stB, true,  Dir.R) := rfl
@[simp] private theorem tr_A1 : tm.tr stA true  = some (stD, true,  Dir.L) := rfl
@[simp] private theorem tr_B0 : tm.tr stB false = some (stC, true,  Dir.R) := rfl
@[simp] private theorem tr_B1 : tm.tr stB true  = some (stE, false, Dir.L) := rfl
@[simp] private theorem tr_C0 : tm.tr stC false = some (stA, true,  Dir.L) := rfl
@[simp] private theorem tr_C1 : tm.tr stC true  = some (stE, true,  Dir.R) := rfl
@[simp] private theorem tr_D0 : tm.tr stD false = some (stF, false, Dir.L) := rfl
@[simp] private theorem tr_D1 : tm.tr stD true  = some (stA, true,  Dir.L) := rfl
@[simp] private theorem tr_E0 : tm.tr stE false = some (stB, true,  Dir.R) := rfl
@[simp] private theorem tr_E1 : tm.tr stE true  = some (stB, false, Dir.R) := rfl
@[simp] private theorem tr_F0 : tm.tr stF false = none := rfl
@[simp] private theorem tr_F1 : tm.tr stF true  = some (stB, false, Dir.L) := rfl

-- ============================================================
-- Macro configuration
-- ============================================================

/-- Macro configuration `M_Config L k`: state E, head on 0 (right blank),
    left tape = `ones k *> [false] *> L`, right tape = `blank∞`.

    Represents `L' 0 1^k [E] 0 blank∞` on the real tape, where `L'` is any
    Side containing whatever is further left (encoded in `L`). -/
def M_Config (L : Side) (k : Nat) : SConfig 6 :=
  { state := some stE,
    head := false,
    left := ones k *> [false] *> L,
    right := blank∞ }

-- ============================================================
-- Simple bump macro rule  (k ≡ 2 mod 6)
-- ============================================================

-- ============================================================
-- Structural lemmas for the inductive proof of `simple_bump`
-- ============================================================
-- The bump decomposes into 5 phases (for k = 6j + 2):
--   Phase 1 (3 steps): right-push — E→B→C writes 11, turns around at
--                      right blank, leaves state A on last written 1.
--   Phase 2 (k+2 = 6j+4 steps): A/D left-sweep eats (k+1) ones plus the
--                      [false] separator, ending in state A on that 0.
--   Phase 3 (4 steps): prelude A→B→E→B→C — transitions to cycle start,
--                      sets up innermost-ones-1 marker and consumes 2 ones.
--   Phase 4 (5·(2j+1) = 10j+5 steps): iterated C↦C 5-step cycle, each
--                      transferring 3 ones from right to inner-left.
--   Phase 5 (1 step): C→E via C,1→1RE on trailing blank.
--
-- Total: 3 + (6j+4) + 4 + (10j+5) + 1 = 16j + 17.

/-- **5-step C-cycle**: state C at head=1, with `ones n *> [false] *> L` on
    left and `ones (m + 3) *> R` on right, advances to the same state
    with inner-ones block grown by 3 and right-block shrunk by 3. -/
lemma ones_cycle5 (n m : Nat) (L R : Side) :
    srun tm
      { state := some stC, head := true,
        left := ones n *> [false] *> L,
        right := ones (m + 3) *> R } 5
    = { state := some stC, head := true,
        left := ones (n + 3) *> [false] *> L,
        right := ones m *> R } := by
  simp [srun, sstep, tm]

/-- Helper: combine two `ones` prefixes on a Side. -/
private lemma ones_ones (a b : Nat) (s : Side) :
    Side.prepend (ones a) (Side.prepend (ones b) s)
      = Side.prepend (ones (a + b)) s := by
  rw [← Side.prepend_append, ones_append]

/-- **Iterated C-cycle**: N applications of `ones_cycle5` transfer 3N ones
    from the right ones-block to the inner-left ones-block. -/
lemma ones_cycle5_iter (N n m : Nat) (L R : Side) :
    srun tm
      { state := some stC, head := true,
        left := ones n *> [false] *> L,
        right := ones (3 * N + m) *> R } (5 * N)
    = { state := some stC, head := true,
        left := ones (3 * N + n) *> [false] *> L,
        right := ones m *> R } := by
  induction N generalizing n m with
  | zero => simp
  | succ N' ih =>
    rw [show 5 * (N' + 1) = 5 + 5 * N' from by ring,
        show 3 * (N' + 1) + m = (3 * N' + m) + 3 from by ring,
        srun_add, ones_cycle5 n (3 * N' + m) L R, ih (n + 3) m,
        show 3 * N' + (n + 3) = 3 * (N' + 1) + n from by ring]

/-- **Phase 2 — AD left-sweep** (by induction on `n`): state A head=1 on
    `ones (2n+1) *> [false] *> L` sweeps to the separator in `2n+2` steps,
    ending at state A head=0 on `L`, depositing `ones (2n+1)` on right. -/
lemma AD_sweep_to_sep (n : Nat) (L R : Side) :
    srun tm
      { state := some stA, head := true,
        left := ones (2 * n + 1) *> [false] *> L,
        right := R } (2 * n + 2)
    = { state := some stA, head := false,
        left := L,
        right := ones (2 * n + 1) *> Side.cons true R } := by
  induction n generalizing R with
  | zero => simp [srun, sstep, tm]
  | succ n' ih =>
    rw [show 2 * (n' + 1) + 2 = 2 + (2 * n' + 2) from by ring,
        show 2 * (n' + 1) + 1 = 2 + (2 * n' + 1) from by ring,
        ← ones_ones 2 (2 * n' + 1) (Side.prepend [false] L),
        srun_add]
    have h2 : srun tm
        { state := some stA, head := true,
          left := ones 2 *> ones (2 * n' + 1) *> [false] *> L, right := R } 2
        = { state := some stA, head := true,
            left := ones (2 * n' + 1) *> [false] *> L, right := ones 2 *> R } := by
      simp [srun, sstep, tm]
    rw [h2, ih (Side.prepend (ones 2) R)]
    -- Reconcile the right-sides.
    congr 1
    have e1 : Side.cons true (Side.prepend (ones 2) R) = Side.prepend (ones 3) R := rfl
    have e2 : Side.cons true R = Side.prepend (ones 1) R := rfl
    rw [e1, e2, ones_ones (2 * n' + 1) 3 R, ones_ones (2 + (2 * n' + 1)) 1 R,
        show (2 * n' + 1) + 3 = (2 + (2 * n' + 1)) + 1 from by ring]

/-- **Phase 1 — right-push** (3 fixed steps): from `M_Config L k`, state E
    turns into state A after writing two 1s on the right and one 1 at the
    original head position. -/
lemma phase1_right_push (L : Side) (k : Nat) :
    srun tm (M_Config L k) 3
    = { state := some stA, head := true,
        left := ones (k + 1) *> [false] *> L,
        right := Side.cons true blank∞ } := by
  simp [M_Config, srun, sstep, tm]

/-- **Phase 2 — AD sweep specialized** from post-right-push config.
    For `k = 6j + 2` (so `k+1 = 2·(3j+1) + 1`), the sweep takes `k + 2 = 6j+4`
    steps and ends at state A head=0 on `L` with `ones (k+3)` on right. -/
lemma phase2_sweep (L : Side) (j : Nat) :
    srun tm
      { state := some stA, head := true,
        left := ones (6*j + 3) *> [false] *> L,
        right := Side.cons true blank∞ } (6*j + 4)
    = { state := some stA, head := false,
        left := L,
        right := ones (6*j + 5) *> blank∞ } := by
  have h := AD_sweep_to_sep (3*j + 1) L (Side.cons true blank∞)
  rw [show 2 * (3*j + 1) + 1 = 6*j + 3 from by ring,
      show 2 * (3*j + 1) + 2 = 6*j + 4 from by ring] at h
  rw [h]
  -- ones(6j+3) *> cons true (cons true blank) = ones(6j+5) *> blank
  congr 1
  have e : Side.cons true (Side.cons true blank∞) = Side.prepend (ones 2) blank∞ := rfl
  rw [e, ones_ones (6*j + 3) 2 blank∞,
      show (6*j + 3) + 2 = 6*j + 5 from by ring]

/-- **Phase 3 — prelude** (4 fixed steps): transitions post-sweep state A
    head=0 on `L` with `ones (6j+5)` right-ones to the cycle start. -/
lemma phase3_prelude (L : Side) (j : Nat) :
    srun tm
      { state := some stA, head := false,
        left := L,
        right := ones (6*j + 5) *> blank∞ } 4
    = { state := some stC, head := true,
        left := ones 1 *> [false] *> L,
        right := ones (6*j + 3) *> blank∞ } := by
  rw [show 6*j + 5 = 3 + (6*j + 2) from by ring,
      show 6*j + 3 = 1 + (6*j + 2) from by ring,
      ← ones_ones 3 (6*j + 2) blank∞, ← ones_ones 1 (6*j + 2) blank∞]
  simp [srun, sstep, tm]

/-- **Phase 4 — iterated cycle**: `2j+1` cycles consume all `6j+3` right-ones
    and grow the inner-left-ones from 1 to `6j+4`. -/
lemma phase4_cycle (L : Side) (j : Nat) :
    srun tm
      { state := some stC, head := true,
        left := ones 1 *> [false] *> L,
        right := ones (6*j + 3) *> blank∞ } (10*j + 5)
    = { state := some stC, head := true,
        left := ones (6*j + 4) *> [false] *> L,
        right := blank∞ } := by
  have h := ones_cycle5_iter (2*j + 1) 1 0 L blank∞
  rw [show 3 * (2*j + 1) + 0 = 6*j + 3 from by ring,
      show 5 * (2*j + 1) = 10*j + 5 from by ring,
      show 3 * (2*j + 1) + 1 = 6*j + 4 from by ring] at h
  rw [h]; simp

/-- **Phase 5 — final step**: C,1→1RE on trailing blank exits to state E. -/
lemma phase5_final (L : Side) (j : Nat) :
    srun tm
      { state := some stC, head := true,
        left := ones (6*j + 4) *> [false] *> L,
        right := blank∞ } 1
    = M_Config L (6*j + 5) := by
  rw [show (6*j + 5 : Nat) = (6*j + 4) + 1 from by ring]
  simp [M_Config, srun, sstep, tm]

/-- Base case of `simple_bump` at `j = 0`:
    `M_Config L 2 → M_Config L 5` in 17 steps.  Proved by direct simp
    (unfolds 17 TM steps; `L` stays abstract as a suffix of `left`). -/
lemma simple_bump_base (L : Side) :
    srun tm (M_Config L 2) 17 = M_Config L 5 := by
  simp [M_Config, srun, sstep, tm]

/-- **Simple bump rule.**  When the rightmost block has size `k = 6j + 2`
    (i.e. `k ≡ 2 mod 6`), the E-turnaround grows it by 3 in `16j + 17`
    steps, leaving the rest of the tape untouched.

    Verified in Python (`sim.py`) for `j = 0..5` with diverse left prefixes
    including empty, pure-ones, and mixed patterns.  The rule is **fully
    local**: it does not depend on the structure of `L` at all, only on the
    `[false]` separator just left of the ones block.

    Proof composes 5 phase lemmas (right-push, AD sweep, prelude, iterated
    cycle, final), summing to `3 + (6j+4) + 4 + (10j+5) + 1 = 16j + 17`. -/
theorem simple_bump (L : Side) (j : Nat) :
    srun tm (M_Config L (6*j + 2)) (16*j + 17) = M_Config L (6*j + 5) := by
  -- Right-associate the step decomposition so `srun_add` peels from the outside.
  rw [show (16*j + 17 : Nat) = 3 + ((6*j + 4) + (4 + ((10*j + 5) + 1))) from by ring,
      srun_add, phase1_right_push L (6*j + 2),
      show (6*j + 2) + 1 = 6*j + 3 from by ring,
      srun_add, phase2_sweep L j,
      srun_add, phase3_prelude L j,
      srun_add, phase4_cycle L j,
      phase5_final L j]

-- ============================================================
-- Initial configuration
-- ============================================================

/-- Config-form initial run target (matches SConfig form under `.toSConfig`). -/
def Init_Config_52 : Config 6 :=
  { state := some stE,
    head := false,
    left := ones 2 ++ [false] ++ ones 5 ++ [false],
    right := [] }

/-- Config-side lemma: from the blank tape, in 59 steps we reach the concrete
    `Init_Config_52`. -/
lemma init_to_Init_Config_52 :
    run tm (initConfig 6) 59 = Init_Config_52 := by
  decide

/-- Bridge: `Init_Config_52` lifts to `M_Config (ones 5 *> blank∞) 2`. -/
lemma Init_Config_52_toSConfig :
    Init_Config_52.toSConfig = M_Config (ones 5 *> blank∞) 2 := by
  simp [Init_Config_52, M_Config, Config.toSConfig]

/-- From the blank tape, the TM reaches the first macro configuration
    `[5, 2]` at step 59.  I.e. tape = `blank∞ 1^5 0 1^2 [E] 0 blank∞`. -/
theorem init_to_M_52 :
    srun tm (sinitConfig 6) 59 =
      M_Config (ones 5 *> blank∞) 2 := by
  have h := congrArg Config.toSConfig init_to_Init_Config_52
  rw [toSConfig_run, toSConfig_initConfig, Init_Config_52_toSConfig] at h
  exact h

-- ============================================================
-- First simple bump from the initial macro config
-- ============================================================

/-- Combining `init_to_M_52` and `simple_bump_base`: from blank, in 76 steps
    we reach the `[5, 5]` configuration. -/
theorem init_to_M_55 :
    srun tm (sinitConfig 6) 76 =
      M_Config (ones 5 *> blank∞) 5 := by
  rw [show (76 : Nat) = 59 + 17 from rfl, srun_add, init_to_M_52,
      simple_bump_base]

-- ============================================================
-- Restructure rules (chaotic — listed for documentation)
-- ============================================================
/-
After a simple bump, the rightmost block is ≡ 5 (mod 6).  The next
E-turnaround involves a restructure whose shape depends on the entire
left tape.  Empirical pairs observed in the simulator:

  [5, 5]                      → [2, 5, 2, 2, 2]             (dt = 99)
  [2, 5, 2, 2, 5]             → [2, 5, 5, 8]                (dt = 45)
  [2, 5, 5, 11]               → [2, 8, 5, 2, 2, 2, 2, 2]    (dt = 165)
                                 (rightmost 11 "overflows" through earlier blocks)
  [2, 8, 5, 2, 2, 2, 2, 5]    → [2, 8, 5, 2, 2, 5, 8]       (dt = 45)
  [2, 8, 5, 2, 2, 5, 11]      → [2, 8, 5, 2, 5, 2, 14]      (dt = 73)
  [2, 8, 5, 2, 5, 2, 17]      → [5, 2, 2, 8, 8, 20]         (dt = 157)

The simplest non-trivial pattern (`carry_22_5` below) is
`[…, 2, 2, 5] → […, 5, 8]` with dt = 45: three rightmost blocks collapse
to two.  Fully local for any prefix `…`.

No simple closed form is visible yet; this TM is genuinely "chaotic" on
this macro scale — which is why it remains a BB(6) holdout.
-/

-- ============================================================
-- Carry rule [2, 2, 5] → [5, 8]
-- ============================================================

/-- **Carry rule** (`dt = 45`): when the three rightmost blocks have sizes
    `[2, 2, 5]` (reading L-to-R), an E-turnaround collapses them to two
    blocks of sizes `[5, 8]` in 45 steps.  Fully local in any prefix `L`
    (verified in `sim.py` for empty/pure-ones/mixed prefixes).

    Note: input rightmost block has size 5, and the two previous blocks
    are both size 2.  This triggers the simplest chaotic restructure. -/
theorem carry_22_5 (L : Side) :
    srun tm
      (M_Config (ones 2 *> [false] *> ones 2 *> [false] *> L) 5) 45
    = M_Config (ones 5 *> [false] *> L) 8 := by
  simp [M_Config, srun, sstep, tm]

-- ============================================================
-- Closed-form characterization of macro rules (from simulator analysis)
-- ============================================================
/-
**Global pattern**.  At every E-turnaround, the rightmost block has size
`k` and the macro step always produces `k + 3`.  The step count follows
    `dt = (8 · k + C_family) / 3`
where `C_family` is an integer constant determined by the few rightmost
blocks (the "family" prefix).  Examples:

  family          prefix_in → prefix_out   C_family   dt formula
  simple_bump     []        → []           35         dt = (8k+35)/3
  carry_22        [2,2]     → [5]          95         dt = (8k+95)/3
  swap_25         [2,5]     → [5,2]        131        dt = (8k+131)/3
  carry_85        [8,5]     → [11,2]       179        dt = (8k+179)/3
  carry_22_52     [2,2,5,2] → [5,8]        179        dt = (8k+179)/3
  carry_88        [8,8]     → [11,2,2]     215        dt = (8k+215)/3
  spread_14       [14,2]    → [17]         191        dt = (8k+191)/3
  spread_2_14     [2,14]    → [5,2,2,2,2]  239        dt = (8k+239)/3
  ... (335+ distinct families observed in 500M-step sim)

All families preserve the `sᵢ ≡ 2 (mod 3)` invariant (see below).
Verified empirically: the 8⋅10⁶ block samples from a 10⁹-step simulation
are all ≡ 2 (mod 3), across all observed families.

Since the family applies uniformly for any `k ≡ 5 (mod 6)` (odd-bump case)
or `k ≡ 2 (mod 6)` (simple-bump case), each family admits a general
induction on `j` (where `k = 6j+2` or `k = 6j+5`) mirroring `simple_bump`.
-/

/-- Concrete base case of the `[..., 2, 2, k]` family at `k = 11` (j = 1).
    `[prefix, 2, 2, 11] → [prefix, 5, 14]` in 61 = (8·11+95)/3 steps. -/
theorem carry_22_11 (L : Side) :
    srun tm
      (M_Config (ones 2 *> [false] *> ones 2 *> [false] *> L) 11) 61
    = M_Config (ones 5 *> [false] *> L) 14 := by
  simp [M_Config, srun, sstep, tm]

/-- Concrete base case of the `[..., 2, 5, k]` family at `k = 11`.
    `[prefix, 2, 5, 11] → [prefix, 5, 2, 14]` in 73 = (8·11+131)/3 steps. -/
theorem swap_25_11 (L : Side) :
    srun tm
      (M_Config (ones 5 *> [false] *> ones 2 *> [false] *> L) 11) 73
    = M_Config (ones 2 *> [false] *> ones 5 *> [false] *> L) 14 := by
  simp [M_Config, srun, sstep, tm]

set_option maxRecDepth 2000 in
/-- Concrete base case of the `[..., 8, 5, k]` family at `k = 35`.
    `[prefix, 8, 5, 35] → [prefix, 11, 2, 38]` in 153 = (8·35+179)/3 steps. -/
theorem carry_85_35 (L : Side) :
    srun tm
      (M_Config (ones 5 *> [false] *> ones 8 *> [false] *> L) 35) 153
    = M_Config (ones 2 *> [false] *> ones 11 *> [false] *> L) 38 := by
  simp [M_Config, srun, sstep, tm]

/-
## Progress log

2026-04-21:
- Python sim (`sim.py`) confirms the simple-bump rule is fully local.
- `simple_bump_base` (j=0) proven by direct simp.
- `init_to_M_52` proven via Config bridge + `decide` (59 steps).
- `init_to_M_55` proven by composition (59 + 17 = 76 steps).
- **`simple_bump` fully proven** by induction on `j`, via a 5-phase
  decomposition: right-push (3) + AD sweep (6j+4) + prelude (4) +
  iterated C-cycle (10j+5) + final (1) = 16j+17.  Key structural lemmas
  `AD_sweep_to_sep` (sweep induction on `n`) and `ones_cycle5_iter`
  (5-step C→C cycle induction on `N`) carry the weight of the induction.
- **`carry_22_5` proven** by direct simp (45 steps, abstract `L`).
  The rule `[…, 2, 2, 5] → […, 5, 8]` is fully local — the three
  rightmost blocks collapse to two irrespective of the left prefix.

2026-04-21 (deep sim + characterization):
- Deep simulation (`deep_sim.py`, `classify_rules.py`, `analyze_rules.py`):
  ran 6.04 × 10⁹ raw TM steps (30 min, 12 MB RSS constant), collected
  39,387 E-turnaround events with **19,773,584 block samples**.
  **Zero violations of `sᵢ ≡ 2 (mod 3)`** — the invariant holds perfectly.
  Max block size 116,558; block count hovers ~500 throughout.  Rate
  ~3.35 × 10⁶ steps/sec sustained.
- 500M-step analysis identified **335 distinct macro-rule families**,
  with ALL rules matching the closed form
      dt = (8·k + C_family) / 3,  Δk = +3
  where k is the rightmost block size and C_family is family-specific:
      []          35    (simple_bump)
      [2,2]       95    (carry_22)
      [2,5]       131   (swap_25)
      [8,5]       179   (carry_85)
      [2,2,5,2]   179
      [8,8]       215   (carry_88)
      [14,2]      191
      [2,14]      239
      …
- Added `carry_22_11`, `swap_25_11`, `carry_85_35` as concrete base
  cases of three restructure families (all proved by direct simp;
  `carry_85_35` needs `maxRecDepth 2000` at 153 steps).
- File is sorry-free and builds cleanly.

Summary of provable macro content:
- `simple_bump` — full family `[k] → [k+3]` for any `k = 6j+2` (induction).
- `carry_22_5`, `carry_22_11` — `[2,2,k] → [5,k+3]` family (base cases).
- `swap_25_11` — `[2,5,k] → [5,2,k+3]` family (base case).
- `carry_85_35` — `[8,5,k] → [11,2,k+3]` family (base case).

Open: proving each restructure family generally (induction on `j`
analogous to `simple_bump`) would require per-family 5-phase
decompositions.  Full formal proof of the mod-3 invariant requires
characterizing ALL ~∞ families, which matches the "chaotic counter"
description from the BB wiki.

## Alternative approaches to proving the mod-3 invariant

Enumerating macro-rule families does not scale (335+ observed, likely
unbounded).  Four alternative approaches:

1. **State-parameterized structural invariant** (ClosedSet-style).
   Define a predicate `P(c)` on configurations that encodes the tape's
   shape IN EACH TM STATE, with mod-3 constraints baked in.  Prove `P`
   is preserved by each of the 12 TM transitions (not by each macro
   rule).  Show the initial config satisfies `P`.  Derive the mod-3
   invariant as a corollary at E-turnarounds.

   Advantage: only 12 case-splits; scales to infinite macro rules.
   Cost: designing the right `P`.  Empirically the tape-shape schemata
   per state total ~10–20 (see `shape_trace.py`, not 335).

2. **"Digit" encoding**.  Recast each block of size `s = 3a+2` as a
   non-negative digit `a`.  The invariant becomes `a ∈ ℕ`.  Show the
   TM simulates some arithmetic operation on digit sequences that
   preserves non-negativity.  Works if the macro semantics are clean;
   likely hard here given the "chaotic" label.

3. **Regularity / Presburger**.  The invariant language
      `L_safe = {tapes where every maximal 1-run has length ≡ 2 (mod 3)}`
   IS regular (5-state DFA).  Investigation (`regularity.py`, 690K steps):
   - Step-level preservation FAILS: only 75% of intermediate configs
     satisfy L_safe; the other 25% are "transient" during restructures.
   - Of the 12 TM transitions, **only 5 preserve L_safe at every step**:
       A,1→D   D,1→A   C,1→E   D,0→F   E,1→B  (only when fired from a schema where pos≡2 mod 3)
     These 5 correspond to "no-write" transitions (write same as read)
     plus one specific E,1-at-pos-2 firing.
   - 6 transitions can break L_safe transiently: `B,1→E` (85K breaks),
     `E,0→B`, `F,1→B`, `B,0→C`, `C,0→A`, `A,0→B`.
   - **Refined regular invariant**: `L_refined = L_safe ∧ (TM-state, head-position
     phase-tag)`.  This is regular (product of L_safe DFA with the ~20-25
     shape-schema DFA).  Preservation under all 12 transitions holds by
     construction.  Extracting `L_safe` at E-turnarounds (phase = "at
     right blank") gives the invariant.
   - **Presburger angle**: the mod-3 property on a FIXED list of block
     sizes is Presburger-definable (∀i. s_i ≡ 2 mod 3).  But the
     REACHABILITY predicate over block-sequences is not Presburger
     (variable arity, chaotic).  Regular-tree / regular-language
     encoding captures what Presburger cannot.
   - **Implementation path**: the "refined regular invariant" ≡ the
     ClosedSet predicate of approach 1.  The regularity framing tells
     us the predicate has a finite-automaton representation, which is
     what makes the case analysis mechanical.  Tools like regular
     model checking (MONA, LASH, FASTer) could in principle automate
     the fixed-point computation.

4. **WSTS / well-quasi-order**.  For monotone counter TMs sometimes
   applicable; unlikely here.

**Recommended**: approach 1, using `BusyLean.ClosedSet`.  The shape
schemata per state are enumerable from `shape_trace.py`.

## Enumerated shape schemata per state (from `shape_summary.py`)

Empirical trace of ~2M configs (≈2M steps, 60s wall time) over the
steady-state regime.  For each state, the "active-region" pattern —
bounded window around the head — collapses into a small number of
schemata accounting for 99%+ of configs.

**Legend:** "block≡r" = head is on a 1 inside a run of 1s of length
`≡ r (mod 3)`; "pos≡q" = head's L-neighbor count within that run is
`≡ q (mod 3)`; "L-nbr"/"R-nbr" = immediate neighbor cell.

**State A** — 3 core shapes (33% each), ~99% cumulative:
  A₀:  h=1 block≡2 pos≡0 L=1 R=1        (mid-sweep, phase-0)
  A₁:  h=1 block≡2 pos≡1 L=1 R=1        (mid-sweep, phase-1)
  A₂:  h=1 block≡2 pos≡2 L=1 R=1        (mid-sweep, phase-2)
  Edge cases (<1% total): h=1 with L=0 (sweep hitting left boundary),
  and h=0 at post-sweep turnaround.

**State B** — 2 core shapes (49% each), ~98% cumulative:
  B₁:  h=1 block≡2 pos=0 L=0 R=1        (head at block-start, just past sep)
  B₀:  h=0 L=[0,1...] R=[0,1...]        (head on separator between two 1s)
  Edge cases: right-blank boundary (R=blank), and transient block≡1 cases
  (head inside a block being broken during cycle).

**State C** — 1 core shape (97%), ~99% with neighbors:
  C:   h=1 block≡2 pos≡1 L=1 R=1        (always pos≡1 in a ≡2 block)
  Edge cases: R=0 (right-edge), R=blank, transient block≡0.

**State D** — 3 core shapes (33% each), ~99% cumulative:
  D₀, D₁, D₂  mirroring state A (AD alternation).

**State E** — 2 core shapes (49% each), ~98% cumulative:
  E₀:  h=0 L=[0,1...] R=[0,1...]        (at separator, about to sweep right)
  E₁:  h=1 block≡2 pos≡2 L=1 R=1        (inside block, last cell before sep)
  Edge cases: R=blank (E-turnaround! — this is the canonical macro event),
  transient block≡0.

**State F** — 1 core shape (100%):
  F:   h=1 block≡2 pos≡1 L=1 R=0        (always one cell into a block with 0 on right)

**Total core schemata: 3 + 2 + 1 + 3 + 2 + 1 = 12.**

**Total including edge/transient schemata: ~20–25.**

### Implications for the ClosedSet predicate `P(c)`

For a full Lean proof, `P` is a disjunction of ~20–25 shape-schema clauses.
Each schema is parameterized by finitely many natural numbers (block sizes,
sweep positions) and has an explicit tape-pattern.  Preservation under each
of the 12 TM transitions is mechanical: each transition moves between two
specific schemata (or stays within one, updating parameters).

Key observation: the mod-3 "exception" cases (block≡0 or block≡1) are
TRANSIENT and only occur when the head is actively inside a block being
torn down / built up.  The "permanent" blocks (those not currently under
the head) always satisfy `≡ 2 (mod 3)`.  Thus `P` distinguishes the
"current block" from "committed blocks".

**Upshot**: a ClosedSet-style proof of the mod-3 invariant is **feasible**
but requires ~20–25 schema clauses × 12 transitions ≈ 100–300 small
case-splits.  Much less work than enumerating 335+ macro-rule families.

## Can nonhalt be proved without schemata?

### Halt precondition

Only halting transition is `F,0 → ---`.  F is entered only via `D,0 → 0LF`.
So **halt iff D fires on 0 AND cell L of D is also 0** (then F reads 0).

### Sufficient nonhalt conditions, in order of strength

  W1: Whenever D fires on 0, the cell L of D is 1.            (weakest)
  W2: Tape has ≥ 2 blocks at every E-turnaround.
  W3: Leftmost 1 position is monotonically non-increasing.
  W4: Tape has no "00" in the non-blank region.               (strongest)

### Empirical status (1.6M step trace, `nonhalt_investigation.py`)

  W1: ✓ holds (0 violations in 2,764 D-fires).
  W2: ✓ holds (min 2 blocks, max 532, over many E-turnarounds).
  W3: ✗ FAILS (9 rightward moves — leftmost 1 IS occasionally erased).
  W4: ✗ FAILS badly (12.9% of steps have "00" in non-blank region).

W4 is violated transiently during B,1→0 firings (creates a local "00"
that is repaired by the next E,0→1 write).  W3 is violated during some
deep restructures that completely replace the leftmost block.

### Why W1 is enough but hard to prove directly

Chain: `W1 ← W2 ← W1' := AD sweep always lands at separator
between two existing blocks`.

To prove W1', must know: the AD left-sweep over `ones (6j+3)` ends at
the separator BEFORE the blank boundary, AND the cell further L is 1.
This requires tracking:
  - Location of sweep start (head after right-push).
  - Length of current block (determines sweep duration).
  - Existence of a left-neighbor block (requires block-count invariant).

All three are encoded in the shape schemata.  **No smaller fact suffices.**

### What standard BB deciders can/cannot do

  Cyclers:        detect exact config repeat.  Fails: configs grow.
  Translated Cyclers:  detect translated repeat.  Fails: non-shift.
  Bouncers:       detect reflection off boundary.  Fails: bidirectional
                  growth + non-periodic structure.
  MITMLR:         meet-in-the-middle on left/right run patterns.  Fails:
                  run lengths take unboundedly many values.
  Closed Position Set:  head stays in bounded region.  Fails: head grows.
  Backwards Reasoning:  show halt config has no predecessor chain.  Fails:
                  halt condition's predecessors extend to unbounded depth.
  Finite Automata Reduction (FAR):  regular invariant over tape.  Fails:
                  L_safe alone is not step-preserved (§3 above); refined
                  regular invariant requires the schemata.

This TM is a BB(6) **holdout** precisely because all schema-free
deciders fail on it.

### Fundamental obstruction

The reachable configurations form a single infinite orbit.  Each macro
event depends on a non-trivial portion of the tape, so the orbit has
no compressed closed-form description (is not periodic, eventually
periodic, semilinear, or regular).  To rule out halt, we must show D
never reaches a "blank-adjacent" 0, which requires knowing the tape's
local structure in each state — i.e., schemata.

### Conclusion

Proving nonhalt without schemata appears **infeasible** with current
techniques for this TM.  The "chaotic counter" character forces
schematic analysis.  Any successful nonhalt proof for this machine is
likely to:
  - Define state-parameterized tape schemata (as enumerated above).
  - Show step-level preservation of the schema union.
  - Derive the halt-precondition's unreachability as a corollary.

This matches the BB wiki's description of the machine as a
"chaotic counter" holdout and the failure of all schema-free BB
deciders on it.
-/

end Chaotic6
