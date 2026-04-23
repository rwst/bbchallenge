import BusyLean
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open BusyLean

namespace LucysMoonlight

/-!
# `1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA` — *Lucy's Moonlight*

BB(6) halt/nonhalt holdout (5% champion candidate).  Halt/nonhalt is
**not** the target; this file records observed macro rules following
Shawn Ligocki's analysis from `previous-work/wiki.txt`.

## Transition table
|   | 0   | 1   |
|---|-----|-----|
| A | 1RB | 0RD |
| B | 0RC | 1RE |
| C | 1RD | 0LA |
| D | 1LE | 1LC |
| E | 1RF | 0LD |
| F | --- | 0RA |

The only halting transition is `F,0 → ---`.  F is entered only from
`E,0 → 1RF`.

## Macro configuration (Ligocki)

Let `C(a, b, c) := 0^∞ (1011)^a 1^b (10)^c  [C]  0^∞`.  The default macro
form uses `c = 1`:

    C(a, b) := C(a, b, 1)   =   0^∞ (1011)^a 1^b 1 0 [C] 0^∞.

The TM starts with `Start --(2 steps)--> C(0, 0)`.

## Ligocki's macro rules (verified by `sim.py verify`)

  R1:  C(a+1, 3k)   -> C(a, 8k+6)      dt = 12k² + 53k + 28
  R2:  C(a+2, 3k+1) -> C(a, 8k+16)     dt = 12k² + 77k + 103
  R3:  C(a+2, 3k+2) -> C(a, 8k+22)     dt = 12k² + 101k + 184

  E1:  C(0,   3k)   -> C(2k, 8)        dt = 12k² + 29k + 52       (k ≥ 0)
  E2:  C(0,   3k+1) -> C(0, 8k+5)      dt = 12k² + 53k + 30
  E3:  C(0,   3k+2) -> C(0, 8k+5)      dt = 12k² + 53k + 28

  H1:  C(1,   3k+1) -> Halt            dt = 12k² + 53k + 59       (halt)
  E4:  C(1,   3k+2) -> C(2k+4, 8)      dt = 12k² + 77k + 160

  Init (blank): start --(2)--> C(0, 0)

All step counts are **independent of `a`** (the left prefix `(1011)^a`
plays no role in any rule).  Observed second-difference `24` → quadratic
in `k`, verified by `sim.py verify` for `k ∈ 0..4`, `a ∈ 0..4`.

Racheline's corresponding `c_n` values (first three):
  c_0 = 14, c_1 = 11 292, c_2 ≈ 10^2901.92.

## Status

All macro rules below are currently `sorry`ed and are verified
**empirically** by `sim.py`.  Lean proofs will follow the Chaotic6 /
Shifty6 pattern: decompose each rule into `shift`-style lemmas
(state-A/D/etc. sweeps) plus a direct `simp` for a base case.
-/

def tm : TM 6 := tm! "1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA"

-- Transition simp lemmas: evaluate `tm.tr st sym` without unfolding the literal.
@[simp] private theorem tr_A0 : tm.tr stA false = some (stB, true,  Dir.R) := rfl
@[simp] private theorem tr_A1 : tm.tr stA true  = some (stD, false, Dir.R) := rfl
@[simp] private theorem tr_B0 : tm.tr stB false = some (stC, false, Dir.R) := rfl
@[simp] private theorem tr_B1 : tm.tr stB true  = some (stE, true,  Dir.R) := rfl
@[simp] private theorem tr_C0 : tm.tr stC false = some (stD, true,  Dir.R) := rfl
@[simp] private theorem tr_C1 : tm.tr stC true  = some (stA, false, Dir.L) := rfl
@[simp] private theorem tr_D0 : tm.tr stD false = some (stE, true,  Dir.L) := rfl
@[simp] private theorem tr_D1 : tm.tr stD true  = some (stC, true,  Dir.L) := rfl
@[simp] private theorem tr_E0 : tm.tr stE false = some (stF, true,  Dir.R) := rfl
@[simp] private theorem tr_E1 : tm.tr stE true  = some (stD, false, Dir.L) := rfl
@[simp] private theorem tr_F0 : tm.tr stF false = none := rfl
@[simp] private theorem tr_F1 : tm.tr stF true  = some (stA, false, Dir.R) := rfl

-- ============================================================
-- Macro configuration
-- ============================================================

/-- One `(1011)` block encoded as a list in `left`-side order (i.e. read
    right-to-left from the head).  In the tape left-to-right the block is
    `1,0,1,1`; reading cell-by-cell from the right we see `1,1,0,1`. -/
def block1011 : List Sym := [true, true, false, true]

/-- `aBlocks a` encodes `(1011)^a` in the `left` side — `a` copies of
    `block1011` concatenated. -/
def aBlocks : Nat → List Sym
  | 0     => []
  | a + 1 => block1011 ++ aBlocks a

/-- Ligocki macro configuration `C(a, b) = C(a, b, 1)`:
      tape = `0^∞ (1011)^a 1^b 1 0 [C] 0^∞`,
    state C, head on the right blank. -/
def C_Config (a b : Nat) : SConfig 6 :=
  { state := some stC,
    head := false,
    left := (false :: true :: (ones b ++ aBlocks a)) *> blank∞,
    right := blank∞ }

/-- `aBlocks_succ`: fold lemma. -/
theorem aBlocks_succ (a : Nat) :
    aBlocks (a + 1) = block1011 ++ aBlocks a := rfl

-- ============================================================
-- Initial configuration: Start -(2)-> C(0, 0)
-- ============================================================

/-- After 2 steps from blank, the TM reaches `C(0, 0)`.
    (Verified against `sim.py init`; tape after step 2 is
    `0^∞ 1 0 [C] 0^∞`.) -/
theorem init_to_C00 :
    srun tm (sinitConfig 6) 2 = C_Config 0 0 := by
  simp [C_Config, aBlocks, sinitConfig, srun, sstep, tm]

-- ============================================================
-- Shift lemmas  (building blocks for the general-k proofs)
-- ============================================================

/-- **Right-push phase (5 steps)** — universal opener of every rule.
    From state C at the right blank with left prefix `[false, true, true]`
    (which matches every `C_Config a (b+1)` config *and* also `C_Config
    (a+1) 0` since `aBlocks (a+1)` starts with `true, true`), run 5 steps:
      C,0→1RD;  D,0→1LE;  E,1→0LD;  D,0→1LE;  E,1→0LD.
    The head moves `R` once then `L` four times (net -3), pops the
    abstract `[false, true, true]` prefix off the left, and deposits
    `[false, true, false, true]` = `zebra 2` on the right. -/
lemma rightPush_5step (L : Side) :
    srun tm
      { state := some stC, head := false,
        left := [false, true, true] *> L, right := blank∞ } 5
    = { state := some stD, head := true, left := L,
        right := [false, true, false, true] *> blank∞ } := by
  simp [srun, sstep, tm]

/-- **Zebra-extend step (2 steps)** — from state D reading a `1`, with a
    `1` at `left[0]`, two TM steps `D,1→1LC; C,1→0LA` advance the head
    two cells L, leave state A on whatever is now head-adjacent, and
    prepend `[false, true]` to the right side (extending any zebra
    there). -/
lemma zebraExtend_2step (L R : Side) :
    srun tm
      { state := some stD, head := true,
        left := [true] *> L, right := R } 2
    = { state := some stA, head := L.head, left := L.tail,
        right := [false, true] *> R } := by
  simp [srun, sstep, tm]

/-- **Zebra-consume A-cycle (8 steps)** — the main engine of R1/R3/E2/E3.
    From state A reading `0`, with `ones n *> blank∞` on the left and
    a zebra pair prefix `[false, true, false, true]` on the right,
    8 TM steps consume the first zebra pair, produce two new ones on
    the left, and return to state A reading `0` — ready to iterate.

    The step sequence is:
      A,0→1RB;  B,0→0RC;  C,1→0LA;   (3 steps: consume first `0,1`
                                       pair → A head=0)
      A,0→1RB;  B,0→0RC;  C,0→1RD;   (3 steps: advance into second
                                       pair → D head=1)
      D,1→1LC;  C,1→0LA.             (2 steps: D/C retreat → A head=0)

    After iterating this cycle `k` times, a `zebra (k+c)` tail shrinks
    to `zebra c` and the left `ones n` grows to `ones (n + 2k)` —
    giving the `12k²`/`53k` terms in every R/E rule's step count. -/
lemma zebraA_cycle_8step (n : Nat) (M R : Side) :
    srun tm
      { state := some stA, head := false,
        left := ones n *> M,
        right := [false, true, false, true] *> R } 8
    = { state := some stA, head := false,
        left := ones (n + 2) *> M,
        right := [false, true] *> R } := by
  simp [srun, sstep, tm, show ones (n + 2) = true :: true :: ones n from rfl]

/-- **Drain cycle (4 steps)** — handles `k ≥ 1` by sweeping when the head
    returns to state A reading `1`.  From `{A, head=1, left=L, right=
    zebra (k+1) *> R}`, four TM steps `A,1→D,R; D,0→E,L; E,0→F,R;
    F,1→A,R` consume one zebra pair from the right AND prepend
    `[false, true]` to the left, returning to state A reading `1` —
    ready to iterate.

    Proof: mechanical simp over 4 sstep unfoldings.  `L` is abstract —
    the head never touches it during the 4 steps. -/
lemma drainA_cycle_4step (k : Nat) (L R : Side) :
    srun tm
      { state := some stA, head := true,
        left := L, right := zebra (k + 1) *> R } 4
    = { state := some stA, head := true,
        left := [false, true] *> L,
        right := zebra k *> R } := by
  rw [show zebra (k + 1) = [false, true] ++ zebra k from by rw [zebra_succ]; rfl,
      Side.prepend_append]
  simp [srun, sstep, tm]

/-- **Iterated drain cycle** (induction on `N`).  Starting with `N+k`
    zebra pairs on the right and left `L`, run `4N` steps to reduce
    to `k` zebra pairs, prepending a zebra-`N` block on the left. -/
lemma drainA_cycle_iter (N : Nat) : ∀ (k : Nat) (L R : Side),
    srun tm
      { state := some stA, head := true,
        left := L, right := zebra (N + k) *> R } (4 * N)
    = { state := some stA, head := true,
        left := zebra N *> L,
        right := zebra k *> R } := by
  induction N with
  | zero =>
    intro k L R
    simp [srun, zebra]
  | succ N' ih =>
    intro k L R
    have hz : N' + 1 + k = (N' + k) + 1 := by omega
    rw [show 4 * (N' + 1) = 4 + 4 * N' from by ring, srun_add, hz]
    have hsplit : zebra (N' + k + 1) = [false, true] ++ zebra (N' + k) := by
      rw [zebra_succ]; rfl
    rw [hsplit, Side.prepend_append]
    have h4 : srun tm
        { state := some stA, head := true,
          left := L,
          right := [false, true] *> zebra (N' + k) *> R } 4
        = { state := some stA, head := true,
            left := [false, true] *> L,
            right := zebra (N' + k) *> R } := by
      rw [show ([false, true] *> zebra (N' + k) *> R : Side)
            = Side.prepend [false, true] (Side.prepend (zebra (N' + k)) R) from rfl]
      have := drainA_cycle_4step (N' + k) L R
      rw [show zebra (N' + k + 1) = [false, true] ++ zebra (N' + k) from by rw [zebra_succ]; rfl,
          Side.prepend_append] at this
      exact this
    rw [h4, ih k (Side.prepend [false, true] L) R]
    congr 1
    show Side.prepend (zebra N') (Side.prepend [false, true] L)
       = Side.prepend (zebra (N' + 1)) L
    rw [← Side.prepend_append, ← zebra_succ_append]

/-- **Left-zebra-consume cycle (2 steps)** — the symmetric partner of
    `drainA_cycle_4step` / `zebraA_cycle_8step` for the "left sweep"
    phase.  From state D reading 0 with left prefix `[true, false]` and
    abstract tails, two TM steps `D,0→1LE; E,1→0LD` consume the `[T,F]`
    pair from the left AND prepend `[false, true]` to the right.

    Net effect: state stays D,0; one `[T,F]` pair moves from left to
    right (as a `[F,T]` pair — i.e. one zebra pair). -/
lemma leftZebra_consume_2step (L R : Side) :
    srun tm
      { state := some stD, head := false,
        left := [true, false] *> L, right := R } 2
    = { state := some stD, head := false,
        left := L, right := [false, true] *> R } := by
  simp [srun, sstep, tm]

/-- **Iterated left-zebra-consume** (induction on `N`).  Starting from
    `{D, 0, [T] *> zebra (N+K) *> M, R}`, run `2N` steps to consume
    `N` zebra pairs off the left (from between the `[T]` prefix and
    the `M` tail) while prepending `zebra N` to the right.

    Works because `[T] *> zebra (K+N+1) *> M = [T, F] *> [T] *> zebra
    (K+N) *> M` — the `[T, F]` prefix required by `leftZebra_consume_2step`
    exactly peels one zebra pair off the middle and leaves the `[T]`
    prefix intact for the next iteration.

    Index convention: uses `N + K` (right-addition) so that `K = 0`
    reduces `N + 0` to `N` definitionally — important for composition. -/
lemma leftZebra_consume_iter (N : Nat) : ∀ (K : Nat) (M R : Side),
    srun tm
      { state := some stD, head := false,
        left := [true] *> zebra (N + K) *> M, right := R } (2 * N)
    = { state := some stD, head := false,
        left := [true] *> zebra K *> M,
        right := zebra N *> R } := by
  induction N with
  | zero =>
    intro K M R
    simp [srun, zebra]
  | succ N' ih =>
    intro K M R
    -- Peel one [T, F] pair off the front of `[T] *> zebra (N'+1+K) *> M`.
    have hz : zebra (N' + 1 + K) = [false, true] ++ zebra (N' + K) := by
      rw [show N' + 1 + K = (N' + K) + 1 from by omega, zebra_succ]; rfl
    have hstep : srun tm
        { state := some stD, head := false,
          left := [true] *> zebra (N' + 1 + K) *> M, right := R } 2
        = { state := some stD, head := false,
            left := [true] *> zebra (N' + K) *> M,
            right := [false, true] *> R } := by
      rw [hz, Side.prepend_append]
      -- Fold `[true] *> [false, true] *> ...` into `[true, false] *> [true] *> ...`
      have eq : Side.prepend [true] (Side.prepend [false, true] (Side.prepend (zebra (N' + K)) M))
            = Side.prepend [true, false]
                (Side.prepend [true] (Side.prepend (zebra (N' + K)) M)) := by
        rw [← Side.prepend_append, ← Side.prepend_append]; rfl
      rw [eq]
      exact leftZebra_consume_2step
        (Side.prepend [true] (Side.prepend (zebra (N' + K)) M)) R
    rw [show 2 * (N' + 1) = 2 + 2 * N' from by ring, srun_add, hstep,
        ih K M ([false, true] *> R)]
    congr 1
    show Side.prepend (zebra N') (Side.prepend [false, true] R)
       = Side.prepend (zebra (N' + 1)) R
    rw [← Side.prepend_append, ← zebra_succ_append]

/-- **Drain-to-blank edge (4 steps)** — fires once after `drainA_cycle_iter`
    has fully consumed the right zebra, leaving `right = blank∞`.  The
    same 4-step state sequence `A,1→D,R; D,0→E,L; E,0→F,R; F,1→A,R`
    now operates against blanks instead of zebra pairs.

    Net effect: flip the head from A,1 to A,F, and prepend `[false,
    true]` to the left (extending any zebra prefix by one pair).
    Right stays `blank∞` throughout — the blank gets "written through"
    twice, exploiting `cons F blank = blank`. -/
lemma drainEdge_4step (L : Side) :
    srun tm
      { state := some stA, head := true,
        left := L, right := blank∞ } 4
    = { state := some stA, head := false,
        left := [false, true] *> L,
        right := blank∞ } := by
  simp [srun, sstep, tm]

/-- **A→B→C→D transition (3 steps)** — bridges from the end of `drainEdge_4step`
    to the start of `leftZebra_consume_iter`.  From `{A, 0, L, blank∞}`,
    three TM steps `A,0→1RB; B,0→0RC; C,0→1RD` (all with head reading
    blank, all direction R) prepend `[T, F, T]` to the left and leave
    the right as `blank∞`.

    When `L = zebra N *> M`, the output left `[T, F, T] *> zebra N *> M`
    equals `[T] *> zebra (N+1) *> M` (via `zebra_succ`), which is
    exactly the canonical shape consumed by `leftZebra_consume_iter`. -/
lemma A_to_D_3step (L : Side) :
    srun tm
      { state := some stA, head := false,
        left := L, right := blank∞ } 3
    = { state := some stD, head := false,
        left := [true, false, true] *> L,
        right := blank∞ } := by
  simp [srun, sstep, tm]

/-- **Loop-chain cycle (4 steps)** — bridges between outer iterations of
    the general-`k` decomposition.  Same 4-step state sequence as
    `reentry_4step` (D,0→E,1→D,1→C,1→A) but abstract in the number of
    ones on the left and in the tail `M` past the ones.

    From `{D, 0, ones (n+4) *> M, zebra m *> R}`, four TM steps consume
    4 cells off the left (the 4 leading ones, leaving `ones n`) AND
    prepend `zebra 2` (i.e., `[F, T, F, T]`) to the right — so the
    right's zebra count grows by 2.  Output head is `true` (the next
    one from the remaining `ones n` block, or abstract `M.head` if
    `n = 0`; since `ones (n+1).head = true` always, the lemma holds
    uniformly for all `n ≥ 0`).

    This is exactly the transition `{D, 0, ones (3(k-j)+3), zebra (4j+1)}
    → {A, 1, ones (3(k-j)-1), zebra (4j+3)}` (with `n = 3(k-j)-1`,
    `m = 4j+1`) that fires between iterations `j` and `j+1` of the
    outer loop in `rule_E3` for general `k`. -/
lemma loop_chain_4step (n m : ℕ) (M R : Side) :
    srun tm
      { state := some stD, head := false,
        left := Side.prepend (ones (n + 4)) M,
        right := Side.prepend (zebra m) R } 4
    = { state := some stA, head := true,
        left := Side.prepend (ones n) M,
        right := Side.prepend (zebra (m + 2)) R } := by
  simp [srun, sstep, tm,
        show ones (n + 4) = true :: true :: true :: true :: ones n from rfl]

/-- **D→E→D→C→A re-entry (4 steps)** — bridges from the end of
    `leftZebra_consume_iter` (when `left = ones 3 *> blank∞`) to the
    start of `zebraA_cycle_iter`.  From `{D, 0, ones 3 *> blank∞, R}`,
    four TM steps `D,0→1LE; E,1→0LD; D,1→1LC; C,1→0LA` (all direction
    L) fully consume `ones 3` from the left, prepending `zebra 2` to
    the right in the process.  Ends at state A reading blank with
    left fully absorbed into the blank stream — ready to begin the
    main zebra-consume cycle on the accumulated right-zebra. -/
lemma reentry_4step (R : Side) :
    srun tm
      { state := some stD, head := false,
        left := ones 3 *> blank∞, right := R } 4
    = { state := some stA, head := false,
        left := blank∞,
        right := zebra 2 *> R } := by
  simp [srun, sstep, tm, show ones 3 = [true, true, true] from rfl]

-- Fold helpers for the outer-iter composition.  All by zebra_succ +
-- prepend_append algebra.

private lemma zebra_succ_fold (k : Nat) (X : Side) :
    Side.prepend [false, true] (Side.prepend (zebra k) X)
      = Side.prepend (zebra (k + 1)) X := by
  rw [show zebra (k + 1) = [false, true] ++ zebra k from by rw [zebra_succ]; rfl,
      Side.prepend_append]

private lemma zebra_tft_fold (k : Nat) (X : Side) :
    Side.prepend [true, false, true] (Side.prepend (zebra k) X)
      = Side.prepend [true] (Side.prepend (zebra (k + 1)) X) := by
  rw [show ([true, false, true] : List Sym) = [true] ++ [false, true] from rfl,
      Side.prepend_append, zebra_succ_fold]

private lemma cons_true_ones_fold (n : Nat) (X : Side) :
    Side.prepend [true] (Side.prepend (ones n) X)
      = Side.prepend (ones (n + 1)) X := by
  rw [← Side.prepend_append]; rfl

/-- **Outer iteration step** — one non-final outer iteration of the general-`k`
    rule_E3 decomposition, comprising
      drainA_cycle_iter (16q+12 = 4(4q+3) steps)
      drainEdge_4step (4 steps)
      A_to_D_3step (3 steps)
      leftZebra_consume_iter (8q+10 = 2(4q+5) steps)
      loop_chain_4step (4 steps)
    for a total of `24q+33` steps.

    Parameters `m` and `q` avoid all `Nat` subtraction: input ones count
    `3m+5`, input zebra count `4q+3`; after one iteration ones count is
    `3m+2` (down by 3) and zebra count is `4q+7` (up by 4).  In the
    general-k rule_E3 this fires for iteration indices `j ∈ [1, k-1]`
    with `m = k-j-1` and `q = j-1`. -/
lemma outer_iter_step (m q : Nat) :
    srun tm
      { state := some stA, head := true,
        left := Side.prepend (ones (3*m + 5)) blank∞,
        right := Side.prepend (zebra (4*q + 3)) blank∞ } (24*q + 33)
    = { state := some stA, head := true,
        left := Side.prepend (ones (3*m + 2)) blank∞,
        right := Side.prepend (zebra (4*q + 7)) blank∞ } := by
  rw [show 24*q + 33 = 4*(4*q + 3) + (4 + (3 + (2*(4*q + 5) + 4))) from by ring]
  -- Phase 1: drainA_cycle_iter N=(4q+3) k'=0
  rw [srun_add,
      show (zebra (4*q + 3) : List Sym) = zebra ((4*q + 3) + 0) from by norm_num,
      drainA_cycle_iter (4*q + 3) 0
        (Side.prepend (ones (3*m + 5)) blank∞) blank∞,
      show Side.prepend (zebra 0) blank∞ = blank∞ from rfl]
  -- Phase 2: drainEdge_4step
  rw [srun_add, drainEdge_4step
    (Side.prepend (zebra (4*q + 3)) (Side.prepend (ones (3*m + 5)) blank∞)),
      zebra_succ_fold (4*q + 3) (Side.prepend (ones (3*m + 5)) blank∞)]
  -- Phase 3: A_to_D_3step
  rw [srun_add, A_to_D_3step
    (Side.prepend (zebra (4*q + 3 + 1)) (Side.prepend (ones (3*m + 5)) blank∞)),
      zebra_tft_fold (4*q + 3 + 1) (Side.prepend (ones (3*m + 5)) blank∞)]
  -- Phase 4: leftZebra_consume_iter N=(4q+5) K=0; zebra index is (4q+5)+0 via N+K form.
  rw [srun_add,
      leftZebra_consume_iter (4*q + 5) 0
        (Side.prepend (ones (3*m + 5)) blank∞) blank∞,
      show Side.prepend (zebra 0) (Side.prepend (ones (3*m + 5)) blank∞)
        = Side.prepend (ones (3*m + 5)) blank∞ from rfl,
      cons_true_ones_fold (3*m + 5) blank∞]
  -- Phase 5: loop_chain_4step with n=3m+2 (since ones (3m+6) = ones ((3m+2)+4))
  rw [show (3*m + 5 + 1 : Nat) = (3*m + 2) + 4 from by ring]
  exact loop_chain_4step (3*m + 2) (4*q + 5) blank∞ blank∞

/-- **Outer-iteration chaining** (induction on `i`).  Composes `i` applications
    of `outer_iter_step` — each a non-final outer iteration of `rule_E3`.

    After `i` iterations starting from `{A, 1, ones (3*(leftover+i)+2), zebra 3}`,
    the state is `{A, 1, ones (3*leftover+2), zebra (4*i+3)}` with step cost
    `12*i² + 21*i = Σⱼ₌₀ⁱ⁻¹ (24j+33)`.

    `leftover` is the number of iterations that will remain AFTER these `i`
    iterations.  For the full general-`k` `rule_E3`, we will invoke this with
    `leftover = 0` and `i = k-1` (all non-final iterations), leaving the
    state ready for the final iter + closing phase. -/
lemma outer_iter_iter : ∀ (i : Nat) (leftover : Nat),
    srun tm
      { state := some stA, head := true,
        left := Side.prepend (ones (3*(leftover + i) + 2)) blank∞,
        right := Side.prepend (zebra 3) blank∞ } (12*i*i + 21*i)
    = { state := some stA, head := true,
        left := Side.prepend (ones (3*leftover + 2)) blank∞,
        right := Side.prepend (zebra (4*i + 3)) blank∞ } := by
  intro i
  induction i with
  | zero =>
    intro leftover
    show srun tm _ 0 = _
    rfl
  | succ i' ih =>
    intro leftover
    -- Split step count: 12(i'+1)² + 21(i'+1) = (12i'² + 21i') + (24i' + 33)
    rw [show 12*(i'+1)*(i'+1) + 21*(i'+1) = (12*i'*i' + 21*i') + (24*i' + 33) from by ring,
        srun_add]
    -- Reshape initial ones index: 3*(leftover + (i'+1))+2 = 3*((leftover+1) + i')+2
    rw [show 3*(leftover + (i'+1)) + 2 = 3*((leftover+1) + i') + 2 from by ring]
    -- Apply IH at (leftover+1, i') — consumes the first 12i'² + 21i' steps.
    rw [ih (leftover+1)]
    -- Now at {A, 1, ones (3*(leftover+1)+2), zebra (4i'+3)}.
    -- Reshape ones for outer_iter_step: 3*(leftover+1)+2 = 3*leftover+5.
    rw [show 3*(leftover+1) + 2 = 3*leftover + 5 from by ring]
    -- Apply outer_iter_step with m = leftover, q = i'.
    exact outer_iter_step leftover i'

/-- **E2 re-entry (6 steps)** — analogue of `reentry_4step` for `rule_E2`.
    From `{D, 0, ones 2 *> blank, R}` (exactly `ones 2` on the left — not
    `ones 3` as in `reentry_4step`), 6 TM steps `D,0→E,1→D,1→C,0→D,1→C,1→A`
    reach `{A, 0, blank, zebra 2 *> R}`.  The 6-step sequence includes a
    C,0→1RD bounce off the blank left tail (the 4th step), which adds 2
    extra steps compared to `reentry_4step`'s ones-3 boundary case. -/
lemma reentry_E2_6step (R : Side) :
    srun tm
      { state := some stD, head := false,
        left := Side.prepend (ones 2) blank∞,
        right := R } 6
    = { state := some stA, head := false,
        left := blank∞,
        right := Side.prepend (zebra 2) R } := by
  simp [srun, sstep, tm, show ones 2 = [true, true] from rfl]

/-- **E2 outer iteration step** — analogue of `outer_iter_step` with ones
    offset `3m+4 → 3m+1` (instead of E3's `3m+5 → 3m+2`). -/
lemma outer_iter_step_E2 (m q : Nat) :
    srun tm
      { state := some stA, head := true,
        left := Side.prepend (ones (3*m + 4)) blank∞,
        right := Side.prepend (zebra (4*q + 3)) blank∞ } (24*q + 33)
    = { state := some stA, head := true,
        left := Side.prepend (ones (3*m + 1)) blank∞,
        right := Side.prepend (zebra (4*q + 7)) blank∞ } := by
  rw [show 24*q + 33 = 4*(4*q + 3) + (4 + (3 + (2*(4*q + 5) + 4))) from by ring]
  rw [srun_add,
      show (zebra (4*q + 3) : List Sym) = zebra ((4*q + 3) + 0) from by norm_num,
      drainA_cycle_iter (4*q + 3) 0
        (Side.prepend (ones (3*m + 4)) blank∞) blank∞,
      show Side.prepend (zebra 0) blank∞ = blank∞ from rfl]
  rw [srun_add, drainEdge_4step
    (Side.prepend (zebra (4*q + 3)) (Side.prepend (ones (3*m + 4)) blank∞)),
      zebra_succ_fold (4*q + 3) (Side.prepend (ones (3*m + 4)) blank∞)]
  rw [srun_add, A_to_D_3step
    (Side.prepend (zebra (4*q + 3 + 1)) (Side.prepend (ones (3*m + 4)) blank∞)),
      zebra_tft_fold (4*q + 3 + 1) (Side.prepend (ones (3*m + 4)) blank∞)]
  rw [srun_add,
      show (4*q + 3 + 1 + 1 : Nat) = (4*q + 5) + 0 from by ring,
      leftZebra_consume_iter (4*q + 5) 0
        (Side.prepend (ones (3*m + 4)) blank∞) blank∞,
      show Side.prepend (zebra 0) (Side.prepend (ones (3*m + 4)) blank∞)
        = Side.prepend (ones (3*m + 4)) blank∞ from rfl,
      cons_true_ones_fold (3*m + 4) blank∞]
  rw [show (3*m + 4 + 1 : Nat) = (3*m + 1) + 4 from by ring]
  exact loop_chain_4step (3*m + 1) (4*q + 5) blank∞ blank∞

/-- **E2 outer iteration chaining** — analogue of `outer_iter_iter` for E2. -/
lemma outer_iter_iter_E2 : ∀ (i : Nat) (leftover : Nat),
    srun tm
      { state := some stA, head := true,
        left := Side.prepend (ones (3*(leftover + i) + 1)) blank∞,
        right := Side.prepend (zebra 3) blank∞ } (12*i*i + 21*i)
    = { state := some stA, head := true,
        left := Side.prepend (ones (3*leftover + 1)) blank∞,
        right := Side.prepend (zebra (4*i + 3)) blank∞ } := by
  intro i
  induction i with
  | zero =>
    intro leftover
    show srun tm _ 0 = _
    rfl
  | succ i' ih =>
    intro leftover
    rw [show 12*(i'+1)*(i'+1) + 21*(i'+1) = (12*i'*i' + 21*i') + (24*i' + 33) from by ring,
        srun_add]
    rw [show 3*(leftover + (i'+1)) + 1 = 3*((leftover+1) + i') + 1 from by ring]
    rw [ih (leftover+1)]
    rw [show 3*(leftover+1) + 1 = 3*leftover + 4 from by ring]
    exact outer_iter_step_E2 leftover i'

/-- **E2 final iteration body** (24k'+35 steps) — like `final_iter_body`
    but uses `reentry_E2_6step` (6 steps) instead of `reentry_4step` (4
    steps), giving 2 extra steps per final iteration.  Input ones count
    is `1` (not `2` as in E3). -/
lemma final_iter_body_E2 (k' : Nat) :
    srun tm
      { state := some stA, head := true,
        left := Side.prepend (ones 1) blank∞,
        right := Side.prepend (zebra (4*k' + 3)) blank∞ } (24*k' + 35)
    = { state := some stA, head := false,
        left := blank∞,
        right := Side.prepend (zebra (4*k' + 7)) blank∞ } := by
  rw [show 24*k' + 35 = 4*(4*k' + 3) + (4 + (3 + (2*(4*k' + 5) + 6))) from by ring]
  rw [srun_add,
      show (zebra (4*k' + 3) : List Sym) = zebra ((4*k' + 3) + 0) from by norm_num,
      drainA_cycle_iter (4*k' + 3) 0 (Side.prepend (ones 1) blank∞) blank∞,
      show Side.prepend (zebra 0) blank∞ = blank∞ from rfl]
  rw [srun_add, drainEdge_4step
    (Side.prepend (zebra (4*k' + 3)) (Side.prepend (ones 1) blank∞)),
      zebra_succ_fold (4*k' + 3) (Side.prepend (ones 1) blank∞)]
  rw [srun_add, A_to_D_3step
    (Side.prepend (zebra (4*k' + 3 + 1)) (Side.prepend (ones 1) blank∞)),
      zebra_tft_fold (4*k' + 3 + 1) (Side.prepend (ones 1) blank∞)]
  rw [srun_add,
      show (4*k' + 3 + 1 + 1 : Nat) = (4*k' + 5) + 0 from by ring,
      leftZebra_consume_iter (4*k' + 5) 0 (Side.prepend (ones 1) blank∞) blank∞,
      show Side.prepend (zebra 0) (Side.prepend (ones 1) blank∞)
        = Side.prepend (ones 1) blank∞ from rfl,
      cons_true_ones_fold 1 blank∞]
  rw [show (1 + 1 : Nat) = 2 from rfl,
      reentry_E2_6step (Side.prepend (zebra (4*k' + 5)) blank∞)]
  rw [show Side.prepend (zebra 2) (Side.prepend (zebra (4*k' + 5)) blank∞)
        = Side.prepend (zebra (4*k' + 7)) blank∞ from by
      rw [← Side.prepend_append, zebra_append,
          show 2 + (4*k' + 5) = 4*k' + 7 from by ring]]

/-- **Abstract-tail outer iteration step** — generalizes `outer_iter_step`
    to an arbitrary left-tail `L` (rather than `blank∞`).  Needed by
    `rule_R1`/`R2`/`R3` where the left has an `aBlocks (a+1) *> blank`
    tail beyond the ones block. -/
lemma outer_iter_step_abs (L : Side) (m q : Nat) :
    srun tm
      { state := some stA, head := true,
        left := Side.prepend (ones (3*m + 5)) L,
        right := Side.prepend (zebra (4*q + 3)) blank∞ } (24*q + 33)
    = { state := some stA, head := true,
        left := Side.prepend (ones (3*m + 2)) L,
        right := Side.prepend (zebra (4*q + 7)) blank∞ } := by
  rw [show 24*q + 33 = 4*(4*q + 3) + (4 + (3 + (2*(4*q + 5) + 4))) from by ring]
  rw [srun_add,
      show (zebra (4*q + 3) : List Sym) = zebra ((4*q + 3) + 0) from by norm_num,
      drainA_cycle_iter (4*q + 3) 0 (Side.prepend (ones (3*m + 5)) L) blank∞,
      show Side.prepend (zebra 0) blank∞ = blank∞ from rfl]
  rw [srun_add, drainEdge_4step
    (Side.prepend (zebra (4*q + 3)) (Side.prepend (ones (3*m + 5)) L)),
      zebra_succ_fold (4*q + 3) (Side.prepend (ones (3*m + 5)) L)]
  rw [srun_add, A_to_D_3step
    (Side.prepend (zebra (4*q + 3 + 1)) (Side.prepend (ones (3*m + 5)) L)),
      zebra_tft_fold (4*q + 3 + 1) (Side.prepend (ones (3*m + 5)) L)]
  rw [srun_add,
      show (4*q + 3 + 1 + 1 : Nat) = (4*q + 5) + 0 from by ring,
      leftZebra_consume_iter (4*q + 5) 0 (Side.prepend (ones (3*m + 5)) L) blank∞,
      show Side.prepend (zebra 0) (Side.prepend (ones (3*m + 5)) L)
        = Side.prepend (ones (3*m + 5)) L from rfl,
      cons_true_ones_fold (3*m + 5) L]
  rw [show (3*m + 5 + 1 : Nat) = (3*m + 2) + 4 from by ring]
  exact loop_chain_4step (3*m + 2) (4*q + 5) L blank∞

/-- **Fully-general outer iteration step** — generalizes `outer_iter_step_abs`
    to an arbitrary output ones-count `base` (not tied to `3*m + 2`).  Needed
    for `rule_R2` / `rule_R3` where the opening produces `ones (3k'+3)` on the
    left, so we need an iteration with `base ≡ 3 (mod 3)` rather than R1's
    `base ≡ 2 (mod 3)`.

    Semantics: in `24q+33` steps, consumes 3 ones from left (via the standard
    drainA + drainEdge + A_to_D + leftZebra_consume + loop_chain pipeline),
    contracts right-zebra from `zebra (4q+3)` to `zebra (4q+7)`.

    `rule_R1`'s `outer_iter_step_abs (L m q) = outer_iter_step_gen L (3*m+2) q`. -/
lemma outer_iter_step_gen (L : Side) (base q : Nat) :
    srun tm
      { state := some stA, head := true,
        left := Side.prepend (ones (base + 3)) L,
        right := Side.prepend (zebra (4*q + 3)) blank∞ } (24*q + 33)
    = { state := some stA, head := true,
        left := Side.prepend (ones base) L,
        right := Side.prepend (zebra (4*q + 7)) blank∞ } := by
  rw [show 24*q + 33 = 4*(4*q + 3) + (4 + (3 + (2*(4*q + 5) + 4))) from by ring]
  rw [srun_add,
      show (zebra (4*q + 3) : List Sym) = zebra ((4*q + 3) + 0) from by norm_num,
      drainA_cycle_iter (4*q + 3) 0 (Side.prepend (ones (base + 3)) L) blank∞,
      show Side.prepend (zebra 0) blank∞ = blank∞ from rfl]
  rw [srun_add, drainEdge_4step
    (Side.prepend (zebra (4*q + 3)) (Side.prepend (ones (base + 3)) L)),
      zebra_succ_fold (4*q + 3) (Side.prepend (ones (base + 3)) L)]
  rw [srun_add, A_to_D_3step
    (Side.prepend (zebra (4*q + 3 + 1)) (Side.prepend (ones (base + 3)) L)),
      zebra_tft_fold (4*q + 3 + 1) (Side.prepend (ones (base + 3)) L)]
  rw [srun_add,
      show (4*q + 3 + 1 + 1 : Nat) = (4*q + 5) + 0 from by ring,
      leftZebra_consume_iter (4*q + 5) 0 (Side.prepend (ones (base + 3)) L) blank∞,
      show Side.prepend (zebra 0) (Side.prepend (ones (base + 3)) L)
        = Side.prepend (ones (base + 3)) L from rfl,
      cons_true_ones_fold (base + 3) L]
  rw [show (base + 3 + 1 : Nat) = base + 4 from by ring]
  exact loop_chain_4step base (4*q + 5) L blank∞

/-- **Fully-general outer iteration chaining** — iterates `outer_iter_step_gen`
    `i` times, parameterized by `base` (the final output ones-count after all
    `i` iterations).  Reduces ones by 3 per iteration.

    `base` is universally quantified *inside* the statement (not as a lemma
    parameter) so that the inductive hypothesis can be instantiated at
    `base + 3` during the step case. -/
lemma outer_iter_iter_gen (L : Side) : ∀ (i base : Nat),
    srun tm
      { state := some stA, head := true,
        left := Side.prepend (ones (3*i + base)) L,
        right := Side.prepend (zebra 3) blank∞ } (12*i*i + 21*i)
    = { state := some stA, head := true,
        left := Side.prepend (ones base) L,
        right := Side.prepend (zebra (4*i + 3)) blank∞ } := by
  intro i
  induction i with
  | zero =>
    intro base
    show srun tm _ 0 = _
    rw [show (3*0 + base : Nat) = base from by ring,
        show (4*0 + 3 : Nat) = 3 from rfl]
    rfl
  | succ i' ih =>
    intro base
    rw [show 12*(i'+1)*(i'+1) + 21*(i'+1) = (12*i'*i' + 21*i') + (24*i' + 33) from by ring,
        srun_add]
    rw [show 3*(i'+1) + base = 3*i' + (base + 3) from by ring]
    rw [ih (base + 3)]
    exact outer_iter_step_gen L base i'

/-- **Abstract-tail outer iteration chaining** — iterates `outer_iter_step_abs`. -/
lemma outer_iter_iter_abs (L : Side) : ∀ (i : Nat) (leftover : Nat),
    srun tm
      { state := some stA, head := true,
        left := Side.prepend (ones (3*(leftover + i) + 2)) L,
        right := Side.prepend (zebra 3) blank∞ } (12*i*i + 21*i)
    = { state := some stA, head := true,
        left := Side.prepend (ones (3*leftover + 2)) L,
        right := Side.prepend (zebra (4*i + 3)) blank∞ } := by
  intro i
  induction i with
  | zero =>
    intro leftover
    show srun tm _ 0 = _
    rfl
  | succ i' ih =>
    intro leftover
    rw [show 12*(i'+1)*(i'+1) + 21*(i'+1) = (12*i'*i' + 21*i') + (24*i' + 33) from by ring,
        srun_add]
    rw [show 3*(leftover + (i'+1)) + 2 = 3*((leftover+1) + i') + 2 from by ring]
    rw [ih (leftover+1)]
    rw [show 3*(leftover+1) + 2 = 3*leftover + 5 from by ring]
    exact outer_iter_step_abs L leftover i'

/-- **Abstract-tail reentry (4 steps)** — generalizes `reentry_4step` to abstract
    left-tail `X` beyond the `ones 3` prefix.  The output head and left-side
    depend on `X.head` / `X.tail`. -/
lemma reentry_4step_abs (X R : Side) :
    srun tm
      { state := some stD, head := false,
        left := Side.prepend (ones 3) X,
        right := R } 4
    = { state := some stA, head := X.head,
        left := X.tail,
        right := Side.prepend (zebra 2) R } := by
  simp [srun, sstep, tm, show ones 3 = [true, true, true] from rfl]

/-- **Abstract-tail cleanup (5 steps)** — generalizes `cleanup_5step` to
    abstract left-tail `X`. -/
lemma cleanup_5step_abs (n : Nat) (X : Side) :
    srun tm
      { state := some stA, head := false,
        left := Side.prepend (ones n) X,
        right := Side.prepend [false, true] blank∞ } 5
    = { state := some stC, head := false,
        left := Side.prepend (false :: ones (n + 2)) X,
        right := blank∞ } := by
  simp [srun, sstep, tm, show ones (n + 2) = true :: true :: ones n from rfl]

/-- **R1 final iteration body** (24k'+33 steps) — final iter body + reentry,
    for the R1 case where the left-tail beyond the ones block is `[F, T] *> Y`
    (from `aBlocks (a+1) = block1011 ++ aBlocks a`, with the leading [T, T]
    of `block1011` absorbed into the ones block, leaving `[F, T]` separator
    and `aBlocks a` tail). -/
lemma final_iter_body_R1 (Y : Side) (k' : Nat) :
    srun tm
      { state := some stA, head := true,
        left := Side.prepend (ones 2) (Side.prepend [false, true] Y),
        right := Side.prepend (zebra (4*k' + 3)) blank∞ } (24*k' + 33)
    = { state := some stA, head := false,
        left := Side.prepend (ones 1) Y,
        right := Side.prepend (zebra (4*k' + 7)) blank∞ } := by
  rw [show 24*k' + 33 = 4*(4*k' + 3) + (4 + (3 + (2*(4*k' + 5) + 4))) from by ring]
  -- Phase 1: drainA_cycle_iter
  rw [srun_add,
      show (zebra (4*k' + 3) : List Sym) = zebra ((4*k' + 3) + 0) from by norm_num,
      drainA_cycle_iter (4*k' + 3) 0
        (Side.prepend (ones 2) (Side.prepend [false, true] Y)) blank∞,
      show Side.prepend (zebra 0) blank∞ = blank∞ from rfl]
  -- Phase 2: drainEdge_4step
  rw [srun_add, drainEdge_4step
    (Side.prepend (zebra (4*k' + 3))
      (Side.prepend (ones 2) (Side.prepend [false, true] Y))),
      zebra_succ_fold (4*k' + 3)
        (Side.prepend (ones 2) (Side.prepend [false, true] Y))]
  -- Phase 3: A_to_D_3step
  rw [srun_add, A_to_D_3step
    (Side.prepend (zebra (4*k' + 3 + 1))
      (Side.prepend (ones 2) (Side.prepend [false, true] Y))),
      zebra_tft_fold (4*k' + 3 + 1)
        (Side.prepend (ones 2) (Side.prepend [false, true] Y))]
  -- Phase 4: leftZebra_consume_iter
  rw [srun_add,
      show (4*k' + 3 + 1 + 1 : Nat) = (4*k' + 5) + 0 from by ring,
      leftZebra_consume_iter (4*k' + 5) 0
        (Side.prepend (ones 2) (Side.prepend [false, true] Y)) blank∞,
      show Side.prepend (zebra 0)
            (Side.prepend (ones 2) (Side.prepend [false, true] Y))
        = Side.prepend (ones 2) (Side.prepend [false, true] Y) from rfl,
      cons_true_ones_fold 2 (Side.prepend [false, true] Y)]
  -- Phase 5: reentry_4step_abs with X = [F, T] *> Y; X.head = F, X.tail = [T] *> Y = ones 1 *> Y
  rw [show (2 + 1 : Nat) = 3 from rfl,
      reentry_4step_abs (Side.prepend [false, true] Y)
        (Side.prepend (zebra (4*k' + 5)) blank∞)]
  -- Simplify: X.head = false, X.tail = Side.prepend [true] Y = ones 1 *> Y
  rw [show (Side.prepend [false, true] Y).head = false from rfl,
      show (Side.prepend [false, true] Y).tail = Side.prepend [true] Y from rfl,
      show (Side.prepend [true] Y : Side) = Side.prepend (ones 1) Y from rfl]
  -- Fold zebra 2 *> zebra (4k'+5) = zebra (4k'+7)
  rw [show Side.prepend (zebra 2) (Side.prepend (zebra (4*k' + 5)) blank∞)
        = Side.prepend (zebra (4*k' + 7)) blank∞ from by
      rw [← Side.prepend_append, zebra_append,
          show 2 + (4*k' + 5) = 4*k' + 7 from by ring]]

/-- **Start config reshape for `rule_R1`** — converts `C_Config (a+1) (3*(k'+1))`
    into the canonical rightPush-compatible form with `[F, T, T]` prefix and
    an explicit `[F, T] *> aBlocks a *> blank` tail after the ones.  Uses
    `ones_append` to merge `ones (3k'+3) ++ [T, T]` into `ones (3k'+5)`. -/
private lemma rule_R1_start_eq (a k' : Nat) :
    C_Config (a+1) (3*(k'+1)) =
      { state := some stC, head := false,
        left := Side.prepend [false, true, true]
                  (Side.prepend (ones (3*k' + 4))
                    (Side.prepend [false, true]
                      (Side.prepend (aBlocks a) blank∞))),
        right := blank∞ } := by
  unfold C_Config
  simp only [aBlocks, block1011]
  congr 1
  rw [← Side.prepend_append, ← Side.prepend_append, ← Side.prepend_append]
  congr 1
  -- Pure list equality.
  rw [show (3*(k'+1) : Nat) = 3*k' + 3 from by ring]
  have lhs_eq : (false :: true :: (ones (3*k'+3) ++ ([true, true, false, true] ++ aBlocks a)) : List Sym)
              = [false, true] ++ ones (3*k'+5) ++ [false, true] ++ aBlocks a := by
    show ([false, true] ++ (ones (3*k'+3) ++ ([true, true, false, true] ++ aBlocks a)) : List Sym)
       = [false, true] ++ ones (3*k'+5) ++ [false, true] ++ aBlocks a
    rw [show ([true, true, false, true] : List Sym) = ones 2 ++ [false, true] from rfl]
    rw [show (ones (3*k'+3) ++ (ones 2 ++ [false, true] ++ aBlocks a) : List Sym)
          = (ones (3*k'+3) ++ ones 2) ++ [false, true] ++ aBlocks a from by
        simp only [List.append_assoc]]
    rw [ones_append, show (3*k'+3 + 2 : Nat) = 3*k'+5 from by ring]
    simp only [List.append_assoc]
  have rhs_eq : ([false, true, true] ++ ones (3*k'+4) ++ [false, true] ++ aBlocks a : List Sym)
              = [false, true] ++ ones (3*k'+5) ++ [false, true] ++ aBlocks a := by
    rw [show ([false, true, true] : List Sym) = [false, true] ++ ones 1 from rfl]
    rw [show (([false, true] ++ ones 1) ++ ones (3*k'+4) : List Sym)
          = [false, true] ++ (ones 1 ++ ones (3*k'+4)) from by
        simp only [List.append_assoc]]
    rw [ones_append, show (1 + (3*k'+4) : Nat) = 3*k'+5 from by ring]
  rw [lhs_eq, ← rhs_eq]

/-- **Step-count arithmetic for `rule_E2`** (`k ≥ 1` case via `k = k'+1`).  Same
    structure as `step_count_E3` but with 2 extra steps in final iter (24(k'+1)+11
    instead of 24(k'+1)+9). -/
private lemma step_count_E2 (k' : Nat) :
    12*(k'+1)*(k'+1) + 53*(k'+1) + 30 =
      5 + (2 + ((12*k'*k' + 21*k') + ((24*(k'+1) + 11) + ((32*(k'+1) + 16) + 5)))) := by
  ring

/-- **Step-count arithmetic for `rule_E3`** (`k ≥ 1` case via `k = k'+1`).

    The full step count `12·k² + 53·k + 28` decomposes into the sum of:
    * `7` — opening (rightPush_5step + zebraExtend_2step)
    * `12·k'² + 21·k'` — `outer_iter_iter i=k'` (bulk of k' non-final outer iterations)
    * `24·(k'+1) + 9 = 24k + 9` — final iter body (drainA + drainEdge + A_to_D +
      leftZebra_consume) + reentry_4step
    * `32·(k'+1) + 16 = 32k + 16` — zebraA_cycle_iter N=(4k+2)
    * `5` — cleanup_5step

    Verified by `ring`.  Use at the `rule_E3` call site to split the
    step count cleanly for `srun_add` chaining. -/
private lemma step_count_E3 (k' : Nat) :
    12*(k'+1)*(k'+1) + 53*(k'+1) + 28 =
      5 + (2 + ((12*k'*k' + 21*k') + ((24*(k'+1) + 9) + ((32*(k'+1) + 16) + 5)))) := by
  ring

/-- **Cleanup phase (5 steps)** — terminates the R1/E3 trajectory.  From
    state A reading 0 with `ones n *> blank∞` on the left and exactly
    one zebra pair `[false, true] *> blank∞` on the right, 5 TM steps
    finish the rule: `A,0→1RB; B,0→0RC; C,1→0LA; A,0→1RB; B,0→0RC`
    leaving state C at the right blank with `[false] ++ ones (n+2)` on
    the left — which is exactly `C_Config 0 (n+1)`. -/
lemma cleanup_5step (n : Nat) :
    srun tm
      { state := some stA, head := false,
        left := ones n *> blank∞,
        right := [false, true] *> blank∞ } 5
    = { state := some stC, head := false,
        left := false :: ones (n + 2) *> blank∞,
        right := blank∞ } := by
  simp [srun, sstep, tm, show ones (n + 2) = true :: true :: ones n from rfl]

/-- **Iterated zebra-consume cycle** (induction on `N`).  Starting from state
    A with `N+1` zebra pairs on the right, run `8N` steps to reduce them to
    `zebra 1` (one pair), growing the left `ones n` by `2N`. -/
lemma zebraA_cycle_iter (N : Nat) : ∀ (n : Nat) (M R : Side),
    srun tm
      { state := some stA, head := false,
        left := ones n *> M,
        right := zebra (N + 1) *> R } (8 * N)
    = { state := some stA, head := false,
        left := ones (n + 2 * N) *> M,
        right := zebra 1 *> R } := by
  induction N with
  | zero =>
    intro n M R
    simp [srun]
  | succ N' ih =>
    intro n M R
    -- Peel one cycle, then apply IH
    have hz : zebra (N' + 1 + 1) = [false, true, false, true] ++ zebra N' := by
      rw [zebra_succ, zebra_succ]; rfl
    have hz2 : [false, true] ++ zebra N' = zebra (N' + 1) := by
      rw [zebra_succ]; rfl
    rw [show 8 * (N' + 1) = 8 + 8 * N' from by ring, srun_add, hz,
        Side.prepend_append, zebraA_cycle_8step n M (zebra N' *> R),
        ← Side.prepend_append, hz2, ih (n + 2) M R,
        show n + 2 + 2 * N' = n + 2 * (N' + 1) from by ring]


/-- **Final iteration body** (24k'+33 steps) — the k'th (final) outer
    iteration with `reentry_4step` instead of `loop_chain_4step` as the
    trailing step.  Same phase structure as `outer_iter_step` but ending at
    state `A, head=0, left=blank∞` with `zebra (4k'+7)` on right, ready for
    `zebraA_cycle_iter`. -/
lemma final_iter_body (k' : Nat) :
    srun tm
      { state := some stA, head := true,
        left := Side.prepend (ones 2) blank∞,
        right := Side.prepend (zebra (4*k' + 3)) blank∞ } (24*k' + 33)
    = { state := some stA, head := false,
        left := blank∞,
        right := Side.prepend (zebra (4*k' + 7)) blank∞ } := by
  rw [show 24*k' + 33 = 4*(4*k' + 3) + (4 + (3 + (2*(4*k' + 5) + 4))) from by ring]
  -- Phase 1: drainA_cycle_iter
  rw [srun_add,
      show (zebra (4*k' + 3) : List Sym) = zebra ((4*k' + 3) + 0) from by norm_num,
      drainA_cycle_iter (4*k' + 3) 0 (Side.prepend (ones 2) blank∞) blank∞,
      show Side.prepend (zebra 0) blank∞ = blank∞ from rfl]
  -- Phase 2: drainEdge_4step
  rw [srun_add, drainEdge_4step
    (Side.prepend (zebra (4*k' + 3)) (Side.prepend (ones 2) blank∞)),
      zebra_succ_fold (4*k' + 3) (Side.prepend (ones 2) blank∞)]
  -- Phase 3: A_to_D_3step
  rw [srun_add, A_to_D_3step
    (Side.prepend (zebra (4*k' + 3 + 1)) (Side.prepend (ones 2) blank∞)),
      zebra_tft_fold (4*k' + 3 + 1) (Side.prepend (ones 2) blank∞)]
  -- Phase 4: leftZebra_consume_iter N=(4k'+5) K=0
  rw [srun_add,
      show (4*k' + 3 + 1 + 1 : Nat) = (4*k' + 5) + 0 from by ring,
      leftZebra_consume_iter (4*k' + 5) 0 (Side.prepend (ones 2) blank∞) blank∞,
      show Side.prepend (zebra 0) (Side.prepend (ones 2) blank∞)
        = Side.prepend (ones 2) blank∞ from rfl,
      cons_true_ones_fold 2 blank∞]
  -- Phase 5: reentry_4step (instead of loop_chain_4step)
  rw [show (2 + 1 : Nat) = 3 from rfl,
      reentry_4step (Side.prepend (zebra (4*k' + 5)) blank∞)]
  -- Fold: zebra 2 *> zebra (4k'+5) = zebra (4k'+7) — uses zebra_append + Nat arith.
  rw [show Side.prepend (zebra 2) (Side.prepend (zebra (4*k' + 5)) blank∞)
        = Side.prepend (zebra (4*k' + 7)) blank∞ from by
      rw [← Side.prepend_append, zebra_append,
          show 2 + (4*k' + 5) = 4*k' + 7 from by ring]]

/-- **Closing phase** (32k'+53 steps) — from post-`final_iter_body` state to
    target `C_Config 0 (8k'+13)`.  Comprises `zebraA_cycle_iter N=(4k'+6)`
    followed by `cleanup_5step n=(8k'+12)`. -/
lemma closing_phase (k' : Nat) :
    srun tm
      { state := some stA, head := false,
        left := blank∞,
        right := Side.prepend (zebra (4*k' + 7)) blank∞ } (32*(k'+1) + 16 + 5)
    = { state := some stC, head := false,
        left := Side.prepend (false :: ones (8*k' + 14)) blank∞,
        right := blank∞ } := by
  -- Split step count.
  rw [show 32*(k'+1) + 16 + 5 = 8*(4*k' + 6) + 5 from by ring, srun_add]
  -- Apply zebraA_cycle_iter via `have` + defeq coercion of the result.
  have hZ : srun tm
      { state := some stA, head := false,
        left := blank∞,
        right := Side.prepend (zebra (4*k' + 7)) blank∞ } (8*(4*k' + 6))
    = { state := some stA, head := false,
        left := Side.prepend (ones (8*k' + 12)) blank∞,
        right := Side.prepend [false, true] blank∞ } := by
    have := zebraA_cycle_iter (4*k' + 6) 0 blank∞ blank∞
    -- Simplify `0 + 2*(4*k'+6) = 8*k'+12` in the result.
    rw [show (0 + 2*(4*k' + 6) : Nat) = 8*k' + 12 from by ring] at this
    exact this
  rw [hZ, cleanup_5step (8*k' + 12)]

/-- **Generalized closing phase** — extends `closing_phase` to abstract
    initial ones count `n` and abstract left-tail `Y`.  For E3: `n=0,
    Y=blank∞`.  For R1: `n=1, Y=aBlocks a *> blank∞`. -/
lemma closing_phase_gen (n k' : Nat) (Y : Side) :
    srun tm
      { state := some stA, head := false,
        left := Side.prepend (ones n) Y,
        right := Side.prepend (zebra (4*k' + 7)) blank∞ } (32*(k'+1) + 16 + 5)
    = { state := some stC, head := false,
        left := Side.prepend (false :: ones (n + 8*k' + 14)) Y,
        right := blank∞ } := by
  rw [show 32*(k'+1) + 16 + 5 = 8*(4*k' + 6) + 5 from by ring, srun_add]
  have hZ : srun tm
      { state := some stA, head := false,
        left := Side.prepend (ones n) Y,
        right := Side.prepend (zebra (4*k' + 7)) blank∞ } (8*(4*k' + 6))
    = { state := some stA, head := false,
        left := Side.prepend (ones (n + 8*k' + 12)) Y,
        right := Side.prepend [false, true] blank∞ } := by
    have := zebraA_cycle_iter (4*k' + 6) n Y blank∞
    rw [show (n + 2*(4*k' + 6) : Nat) = n + 8*k' + 12 from by ring] at this
    exact this
  rw [hZ, cleanup_5step_abs (n + 8*k' + 12) Y]

-- ============================================================
-- Macro rules  (all sorried; verified empirically by sim.py verify)
-- ============================================================

set_option maxHeartbeats 400000 in
/-- **Rule R1** (`dt = 12k² + 53k + 28`).
    `C(a+1, 3k) → C(a, 8k+6)`.  One `(1011)` block from the left prefix
    is consumed; the right `1^{3k} 1 0` pattern is rewritten into
    `1^{8k+6} 1 0`.  Step count identical to `rule_E3`. -/
theorem rule_R1 (a k : Nat) :
    srun tm (C_Config (a + 1) (3 * k)) (12*k*k + 53*k + 28) =
      C_Config a (8 * k + 6) := by
  match k with
  | 0 =>
    -- rule_R1_base a inlined.
    simp only [C_Config, aBlocks, block1011]
    simp [srun, sstep, tm]
  | k' + 1 =>
    rw [step_count_E3 k']
    rw [rule_R1_start_eq a k']
    have hTarget : C_Config a (8*(k'+1)+6) =
        { state := some stC, head := false,
          left := Side.prepend (false :: ones (1 + 8*k' + 14))
            (Side.prepend (aBlocks a) blank∞),
          right := blank∞ } := by
      -- Use SConfig.ext to avoid `congr 1`'s whnf blowup.
      refine SConfig.ext rfl ?_ rfl rfl
      -- Remaining: left-field equality.
      show Side.prepend (false :: true :: (ones (8*(k'+1)+6) ++ aBlocks a)) blank∞
         = Side.prepend (false :: ones (1 + 8*k' + 14))
             (Side.prepend (aBlocks a) blank∞)
      rw [show (8*(k'+1)+6 : Nat) = 8*k' + 14 from by ring,
          show (1 + 8*k' + 14 : Nat) = 8*k' + 15 from by ring]
      rw [show (false :: true :: (ones (8*k' + 14) ++ aBlocks a) : List Sym)
            = (false :: ones (8*k' + 15)) ++ aBlocks a from rfl,
          Side.prepend_append]
    rw [hTarget]
    -- Phase 1 (5): rightPush_5step
    rw [srun_add, rightPush_5step
      (Side.prepend (ones (3*k' + 4))
        (Side.prepend [false, true] (Side.prepend (aBlocks a) blank∞)))]
    -- Phase 2 (2): zebraExtend_2step
    rw [show (Side.prepend (ones (3*k' + 4))
              (Side.prepend [false, true] (Side.prepend (aBlocks a) blank∞)) : Side)
          = Side.prepend [true]
              (Side.prepend (ones (3*k' + 3))
                (Side.prepend [false, true] (Side.prepend (aBlocks a) blank∞)))
        from by
        rw [show (ones (3*k' + 4) : List Sym) = [true] ++ ones (3*k' + 3) from rfl,
            Side.prepend_append],
        srun_add, zebraExtend_2step
          (Side.prepend (ones (3*k' + 3))
            (Side.prepend [false, true] (Side.prepend (aBlocks a) blank∞)))
          (Side.prepend [false, true, false, true] blank∞)]
    rw [show (Side.prepend (ones (3*k' + 3))
              (Side.prepend [false, true] (Side.prepend (aBlocks a) blank∞)) : Side).head
          = true from rfl,
        show (Side.prepend (ones (3*k' + 3))
              (Side.prepend [false, true] (Side.prepend (aBlocks a) blank∞)) : Side).tail
          = Side.prepend (ones (3*k' + 2))
              (Side.prepend [false, true] (Side.prepend (aBlocks a) blank∞)) from rfl]
    rw [show Side.prepend [false, true]
              (Side.prepend [false, true, false, true] blank∞)
          = Side.prepend (zebra 3) blank∞ from by
        rw [← Side.prepend_append]; rfl]
    -- Phase 3: outer_iter_iter_abs k' 0
    rw [show (Side.prepend (ones (3*k' + 2))
              (Side.prepend [false, true] (Side.prepend (aBlocks a) blank∞)) : Side)
          = Side.prepend (ones (3*(0 + k') + 2))
              (Side.prepend [false, true] (Side.prepend (aBlocks a) blank∞)) from by
        congr 2; ring,
        srun_add, outer_iter_iter_abs
          (Side.prepend [false, true] (Side.prepend (aBlocks a) blank∞)) k' 0]
    rw [show (3*0 + 2 : Nat) = 2 from rfl]
    -- Phase 4: final_iter_body_R1
    rw [show 24*(k'+1) + 9 = 24*k' + 33 from by ring,
        srun_add, final_iter_body_R1 (Side.prepend (aBlocks a) blank∞) k']
    -- Phase 5+6: closing_phase_gen with n=1, Y=aBlocks a *> blank
    exact closing_phase_gen 1 k' (Side.prepend (aBlocks a) blank∞)

/-- **R2 opening (7 steps)** — analogue of R1's `rightPush + zebraExtend` opener.
    From `C_Config (a+2) (3k+1)`, 7 TM steps reach state `A` with head `1`,
    left `ones (3k) *> [F,T] *> aBlocks (a+1) *> blank`, right `zebra 3 *> blank`.

    Unlike R1's opener (which leaves `aBlocks a` in the tail), R2's opener
    leaves `aBlocks (a+1)` — because the initial `(1011)^{a+2}` prefix has
    one more block than R1's `(1011)^{a+1}`.  Deep-sim trace confirmation:
    for every `k ≥ 0`, step 7 of `C(a+2, 3k+1)` is at state `A, head=1`,
    with the compact form `ones (3k) *> zebra 1 *> aBlocks (a+1)` on the
    left (here written as `ones (3k) *> [F,T] *> aBlocks (a+1)` =
    `ones (3k) *> zebra 1 *> aBlocks (a+1)`).

    Proof: reshape `C_Config` to a `[F,T,T] *> ones (3k+2) *> [F,T] *> aBlocks (a+1)`
    prefix by merging `[T,T]` from the first `(1011)` block into the ones; then
    apply `rightPush_5step` + `zebraExtend_2step`. -/
lemma rule_R2_opening (a k : Nat) :
    srun tm (C_Config (a+2) (3*k + 1)) 7 = {
      state := some stA, head := true,
      left := Side.prepend (ones (3*k))
                (Side.prepend [false, true]
                  (Side.prepend (aBlocks (a+1)) blank∞)),
      right := Side.prepend (zebra 3) blank∞ } := by
  -- Reshape: C_Config (a+2) (3k+1) with left = [F,T] ++ ones(3k+1) ++ aBlocks(a+2)
  -- becomes [F,T,T] *> ones(3k+2) *> [F,T] *> aBlocks (a+1) *> blank.
  -- Key merges: aBlocks (a+2) = [T,T,F,T] ++ aBlocks (a+1);
  --             [T,T,F,T] = ones 2 ++ [F,T];
  --             ones (3k+1) ++ ones 2 = ones (3k+3) = [T] ++ ones (3k+2).
  have hInit : C_Config (a+2) (3*k + 1) = {
      state := some stC, head := false,
      left := Side.prepend [false, true, true]
                (Side.prepend (ones (3*k + 2))
                  (Side.prepend [false, true]
                    (Side.prepend (aBlocks (a+1)) blank∞))),
      right := blank∞ } := by
    unfold C_Config
    simp only [aBlocks, block1011]
    congr 1
    rw [← Side.prepend_append, ← Side.prepend_append, ← Side.prepend_append]
    congr 1
    -- simp only [aBlocks, block1011] unfolded aBlocks (a+2) and aBlocks (a+1)
    -- in both sides to expose aBlocks a. Pure list equality:
    --   LHS: false :: true :: (ones (3k+1) ++ ([T,T,F,T] ++ ([T,T,F,T] ++ aBlocks a)))
    --   RHS: [F,T,T] ++ ones (3k+2) ++ [F,T] ++ ([T,T,F,T] ++ aBlocks a)
    -- Both sides canonicalize to:
    --   [F,T] ++ ones (3k+3) ++ [F,T] ++ ones 2 ++ [F,T] ++ aBlocks a.
    have lhs_eq : (false :: true :: (ones (3*k + 1) ++ ([true, true, false, true] ++
                    ([true, true, false, true] ++ aBlocks a))) : List Sym)
                = [false, true] ++ ones (3*k + 3) ++ [false, true] ++ ones 2
                    ++ [false, true] ++ aBlocks a := by
      show ([false, true] ++ (ones (3*k + 1) ++ ([true, true, false, true] ++
              ([true, true, false, true] ++ aBlocks a))) : List Sym) = _
      rw [show ([true, true, false, true] : List Sym) = ones 2 ++ [false, true] from rfl]
      rw [show (ones (3*k + 1) ++ ((ones 2 ++ [false, true]) ++
                (ones 2 ++ [false, true] ++ aBlocks a)) : List Sym)
            = (ones (3*k + 1) ++ ones 2) ++ [false, true] ++ ones 2
                ++ [false, true] ++ aBlocks a from by
          simp only [List.append_assoc]]
      rw [ones_append, show (3*k + 1 + 2 : Nat) = 3*k + 3 from by ring]
      simp only [List.append_assoc]
    have rhs_eq : ([false, true, true] ++ ones (3*k + 2) ++ [false, true] ++
                    ([true, true, false, true] ++ aBlocks a) : List Sym)
                = [false, true] ++ ones (3*k + 3) ++ [false, true] ++ ones 2
                    ++ [false, true] ++ aBlocks a := by
      rw [show ([false, true, true] : List Sym) = [false, true] ++ ones 1 from rfl,
          show ([true, true, false, true] : List Sym) = ones 2 ++ [false, true] from rfl]
      rw [show (([false, true] ++ ones 1) ++ ones (3*k + 2) : List Sym)
            = [false, true] ++ (ones 1 ++ ones (3*k + 2)) from by
          simp only [List.append_assoc]]
      rw [ones_append, show (1 + (3*k + 2) : Nat) = 3*k + 3 from by ring]
      simp only [List.append_assoc]
    rw [lhs_eq, ← rhs_eq]
  rw [hInit]
  rw [show (7 : Nat) = 5 + 2 from rfl, srun_add]
  -- Phase 1: rightPush_5step pops [F,T,T] from left, deposits zebra 2 on right.
  rw [rightPush_5step
        (Side.prepend (ones (3*k + 2))
          (Side.prepend [false, true]
            (Side.prepend (aBlocks (a+1)) blank∞)))]
  -- Reshape ones(3k+2) *> ... to [T] *> ones(3k+1) *> ...
  rw [show (Side.prepend (ones (3*k + 2))
            (Side.prepend [false, true]
              (Side.prepend (aBlocks (a+1)) blank∞)) : Side)
        = Side.prepend [true]
            (Side.prepend (ones (3*k + 1))
              (Side.prepend [false, true]
                (Side.prepend (aBlocks (a+1)) blank∞))) from by
      rw [show (ones (3*k + 2) : List Sym) = [true] ++ ones (3*k + 1) from rfl,
          Side.prepend_append]]
  -- Phase 2: zebraExtend_2step pops [T], moves head, prepends [F,T] to right.
  rw [zebraExtend_2step
        (Side.prepend (ones (3*k + 1))
          (Side.prepend [false, true]
            (Side.prepend (aBlocks (a+1)) blank∞)))
        (Side.prepend [false, true, false, true] blank∞)]
  -- Simplify L.head / L.tail for the inner prepend-chain:
  rw [show (Side.prepend (ones (3*k + 1))
            (Side.prepend [false, true]
              (Side.prepend (aBlocks (a+1)) blank∞)) : Side).head = true from rfl,
      show (Side.prepend (ones (3*k + 1))
            (Side.prepend [false, true]
              (Side.prepend (aBlocks (a+1)) blank∞)) : Side).tail
        = Side.prepend (ones (3*k))
            (Side.prepend [false, true]
              (Side.prepend (aBlocks (a+1)) blank∞)) from rfl]
  -- Fold right: [F,T] *> [F,T,F,T] *> blank = zebra 3 *> blank
  rw [show Side.prepend [false, true] (Side.prepend [false, true, false, true] blank∞)
        = Side.prepend (zebra 3) blank∞ from by
      rw [← Side.prepend_append]; rfl]

/-- **R2 final iteration** (`24k+35 steps`) — the last big-cycle of R2, playing the
    analogue of `final_iter_body_R1` but starting from R2's "no-ones-on-left"
    post-outer state `{A, T, [F,T] *> aBlocks (a+1) *> blank, zebra (4k+3) *>
    blank}` (no `ones 2` prefix, and with `aBlocks (a+1)` instead of
    `aBlocks a` as the tail).

    Phase breakdown (total `24k+35 = 4(4k+3) + 4 + 3 + 2(4k+6) + 4`):
    * `drainA_cycle_iter (4k+3) 0` — 16k+12 steps, consume all right-zebra,
      grow left by `zebra (4k+3)`.
    * `drainEdge_4step` — 4 steps, extend left by one more zebra pair.
    * `A_to_D_3step` — 3 steps, add `[T, F, T]` = `[T] ++ [F, T]` to left.
    * `leftZebra_consume_iter (4k+6) 0` — 8k+12 steps, move `4k+6` zebra pairs
      from left to right.
    * `reentry_4step_abs` — 4 steps, absorb `ones 3` (= `[T] ++ aBlocks (a+1)`
      after peeling the leading `[T,T]` of block1011 into `ones 2`, then
      prepending `[T]`) and deposit `zebra 2` on right.

    Output: `{A, F, ones 1 *> aBlocks a *> blank, zebra (4k+8) *> blank}` —
    one more zebra pair on right (`zebra (4k+8)` vs R1's `zebra (4k+7)`),
    leading to the off-by-one in the closing phase. -/
lemma rule_R2_final_iter (a k : Nat) :
    srun tm
      { state := some stA, head := true,
        left := Side.prepend [false, true] (Side.prepend (aBlocks (a+1)) blank∞),
        right := Side.prepend (zebra (4*k + 3)) blank∞ } (24*k + 35)
    = { state := some stA, head := false,
        left := Side.prepend (ones 1) (Side.prepend (aBlocks a) blank∞),
        right := Side.prepend (zebra (4*k + 8)) blank∞ } := by
  rw [show 24*k + 35 = 4*(4*k + 3) + (4 + (3 + (2*(4*k + 6) + 4))) from by ring]
  -- Phase 1: drainA_cycle_iter
  rw [srun_add,
      show (zebra (4*k + 3) : List Sym) = zebra ((4*k + 3) + 0) from by norm_num,
      drainA_cycle_iter (4*k + 3) 0
        (Side.prepend [false, true] (Side.prepend (aBlocks (a+1)) blank∞)) blank∞,
      show Side.prepend (zebra 0) blank∞ = blank∞ from rfl]
  -- Phase 2: drainEdge_4step
  rw [srun_add, drainEdge_4step
    (Side.prepend (zebra (4*k + 3))
      (Side.prepend [false, true] (Side.prepend (aBlocks (a+1)) blank∞))),
      zebra_succ_fold (4*k + 3)
        (Side.prepend [false, true] (Side.prepend (aBlocks (a+1)) blank∞))]
  -- Phase 3: A_to_D_3step
  rw [srun_add, A_to_D_3step
    (Side.prepend (zebra (4*k + 3 + 1))
      (Side.prepend [false, true] (Side.prepend (aBlocks (a+1)) blank∞))),
      zebra_tft_fold (4*k + 3 + 1)
        (Side.prepend [false, true] (Side.prepend (aBlocks (a+1)) blank∞))]
  -- Reshape zebra (4k+5) *> [F,T] *> X = zebra (4k+6) *> X
  rw [show Side.prepend (zebra (4*k + 3 + 1 + 1))
          (Side.prepend [false, true] (Side.prepend (aBlocks (a+1)) blank∞))
        = Side.prepend (zebra (4*k + 6)) (Side.prepend (aBlocks (a+1)) blank∞) from by
      rw [show (4*k + 3 + 1 + 1 : Nat) = 4*k + 5 from by ring,
          ← Side.prepend_append, ← zebra_succ_append,
          show (4*k + 5 + 1 : Nat) = 4*k + 6 from by ring]]
  -- Phase 4: leftZebra_consume_iter (4k+6) 0
  rw [srun_add,
      show (4*k + 6 : Nat) = (4*k + 6) + 0 from by norm_num,
      leftZebra_consume_iter (4*k + 6) 0
        (Side.prepend (aBlocks (a+1)) blank∞) blank∞,
      show Side.prepend (zebra 0) (Side.prepend (aBlocks (a+1)) blank∞)
        = Side.prepend (aBlocks (a+1)) blank∞ from rfl]
  -- Reshape [T] *> aBlocks(a+1) = ones 3 *> [F,T] *> aBlocks a
  rw [show Side.prepend [true] (Side.prepend (aBlocks (a+1)) blank∞)
        = Side.prepend (ones 3)
            (Side.prepend [false, true] (Side.prepend (aBlocks a) blank∞)) from by
      rw [show aBlocks (a+1) = block1011 ++ aBlocks a from rfl,
          show (block1011 : List Sym) = [true, true, false, true] from rfl,
          Side.prepend_append, ← Side.prepend_append,
          show ([true] ++ [true, true, false, true] : List Sym)
                = ones 3 ++ [false, true] from rfl,
          Side.prepend_append]]
  -- Phase 5: reentry_4step_abs
  rw [reentry_4step_abs
        (Side.prepend [false, true] (Side.prepend (aBlocks a) blank∞))
        (Side.prepend (zebra (4*k + 6)) blank∞)]
  rw [show (Side.prepend [false, true] (Side.prepend (aBlocks a) blank∞) : Side).head
        = false from rfl,
      show (Side.prepend [false, true] (Side.prepend (aBlocks a) blank∞) : Side).tail
        = Side.prepend [true] (Side.prepend (aBlocks a) blank∞) from rfl,
      show (Side.prepend [true] (Side.prepend (aBlocks a) blank∞) : Side)
        = Side.prepend (ones 1) (Side.prepend (aBlocks a) blank∞) from rfl]
  -- Fold zebra 2 *> zebra (4k+6) = zebra (4k+8)
  rw [show Side.prepend (zebra 2) (Side.prepend (zebra (4*k + 6)) blank∞)
        = Side.prepend (zebra (4*k + 8)) blank∞ from by
      rw [← Side.prepend_append, zebra_append,
          show (2 + (4*k + 6) : Nat) = 4*k + 8 from by ring]]

/-- **R2 closing phase** (`32k+61 steps`) — from post-final-iter state
    `{A, F, ones 1 *> aBlocks a *> blank, zebra (4k+8) *> blank}` reaches
    `C_Config a (8k+16)`.  Structurally `zebraA_cycle_iter (4k+7) + cleanup_5step_abs`.
    Differs from `closing_phase_gen 1 k (aBlocks a *> blank)` (which expects
    `zebra (4k+7)` input) by 8 extra drain steps from the extra zebra pair. -/
lemma rule_R2_closing (a k : Nat) :
    srun tm
      { state := some stA, head := false,
        left := Side.prepend (ones 1) (Side.prepend (aBlocks a) blank∞),
        right := Side.prepend (zebra (4*k + 8)) blank∞ } (32*k + 61)
    = C_Config a (8*k + 16) := by
  rw [show 32*k + 61 = 8*(4*k + 7) + 5 from by ring, srun_add]
  -- zebraA_cycle_iter (4k+7) n M R: input zebra ((4k+7)+1)=zebra(4k+8) ✓
  have hZ : srun tm
      { state := some stA, head := false,
        left := Side.prepend (ones 1) (Side.prepend (aBlocks a) blank∞),
        right := Side.prepend (zebra (4*k + 8)) blank∞ } (8*(4*k + 7))
    = { state := some stA, head := false,
        left := Side.prepend (ones (1 + 2*(4*k + 7))) (Side.prepend (aBlocks a) blank∞),
        right := Side.prepend [false, true] blank∞ } := by
    have := zebraA_cycle_iter (4*k + 7) 1 (Side.prepend (aBlocks a) blank∞) blank∞
    exact this
  rw [hZ, show (1 + 2*(4*k + 7) : Nat) = 8*k + 15 from by ring,
      cleanup_5step_abs (8*k + 15) (Side.prepend (aBlocks a) blank∞)]
  -- Result: {stC, F, false :: ones (8k+15+2) *> aBlocks a *> blank, blank}
  -- Target C_Config a (8k+16) uses (false :: true :: (ones (8k+16) ++ aBlocks a)) *> blank.
  unfold C_Config
  refine SConfig.ext rfl ?_ rfl rfl
  show Side.prepend (false :: ones (8*k + 15 + 2)) (Side.prepend (aBlocks a) blank∞)
     = Side.prepend (false :: true :: (ones (8*k + 16) ++ aBlocks a)) blank∞
  rw [show (8*k + 15 + 2 : Nat) = 8*k + 17 from by ring,
      show (ones (8*k + 17) : List Sym) = true :: ones (8*k + 16) from rfl,
      ← Side.prepend_append]
  rfl

/-- **Step-count arithmetic for `rule_R2`**: decomposes `12k²+77k+103` as
    `7 + (12k²+21k) + (24k+35) + (32k+61)`, matching opening + outer_iter_iter_gen +
    R2_final_iter + R2_closing. -/
private lemma step_count_R2 (k : Nat) :
    12*k*k + 77*k + 103 = 7 + ((12*k*k + 21*k) + ((24*k + 35) + (32*k + 61))) := by ring

/-- **Rule R2** (`dt = 12k² + 77k + 103`).
    `C(a+2, 3k+1) → C(a, 8k+16)`.  Two `(1011)` blocks from the left are
    consumed; requires `a+2 ≥ 2`.  Note the jump of two blocks — R2's
    `C(a+2, ·)` pattern ALSO covers `C(1, 3k+1)` but that case halts
    (see H1).

    Proof structure (deep-sim guided):
    * `rule_R2_opening` — 7 steps to `{A, T, ones (3k) *> [F,T] *> aBlocks (a+1), zebra 3}`.
    * `outer_iter_iter_gen` with `i=k`, `base=0` — 12k²+21k steps for k big outer cycles.
    * `rule_R2_final_iter` — 24k+35 steps for the (k+1)-th big cycle.
    * `rule_R2_closing` — 32k+61 steps to the target `C_Config a (8k+16)`.

    Total: 12k²+77k+103.  Unlike R1 (which splits on `k=0` / `k=k'+1`), this
    works uniformly for all `k ≥ 0` because `outer_iter_iter_gen` at `i=0` is
    a no-op and the other phases don't require `k ≥ 1`. -/
theorem rule_R2 (a k : Nat) :
    srun tm (C_Config (a + 2) (3 * k + 1)) (12*k*k + 77*k + 103) =
      C_Config a (8 * k + 16) := by
  rw [step_count_R2 k, srun_add, rule_R2_opening a k]
  rw [srun_add,
      show Side.prepend (ones (3*k))
              (Side.prepend [false, true] (Side.prepend (aBlocks (a+1)) blank∞))
          = Side.prepend (ones (3*k + 0))
              (Side.prepend [false, true] (Side.prepend (aBlocks (a+1)) blank∞)) from by
        rw [show (3*k + 0 : Nat) = 3*k from by ring],
      outer_iter_iter_gen
        (Side.prepend [false, true] (Side.prepend (aBlocks (a+1)) blank∞)) k 0]
  rw [srun_add, show (4*k + 3 : Nat) = 4*k + 3 from rfl,
      show Side.prepend (ones 0)
            (Side.prepend [false, true] (Side.prepend (aBlocks (a+1)) blank∞))
          = Side.prepend [false, true] (Side.prepend (aBlocks (a+1)) blank∞) from rfl,
      rule_R2_final_iter a k]
  exact rule_R2_closing a k

/-- **aBlock-peel transition (6 steps)** — used in R3's middle big cycle in
    place of R2's `reentry_4step_abs`.  From `{D, 0, [T,T,F,T] *> L, R}` where
    `[T,T,F,T]` = `block1011` is one aBlock, 6 TM steps consume the aBlock from
    the left and deposit `zebra 2` on the right:
      D,0→1LE; E,1→0LD; D,1→1LC; C,0→1RD; D,1→1LC; C,1→0LA.
    Each of the 6 transitions is mechanical; the final head symbol is `T` from
    the underlying tail `L`. -/
lemma aBlock_peel_6step (L R : Side) :
    srun tm
      { state := some stD, head := false,
        left := Side.prepend [true, true, false, true] L,
        right := R } 6
    = { state := some stA, head := true,
        left := L,
        right := Side.prepend (zebra 2) R } := by
  simp [srun, sstep, tm]

/-- **R3 opening (7 steps)** — analogous to `rule_R2_opening` but with
    `ones (3k+1)` prefix (one more T than R2) because R3's initial `b = 3k+2`
    has one more T than R2's `b = 3k+1`.  From `C_Config (a+2) (3k+2)`, 7 TM
    steps reach `{A, T, ones (3k+1) *> [F,T] *> aBlocks (a+1) *> blank, zebra 3 *> blank}`. -/
lemma rule_R3_opening (a k : Nat) :
    srun tm (C_Config (a+2) (3*k + 2)) 7 = {
      state := some stA, head := true,
      left := Side.prepend (ones (3*k + 1))
                (Side.prepend [false, true]
                  (Side.prepend (aBlocks (a+1)) blank∞)),
      right := Side.prepend (zebra 3) blank∞ } := by
  have hInit : C_Config (a+2) (3*k + 2) = {
      state := some stC, head := false,
      left := Side.prepend [false, true, true]
                (Side.prepend (ones (3*k + 3))
                  (Side.prepend [false, true]
                    (Side.prepend (aBlocks (a+1)) blank∞))),
      right := blank∞ } := by
    unfold C_Config
    simp only [aBlocks, block1011]
    congr 1
    rw [← Side.prepend_append, ← Side.prepend_append, ← Side.prepend_append]
    congr 1
    have lhs_eq : (false :: true :: (ones (3*k + 2) ++ ([true, true, false, true] ++
                    ([true, true, false, true] ++ aBlocks a))) : List Sym)
                = [false, true] ++ ones (3*k + 4) ++ [false, true] ++ ones 2
                    ++ [false, true] ++ aBlocks a := by
      show ([false, true] ++ (ones (3*k + 2) ++ ([true, true, false, true] ++
              ([true, true, false, true] ++ aBlocks a))) : List Sym) = _
      rw [show ([true, true, false, true] : List Sym) = ones 2 ++ [false, true] from rfl]
      rw [show (ones (3*k + 2) ++ ((ones 2 ++ [false, true]) ++
                (ones 2 ++ [false, true] ++ aBlocks a)) : List Sym)
            = (ones (3*k + 2) ++ ones 2) ++ [false, true] ++ ones 2
                ++ [false, true] ++ aBlocks a from by
          simp only [List.append_assoc]]
      rw [ones_append, show (3*k + 2 + 2 : Nat) = 3*k + 4 from by ring]
      simp only [List.append_assoc]
    have rhs_eq : ([false, true, true] ++ ones (3*k + 3) ++ [false, true] ++
                    ([true, true, false, true] ++ aBlocks a) : List Sym)
                = [false, true] ++ ones (3*k + 4) ++ [false, true] ++ ones 2
                    ++ [false, true] ++ aBlocks a := by
      rw [show ([false, true, true] : List Sym) = [false, true] ++ ones 1 from rfl,
          show ([true, true, false, true] : List Sym) = ones 2 ++ [false, true] from rfl]
      rw [show (([false, true] ++ ones 1) ++ ones (3*k + 3) : List Sym)
            = [false, true] ++ (ones 1 ++ ones (3*k + 3)) from by
          simp only [List.append_assoc]]
      rw [ones_append, show (1 + (3*k + 3) : Nat) = 3*k + 4 from by ring]
      simp only [List.append_assoc]
    rw [lhs_eq, ← rhs_eq]
  rw [hInit]
  rw [show (7 : Nat) = 5 + 2 from rfl, srun_add]
  rw [rightPush_5step
        (Side.prepend (ones (3*k + 3))
          (Side.prepend [false, true]
            (Side.prepend (aBlocks (a+1)) blank∞)))]
  rw [show (Side.prepend (ones (3*k + 3))
            (Side.prepend [false, true]
              (Side.prepend (aBlocks (a+1)) blank∞)) : Side)
        = Side.prepend [true]
            (Side.prepend (ones (3*k + 2))
              (Side.prepend [false, true]
                (Side.prepend (aBlocks (a+1)) blank∞))) from by
      rw [show (ones (3*k + 3) : List Sym) = [true] ++ ones (3*k + 2) from rfl,
          Side.prepend_append]]
  rw [zebraExtend_2step
        (Side.prepend (ones (3*k + 2))
          (Side.prepend [false, true]
            (Side.prepend (aBlocks (a+1)) blank∞)))
        (Side.prepend [false, true, false, true] blank∞)]
  rw [show (Side.prepend (ones (3*k + 2))
            (Side.prepend [false, true]
              (Side.prepend (aBlocks (a+1)) blank∞)) : Side).head = true from rfl,
      show (Side.prepend (ones (3*k + 2))
            (Side.prepend [false, true]
              (Side.prepend (aBlocks (a+1)) blank∞)) : Side).tail
        = Side.prepend (ones (3*k + 1))
            (Side.prepend [false, true]
              (Side.prepend (aBlocks (a+1)) blank∞)) from rfl]
  rw [show Side.prepend [false, true] (Side.prepend [false, true, false, true] blank∞)
        = Side.prepend (zebra 3) blank∞ from by
      rw [← Side.prepend_append]; rfl]

/-- **R3 extra iteration body** (24k+35 steps) — middle big-cycle of R3,
    analogous to `rule_R2_final_iter` but ending with `aBlock_peel_6step`
    (which peels one `aBlock` from `aBlocks(a+1)`) instead of `reentry_4step_abs`
    (which absorbs ones 3 and stops).  The `leftZebra_consume` phase has
    `4k+5` pairs (vs R2's `4k+6`), so the per-phase count `2(4k+5) + 6 =
    8k+16` matches R2's `2(4k+6) + 4 = 8k+16`.

    From `{A, T, ones 1 *> [F,T] *> aBlocks (a+1), zebra (4k+3)}`, 24k+35 TM
    steps reach `{A, T, aBlocks (a+1), zebra (4k+7)}`. -/
lemma rule_R3_extra_iter (a k : Nat) :
    srun tm
      { state := some stA, head := true,
        left := Side.prepend (ones 1)
                  (Side.prepend [false, true]
                    (Side.prepend (aBlocks (a+1)) blank∞)),
        right := Side.prepend (zebra (4*k + 3)) blank∞ } (24*k + 35)
    = { state := some stA, head := true,
        left := Side.prepend (aBlocks (a+1)) blank∞,
        right := Side.prepend (zebra (4*k + 7)) blank∞ } := by
  rw [show 24*k + 35 = 4*(4*k + 3) + (4 + (3 + (2*(4*k + 5) + 6))) from by ring]
  rw [srun_add,
      show (zebra (4*k + 3) : List Sym) = zebra ((4*k + 3) + 0) from by norm_num,
      drainA_cycle_iter (4*k + 3) 0
        (Side.prepend (ones 1)
          (Side.prepend [false, true]
            (Side.prepend (aBlocks (a+1)) blank∞))) blank∞,
      show Side.prepend (zebra 0) blank∞ = blank∞ from rfl]
  rw [srun_add, drainEdge_4step
    (Side.prepend (zebra (4*k + 3))
      (Side.prepend (ones 1)
        (Side.prepend [false, true]
          (Side.prepend (aBlocks (a+1)) blank∞)))),
      zebra_succ_fold (4*k + 3)
        (Side.prepend (ones 1)
          (Side.prepend [false, true]
            (Side.prepend (aBlocks (a+1)) blank∞)))]
  rw [srun_add, A_to_D_3step
    (Side.prepend (zebra (4*k + 3 + 1))
      (Side.prepend (ones 1)
        (Side.prepend [false, true]
          (Side.prepend (aBlocks (a+1)) blank∞)))),
      zebra_tft_fold (4*k + 3 + 1)
        (Side.prepend (ones 1)
          (Side.prepend [false, true]
            (Side.prepend (aBlocks (a+1)) blank∞)))]
  rw [srun_add,
      show (4*k + 3 + 1 + 1 : Nat) = (4*k + 5) + 0 from by ring,
      leftZebra_consume_iter (4*k + 5) 0
        (Side.prepend (ones 1)
          (Side.prepend [false, true]
            (Side.prepend (aBlocks (a+1)) blank∞))) blank∞,
      show Side.prepend (zebra 0)
            (Side.prepend (ones 1)
              (Side.prepend [false, true]
                (Side.prepend (aBlocks (a+1)) blank∞)))
        = Side.prepend (ones 1)
            (Side.prepend [false, true]
              (Side.prepend (aBlocks (a+1)) blank∞)) from rfl]
  -- Reshape [T] *> ones 1 *> [F,T] *> aBlocks(a+1) = [T,T,F,T] *> aBlocks(a+1)
  rw [show Side.prepend [true]
            (Side.prepend (ones 1)
              (Side.prepend [false, true]
                (Side.prepend (aBlocks (a+1)) blank∞)))
        = Side.prepend [true, true, false, true]
            (Side.prepend (aBlocks (a+1)) blank∞) from by
      rw [show (ones 1 : List Sym) = [true] from rfl,
          ← Side.prepend_append, ← Side.prepend_append,
          show ([true] ++ [true] ++ [false, true] : List Sym)
                = [true, true, false, true] from rfl]]
  rw [aBlock_peel_6step
        (Side.prepend (aBlocks (a+1)) blank∞)
        (Side.prepend (zebra (4*k + 5)) blank∞)]
  rw [show Side.prepend (zebra 2) (Side.prepend (zebra (4*k + 5)) blank∞)
        = Side.prepend (zebra (4*k + 7)) blank∞ from by
      rw [← Side.prepend_append, zebra_append,
          show (2 + (4*k + 5) : Nat) = 4*k + 7 from by ring]]

/-- **Step-count arithmetic for `rule_R3`**: decomposes `12k²+101k+184`. -/
private lemma step_count_R3 (k : Nat) :
    12*k*k + 101*k + 184
      = 7 + ((12*k*k + 21*k) + ((24*k + 35) + ((24*(k+1) + 33) + (32*(k+1) + 53)))) := by ring

/-- **Rule R3** (`dt = 12k² + 101k + 184`).
    `C(a+2, 3k+2) → C(a, 8k+22)`.  Analogue of R2 for the `3k+2` residue,
    with one extra big cycle (k+2 total vs R2's k+1).

    Proof pipeline:
    1. `rule_R3_opening` (7) — to `{A, T, ones (3k+1) *> [F,T] *> aBlocks (a+1), zebra 3}`.
    2. `outer_iter_iter_gen` `i=k` `base=1` (12k²+21k) — k big cycles.
    3. `rule_R3_extra_iter` (24k+35) — middle big cycle via `aBlock_peel_6step`.
    4. `final_iter_body_R1` with `k+1` (24k+57) — reshape `aBlocks(a+1) = ones 2 *> [F,T] *> aBlocks a`
       so the R1 pipeline applies with one extra iteration.
    5. `closing_phase_gen 1 (k+1) Y` (32k+85) — closes to `C_Config a (8k+22)`. -/
theorem rule_R3 (a k : Nat) :
    srun tm (C_Config (a + 2) (3 * k + 2)) (12*k*k + 101*k + 184) =
      C_Config a (8 * k + 22) := by
  rw [step_count_R3 k, srun_add, rule_R3_opening a k]
  -- Phase 2: outer_iter_iter_gen i=k, base=1
  rw [srun_add,
      show Side.prepend (ones (3*k + 1))
              (Side.prepend [false, true]
                (Side.prepend (aBlocks (a+1)) blank∞))
          = Side.prepend (ones (3*k + 1))
              (Side.prepend [false, true]
                (Side.prepend (aBlocks (a+1)) blank∞)) from rfl]
  have hOuter : srun tm
      { state := some stA, head := true,
        left := Side.prepend (ones (3*k + 1))
                  (Side.prepend [false, true]
                    (Side.prepend (aBlocks (a+1)) blank∞)),
        right := Side.prepend (zebra 3) blank∞ } (12*k*k + 21*k)
    = { state := some stA, head := true,
        left := Side.prepend (ones 1)
                  (Side.prepend [false, true]
                    (Side.prepend (aBlocks (a+1)) blank∞)),
        right := Side.prepend (zebra (4*k + 3)) blank∞ } := by
    exact outer_iter_iter_gen
      (Side.prepend [false, true] (Side.prepend (aBlocks (a+1)) blank∞)) k 1
  rw [hOuter]
  -- Phase 3: rule_R3_extra_iter
  rw [srun_add, rule_R3_extra_iter a k]
  -- Phase 4: final_iter_body_R1 with k'=k+1
  rw [srun_add]
  -- Reshape aBlocks(a+1) = ones 2 *> [F,T] *> aBlocks a
  rw [show Side.prepend (aBlocks (a+1)) blank∞
        = Side.prepend (ones 2)
            (Side.prepend [false, true]
              (Side.prepend (aBlocks a) blank∞)) from by
      rw [show aBlocks (a+1) = [true, true, false, true] ++ aBlocks a from rfl,
          show ([true, true, false, true] : List Sym) = ones 2 ++ [false, true] from rfl,
          Side.prepend_append, Side.prepend_append]]
  rw [show (4*k + 7 : Nat) = 4*(k+1) + 3 from by ring,
      final_iter_body_R1 (Side.prepend (aBlocks a) blank∞) (k+1)]
  -- Phase 5: closing_phase_gen 1 (k+1) Y
  have hTarget : C_Config a (8*k + 22) = {
      state := some stC, head := false,
      left := Side.prepend (false :: ones (1 + 8*(k+1) + 14))
                (Side.prepend (aBlocks a) blank∞),
      right := blank∞ } := by
    unfold C_Config
    refine SConfig.ext rfl ?_ rfl rfl
    show Side.prepend (false :: true :: (ones (8*k + 22) ++ aBlocks a)) blank∞
       = Side.prepend (false :: ones (1 + 8*(k+1) + 14)) (Side.prepend (aBlocks a) blank∞)
    rw [show (1 + 8*(k+1) + 14 : Nat) = 8*k + 23 from by ring,
        show (ones (8*k + 23) : List Sym) = true :: ones (8*k + 22) from rfl,
        ← Side.prepend_append]
    rfl
  rw [hTarget]
  exact closing_phase_gen 1 (k+1) (Side.prepend (aBlocks a) blank∞)

-- `rule_E1` is defined below (after `rule_E1_base` and H1 lemmas) due to
-- forward dependencies on `rule_E1_base`, `H1_transition_5step`, and
-- `H1_build_cycle_4step`.

/-- **Edge rule E2** (`dt = 12k² + 53k + 30`).
    `C(0, 3k+1) → C(0, 8k+5)`.  Left prefix stays empty; right block
    grows from `3k+1` to `8k+5`.

    **Proved** by case split on `k`:
    * `k = 0`: direct simp (C(0, 1) → C(0, 5) in 30 steps).
    * `k = k'+1`: structured composition via `outer_iter_iter_E2` +
      `final_iter_body_E2` + `closing_phase` (same closing as E3). -/
theorem rule_E2 (k : Nat) :
    srun tm (C_Config 0 (3 * k + 1)) (12*k*k + 53*k + 30) =
      C_Config 0 (8 * k + 5) := by
  match k with
  | 0 =>
    simp [C_Config, aBlocks, srun, sstep, tm]
  | k' + 1 =>
    rw [step_count_E2 k']
    have hStart : C_Config 0 (3*(k'+1)+1) =
        { state := some stC, head := false,
          left := Side.prepend [false, true, true]
            (Side.prepend (ones (3*k' + 3)) blank∞),
          right := blank∞ } := by
      unfold C_Config
      simp only [aBlocks, List.append_nil]
      rfl
    have hTarget : C_Config 0 (8*(k'+1)+5) =
        { state := some stC, head := false,
          left := Side.prepend (false :: ones (8*k' + 14)) blank∞,
          right := blank∞ } := by
      unfold C_Config
      simp only [aBlocks, List.append_nil]
      rfl
    rw [hStart, hTarget]
    -- Phase 1 (5): rightPush_5step
    rw [srun_add, rightPush_5step (Side.prepend (ones (3*k' + 3)) blank∞)]
    -- Phase 2 (2): zebraExtend_2step — reshape ones (3k'+3) = [T] ++ ones (3k'+2)
    rw [show (Side.prepend (ones (3*k' + 3)) blank∞ : Side)
          = Side.prepend [true] (Side.prepend (ones (3*k' + 2)) blank∞) from by
        rw [show (ones (3*k' + 3) : List Sym) = [true] ++ ones (3*k' + 2) from rfl,
            Side.prepend_append],
        srun_add, zebraExtend_2step (Side.prepend (ones (3*k' + 2)) blank∞)
          (Side.prepend [false, true, false, true] blank∞)]
    rw [show (Side.prepend (ones (3*k' + 2)) blank∞ : Side).head = true from rfl,
        show (Side.prepend (ones (3*k' + 2)) blank∞ : Side).tail
          = Side.prepend (ones (3*k' + 1)) blank∞ from rfl]
    rw [show Side.prepend [false, true]
              (Side.prepend [false, true, false, true] blank∞)
          = Side.prepend (zebra 3) blank∞ from by
        rw [← Side.prepend_append]; rfl]
    -- Phase 3: outer_iter_iter_E2 k' 0 — reshape ones (3k'+1) = ones (3*(0+k')+1)
    rw [show (Side.prepend (ones (3*k' + 1)) blank∞ : Side)
          = Side.prepend (ones (3*(0 + k') + 1)) blank∞ from by
        congr 2; ring,
        srun_add, outer_iter_iter_E2 k' 0]
    rw [show (3*0 + 1 : Nat) = 1 from rfl]
    -- Phase 4: final_iter_body_E2 — reshape step count 24*(k'+1)+11 = 24*k'+35
    rw [show 24*(k'+1) + 11 = 24*k' + 35 from by ring,
        srun_add, final_iter_body_E2 k']
    -- Phase 5+6: closing_phase (same as rule_E3)
    exact closing_phase k'

/-- **Edge rule E3** (`dt = 12k² + 53k + 28`).
    `C(0, 3k+2) → C(0, 8k+5)`.  Same destination as E2; different `dt`.

    **Proved** by case split on `k`:
    * `k = 0`: exact `rule_E3_base` (C(0, 2) → C(0, 5) in 28 steps).
    * `k = k'+1`: structured composition via the 14 proved shift/helper lemmas.
      Step count split by `step_count_E3 k'`:
        7 + (12k'² + 21k') + (24(k'+1)+9) + ((32(k'+1)+16) + 5) = 12(k'+1)² + 53(k'+1) + 28

    Phases:
      1. rightPush_5step (5)        — opening
      2. zebraExtend_2step (2)      — opening cont.
      3. outer_iter_iter k' (12k'²+21k') — all non-final outer iterations
      4. final_iter_body k' (24k'+33) — final iter body + reentry_4step
      5. closing_phase k' (32k'+53)   — zebraA_cycle_iter + cleanup_5step -/
theorem rule_E3 (k : Nat) :
    srun tm (C_Config 0 (3 * k + 2)) (12*k*k + 53*k + 28) =
      C_Config 0 (8 * k + 5) := by
  match k with
  | 0 =>
    -- Base case: C(0, 2) → C(0, 5) in 28 steps, direct simp.
    simp [C_Config, aBlocks, srun, sstep, tm]
  | k' + 1 =>
    rw [step_count_E3 k']
    -- Reshape start and target via C_Config/aBlocks unfolding.
    have hStart : C_Config 0 (3*(k'+1)+2) =
        { state := some stC, head := false,
          left := Side.prepend [false, true, true]
            (Side.prepend (ones (3*k' + 4)) blank∞),
          right := blank∞ } := by
      unfold C_Config
      simp only [aBlocks, List.append_nil]
      rfl
    have hTarget : C_Config 0 (8*(k'+1)+5) =
        { state := some stC, head := false,
          left := Side.prepend (false :: ones (8*k' + 14)) blank∞,
          right := blank∞ } := by
      unfold C_Config
      simp only [aBlocks, List.append_nil]
      rfl
    rw [hStart, hTarget]
    -- Phase 1 (5 steps): rightPush_5step
    rw [srun_add, rightPush_5step (Side.prepend (ones (3*k' + 4)) blank∞)]
    -- Phase 2 (2 steps): zebraExtend_2step — reshape ones (3k'+4) = [T] ++ ones (3k'+3)
    rw [show (Side.prepend (ones (3*k' + 4)) blank∞ : Side)
          = Side.prepend [true] (Side.prepend (ones (3*k' + 3)) blank∞) from by
        rw [show (ones (3*k' + 4) : List Sym) = [true] ++ ones (3*k' + 3) from rfl,
            Side.prepend_append],
        srun_add, zebraExtend_2step (Side.prepend (ones (3*k' + 3)) blank∞)
          (Side.prepend [false, true, false, true] blank∞)]
    -- After zebraExtend: head = T, left = ones (3k'+2) *> blank, right absorbs [F,T]
    rw [show (Side.prepend (ones (3*k' + 3)) blank∞ : Side).head = true from rfl,
        show (Side.prepend (ones (3*k' + 3)) blank∞ : Side).tail
          = Side.prepend (ones (3*k' + 2)) blank∞ from rfl]
    -- Fold right: [F,T] *> [F,T,F,T] = zebra 3
    rw [show Side.prepend [false, true]
              (Side.prepend [false, true, false, true] blank∞)
          = Side.prepend (zebra 3) blank∞ from by
        rw [← Side.prepend_append]; rfl]
    -- Phase 3: outer_iter_iter k' 0 — reshape ones (3k'+2) = ones (3*(0+k')+2)
    rw [show (Side.prepend (ones (3*k' + 2)) blank∞ : Side)
          = Side.prepend (ones (3*(0 + k') + 2)) blank∞ from by
        congr 2; ring,
        srun_add, outer_iter_iter k' 0]
    -- Simplify: 3*0+2 = 2, output config is {A, T, ones 2, zebra (4k'+3)}
    rw [show (3*0 + 2 : Nat) = 2 from rfl]
    -- Phase 4: final_iter_body — reshape step count 24*(k'+1)+9 = 24*k'+33
    rw [show 24*(k'+1) + 9 = 24*k' + 33 from by ring,
        srun_add, final_iter_body k']
    -- Phase 5+6: closing_phase
    exact closing_phase k'

/-- **H1 opening (7 steps)** — analogue of `rule_R2_opening` specialized to
    `C_Config 1 (3k+1)`.  Since `aBlocks 1 = block1011 = ones 2 ++ [F,T]`,
    the merging trick gives `[F,T] ++ ones(3k+1) ++ aBlocks 1 = [F,T] ++ ones(3k+3) ++ [F,T]`.
    After `rightPush_5step + zebraExtend_2step` reaches
    `{A, T, ones (3k) *> [F,T] *> blank∞, zebra 3 *> blank∞}`. -/
lemma rule_H1_opening (k : Nat) :
    srun tm (C_Config 1 (3*k + 1)) 7 = {
      state := some stA, head := true,
      left := Side.prepend (ones (3*k))
                (Side.prepend [false, true] blank∞),
      right := Side.prepend (zebra 3) blank∞ } := by
  have hInit : C_Config 1 (3*k + 1) = {
      state := some stC, head := false,
      left := Side.prepend [false, true, true]
                (Side.prepend (ones (3*k + 2))
                  (Side.prepend [false, true] blank∞)),
      right := blank∞ } := by
    unfold C_Config
    simp only [aBlocks, block1011]
    congr 1
    rw [← Side.prepend_append, ← Side.prepend_append]
    congr 1
    -- LHS: false :: true :: (ones (3k+1) ++ ([T,T,F,T] ++ []))
    -- RHS: [F,T,T] ++ ones(3k+2) ++ [F,T]
    -- After simp only [aBlocks, block1011], aBlocks 0 becomes [], so the goal has
    -- `[true, true, false, true] ++ []` which we simplify next.
    rw [List.append_nil]
    have lhs_eq : (false :: true :: (ones (3*k + 1) ++ [true, true, false, true]) : List Sym)
                = [false, true] ++ ones (3*k + 3) ++ [false, true] := by
      show ([false, true] ++ (ones (3*k + 1) ++ [true, true, false, true]) : List Sym) = _
      rw [show ([true, true, false, true] : List Sym) = ones 2 ++ [false, true] from rfl]
      rw [show (ones (3*k + 1) ++ (ones 2 ++ [false, true]) : List Sym)
            = (ones (3*k + 1) ++ ones 2) ++ [false, true] from by
          simp only [List.append_assoc]]
      rw [ones_append, show (3*k + 1 + 2 : Nat) = 3*k + 3 from by ring]
      simp only [List.append_assoc]
    have rhs_eq : ([false, true, true] ++ ones (3*k + 2) ++ [false, true] : List Sym)
                = [false, true] ++ ones (3*k + 3) ++ [false, true] := by
      rw [show ([false, true, true] : List Sym) = [false, true] ++ ones 1 from rfl]
      rw [show (([false, true] ++ ones 1) ++ ones (3*k + 2) : List Sym)
            = [false, true] ++ (ones 1 ++ ones (3*k + 2)) from by
          simp only [List.append_assoc]]
      rw [ones_append, show (1 + (3*k + 2) : Nat) = 3*k + 3 from by ring]
    rw [lhs_eq, ← rhs_eq]
  rw [hInit]
  rw [show (7 : Nat) = 5 + 2 from rfl, srun_add]
  rw [rightPush_5step
        (Side.prepend (ones (3*k + 2))
          (Side.prepend [false, true] blank∞))]
  rw [show (Side.prepend (ones (3*k + 2))
            (Side.prepend [false, true] blank∞) : Side)
        = Side.prepend [true]
            (Side.prepend (ones (3*k + 1))
              (Side.prepend [false, true] blank∞)) from by
      rw [show (ones (3*k + 2) : List Sym) = [true] ++ ones (3*k + 1) from rfl,
          Side.prepend_append]]
  rw [zebraExtend_2step
        (Side.prepend (ones (3*k + 1))
          (Side.prepend [false, true] blank∞))
        (Side.prepend [false, true, false, true] blank∞)]
  rw [show (Side.prepend (ones (3*k + 1))
            (Side.prepend [false, true] blank∞) : Side).head = true from rfl,
      show (Side.prepend (ones (3*k + 1))
            (Side.prepend [false, true] blank∞) : Side).tail
        = Side.prepend (ones (3*k))
            (Side.prepend [false, true] blank∞) from rfl]
  rw [show Side.prepend [false, true] (Side.prepend [false, true, false, true] blank∞)
        = Side.prepend (zebra 3) blank∞ from by
      rw [← Side.prepend_append]; rfl]

/-- **H1 drain phase** (24k+31 steps) — from the outer-iter output state
    `{A, T, [F,T] *> blank∞, zebra (4k+3) *> blank∞}`, 24k+31 steps do
    drainA_cycle_iter (4k+3) + drainEdge + A_to_D + leftZebra_consume_iter (4k+6)
    to reach `{D, F, ones 1 *> blank∞, zebra (4k+6) *> blank∞}`.

    Breakdown: `4(4k+3) + 4 + 3 + 2(4k+6) = 24k+31`. -/
lemma rule_H1_drain (k : Nat) :
    srun tm
      { state := some stA, head := true,
        left := Side.prepend [false, true] blank∞,
        right := Side.prepend (zebra (4*k + 3)) blank∞ } (24*k + 31)
    = { state := some stD, head := false,
        left := Side.prepend (ones 1) blank∞,
        right := Side.prepend (zebra (4*k + 6)) blank∞ } := by
  rw [show 24*k + 31 = 4*(4*k + 3) + (4 + (3 + 2*(4*k + 6))) from by ring]
  -- Phase 1: drainA_cycle_iter
  rw [srun_add,
      show (zebra (4*k + 3) : List Sym) = zebra ((4*k + 3) + 0) from by norm_num,
      drainA_cycle_iter (4*k + 3) 0
        (Side.prepend [false, true] blank∞) blank∞,
      show Side.prepend (zebra 0) blank∞ = blank∞ from rfl]
  -- Phase 2: drainEdge
  rw [srun_add, drainEdge_4step
    (Side.prepend (zebra (4*k + 3))
      (Side.prepend [false, true] blank∞)),
      zebra_succ_fold (4*k + 3) (Side.prepend [false, true] blank∞)]
  -- Phase 3: A_to_D
  rw [srun_add, A_to_D_3step
    (Side.prepend (zebra (4*k + 3 + 1))
      (Side.prepend [false, true] blank∞)),
      zebra_tft_fold (4*k + 3 + 1) (Side.prepend [false, true] blank∞)]
  -- Reshape [T] *> zebra (4k+5) *> [F,T] *> blank = [T] *> zebra (4k+6) *> blank
  rw [show Side.prepend (zebra (4*k + 3 + 1 + 1))
            (Side.prepend [false, true] blank∞)
        = Side.prepend (zebra (4*k + 6)) blank∞ from by
      rw [show (4*k + 3 + 1 + 1 : Nat) = 4*k + 5 from by ring,
          ← Side.prepend_append, ← zebra_succ_append,
          show (4*k + 5 + 1 : Nat) = 4*k + 6 from by ring]]
  -- Phase 4: leftZebra_consume_iter
  rw [show (2 * (4*k + 6) : Nat) = 2 * (4*k + 6) from rfl,
      show (4*k + 6 : Nat) = (4*k + 6) + 0 from by ring,
      leftZebra_consume_iter (4*k + 6) 0 blank∞ blank∞,
      show Side.prepend (zebra 0) blank∞ = blank∞ from rfl]
  -- Reshape [T] *> blank = ones 1 *> blank
  rw [show (Side.prepend [true] blank∞ : Side)
        = Side.prepend (ones 1) blank∞ from rfl]

/-- **H1 transition phase (5 steps)** — from `{D, F, ones 1 *> blank, zebra N *> blank}`
    reaches `{A, F, [F,T] *> blank, [T] *> zebra N *> blank}`.  Works for any `N ≥ 0`
    because `zebra 0 = []` makes `cons F (ones 1 *> zebra N *> blank) = zebra (N+1)`
    unfold correctly. -/
lemma H1_transition_5step (N : Nat) :
    srun tm
      { state := some stD, head := false,
        left := Side.prepend (ones 1) blank∞,
        right := Side.prepend (zebra N) blank∞ } 5
    = { state := some stA, head := false,
        left := Side.prepend [false, true] blank∞,
        right := Side.prepend [true] (Side.prepend (zebra N) blank∞) } := by
  -- Trace: D,0→E,1,blank,[T,zebra N];  E,1→D,0,blank,zebra(N+1);
  --        D,0→E,F,blank,[T,zebra(N+1)]; E,0→F,T,[T],zebra(N+1);
  --        F,1→A,F,[F,T],[T,zebra N].
  simp only [show (5 : Nat) = 1 + 1 + 1 + 1 + 1 from rfl, srun, sstep, tm,
             show (ones 1 : List Sym) = [true] from rfl]
  -- After full unfolding via simp, the result should be structurally the target.
  -- Rely on `Side.cons_false_blank` for blank absorption.
  rfl

/-- **H1 build cycle (4 steps)** — from `{A, F, [F,T] *> aBlocks a *> R, [T] *> zebra(m+2) *> blank}`
    reaches `{A, F, [F,T] *> aBlocks(a+1) *> R, [T] *> zebra m *> blank}`.
    Consumes one zebra pair from the right's middle segment and builds one more
    `aBlock` on the left. -/
lemma H1_build_cycle_4step (a m : Nat) (R : Side) :
    srun tm
      { state := some stA, head := false,
        left := Side.prepend [false, true] (Side.prepend (aBlocks a) R),
        right := Side.prepend [true] (Side.prepend (zebra (m + 2)) blank∞) } 4
    = { state := some stA, head := false,
        left := Side.prepend [false, true] (Side.prepend (aBlocks (a + 1)) R),
        right := Side.prepend [true] (Side.prepend (zebra m) blank∞) } := by
  rw [show (zebra (m + 2) : List Sym) = [false, true] ++ zebra (m + 1) from by
      rw [zebra_succ]; rfl,
      show (zebra (m + 1) : List Sym) = [false, true] ++ zebra m from by
      rw [zebra_succ]; rfl]
  simp only [Side.prepend_append, show aBlocks (a+1) = block1011 ++ aBlocks a from rfl,
             show (block1011 : List Sym) = [true, true, false, true] from rfl]
  simp [srun, sstep, tm]

/-- **H1 build cycle iteration** — iterated version of `H1_build_cycle_4step`.
    Starting from `aBlocks a` on the left with zebra `2N` on right, after 4N steps
    we have `aBlocks (a+N)` on the left and zebra 0 on right (absorbed into blank). -/
lemma H1_build_cycle_iter (N : Nat) : ∀ (a : Nat) (R : Side),
    srun tm
      { state := some stA, head := false,
        left := Side.prepend [false, true] (Side.prepend (aBlocks a) R),
        right := Side.prepend [true] (Side.prepend (zebra (2 * N)) blank∞) } (4 * N)
    = { state := some stA, head := false,
        left := Side.prepend [false, true] (Side.prepend (aBlocks (a + N)) R),
        right := Side.prepend [true] blank∞ } := by
  induction N with
  | zero =>
    intro a R
    show srun tm _ 0 = _
    simp [srun, zebra, show a + 0 = a from by omega]
  | succ N' ih =>
    intro a R
    have hsteps : 4 * (N' + 1) = 4 + 4 * N' := by ring
    have hzebra : 2 * (N' + 1) = (2 * N') + 2 := by ring
    rw [hsteps, srun_add, hzebra, H1_build_cycle_4step a (2 * N') R]
    rw [ih (a + 1) R]
    rw [show (a + 1 + N' : Nat) = a + (N' + 1) from by ring]

/-- **H1 wind-down (4 steps → halt)** — from `{A, F, [F,T] *> aBlocks N *> blank, [T] *> blank}`,
    4 TM steps reach the halting state (state = none).  The final transition is
    `F,0 → HALT`. -/
lemma H1_wind_down_4step (N : Nat) :
    (srun tm
      { state := some stA, head := false,
        left := Side.prepend [false, true] (Side.prepend (aBlocks N) blank∞),
        right := Side.prepend [true] blank∞ } 4).state = none := by
  simp [srun, sstep, tm]

/-- **H1 halt tail** (8k+21 steps → halt) — from `{D, F, ones 1 *> blank, zebra(4k+6) *> blank}`,
    the machine halts in exactly 8k+21 steps.

    Breakdown: `5` (transition_5step) `+ 4(2k+3)` (build_cycle_iter with N=2k+3)
    `+ 4` (wind_down_4step) `= 8k+21`. -/
lemma H1_halt_tail (k : Nat) :
    (srun tm
      { state := some stD, head := false,
        left := Side.prepend (ones 1) blank∞,
        right := Side.prepend (zebra (4*k + 6)) blank∞ } (8*k + 21)).state = none := by
  rw [show 8*k + 21 = 5 + (4*(2*k + 3) + 4) from by ring, srun_add,
      H1_transition_5step (4*k + 6), srun_add]
  -- After H1_transition_5step: left = [F,T] *> blank∞. Reshape to
  -- [F,T] *> aBlocks 0 *> blank∞ so H1_build_cycle_iter applies with a=0.
  rw [show (Side.prepend [false, true] blank∞ : Side)
        = Side.prepend [false, true] (Side.prepend (aBlocks 0) blank∞) from rfl]
  -- Reshape: zebra(4k+6) matches zebra(2*(2k+3)) for build_cycle_iter.
  rw [show (4*k + 6 : Nat) = 2 * (2*k + 3) from by ring,
      H1_build_cycle_iter (2*k + 3) 0 blank∞]
  -- Now: {A, F, [F,T] *> aBlocks(0 + (2k+3)) *> blank, [T] *> blank}
  -- Apply H1_wind_down_4step with N = 2k+3.
  rw [show (0 + (2*k + 3) : Nat) = 2*k + 3 from by ring]
  exact H1_wind_down_4step (2*k + 3)

/-- **Step-count arithmetic for `rule_H1`**: decomposes `12k²+53k+59` as
    `7 + (12k²+21k) + (24k+31) + (8k+21)`. -/
private lemma step_count_H1 (k : Nat) :
    12*k*k + 53*k + 59 = 7 + ((12*k*k + 21*k) + ((24*k + 31) + (8*k + 21))) := by ring

/-- **Halt rule H1** (`dt = 12k² + 53k + 59`).
    `C(1, 3k+1) → Halt`.  The only family of halting macro
    configurations (beyond the degenerate start analog).

    Proof pipeline (4 phases):
    1. `rule_H1_opening` (7 steps) → `{A, T, ones(3k) *> [F,T] *> blank, zebra 3}`.
    2. `outer_iter_iter_gen i=k, base=0, L=[F,T]*>blank` (12k²+21k steps).
    3. `rule_H1_drain` (24k+31 steps) → `{D, F, ones 1 *> blank, zebra(4k+6) *> blank}`.
    4. `H1_halt_tail` (8k+21 steps → state = none) — includes 5-step transition,
       (2k+3) build cycles, and 4-step wind-down ending with F,0 → HALT. -/
theorem rule_H1 (k : Nat) :
    (srun tm (C_Config 1 (3 * k + 1)) (12*k*k + 53*k + 59)).state = none := by
  rw [step_count_H1 k, srun_add, rule_H1_opening k]
  rw [srun_add]
  -- Phase 2: outer_iter_iter_gen with i=k, base=0, L = [F,T]*>blank
  have hOuter : srun tm
      { state := some stA, head := true,
        left := Side.prepend (ones (3*k))
                  (Side.prepend [false, true] blank∞),
        right := Side.prepend (zebra 3) blank∞ } (12*k*k + 21*k)
    = { state := some stA, head := true,
        left := Side.prepend [false, true] blank∞,
        right := Side.prepend (zebra (4*k + 3)) blank∞ } := by
    have := outer_iter_iter_gen (Side.prepend [false, true] blank∞) k 0
    rw [show (3*k + 0 : Nat) = 3*k from by ring] at this
    simp only [show Side.prepend (ones 0)
              (Side.prepend [false, true] blank∞)
                = Side.prepend [false, true] blank∞ from rfl] at this
    exact this
  rw [hOuter]
  rw [srun_add, rule_H1_drain k]
  exact H1_halt_tail k

-- `rule_E4` is defined after E1 helpers (it reuses `E1_build_iter`,
-- `E1_edge_build_4step`, `rule_E1_reduce`, `rule_E1_fill`) and uses
-- `aBlock_peel_6step`, `H1_transition_5step`, etc.

-- ============================================================
-- Base cases verifiable by direct `simp` (sanity checks)
-- ============================================================

/-- Base case of R1 at `k = 0`: `C(a+1, 0) → C(a, 6)` in 28 steps.
    Abstract in `a` (rule is independent of left prefix). -/
theorem rule_R1_base (a : Nat) :
    srun tm (C_Config (a + 1) 0) 28 = C_Config a 6 := by
  -- Unfold one `(1011)` block; abstract `a` remains in the tail.
  simp only [C_Config, aBlocks, block1011]
  simp [srun, sstep, tm]

/-- Base case of E1 at `k = 0` (= the start case):
    `C(0, 0) → C(0, 8)` in 52 steps. -/
theorem rule_E1_base :
    srun tm (C_Config 0 0) 52 = C_Config 0 8 := by
  -- `a = 0` so left-side `aBlocks 0 = []` — fully reducible by `simp`.
  simp [C_Config, aBlocks, srun, sstep, tm]

-- ============================================================
-- E1 helper lemmas (depend on rule_E1_base and H1 lemmas)
-- ============================================================

/-- **E1 opening (7 steps)** — for `k = k'+1 ≥ 1`, analogous to other openers
    but with `aBlocks 0 = []` on the tail.  Takes `C_Config 0 (3k)` to
    `{A, T, ones (3k') *> blank∞, zebra 3 *> blank∞}`. -/
lemma rule_E1_opening (k' : Nat) :
    srun tm (C_Config 0 (3*(k' + 1))) 7 = {
      state := some stA, head := true,
      left := Side.prepend (ones (3*k')) blank∞,
      right := Side.prepend (zebra 3) blank∞ } := by
  have hInit : C_Config 0 (3*(k' + 1)) = {
      state := some stC, head := false,
      left := Side.prepend [false, true, true]
                (Side.prepend (ones (3*k' + 2)) blank∞),
      right := blank∞ } := by
    unfold C_Config
    simp only [aBlocks]
    congr 1
    rw [← Side.prepend_append]
    congr 1
    rw [List.append_nil]
    show (false :: true :: ones (3*(k'+1)) : List Sym)
       = [false, true, true] ++ ones (3*k' + 2)
    rw [show ([false, true, true] : List Sym) = [false, true] ++ ones 1 from rfl]
    rw [show ([false, true] ++ ones 1 ++ ones (3*k' + 2) : List Sym)
          = [false, true] ++ (ones 1 ++ ones (3*k' + 2)) from by
        simp only [List.append_assoc]]
    rw [ones_append, show (1 + (3*k' + 2) : Nat) = 3*(k'+1) from by ring]
    rfl
  rw [hInit]
  rw [show (7 : Nat) = 5 + 2 from rfl, srun_add]
  rw [rightPush_5step (Side.prepend (ones (3*k' + 2)) blank∞)]
  rw [show (Side.prepend (ones (3*k' + 2)) blank∞ : Side)
        = Side.prepend [true] (Side.prepend (ones (3*k' + 1)) blank∞) from by
      rw [show (ones (3*k' + 2) : List Sym) = [true] ++ ones (3*k' + 1) from rfl,
          Side.prepend_append]]
  rw [zebraExtend_2step (Side.prepend (ones (3*k' + 1)) blank∞)
        (Side.prepend [false, true, false, true] blank∞)]
  rw [show (Side.prepend (ones (3*k' + 1)) blank∞ : Side).head = true from rfl,
      show (Side.prepend (ones (3*k' + 1)) blank∞ : Side).tail
        = Side.prepend (ones (3*k')) blank∞ from rfl]
  rw [show Side.prepend [false, true] (Side.prepend [false, true, false, true] blank∞)
        = Side.prepend (zebra 3) blank∞ from by
      rw [← Side.prepend_append]; rfl]

/-- **E1 final iteration** (`24k'+34` steps) — the `k`-th (last) outer iteration
    for E1 at `k = k'+1`, ending with `H1_transition_5step` (not reentry). -/
lemma rule_E1_final_iter (k' : Nat) :
    srun tm
      { state := some stA, head := true,
        left := blank∞,
        right := Side.prepend (zebra (4*k' + 3)) blank∞ } (24*k' + 34)
    = { state := some stA, head := false,
        left := Side.prepend [false, true] blank∞,
        right := Side.prepend [true]
                   (Side.prepend (zebra (4*k' + 5)) blank∞) } := by
  rw [show 24*k' + 34 = 4*(4*k' + 3) + (4 + (3 + (2*(4*k' + 5) + 5))) from by ring]
  rw [srun_add,
      show (zebra (4*k' + 3) : List Sym) = zebra ((4*k' + 3) + 0) from by norm_num,
      drainA_cycle_iter (4*k' + 3) 0 blank∞ blank∞,
      show Side.prepend (zebra 0) blank∞ = blank∞ from rfl]
  rw [srun_add, drainEdge_4step (Side.prepend (zebra (4*k' + 3)) blank∞),
      zebra_succ_fold (4*k' + 3) blank∞]
  rw [srun_add, A_to_D_3step (Side.prepend (zebra (4*k' + 3 + 1)) blank∞),
      zebra_tft_fold (4*k' + 3 + 1) blank∞]
  rw [srun_add,
      show (4*k' + 3 + 1 + 1 : Nat) = (4*k' + 5) + 0 from by ring,
      leftZebra_consume_iter (4*k' + 5) 0 blank∞ blank∞,
      show Side.prepend (zebra 0) blank∞ = blank∞ from rfl]
  exact H1_transition_5step (4*k' + 5)

/-- **E1 build iteration** (`4N` steps) — iterated build cycle generalizing
    `H1_build_cycle_iter` to arbitrary initial zebra count `m + 2N`. -/
lemma E1_build_iter (N : Nat) : ∀ (a m : Nat) (R : Side),
    srun tm
      { state := some stA, head := false,
        left := Side.prepend [false, true] (Side.prepend (aBlocks a) R),
        right := Side.prepend [true]
                   (Side.prepend (zebra (m + 2*N)) blank∞) } (4 * N)
    = { state := some stA, head := false,
        left := Side.prepend [false, true] (Side.prepend (aBlocks (a + N)) R),
        right := Side.prepend [true]
                   (Side.prepend (zebra m) blank∞) } := by
  induction N with
  | zero =>
    intro a m R
    show srun tm _ 0 = _
    simp [srun, show a + 0 = a from by omega]
  | succ N' ih =>
    intro a m R
    rw [show 4 * (N' + 1) = 4 + 4 * N' from by ring, srun_add]
    rw [show (m + 2 * (N' + 1) : Nat) = (m + 2*N') + 2 from by ring,
        H1_build_cycle_4step a (m + 2*N') R]
    rw [ih (a + 1) m R,
        show (a + 1 + N' : Nat) = a + (N' + 1) from by ring]

/-- **E1 edge build cycle (4 steps)** — handles the final build cycle where right
    has `zebra 1`.  Transforms to `blank∞` on right, building one more aBlock. -/
lemma E1_edge_build_4step (a : Nat) (R : Side) :
    srun tm
      { state := some stA, head := false,
        left := Side.prepend [false, true] (Side.prepend (aBlocks a) R),
        right := Side.prepend [true]
                   (Side.prepend (zebra 1) blank∞) } 4
    = { state := some stA, head := false,
        left := Side.prepend [false, true] (Side.prepend (aBlocks (a + 1)) R),
        right := blank∞ } := by
  simp only [show zebra 1 = [false, true] from rfl,
             show aBlocks (a+1) = block1011 ++ aBlocks a from rfl,
             show (block1011 : List Sym) = [true, true, false, true] from rfl,
             Side.prepend_append]
  simp [srun, sstep, tm]

/-- **E1 reduce phase (11 steps)** — after the build phase, reduces one aBlock
    while adding zebra 4 to right.  A_to_D + leftZebra_consume(2) + reentry_4step_abs. -/
lemma rule_E1_reduce (a : Nat) :
    srun tm
      { state := some stA, head := false,
        left := Side.prepend [false, true]
                  (Side.prepend (aBlocks (a + 1)) blank∞),
        right := blank∞ } 11
    = { state := some stA, head := false,
        left := Side.prepend (ones 1) (Side.prepend (aBlocks a) blank∞),
        right := Side.prepend (zebra 4) blank∞ } := by
  rw [show (11 : Nat) = 3 + (2*2 + 4) from rfl]
  rw [srun_add, A_to_D_3step
        (Side.prepend [false, true] (Side.prepend (aBlocks (a+1)) blank∞))]
  -- Reshape [T, F, T] *> [F, T] *> aBlocks(a+1) = [T] *> zebra 2 *> aBlocks(a+1)
  rw [show Side.prepend [true, false, true]
            (Side.prepend [false, true] (Side.prepend (aBlocks (a+1)) blank∞))
        = Side.prepend [true] (Side.prepend (zebra 2)
                                 (Side.prepend (aBlocks (a+1)) blank∞)) from by
      rw [show ([true, false, true] : List Sym) = [true] ++ [false, true] from rfl]
      rw [Side.prepend_append]
      rw [show Side.prepend [false, true]
              (Side.prepend [false, true] (Side.prepend (aBlocks (a+1)) blank∞))
            = Side.prepend (zebra 2) (Side.prepend (aBlocks (a+1)) blank∞) from by
          rw [← Side.prepend_append]; rfl]]
  rw [srun_add,
      show (2 : Nat) = 2 + 0 from rfl,
      leftZebra_consume_iter 2 0
        (Side.prepend (aBlocks (a+1)) blank∞) blank∞,
      show Side.prepend (zebra 0) (Side.prepend (aBlocks (a+1)) blank∞)
        = Side.prepend (aBlocks (a+1)) blank∞ from rfl]
  -- Reshape [T] *> aBlocks(a+1) = ones 3 *> [F,T] *> aBlocks a
  rw [show Side.prepend [true]
            (Side.prepend (aBlocks (a+1)) blank∞)
        = Side.prepend (ones 3)
            (Side.prepend [false, true] (Side.prepend (aBlocks a) blank∞)) from by
      rw [show aBlocks (a+1) = block1011 ++ aBlocks a from rfl,
          show (block1011 : List Sym) = [true, true, false, true] from rfl,
          Side.prepend_append, ← Side.prepend_append,
          show ([true] ++ [true, true, false, true] : List Sym)
                = ones 3 ++ [false, true] from rfl,
          Side.prepend_append]]
  rw [reentry_4step_abs
        (Side.prepend [false, true] (Side.prepend (aBlocks a) blank∞))
        (Side.prepend (zebra 2) blank∞)]
  rw [show (Side.prepend [false, true] (Side.prepend (aBlocks a) blank∞) : Side).head
        = false from rfl,
      show (Side.prepend [false, true] (Side.prepend (aBlocks a) blank∞) : Side).tail
        = Side.prepend [true] (Side.prepend (aBlocks a) blank∞) from rfl,
      show (Side.prepend [true] (Side.prepend (aBlocks a) blank∞) : Side)
        = Side.prepend (ones 1) (Side.prepend (aBlocks a) blank∞) from rfl]
  rw [show Side.prepend (zebra 2) (Side.prepend (zebra 2) blank∞)
        = Side.prepend (zebra 4) blank∞ from by
      rw [← Side.prepend_append, zebra_append]]

/-- **E1 fill phase (29 steps)** — `zebraA_cycle_iter 3 + cleanup_5step_abs`. -/
lemma rule_E1_fill (k' : Nat) :
    srun tm
      { state := some stA, head := false,
        left := Side.prepend (ones 1) (Side.prepend (aBlocks (2*k'+2)) blank∞),
        right := Side.prepend (zebra 4) blank∞ } 29
    = C_Config (2*k' + 2) 8 := by
  rw [show (29 : Nat) = 8*3 + 5 from rfl, srun_add]
  have hZ : srun tm
      { state := some stA, head := false,
        left := Side.prepend (ones 1) (Side.prepend (aBlocks (2*k'+2)) blank∞),
        right := Side.prepend (zebra 4) blank∞ } (8*3)
    = { state := some stA, head := false,
        left := Side.prepend (ones 7) (Side.prepend (aBlocks (2*k'+2)) blank∞),
        right := Side.prepend [false, true] blank∞ } := by
    have := zebraA_cycle_iter 3 1 (Side.prepend (aBlocks (2*k'+2)) blank∞) blank∞
    rw [show (1 + 2*3 : Nat) = 7 from by ring] at this
    exact this
  rw [hZ, cleanup_5step_abs 7 (Side.prepend (aBlocks (2*k'+2)) blank∞)]
  unfold C_Config
  refine SConfig.ext rfl ?_ rfl rfl
  show Side.prepend (false :: ones (7 + 2)) (Side.prepend (aBlocks (2*k'+2)) blank∞)
     = Side.prepend (false :: true :: (ones 8 ++ aBlocks (2*k'+2))) blank∞
  rw [show (7 + 2 : Nat) = 9 from rfl,
      show (ones 9 : List Sym) = true :: ones 8 from rfl,
      ← Side.prepend_append]
  rfl

/-- **Step-count arithmetic for `rule_E1`**. -/
private lemma step_count_E1 (k' : Nat) :
    12*(k'+1)*(k'+1) + 29*(k'+1) + 52
      = 7 + ((12*k'*k' + 21*k') + ((24*k' + 34) + ((4*(2*k'+2)) + (4 + (11 + 29))))) := by ring

/-- **Edge rule E1** (`dt = 12k² + 29k + 52`).
    `C(0, 3k) → C(2k, 8)`.  The left prefix is empty; machine creates `2k`
    fresh `(1011)` blocks.  Also covers initial case `C(0, 0) → C(0, 8)` (k=0).

    Pipeline (k = k'+1): opening + outer_iter_iter_gen(L=blank) + E1_final_iter +
    E1_build_iter(2k'+2) + E1_edge_build + E1_reduce + E1_fill. -/
theorem rule_E1 (k : Nat) :
    srun tm (C_Config 0 (3 * k)) (12*k*k + 29*k + 52) =
      C_Config (2 * k) 8 := by
  match k with
  | 0 =>
    show srun tm (C_Config 0 0) 52 = C_Config 0 8
    exact rule_E1_base
  | k' + 1 =>
    rw [step_count_E1 k', srun_add, rule_E1_opening k']
    rw [srun_add]
    have hOuter : srun tm
        { state := some stA, head := true,
          left := Side.prepend (ones (3*k')) blank∞,
          right := Side.prepend (zebra 3) blank∞ } (12*k'*k' + 21*k')
      = { state := some stA, head := true,
          left := blank∞,
          right := Side.prepend (zebra (4*k' + 3)) blank∞ } := by
      have := outer_iter_iter_gen blank∞ k' 0
      rw [show (3*k' + 0 : Nat) = 3*k' from by ring] at this
      rw [show Side.prepend (ones 0) blank∞ = blank∞ from rfl] at this
      exact this
    rw [hOuter]
    rw [srun_add, rule_E1_final_iter k']
    rw [srun_add]
    rw [show Side.prepend [false, true] blank∞
          = Side.prepend [false, true] (Side.prepend (aBlocks 0) blank∞) from rfl,
        show (4*k' + 5 : Nat) = 1 + 2*(2*k' + 2) from by ring]
    rw [E1_build_iter (2*k' + 2) 0 1 blank∞]
    rw [show (0 + (2*k' + 2) : Nat) = 2*k' + 2 from by ring]
    rw [srun_add, E1_edge_build_4step (2*k' + 2) blank∞]
    rw [srun_add]
    rw [show Side.prepend [false, true] (Side.prepend (aBlocks (2*k' + 2 + 1)) blank∞)
          = Side.prepend [false, true]
              (Side.prepend (aBlocks ((2*k' + 2) + 1)) blank∞) from rfl]
    rw [rule_E1_reduce (2*k' + 2)]
    have hTarget : C_Config (2 * (k' + 1)) 8 = C_Config (2*k' + 2) 8 := by
      rw [show (2 * (k' + 1) : Nat) = 2*k' + 2 from by ring]
    rw [hTarget]
    exact rule_E1_fill k'

-- ============================================================
-- E4 helper lemmas (depend on E1 helpers and H1 lemmas)
-- ============================================================

/-- **E4 opening (7 steps)** — analogous to E1's opening but from
    `C_Config 1 (3k+2)`.  Reaches `{A, T, ones (3k+1) *> [F,T] *> blank, zebra 3}`. -/
lemma rule_E4_opening (k : Nat) :
    srun tm (C_Config 1 (3*k + 2)) 7 = {
      state := some stA, head := true,
      left := Side.prepend (ones (3*k + 1))
                (Side.prepend [false, true] blank∞),
      right := Side.prepend (zebra 3) blank∞ } := by
  have hInit : C_Config 1 (3*k + 2) = {
      state := some stC, head := false,
      left := Side.prepend [false, true, true]
                (Side.prepend (ones (3*k + 3))
                  (Side.prepend [false, true] blank∞)),
      right := blank∞ } := by
    unfold C_Config
    simp only [aBlocks, block1011]
    congr 1
    rw [← Side.prepend_append, ← Side.prepend_append]
    congr 1
    rw [List.append_nil]
    have lhs_eq : (false :: true :: (ones (3*k + 2) ++
                    [true, true, false, true]) : List Sym)
                = [false, true] ++ ones (3*k + 4) ++ [false, true] := by
      show ([false, true] ++ (ones (3*k + 2) ++ [true, true, false, true]) : List Sym) = _
      rw [show ([true, true, false, true] : List Sym) = ones 2 ++ [false, true] from rfl]
      rw [show (ones (3*k + 2) ++ (ones 2 ++ [false, true]) : List Sym)
            = (ones (3*k + 2) ++ ones 2) ++ [false, true] from by
          simp only [List.append_assoc]]
      rw [ones_append, show (3*k + 2 + 2 : Nat) = 3*k + 4 from by ring]
      simp only [List.append_assoc]
    have rhs_eq : ([false, true, true] ++ ones (3*k + 3) ++ [false, true] : List Sym)
                = [false, true] ++ ones (3*k + 4) ++ [false, true] := by
      rw [show ([false, true, true] : List Sym) = [false, true] ++ ones 1 from rfl]
      rw [show (([false, true] ++ ones 1) ++ ones (3*k + 3) : List Sym)
            = [false, true] ++ (ones 1 ++ ones (3*k + 3)) from by
          simp only [List.append_assoc]]
      rw [ones_append, show (1 + (3*k + 3) : Nat) = 3*k + 4 from by ring]
    rw [lhs_eq, ← rhs_eq]
  rw [hInit]
  rw [show (7 : Nat) = 5 + 2 from rfl, srun_add]
  rw [rightPush_5step
        (Side.prepend (ones (3*k + 3))
          (Side.prepend [false, true] blank∞))]
  rw [show (Side.prepend (ones (3*k + 3))
            (Side.prepend [false, true] blank∞) : Side)
        = Side.prepend [true]
            (Side.prepend (ones (3*k + 2))
              (Side.prepend [false, true] blank∞)) from by
      rw [show (ones (3*k + 3) : List Sym) = [true] ++ ones (3*k + 2) from rfl,
          Side.prepend_append]]
  rw [zebraExtend_2step
        (Side.prepend (ones (3*k + 2))
          (Side.prepend [false, true] blank∞))
        (Side.prepend [false, true, false, true] blank∞)]
  rw [show (Side.prepend (ones (3*k + 2))
            (Side.prepend [false, true] blank∞) : Side).head = true from rfl,
      show (Side.prepend (ones (3*k + 2))
            (Side.prepend [false, true] blank∞) : Side).tail
        = Side.prepend (ones (3*k + 1))
            (Side.prepend [false, true] blank∞) from rfl]
  rw [show Side.prepend [false, true] (Side.prepend [false, true, false, true] blank∞)
        = Side.prepend (zebra 3) blank∞ from by
      rw [← Side.prepend_append]; rfl]

/-- **E4 outer iter step** (reentry variant, `24j+25` steps) — for iter `j`
    with `m ≥ 1` ones-triples remaining.  Consumes `ones 3` from the middle,
    growing the left zebra prefix by 4 pairs. -/
lemma E4_outer_iter_reentry (j m : Nat) :
    srun tm
      { state := some stA, head := false,
        left := Side.prepend (zebra (4*j))
                  (Side.prepend (ones (3*(m+1)+1))
                    (Side.prepend (zebra 1) blank∞)),
        right := blank∞ } (24*j + 25)
    = { state := some stA, head := false,
        left := Side.prepend (zebra (4*(j+1)))
                  (Side.prepend (ones (3*m+1))
                    (Side.prepend (zebra 1) blank∞)),
        right := blank∞ } := by
  rw [show 24*j + 25 = 3 + ((2*(4*j+1)) + (4 + ((4*(4*j+3)) + 4))) from by ring]
  -- Phase 1: A_to_D_3step, then fold [T,F,T] *> zebra(4j) = [T] *> zebra(4j+1)
  rw [srun_add, A_to_D_3step
    (Side.prepend (zebra (4*j))
      (Side.prepend (ones (3*(m+1)+1))
        (Side.prepend (zebra 1) blank∞)))]
  rw [zebra_tft_fold (4*j)
        (Side.prepend (ones (3*(m+1)+1))
          (Side.prepend (zebra 1) blank∞))]
  -- Phase 2: leftZebra_consume_iter (4j+1) 0 M blank
  rw [srun_add,
      show (4*j + 1 : Nat) = (4*j + 1) + 0 from by ring,
      leftZebra_consume_iter (4*j + 1) 0
        (Side.prepend (ones (3*(m+1)+1))
          (Side.prepend (zebra 1) blank∞)) blank∞,
      show Side.prepend (zebra 0)
              (Side.prepend (ones (3*(m+1)+1))
                (Side.prepend (zebra 1) blank∞))
        = Side.prepend (ones (3*(m+1)+1))
            (Side.prepend (zebra 1) blank∞) from rfl]
  -- Reshape [T] *> ones(3(m+1)+1) = ones 3 *> ones(3m+2) (both equal ones(3m+5))
  rw [show Side.prepend [true]
            (Side.prepend (ones (3*(m+1)+1))
              (Side.prepend (zebra 1) blank∞))
        = Side.prepend (ones 3)
            (Side.prepend (ones (3*m + 2))
              (Side.prepend (zebra 1) blank∞)) from by
      have h1 : Side.prepend [true]
                  (Side.prepend (ones (3*(m+1)+1))
                    (Side.prepend (zebra 1) blank∞))
              = Side.prepend (ones (3*m + 5))
                  (Side.prepend (zebra 1) blank∞) := by
        rw [show ([true] : List Sym) = ones 1 from rfl,
            ← Side.prepend_append, ones_append,
            show (1 + (3*(m+1)+1) : Nat) = 3*m + 5 from by ring]
      have h2 : Side.prepend (ones 3)
                  (Side.prepend (ones (3*m + 2))
                    (Side.prepend (zebra 1) blank∞))
              = Side.prepend (ones (3*m + 5))
                  (Side.prepend (zebra 1) blank∞) := by
        rw [← Side.prepend_append, ones_append,
            show (3 + (3*m + 2) : Nat) = 3*m + 5 from by ring]
      rw [h1, ← h2]]
  -- Phase 3: reentry_4step_abs with X = ones(3m+2) *> zebra 1 *> blank, R = zebra(4j+1)
  rw [srun_add, reentry_4step_abs
        (Side.prepend (ones (3*m + 2)) (Side.prepend (zebra 1) blank∞))
        (Side.prepend (zebra (4*j + 1)) blank∞)]
  rw [show (Side.prepend (ones (3*m + 2)) (Side.prepend (zebra 1) blank∞) : Side).head
        = true from rfl,
      show (Side.prepend (ones (3*m + 2)) (Side.prepend (zebra 1) blank∞) : Side).tail
        = Side.prepend (ones (3*m + 1)) (Side.prepend (zebra 1) blank∞) from rfl]
  -- Fold zebra 2 *> zebra(4j+1) = zebra(4j+3)
  rw [show Side.prepend (zebra 2) (Side.prepend (zebra (4*j + 1)) blank∞)
        = Side.prepend (zebra (4*j + 3)) blank∞ from by
      rw [← Side.prepend_append, zebra_append,
          show (2 + (4*j + 1) : Nat) = 4*j + 3 from by ring]]
  -- Phase 4: drainA_cycle_iter (4j+3) 0
  rw [srun_add,
      show (zebra (4*j + 3) : List Sym) = zebra ((4*j + 3) + 0) from by norm_num,
      drainA_cycle_iter (4*j + 3) 0
        (Side.prepend (ones (3*m + 1)) (Side.prepend (zebra 1) blank∞)) blank∞,
      show Side.prepend (zebra 0) blank∞ = blank∞ from rfl]
  -- Phase 5: drainEdge_4step, then fold [F,T] *> zebra(4j+3) = zebra(4(j+1))
  rw [drainEdge_4step
        (Side.prepend (zebra (4*j + 3))
          (Side.prepend (ones (3*m + 1))
            (Side.prepend (zebra 1) blank∞)))]
  rw [zebra_succ_fold (4*j + 3)
        (Side.prepend (ones (3*m + 1))
          (Side.prepend (zebra 1) blank∞))]
  rw [show (4*j + 3 + 1 : Nat) = 4*(j + 1) from by ring]

/-- **E4 outer last iter** (peel variant, `24j+27` steps) — for the (k+1)-th iter
    where only `ones 1 + zebra 1` remains to consume.  Uses `aBlock_peel_6step`. -/
lemma E4_outer_iter_peel (j : Nat) :
    srun tm
      { state := some stA, head := false,
        left := Side.prepend (zebra (4*j))
                  (Side.prepend (ones 1)
                    (Side.prepend (zebra 1) blank∞)),
        right := blank∞ } (24*j + 27)
    = { state := some stA, head := false,
        left := Side.prepend (zebra (4*(j+1))) blank∞,
        right := blank∞ } := by
  rw [show 24*j + 27 = 3 + ((2*(4*j+1)) + (6 + ((4*(4*j+3)) + 4))) from by ring]
  -- Phase 1: A_to_D_3step + zebra_tft_fold
  rw [srun_add, A_to_D_3step
    (Side.prepend (zebra (4*j))
      (Side.prepend (ones 1)
        (Side.prepend (zebra 1) blank∞)))]
  rw [zebra_tft_fold (4*j)
        (Side.prepend (ones 1)
          (Side.prepend (zebra 1) blank∞))]
  -- Phase 2: leftZebra_consume_iter (4j+1) 0
  rw [srun_add,
      show (4*j + 1 : Nat) = (4*j + 1) + 0 from by ring,
      leftZebra_consume_iter (4*j + 1) 0
        (Side.prepend (ones 1) (Side.prepend (zebra 1) blank∞)) blank∞,
      show Side.prepend (zebra 0)
              (Side.prepend (ones 1) (Side.prepend (zebra 1) blank∞))
        = Side.prepend (ones 1) (Side.prepend (zebra 1) blank∞) from rfl]
  -- Reshape [T] *> ones 1 *> zebra 1 = [T, T, F, T] = block1011
  rw [show Side.prepend [true]
            (Side.prepend (ones 1) (Side.prepend (zebra 1) blank∞))
        = Side.prepend [true, true, false, true] blank∞ from by
      rw [show (ones 1 : List Sym) = [true] from rfl,
          show (zebra 1 : List Sym) = [false, true] from rfl,
          ← Side.prepend_append, ← Side.prepend_append]
      rfl]
  -- Phase 3: aBlock_peel_6step (L = blank∞, R = zebra(4j+1) *> blank)
  rw [srun_add, aBlock_peel_6step blank∞ (Side.prepend (zebra (4*j + 1)) blank∞)]
  -- Fold zebra 2 *> zebra(4j+1) = zebra(4j+3)
  rw [show Side.prepend (zebra 2) (Side.prepend (zebra (4*j + 1)) blank∞)
        = Side.prepend (zebra (4*j + 3)) blank∞ from by
      rw [← Side.prepend_append, zebra_append,
          show (2 + (4*j + 1) : Nat) = 4*j + 3 from by ring]]
  -- Phase 4: drainA_cycle_iter (4j+3) 0 blank blank
  rw [srun_add,
      show (zebra (4*j + 3) : List Sym) = zebra ((4*j + 3) + 0) from by norm_num,
      drainA_cycle_iter (4*j + 3) 0 blank∞ blank∞,
      show Side.prepend (zebra 0) blank∞ = blank∞ from rfl]
  -- Phase 5: drainEdge_4step + zebra_succ_fold
  rw [drainEdge_4step (Side.prepend (zebra (4*j + 3)) blank∞)]
  rw [zebra_succ_fold (4*j + 3) blank∞]
  rw [show (4*j + 3 + 1 : Nat) = 4*(j + 1) from by ring]

/-- **E4 outer k iters (iterated reentry)** — applies `E4_outer_iter_reentry`
    `k` times, starting at iter `j0`.  Takes `ones (3k+1)` on left down to `ones 1`,
    and grows `zebra(4j0)` to `zebra(4(j0+k))`. -/
lemma E4_outer_k_iters (k : Nat) : ∀ (j0 : Nat),
    srun tm
      { state := some stA, head := false,
        left := Side.prepend (zebra (4*j0))
                  (Side.prepend (ones (3*k + 1))
                    (Side.prepend (zebra 1) blank∞)),
        right := blank∞ } (12*k*k + 24*k*j0 + 13*k)
    = { state := some stA, head := false,
        left := Side.prepend (zebra (4*(j0+k)))
                  (Side.prepend (ones 1)
                    (Side.prepend (zebra 1) blank∞)),
        right := blank∞ } := by
  induction k with
  | zero =>
    intro j0
    show srun tm _ 0 = _
    rw [show (12*0*0 + 24*0*j0 + 13*0 : Nat) = 0 from by ring]
    rw [show (j0 + 0 : Nat) = j0 from by omega]
    rw [show (3*0 + 1 : Nat) = 1 from rfl]
    rfl
  | succ k' ih =>
    intro j0
    rw [show 12*(k'+1)*(k'+1) + 24*(k'+1)*j0 + 13*(k'+1)
          = (24*j0 + 25) + (12*k'*k' + 24*k'*(j0+1) + 13*k') from by ring,
        srun_add]
    rw [show (3*(k' + 1) + 1 : Nat) = 3*(k' + 1) + 1 from rfl]
    rw [E4_outer_iter_reentry j0 k']
    rw [ih (j0+1)]
    rw [show (j0 + 1 + k' : Nat) = j0 + (k'+1) from by ring]

/-- **Edge rule E4** (`dt = 12k² + 77k + 160`).
    `C(1, 3k+2) → C(2k+4, 8)`.

    Pipeline:
    1. `rule_E4_opening` (7 steps) → `{A, T, ones(3k+1) *> [F,T] *> blank, zebra 3}`
    2. drainA×3 + drainEdge (16 steps) → `{A, F, zebra 4 *> ones(3k+1) *> zebra 1 *> blank, blank}`
    3. `E4_outer_k_iters` with k iters from j0=1 (12k²+37k steps) →
       `{A, F, zebra(4(k+1)) *> ones 1 *> zebra 1 *> blank, blank}`
    4. `E4_outer_iter_peel` with j=k+1 (24k+51 steps) →
       `{A, F, zebra(4(k+2)) *> blank, blank}`
    5. A_to_D + leftZebra_consume_iter(4k+9) + H1_transition_5step (8k+26 steps) →
       `{A, F, zebra 1, ones 1 + zebra(4k+9)}`
    6. E1_build_iter (2k+4) + E1_edge_build_4step (8k+20 steps) →
       `{A, F, zebra 1 + aBlocks(2k+5), blank}`
    7. `rule_E1_reduce (2k+4)` (11 steps) →
       `{A, F, ones 1 + aBlocks(2k+4), zebra 4}`
    8. `rule_E1_fill (k+1)` (29 steps) → `C_Config (2k+4) 8`. -/
theorem rule_E4 (k : Nat) :
    srun tm (C_Config 1 (3 * k + 2)) (12*k*k + 77*k + 160) =
      C_Config (2 * k + 4) 8 := by
  -- Right-associated step decomposition: opening(7) + drainA(12) + drainEdge(4) +
  -- k-iters(12k²+37k) + peel(24k+51) + A_to_D(3) + leftZebra(8k+18) + transition(5) +
  -- build_iter(8k+16) + edge(4) + reduce(11) + fill(29) = 12k²+77k+160.
  rw [show 12*k*k + 77*k + 160
        = 7 + ((4*3) + (4 + ((12*k*k + 24*k*1 + 13*k) + ((24*(k+1) + 27) +
              (3 + ((2*(4*k + 9)) + (5 + ((4*(2*k+4) + 4) + (11 + 29)))))))))
        from by ring]
  -- Phase 1: rule_E4_opening
  rw [srun_add, rule_E4_opening k]
  -- Phase 2: drainA_cycle_iter 3 0
  rw [srun_add,
      show (zebra 3 : List Sym) = zebra (3 + 0) from by norm_num,
      drainA_cycle_iter 3 0
        (Side.prepend (ones (3*k + 1)) (Side.prepend [false, true] blank∞)) blank∞,
      show Side.prepend (zebra 0) blank∞ = blank∞ from rfl]
  -- Phase 3: drainEdge_4step, then fold to zebra 4 *> ones(3k+1) *> zebra 1 *> blank
  rw [srun_add, drainEdge_4step
        (Side.prepend (zebra 3)
          (Side.prepend (ones (3*k + 1))
            (Side.prepend [false, true] blank∞)))]
  rw [show Side.prepend [false, true]
            (Side.prepend (zebra 3)
              (Side.prepend (ones (3*k + 1))
                (Side.prepend [false, true] blank∞)))
        = Side.prepend (zebra (4*1))
            (Side.prepend (ones (3*k + 1))
              (Side.prepend (zebra 1) blank∞)) from by
      rw [show ([false, true] : List Sym) = zebra 1 from rfl]
      rw [← Side.prepend_append, zebra_append,
          show (1 + 3 : Nat) = 4*1 from by ring]]
  -- Phase 4: E4_outer_k_iters k 1
  rw [srun_add, E4_outer_k_iters k 1]
  -- After: {A, F, zebra(4*(1+k)) *> ones 1 *> zebra 1 *> blank, blank}
  rw [show (1 + k : Nat) = k + 1 from by ring]
  -- Phase 5: E4_outer_iter_peel (k+1)
  rw [srun_add]
  rw [show Side.prepend (zebra (4*(k+1)))
            (Side.prepend (ones 1) (Side.prepend (zebra 1) blank∞))
        = Side.prepend (zebra (4*(k+1)))
            (Side.prepend (ones 1) (Side.prepend (zebra 1) blank∞)) from rfl]
  rw [E4_outer_iter_peel (k+1)]
  -- After: {A, F, zebra(4*((k+1)+1)) *> blank, blank}
  rw [show ((k+1) + 1 : Nat) = k + 2 from by ring]
  -- Phase 6: A_to_D_3step → [T] *> zebra(4(k+2)+1) = [T] *> zebra(4k+9)
  rw [srun_add, A_to_D_3step (Side.prepend (zebra (4*(k+2))) blank∞)]
  rw [zebra_tft_fold (4*(k+2)) blank∞]
  rw [show (4*(k+2) + 1 : Nat) = 4*k + 9 from by ring]
  -- Phase 7: leftZebra_consume_iter (4k+9) 0 blank blank
  rw [srun_add,
      show (4*k + 9 : Nat) = (4*k + 9) + 0 from by ring,
      leftZebra_consume_iter (4*k + 9) 0 blank∞ blank∞,
      show Side.prepend (zebra 0) blank∞ = blank∞ from rfl]
  -- Phase 8: H1_transition_5step
  rw [show (Side.prepend [true] blank∞ : Side) = Side.prepend (ones 1) blank∞ from rfl]
  rw [srun_add, H1_transition_5step (4*k + 9)]
  -- Phase 9: E1_build_iter (2k+4) 0 1 blank∞
  -- Three srun_adds: split off (build+edge)+(reduce+fill); split reduce+fill; split build from edge.
  rw [srun_add, srun_add, srun_add]
  rw [show Side.prepend [false, true] blank∞
        = Side.prepend [false, true] (Side.prepend (aBlocks 0) blank∞) from rfl,
      show (4*k + 9 : Nat) = 1 + 2*(2*k + 4) from by ring]
  rw [E1_build_iter (2*k + 4) 0 1 blank∞]
  rw [show (0 + (2*k + 4) : Nat) = 2*k + 4 from by ring]
  -- Phase 10: E1_edge_build_4step (2k+4) blank
  rw [E1_edge_build_4step (2*k + 4) blank∞]
  -- Phase 11: rule_E1_reduce (2k+4): needs aBlocks((2k+4)+1) = aBlocks(2k+5)
  rw [show (2*k + 4 + 1 : Nat) = (2*k + 4) + 1 from rfl]
  rw [rule_E1_reduce (2*k + 4)]
  -- Phase 12: rule_E1_fill (k+1): output C_Config (2(k+1)+2) = C_Config (2k+4) 8
  have hTarget : C_Config (2*k + 4) 8 = C_Config (2*(k+1) + 2) 8 := by
    rw [show (2*(k+1) + 2 : Nat) = 2*k + 4 from by ring]
  rw [hTarget]
  exact rule_E1_fill (k+1)

/-- Combined: from blank in 54 steps, reach `C(0, 8)`. -/
theorem init_to_C08 :
    srun tm (sinitConfig 6) 54 = C_Config 0 8 := by
  rw [show (54 : Nat) = 2 + 52 from rfl, srun_add, init_to_C00, rule_E1_base]

/-- Base case of E2 at `k = 0`: `C(0, 1) → C(0, 5)` in 30 steps. -/
theorem rule_E2_base :
    srun tm (C_Config 0 1) 30 = C_Config 0 5 := by
  simp [C_Config, aBlocks, srun, sstep, tm]

/-- Base case of E3 at `k = 0`: `C(0, 2) → C(0, 5)` in 28 steps. -/
theorem rule_E3_base :
    srun tm (C_Config 0 2) 28 = C_Config 0 5 := by
  simp [C_Config, aBlocks, srun, sstep, tm]

set_option maxRecDepth 4000 in
/-- **E3 at k = 1** — `C(0, 5) → C(0, 13)` in 93 steps.

    This concrete instance decomposes via the 12 shift lemmas
    according to the plan below; end-to-end the composition gives
    `5+2+12+4+3+10+4+48+5 = 93` steps matching the measured `dt`.
    Mechanized via direct `simp` (same strategy as `rule_R1_k1`/`k2`).

    Decomposition plan:
      rightPush_5step         (5)  → {D, 1, ones 4, zebra 2}
      zebraExtend_2step       (2)  → {A, 1, ones 2, zebra 3}
      drainA_cycle_iter N=3  (12)  → {A, 1, zebra 3 *> ones 2, blank}
      drainEdge_4step         (4)  → {A, 0, zebra 4 *> ones 2, blank}
      A_to_D_3step            (3)  → {D, 0, [T] *> zebra 5 *> ones 2, blank}
      leftZebra_consume_iter (10)  → {D, 0, ones 3, zebra 5}
      reentry_4step           (4)  → {A, 0, blank, zebra 7}
      zebraA_cycle_iter N=6  (48)  → {A, 0, ones 12, zebra 1}
      cleanup_5step           (5)  → {C, 0, [F] ++ ones 14, blank}
                                    = C_Config 0 13
-/
theorem rule_E3_k1 : srun tm (C_Config 0 5) 93 = C_Config 0 13 := by
  simp only [C_Config, aBlocks]
  simp [srun, sstep, tm]

set_option maxRecDepth 4000 in
/-- **E2 at k = 1** — `C(0, 4) → C(0, 13)` in 95 steps.
    Same target as `rule_E3_k1` but 2 extra steps (dt = 12k² + 53k + 30
    vs 12k² + 53k + 28).  The extra 2 steps come from the different
    `b mod 3` residue class: `b = 3k+1` starts the trajectory with an
    odd-parity right push that needs one extra `D,E` pair before
    entering the same drain/consume machinery. -/
theorem rule_E2_k1 : srun tm (C_Config 0 4) 95 = C_Config 0 13 := by
  simp only [C_Config, aBlocks]
  simp [srun, sstep, tm]

set_option maxRecDepth 2000 in
/-- **H1 at k = 1** — `C(1, 4)` halts in 124 steps
    (= 12·1² + 53·1 + 59, sim_dt + 1 for the halting transition). -/
theorem rule_H1_k1 : (srun tm (C_Config 1 4) 124).state = none := by
  simp [C_Config, aBlocks, block1011, srun, sstep, tm]

set_option maxRecDepth 8000 in
/-- **R1 at k = 3** — `C(a+1, 9) → C(a, 30)` in 295 steps (abstract `a`).
    Confirms the `12k² + 53k + 28` formula scales to larger `k`. -/
theorem rule_R1_k3 (a : Nat) :
    srun tm (C_Config (a + 1) 9) 295 = C_Config a 30 := by
  simp only [C_Config, aBlocks, block1011]
  simp [srun, sstep, tm]

set_option maxRecDepth 2000 in
/-- Base case of R2 at `k = 0`: `C(a+2, 1) → C(a, 16)` in 103 steps.
    Abstract in `a` (rule independent of left prefix). -/
theorem rule_R2_base (a : Nat) :
    srun tm (C_Config (a + 2) 1) 103 = C_Config a 16 := by
  simp only [C_Config, aBlocks, block1011]
  simp [srun, sstep, tm]

set_option maxRecDepth 4000 in
/-- Base case of R3 at `k = 0`: `C(a+2, 2) → C(a, 22)` in 184 steps.
    Abstract in `a`. -/
theorem rule_R3_base (a : Nat) :
    srun tm (C_Config (a + 2) 2) 184 = C_Config a 22 := by
  simp only [C_Config, aBlocks, block1011]
  simp [srun, sstep, tm]

set_option maxRecDepth 4000 in
/-- Concrete instance of R1 at `k = 1`: `C(a+1, 3) → C(a, 14)` in 93 steps.
    Abstract in `a`. -/
theorem rule_R1_k1 (a : Nat) :
    srun tm (C_Config (a + 1) 3) 93 = C_Config a 14 := by
  simp only [C_Config, aBlocks, block1011]
  simp [srun, sstep, tm]

set_option maxRecDepth 8000 in
/-- Concrete instance of R1 at `k = 2`: `C(a+1, 6) → C(a, 22)` in 182 steps. -/
theorem rule_R1_k2 (a : Nat) :
    srun tm (C_Config (a + 1) 6) 182 = C_Config a 22 := by
  simp only [C_Config, aBlocks, block1011]
  simp [srun, sstep, tm]

set_option maxRecDepth 2000 in
/-- Base case of H1 at `k = 0`: `C(1, 1)` halts in 59 steps
    (58 transitions + the halting transition). -/
theorem rule_H1_base :
    (srun tm (C_Config 1 1) 59).state = none := by
  simp [C_Config, aBlocks, block1011, srun, sstep, tm]

-- ============================================================
-- First orbit steps (documentation, from sim.py orbit):
--
--   i    a       b      dt    total
--   0    0       0      52    54           C(0, 0)    -> C(0, 8)     (E1, k=0)
--   1    0       8     182    236          C(0, 8)    -> C(0, 21)    (E3, k=2)
--   2    0      21     843    1079         C(0, 21)   -> C(14, 8)    (E1, k=7)
--   3   14       8    1414    ...          C(14, 8)   -> C(12, 22)   (R3, a=12, k=2)
--   ...
--
-- Racheline's c_0 = 14 corresponds to the first non-trivial "large a"
-- value reached, at total step ≈ 1079.
-- ============================================================

-- ============================================================
-- Progress log
--
-- 2026-04-22:
-- - `sim.py` + empirical verification of all Ligocki rules for
--   `a ∈ 0..4`, `k ∈ 0..4` (all cases OK).
-- - Closed-form `dt` extracted for each rule (quadratic in `k`, second
--   difference 24, independent of `a`).  Halt-rule `dt` = sim_dt + 1
--   (the halting transition counts in Lean but not in sim.py).
-- - Initial config `Start --(2)--> C(0, 0)` proved by direct `simp`.
-- - Base cases (k = 0) closed by direct `simp`:
--   * `rule_E1_base`: C(0, 0) → C(0, 8), 52 steps
--   * `rule_E2_base`: C(0, 1) → C(0, 5), 30 steps
--   * `rule_E3_base`: C(0, 2) → C(0, 5), 28 steps
--   * `rule_R1_base`: C(a+1, 0) → C(a, 6), 28 steps (abstract `a`)
--   * `rule_R2_base`: C(a+2, 1) → C(a, 16), 103 steps (abstract `a`,
--                     needs `maxRecDepth 2000`)
--   * `rule_R3_base`: C(a+2, 2) → C(a, 22), 184 steps (abstract `a`,
--                     needs `maxRecDepth 4000`)
--   * `rule_H1_base`: C(1, 1) halts in 59 steps (`maxRecDepth 2000`)
--   * `init_to_C08`:  blank → C(0, 8), 54 steps (composition)
-- - Small-`k` sanity checks proved by direct `simp` (abstract `a`):
--   * `rule_R1_k1`: C(a+1, 3) → C(a, 14), 93 steps (`maxRecDepth 4000`)
--   * `rule_R1_k2`: C(a+1, 6) → C(a, 22), 182 steps (`maxRecDepth 8000`)
--   These confirm the encoding scales: for any concrete `k`, the rule
--   is `simp`-reducible because the abstract `a` only affects the
--   deep tail of the left side (`aBlocks a *> blank∞`) which is
--   never touched.
-- - Shift-lemma infrastructure — 12 composable lemmas, all proved:
--   * `rightPush_5step` (5 steps, abstract `L`): universal opener;
--     C-state pops `[false, true, true]` prefix, writes `zebra 2`.
--   * `zebraExtend_2step` (2 steps): D→C→A pops `[true]` off left,
--     prepends `[false, true]` to right.
--   * `zebraA_cycle_8step` (8 steps, abstract `n, M, R`): A-head-0
--     engine consuming one zebra pair from right, producing 2 ones
--     on left.  Main source of the quadratic `12k²` cost.
--   * `zebraA_cycle_iter` (8N steps, by induction on N): iterated
--     cycle contracting `zebra (N+1)` → `zebra 1` on right while
--     growing left `ones n` → `ones (n+2N)`.
--   * `cleanup_5step` (5 steps): final A→B→C→A→B closer; `zebra 1`
--     tail collapses to `[false] ++ ones (n+2)` on left.
--   * `drainA_cycle_4step` (4 steps, abstract `L, R`): A-head-1
--     engine `A,1→D→E→F→A` consuming one zebra pair from right
--     AND prepending `[false, true]` to left.  Fires whenever the
--     b-ones prefix (from `C(a, 3k)` etc.) leaves the head at A,1.
--   * `drainA_cycle_iter` (4N steps, by induction on N): iterated
--     drain — in `4N` steps contracts `zebra (N+k)` → `zebra k` on
--     right while prepending `zebra N` to left.
--   * `drainEdge_4step` (4 steps): the "drain-to-blank edge".  Same
--     4-step state sequence as `drainA_cycle_4step` but with
--     `right = blank∞` throughout (no zebra to consume).  Flips the
--     head A,1 → A,F and prepends `[false, true]` to left.  Fires
--     exactly once after `drainA_cycle_iter` has exhausted the
--     right zebra, bridging to the zebra-consume phase on the
--     left-side zebra built up during drain.
--   * `leftZebra_consume_2step` (2 steps, abstract `L, R`): symmetric
--     partner of `drainA_cycle_4step` for the left-sweep phase.
--     From `{D, 0, [true, false] *> L, R}`, the 2-step sequence
--     `D,0→1LE; E,1→0LD` pops `[T, F]` off the left and prepends
--     `[false, true]` to the right — a zebra pair transitively
--     moves from left to right.
--   * `leftZebra_consume_iter` (2N steps, by induction on N): iterated
--     left-drain.  Given `[T] *> zebra (K+N) *> M` on the left (the
--     canonical shape after the A→B→C→D transition from the
--     post-drainEdge config), in `2N` steps reduces to
--     `[T] *> zebra K *> M` while prepending `zebra N` to the right.
--     The key algebraic step is `[T] *> zebra (K+N+1) = [T, F] *>
--     [T] *> zebra (K+N)`, unfolding one `[T, F]` pair that the
--     2-step cycle consumes.
--   * `A_to_D_3step` (3 steps, abstract `L`): the "A→B→C→D bridge"
--     connecting `drainEdge_4step`'s exit (A,0,·,blank) to
--     `leftZebra_consume_iter`'s entry (D,0,[T,F,T]*>L,blank).
--     Three R-steps all on blank: `A,0→1RB; B,0→0RC; C,0→1RD`.
--     The output `[T, F, T] *> zebra N *> M` folds into the needed
--     `[T] *> zebra (N+1) *> M` via `zebra_succ`.
--   * `reentry_4step` (4 steps, abstract `R`): the "D→E→D→C→A
--     re-entry" connecting `leftZebra_consume_iter`'s exit
--     (D,0,ones 3*>blank,·) to `zebraA_cycle_iter`'s entry
--     (A,0,blank,zebra (M+2)).  Four L-steps:
--     `D,0→1LE; E,1→0LD; D,1→1LC; C,1→0LA`.  Consumes `ones 3`
--     entirely and prepends `zebra 2` to the right.  Note: requires
--     left-tail `blank∞` (not arbitrary) so the final C,1→0LA pops
--     a blank and exits to A,F rather than staying in the ones.
--
-- Composition for the k=0 case of R1/E3 (28 steps):
--   rightPush (5) + zebraExtend (2) + zebraA_cycle_iter N=2 (16)
--                                                + cleanup (5) = 28
--
-- Full composition plan for rule_E3 at k=1 (C(0, 5) → C(0, 13), 93 steps):
--   rightPush_5step (5)                   → {D, 1, ones 4, zebra 2}
--   zebraExtend_2step (2)                 → {A, 1, ones 2, zebra 3}
--   drainA_cycle_iter N=3 (12)            → {A, 1, zebra 3 ++ ones 2, blank}
--   drainEdge_4step (4)                   → {A, 0, zebra 4 ++ ones 2, blank}
--   A→B→C 2-step transition (2)           → {C, 0, zebra 5 ++ ones 2, blank}
--   C→D 1-step (1)                        → {D, 0, [T] ++ zebra 5 ++ ones 2, blank}
--   leftZebra_consume_iter N=5 K=0 (10)   → {D, 0, ones 3, zebra 5}
--   D→E→D→C→A 4-step re-entry (4)         → {A, 0, blank, zebra 7}
--   zebraA_cycle_iter N=6 (48)            → {A, 0, ones 12, zebra 1}
--   cleanup_5step (5)                     → {C, 0, [F] ++ ones 14, blank}
--                                           = C_Config 0 13 ✓
-- Total: 5+2+12+4+2+1+10+4+48+5 = 93 ✓
--
-- With all 12 shift lemmas, the composition sketch ABOVE closes
-- `rule_E3` at `k=1` (93 = 5+2+12+4+3+10+4+48+5 steps) by pure
-- assembly — no more shift lemmas required for that specific case.
--
-- Remaining obstacle for general `k ≥ 2`:
--   After `leftZebra_consume_iter N=5 K=0`, the left is `ones (3k)`
--   (a `3k`-long block of ones).  The `reentry_4step` lemma only
--   handles `ones 3` exactly.  For `k ≥ 2`, an additional "inner
--   cycle" is needed that processes the extra `3(k-1)` ones — this
--   is structurally a k-indexed iteration producing the `12k²` term
--   from something like `4·(2k-1)·(k) + linear` steps.
--
-- All 12 shift lemmas use `simp [srun, sstep, tm]` plus
-- `zebra_succ`/`zebra_succ_append` for zebra arithmetic; the three
-- iterated versions (`zebraA_cycle_iter`, `drainA_cycle_iter`,
-- `leftZebra_consume_iter`) additionally use explicit induction.
-- - Base cases still TODO: `rule_E4_base` (C(1, 2) → C(4, 8), 160
--   steps), requires constructing `aBlocks 4` on the RHS via simp;
--   unusual because LHS has `a = 1` but RHS has `a = 4`.
-- - All general-`k` rules R1/R2/R3/E1/E2/E3/E4/H1 stated with exact
--   step counts, currently `sorry`ed.
--
-- ## Proof strategy sketch (for future work)
--
-- From the `trace.py` traces, every rule has a 2-pass structure:
--
--   Pass 1 ("right-push"): head moves R into the initial blank and
--     begins a `D/E`-alternating left-sweep that writes a zebra
--     pattern `[false, true, false, true, ...]` into what was the
--     `1^b 1 0` region.  After `f₁(k)` steps reaches state D on the
--     leftmost 1 of that region.
--
--   Pass 2 ("zebra expansion"): head oscillates L/R through the
--     zebra pattern it just wrote, absorbing the outer `(1011)` block
--     and expanding each zebra cell into `8/3` fresh 1s (the `8k+c`
--     term on the RHS).  Visible in the trace as long sequences of
--     `A-B-C-D` rotations.
--
-- The key state-sweep lemmas needed (state D most involved; A/E are
-- simpler 1-cell walks):
--
--   D_zebra_sweep : state D head=1 over `zebra n *> blank∞` on right,
--                   in 2n steps becomes state D head at left edge of
--                   the zebra, having written 1s over the zebra.
--
--   ABCD_cycle    : 6-step cycle composed of A,0→B,R; B,0→C,R;
--                   C,0→D,R; D,1→C,L; C,1→A,L; A,1→D,R that
--                   advances the head by 1 while consuming one
--                   zebra block from the right and producing two 1s
--                   on the left.
--
-- Given these, each general rule should decompose as:
--   phase1 (right-push, fixed steps)
--   + phase2 (zebra-write sweep, linear in k)
--   + phase3 (zebra-consume cycle, linear-in-k iterated k+c times,
--             giving quadratic `12k²`)
--   + phase4 (final cleanup, fixed steps).
--
-- Effort estimate: ~300-500 lines per rule family, similar to
-- `Chaotic6.simple_bump` and `Shifty6.rule_R2` / `rule_R3` (200-300
-- lines each).  The abstract-`a` invariance means `L : Side` can be
-- left as a black-box parameter throughout — only `aBlocks 0 = []`
-- needs special handling.
-- ============================================================

-- ============================================================
-- Halt-equivalence theorem: TM halts iff macro iteration halts
-- ============================================================

/-- **Macro halting predicate**.  Inductively defined: `macroHalts (a, b)` iff
    applying the 8 proven rules from the config `C(a, b)` eventually reaches the
    halt rule `H1 : C(1, 3k+1) → Halt`.  Each constructor corresponds to one
    macro rule. -/
inductive macroHalts : Nat × Nat → Prop
  | halt_H1 (k : Nat) : macroHalts (1, 3*k + 1)
  | step_R1 (a k : Nat) (h : macroHalts (a, 8*k + 6)) : macroHalts (a+1, 3*k)
  | step_R2 (a k : Nat) (h : macroHalts (a, 8*k + 16)) : macroHalts (a+2, 3*k+1)
  | step_R3 (a k : Nat) (h : macroHalts (a, 8*k + 22)) : macroHalts (a+2, 3*k+2)
  | step_E1 (k : Nat) (h : macroHalts (2*k, 8)) : macroHalts (0, 3*k)
  | step_E2 (k : Nat) (h : macroHalts (0, 8*k + 5)) : macroHalts (0, 3*k+1)
  | step_E3 (k : Nat) (h : macroHalts (0, 8*k + 5)) : macroHalts (0, 3*k+2)
  | step_E4 (k : Nat) (h : macroHalts (2*k + 4, 8)) : macroHalts (1, 3*k+2)

/-- If `macroHalts (a, b)` holds, then the TM halts starting from `C_Config a b`.
    Proof by induction on `macroHalts`; each constructor uses the corresponding
    rule (`rule_R1`, …, `rule_H1`) to advance the TM by a specific number of steps
    and then applies the IH. -/
lemma C_halts (ab : Nat × Nat) (h : macroHalts ab) :
    ∃ k, (srun tm (C_Config ab.1 ab.2) k).state = none := by
  induction h with
  | halt_H1 k =>
    exact ⟨12*k*k + 53*k + 59, rule_H1 k⟩
  | step_R1 a k _ ih =>
    obtain ⟨k', hk'⟩ := ih
    refine ⟨(12*k*k + 53*k + 28) + k', ?_⟩
    rw [srun_add, rule_R1 a k]; exact hk'
  | step_R2 a k _ ih =>
    obtain ⟨k', hk'⟩ := ih
    refine ⟨(12*k*k + 77*k + 103) + k', ?_⟩
    rw [srun_add, rule_R2 a k]; exact hk'
  | step_R3 a k _ ih =>
    obtain ⟨k', hk'⟩ := ih
    refine ⟨(12*k*k + 101*k + 184) + k', ?_⟩
    rw [srun_add, rule_R3 a k]; exact hk'
  | step_E1 k _ ih =>
    obtain ⟨k', hk'⟩ := ih
    refine ⟨(12*k*k + 29*k + 52) + k', ?_⟩
    rw [srun_add, rule_E1 k]; exact hk'
  | step_E2 k _ ih =>
    obtain ⟨k', hk'⟩ := ih
    refine ⟨(12*k*k + 53*k + 30) + k', ?_⟩
    rw [srun_add, rule_E2 k]; exact hk'
  | step_E3 k _ ih =>
    obtain ⟨k', hk'⟩ := ih
    refine ⟨(12*k*k + 53*k + 28) + k', ?_⟩
    rw [srun_add, rule_E3 k]; exact hk'
  | step_E4 k _ ih =>
    obtain ⟨k', hk'⟩ := ih
    refine ⟨(12*k*k + 77*k + 160) + k', ?_⟩
    rw [srun_add, rule_E4 k]; exact hk'

/-- **Macro-step simulation**: from any `C(a, b)`, the TM in some positive number of
    steps either (i) reaches the next `C(a', b')` predicted by one of the 8 rules
    (with `macroHalts (a', b') → macroHalts (a, b)` as the backward closure), or
    (ii) halts.  Case split on `(a, b mod 3)` selects one of the 8 rules. -/
lemma stm_simulates_macro (a b : Nat) :
    (∃ k a' b', 0 < k ∧ srun tm (C_Config a b) k = C_Config a' b'
                     ∧ (macroHalts (a', b') → macroHalts (a, b)))
    ∨
    (∃ k, 0 < k ∧ (srun tm (C_Config a b) k).state = none
                ∧ macroHalts (a, b)) := by
  -- Normalize b = 3q + r, r ∈ {0, 1, 2}.
  have hb_eq : b = 3*(b/3) + b%3 := by omega
  have hb_mod : b%3 < 3 := Nat.mod_lt _ (by omega)
  set q := b / 3 with hq
  set r := b % 3 with hr
  -- Rewrite b in the goal so constructors' conclusions match.
  rw [show b = 3*q + r from hb_eq]
  -- Case split on a ∈ {0, 1, a+2} and r ∈ {0, 1, 2}.
  match a, r, hb_mod with
  | 0, 0, _ =>
    left; refine ⟨12*q*q + 29*q + 52, 2*q, 8, by positivity, ?_, macroHalts.step_E1 q⟩
    rw [Nat.add_zero]; exact rule_E1 q
  | 0, 1, _ =>
    left; refine ⟨12*q*q + 53*q + 30, 0, 8*q+5, by positivity, ?_, macroHalts.step_E2 q⟩
    exact rule_E2 q
  | 0, 2, _ =>
    left; refine ⟨12*q*q + 53*q + 28, 0, 8*q+5, by positivity, ?_, macroHalts.step_E3 q⟩
    exact rule_E3 q
  | 1, 0, _ =>
    left; refine ⟨12*q*q + 53*q + 28, 0, 8*q+6, by positivity, ?_, macroHalts.step_R1 0 q⟩
    rw [Nat.add_zero, show (1:Nat) = 0 + 1 from rfl]; exact rule_R1 0 q
  | 1, 1, _ =>
    right; refine ⟨12*q*q + 53*q + 59, by positivity, rule_H1 q, macroHalts.halt_H1 q⟩
  | 1, 2, _ =>
    left; refine ⟨12*q*q + 77*q + 160, 2*q+4, 8, by positivity, ?_, macroHalts.step_E4 q⟩
    exact rule_E4 q
  | a'+2, 0, _ =>
    left; refine ⟨12*q*q + 53*q + 28, a'+1, 8*q+6, by positivity, ?_,
                  macroHalts.step_R1 (a'+1) q⟩
    rw [Nat.add_zero, show (a'+2 : Nat) = (a'+1)+1 from rfl]; exact rule_R1 (a'+1) q
  | a'+2, 1, _ =>
    left; refine ⟨12*q*q + 77*q + 103, a', 8*q+16, by positivity, ?_, macroHalts.step_R2 a' q⟩
    exact rule_R2 a' q
  | a'+2, 2, _ =>
    left; refine ⟨12*q*q + 101*q + 184, a', 8*q+22, by positivity, ?_, macroHalts.step_R3 a' q⟩
    exact rule_R3 a' q
  | _, _+3, h => omega

/-- If the TM halts starting from `C(a, b)` in `n` steps, then `macroHalts (a, b)`.
    Strong induction on `n`, using `stm_simulates_macro` to chunk the trajectory. -/
lemma C_halts_converse : ∀ (n : Nat) (a b : Nat),
    (srun tm (C_Config a b) n).state = none → macroHalts (a, b) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hhalt
    rcases stm_simulates_macro a b with
      ⟨k_sim, a', b', _hk_pos, h_sim, h_close⟩ | ⟨_k_sim, _hk_pos, _, h_mh⟩
    · -- TM advances to C(a', b') in k_sim steps.
      by_cases h_lt : n < k_sim
      · -- Contradiction: if TM halts in n < k_sim steps, then at step k_sim it's
        -- still halted.  But h_sim says step k_sim reaches C(a', b') with state
        -- some stC — contradiction.
        exfalso
        have h_still : (srun tm (C_Config a b) k_sim).state = none := by
          rw [show k_sim = n + (k_sim - n) from by omega, srun_add,
              srun_halted tm _ hhalt (k_sim - n)]
          exact hhalt
        rw [h_sim] at h_still
        exact absurd h_still (by simp [C_Config])
      · push_neg at h_lt
        apply h_close
        apply ih (n - k_sim) (by omega) a' b'
        rw [show n = k_sim + (n - k_sim) from by omega, srun_add, h_sim] at hhalt
        exact hhalt
    · exact h_mh

/-- **Main halting equivalence (both directions).**
    The TM halts from the initial blank tape iff the macro iteration halts
    starting at the config `C(0, 0)` (which is reached after 2 steps).

    Forward (→): uses `C_halts_converse` on the trajectory after the first 2
    steps (reaching `C(0, 0)` via `init_to_C00`).  The TM can't halt in the
    first 2 steps (checked mechanically).

    Backward (←): uses `C_halts` composed with `init_to_C00`. -/
theorem tm_halt_iff :
    (∃ k, (srun tm (sinitConfig 6) k).state = none) ↔ macroHalts (0, 0) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨k, hk⟩
    -- If k < 2, TM is in initial phase and state is not none yet.
    -- For k ≥ 2, apply init_to_C00 then C_halts_converse.
    by_cases hk2 : k ≥ 2
    · have h_after : (srun tm (C_Config 0 0) (k - 2)).state = none := by
        rw [show k = 2 + (k - 2) from by omega, srun_add, init_to_C00] at hk
        exact hk
      exact C_halts_converse (k - 2) 0 0 h_after
    · -- k < 2: contradiction.
      push_neg at hk2
      exfalso
      match k, hk2 with
      | 0, _ => simp [srun, sinitConfig] at hk
      | 1, _ => simp [srun, sinitConfig, sstep, tm] at hk
  · intro h
    obtain ⟨k, hk⟩ := C_halts (0, 0) h
    exact ⟨2 + k, by rw [srun_add, init_to_C00]; exact hk⟩

/-! ### Self-contained mathematical halting function

Encodes the 8 proven macro rules as a total partial function `f : ℕ × ℕ → Option (ℕ × ℕ)`
that returns `none` on the halt case (`a = 1, b ≡ 1 (mod 3)`).  Combined with iterated
application `fiter`, gives a purely number-theoretic characterization of TM halting. -/

/-- Mathematical iteration function.  7-case piecewise:
    * `a = 0, b ≡ 0 (mod 3)` ↦ `(2⌊b/3⌋, 8)` (E1)
    * `a = 0, b ≢ 0 (mod 3)` ↦ `(0, 8⌊b/3⌋+5)` (E2/E3 merged)
    * `a ≥ 1, b ≡ 0 (mod 3)` ↦ `(a-1, 8⌊b/3⌋+6)` (R1)
    * `a = 1, b ≡ 1 (mod 3)` ↦ `none` (H1, HALT)
    * `a ≥ 2, b ≡ 1 (mod 3)` ↦ `(a-2, 8⌊b/3⌋+16)` (R2)
    * `a = 1, b ≡ 2 (mod 3)` ↦ `(2⌊b/3⌋+4, 8)` (E4)
    * `a ≥ 2, b ≡ 2 (mod 3)` ↦ `(a-2, 8⌊b/3⌋+22)` (R3) -/
def f (ab : Nat × Nat) : Option (Nat × Nat) :=
  let a := ab.1
  let b := ab.2
  let q := b / 3
  if b % 3 = 0 then
    if a = 0 then some (2 * q, 8)
    else some (a - 1, 8 * q + 6)
  else if b % 3 = 1 then
    if a = 0 then some (0, 8 * q + 5)
    else if a = 1 then none
    else some (a - 2, 8 * q + 16)
  else
    if a = 0 then some (0, 8 * q + 5)
    else if a = 1 then some (2 * q + 4, 8)
    else some (a - 2, 8 * q + 22)

/-- Iterated application of `f`, short-circuiting on `none`.  `fiter k ab = none`
    means iterating `f` starting at `ab` hits the HALT case within `k` steps. -/
def fiter : Nat → Nat × Nat → Option (Nat × Nat)
  | 0,     ab => some ab
  | k + 1, ab => match f ab with
                 | none     => none
                 | some ab' => fiter k ab'

/-- `macroHalts ab` implies that iterating `f` starting from `ab` eventually
    hits the HALT case.  Proved by induction on `macroHalts`, computing `f` at
    each step to match the constructor. -/
lemma fiter_halts_of_macroHalts (ab : Nat × Nat) (h : macroHalts ab) :
    ∃ k, fiter k ab = none := by
  induction h with
  | halt_H1 k =>
    refine ⟨1, ?_⟩
    have hf : f (1, 3*k + 1) = none := by
      unfold f
      simp [show (3*k + 1) % 3 = 1 from by omega]
    simp [fiter, hf]
  | step_R1 a k _ ih =>
    obtain ⟨k', hk'⟩ := ih
    refine ⟨k' + 1, ?_⟩
    have hf : f (a + 1, 3*k) = some (a, 8*k + 6) := by
      unfold f
      simp [show (3*k) % 3 = 0 from by omega, show (3*k) / 3 = k from by omega]
    show (match f (a + 1, 3*k) with | none => none | some ab' => fiter k' ab') = none
    rw [hf]; exact hk'
  | step_R2 a k _ ih =>
    obtain ⟨k', hk'⟩ := ih
    refine ⟨k' + 1, ?_⟩
    have hf : f (a + 2, 3*k + 1) = some (a, 8*k + 16) := by
      unfold f
      simp [show (3*k + 1) % 3 = 1 from by omega, show (3*k + 1) / 3 = k from by omega]
    show (match f (a + 2, 3*k + 1) with | none => none | some ab' => fiter k' ab') = none
    rw [hf]; exact hk'
  | step_R3 a k _ ih =>
    obtain ⟨k', hk'⟩ := ih
    refine ⟨k' + 1, ?_⟩
    have hf : f (a + 2, 3*k + 2) = some (a, 8*k + 22) := by
      unfold f
      simp [show (3*k + 2) % 3 = 2 from by omega, show (3*k + 2) / 3 = k from by omega]
    show (match f (a + 2, 3*k + 2) with | none => none | some ab' => fiter k' ab') = none
    rw [hf]; exact hk'
  | step_E1 k _ ih =>
    obtain ⟨k', hk'⟩ := ih
    refine ⟨k' + 1, ?_⟩
    have hf : f (0, 3*k) = some (2*k, 8) := by
      unfold f
      simp [show (3*k) % 3 = 0 from by omega, show (3*k) / 3 = k from by omega]
    show (match f (0, 3*k) with | none => none | some ab' => fiter k' ab') = none
    rw [hf]; exact hk'
  | step_E2 k _ ih =>
    obtain ⟨k', hk'⟩ := ih
    refine ⟨k' + 1, ?_⟩
    have hf : f (0, 3*k + 1) = some (0, 8*k + 5) := by
      unfold f
      simp [show (3*k + 1) % 3 = 1 from by omega, show (3*k + 1) / 3 = k from by omega]
    show (match f (0, 3*k + 1) with | none => none | some ab' => fiter k' ab') = none
    rw [hf]; exact hk'
  | step_E3 k _ ih =>
    obtain ⟨k', hk'⟩ := ih
    refine ⟨k' + 1, ?_⟩
    have hf : f (0, 3*k + 2) = some (0, 8*k + 5) := by
      unfold f
      simp [show (3*k + 2) % 3 = 2 from by omega, show (3*k + 2) / 3 = k from by omega]
    show (match f (0, 3*k + 2) with | none => none | some ab' => fiter k' ab') = none
    rw [hf]; exact hk'
  | step_E4 k _ ih =>
    obtain ⟨k', hk'⟩ := ih
    refine ⟨k' + 1, ?_⟩
    have hf : f (1, 3*k + 2) = some (2*k + 4, 8) := by
      unfold f
      simp [show (3*k + 2) % 3 = 2 from by omega, show (3*k + 2) / 3 = k from by omega]
    show (match f (1, 3*k + 2) with | none => none | some ab' => fiter k' ab') = none
    rw [hf]; exact hk'

/-- Converse: if iterating `f` from `ab` eventually hits `none`, then `macroHalts ab`.
    Strong induction on `k`; at each step, case-split on `f ab` using the explicit
    9-cell table (3 values of `a` × 3 values of `b mod 3`) to find the matching
    constructor. -/
lemma macroHalts_of_fiter_halts : ∀ (k : Nat) (ab : Nat × Nat),
    fiter k ab = none → macroHalts ab := by
  intro k
  induction k with
  | zero => intro ab h; simp [fiter] at h
  | succ k' ih =>
    intro ab h
    -- h : fiter (k' + 1) ab = none = match f ab with | none => none | some ab' => fiter k' ab'
    simp only [fiter] at h
    -- Case on (a, b % 3) to identify which rule fires.
    obtain ⟨q, hq⟩ : ∃ q, ab.2 = 3*q + ab.2 % 3 := ⟨ab.2 / 3, by omega⟩
    have hmod : ab.2 % 3 < 3 := Nat.mod_lt _ (by omega)
    -- Split on a.
    match ha : ab.1, hr : ab.2 % 3, hmod with
    | 0, 0, _ =>
      have hab : ab = (0, 3*q) := by
        rcases ab with ⟨a, b⟩; simp at ha hr ⊢; omega
      rw [hab]
      -- f (0, 3*q) = some (2*q, 8); need macroHalts (0, 3*q) via step_E1.
      have hf : f (0, 3*q) = some (2*q, 8) := by
        unfold f; simp [show (3*q) % 3 = 0 from by omega, show (3*q) / 3 = q from by omega]
      rw [hab, hf] at h
      exact macroHalts.step_E1 q (ih (2*q, 8) h)
    | 0, 1, _ =>
      have hab : ab = (0, 3*q + 1) := by
        rcases ab with ⟨a, b⟩; simp at ha hr ⊢; omega
      rw [hab]
      have hf : f (0, 3*q + 1) = some (0, 8*q + 5) := by
        unfold f; simp [show (3*q + 1) % 3 = 1 from by omega,
                         show (3*q + 1) / 3 = q from by omega]
      rw [hab, hf] at h
      exact macroHalts.step_E2 q (ih (0, 8*q + 5) h)
    | 0, 2, _ =>
      have hab : ab = (0, 3*q + 2) := by
        rcases ab with ⟨a, b⟩; simp at ha hr ⊢; omega
      rw [hab]
      have hf : f (0, 3*q + 2) = some (0, 8*q + 5) := by
        unfold f; simp [show (3*q + 2) % 3 = 2 from by omega,
                         show (3*q + 2) / 3 = q from by omega]
      rw [hab, hf] at h
      exact macroHalts.step_E3 q (ih (0, 8*q + 5) h)
    | 1, 0, _ =>
      have hab : ab = (1, 3*q) := by
        rcases ab with ⟨a, b⟩; simp at ha hr ⊢; omega
      rw [hab]
      have hf : f (1, 3*q) = some (0, 8*q + 6) := by
        unfold f; simp [show (3*q) % 3 = 0 from by omega, show (3*q) / 3 = q from by omega]
      rw [hab, hf] at h
      exact macroHalts.step_R1 0 q (ih (0, 8*q + 6) h)
    | 1, 1, _ =>
      have hab : ab = (1, 3*q + 1) := by
        rcases ab with ⟨a, b⟩; simp at ha hr ⊢; omega
      rw [hab]; exact macroHalts.halt_H1 q
    | 1, 2, _ =>
      have hab : ab = (1, 3*q + 2) := by
        rcases ab with ⟨a, b⟩; simp at ha hr ⊢; omega
      rw [hab]
      have hf : f (1, 3*q + 2) = some (2*q + 4, 8) := by
        unfold f; simp [show (3*q + 2) % 3 = 2 from by omega,
                         show (3*q + 2) / 3 = q from by omega]
      rw [hab, hf] at h
      exact macroHalts.step_E4 q (ih (2*q + 4, 8) h)
    | a'+2, 0, _ =>
      have hab : ab = (a'+2, 3*q) := by
        rcases ab with ⟨a, b⟩; simp at ha hr ⊢; omega
      rw [hab]
      have hf : f (a'+2, 3*q) = some (a'+1, 8*q + 6) := by
        unfold f; simp [show (3*q) % 3 = 0 from by omega, show (3*q) / 3 = q from by omega]
      rw [hab, hf] at h
      rw [show (a'+2 : Nat) = (a'+1)+1 from rfl]
      exact macroHalts.step_R1 (a'+1) q (ih (a'+1, 8*q + 6) h)
    | a'+2, 1, _ =>
      have hab : ab = (a'+2, 3*q + 1) := by
        rcases ab with ⟨a, b⟩; simp at ha hr ⊢; omega
      rw [hab]
      have hf : f (a'+2, 3*q + 1) = some (a', 8*q + 16) := by
        unfold f; simp [show (3*q + 1) % 3 = 1 from by omega,
                         show (3*q + 1) / 3 = q from by omega]
      rw [hab, hf] at h
      exact macroHalts.step_R2 a' q (ih (a', 8*q + 16) h)
    | a'+2, 2, _ =>
      have hab : ab = (a'+2, 3*q + 2) := by
        rcases ab with ⟨a, b⟩; simp at ha hr ⊢; omega
      rw [hab]
      have hf : f (a'+2, 3*q + 2) = some (a', 8*q + 22) := by
        unfold f; simp [show (3*q + 2) % 3 = 2 from by omega,
                         show (3*q + 2) / 3 = q from by omega]
      rw [hab, hf] at h
      exact macroHalts.step_R3 a' q (ih (a', 8*q + 22) h)
    | _, _+3, hmod => omega

/-- **Mathematical halting equivalence**: the TM halts from the blank tape iff
    iterating the 7-case function `f` from `(0, 0)` eventually returns `none`.

    Combined with `tm_halt_iff`, this gives the precise number-theoretic
    statement: Lucy's Moonlight halts iff ∃ k, f^k(0,0) = HALT. -/
theorem tm_halt_iff_math :
    (∃ k, (srun tm (sinitConfig 6) k).state = none) ↔
    ∃ k, fiter k (0, 0) = none := by
  rw [tm_halt_iff]
  exact ⟨fiter_halts_of_macroHalts (0, 0),
         fun ⟨k, hk⟩ => macroHalts_of_fiter_halts k (0, 0) hk⟩

end LucysMoonlight
