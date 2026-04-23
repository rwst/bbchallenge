



import BusyLean
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open BusyLean

namespace Counter6

/-!
# 6-state TM `1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC`

BB(6) holdout.  Halt/nonhalt is **not** the target; this file records observed
macro rules.

## Transition table
|   | 0   | 1   |
|---|-----|-----|
| A | 1RB | 1RA |
| B | 0RC | 1RC |
| C | 1LD | 0LF |
| D | 0LE | 1LE |
| E | 1RA | 0LB |
| F | --- | 0LC |

Only halting transition: `F,0 → ---`.  F is entered only via `C,1 → 0LF`.

## Macro configuration (Shawn Ligocki, wiki)

`C(a, b, c) = $ 1^{2a+1} C> 0^{2b} 1^c 01 $`

Head rests at state C on the cell immediately right of the left 1-block.  Three
head-symbol cases (see variants below):

* `b ≥ 1`: head reads a `0` (start of `0^{2b}`).
* `b = 0, c ≥ 1`: head reads a `1` (start of `1^c`).
* `b = 0, c = 0`: head reads a `0` (the `0` of the trailing `01` marker).

## Atomic C→C rules (verified empirically by `sim.py`)

| Rule | Statement                                  | dt       |
|------|--------------------------------------------|----------|
| R1   | `C(a, 2,   c)   → C(a+1, 1,   c+1)`        | `6a+11`  |
| R2   | `C(a, b+3, c)   → C(a+3, b+1, c)`          | `12a+24` |
| R3a  | `C(a, 1,   c+2) → C(a+2, 0,   c+1)`        | `6a+7`   |
| R3b  | `C(a, 1,   1)   → C(a+2, 0,   0)`          | `6a+7`   |
| R4   | `C(a, 0,   c+1) → C(1,   a+1, c)`          | `2a+7`   |
| R5   | `C(a, 0,   0)   → C(1,   0,   2a+4)`       | `10a+25` |
| R6   | `C(a, 1,   0)   → HALT`                    | `2a+9`   |

The wiki's "Level-1" rules are compositions of these atomic rules.  For
example, the wiki's bump `C(a, b+2, c) → C(a+3, b, c)` is a single atomic step
only when `b ≥ 1` (our R2); for `b = 0` it is the pair R1 + R3a.

From the blank tape, the TM reaches `C(1, 0, 0)` at step 11.

## Orbit snippet (from `sim.py`)

```
init at step 11: C(1, 0, 0)
  C(1, 0, 0)  → C(1, 0, 6)     dt=35    [R5, a=1]
  C(1, 0, 6)  → C(1, 2, 5)     dt=9     [R4, a=1, c=5]
  C(1, 2, 5)  → C(2, 1, 6)     dt=17    [R1, a=1, c=5]
  C(2, 1, 6)  → C(4, 0, 5)     dt=19    [R3a, a=2, c=4]
  C(4, 0, 5)  → C(1, 5, 4)     dt=15    [R4, a=4, c=4]
  C(1, 5, 4)  → C(4, 3, 4)     dt=36    [R2, a=1, b=3]
  C(4, 3, 4)  → C(7, 1, 4)     dt=72    [R2, a=4, b=1]
  C(7, 1, 4)  → C(9, 0, 3)     dt=49    [R3a, a=7, c=2]
  ...
```
-/

def tm : TM 6 := tm! "1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC"

-- Transition simp lemmas: evaluate `tm.tr st sym` without unfolding the literal.
@[simp] private theorem tr_A0 : tm.tr stA false = some (stB, true,  Dir.R) := rfl
@[simp] private theorem tr_A1 : tm.tr stA true  = some (stA, true,  Dir.R) := rfl
@[simp] private theorem tr_B0 : tm.tr stB false = some (stC, false, Dir.R) := rfl
@[simp] private theorem tr_B1 : tm.tr stB true  = some (stC, true,  Dir.R) := rfl
@[simp] private theorem tr_C0 : tm.tr stC false = some (stD, true,  Dir.L) := rfl
@[simp] private theorem tr_C1 : tm.tr stC true  = some (stF, false, Dir.L) := rfl
@[simp] private theorem tr_D0 : tm.tr stD false = some (stE, false, Dir.L) := rfl
@[simp] private theorem tr_D1 : tm.tr stD true  = some (stE, true,  Dir.L) := rfl
@[simp] private theorem tr_E0 : tm.tr stE false = some (stA, true,  Dir.R) := rfl
@[simp] private theorem tr_E1 : tm.tr stE true  = some (stB, false, Dir.L) := rfl
@[simp] private theorem tr_F0 : tm.tr stF false = none := rfl
@[simp] private theorem tr_F1 : tm.tr stF true  = some (stC, false, Dir.L) := rfl

-- ============================================================
-- Macro configuration variants
-- ============================================================

/-- Variant 1 — `C_zb a b c`: zero-block not empty.
Represents macro `C(a, b+1, c)`, i.e. tape
`1^{2a+1} C> 0^{2(b+1)} 1^c 0 1 blank∞` with head on the first `0`.

Right-of-head Side: `zeros (2b+1) *> ones c *> [false, true] *> blank∞`. -/
def C_zb (a b c : ℕ) : SConfig 6 :=
  { state := some stC,
    head  := false,
    left  := ones (2*a + 1) *> blank∞,
    right := zeros (2*b + 1) *> ones c *> [false, true] *> blank∞ }

/-- Variant 2 — `C_on a c`: zero-block empty, head on first `1`.
Represents macro `C(a, 0, c+1)`, i.e. tape
`1^{2a+1} C> 1^{c+1} 0 1 blank∞` with head on the leftmost `1`.

Right-of-head Side: `ones c *> [false, true] *> blank∞`. -/
def C_on (a c : ℕ) : SConfig 6 :=
  { state := some stC,
    head  := true,
    left  := ones (2*a + 1) *> blank∞,
    right := ones c *> [false, true] *> blank∞ }

/-- Variant 3 — `C_off a`: zero-block empty, c=0.
Represents macro `C(a, 0, 0)`, i.e. tape `1^{2a+1} C> 0 1 blank∞` with head
on the leading `0` of the `01` marker. -/
def C_off (a : ℕ) : SConfig 6 :=
  { state := some stC,
    head  := false,
    left  := ones (2*a + 1) *> blank∞,
    right := [true] *> blank∞ }

-- ============================================================
-- Shift lemmas (phase structure of the macro rules)
-- ============================================================

/-- **Inner cycle** (4 steps).  From state C, head=0 on a left-block with 3+
ones at its front, one cycle consumes 2 ones from the left and deposits 2 ones
at the front of the right.  Pattern `C,0 → D,1 → E,1 → B,1 → C,0` with the
E,1→0LB write turning one left-block one into a right-block one. -/
private lemma inner_cycle (L R : Side) :
    srun tm
      ({state := some stC, head := false,
        left := ones 3 *> L,
        right := R} : SConfig 6) 4
    = {state := some stC, head := false,
       left := ones 1 *> L,
       right := ones 2 *> R} := by
  simp [srun, sstep, tm]

/-- Helper: `ones a *> ones b *> S = ones (a+b) *> S`. -/
private lemma ones_merge (a b : ℕ) (S : Side) :
    Side.prepend (ones a) (Side.prepend (ones b) S) = Side.prepend (ones (a + b)) S := by
  rw [← Side.prepend_append, ones_append]

/-- Iterated inner cycle.  After `a` cycles, a left-block of `2a+1` ones is
reduced to 1 one, and `2a` ones are deposited at the front of the right. -/
private lemma inner_cycle_iter (a : ℕ) (R : Side) :
    srun tm
      ({state := some stC, head := false,
        left := ones (2*a + 1) *> blank∞,
        right := R} : SConfig 6) (4*a)
    = {state := some stC, head := false,
       left := ones 1 *> blank∞,
       right := ones (2*a) *> R} := by
  induction a generalizing R with
  | zero => simp [srun]
  | succ a' ih =>
    -- Split the (2a'+3)-long left block as 3 + (2a'): left = ones 3 *> (ones (2a') *> blank).
    rw [show (4 * (a' + 1) : ℕ) = 4 + 4*a' from by ring, srun_add,
        show (2*(a'+1) + 1 : ℕ) = 3 + 2*a' from by ring,
        ← ones_merge 3 (2*a') blank∞,
        inner_cycle (ones (2*a') *> blank∞) R,
        ones_merge 1 (2*a') blank∞,
        show (1 + 2*a' : ℕ) = 2*a' + 1 from by ring,
        ih (ones 2 *> R),
        ones_merge (2*a') 2 R,
        show (2*a' + 2 : ℕ) = 2*(a'+1) from by ring]

/-- **Phase 2 (post-cycles)** (3 steps).  From state C head=0 with left block
reduced to `ones 1 *> blank∞`, transitions to state A head=1 depositing one
additional 1 at the front of the right. -/
private lemma phase2_R3b (R : Side) :
    srun tm
      ({state := some stC, head := false,
        left := ones 1 *> blank∞,
        right := R} : SConfig 6) 3
    = {state := some stA, head := true,
       left := ones 1 *> blank∞,
       right := ones 1 *> R} := by
  simp [srun, sstep, tm]

/-- **A right-sweep** (k+1 steps).  State A head=1 traverses `k` ones followed
by a 0 marker, ending at state A head=0 with `k+1` ones prepended to the left. -/
private lemma AR_sweep (k : ℕ) (L M : Side) :
    srun tm
      ({state := some stA, head := true, left := L,
        right := ones k *> Side.cons false M} : SConfig 6) (k + 1)
    = {state := some stA, head := false,
       left := ones (k + 1) *> L,
       right := M} := by
  induction k generalizing L with
  | zero => simp [srun, sstep, tm]
  | succ k' ih =>
    rw [show (k' + 1 + 1 : ℕ) = 1 + (k' + 1) from by ring, srun_add]
    have h1 : srun tm
        ({state := some stA, head := true, left := L,
          right := ones (k' + 1) *> Side.cons false M} : SConfig 6) 1
        = {state := some stA, head := true, left := ones 1 *> L,
           right := ones k' *> Side.cons false M} := by
      simp [srun, sstep, tm]
    rw [h1, ih (ones 1 *> L), ones_merge (k'+1) 1 L,
        show (k' + 1 + 1 : ℕ) = 1 + (k' + 1) from by ring]

/-- **Phase 4 (endgame)** (2 steps).  State A head=0 on `[1,0,1]` pattern
transitions via A,0→B and B,1→C, depositing 2 ones on the left. -/
private lemma phase4_R3b (K : ℕ) :
    srun tm
      ({state := some stA, head := false,
        left := ones K *> blank∞,
        right := ([true, false, true] : List Sym) *> blank∞} : SConfig 6) 2
    = {state := some stC, head := false,
       left := ones (K + 2) *> blank∞,
       right := ([true] : List Sym) *> blank∞} := by
  simp [srun, sstep, tm]

/-- **Phase 4 (halt)** (4 steps).  State A head=0 on `[0,1]` pattern: A,0→B,
B,0→C, C,1→F (writes 0), F,0 → HALT. -/
private lemma phase4_R6 (K : ℕ) :
    (srun tm
      ({state := some stA, head := false,
        left := ones K *> blank∞,
        right := ([false, true] : List Sym) *> blank∞} : SConfig 6) 4).state = none := by
  simp [srun, sstep, tm]

/-- **R4 sub-cycle** (2 steps): `C,1 → F,1 → C`.  Head=1 on left block, 2
steps move L twice consuming 2 ones (from `cons 1 L`), deposit 2 zeros on
the right.  Ending head = `L.head` (could be 0 if L is blank). -/
private lemma sub_cycle_R4 (L R : Side) :
    srun tm
      ({state := some stC, head := true,
        left := Side.cons true L,
        right := R} : SConfig 6) 2
    = {state := some stC, head := L.head,
       left := L.tail,
       right := Side.cons false (Side.cons false R)} := by
  simp [srun, sstep, tm]

/-- Iterated sub-cycle for R4.  Starting left `ones (2a+1) *> blank∞`,
`a+1` cycles (= `2a+2` steps) reduce the left to blank and deposit
`2a+2` zeros at the front of the right.  Final head = 0 (reading blank). -/
private lemma phase1_R4 (a : ℕ) (R : Side) :
    srun tm
      ({state := some stC, head := true,
        left := ones (2*a + 1) *> blank∞,
        right := R} : SConfig 6) (2*a + 2)
    = {state := some stC, head := false,
       left := blank∞,
       right := zeros (2*a + 2) *> R} := by
  induction a generalizing R with
  | zero =>
    -- 2 steps concrete
    show srun tm {state := some stC, head := true,
                  left := ones 1 *> blank∞,
                  right := R} 2
       = {state := some stC, head := false,
          left := blank∞,
          right := zeros 2 *> R}
    simp [srun, sstep, tm]
  | succ a' ih =>
    -- Unfold left to cons true (ones (2a'+2) *> blank).
    have hleft : Side.prepend (ones (2*(a'+1) + 1)) blank∞
               = Side.cons true (ones (2*a' + 2) *> blank∞) := by
      rw [show (2*(a'+1) + 1 : ℕ) = 2*a' + 3 from by ring]; rfl
    -- After one sub-cycle, ones (2a'+2) *> blank unfolds to cons true (ones (2a'+1) *> blank).
    have hleft2 : (ones (2*a' + 2) *> blank∞ : Side)
                = Side.cons true (ones (2*a' + 1) *> blank∞) := by
      show Side.prepend (ones (2*a' + 2)) blank∞ = _
      rw [show (2*a' + 2 : ℕ) = (2*a' + 1) + 1 from by ring]; rfl
    -- After IH, zeros (2a'+2) *> [0, 0] *> R = zeros (2(a'+1)+2) *> R.
    have hR : Side.prepend (zeros (2*a' + 2)) (Side.cons false (Side.cons false R))
            = Side.prepend (zeros (2*(a'+1) + 2)) R := by
      show Side.prepend (zeros (2*a'+2)) (Side.prepend [false, false] R)
         = Side.prepend (zeros (2*(a'+1)+2)) R
      rw [← Side.prepend_append]
      show Side.prepend (zeros (2*a'+2) ++ zeros 2) R = _
      rw [zeros_append, show (2*a' + 2 + 2 : ℕ) = 2*(a'+1) + 2 from by ring]
    rw [show (2*(a'+1) + 2 : ℕ) = 2 + (2*a' + 2) from by ring, srun_add, hleft,
        sub_cycle_R4 (ones (2*a' + 2) *> blank∞) R, hleft2]
    show srun tm {state := some stC, head := true,
                  left := ones (2*a' + 1) *> blank∞,
                  right := Side.cons false (Side.cons false R)} (2*a' + 2) = _
    rw [ih (Side.cons false (Side.cons false R)), hR,
        show (2*(a'+1) + 2 : ℕ) = 2 + (2*a' + 2) from by ring]

/-- **R4 phases 2+3** (5 steps): from state C head=0 on `[false] *> S₀`,
transitions via C→D→E→A→B→C, depositing 3 ones on the left and consuming
one zero (absorbed into a read-then-tail-drop of `cons false S₀`). -/
private lemma phase23_R4 (S : Side) :
    srun tm
      ({state := some stC, head := false,
        left := blank∞,
        right := Side.cons false S} : SConfig 6) 5
    = {state := some stC, head := false,
       left := ones 3 *> blank∞,
       right := S} := by
  simp [srun, sstep, tm]

/-- **Phase 4 for R3a** (2 steps): state A head=0, right starts with `ones (c+2)`
followed by `[false, true] *> blank`.  A,0→B consumes a 0 (but there was a 1 —
wait: A reads head=0, transitions.  Then B reads the first of ones(c+2)=1.
After 2 steps we're at C head=1 on the (c+1)-th one. -/
private lemma phase4_R3a (K c : ℕ) :
    srun tm
      ({state := some stA, head := false,
        left := ones K *> blank∞,
        right := ones (c + 2) *> ([false, true] : List Sym) *> blank∞} : SConfig 6) 2
    = {state := some stC, head := true,
       left := ones (K + 2) *> blank∞,
       right := ones c *> ([false, true] : List Sym) *> blank∞} := by
  simp [srun, sstep, tm]

/-- **Phase 4 for R1** (6 steps): state A head=0, right=`zeros 2 *> ones c *>
[false, true] *> blank`.  Left block size unchanged (ones K requires K ≥ 3
here since step 5 is E,1→0LB; we parameterize as `K+3` to enforce this).
Right is rearranged: `zeros 2 *> ones c` → `zeros 1 *> ones (c+1)`. -/
private lemma phase4_R1 (K c : ℕ) :
    srun tm
      ({state := some stA, head := false,
        left := ones (K + 3) *> blank∞,
        right := (zeros 2 : List Sym) *> Side.prepend (ones c)
                   (Side.prepend [false, true] blank∞)} : SConfig 6) 6
    = {state := some stC, head := false,
       left := ones (K + 3) *> blank∞,
       right := (zeros 1 : List Sym) *> Side.prepend (ones (c + 1))
                  (Side.prepend [false, true] blank∞)} := by
  simp [srun, sstep, tm]

/-- **Zero-cycle** (4 steps): C→D→E→B→C similar to `inner_cycle` but the
first left-cell is `0` (a blank "gap") rather than `1`.  Consumes one
`0-1-1` triple from the front of the left, prepends `[0, 1]` to the right.
(Compare to `inner_cycle` which consumes three `1`s and prepends two `1`s.) -/
private lemma zero_cycle (L R : Side) :
    srun tm
      ({state := some stC, head := false,
        left := Side.cons false (Side.cons true (Side.cons true L)),
        right := R} : SConfig 6) 4
    = {state := some stC, head := false,
       left := Side.cons true L,
       right := ([false, true] : List Sym) *> R} := by
  simp [srun, sstep, tm]

/-- **Prelude for R2 phase 4** (2 steps): A,0→B, B,0→C.  `K+1` ones on the
left; right starts with a `0`.  Deposits a `0` at the head of left and adds
2 ones under it. -/
private lemma prelude_R2 (K : ℕ) (R : Side) :
    srun tm
      ({state := some stA, head := false,
        left := ones (K + 1) *> blank∞,
        right := Side.cons false R} : SConfig 6) 2
    = {state := some stC, head := R.head,
       left := Side.cons false (ones (K + 2) *> blank∞),
       right := R.tail} := by
  simp [srun, sstep, tm]

/-- **Finish for R2 phase 4** (2 steps): A,0→B, B,1→C.  Unlike
`phase4_R3b` (which expects `[true, false, true]` on the right), this one
expects `cons true R` and leaves head = `R.head`. -/
private lemma finish_R2 (K : ℕ) (R : Side) :
    srun tm
      ({state := some stA, head := false,
        left := ones (K + 1) *> blank∞,
        right := Side.cons true R} : SConfig 6) 2
    = {state := some stC, head := R.head,
       left := ones (K + 3) *> blank∞,
       right := R.tail} := by
  simp [srun, sstep, tm]

/-- **Edge cycle** (4 steps): like `inner_cycle` but the left block has only
2 ones and terminates onto blank.  Ends with `cons false blank∞` on the left
(a single written `0` marker past the blank boundary). -/
private lemma edge_cycle (R : Side) :
    srun tm
      ({state := some stC, head := false,
        left := ones 2 *> blank∞,
        right := R} : SConfig 6) 4
    = {state := some stC, head := false,
       left := Side.cons false blank∞,
       right := ones 2 *> R} := by
  simp [srun, sstep, tm]

/-- **Phase 2 for R5** (3 steps): C→D→E→A from the `cons false blank∞` edge
state.  Prepends one `1` to the right. -/
private lemma phase2_R5 (R : Side) :
    srun tm
      ({state := some stC, head := false,
        left := Side.cons false blank∞,
        right := R} : SConfig 6) 3
    = {state := some stA, head := false,
       left := ones 1 *> blank∞,
       right := Side.cons true R} := by
  simp [srun, sstep, tm]

/-- **R5 "middle chunk"** (4a+8 steps): `a+1` inner cycles + 1 edge cycle.
Transforms state C head=0 left=ones(2a+4)*>blank right=R  into
state C head=0 left=cons false blank right=ones(2a+4) *> R. -/
private lemma R5_mid_gen (a : ℕ) (R : Side) :
    srun tm
      ({state := some stC, head := false,
        left := ones (2*a + 4) *> blank∞,
        right := R} : SConfig 6) (4*a + 8)
    = {state := some stC, head := false,
       left := Side.cons false blank∞,
       right := ones (2*a + 4) *> R} := by
  induction a generalizing R with
  | zero =>
    -- 8 steps: 1 inner_cycle + 1 edge_cycle.
    have hleft0 : Side.prepend (ones (2*0 + 4)) blank∞
                = Side.prepend (ones 3) (Side.prepend (ones 1) blank∞) := rfl
    rw [show (4*0 + 8 : ℕ) = 4 + 4 from rfl, srun_add, hleft0,
        inner_cycle (Side.prepend (ones 1) blank∞) R,
        show Side.prepend (ones 1) (Side.prepend (ones 1) blank∞)
           = Side.prepend (ones 2) blank∞ from by
          rw [ones_merge 1 1 _],
        edge_cycle (Side.prepend (ones 2) R),
        ones_merge 2 2 R]
  | succ a' ih =>
    -- Unfold left as ones 3 *> ones(2a'+3) *> blank.
    have hleft : Side.prepend (ones (2*(a'+1) + 4)) blank∞
               = Side.prepend (ones 3) (Side.prepend (ones (2*a' + 3)) blank∞) := by
      rw [ones_merge 3 (2*a' + 3) blank∞,
          show (3 + (2*a' + 3) : ℕ) = 2*(a'+1) + 4 from by ring]
    -- After inner_cycle, left becomes ones 1 *> ones(2a'+3) *> blank = ones(2a'+4) *> blank.
    have hleft2 : Side.prepend (ones 1) (Side.prepend (ones (2*a' + 3)) blank∞)
                = Side.prepend (ones (2*a' + 4)) blank∞ := by
      rw [ones_merge 1 (2*a' + 3) _, show (1 + (2*a' + 3) : ℕ) = 2*a' + 4 from by ring]
    rw [show (4*(a'+1) + 8 : ℕ) = 4 + (4*a' + 8) from by ring, srun_add, hleft,
        inner_cycle (Side.prepend (ones (2*a' + 3)) blank∞) R, hleft2,
        ih (ones 2 *> R),
        ones_merge (2*a' + 4) 2 R,
        show (2*a' + 4 + 2 : ℕ) = 2*(a'+1) + 4 from by ring]

-- ============================================================
-- Macro rules (all sorried; empirically verified by sim.py)
-- ============================================================

/-- **R1**: `C(a, 2, c) → C(a+1, 1, c+1)`, dt = 6a + 11.
Input zero-block size 2; output zero-block size 1.  Only `b=2` case of the
"bump"; for `b ≥ 3` see R2.

**Phase structure**: `4a` inner cycles + `3` phase2 + `(2a+2)` A-sweep +
`6` phase4_R1 = `6a+11`. -/
theorem rule_R1 (a c : ℕ) :
    srun tm (C_zb a 1 c) (6*a + 11) = C_zb (a + 1) 0 (c + 1) := by
  -- Rewrite C_zb a 1 c's right: zeros 3 *> ones c *> [false, true] *> blank.
  have hright : Side.prepend (zeros (2*1 + 1)) (Side.prepend (ones c)
                  (Side.prepend [false, true] blank∞))
              = Side.prepend (zeros 3) (Side.prepend (ones c)
                  (Side.prepend [false, true] blank∞)) := rfl
  rw [show (6*a + 11 : ℕ) = 4*a + (3 + ((2*a + 2) + 6)) from by ring]
  show srun tm {state := some stC, head := false,
                left := ones (2*a+1) *> blank∞,
                right := Side.prepend (zeros (2*1+1)) (Side.prepend (ones c)
                          (Side.prepend [false, true] blank∞))} _ = _
  rw [hright, srun_add]
  -- Phase 1: inner cycles.
  rw [inner_cycle_iter a (Side.prepend (zeros 3) (Side.prepend (ones c)
                            (Side.prepend [false, true] blank∞))), srun_add]
  -- Phase 2: C→D→E→A, adds 1 one at front of right.
  rw [phase2_R3b (ones (2*a) *> Side.prepend (zeros 3) (Side.prepend (ones c)
                                  (Side.prepend [false, true] blank∞))), srun_add]
  -- Reshape right: ones 1 *> ones (2a) *> zeros 3 *> ones c *> [false, true] *> blank
  --              = ones (2a+1) *> cons 0 (cons 0 (cons 0 (ones c *> [false, true] *> blank)))
  --              = ones (2a+1) *> cons false (zeros 2 *> ones c *> [false, true] *> blank)
  have hR : Side.prepend (ones 1) (Side.prepend (ones (2*a))
              (Side.prepend (zeros 3) (Side.prepend (ones c)
                (Side.prepend [false, true] blank∞))))
          = Side.prepend (ones (2*a + 1)) (Side.cons false
              ((zeros 2 : List Sym) *> Side.prepend (ones c)
                (Side.prepend [false, true] blank∞))) := by
    rw [ones_merge 1 (2*a) _, show (1 + 2*a : ℕ) = 2*a + 1 from by ring]
    rfl
  rw [hR]
  -- Phase 3: A-sweep through ones (2a+1).
  rw [AR_sweep (2*a+1) (Side.prepend (ones 1) blank∞)
         ((zeros 2 : List Sym) *> Side.prepend (ones c)
            (Side.prepend [false, true] blank∞)),
      ones_merge (2*a+1+1) 1 blank∞,
      show (2*a + 1 + 1 + 1 : ℕ) = 2*a + 3 from by ring]
  -- Phase 4: 6-step transform.
  have hK : (2*a + 3 : ℕ) = 2*a + 3 := rfl
  rw [show (2*a + 3 : ℕ) = (2*a) + 3 from by ring, phase4_R1 (2*a) c]
  -- Match C_zb (a+1) 0 (c+1).
  show ({state := some stC, head := false,
         left := ones (2*a + 3) *> blank∞,
         right := (zeros 1 : List Sym) *> Side.prepend (ones (c+1))
                    (Side.prepend [false, true] blank∞)} : SConfig 6)
       = C_zb (a+1) 0 (c+1)
  simp only [C_zb]
  congr 2

/-- **R2**: `C(a, b+3, c) → C(a+3, b+1, c)`, dt = 12a + 24.
Uniform "bump" for zero-block size ≥ 3; shrinks zero-block by 2 and adds 3 ones
on the left.  Independent of `b` and `c`.

**Phase structure**: `4a` inner_cycle_iter + `3` phase2_R3b + `(2a+2)` AR_sweep +
`(6a+19)` phase 4, where phase 4 itself decomposes as
`2 prelude + 4 zero_cycle + 4(a+1) inner_cycle_iter + 3 phase2_R3b + (2a+4) AR_sweep + 2 finish`. -/
theorem rule_R2 (a b c : ℕ) :
    srun tm (C_zb a (b + 2) c) (12*a + 24) = C_zb (a + 3) b c := by
  -- Abbreviate the common "tail" Side.
  set T : Side := Side.prepend (ones c) (Side.prepend [false, true] blank∞) with hT
  -- Unfold C_zb into explicit pieces.
  have hC_in : C_zb a (b + 2) c = {state := some stC, head := false,
                                    left := ones (2*a + 1) *> blank∞,
                                    right := Side.prepend (zeros (2*(b+2) + 1)) T} := rfl
  have hC_out : C_zb (a + 3) b c = {state := some stC, head := false,
                                    left := ones (2*(a+3) + 1) *> blank∞,
                                    right := Side.prepend (zeros (2*b + 1)) T} := rfl
  -- Split dt: 12a+24 = 4a + (3 + ((2a+2) + ((2 + (4 + (4*(a+1) + (3 + ((2a+4) + 2))))))))
  rw [show (12*a + 24 : ℕ)
       = 4*a + (3 + ((2*a + 2) + (2 + (4 + (4*(a+1) + (3 + ((2*a + 4) + 2)))))))
       from by ring, hC_in, hC_out]
  -- Phase 1: inner_cycle_iter a.
  rw [srun_add, inner_cycle_iter a (Side.prepend (zeros (2*(b+2) + 1)) T)]
  -- Phase 2: phase2_R3b.
  rw [srun_add, phase2_R3b
        (ones (2*a) *> Side.prepend (zeros (2*(b+2) + 1)) T)]
  -- Reshape right for AR_sweep: ones 1 *> ones (2a) *> zeros (2(b+2)+1) *> T
  --   = ones (2a+1) *> cons false (zeros (2b+4) *> T)
  have hR1 : Side.prepend (ones 1) (Side.prepend (ones (2*a))
                (Side.prepend (zeros (2*(b+2) + 1)) T))
           = Side.prepend (ones (2*a + 1))
               (Side.cons false (Side.prepend (zeros (2*b + 4)) T)) := by
    rw [ones_merge 1 (2*a) _, show (1 + 2*a : ℕ) = 2*a + 1 from by ring]
    show Side.prepend (ones (2*a+1)) (Side.prepend (zeros (2*(b+2)+1)) T)
       = Side.prepend (ones (2*a+1)) (Side.cons false (Side.prepend (zeros (2*b+4)) T))
    rw [show (2*(b+2) + 1 : ℕ) = (2*b + 4) + 1 from by ring]; rfl
  rw [hR1]
  -- Phase 3: AR_sweep k=2a+1.
  rw [srun_add, AR_sweep (2*a + 1) (Side.prepend (ones 1) blank∞)
        (Side.prepend (zeros (2*b + 4)) T),
      ones_merge (2*a + 1 + 1) 1 blank∞,
      show (2*a + 1 + 1 + 1 : ℕ) = 2*a + 3 from by ring]
  -- Phase 4 begin: A head=0, left=ones(2a+3), right=zeros(2b+4)*>T.
  -- Rewrite zeros(2b+4) = cons 0 (zeros(2b+3)).
  have hR2 : Side.prepend (zeros (2*b + 4)) T
           = Side.cons false (Side.prepend (zeros (2*b + 3)) T) := by
    rw [show (2*b + 4 : ℕ) = (2*b + 3) + 1 from by ring]; rfl
  rw [hR2]
  -- Prelude: use prelude_R2 with K = 2a+2 (K+1 = 2a+3).
  rw [srun_add,
      show (2*a + 3 : ℕ) = (2*a + 2) + 1 from by ring,
      prelude_R2 (2*a + 2) (Side.prepend (zeros (2*b + 3)) T)]
  -- After prelude: state C, head = (zeros(2b+3)*>T).head = false,
  --   left = cons 0 (ones(2a+4)*>blank), right = (zeros(2b+3)*>T).tail = zeros(2b+2)*>T.
  have hhead : (Side.prepend (zeros (2*b + 3)) T).head = false := by
    rw [show (2*b + 3 : ℕ) = (2*b + 2) + 1 from by ring]; rfl
  have htail : (Side.prepend (zeros (2*b + 3)) T).tail = Side.prepend (zeros (2*b + 2)) T := by
    rw [show (2*b + 3 : ℕ) = (2*b + 2) + 1 from by ring]; rfl
  rw [hhead, htail]
  -- Zero-cycle: input left = cons 0 (ones(2a+4)*>blank) = cons 0 (cons 1 (cons 1 (ones(2a+2)*>blank))).
  have hleft_zc : Side.cons false (ones (2*a + 4) *> blank∞)
                = Side.cons false (Side.cons true (Side.cons true
                    (ones (2*a + 2) *> blank∞))) := by
    rw [show (2*a + 4 : ℕ) = (2*a + 2) + 1 + 1 from by ring]; rfl
  rw [hleft_zc, srun_add, zero_cycle (ones (2*a + 2) *> blank∞)
        (Side.prepend (zeros (2*b + 2)) T)]
  -- After zero-cycle: state C head=0 left = cons 1 (ones(2a+2)*>blank) = ones(2a+3)*>blank,
  --   right = [false, true] *> zeros(2b+2) *> T.
  have hleft_ic : Side.cons true (Side.prepend (ones (2*a + 2)) blank∞)
                = Side.prepend (ones (2*(a+1) + 1)) blank∞ := by
    rw [show (2*(a+1) + 1 : ℕ) = (2*a + 2) + 1 from by ring]; rfl
  rw [hleft_ic]
  -- Apply inner_cycle_iter (a+1).
  rw [srun_add, inner_cycle_iter (a + 1)
        (Side.prepend [false, true] (Side.prepend (zeros (2*b + 2)) T))]
  -- Output: left = ones 1 *> blank, right = ones(2(a+1)) *> [false,true] *> zeros(2b+2)*>T.
  -- Apply phase2_R3b.
  rw [srun_add, phase2_R3b
        (ones (2*(a+1)) *> Side.prepend [false, true]
          (Side.prepend (zeros (2*b + 2)) T))]
  -- Reshape right: ones 1 *> ones(2(a+1)) *> [false, true] *> ...
  --              = ones(2a+3) *> cons false (ones 1 *> zeros(2b+2) *> T)
  have hR3 : Side.prepend (ones 1) (Side.prepend (ones (2*(a+1)))
                (Side.prepend [false, true] (Side.prepend (zeros (2*b + 2)) T)))
           = Side.prepend (ones (2*a + 3)) (Side.cons false
               (Side.prepend (ones 1) (Side.prepend (zeros (2*b + 2)) T))) := by
    rw [ones_merge 1 (2*(a+1)) _,
        show (1 + 2*(a+1) : ℕ) = 2*a + 3 from by ring]
    rfl
  rw [hR3]
  -- AR_sweep k=2a+3.
  rw [srun_add, AR_sweep (2*a + 3) (Side.prepend (ones 1) blank∞)
        (Side.prepend (ones 1) (Side.prepend (zeros (2*b + 2)) T)),
      ones_merge (2*a + 3 + 1) 1 blank∞,
      show (2*a + 3 + 1 + 1 : ℕ) = (2*a + 4) + 1 from by ring]
  -- Now state A head=0 left=ones(2a+5)*>blank right=ones 1 *> zeros(2b+2)*>T.
  -- Rewrite ones 1 *> ... as cons true (...).
  have hR4 : Side.prepend (ones 1) (Side.prepend (zeros (2*b + 2)) T)
           = Side.cons true (Side.prepend (zeros (2*b + 2)) T) := rfl
  rw [hR4]
  -- Apply finish_R2 with K = 2a+4 (K+1 = 2a+5).
  rw [finish_R2 (2*a + 4) (Side.prepend (zeros (2*b + 2)) T)]
  -- Final match: state C head = (zeros(2b+2)*>T).head = 0, left = ones(2a+7), right = zeros(2b+1)*>T.
  have hhead2 : (Side.prepend (zeros (2*b + 2)) T).head = false := by
    rw [show (2*b + 2 : ℕ) = (2*b + 1) + 1 from by ring]; rfl
  have htail2 : (Side.prepend (zeros (2*b + 2)) T).tail = Side.prepend (zeros (2*b + 1)) T := by
    rw [show (2*b + 2 : ℕ) = (2*b + 1) + 1 from by ring]; rfl
  rw [hhead2, htail2]
  -- Normalize the left ones count: 2a+4+3 = 2(a+3)+1.
  show ({state := some stC, head := false,
         left := ones ((2*a + 4) + 3) *> blank∞,
         right := Side.prepend (zeros (2*b + 1)) T} : SConfig 6)
       = {state := some stC, head := false,
          left := ones (2*(a + 3) + 1) *> blank∞,
          right := Side.prepend (zeros (2*b + 1)) T}
  congr 2

/-- **R3a**: `C(a, 1, c+2) → C(a+2, 0, c+1)`, dt = 6a + 7.
Zero-block of size 2 with c+2 ones to the right; shrinks zero-block to 0,
adds 2 ones on the left, drops 1 one on the right.  Output still has at
least 1 one on the right, so it matches `C_on`.

**Phase structure**: same as R3b but phase 4 is `phase4_R3a` (2 steps, ends
on state C head=1 since the right still has ones). -/
theorem rule_R3a (a c : ℕ) :
    srun tm (C_zb a 0 (c + 2)) (6*a + 7) = C_on (a + 2) c := by
  -- Rewrite C_zb's right (zeros 1 *> ones (c+2) *> ...) into the form needed for the phases.
  have hright : Side.prepend (zeros (2*0 + 1)) (Side.prepend (ones (c+2))
                  (Side.prepend [false, true] blank∞))
              = Side.cons false (Side.prepend (ones (c+2))
                  (Side.prepend [false, true] blank∞)) := rfl
  rw [show (6*a + 7 : ℕ) = 4*a + (3 + ((2*a + 2) + 2)) from by ring]
  show srun tm {state := some stC, head := false,
                left := ones (2*a+1) *> blank∞,
                right := Side.prepend (zeros (2*0+1)) (Side.prepend (ones (c+2))
                          (Side.prepend [false, true] blank∞))} _ = _
  rw [hright, srun_add,
      inner_cycle_iter a (Side.cons false (Side.prepend (ones (c+2))
                           (Side.prepend [false, true] blank∞))),
      srun_add,
      phase2_R3b (ones (2*a) *> Side.cons false (Side.prepend (ones (c+2))
                                   (Side.prepend [false, true] blank∞))),
      srun_add]
  -- Reshape right: ones 1 *> ones (2a) *> cons false (ones (c+2) *> [false, true] *> blank)
  --              = ones (2a+1) *> cons false (ones (c+2) *> [false, true] *> blank)
  have hR : Side.prepend (ones 1) (Side.prepend (ones (2*a)) (Side.cons false
              (Side.prepend (ones (c+2)) (Side.prepend [false, true] blank∞))))
          = Side.prepend (ones (2*a + 1)) (Side.cons false
              (Side.prepend (ones (c+2)) (Side.prepend [false, true] blank∞))) := by
    rw [ones_merge 1 (2*a) _, show (1 + 2*a : ℕ) = 2*a + 1 from by ring]
  rw [hR, AR_sweep (2*a+1) (Side.prepend (ones 1) blank∞)
            (Side.prepend (ones (c+2)) (Side.prepend [false, true] blank∞)),
      ones_merge (2*a+1+1) 1 blank∞,
      phase4_R3a (2*a+1+1+1) c]
  -- Match C_on (a+2) c.
  show ({state := some stC, head := true,
         left := ones (2*a + 1 + 1 + 1 + 2) *> blank∞,
         right := Side.prepend (ones c) (Side.prepend [false, true] blank∞)} : SConfig 6)
       = C_on (a + 2) c
  simp only [C_on]
  congr 2

/-- **R3b**: `C(a, 1, 1) → C(a+2, 0, 0)`, dt = 6a + 7.
Boundary of R3a when `c+2 = 1`.  Output has `c = 0`, so matches `C_off`.

**Phase structure**: `4a` inner cycles + `3` step C→D→E→A transition +
`(2a+2)` step A right-sweep through 2a+1 ones + `2` step A→B→C endgame. -/
theorem rule_R3b (a : ℕ) :
    srun tm (C_zb a 0 1) (6*a + 7) = C_off (a + 2) := by
  -- Unfold macro configs; rewrite C_zb's right to a canonical list form.
  have hright : Side.prepend (zeros (2*0 + 1)) (Side.prepend (ones 1)
                  (Side.prepend [false, true] blank∞))
              = Side.prepend [false, true, false, true] blank∞ := by
    show Side.prepend (zeros 1) _ = _
    rw [← Side.prepend_append, ← Side.prepend_append]; rfl
  rw [show (6*a + 7 : ℕ) = 4*a + (3 + ((2*a + 2) + 2)) from by ring]
  show srun tm {state := some stC, head := false,
                left := ones (2*a+1) *> blank∞,
                right := zeros (2*0+1) *> ones 1 *> ([false, true] : List Sym) *> blank∞} _ = _
  rw [hright, srun_add,
      inner_cycle_iter a (([false, true, false, true] : List Sym) *> blank∞),
      srun_add,
      phase2_R3b (ones (2*a) *> (([false, true, false, true] : List Sym) *> blank∞)),
      srun_add]
  -- Reshape right: ones 1 *> ones (2a) *> [false, true, false, true] *> blank
  --              = ones (2a+1) *> cons false ([true, false, true] *> blank)
  have hR : Side.prepend (ones 1) (Side.prepend (ones (2*a))
              (Side.prepend [false, true, false, true] blank∞))
          = Side.prepend (ones (2*a + 1)) (Side.cons false
              (Side.prepend [true, false, true] blank∞)) := by
    rw [ones_merge 1 (2*a) _, show (1 + 2*a : ℕ) = 2*a + 1 from by ring]
    rfl
  rw [hR, AR_sweep (2*a+1) (Side.prepend (ones 1) blank∞)
            (Side.prepend [true, false, true] blank∞),
      ones_merge (2*a+1+1) 1 blank∞,
      phase4_R3b (2*a+1+1+1)]
  -- Final: C_off (a+2) unfolding
  show ({state := some stC, head := false,
         left := ones (2*a + 1 + 1 + 1 + 2) *> blank∞,
         right := ([true] : List Sym) *> blank∞} : SConfig 6) = C_off (a + 2)
  simp only [C_off]
  congr 2

/-- Base case of R3b at `a = 0`: direct unfold. -/
example : srun tm (C_zb 0 0 1) 7 = C_off 2 := by
  simp [C_zb, C_off, srun, sstep, tm]

/-- **R4**: `C(a, 0, c+1) → C(1, a+1, c)`, dt = 2a + 7.
Empty zero-block with c+1 ones; the left 1-block resets to `1^3` while
`a+1` of the right ones are converted into zeros.

**Phase structure**: `(2a+2)` step `C→F→C` iterated (consumes left ones,
deposits zeros on the right) + `5` step `C→D→E→A→B→C` endgame. -/
theorem rule_R4 (a c : ℕ) :
    srun tm (C_on a c) (2*a + 7) = C_zb 1 a c := by
  -- Abbreviation for the common right-tail Side.
  set T : Side := Side.prepend (ones c) (Side.prepend [false, true] blank∞) with hT
  have hC_on : C_on a c = {state := some stC, head := true,
                           left := ones (2*a + 1) *> blank∞, right := T} := rfl
  have hC_zb : C_zb 1 a c = {state := some stC, head := false,
                             left := ones 3 *> blank∞,
                             right := Side.prepend (zeros (2*a + 1)) T} := rfl
  rw [show (2*a + 7 : ℕ) = (2*a + 2) + 5 from by ring, hC_on, hC_zb, srun_add,
      phase1_R4 a T]
  have hR : Side.prepend (zeros (2*a + 2)) T
          = Side.cons false (Side.prepend (zeros (2*a + 1)) T) := by
    rw [show (2*a + 2 : ℕ) = (2*a + 1) + 1 from by ring]; rfl
  rw [hR, phase23_R4 (Side.prepend (zeros (2*a + 1)) T)]

/-- **R5**: `C(a, 0, 0) → C(1, 0, 2a+4)`, dt = 10a + 25.
Empty zero-block, no ones, on the trailing `0` of `01`.  Unfolds a much
larger right 1-block and resets the left block to `1^3`.

**Phase structure**: `4a` inner_cycle_iter + `3` phase2_R3b + `(2a+3)` AR_sweep
(with `M = blank` via `cons_false_blank`) + `2` prelude_R2 (with R=blank) +
`4` zero_cycle + `(4a+8)` R5_mid_gen + `3` phase2_R5 + `2` finish_R2. -/
theorem rule_R5 (a : ℕ) :
    srun tm (C_off a) (10*a + 25) = C_on 1 (2*a + 3) := by
  have hC_off : C_off a = {state := some stC, head := false,
                           left := ones (2*a + 1) *> blank∞,
                           right := Side.prepend [true] blank∞} := rfl
  have hC_on : C_on 1 (2*a + 3) = {state := some stC, head := true,
                                    left := ones 3 *> blank∞,
                                    right := Side.prepend (ones (2*a + 3))
                                               (Side.prepend [false, true] blank∞)} := rfl
  rw [show (10*a + 25 : ℕ)
       = 4*a + (3 + ((2*a + 3) + (2 + (4 + ((4*a + 8) + (3 + 2))))))
       from by ring, hC_off, hC_on]
  -- Phase 1: inner_cycle_iter.
  rw [srun_add, inner_cycle_iter a (Side.prepend [true] blank∞)]
  -- Phase 2: phase2_R3b.
  rw [srun_add, phase2_R3b (ones (2*a) *> Side.prepend [true] blank∞)]
  -- Reshape right: ones 1 *> ones (2a) *> [true] *> blank = ones (2a+2) *> blank.
  have hR1 : Side.prepend (ones 1) (Side.prepend (ones (2*a)) (Side.prepend [true] blank∞))
           = Side.prepend (ones (2*a + 2)) blank∞ := by
    rw [ones_merge 1 (2*a) _, show (1 + 2*a : ℕ) = 2*a + 1 from by ring]
    show Side.prepend (ones (2*a + 1)) (Side.prepend [true] blank∞)
       = Side.prepend (ones (2*a + 2)) blank∞
    rw [show (Side.prepend [true] blank∞) = Side.prepend (ones 1) blank∞ from rfl,
        ones_merge (2*a + 1) 1 blank∞,
        show (2*a + 1 + 1 : ℕ) = 2*a + 2 from by ring]
  rw [hR1]
  -- Phase 3: AR_sweep k=2a+2 with M = blank (using blank = cons false blank).
  have hblank : (blank∞ : Side) = Side.cons false blank∞ := Side.cons_false_blank.symm
  rw [show (Side.prepend (ones (2*a + 2)) blank∞ : Side)
        = Side.prepend (ones (2*a + 2)) (Side.cons false blank∞) from by rw [← hblank]]
  rw [srun_add, AR_sweep (2*a + 2) (Side.prepend (ones 1) blank∞) blank∞,
      ones_merge (2*a + 2 + 1) 1 blank∞,
      show (2*a + 2 + 1 + 1 : ℕ) = 2*a + 4 from by ring]
  -- Now state A head=0 left=ones(2a+4)*>blank right=blank.
  -- Rewrite the RIGHT (only) to cons false blank∞, preserving left=ones(2a+4)*>blank∞.
  show srun tm
        {state := some stA, head := false,
         left := ones (2*a + 4) *> blank∞, right := blank∞} (2 + _) = _
  rw [show ({state := some stA, head := false,
             left := ones (2*a + 4) *> blank∞, right := blank∞} : SConfig 6)
        = {state := some stA, head := false,
           left := ones ((2*a + 3) + 1) *> blank∞,
           right := Side.cons false blank∞} from by
        rw [show ((2*a + 3) + 1 : ℕ) = 2*a + 4 from by ring, ← hblank]]
  rw [srun_add, prelude_R2 (2*a + 3) blank∞]
  -- After prelude: state C head=blank.head=0 left=cons 0 (ones(2a+5)*>blank) right=blank.tail=blank.
  simp only [Side.head_blank, Side.tail_blank]
  -- Zero-cycle: left = cons 0 (ones(2a+5)*>blank).
  -- First unfold ones(2a+5) = cons 1 (cons 1 (ones(2a+3)*>blank)).
  have hleft_zc : Side.cons false (Side.prepend (ones ((2*a + 3) + 1 + 1)) blank∞)
                = Side.cons false (Side.cons true (Side.cons true
                    (Side.prepend (ones (2*a + 3)) blank∞))) := by
    show Side.cons false (Side.prepend (ones (2*a + 5)) blank∞)
       = Side.cons false (Side.cons true (Side.cons true
           (Side.prepend (ones (2*a + 3)) blank∞)))
    rw [show (2*a + 5 : ℕ) = (2*a + 3) + 1 + 1 from by ring]; rfl
  rw [hleft_zc, srun_add, zero_cycle (Side.prepend (ones (2*a + 3)) blank∞) blank∞]
  -- After zero_cycle: left = cons 1 (ones(2a+3)*>blank) = ones(2a+4)*>blank.
  --                   right = [false, true] *> blank.
  have hleft_rc : Side.cons true (Side.prepend (ones (2*a + 3)) blank∞)
                = Side.prepend (ones (2*a + 4)) blank∞ := by
    rw [show (2*a + 4 : ℕ) = (2*a + 3) + 1 from by ring]; rfl
  rw [hleft_rc, srun_add,
      R5_mid_gen a (Side.prepend ([false, true] : List Sym) blank∞)]
  -- After R5_mid_gen: left = cons 0 blank, right = ones(2a+4) *> [false, true] *> blank.
  rw [srun_add, phase2_R5 (Side.prepend (ones (2*a + 4)) (Side.prepend [false, true] blank∞))]
  -- After phase2_R5: state A head=0 left=ones 1 right=cons true (ones(2a+4) *> [false, true] *> blank).
  -- Apply finish_R2 with K=0 (K+1=1). R = ones(2a+4) *> [false, true] *> blank.
  -- finish_R2 output: head=R.head=1 (since ones(2a+4) starts with 1 if 2a+4 ≥ 1).
  rw [finish_R2 0 (Side.prepend (ones (2*a + 4)) (Side.prepend [false, true] blank∞))]
  -- Final: head=1, left=ones 3, right=(ones(2a+4) *> [false, true] *> blank).tail = ones(2a+3) *> [false, true] *> blank.
  have hhead : (Side.prepend (ones (2*a + 4)) (Side.prepend [false, true] blank∞)).head = true := by
    rw [show (2*a + 4 : ℕ) = (2*a + 3) + 1 from by ring]; rfl
  have htail : (Side.prepend (ones (2*a + 4)) (Side.prepend [false, true] blank∞)).tail
             = Side.prepend (ones (2*a + 3)) (Side.prepend [false, true] blank∞) := by
    rw [show (2*a + 4 : ℕ) = (2*a + 3) + 1 from by ring]; rfl
  rw [hhead, htail]

/-- Base case of R5 at `a = 0`: direct unfold. -/
example : srun tm (C_off 0) 25 = C_on 1 3 := by
  simp [C_off, C_on, srun, sstep, tm]

/-- **R6**: `C(a, 1, 0) → Halt`, dt = 6a + 9 (includes the final halting
transition `F, 0 → ---`; sim.py's dt = 6a+8 undercounts the halt step by 1).
Zero-block of size 2 but no ones to its right.

**Phase structure**: `4a` inner cycles + `3` step C→D→E→A transition +
`(2a+2)` step A right-sweep + `4` step halt endgame (A,0→B, B,0→C, C,1→F,
F,0 → ---). -/
theorem rule_R6 (a : ℕ) :
    (srun tm (C_zb a 0 0) (6*a + 9)).state = none := by
  have hright : Side.prepend (zeros (2*0 + 1)) (Side.prepend (ones 0)
                  (Side.prepend [false, true] blank∞))
              = Side.prepend [false, false, true] blank∞ := by
    show Side.prepend (zeros 1) (Side.prepend [] _) = _
    rw [Side.prepend_nil, ← Side.prepend_append]; rfl
  rw [show (6*a + 9 : ℕ) = 4*a + (3 + ((2*a + 2) + 4)) from by ring]
  show (srun tm {state := some stC, head := false,
                 left := ones (2*a+1) *> blank∞,
                 right := Side.prepend (zeros (2*0+1)) (Side.prepend (ones 0)
                            (Side.prepend [false, true] blank∞))} _).state = none
  rw [hright, srun_add,
      inner_cycle_iter a (Side.prepend [false, false, true] blank∞),
      srun_add,
      phase2_R3b (ones (2*a) *> Side.prepend [false, false, true] blank∞),
      srun_add]
  have hR : Side.prepend (ones 1) (Side.prepend (ones (2*a))
              (Side.prepend [false, false, true] blank∞))
          = Side.prepend (ones (2*a + 1)) (Side.cons false
              (Side.prepend [false, true] blank∞)) := by
    rw [ones_merge 1 (2*a) _, show (1 + 2*a : ℕ) = 2*a + 1 from by ring]
    rfl
  rw [hR, AR_sweep (2*a+1) (Side.prepend (ones 1) blank∞)
            (Side.prepend [false, true] blank∞),
      ones_merge (2*a+1+1) 1 blank∞]
  exact phase4_R6 (2*a+1+1+1)

/-- Base case of R6 at `a = 0`: direct unfold. -/
example : (srun tm (C_zb 0 0 0) 9).state = none := by
  simp [C_zb, srun, sstep, tm]

-- ============================================================
-- Initial configuration
-- ============================================================

/-- Config-form initial run target (matches `C_off 1` under `.toSConfig`). -/
def Init_Config : Config 6 :=
  { state := some stC,
    head  := false,
    left  := ones 3,
    right := [true] }

/-- Config-side lemma: from blank tape, reach `Init_Config` in 11 steps. -/
lemma init_to_Init_Config :
    run tm (initConfig 6) 11 = Init_Config := by
  decide

/-- Bridge: `Init_Config` lifts to `C_off 1`. -/
lemma Init_Config_toSConfig :
    Init_Config.toSConfig = C_off 1 := by
  simp [Init_Config, C_off, Config.toSConfig]

/-- From the blank tape, the TM reaches the first macro config `C(1, 0, 0)` at
step 11. -/
theorem init_to_C_off_1 :
    srun tm (sinitConfig 6) 11 = C_off 1 := by
  have h := congrArg Config.toSConfig init_to_Init_Config
  rw [toSConfig_run, toSConfig_initConfig, Init_Config_toSConfig] at h
  exact h

-- ============================================================
-- Mathematical model and halting equivalence
-- ============================================================

/-- Math-level macro state `C(a, b, c)`.  The three fields encode:
  * `a` — ones count in the left block (tape has `1^{2a+1}` left of head).
  * `b` — zero-block size (`0^{2b}` just right of head).
  * `c` — ones-block size (`1^c` after the zeros). -/
structure MathState where
  a : Nat
  b : Nat
  c : Nat
deriving Repr, Inhabited, DecidableEq

/-- One macro step: dispatches to the appropriate atomic rule based on the
`(b, c)` shape.  Returns `none` only at the halting case `(a, 1, 0)` (R6). -/
def nextMathState : MathState → Option MathState
  | ⟨a, 0, 0⟩       => some ⟨1, 0, 2*a + 4⟩                  -- R5
  | ⟨a, 0, c + 1⟩   => some ⟨1, a + 1, c⟩                    -- R4
  | ⟨_, 1, 0⟩       => none                                   -- R6 halt
  | ⟨a, 1, 1⟩       => some ⟨a + 2, 0, 0⟩                    -- R3b
  | ⟨a, 1, c + 2⟩   => some ⟨a + 2, 0, c + 1⟩                -- R3a
  | ⟨a, 2, c⟩       => some ⟨a + 1, 1, c + 1⟩                -- R1
  | ⟨a, b + 3, c⟩   => some ⟨a + 3, b + 1, c⟩                -- R2

/-- Math-level halt: the iteration of `nextMathState` eventually returns
`none`. -/
inductive mathHalts : MathState → Prop
  | haltStep (m : MathState) (h : nextMathState m = none) : mathHalts m
  | nextStep (m m' : MathState) (h : nextMathState m = some m')
             (h' : mathHalts m') : mathHalts m

/-- Embed a math state into its TM SConfig form. -/
def toConfig : MathState → SConfig 6
  | ⟨a, 0, 0⟩       => C_off a
  | ⟨a, 0, c + 1⟩   => C_on a c
  | ⟨a, b + 1, c⟩   => C_zb a b c

lemma toConfig_state (m : MathState) : (toConfig m).state = some stC := by
  rcases m with ⟨a, b, c⟩
  match b, c with
  | 0, 0 => rfl
  | 0, _+1 => rfl
  | _+1, _ => rfl

/-- Each math step is realized by a `k > 0`-step TM run.  If `nextMathState`
returns `some m'`, the TM reaches `toConfig m'`; if `none`, the TM halts. -/
theorem stm_simulates_math (m : MathState) :
    ∃ k, k > 0 ∧ (
      match nextMathState m with
      | some m' => srun tm (toConfig m) k = toConfig m'
      | none    => (srun tm (toConfig m) k).state = none) := by
  rcases m with ⟨a, b, c⟩
  match b, c with
  | 0, 0   => exact ⟨10*a + 25, by omega, rule_R5 a⟩
  | 0, c+1 => exact ⟨2*a + 7,   by omega, rule_R4 a c⟩
  | 1, 0   => exact ⟨6*a + 9,   by omega, rule_R6 a⟩
  | 1, 1   => exact ⟨6*a + 7,   by omega, rule_R3b a⟩
  | 1, c+2 => exact ⟨6*a + 7,   by omega, rule_R3a a c⟩
  | 2, c   => exact ⟨6*a + 11,  by omega, rule_R1 a c⟩
  | b+3, c => exact ⟨12*a + 24, by omega, rule_R2 a b c⟩

/-- **Halting equivalence** (math ↔ TM): from any math state, the TM halts
iff the math model halts. -/
theorem stm_halt_iff_math (m : MathState) :
    (∃ k, (srun tm (toConfig m) k).state = none) ↔ mathHalts m := by
  constructor
  · -- Forward: TM halts ⇒ math halts.  Strong induction on step count.
    intro ⟨k, hk⟩
    suffices ∀ (n : Nat) (m : MathState),
        (srun tm (toConfig m) n).state = none → mathHalts m from
      this k m hk
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro m hk
      obtain ⟨k_sim, _, h_sim⟩ := stm_simulates_math m
      cases h_next : nextMathState m with
      | none => exact mathHalts.haltStep _ h_next
      | some m' =>
        rw [h_next] at h_sim
        by_cases h_lt : n < k_sim
        · exfalso
          have h_kstate : (srun tm (toConfig m) k_sim).state = some stC := by
            rw [h_sim]; exact toConfig_state m'
          have h_nstate : (srun tm (toConfig m) k_sim).state = none := by
            rw [show k_sim = n + (k_sim - n) from by omega, srun_add,
                srun_halted _ _ hk]
            exact hk
          exact absurd (h_kstate.symm.trans h_nstate) (by decide)
        · push_neg at h_lt
          rw [show n = k_sim + (n - k_sim) from by omega, srun_add, h_sim] at hk
          exact mathHalts.nextStep _ _ h_next (ih (n - k_sim) (by omega) m' hk)
  · -- Backward: math halts ⇒ TM halts.  Induction on `mathHalts`.
    intro h_math
    induction h_math with
    | haltStep m h_none =>
      obtain ⟨k, _, h_sim⟩ := stm_simulates_math m
      rw [h_none] at h_sim
      exact ⟨k, h_sim⟩
    | nextStep m m' h_some _ ih =>
      obtain ⟨k, _, h_sim⟩ := stm_simulates_math m
      rw [h_some] at h_sim
      obtain ⟨k', hk'⟩ := ih
      exact ⟨k + k', by rw [srun_add, h_sim]; exact hk'⟩

private lemma no_halt_before_11 : ∀ k < 11, (run tm (initConfig 6) k).state ≠ none := by
  decide

/-- Tuple form of the atomic-rule transition function, matching the
`conjecture.txt` display.  `f(a, b, c)` returns the next macro state (or
`none` for `HALT`) by case-splitting on `(b, c)`. -/
def f : ℕ × ℕ × ℕ → Option (ℕ × ℕ × ℕ)
  | (a, 0, 0)     => some (1,     0,     2*a + 4)     -- R5
  | (a, 0, c + 1) => some (1,     a + 1, c)           -- R4
  | (_, 1, 0)     => none                              -- R6 halt
  | (a, 1, 1)     => some (a + 2, 0,     0)           -- R3b
  | (a, 1, c + 2) => some (a + 2, 0,     c + 1)       -- R3a
  | (a, 2, c)     => some (a + 1, 1,     c + 1)       -- R1
  | (a, b + 3, c) => some (a + 3, b + 1, c)           -- R2

/-- One-step iteration of `f` on Option-lifted tuples.  `none` is an
absorbing state (HALT persists). -/
def fStep (x : Option (ℕ × ℕ × ℕ)) : Option (ℕ × ℕ × ℕ) := x.bind f

/-- Bridge: `f` and `nextMathState` agree up to struct↔tuple conversion. -/
private lemma f_eq_nextMathState (a b c : ℕ) :
    f (a, b, c) = (nextMathState ⟨a, b, c⟩).map
                    (fun m => (m.a, m.b, m.c)) := by
  match b, c with
  | 0,     0     => rfl
  | 0,     _ + 1 => rfl
  | 1,     0     => rfl
  | 1,     1     => rfl
  | 1,     _ + 2 => rfl
  | 2,     _     => rfl
  | _ + 3, _     => rfl

/-- `fStep` preserves `none` (HALT is absorbing). -/
private lemma fStep_none_iter (k : ℕ) : fStep^[k] none = none := by
  induction k with
  | zero => rfl
  | succ k' ih => rw [Function.iterate_succ_apply', ih]; rfl

/-- Bridge: `mathHalts m` iff iterating `fStep` from the tuple
`(m.a, m.b, m.c)` eventually returns `none`. -/
private lemma mathHalts_iff_fStep (m : MathState) :
    mathHalts m ↔ ∃ k, fStep^[k] (some (m.a, m.b, m.c)) = none := by
  constructor
  · intro h
    induction h with
    | haltStep m hf =>
      refine ⟨1, ?_⟩
      show fStep (some (m.a, m.b, m.c)) = none
      show f (m.a, m.b, m.c) = none
      rw [f_eq_nextMathState, hf]; rfl
    | nextStep m m' hm' _ ih =>
      obtain ⟨k, hk⟩ := ih
      refine ⟨k + 1, ?_⟩
      rw [Function.iterate_succ_apply]
      show fStep^[k] (f (m.a, m.b, m.c)) = none
      rw [f_eq_nextMathState, hm']
      exact hk
  · rintro ⟨k, hk⟩
    induction k generalizing m with
    | zero =>
      exact absurd hk (by simp [Function.iterate_zero])
    | succ k' ih =>
      rw [Function.iterate_succ_apply] at hk
      show mathHalts m
      cases hfm : nextMathState m with
      | none => exact mathHalts.haltStep m hfm
      | some m' =>
        have hstep : fStep (some (m.a, m.b, m.c)) = some (m'.a, m'.b, m'.c) := by
          show f (m.a, m.b, m.c) = _
          rw [f_eq_nextMathState, hfm]; rfl
        rw [hstep] at hk
        exact mathHalts.nextStep m m' hfm (ih m' hk)

/-- **Main halt-iff theorem**: the Turing machine halts from the blank tape
iff the math model halts from the initial macro state `C(1, 0, 0)`. -/
theorem tm_halt_iff :
    (∃ k, (run tm (initConfig 6) k).state = none) ↔ mathHalts ⟨1, 0, 0⟩ := by
  have h_eq : ∀ k, (run tm (initConfig 6) k).state =
                    (srun tm (sinitConfig 6) k).state := fun k => by
    change _ = (srun tm (initConfig 6).toSConfig k).state
    rw [← toSConfig_run]; rfl
  have h_iff : (∃ k, (run tm (initConfig 6) k).state = none) ↔
               (∃ k, (srun tm (C_off 1) k).state = none) := by
    constructor
    · rintro ⟨k, hk⟩
      by_cases h : 11 ≤ k
      · refine ⟨k - 11, ?_⟩
        rw [h_eq, show k = 11 + (k - 11) from by omega, srun_add, init_to_C_off_1] at hk
        exact hk
      · exact absurd hk (no_halt_before_11 k (by omega))
    · rintro ⟨k, hk⟩
      exact ⟨11 + k, by rw [h_eq, srun_add, init_to_C_off_1]; exact hk⟩
  rw [h_iff]
  exact stm_halt_iff_math ⟨1, 0, 0⟩

/-- **Main halt-iff theorem (tuple form)**: the Turing machine halts from
the blank tape iff iterating `f` from `(1, 0, 0)` eventually hits `HALT`.

This is the Lean counterpart of the `conjecture.txt` statement:
  `Conjecture: ¬ ∃ k, f^k(1, 0, 0) = HALT`
— conjecturing the RHS is `False` is equivalent (by this theorem) to
conjecturing the TM never halts. -/
theorem tm_halt_iff_math :
    (∃ k, (run tm (initConfig 6) k).state = none) ↔
    ∃ k, fStep^[k] (some (1, 0, 0)) = none := by
  rw [tm_halt_iff, mathHalts_iff_fStep]

end Counter6
