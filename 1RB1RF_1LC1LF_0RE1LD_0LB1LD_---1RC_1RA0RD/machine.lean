import BusyLean
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open BusyLean

namespace ParityBouncer

/-!
# BB(6) Candidate: 1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD

## Transition Table

       0     1
  A   1RB   1RF
  B   1LC   1LF
  C   0RE   1LD
  D   0LB   1LD
  E   ---   1RC
  F   1RA   0RD

## Informal Dynamics (unverified — user sketch, 2026-04-19)

The tape length carries a parity that changes whenever the bouncer happens
to hit both ends of the tape at the same cycle. After each parity flip,
an "iterated bouncer" starts from the left end and **roughly doubles** its
reach with each iteration. When it finally hits the right end it advances
the right end by one cell — unless it hits both ends simultaneously, in
which case the machine halts.

Heuristic non-halt argument: under a pseudorandom / uniform model of the
bouncer's starting offset, the probability of a simultaneous both-ends hit
at tape length L decays like 1/L. Hence parity-flip lengths grow
exponentially; the iterated-bouncer lengths within a strip also grow
exponentially. Two exponentially-growing sequences have vanishing
probability of coinciding — so halting is "probviously" false barring an
early unlucky coincidence.

**Proving halt/nonhalt is not the primary goal** — we only want the macro
rewrite rules. Any halt/nonhalt fallout is a bonus.

## Macro Configuration

A **left-bouncer state** is the family

  C(z, m) := 0^∞ [C] (01)^z 1^m 0^∞

i.e. state C sitting on the leftmost cell of a visited region shaped
"zebra of length 2z, then a block of m ones". The integer `z ≥ 0` is the
zebra length (number of `01` pairs starting at the head) and `m ≥ 0` is
the block of solid ones to the right of the zebra.

The infinite-blank sides are realised in a `Config 6` as
`left := [], right := zebra z ++ ones m ++ zeros p`, with a padding
parameter `p` absorbing the right-blank budget.

## Observed Macro Rules (from Python simulation — see `sim*.py`)

The total "length" functional `L = 2z + m` is exactly the number of
non-blank cells. Every macro transition satisfies

                 ΔL ∈ { 2 (within parity strip), odd (parity flip) }.

Concretely we have observed the following rewrite rules. (Δstep counts
given by fitting `6·z²` for the doubling rule.)

1. **DBL** — doubling rule (dominant case, holds when m ≥ 2z is even-ish):
                  C(z, m) → C(2z, m - 2z + 2)             in ~6z² steps.
   This preserves `m`'s parity (2z is even), and increases L by +2.

2. **Non-DBL / parity-preserving boundary** — various small-m cases,
   e.g. (8, 3) → (10, 1), (10, 1) → (8, 7). These preserve the m-parity
   and still give ΔL = 2. Shape of the rule depends on m mod 4 and on z.

3. **Parity-flip cycles** — rare. Length increases by odd Δ (3 or 5).
   These correspond to the bouncer *hitting the right end* during the
   cycle (the `A`-state sweep in the simulator reaches `pos = maxpos + 1`,
   extending the right side by one or two cells before returning).
   Example: (4, 2) → (2, 11), ΔL = 5, parity even → odd.

4. **Simultaneous-both-ends hit** — the hypothesised halting condition.
   Not observed in ≥ 10⁷ steps. Would correspond to a cycle where the
   bouncer extends the right end (generic parity-flip event) *while* the
   F/A oscillation pattern on the left is already at the left edge,
   producing an E-reading-0 halt.

The first ~170 macro events within 10⁷ simulator steps all obey rules
(1)–(3); rule (4) is the (conjecturally absent) halting case.

## Progress Log

### 2026-04-19 — Initial setup, shift lemmas, DBL phases 1-3

- Wrote Python simulator (`sim.py`) and macro-config extractor
  (`sim3.py`, `sim4.py`). Traced a DBL cycle and a parity-flip cycle in
  `sim5.py`.
- Identified `C(z, m)` as the canonical macro config.
- Discovered the invariant `ΔL = 2` within a parity strip, `ΔL` odd
  across a parity flip.
- Observed: DBL takes exactly `6·z²` micro-steps (verified for
  z ∈ {2, 4, 8, 16, 32, ...} up to z ≈ 288 in a 10⁷-step run).
- **Proved (shift lemmas)**: `D_shift`, `CE_shift` (zebra right-sweep,
  `2(n+1)` steps), `FA_shift` (zebra-to-ones conversion ending in D,
  `2n+3` steps), `tm_init` (blank → `C(2, 1)` in 5 steps, via `decide`).
- **Proved (DBL phases 1–3)**: `tm_DBL_phase1` (CE sweep: `2z` steps,
  z zebra blocks → reverse-zebra on left), `tm_DBL_phase2` (4 boundary
  steps C→D→D→B→F), `tm_DBL_phase3` (F/A oscillation: 5 steps,
  consumes one zebra block on right and one 1 on left). Composite
  `tm_DBL_phase12` and `tm_DBL_phase123` verify the composition
  (phases 1+2 = `2z+4` steps; phases 1+2+3 = `2z+9` steps).
- **Remaining sorries**: `tm_DBL` (phases 4-5: D-walks + left
  extension — ~`6z² - 2z - 9` more steps; for z=2 that's 11 steps,
  traced in `sim5.py` as steps 39–50); `tm_small_m_odd` (m=1 case).
- `decide` sanity checks: `run M (C_Config 2 m 1) 24 = C_Config 4 (m-2) 1`
  for m ∈ {4, 11, 6}, plus `(2, 6, 3) → (4, 4, 3)`.

### 2026-04-19 (cont.) — Phase 4+5 dynamics and z=2 DBL

Detailed trace of `(z, m) = (4, 9) → (8, 3)` in 96 steps (sim5.py)
shows that phases 4+5 are **not** a simple loop — they are a
*recursive* structure of alternating sweeps:

  - mini-FA-sweep (F/A rightward, extending the developing zebra on
    the right and consuming 1s),
  - D-walk-back (D leftward through the built-up 1s),
  - repeat, each iteration processing a progressively larger stretch.

This mirrors the Phase-1–3 structure playing out in miniature, which
is exactly why the total step count is `6·z²` (quadratic): each of
the `z` outer zebra-blocks triggers an inner sweep of linear length.

**Proved (z=2 special case)**:
- `tm_DBL_round` — 4-step D,D,B,F cycle. Shape:
  `[0,1,1]++L | 1 | R → [0]++L | 1 | [0,1]++R`.
- `tm_DBL_rounds` — `k` consecutive rounds. Consumes `ones(2k)`
  from the left and prepends `zebra k` to the right.
- `tm_DBL_final` — 3-step closure D,D,B→C that extends the tape by
  two zeros when the left tape is `[false]` exactly.
- `tm_DBL_z2` — full DBL for `z = 2` composed from primitives
  (no `decide`): phase123 (13 steps) + 2 iterated rounds (8 steps)
  + final extension (3 steps) = 24 = `6·2²`.

**For `z ≥ 3`** the same rounds consume `ones 4` (the fixed-size
ones buffer from Phase 3's `false :: ones 4` prefix), but leave
behind the *reverse-zebra* tail `(zebra (z-2)).reverse` on the left.
Processing that tail triggers "break rounds" (D,D,B,F where F reads
`0`, diverting to `F,0→1RA` and a mini-FA-sweep), which recursively
mirror Phases 1–3 at a smaller scale.

TODO: (i) finish DBL phases 4+5 for `z ≥ 3` via an induction over
          the reverse-zebra length; each mini-recursion is
          `break_round + mini_FA + D_shift` matching the pattern of
          `tm_DBL_round` but with F reading 0.
      (ii) state remaining "small-m" rules from hand-traced simulator
           runs on concrete `(z, 1)` inputs.
-/

-- ============================================================
-- TM definition
-- ============================================================

def M : TM 6 := tm! "1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD"

-- Transition lemmas — evaluate M.tr without unfolding M itself.
-- This mirrors the Cryptid file's `cr_*` lemmas and prevents `simp [M]`
-- from expanding the TM globally.
@[simp] theorem pb_A0 : M.tr stA false = some (stB, true,  Dir.R) := rfl
@[simp] theorem pb_A1 : M.tr stA true  = some (stF, true,  Dir.R) := rfl
@[simp] theorem pb_B0 : M.tr stB false = some (stC, true,  Dir.L) := rfl
@[simp] theorem pb_B1 : M.tr stB true  = some (stF, true,  Dir.L) := rfl
@[simp] theorem pb_C0 : M.tr stC false = some (stE, false, Dir.R) := rfl
@[simp] theorem pb_C1 : M.tr stC true  = some (stD, true,  Dir.L) := rfl
@[simp] theorem pb_D0 : M.tr stD false = some (stB, false, Dir.L) := rfl
@[simp] theorem pb_D1 : M.tr stD true  = some (stD, true,  Dir.L) := rfl
@[simp] theorem pb_E0 : M.tr stE false = none := rfl
@[simp] theorem pb_E1 : M.tr stE true  = some (stC, true,  Dir.R) := rfl
@[simp] theorem pb_F0 : M.tr stF false = some (stA, true,  Dir.R) := rfl
@[simp] theorem pb_F1 : M.tr stF true  = some (stD, false, Dir.R) := rfl

-- ============================================================
-- Macro configuration
-- ============================================================

-- `zebra z` (from BusyLean.TapeHelpers): `zebra 0 = []`,
-- `zebra (c+1) = false :: true :: zebra c`. So `zebra z` begins with `0`
-- for `z ≥ 1` and has length `2z`.

/-- `C_Config z m p` = `0^∞ [C] (01)^z 1^m 0^p` with state C at the
    leftmost cell. Uses `mkConfigFromTape` so the head symbol is
    auto-extracted from the tape list — handles `z = 0` cleanly. -/
def C_Config (z m p : Nat) : Config 6 :=
  mkConfigFromTape 6 stC [] (zebra z ++ ones m ++ zeros p)

-- ============================================================
-- Shift lemmas
-- ============================================================

/-- D scans left through a run of `k` ones. After `k` steps the head has
    moved `k` cells left and sits on the `k`-th one (still reading `1`);
    `k` ones have migrated from the left tape to the right tape. -/
lemma D_shift (k : Nat) (L R : List Sym) :
    run M { state := some stD, head := true, left := ones k ++ L, right := R } k =
    { state := some stD, head := true, left := L, right := ones k ++ R } := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih => tm_ind_zero ih stD [M]

/-- **Single CE-cycle**: from C on a `0` with `[1, 0]` next on the
    right, 2 steps later C is on a `0` again with `[1, 0]` pushed to
    the left. Trivially `rfl` via the TM transitions. -/
lemma CE_one (L R : List Sym) :
    run M { state := some stC, head := false, left := L,
            right := true :: false :: R } 2 =
    { state := some stC, head := false,
      left := true :: false :: L, right := R } := rfl

/-- **CE right-sweep** over (n+1) zebra blocks: starting with C on the
    `0` of the first block and the remaining `n` blocks on the right,
    after `2(n+1)` steps C sits on whatever follows the zebra; the
    consumed `(01)^(n+1)` has migrated to the left tape (reversed). -/
lemma CE_shift (n : Nat) (L R : List Sym) :
    run M { state := some stC, head := false, left := L,
            right := true :: zebra n ++ R } (2 * n + 2) =
    { state := some stC, head := listHead R false,
      left := (zebra (n + 1)).reverse ++ L, right := listTail R } := by
  induction n generalizing L with
  | zero =>
    show run M { state := some stC, head := false, left := L, right := true :: R } 2 = _
    rw [show (2 : Nat) = 1 + 1 from rfl, run_add]
    simp only [run, step, pb_C0, pb_E1, listHead_cons, listTail_cons,
      zebra_succ, zebra_zero, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append]
  | succ n ih =>
    rw [show 2 * (n + 1) + 2 = 2 + (2 * n + 2) from by ring, run_add,
        show (zebra (n + 1) : List Sym) = false :: true :: zebra n from rfl,
        show (true :: false :: true :: zebra n ++ R : List Sym) =
          true :: false :: (true :: zebra n ++ R) from rfl]
    conv => lhs; enter [2]; rw [CE_one L (true :: zebra n ++ R)]
    rw [ih (true :: false :: L)]
    -- (zebra (n+1+1)).reverse ++ L = (zebra (n+1)).reverse ++ [true, false] ++ L
    have hz : zebra (n + 1 + 1) = zebra 1 ++ zebra (n + 1) := by
      rw [zebra_append]; congr 1; omega
    rw [hz]
    simp only [List.reverse_append, show (zebra 1).reverse = [true, false] from rfl,
      List.append_assoc, List.cons_append, List.nil_append]

/-- **F/A zebra sweep** with stop on entering the ones region.

    Starting: F on a `0` (the first cell of a zebra block), followed by
    `n` more zebra blocks, followed by at least one more `1` (the first
    cell of the ones region), then `R`.

    After `2n+3` steps, all `n+1` zebra blocks have become all-1, the
    starting cell of the ones region has been overwritten with `0`,
    state is D, head is one cell past that written 0. -/
lemma FA_shift (n : Nat) (L R : List Sym) :
    run M { state := some stF, head := false, left := L,
            right := true :: zebra n ++ true :: R } (2 * n + 3) =
    { state := some stD, head := listHead R false,
      left := false :: ones (2 * n + 2) ++ L, right := listTail R } := by
  induction n generalizing L with
  | zero =>
    show run M { state := some stF, head := false, left := L,
                 right := true :: true :: R } 3 = _
    rw [show (3 : Nat) = 1 + 1 + 1 from rfl, run_add, run_add]
    simp only [run, step, pb_F0, pb_A1, pb_F1, listHead_cons, listTail_cons,
      List.cons_append, List.nil_append, ones_succ, ones_zero]
  | succ n ih =>
    rw [show 2 * (n + 1) + 3 = 2 + (2 * n + 3) from by ring, run_add,
        show (zebra (n + 1) : List Sym) = false :: true :: zebra n from rfl,
        show (true :: false :: true :: zebra n ++ true :: R : List Sym) =
          true :: false :: (true :: zebra n ++ true :: R) from rfl]
    -- Peel 2 steps (F,0→A then A,1→F) leaving the IH shape.
    conv => lhs; enter [2]; rw [show (2 : Nat) = 1 + 1 from rfl, run_add]
    conv => lhs; enter [2]; simp only [run, step, pb_F0, pb_A1,
      listHead_cons, listTail_cons, List.cons_append, List.nil_append]
    rw [show (true :: (zebra n ++ true :: R) : List Sym) =
          true :: zebra n ++ true :: R from rfl]
    rw [ih (true :: true :: L)]
    -- Fold the prepended `true::true` back into `ones (2n+2) + 2`.
    congr 1
    show false :: ones (2 * n + 2) ++ (true :: true :: L) =
          false :: ones (2 * (n + 1) + 2) ++ L
    rw [show (true :: true :: L : List Sym) = ones 2 ++ L from rfl,
        List.cons_append, ← List.append_assoc, ones_append,
        show 2 * n + 2 + 2 = 2 * (n + 1) + 2 from by ring,
        List.cons_append]

-- ============================================================
-- Macro step lemmas (sorried)
-- ============================================================

/-- **DBL sanity-checks at `z = 2`**: concrete instances of the DBL
    rule confirming the statement — step count 24, `p' = p`,
    `m' = m + 2 - 2z = m - 2`. `decide` hits recursion-depth limits
    for `z ≥ 4`; the full `tm_DBL` proof (below, after all primitives)
    is by structural composition. -/
example : run M (C_Config 2 4 1) 24 = C_Config 4 2 1 := by decide
example : run M (C_Config 2 11 1) 24 = C_Config 4 9 1 := by decide
example : run M (C_Config 2 6 3) 24 = C_Config 4 4 3 := by decide

-- Larger concrete checks confirming the step-count formula `6z²`.
-- Need `maxRecDepth` bumped because of deeper TM unfolding.
set_option maxRecDepth 2000 in
example : run M (C_Config 3 8 1) 54 = C_Config 6 4 1 := by decide
set_option maxRecDepth 20000 in
example : run M (C_Config 4 10 1) 96 = C_Config 8 4 1 := by decide

/-- **Phase-1 of a DBL cycle**: the CE-sweep over `z` zebra blocks
    (from `C_Config z m p` with `z ≥ 1`, `m ≥ 1`) takes `2z` steps and
    lands the head on the first `1` of the ones-region with the
    original zebra pushed to the left tape (reversed).

    This is the cleanest phase boundary — subsequent phases (boundary
    steps → FA_shift → D-walk → left-extension) have more intricate
    composition but the same machinery (`D_shift`, `FA_shift`). -/
lemma tm_DBL_phase1 (z m p : Nat) (hz : z ≥ 1) (hm : m ≥ 1) :
    run M (C_Config z m p) (2 * z) =
      { state := some stC, head := true,
        left := (zebra z).reverse, right := ones (m - 1) ++ zeros p } := by
  obtain ⟨z', rfl⟩ : ∃ z', z = z' + 1 := ⟨z - 1, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  show run M (mkConfigFromTape 6 stC []
    (zebra (z' + 1) ++ ones (m' + 1) ++ zeros p)) (2 * (z' + 1)) = _
  -- Peel the tape shape into a cons at the top level so
  -- `mkConfigFromTape_cons` can fire.
  simp only [show (zebra (z' + 1) : List Sym) = false :: true :: zebra z' from rfl,
             show (ones (m' + 1) : List Sym) = true :: ones m' from rfl,
             List.cons_append, mkConfigFromTape_cons]
  rw [show (2 * (z' + 1) : Nat) = 2 * z' + 2 from by ring]
  -- Re-associate to match `CE_shift`'s pattern (`(true :: zebra z') ++ R`).
  rw [show (true :: (zebra z' ++ true :: ones m' ++ zeros p) : List Sym) =
          true :: zebra z' ++ (true :: ones m' ++ zeros p) from by
        simp [List.append_assoc]]
  rw [CE_shift z' [] (true :: ones m' ++ zeros p)]
  simp only [List.cons_append, listHead_cons, listTail_cons,
             List.append_nil, Nat.add_sub_cancel,
             show (zebra (z' + 1) : List Sym) = false :: true :: zebra z' from rfl]

/-- **Phase-2 of a DBL cycle**: 4 boundary steps from the end of
    Phase 1 to F reading `0` one past the leftmost zebra cell. -/
lemma tm_DBL_phase2 (z m p : Nat) (hz : z ≥ 2) (hm : m ≥ 1) :
    run M { state := some stC, head := true,
            left := (zebra z).reverse, right := ones (m - 1) ++ zeros p } 4 =
      { state := some stF, head := false,
        left := (zebra (z - 2)).reverse,
        right := [true, false] ++ ones (m + 1) ++ zeros p } := by
  obtain ⟨z', rfl⟩ : ∃ z', z = z' + 2 := ⟨z - 2, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  -- Decompose: (zebra (z'+2)).reverse = [true,false,true,false] ++ (zebra z').reverse
  rw [show (z' + 2 : Nat) = z' + 2 from rfl, ← zebra_append z' 2, List.reverse_append,
      show ((zebra 2).reverse : List Sym) = [true, false, true, false] from rfl]
  -- Execute 4 concrete steps.
  rw [show (4 : Nat) = 1 + 1 + 1 + 1 from rfl, run_add, run_add, run_add]
  simp only [run, step, pb_C1, pb_D1, pb_D0, pb_B1,
             listHead_cons, listTail_cons, List.cons_append, List.nil_append,
             ones_succ, Nat.add_sub_cancel]

/-- **Phases 1+2 composed**: from `C_Config z m p` with `z ≥ 2` and
    `m ≥ 1`, after `2z + 4` steps the TM is in state F at the left
    edge reading `0`, with the entire original zebra converted into
    a prefix of the right tape `true :: false :: ones (m+1)`. -/
lemma tm_DBL_phase12 (z m p : Nat) (hz : z ≥ 2) (hm : m ≥ 1) :
    run M (C_Config z m p) (2 * z + 4) =
      { state := some stF, head := false,
        left := (zebra (z - 2)).reverse,
        right := [true, false] ++ ones (m + 1) ++ zeros p } := by
  rw [show (2 * z + 4 : Nat) = 2 * z + 4 from rfl, run_add,
      tm_DBL_phase1 z m p (by omega) hm, tm_DBL_phase2 z m p hz hm]

/-- **Phase-3 of a DBL cycle**: 5 steps of F/A oscillation converting
    the just-prepended `[1, 0, 1]` prefix plus the first `1` of the
    remaining ones-region into D with a fresh `false :: ones 4` on
    the left.

    This is `FA_shift` with `n = 1` — it consumes the single zebra
    block we just built in Phase 2. The remaining ones are consumed
    in later phases. Requires `m ≥ 2` so the trigger-cell is followed
    by at least one more `1`. -/
lemma tm_DBL_phase3 (z m p : Nat) (hm : m ≥ 2) :
    run M { state := some stF, head := false,
            left := (zebra (z - 2)).reverse,
            right := [true, false] ++ ones (m + 1) ++ zeros p } 5 =
      { state := some stD, head := true,
        left := false :: ones 4 ++ (zebra (z - 2)).reverse,
        right := ones (m - 2) ++ zeros p } := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  -- Rewrite `right` to FA_shift's pattern: `true :: zebra 1 ++ true :: R`.
  rw [show (([true, false] ++ ones (m' + 2 + 1) ++ zeros p : List Sym)) =
        true :: zebra 1 ++ true :: (ones (m' + 1) ++ zeros p) from by
      rw [show (ones (m' + 2 + 1) : List Sym) = true :: true :: ones (m' + 1) from rfl]
      rfl]
  rw [show (5 : Nat) = 2 * 1 + 3 from rfl]
  rw [FA_shift 1 ((zebra (z - 2)).reverse) (ones (m' + 1) ++ zeros p)]
  simp only [show (ones (m' + 1) : List Sym) = true :: ones m' from rfl,
             List.cons_append, listHead_cons, listTail_cons, Nat.add_sub_cancel,
             show (2 * 1 + 2 : Nat) = 4 from rfl]

/-- **Phases 1+2+3 composed**: from `C_Config z m p` with `z ≥ 2`,
    `m ≥ 2`, after `2z + 9` steps the TM is in state D reading the
    second `1` of the remaining ones-region, with a fresh zebra
    block `false :: ones 4` prepended to the reverse-zebra from
    Phase 2. -/
lemma tm_DBL_phase123 (z m p : Nat) (hz : z ≥ 2) (hm : m ≥ 2) :
    run M (C_Config z m p) (2 * z + 9) =
      { state := some stD, head := true,
        left := false :: ones 4 ++ (zebra (z - 2)).reverse,
        right := ones (m - 2) ++ zeros p } := by
  rw [show (2 * z + 9 : Nat) = (2 * z + 4) + 5 from by ring, run_add,
      tm_DBL_phase12 z m p hz (by omega), tm_DBL_phase3 z m p hm]

-- ============================================================
-- Phase 4: round and final-extension lemmas
-- ============================================================

/-- **One "clean" round of Phase 4**: a 4-step D,D,B,F cycle that
    removes the first 3 cells `[0, 1, 1]` from the left, writes one
    `0` at the final head cell (F,1→0RD), and leaves the machine in
    state D reading 1 (the `1` written by step 3, popped as head
    during step 4). Net: left gets `[0]` prepended to what remains
    after `[0, 1, 1]`; right gets `[0, 1]` prepended.

    L-invariance: steps 1–3 pop from the structural prefix `[0, 1, 1]`
    only. R-invariance: step 4's new head is always `1` because step
    3 wrote it. -/
lemma tm_DBL_round (L R : List Sym) :
    run M { state := some stD, head := true,
            left := [false, true, true] ++ L, right := R } 4 =
      { state := some stD, head := true,
        left := [false] ++ L, right := [false, true] ++ R } := by
  rw [show (4 : Nat) = 1 + 1 + 1 + 1 from rfl, run_add, run_add, run_add]
  simp only [run, step, pb_D1, pb_D0, pb_B1, pb_F1,
             listHead_cons, listTail_cons, List.cons_append, List.nil_append]

/-- **Final left-extension**: when the left tape has been reduced to
    the single `[0]` remnant of Phase 3, 3 more steps extend the tape
    by 2 zero cells and place the head at the new left boundary in
    state C reading 0.

    Steps: D,1→1LD (pops 0) ; D,0→0LB (reads blank) ; B,0→1LC (writes
    1 at the blank and extends to state C). -/
lemma tm_DBL_final (R : List Sym) :
    run M { state := some stD, head := true, left := [false], right := R } 3 =
      { state := some stC, head := false, left := [],
        right := [true, false, true] ++ R } := by
  rw [show (3 : Nat) = 1 + 1 + 1 from rfl, run_add, run_add]
  simp only [run, step, pb_D1, pb_D0, pb_B0,
             listHead_cons, listTail_cons, listHead_nil, listTail_nil,
             List.cons_append, List.nil_append]

/-- **Iterated round**: `k` consecutive "clean" rounds. Starts from
    `left = [0] ++ ones(2k) ++ L`, consumes the `ones(2k)` block in
    chunks of 2, and prepends `zebra k` to the right tape. -/
lemma tm_DBL_rounds (k : Nat) (L R : List Sym) :
    run M { state := some stD, head := true,
            left := [false] ++ ones (2 * k) ++ L, right := R } (4 * k) =
      { state := some stD, head := true,
        left := [false] ++ L, right := zebra k ++ R } := by
  induction k generalizing R with
  | zero =>
    simp only [Nat.mul_zero, ones_zero, List.append_nil, List.nil_append, run, zebra_zero]
  | succ k ih =>
    rw [show (4 * (k + 1) : Nat) = 4 + 4 * k from by ring, run_add]
    -- One round: [0, 1, 1] ++ (ones(2k) ++ L) → [0] ++ (ones(2k) ++ L).
    rw [show ([false] ++ ones (2 * (k + 1)) ++ L : List Sym) =
          [false, true, true] ++ (ones (2 * k) ++ L) from by
        rw [show (2 * (k + 1) : Nat) = 2 * k + 1 + 1 from by ring,
            show (ones (2 * k + 1 + 1) : List Sym) = true :: true :: ones (2 * k) from rfl]
        rfl]
    rw [tm_DBL_round (ones (2 * k) ++ L) R]
    -- IH with R' = [0, 1] ++ R.
    rw [show (([false] ++ (ones (2 * k) ++ L) : List Sym)) =
          [false] ++ ones (2 * k) ++ L from by rw [List.append_assoc]]
    rw [ih ([false, true] ++ R)]
    -- zebra k ++ [0, 1] ++ R = zebra (k+1) ++ R (via zebra_append).
    rw [show (zebra k ++ ([false, true] ++ R) : List Sym) =
          (zebra k ++ [false, true]) ++ R from (List.append_assoc _ _ _).symm]
    rw [show ([false, true] : List Sym) = zebra 1 from rfl]
    rw [show (zebra k ++ zebra 1 : List Sym) = zebra (k + 1) from zebra_append k 1]

/-- **Prelude to a break cycle**: 5 concrete boundary steps
    (D,1→D,0→B,1→F,0→A then A,1→F) that reshape the tape into the
    input form expected by `FA_shift`. -/
private lemma tm_DBL_break_prelude (i X' p : Nat) (L' : List Sym) :
    run M { state := some stD, head := true,
            left := [false, true, false] ++ L',
            right := zebra (2 * i) ++ ones (X' + 2) ++ zeros p } 5 =
      { state := some stF, head := false,
        left := true :: true :: L',
        right := true :: (zebra (2 * i) ++ true :: ones (X' + 1) ++ zeros p) } := by
  rw [show (5 : Nat) = 1 + 1 + 1 + 1 + 1 from rfl,
      run_add, run_add, run_add, run_add]
  simp only [run, step, pb_D1, pb_D0, pb_B1, pb_F0, pb_A1,
             listHead_cons, listTail_cons, List.cons_append, List.nil_append,
             show (ones (X' + 2) : List Sym) = true :: true :: ones X' from rfl,
             show (ones (X' + 1) : List Sym) = true :: ones X' from rfl]

/-- **Break cycle (index `i`)** — the alternating-round variant that
    processes one reverse-zebra pair on the left and emits `ones(4i+4)`
    to the right of the trailing `[false]`, while consuming 2 cells
    off the right-side ones buffer.

    Structure (total `4i+8` steps):
      - 4 steps "break round" D,1→D,0→B,1→F,0→A (differs from clean
        round in that F reads `0` not `1`, so `F,0→1RA` diverts).
      - 1 step A,1→1RF (sets up head=false for `FA_shift`).
      - `FA_shift (2i)` = `4i+3` steps (sweeps through `zebra(2i)`,
        consumes another `true` trigger cell, ends in state D).

    Correctness requires `X ≥ 2` (ones buffer must have 2 cells
    available for the FA to find a trigger and continue). -/
lemma tm_DBL_break_cycle (i X p : Nat) (L' : List Sym) (hX : X ≥ 2) :
    run M { state := some stD, head := true,
            left := [false, true, false] ++ L',
            right := zebra (2 * i) ++ ones X ++ zeros p } (4 * i + 8) =
      { state := some stD, head := true,
        left := [false] ++ ones (4 * i + 4) ++ L',
        right := ones (X - 2) ++ zeros p } := by
  obtain ⟨X', rfl⟩ : ∃ X', X = X' + 2 := ⟨X - 2, by omega⟩
  rw [show (4 * i + 8 : Nat) = 5 + (2 * (2 * i) + 3) from by ring, run_add,
      tm_DBL_break_prelude i X' p L']
  -- Reshape to FA_shift's pattern.
  rw [show ((true :: (zebra (2 * i) ++ true :: ones (X' + 1) ++ zeros p) : List Sym)) =
        true :: zebra (2 * i) ++ true :: (ones (X' + 1) ++ zeros p) from by
      simp [List.append_assoc]]
  rw [FA_shift (2 * i) (true :: true :: L') (ones (X' + 1) ++ zeros p)]
  simp only [show (ones (X' + 1) : List Sym) = true :: ones X' from rfl,
             List.cons_append, listHead_cons, listTail_cons,
             show (2 * (2 * i) + 2 : Nat) = 4 * i + 2 from by ring,
             Nat.add_sub_cancel]
  -- Close: false :: ones(4i+2) ++ true :: true :: L' = false :: ones(4i+4) ++ L'.
  rw [show (true :: true :: L' : List Sym) = ones 2 ++ L' from rfl,
      ← List.append_assoc, ones_append,
      show (4 * i + 2 + 2 : Nat) = 4 * i + 4 from by ring]
  simp only [List.nil_append]

/-- **One "unit" of Phase-4 iteration**: a paired break cycle followed
    by its round group (`break_cycle(i) ; round_group(i+1)`).

    Total step count: `(4i+8) + 8(i+1) = 12i + 16`.

    Consumes 2 cells from the right-side ones buffer (via break_cycle)
    and rebuilds `zebra(2(i+1))` on the right (via round_group). On
    the left, consumes `[true, false]` from the reverse-zebra tail. -/
lemma tm_DBL_unit (i X p : Nat) (L' : List Sym) (hX : X ≥ 2) :
    run M { state := some stD, head := true,
            left := [false, true, false] ++ L',
            right := zebra (2 * i) ++ ones X ++ zeros p } (12 * i + 16) =
      { state := some stD, head := true,
        left := [false] ++ L',
        right := zebra (2 * (i + 1)) ++ ones (X - 2) ++ zeros p } := by
  rw [show (12 * i + 16 : Nat) = (4 * i + 8) + 4 * (2 * (i + 1)) from by ring, run_add,
      tm_DBL_break_cycle i X p L' hX]
  -- After break_cycle: {D, 1, [false] ++ ones(4i+4) ++ L', ones(X-2) ++ zeros p}.
  -- Reshape: ones(4(i+1)) = ones(2·2(i+1)).
  rw [show ((4 * i + 4 : Nat)) = 2 * (2 * (i + 1)) from by ring]
  rw [tm_DBL_rounds (2 * (i + 1)) L' (ones (X - 2) ++ zeros p)]
  -- Close associativity of right tape.
  simp only [List.append_assoc]

/-- **Iterated units**: `j` consecutive Phase-4 units starting at break
    index `i`. The left starts as `[false] ++ (zebra j).reverse` (the
    reverse-zebra tail to process) and ends as `[false]` (fully
    consumed). The right tracks the buildup: `zebra(2i)` → `zebra(2(i+j))`,
    with `2j` ones consumed from the buffer.

    Step count: `12·i·j + 6·j² + 10·j` — verified by summing
    `Σ_{k=0}^{j-1} (12(i+k) + 16)`. -/
lemma tm_DBL_phase4_iter (j : Nat) :
    ∀ (i m p : Nat) (_hm : m ≥ 2 * (i + j)),
    run M { state := some stD, head := true,
            left := [false] ++ (zebra j).reverse,
            right := zebra (2 * i) ++ ones (m - 2 * i) ++ zeros p }
         (12 * i * j + 6 * j * j + 10 * j) =
    { state := some stD, head := true,
      left := [false],
      right := zebra (2 * (i + j)) ++ ones (m - 2 * (i + j)) ++ zeros p } := by
  induction j with
  | zero =>
    intro i m p _
    simp only [Nat.add_zero, zebra_zero, List.reverse_nil, List.append_nil, run]
  | succ j ih =>
    intro i m p hm
    -- 12i(j+1) + 6(j+1)² + 10(j+1) = (12i + 16) + (12(i+1)j + 6j² + 10j)
    rw [show (12 * i * (j + 1) + 6 * (j + 1) * (j + 1) + 10 * (j + 1) : Nat) =
          (12 * i + 16) + (12 * (i + 1) * j + 6 * j * j + 10 * j) from by ring,
        run_add]
    -- Decompose left: (zebra (j+1)).reverse = [true, false] ++ (zebra j).reverse.
    have hzeb : ((zebra (j + 1)).reverse : List Sym) = [true, false] ++ (zebra j).reverse := by
      rw [show (zebra (j + 1) : List Sym) = zebra j ++ zebra 1 from (zebra_append j 1).symm,
          List.reverse_append]
      rfl
    rw [hzeb]
    rw [show (([false] ++ ([true, false] ++ (zebra j).reverse) : List Sym)) =
          [false, true, false] ++ (zebra j).reverse from rfl]
    rw [tm_DBL_unit i (m - 2 * i) p ((zebra j).reverse) (by omega)]
    -- Now state is {D, 1, [false] ++ (zebra j).reverse,
    --                zebra (2(i+1)) ++ ones (m-2i-2) ++ zeros p}.
    rw [show (m - 2 * i - 2 : Nat) = m - 2 * (i + 1) from by omega]
    rw [ih (i + 1) m p (by omega)]
    -- Close: i + 1 + j = i + (j + 1) in the output.
    rw [show (i + 1 + j : Nat) = i + (j + 1) from by omega]

/-- **DBL rule**: one macro cycle of the doubling regime.

    `C(z, m) ─(6z² steps)─► C(2z, m − 2z + 2)`, with padding `p`
    preserved (no right-extension during a DBL cycle).

    Step count `6·z²` decomposes as:
      `phase123 (2z+9) + round_group(1) (8) + phase4_iter (j=z-2, i=1)
       (12(z-2) + 6(z-2)² + 10(z-2)) + final (3) = 6z²`

    Hypothesis `z ≥ 2` is load-bearing (phase 2 needs to pop at least
    one reverse-zebra pair from the left); `m + 2 ≥ 2z` ensures the
    ones-buffer has enough fuel to survive all `z-1` round-groups. -/
lemma tm_DBL (z m p : Nat) (hz : z ≥ 2) (hm : m + 2 ≥ 2 * z) :
    run M (C_Config z m p) (6 * z * z) = C_Config (2 * z) (m + 2 - 2 * z) p := by
  obtain ⟨z', rfl⟩ : ∃ z', z = z' + 2 := ⟨z - 2, by omega⟩
  -- Right-associated decomposition so `run_add` peels the leftmost summand each time.
  rw [show (6 * (z' + 2) * (z' + 2) : Nat) =
        (2 * (z' + 2) + 9) +
          ((4 * 2) + ((12 * 1 * z' + 6 * z' * z' + 10 * z') + 3)) from by ring,
      run_add, run_add, run_add,
      tm_DBL_phase123 (z' + 2) m p (by omega) (by omega)]
  -- After phase123: left = false :: ones 4 ++ (zebra z').reverse.
  simp only [show ((z' + 2 - 2 : Nat)) = z' from by omega]
  -- Reshape left for tm_DBL_rounds 2.
  rw [show ((false :: ones 4 ++ (zebra z').reverse : List Sym)) =
        [false] ++ ones (2 * 2) ++ (zebra z').reverse from rfl]
  rw [tm_DBL_rounds 2 ((zebra z').reverse) (ones (m - 2) ++ zeros p)]
  -- Reshape right for phase4_iter (i=1).
  rw [show ((zebra 2 ++ (ones (m - 2) ++ zeros p) : List Sym)) =
        zebra (2 * 1) ++ ones (m - 2 * 1) ++ zeros p from by
      simp [show (2 * 1 : Nat) = 2 from rfl]]
  rw [tm_DBL_phase4_iter z' 1 m p (by omega)]
  rw [tm_DBL_final (zebra (2 * (1 + z')) ++ ones (m - 2 * (1 + z')) ++ zeros p)]
  -- Close against C_Config (2(z'+2)) (m+2-2(z'+2)) p.
  show _ = mkConfigFromTape 6 stC []
             (zebra (2 * (z' + 2)) ++ ones (m + 2 - 2 * (z' + 2)) ++ zeros p)
  rw [show (m + 2 - 2 * (z' + 2) : Nat) = m - 2 * (1 + z') from by omega,
      show (2 * (z' + 2) : Nat) = 2 + 2 * (1 + z') from by ring,
      ← zebra_append 2 (2 * (1 + z')),
      show (zebra 2 : List Sym) = [false, true, false, true] from rfl]
  simp only [List.cons_append, List.nil_append, mkConfigFromTape_cons,
             List.append_assoc]

/-- **`tm_DBL` for `z = 2`** — fully from primitives (no `decide`).

    Decomposition:
      - `tm_DBL_phase123` (13 steps) → D, head=1, left=[0,1,1,1,1], right=ones(m-2)++zeros p.
      - Round 1 (4 steps) → left=[0,1,1], right=[0,1]++…
      - Round 2 (4 steps) → left=[0], right=[0,1,0,1]++…
      - Final ext. (3 steps) → C, head=0, right=[1,0,1,0,1,0,1]++ones(m-2)++zeros p.

    The final right matches `listTail (zebra 4 ++ ones (m-2) ++ zeros p)`,
    which is exactly `C_Config 4 (m-2) p`. -/
lemma tm_DBL_z2 (m p : Nat) (hm : m ≥ 2) :
    run M (C_Config 2 m p) 24 = C_Config 4 (m - 2) p := by
  rw [show (24 : Nat) = (2 * 2 + 9) + 4 + 4 + 3 from rfl,
      run_add, run_add, run_add,
      tm_DBL_phase123 2 m p (by omega) hm]
  simp only [show (zebra (2 - 2) : List Sym) = [] from rfl,
             List.reverse_nil, List.append_nil, ones_succ, ones_zero]
  -- After phase123: {D, [0,1,1,1,1], 1, ones (m-2) ++ zeros p}
  -- Round 1: L=[1,1], R = ones (m-2) ++ zeros p.
  rw [show ((false :: true :: true :: true :: true :: [] : List Sym)) =
        [false, true, true] ++ [true, true] from rfl]
  rw [tm_DBL_round [true, true] (ones (m - 2) ++ zeros p)]
  -- After round 1: {D, [0]++[1,1]=[0,1,1], 1, [0,1]++ones(m-2)++zeros p}
  rw [show (([false] ++ [true, true] : List Sym)) =
        [false, true, true] ++ [] from rfl]
  rw [tm_DBL_round [] ([false, true] ++ (ones (m - 2) ++ zeros p))]
  -- After round 2: {D, [0]++[]=[0], 1, [0,1]++[0,1]++ones(m-2)++zeros p}
  rw [show (([false] ++ [] : List Sym)) = [false] from rfl]
  rw [tm_DBL_final ([false, true] ++ ([false, true] ++ (ones (m - 2) ++ zeros p)))]
  -- Now close against C_Config 4 (m - 2) p.
  show (⟨some stC, [], false, _⟩ : Config 6) = C_Config 4 (m - 2) p
  simp only [C_Config, mkConfigFromTape,
             show (zebra 4 : List Sym) = [false, true, false, true, false, true, false, true] from rfl,
             List.cons_append, List.nil_append, listHead_cons, listTail_cons]

/-- The step-count formula for DBL. Auxiliary / sanity lemma. -/
lemma DBL_steps (z : Nat) : 6 * z * z = 6 * z^2 := by ring

-- ------------------------------------------------------------
-- Non-DBL transitions: highly irregular; no uniform (z, m) rule.
-- ------------------------------------------------------------
--
-- When the DBL hypothesis `m + 2 ≥ 2z` fails, the TM enters a
-- small-m or parity-flip regime whose outgoing (z', m') depends on
-- details of the tape beyond just (z, m). Simulator data
-- (see `sim6.py`, `sim-results.md`):
--
--   (2, 1)   →  (2, 4)   in 21 steps     [parity flip; start of cycle]
--   (8, 3)   →  (10, 1)  in 194 steps    [small-m, Δz = +2]
--   (10, 1)  →  (8, 7)   in 196 steps    [small-m, Δz = −2]
--   (12, 3)  →  (6, 17)  in 292 steps    [Δz = −6, parity-flip-like]
--   (54, 1)  →  (48, 15) in 5384 steps   [Δz = −6]
--
-- These transitions have no uniform (z, m) fingerprint: two different
-- `(z_1, m_1)` states with the same small-m shape can evolve to very
-- different (z', m'). A full formal account would need separate
-- lemmas for each observed fingerprint. We leave them as future work
-- — only the DBL rule is proven in this file.

-- ============================================================
-- Initialisation
-- ============================================================

/-- The machine reaches `C(2, 1)` in 5 steps from a blank tape. After
    that the main macro pattern begins. -/
lemma tm_init :
    run M (initConfig 6) 5 = C_Config 2 1 0 := by
  decide

-- ============================================================
-- Mathematical model
-- ============================================================

/-- Abstract macro state. `C z m` = left-edge bouncer; `Halt` = machine
    halted. The dynamics on macro states is a partial function whose
    exact definition we do not yet know for the "parity-flip" and
    "small-m" branches — only the DBL branch is regular. -/
inductive MacroState where
  | C    : Nat → Nat → MacroState
  | Halt : MacroState
  deriving Repr, DecidableEq

/-- Heuristic "nextMacroState" covering only the DBL rule. All other
    branches return a sentinel `Halt` — NOT because the machine halts
    (it almost certainly does not), but because this partial model
    only captures the regular doubling regime. A full model would
    require discovering the remaining rules from the simulator. -/
def nextMacroState_DBL : MacroState → MacroState
  | .C z m => if z ≥ 2 ∧ m + 2 ≥ 2 * z then .C (2 * z) (m + 2 - 2 * z) else .Halt
  | .Halt  => .Halt

/-- Soundness of the DBL model (via `tm_DBL`). -/
lemma DBL_simulates_TM (z m p : Nat) (hz : z ≥ 2) (hm : m + 2 ≥ 2 * z) :
    run M (C_Config z m p) (6 * z * z) =
      match nextMacroState_DBL (.C z m) with
      | .C z' m' => C_Config z' m' p
      | .Halt    => C_Config 0 0 0 := by
  simp [nextMacroState_DBL, hz, hm]
  exact tm_DBL z m p hz hm

-- ============================================================
-- Halt-condition commentary
-- ============================================================

/-
The only halting transition is `E, 0 → ---`. To reach this, the head
must be in state E reading a `0`. From the simulator trace the **only
way** state E gets a `0` under its head is during the C/E zebra-sweep
when the sweep runs off the end of the zebra into a right-side `0`.
In the DBL cycle this never happens: the zebra is always bounded to
the right by a `1` (the first cell of the `1^m` block, m ≥ 1).

The halt would therefore require an anomalous cycle where:
  (a) m = 0 (no ones buffer), so the zebra ends immediately in a 0, OR
  (b) the right extension during a parity flip aligns exactly so the
      next zebra sweep runs off the edge.

Condition (a) is visibly never hit (m ≥ 1 always in the simulator).
Condition (b) is the "hits both ends simultaneously" event of the
informal argument.
-/

/-- The conjectured halting condition. Empty predicate for now —
    completing this would require a full macro model. -/
def halts_macro : MacroState → Prop := fun _ => False

-- ============================================================
-- End of ParityBouncer
-- ============================================================

end ParityBouncer
