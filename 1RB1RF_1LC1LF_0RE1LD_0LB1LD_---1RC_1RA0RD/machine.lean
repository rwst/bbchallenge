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

### 2026-04-19 — Initial setup & shift lemmas

- Wrote Python simulator (`sim.py`) and macro-config extractor
  (`sim3.py`, `sim4.py`). Traced a DBL cycle and a parity-flip cycle in
  `sim5.py`.
- Identified `C(z, m)` as the canonical macro config.
- Discovered the invariant `ΔL = 2` within a parity strip, `ΔL` odd
  across a parity flip.
- Observed: DBL takes exactly `6·z²` micro-steps (verified for
  z ∈ {2, 4, 8, 16, 32, ...} up to z ≈ 288 in a 10⁷-step run).
- **Proved**: `D_shift`, `CE_shift` (zebra right-sweep, 2(n+1) steps),
  `FA_shift` (zebra-to-ones conversion ending in D, 2n+3 steps),
  `tm_init` (blank → `C(2, 1)` in 5 steps, via `decide`).
- **Remaining sorries**: `tm_DBL` (main macro cycle — needs gluing the
  shift lemmas + ~10 concrete boundary steps); `tm_small_m_odd` and
  `tm_parity_flip` (placeholders — need more simulator tracing).

TODO: (i) prove DBL — a clean plan exists (CE_shift → 3 C/D/B steps →
          1 B→F step → FA_shift → D-scan back → B-extend-left → CE_shift
          of length z+1 blocks backwards); step arithmetic should match
          `6z²` exactly, but needs checking against `sim5.py` output,
      (ii) state remaining "small-m" and parity-flip rules from
           hand-traced simulator runs on concrete `(z, m)` inputs,
      (iii) (aspirational) halt-equivalence theorem paralleling
            Antihydra's `mathHalts`.
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

/-- **DBL rule**: one macro cycle of the doubling regime.

    `C(z, m) ─(6z² steps)─► C(2z, m - 2z + 2)`, with the right-side
    padding preserved (no right-extension during a DBL cycle; the
    `+2` length increase is entirely absorbed on the left).

    Verified empirically by simulator for `z ∈ {2, 4, 8, 16, 32, 64, 128,
    256}` and `m` ranging over many residues. Step count formula: the
    cycle visits each of the `z` zebra blocks four times (two sweeps C/E
    and two sweeps F/A plus a D scan) giving `6·z²`. -/
lemma tm_DBL (z m p : Nat) (hz : z ≥ 1) (hm : m + 2 ≥ 2 * z) :
    run M (C_Config z m p) (6 * z * z) = C_Config (2 * z) (m + 2 - 2 * z) p := by
  sorry

/-- **DBL sanity-check at `z = 2`**: a concrete instance of the DBL
    rule, reducible by `decide`. This confirms the statement of
    `tm_DBL` (step count, `p' = p`, `m' = m + 2 - 2z` formula) on the
    smallest nontrivial case. `decide` hits recursion-depth limits for
    `z ≥ 4`; the full `tm_DBL` proof would need a structural
    composition via `CE_shift`, `FA_shift`, `D_shift`, and ~10 concrete
    boundary steps. -/
example : run M (C_Config 2 4 1) 24 = C_Config 4 2 1 := by decide
example : run M (C_Config 2 11 1) 24 = C_Config 4 9 1 := by decide
example : run M (C_Config 2 6 3) 24 = C_Config 4 4 3 := by decide

/-- The step-count formula for DBL. Auxiliary / sanity lemma. -/
lemma DBL_steps (z : Nat) : 6 * z * z = 6 * z^2 := by ring

-- ------------------------------------------------------------
-- Parity-flip and boundary cycles (empirical inventory).
-- Each of these has been observed in the simulator; the exact Δstep
-- and Δm depend on z and on the specific residue of m mod (a small
-- modulus). We record them as *sorries* awaiting micro-level proof.
-- ------------------------------------------------------------

/-- **Small-m boundary rule (observed at m = 1)**: when `m = 1` and
    `z ≥ 4`, the DBL rule's hypothesis `m + 2 ≥ 2z` fails. Simulator
    data at `(z, 1) = (8, 1)` shows an `(z+2, 2z-1)` transition takes
    `194` steps (z=8 → z+2=10, 2z-1=15, final (10, 1) observed at step
    416 from (8, 1) at step 222; Δstep = 194).

    Not yet proved; statement below is the empirically conjectured
    shape. May require tightening of conditions on `z` mod 4. -/
lemma tm_small_m_odd (z : Nat) (_hz : z ≥ 4) (p : Nat) :
    ∃ steps p',
      run M (C_Config z 1 p) steps = C_Config (z + 2) (2 * z - 1) p' := by
  sorry

-- NOTE on parity flips. The transitions where the bouncer reaches the
-- right end (ΔL ∈ {3, 5}) have highly irregular (z, m) → (z', m')
-- fingerprints; see `sim4.py` output around steps 10089, 14303,
-- 220812, 241480, etc. Stating them as clean Lean lemmas requires a
-- case split on the precise way the right-end extension happens. We
-- defer these for now; the DBL rule + small-m boundary cover the
-- overwhelming majority of macro cycles.

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
  | .C z m => if z ≥ 1 ∧ m + 2 ≥ 2 * z then .C (2 * z) (m + 2 - 2 * z) else .Halt
  | .Halt  => .Halt

/-- Soundness of the DBL model (via `tm_DBL`). -/
lemma DBL_simulates_TM (z m p : Nat) (hz : z ≥ 1) (hm : m + 2 ≥ 2 * z) :
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
