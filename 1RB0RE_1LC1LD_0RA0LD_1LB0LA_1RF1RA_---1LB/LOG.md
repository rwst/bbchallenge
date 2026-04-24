# Log — `1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB`

BB(6) holdout (Racheline's macro).  Goal: record **macro rules** for the
machine (halt/nonhalt is not the target).

## Transition table
|   | 0   | 1   |
|---|-----|-----|
| A | 1RB | 0RE |
| B | 1LC | 1LD |
| C | 0RA | 0LD |
| D | 1LB | 0LA |
| E | 1RF | 1RA |
| F | --- | 1LB |

Halt: only `F,0 → ---`.  F is reached only via `E,0 → 1RF`.

## Macro configuration  (wiki, Racheline)

```
A(n, m)  :=  …0 (01)^(3n−4) [A>] (01)^m 0…
```

State A moving right, head on the first cell of the right `(01)`-block
(reading a `0`).  Left tape = `(01)^(3n−4)` blank, right tape = `(01)^m`
blank.  Requires `n ≥ 2` (so `3n−4 ≥ 2`).

Initial reach: blank → `A(2, 0)` in **22 steps** (`sim.py init`).

## Macro rules (verified by `sim.py verify`)

All rules have step counts depending only on `n`, never on `m`
(except rule R1 which operates at `m = 0`).  Closed forms:

| Rule | Pattern | dt | Verified range |
|------|---------|------|----------------|
| R1 (reset) | `A(n, 0) → A(2, 3n−4)` | `12 n + 6` | `n ∈ [2, 9]` |
| R2 (even)  | `A(2n, m) → A(3n, m−2)`, `m ≥ 2` | `72 n² + 12 n − 30` | `n ∈ [1, 5]`, `m ∈ [2, 5]` |
| R3 (odd)   | `A(2n+1, m) → A(3n+1, m−1)`, `m ≥ 1` | `72 n² + 48 n − 10` | `n ∈ [1, 5]`, `m ∈ [1, 5]` |
| R4 (halt)  | `A(2n, 1) → halt` | `72 n² − 24 n − 15` | `n ∈ [1, 4]` |

Cross-checks:
- dt differences between R2 and R4 are always `36 n − 15` (the "savings"
  from the tape running off the right block at m = 1 instead of m ≥ 2).
- dt(R3) − dt(R2) = `36 n − 20`.  Odd-n requires one extra "carry" step
  per ones-sweep compared to even-n.

See `sim.py verify` output for the full table.

## Hydra reformulation

Racheline rewrites the orbit as a hydra map on a 3-tuple `(a, b, c)`:
```
a_0 = 2,  a_{i+1} = HydraMap(a_i)  where
  HydraMap(a) = a/2 * 3      if a even
  HydraMap(a) = a/2 * 3 + 1  if a odd
b_0 = 0,  b_{i+1} = b_i + (1 if a_i odd else 2)
c_0 = 0,  c_{i+1} = 3 a_j − 4  where  b_j = c_i
```

Observed `c` sequence: `0, 2, 5, 14, 185, 22205951667644132025548, …`.
Super-exponential growth; finite simulation never settles halt.

## Lean file structure  (`machine.lean`)

- TM literal and 12 transition `simp` lemmas — uncontentious.
- `oz k` = left-outward pattern `1,0,1,0,…` of length `2k` (list).
- `rightPat m` = right-outward pattern `1,0,1,0,…,1` of length `2m−1`
  (list; empty when `m = 0`).  Equals `1 :: zebra (m−1)`.
- `A_Config n' m` = wiki's `A(n' + 2, m)` as an `SConfig 6`.
  Using `n' := n − 2` eliminates all natural subtraction.
- Five sorried theorems:
  - `rule_reset  (n')         — R1`
  - `rule_even   (k m)        — R2 with n = k + 1`
  - `rule_odd    (k m)        — R3 with n = k + 1`
  - `rule_halt   (k)          — R4 with n = k + 1`
  - `init_to_A_20             — 22-step initial reach`

## Progress

2026-04-23:
- Wrote `sim.py` (bytearray-tape simulator, ~1e6 steps/s).
- Verified Racheline's four rules exhaustively on `n ≤ 11`, `m ≤ 5`.
- Derived closed-form `dt` for each rule (quadratic in `n`, indep. of `m`
  for R2/R3/R4, linear in `n` for R1).
- Wrote `machine.lean` with TM definition, transition simp lemmas,
  `A_Config` macro, and five sorried rule theorems.  File builds
  (only `sorry` warnings).
- Registered `Racheline6` in `lakefile.toml`.

2026-04-23 (R1 + initial proved):
- **`rule_reset` proved** via `left_cycle` (4-step shift) + `left_cycle_iter`
  (inductive `k`-step) + `phase2` (22-step tail with abstract tail `T`).
  Closed-form structure:
    - Phase 1 (left sweep, `4 (3n'+2)` steps): `oz (3n'+2) *> blank → blank`
      on left, depositing `cons false (zebra (3n'+2) *> blank)` on right.
      Proved by induction on `k = 3n'+2`; step uses `zebra_succ_append` to
      fold the per-cycle `(0,0,1)` prefix into `zebra`.
    - Phase 2 (22-step tail): empirically the head excursion is bounded
      (`+2` right, `−3` left) so the trajectory is uniform in any right
      tail `T`; closed by a single 22-step `simp [srun, sstep, tm, oz]`.
    - Composition: rewrite `zebra (3n'+2) = 0 :: 1 :: zebra (3n'+1)` to
      split the phase-1 output into phase-2's expected `cons false
      (cons false T)` shape.
- **`init_to_A_20` proved** as the corollary `phase2 blank∞` after
  simp-absorbing the blank duplication (`cons false blank = blank`).

2026-04-23 (R2/R3/R4 base cases proved):
- Empirically verified **tail-uniformity** for all four rules (head
  excursion is strictly bounded on the right):
    - R1: right_exc = 2 (consumes 0 cells of right, produces `3n−4` cells).
    - R2: right_exc = 4 (consumes `[T,F,T,F]` prefix, preserves `rightPat m`).
    - R3: right_exc = 2 (consumes `[T,F]` prefix, preserves `rightPat m`).
    - R4: right_exc = 3 (halts regardless of `m = 1`'s tail).
- **`rule_even_base (m)`**, **`rule_odd_base (m)`**, **`rule_halt_base`**
  proved by direct `simp [srun, sstep, tm]` on the abstract-tail
  reformulation.  54, 110, and 34 steps respectively.
- **`rule_halt` step count corrected**: the last-alive step is `72k²+120k+33`
  but `srun ... (dt+1)` is needed for `state = none` (since the
  halt-attempt step sets state to `none` via `sstep`'s `match tm.tr q s`
  `none ⇒ {c with state := none}` branch).  Updated theorem to use `+34`.

## TODO

Remaining sorries (3 general macro rules, all quadratic dt):

1. `rule_even` (general `k`) — `A(2k+2, m+2) → A(3k+3, m)` in `72k² + 156k + 54`.
2. `rule_odd`  (general `k`) — `A(2k+3, m+1) → A(3k+4, m)` in `72k² + 192k + 110`.
3. `rule_halt` (general `k`) — `A(2k+2, 1) → halt` in `72k² + 120k + 34`.

**Proof strategy** (partial — endgame infrastructure ready):

2026-04-24:
- **Identified endgame structure.**  For R2 and R3, the last phase of
  the trajectory is an **A-E sweep** over a run of `1`s: two-step cycles
  `A,1→0RE ; E,1→1RA` each consume one right-side `1` and prepend
  `(true, false)` to the left-outward tape (= one `oz` pair).
- **`ae_cycle` and `ae_sweep` proved** as general shift lemmas
  (parametric in left `L` and right `R` tails).  `ae_sweep k L R` runs
  `2k+2` steps on `ones (2k+1) *> R`, producing `oz (k+1) *> L` on the
  left and `R.tail` as right with head = `R.head`.
- **Setup phase shape understood** (empirically from `sim.py`): for R2
  at k, the first `72k² + 138k + 44` steps transform
  ```
    {A, false, oz (6k+2) *> blank, rightPat (m+2) *> blank}
  ```
  into the endgame input
  ```
    {A, true, blank, ones (18k+9) *> zebra m *> blank}.
  ```
  Then `ae_sweep (9k+4)` (= `2(9k+4)+2 = 18k+10` steps) finishes with
  `{A, false, oz (9k+5) *> blank, rightPat m *> blank} = A_Config (3k+1) m`.
  Total: `72k² + 156k + 54`. ✓
- **Setup phase itself is still quadratic** and resists an obvious
  inductive decomposition.  Each `k → k+1` adds `300k + 228` steps; the
  head trace shows `O(k)` excursions of growing depth, suggesting a
  nested `O(k) × O(k)` loop structure in the setup.

## Shifty6-style `subcycle_iter` machinery — plan and partial implementation

**Architecture goal** (mirrors `1RB1LA_0LC0RC_…-1LE/machine.lean`):

1. **Intermediate macro configs.**  Define `IntermR2 (outer inner : ℕ)`
   or similar, parameterized by the outer-loop counter (left-block
   oz pairs remaining) and inner counter (ones already accumulated on
   right).  Capture the per-excursion state A at left boundary.
2. **Fundamental shift lemmas.**  Short-trajectory lemmas with
   abstract `L`/`R` tails, each closable by direct `simp`:
    - `ae_cycle` (2 steps, done): `A,1` + `E,1` consumes one right `1`,
      prepends `oz 1` to left.
    - `ae_sweep` (`2k+2` steps, done): iterated `ae_cycle` over `ones
      (2k+1)`.
    - [TODO] **`bd_cycle`**: analogous for state B/D during leftward
      sweep through a zebra-like pattern (not yet identified precisely).
    - [TODO] **`boundary_turn`**: state-C hitting the left blank
      boundary, turning around with a specific write pattern.
3. **One outer iteration**: compose the above into a single
   `outer_step` lemma — "one excursion" of R2's setup phase — that
   goes from `IntermR2 (j+1) i` to `IntermR2 j (i+3)` (or similar).
4. **Iterated outer** → induction on the outer counter.
5. **Glue at `k=0` endpoint** → finalizes into `setup_phase_R2_k`
   form: `{A, true, blank, ones (18k+9) *> cons false X}`.
6. **Compose** with `ae_sweep (9k+4)` for the endgame → full `rule_even`.

**Done so far (2026-04-24):**
- `ae_cycle`, `ae_sweep` (general `k`).
- `bd_cycle`, `bd_sweep` (general `k`) — the left-sweep dual of AE:
  `bd_cycle` consumes `oz 1` from the left and deposits `ones 2` on
  the right, while `bd_sweep k` iterates this `k+1` times to consume
  `oz (k+1)` on the left and emit `ones (2k+2)` on the right.  This
  is the "reverse" primitive to `ae_sweep` — AE converts
  `ones → oz` (right-to-left), BD converts `oz → ones` (left-to-right).
  Both are fully local in the tape tails.
- `oz_succ_append` helper.
- `setup_phase_R2_k0` — explicit 44-step setup for `k=0`, closed by
  direct `simp` and parametric in an arbitrary tail `X`.
- `rule_even_base` — rewritten cleanly as `setup_phase_R2_k0` +
  `ae_sweep 4`, demonstrating the target decomposition shape.

**Hydra interpretation of the AE/BD duality:** The macro map
`A(2n, m) → A(3n, m−2)` multiplies `n` by `3/2`.  On the tape, `n` is
encoded as oz-pair count.  `bd_sweep` collapses `k` oz-pairs into `2k`
ones (halving), while `ae_sweep` expands `2k+1` ones into `k+1`
oz-pairs (doubling-ish).  The full R2 macro step is effectively
BD-sweep (compress) + various carries + AE-sweep (expand), with the
net `2n → 3n` growth reflected in the size change across the pair.

**Open (each needs ~100–200 lines of Lean):**
- `setup_phase_R2_k` (general `k`): the outer loop over oz pairs on
  the left.  Empirically, excursion `j` (for `j = 1, 2, …, 3k+3`)
  starts at state A at position `-(6k+2) - j + 1`, runs an AE-sweep
  rightward, turns around, runs a BD-sweep leftward, extending the
  oz pattern by one cell and returning 1 cell deeper.  Quadratic in
  total since both outer count (∼3k) and per-iteration sweep length
  (∼6k) grow with k.
- Analogous for `rule_odd` (R3) — same structure, different endgame
  size (`ae_sweep` parameter scales as `9k+3`).
- `rule_halt` (R4) — same setup, different endgame: the AE-sweep
  fails early (at `m=1` on the right, the first `1` of the right block
  is consumed but the trailing `0` halts via `F`).

**Decomposition progress snapshot:** R2 at k=0 decomposes as
`setup_phase_R2_k0` (44 steps, proved) + `ae_sweep 4` (10 steps,
proved via general lemma) = 54 steps.  The identical pattern for
general `k` gives `72k²+138k+44` + `18k+10` = `72k²+156k+54` — the
only gap is the `setup_phase_R2_k` lemma.

## Empirical structure of the setup phase (2026-04-24, exploratory)

Attempts to induct on `k` via `setup_phase_R2_k` run into the
following obstacles:

1. **No intermediate `A`-configs.**  Between the starting
   `A_Config (2(k+1)) (m+2)` and the ending
   `A_Config (3(k+1)+1) m`, the TM never passes through another
   standard `A_Config` shape (verified exhaustively in sim for `k ≤ 1`).
   So the induction cannot peel off one macro step at a time.

2. **State A head=1 at left-blank-boundary** occurs `6k+4` times per
   run (i.e. 4 for `k=0`, 10 for `k=1`, 16 for `k=2`).  These are the
   natural "outer iteration boundaries" — the head repeatedly returns
   to the left blank after sweeping through the left oz pattern.
   Inter-event step gaps: **not uniform**.  For `k=0`: gaps `13, 5, 7,
   19`.  For `k=1`: gaps `25, 37, 33, 29, 25, 21, 17, 5, 7, 55`.  The
   monotone-decreasing segment (`37 → 17`) suggests a nested-loop
   structure where the inner loop gets shorter as the oz-block grows,
   but the edge segments (start, transitions, tail) don't fit the
   pattern.

3. **Excursion-based decomposition** (each outer iteration shifts
   the leftmost-reach by 1 cell): also non-uniform in step count.
   For `k=1`: excursion gaps `37, 31, 28, 25, 25, 25, 55`.

4. **Outer-step lemma candidate.**  The cleanest potential form would
   be an invariant config `Interm (outer inner : ℕ)` such that
   `srun tm (Interm i (j+1)) f(i, j) = Interm i j`
   for some closed-form `f` (inner step), and
   `srun tm (Interm (i+1) 0) g(i) = Interm i j_max(i)`
   for some `g` (outer step).  Identifying the right parametrization
   of `Interm` requires either:
   - An automated shape-trace analysis (cf. `Chaotic6`'s
     `shape_summary.py`), which we have not built for this TM.
   - Careful manual study of 5–10 consecutive excursions from a
     byte-level trace, to reverse-engineer the invariant.

## Inner-step formula (from empirical analysis, verified for k ≤ 3)

For R2 at arbitrary `k ≥ 1`, the setup phase has a crisp inner loop:

**"A,1,left-blank" events:** occur at monotonically-increasing steps
during the setup phase.  At each event, the state is:
```
{A, true, blank∞, ones N *> cons false (ones M *> cons false (cons true ...))}
```
where `N` (the leading ones count) starts at `12k + 1` and decreases by
`2` per inner-loop iteration, and `M` (middle ones count) starts at
`4` and increases by `3` per iteration.

**Step count per inner iteration:** `2N + 11` steps to go from
`(N, M)` to `(N-2, M+3)`.  Verified exhaustively for R2 at `k=1, 2`.

**Number of inner iterations:** `6k`.  Total inner steps:
```
  ∑ᵢ₌₀^{6k-1} (2(12k+1-2i) + 11) = 72k² + 90k.
```

**Full setup budget** `72k² + 138k + 44`:
- Prelude (~`12k + 25`): reach first `A,1,left-blank` event at
  `ones = 12k+1, M = 4`.
- Inner loop (`6k` iterations, `72k² + 90k` total steps).
- Turnaround (ones=1 and ones=0 transitions, constant steps).
- Buildup (~`24k + small` steps to accumulate final `ones (18k+9)`).

## Path to full R2/R3/R4 proofs

Given the above obstacles, the recommended path is:

1. **`shape_trace.py` built** (2026-04-24).  Runs the TM for a chosen
   R2/R3/R4 configuration and bins each step's config by a compact
   tape-shape schema around the head: `(state, head sym, left 1-run
   length, left 0-run length, left boundary [blank/zebra], right 1-run
   length, right 0-run length, right boundary)`.
2. **Schema inventory (from `shape_trace.py "R2 k=1"`):**
   - State A dominant schemata: `head=1 left=[0^1, zebra] right=[1^N,
     zebra]` for `N ∈ {1, 3, 5, 6}` — the "AE sweep middle" states.
   - State B dominant: `head=1 left=[0^1, zebra] right=[1^N, zebra]`
     — same "zebra sweep" pattern.
   - State A **left-boundary schema**: `head=1 left=[0^6, blank]
     right=[1^6, zebra]` — occurs 6 times for `k=1`, 12 times for
     `k=2` (i.e. `6k` times).  This is the natural outer-iteration
     boundary.
   - State B left-boundary: same pattern, also `6k` per setup.
3. **Proposed `IntermR2` invariant** based on the schema inventory:
   ```
   IntermR2 (outer inner : ℕ) (suffix : Side) : SConfig 6 :=
     { state := some stA, head := true,
       left := blank∞,
       right := ones inner *> Side.cons false suffix }
   ```
   where `suffix` encodes the "growing zebra + preserved tail `X`".
   Need to characterize `suffix`'s structure over outer iterations.
4. **Proposed shift rules** for completing the proof:
   - Already have `ae_sweep`, `bd_sweep`.
   - Need **`left_cycle_on_zebra`**: B or D state traveling leftward
     through a zebra pattern with the head modifying cells.  Direct
     2-step cycle similar to `bd_cycle` but for slightly different
     neighbor patterns.
   - Need **`turnaround_at_boundary`**: state A at leftmost with `0^N,
     blank` on left does a short fixed-length turnaround.
5. **Compose `outer_step`** lemma: one outer iteration transforms
   `IntermR2 (i+1) inner suffix` to `IntermR2 i inner' suffix'` in
   some closed-form number of steps.
6. **Compose `setup_phase_R2_k`** via induction on the outer counter.

Estimated effort: 300–600 lines of Lean per rule (R2, R3, R4), with
shared infrastructure.  The `ae_sweep` / `bd_sweep` primitives we've
already proved will be reused heavily.

## Refined empirical structure (2026-04-24 evening)

Step-count decomposition of setup phase (verified for `k = 1, 2, 3`):
- **Prelude:** `12k + 13` steps to reach first `A,1,left-blank` event with
  ones=`12k+1`, M=4.  Each unit of `k` adds 12 steps, matching the extra
  6 cells on the left (× 2 steps/cell).
- **Inner loop:** `6k` iterations of `2N+11` each, total `72k² + 90k`.
- **Remaining (turnaround + buildup):** `36k + 31` steps.
- **Total:** `(12k+13) + (72k²+90k) + (36k+31) = 72k² + 138k + 44`. ✓

**Good news (uniformity-in-tail verified):**
- For any fixed `k`, `setup_phase_R2 k X` can be proved by **direct
  `simp`** with the tail `X` abstract (trajectory doesn't access cells
  beyond position `hp + 4`).  Proven explicitly: `setup_phase_R2_k0`
  (44 steps) and `setup_phase_R2_k1` (254 steps).  The approach is
  mechanical and works for any fixed `k`.

**Bad news (no clean per-`k` induction):**
- The `(k + 1) → k` step adds `144k + 210` steps (not constant).
- The inner-loop count `6k` depends linearly on `k`, with per-iteration
  step count `2N + 11` where `N = 12k + 1 - 2i` also depends on `k`.
- Hence naive induction on `k` doesn't work; needs nested induction
  with an explicit `N, M` invariant.

## Current proof state (2026-04-24)

`machine.lean` has exactly **3 sorries**:
1. `setup_phase_R2` (line 356) — the general-`k` setup phase for R2.
   All of `rule_even` depends only on this.
2. `rule_odd` (line 519) — R3 has a different structure (head right
   excursion = 2 regardless of `k`; no AE-sweep endgame), so the R2
   decomposition doesn't apply.  Needs its own analysis.
3. `rule_halt` (line 564) — similar structure to R2 but ends at `F,0`;
   the setup phase is largely shared with R2.

**Dependency graph** (2026-04-24, ALL PROVED):
```
rule_reset       — fully proved ✅
init_to_A_20     — fully proved ✅
rule_even_base   — fully proved ✅
rule_odd_base    — fully proved ✅
rule_halt_base   — fully proved ✅
setup_phase_R2   — fully proved ✅  (prelude_R2 + inner_loop_iter + post_inner_loop)
setup_phase_R3   — fully proved ✅  (prelude_R3 + inner_loop_iter + post_inner_loop_R3)
halt_endgame_R4  — fully proved ✅  (phase_A + phase_B + ae_sweep + F,0 halt)
rule_even        — FULLY PROVED ✅ (via setup_phase_R2)
rule_odd         — FULLY PROVED ✅ (via setup_phase_R3)
rule_halt        — FULLY PROVED ✅ (via prelude_R2_gen + inner_loop_iter + halt_endgame_R4)
```

## ALL FOUR RULES FULLY PROVED 🎉

**Shared infrastructure (generic in abstract tail `Y`):**
- `ae_cycle`, `ae_sweep` — A-E 2-step cycle and iterated sweep.
- `bd_cycle`, `bd_sweep` — D-B left-sweep dual.
- `cyclic_rest` — D-state closing sweep (`2p+3` steps, inductive on p).
- `middle_R2` — 9-step middle phase (shared by R2 and R3's inner-step).
- `inner_step` — `4p+17` steps (composition: ae_sweep + middle_R2 + C→D + cyclic_rest).
- `inner_loop_iter` — `4PI+19I-2I²` steps (induction on I).
- `initial_9` — 9-step fixed prelude start (shared by R2 and R4).
- `phase_A`, `phase_B` — fixed 5+7 step post-inner-loop transitions (shared by R2 and R4 halt).
- `phase_C` — R2-specific endgame absorbing `cons true (cons false X)`.

**R3-specific:**
- `initial_16_R3`, `prelude_R3`, `phase_post_R3_1`, `post_inner_loop_R3`, `setup_phase_R3`.

**R4-specific:**
- `prelude_R2_gen` — prelude with abstract `Y2` tail (reuses initial_9).
- `halt_endgame_R4` — phase_A + phase_B + ae_sweep + 3 halt transitions.

**Full R2 proof chain:**
- `ae_cycle` (2 steps) → `ae_sweep` (2k+2 steps, inductive).
- `bd_cycle` (2 steps) → `bd_sweep` (2k+2 steps, inductive).
- `cyclic_rest` (2p+3 steps, inductive on p): D-state closing sweep.
- `middle_R2` (9 steps, fixed): middle of inner step.
- `inner_step` (4p+17 steps): ae_sweep + middle_R2 + C→D + cyclic_rest.
- `inner_loop_iter` (4PI+19I-2I² steps, inductive on I): iterated inner_step.
- `initial_9` (9 steps, fixed): prelude's head start.
- `prelude_R2` (12k+13 steps): initial_9 + C→D + cyclic_rest.
- `phase_A` (5 steps, fixed), `phase_B` (7 steps, fixed), `phase_C`
  (4q+11 steps): post-inner-loop sub-phases.
- `post_inner_loop` (36k+31 steps): phase_A + phase_B + phase_C.
- `setup_phase_R2` (72k²+138k+44 steps): prelude_R2 + inner_loop_iter
  + post_inner_loop, case-split on k=0 vs k ≥ 1.
- `rule_even` (72k²+156k+54 steps): setup_phase_R2 + ae_sweep (9k+4).

## Files

- `machine.lean` — the TM definition, all proved theorems, and the
  3 remaining sorries (general-`k` R2/R3/R4).
- `sim.py` — Python simulator; verification of wiki rules.
- `shape_trace.py` — automated schema-frequency analyzer (see
  `python3 shape_trace.py "R2 k=1"` etc.).
- `LOG.md` — this log.

Infrastructure that will likely be shared across rules:
- **Zebra-sweep lemmas** for states A, C, D when the head traverses a
  block of alternating `01` cells.  The TM has many 2-step cycles over
  `01` patterns (e.g. A reading 0→B writes 1 then B reads 1→D writes 1);
  factor each into a shift-rule `EvStep` lemma.
- **Block-transition lemmas** at the `(01)/(blank)` boundary on the right.
- **Carry lemmas** for the left side: when the TM sweeps left through
  `(01)^k`, it produces a new `(01)^k'` with `k' = 3k/2` or `3(k−1)/2 + 1`
  depending on parity — this is the hydra map acting on the tape.

Other:
- `sim.py trace N` is useful for inspecting state sequences.
- `sim.py orbit N` follows the macro orbit from `A(2, 0)` — can be used
  to sanity-check formalized rules against the true trajectory.
