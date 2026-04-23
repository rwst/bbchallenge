# Counter6 — `1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC`

A BB(6) holdout.  Goal: formalize **macro rules** observed at the `C>`
turnaround.  Halt/nonhalt is NOT the target.

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

## Previous work

`previous-work/wiki.txt` records two related analyses:

- **mxdys** analyzed the nearby TM `…_1RA1LD_…` with state E = `1RA1LD`
  (not ours).  Used `N(n, m) := 0^∞ 1^5 A> 0^{2n+1} 1^m 01 0^∞`.
- **Shawn Ligocki** analyzed OUR TM and gave Level-1 and Level-2 macro rules
  using `C(a, b, c) = $ 1^{2a+1} C> 0^{2b} 1^c 01 $`.

Ligocki's Level-1 rules (not atomic at the `C>` turnaround):
```
C(a, b+2, c)   -> C(a+3, b, c)
C(a, 1, c+2)   -> C(1, a+3, c)
C(a, 0, c+1)   -> C(1, a+1, c)
C(a, 0, 0)     -> C(1, 2, 2a+3)
C(a, 1, 1)     -> C(1, 2, 2a+7)
C(a, 1, 0)     -> Halt(2a+5)
```

These are validated in Ligocki's Rust simulator
(github.com/sligocki/busy-beaver/blob/main/rust/src/validator.rs#L1042).

## Atomic macro rules (this project)

`sim.py` simulates the TM and detects `C(a, b, c)` configurations at every
C-state turnaround (not just Ligocki's coarser checkpoints).  The six atomic
rules that close over all C-configs:

| Rule | Statement                                  | dt       |
|------|--------------------------------------------|----------|
| R1   | `C(a, 2,   c)   → C(a+1, 1,   c+1)`        | `6a+11`  |
| R2   | `C(a, b+3, c)   → C(a+3, b+1, c)`          | `12a+24` |
| R3a  | `C(a, 1,   c+2) → C(a+2, 0,   c+1)`        | `6a+7`   |
| R3b  | `C(a, 1,   1)   → C(a+2, 0,   0)`          | `6a+7`   |
| R4   | `C(a, 0,   c+1) → C(1,   a+1, c)`          | `2a+7`   |
| R5   | `C(a, 0,   0)   → C(1,   0,   2a+4)`       | `10a+25` |
| R6   | `C(a, 1,   0)   → HALT`                    | `2a+9`   |

All step counts verified empirically for `a ∈ 0..7, b ∈ 0..·, c ∈ 0..7`.

**Note**: `sim.py` reports `dt = 2a + 8` for R6 (the number of successful
transitions before the `F,0` halt), while the Lean `srun` convention counts
the halting transition too; hence `2a + 9` in `machine.lean`.  For non-halt
rules the sim and Lean dts agree.

### Why 6 atomic rules vs Ligocki's 6 Level-1 rules?

The rules COUNT is coincidence; the rules DIFFER.  Ligocki's Level-1 are
compositions of our atomic rules.  Examples:

- Ligocki `C(a, 2, c) → C(a+3, 0, c)` = our R1 ∘ R3a  (dt = `(6a+11) + (6(a+1)+7)` = `12a+24`, matches Ligocki).
- Ligocki `C(a, 1, c+2) → C(1, a+3, c)` = our R3a ∘ R4 (dt = `(6a+7) + (2(a+2)+7)` = `8a+18`).
- Ligocki `C(a, 0, 0)  → C(1, 2, 2a+3)` = our R5 ∘ R4 (dt = `(10a+25) + 9` = `10a+34`).
- Ligocki `C(a, 1, 1)  → C(1, 2, 2a+7)` = our R3b ∘ R5 ∘ R4 (three atomic steps).

The wiki's level-1 rules skip over intermediate `C(⋯, 0, ⋯)` checkpoints that
the simulator detects as genuine macro configurations.

## Initial configuration

From blank tape, TM reaches `C(1, 0, 0) = C_off 1` in **11 steps** (proved by
`decide`).

First 10 macro steps from `sim.py orbit`:
```
  C(1, 0, 0)  → C(1, 0, 6)      dt=35    [R5, a=1]
  C(1, 0, 6)  → C(1, 2, 5)      dt=9     [R4, a=1, c=5]
  C(1, 2, 5)  → C(2, 1, 6)      dt=17    [R1, a=1]
  C(2, 1, 6)  → C(4, 0, 5)      dt=19    [R3a, a=2]
  C(4, 0, 5)  → C(1, 5, 4)      dt=15    [R4, a=4]
  C(1, 5, 4)  → C(4, 3, 4)      dt=36    [R2, a=1, b=2]
  C(4, 3, 4)  → C(7, 1, 4)      dt=72    [R2, a=4, b=0]
  C(7, 1, 4)  → C(9, 0, 3)      dt=49    [R3a, a=7]
  C(9, 0, 3)  → C(1, 10, 2)     dt=25    [R4, a=9]
  ...
```

## Lean status

`machine.lean` contains:
- TM definition + transition simp lemmas.
- Three macro config variants: `C_zb` (b ≥ 1), `C_on` (b=0, c ≥ 1), `C_off`
  (b=0, c=0).
- Initial config `Init_Config` with `init_to_Init_Config` proven by `decide`
  and `Init_Config_toSConfig` proven by `simp`.
- `init_to_C_off_1` proven via the Config↔SConfig bridge.
- Six atomic rule theorems (R1, R2, R3a, R3b, R4, R5, R6) all `sorry`.

```
$ lake build Counter6
Build completed successfully (820 jobs).
[7 sorry warnings]
```

## TODO

### Rule status (7 of 7 proved — sorry-free!)
- [x] **`rule_R3b`** general `a`: phase `4a + 3 + (2a+2) + 2 = 6a+7`.
- [x] **`rule_R6`** general `a`: same phases 1–3 as R3b; phase 4 = 4-step halt.
- [x] **`rule_R4`** general `a, c`: phase1_R4 (2a+2) + phase23_R4 (5) = 2a+7.
- [x] **`rule_R3a`** general `a, c`: phases of R3b with phase4_R3a (2 steps,
      ends on state C head=1 since right still has ones).
- [x] **`rule_R1`** general `a, c`: phases of R3b with phase4_R1 (6 steps,
      shrinks zero-block by 2 and adds 1 one to the right).
- [x] **`rule_R2`** general `a, b, c`: nested phases. Outer: `4a + 3 + (2a+2) + (6a+19) = 12a+24`.
      Phase 4 itself is `2 prelude_R2 + 4 zero_cycle + 4(a+1) inner_cycle_iter +
      3 phase2_R3b + (2a+4) AR_sweep + 2 finish_R2`.
- [x] **`rule_R5`** general `a`: longest `dt = 10a+25`.  Structure:
      `4a` inner_cycle_iter + `3` phase2_R3b + `(2a+3)` AR_sweep (M=blank via
      `cons_false_blank`) + `2` prelude_R2 + `4` zero_cycle + `(4a+8)`
      R5_mid_gen (induction on a: a+1 inner_cycles + edge_cycle) + `3`
      phase2_R5 + `2` finish_R2.

### Shift lemmas proven (reusable infrastructure)
- `ones_merge (a b : ℕ) (S : Side)`: `ones a *> ones b *> S = ones (a+b) *> S`.
- `inner_cycle (L R : Side)`: 4-step C→D→E→B→C cycle that consumes 2 ones
  from the front of the left block and deposits 2 ones at the front of the
  right.  Direct `simp`.
- `inner_cycle_iter (a : ℕ) (R : Side)`: `a` iterations of the cycle.
- `phase2_R3b (R : Side)`: 3-step C→D→E→A transition at the left blank
  boundary, depositing 1 one on the right.
- `AR_sweep (k : ℕ) (L M : Side)`: A right-sweep consuming `k` ones followed
  by a 0 marker in `k+1` steps; output state A head=0.
- `phase4_R3b (K : ℕ)`: 2-step A,0→B→C endgame on `[1,0,1] *> blank`.
- `phase4_R6 (K : ℕ)`: 4-step halt endgame on `[0,1] *> blank`.
- `sub_cycle_R4 (L R : Side)`: 2-step C,1→F,1→C cycle consuming 2 ones
  from left, depositing 2 zeros on right.
- `phase1_R4 (a : ℕ) (R : Side)`: `a+1` iterations of `sub_cycle_R4`.
- `phase23_R4 (S : Side)`: 5-step C→D→E→A→B→C from state C head=0 on
  `[false] *> S`, adds 3 ones on left, right becomes `S`.
- `phase4_R3a (K c : ℕ)`: 2-step A,0→B→C ending on state C head=1 when right
  has `ones (c+2)`.
- `phase4_R1 (K c : ℕ)`: 6-step transform shrinking `zeros 2` to `zeros 1`
  and growing `ones c` to `ones (c+1)`.
- `zero_cycle (L R : Side)`: 4-step C→D→E→B→C variant where the leftmost
  cell is `0` rather than `1`.  Consumes `[0, 1, 1] *> L` from front of
  left, prepends `[0, 1]` to right.
- `prelude_R2 (K : ℕ) (R : Side)`: 2-step A,0→B→C when right starts with
  `cons false R`.
- `finish_R2 (K : ℕ) (R : Side)`: 2-step A,0→B→C when right starts with
  `cons true R`; grows left by 2 ones.
- `edge_cycle (R : Side)`: 4-step cycle terminating on blank.  Input left
  `ones 2 *> blank` becomes `cons false blank`; right gains ones 2.
- `phase2_R5 (R : Side)`: 3-step C→D→E→A from the `cons false blank` "edge"
  state; prepends one `1` to the right.
- `R5_mid_gen (a : ℕ) (R : Side)`: `(4a+8)`-step chunk = a+1 inner_cycles +
  1 edge_cycle.  Transforms `ones(2a+4)*>blank` left to `cons false blank`;
  right gains `ones(2a+4)`.  Induction on a.

### Medium-term (shift infrastructure)
- [ ] Identify the internal "phase structure" of each rule.  R1 and R2 likely
      share a right-sweep (A-state through `ones (2a+1)`) + some fixed
      endgame.  Factor as `AR_sweep`, `BR_sweep`, etc. à la Shifty6.
- [ ] Prove `rule_R1`, `rule_R2` by induction on `a` with phase decomposition.
- [ ] Prove `rule_R3a`, `rule_R3b`, `rule_R4` (dt linear in a, uniform in c).
- [ ] Prove `rule_R5`, `rule_R6`.

### Long-term (macro-level dynamics)
- [ ] Define a `MathState := (a b c : ℕ)` math model with `nextMathState` map.
- [ ] Prove `stm_simulates_math` (analog of Antihydra's key theorem): each
      math step is realized by some `srun` of the TM.
- [ ] Connect to `mathHalts` predicate.

## Files
- `sim.py` — Python simulator with macro detection and rule-verification
  modes (`verify`, `dts`, `orbit`, `trace`, `init`).
- `machine.lean` — Lean TM formalization with sorried atomic rules.
- `previous-work/wiki.txt` — copy of BB-wiki entry for reference.

## Proof strategy notes (historical)

- Each rule's dt is linear in `a`, so expected approach is induction on `a`
  (base case `a=0` by direct simp; inductive step with a generic
  `shift`-style lemma).  This is how all 6 proved rules are structured.

- Rules R1, R2, R3a, R3b, R4, R6 share a common "right sweep → left sweep"
  skeleton differing only in endpoint handling.  Confirmed in practice: the
  sweep lemmas (`inner_cycle`, `AR_sweep`, etc.) are heavily shared.

- R2 was initially expected to be hardest among the non-halt rules because
  of abstract `b`.  Actually factored cleanly by reusing `inner_cycle_iter`
  and `AR_sweep` **twice** (once at outer phase, again inside phase 4).

- R5 (`C_off a → C_on 1 (2a+3)`) has the longest per-step count (10a+25)
  and remains unproven.  Phases 1–3 are shared infrastructure; phase 4 is
  `4a+19` steps with its own a-dependent internal structure.

### Ligocki wiki "Level-1" compositions (sanity checks)
- `C(a, 2, c) → C(a+3, 0, c)` = R1 ∘ R3a, dt = `(6a+11) + (6(a+1)+7)` = `12a+24`.
  Matches R2's formula at `b=0`.
- `C(a, 1, c+2) → C(1, a+3, c)` = R3a ∘ R4, dt = `(6a+7) + (2(a+2)+7)` = `8a+18`.
- `C(a, 0, 0) → C(1, 2, 2a+3)` = R5 ∘ R4, dt = `(10a+25) + 9` = `10a+34`.
- `C(a, 1, 1) → C(1, 2, 2a+7)` = R3b ∘ R5 ∘ R4 (three atomic steps).

## Progress

**2026-04-23:**
- Wrote `sim.py`; fixed `detect_C_config` to handle `c = 0` edge case
  (odd leading-zero-run count).
- Ran `verify`, `dts`, `orbit`: confirmed 6 atomic macro rules with clean
  linear-in-`a` step counts.
- Wrote `machine.lean` skeleton: 3 macro config variants, 7 sorried rule
  theorems, init config lemmas proven.
- Added library to `lakefile.toml`; `lake build Counter6` succeeds.
- **Proved `rule_R3b`, `rule_R6`, `rule_R4`, `rule_R3a`, `rule_R1`** by phase
  decomposition.  Built 11 reusable shift lemmas spanning two "macro-
  family" structures:
  - Family A (head=false on zero-block): `inner_cycle`, `inner_cycle_iter`,
    `phase2_R3b`, `AR_sweep`, `phase4_R3b`, `phase4_R3a`, `phase4_R1`,
    `phase4_R6`.
  - Family B (head=true on one-block): `sub_cycle_R4`, `phase1_R4`,
    `phase23_R4`.
  Also corrected `rule_R6`'s dt from `2a+9` (misread sim dt) to `6a+9`.

- **Proved `rule_R2`** — the hardest regular rule.  Phase 4 of R2 has a
  nested structure that **reuses** `inner_cycle_iter` (with parameter `a+1`)
  + `phase2_R3b` + `AR_sweep` (k = 2a+3) a second time.  Added 3 new
  helpers: `zero_cycle` (4-step variant of `inner_cycle` when left starts
  with a 0), `prelude_R2` and `finish_R2` (2-step A→B→C transitions
  conditioned on right's head-cell).

- **Proved `rule_R5`** — the longest rule (10a+25 steps).  Phases 1–3 reuse
  `inner_cycle_iter` + `phase2_R3b` + `AR_sweep` (this time with M=blank via
  `cons_false_blank`).  Phase 4 reuses `prelude_R2` + `zero_cycle`, then a
  new `R5_mid_gen` (which has its own induction on a: a+1 inner_cycles + 1
  edge_cycle), then a new `phase2_R5` (3-step C→D→E→A from the post-edge
  state), then `finish_R2`.  Added 3 new lemmas: `edge_cycle`, `phase2_R5`,
  `R5_mid_gen`.  **File is now sorry-free: 7 of 7 rules proved.**

- **Added `tm_halt_iff`** (Antihydra-style halting equivalence): defined
  `MathState (a b c : Nat)`, `nextMathState` (dispatches to one of the 7
  rules based on `(b, c)` shape), `mathHalts` inductive predicate, and
  `toConfig : MathState → SConfig 6`.  Proved `stm_simulates_math` (each
  math step is a TM run) by case analysis over all 7 rules, and
  `stm_halt_iff_math` (TM halts ↔ math halts, via strong induction and
  `srun_halted`).  The final `tm_halt_iff` bridges blank-tape `run` to
  `srun` via `init_to_C_off_1` and a `no_halt_before_11` (proved by
  `decide`).  Theorem: TM halts from blank ↔ `mathHalts ⟨1, 0, 0⟩`.
