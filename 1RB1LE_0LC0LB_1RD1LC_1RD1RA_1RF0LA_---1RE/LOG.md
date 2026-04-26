# RachelineII — `1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE`

BB(6) holdout / Collatz-like candidate.  Halt/nonhalt is **not** the
target; we record macro rules.

## 2026-04-26 — initial setup

### Macro shape (Racheline, `previous-work/wiki.txt`)

```
A(N, m) = 0^∞ <C (10)^{N-6} 1^m 0^∞    for N ≥ 6, m ≥ 0
```

State C, head=0 sitting on the blank cell to the LEFT of the pattern,
all blanks to the head's left, then `(10)^{N-6} 1^m` to the right
followed by blanks.

In `machine.lean` we parameterise by `n := N - 6`, so `M n m`
represents `A(n+6, m)`.

### Macro rules (verified empirically by `sim.py dt`, n=3..10 each)

All step counts admit the closed form `dt = 6n² + a·n + b` (for the
wiki's `n`).  Translated to our `M` parameterisation (`j := n - 3`,
or `j := n - 4` for R_even_0):

| Rule       | Wiki                              | M-form                                    | dt                |
|------------|-----------------------------------|-------------------------------------------|-------------------|
| R_even     | `A(2n, m+3) → A(3n, m)`     n≥3  | `M (2j) (m+3) → M (3j+3) m`        j≥0  | `6j² + 26j + 17` |
| R_odd      | `A(2n+1, m+3) → A(3n+1, m+1)` n≥3 | `M (2j+1) (m+3) → M (3j+4) (m+1)` j≥0  | `6j² + 26j + 26` |
| R_odd_0    | `A(2n+1, 0) → A(6, 6n-15)`  n≥3  | `M (2j+1) 0 → M 0 (6j+3)`           j≥0  | `6j² + 14j + 7`  |
| R_even_0   | `A(2n, 0) → A(6, 0)`         n≥4  | `M (2j+2) 0 → M 0 0`                j≥0  | `6j² + 14j + 8`  |
| R_even_2   | `A(2n, 2) → halt`            n≥3  | `M (2j) 2` halts                    j≥0  | `6j² + 20j + 10` |
| R_odd_2    | `A(2n+1, 2) → A(6, 6n-10)`   n≥3  | `M (2j+1) 2 → M 0 (6j+8)`           j≥0  | `6j² + 26j + 25` |

Notational equivalence: `M n 1 = M (n+1) 0` (the trailing `0` of an
extra `(10)` block merges with `blank∞`).  Halting is concentrated in
R_even_2 and the translated cycler `M 0 0 → M 0 0` (not handled by any
rule above; never returns to a finite-tape A(N,m) macro config).

### Initial reach

Blank tape → `M 1 0 = A(7, 0)` in 3 steps:
```
  step 0: state A on blank        -> A,0→1RB
  step 1: state B on blank R      -> B,0→0LC
  step 2: state C on `1`          -> C,1→1LC
  step 3: state C on blank L of `1`  ← M 1 0
```

Then `R_odd_0` at `j = 0` takes `M 1 0 → M 0 3 = A(6, 3)` in 7 more
steps (10 total), matching the wiki's start.

### Orbit (from `sim.py orbit`)

Starting from `A(6, 3)`, the trajectory is

```
  i      N      m         dt          total
  0      6      3         17             17  → A(9, 0)
  1      9      0         27             44  → A(6, 9)
  2      6      9         17             61  → A(9, 6)
  3      9      6         58            119  → A(13, 4)
  4     13      4        158            277  → A(19, 2)
  5     19      2        397            674  → A(6, 44)
  ...
 21   2398      7    8613609     15487462  → A(3597, 4)
 22   3597      4   10000000+      timeout
```

The trajectory grows roughly geometrically; whether it ever halts
(via R_even_2) or becomes a translated cycler (via R_even_0 reaching
`M 0 0`) is the BB(6) question for this machine.

## Status

* `sim.py` — Python simulator; verifies all 6 dt formulas exactly for
  `n ∈ 3..10` and traces the orbit.
* `machine.lean` — Lean file with TM definition, transition simp
  lemmas, `tenpow` helper, `M n m` macro config, and **6 sorried**
  macro rules.  Proved:
  - `tenpow_succ_append` (helper)
  - `M_collapse` (notational equivalence `M n 1 = M (n+1) 0`)
  - `init_to_A_7_0` (3-step Config bridge with `decide`)
  - `init_to_A_6_3` (10-step Config bridge with `decide`)
  **All 6 macro rules fully proven!  Zero sorries on the rules.**

  Halting equivalence (added 2026-04-26):
  - `MathState`, `nextMathState`, `mathHalts` math model encoding
    the macro rules with cases for halt (`m=2 ∧ n` even),
    `m=1` notational, `m=0/2/≥3` × `n` even/odd.
  - `M_0_0_nonhalt` — the TM doesn't halt from `M 0 0` (translated
    cycler enters state D and stays).
  - `tm_sim_halt` — fully proven.
  - `tm_sim_step` — sorried (routine 7-case split, each case extracts
    `j, m''` from parity hypothesis and invokes the relevant `rule_R_*`).
  - `stm_halts_iff_mathHalts` — fully proven (uses
    `M_0_0_nonhalt` to handle the `⟨0, 0⟩` translated-cycler case).
  - `tm_halt_iff` — fully proven, modulo `tm_sim_step`.  States:
    `(∃ k, halts) ↔ mathHalts ⟨1, 0⟩`.  Uses `init_to_A_7_0` to bridge
    blank tape → `M 1 0`, plus `init_no_halt_before_3` (3-step
    `decide`) for the `k < 3` case.
  - **`rule_R_even_0` — fully proven.**  Infrastructure (~120 lines):
    `IM_e0` intermediate config; `M_eq_IM_e0` and `IM_e0_eq_M_0_0`
    boundary lemmas; shift lemmas `D_zeros_shift` (k-step F-head sweep
    accumulating `ones k` on left) and `B_drain_ones_shift` (k-step
    T-head drain accumulating `zeros k` on right); 7-phase
    `IM_e0_trans` transition lemma (case-split on `i = 0` vs `i = i'+1`
    with shift composition); `IM_e0_chain_gen` chain by induction on `j`.
  - **`rule_R_odd_0` — fully proven.**  Parallel `IM_o` framework
    (~250 lines): `IM_o`, `M_eq_IM_o`; new shift `C_walk_left` (state-C
    T-head walks left through `ones k` accumulating right);
    `IM_o_trans` (same 7-phase as `IM_e0_trans`, with `tenpow (2j+3)`);
    `IM_o_final` (8-phase: D-shift + D,1 + A,0 + B,0→C + C-walk + final
    C,1-on-blank, takes `IM_o i 0 → M 0 (6i+3)` in `12i+7` steps);
    `IM_o_chain_gen` combining transitions and final phase.
  - **`rule_R_odd_2` — fully proven.**  `IM_o2` framework (~340 lines):
    `IM_o2 i j` (right tape `zeros (6i) *> tenpow (2j+1) *> ones 2 *>
    blank∞`); `M_eq_IM_o2` boundary; `IM_a k` intermediate (right
    `zeros k *> ones 1 *> blank∞`); `IM_o2_trans` (12i+8 steps, copies
    `IM_o_trans` with `*> ones 2` trailer); `IM_o2_bridge`
    (`IM_o2 i 0 → IM_a (6i+5)` in `12i+8` steps, end-of-tape variant);
    `IM_a_final` (`IM_a k → M 0 (k+3)` in `2k+7` steps, mirrors
    `IM_o_final`); `IM_o2_final` composing bridge + IM_a phase
    (`24i+25` steps total); `IM_o2_chain_gen` chain by induction on `j`.
  - **`rule_R_even_2` — fully proven.**  Halt rule.  `IM_e_t` framework
    (~440 lines).  Theorem statement uses Lean step count `6j² + 20j + 11`
    (off-by-1 vs sim's `6j² + 20j + 10` — Lean counts the halt-firing
    step itself).  Components: `IM_e_t i j` (right `zeros (6i) *>
    tenpow (2j) *> ones 2 *> blank∞`); `IM_drain m` (state A, head=T,
    `ones (2m+2)`); two new shift lemmas — `A_E_drain` (alternating
    A,1/E,1 pair drains 2 ones, accumulates `[F,T]` on right) and
    `F_walk` (alternating F,1/E,0 pair consumes 2 zebra cells, builds
    2 ones on left); `IM_e_t_trans` (12i+8); `IM_e_t_to_drain` bridge;
    `IM_drain_halts` 6-phase halt proof (drain + transition + walk +
    F,1 + E,0 + halt); `IM_e_t_final` (18i+11 steps to halt);
    `IM_e_t_chain_gen` chain by induction on j.
  - **`rule_R_even` — fully proven.** `IM_R_e` framework (~600 lines).
    Components: `IM_R_e i j m` (right `zeros (6i) *> tenpow (2j) *>
    ones (m+3) *> blank∞`); `IM_R_e_post` intermediate; `M_eq_IM_R_e`
    boundary; three new lemmas — `cons_T_zebra` (list identity
    `[T] ++ zebra k = tenpow k ++ [T]`), `EF_tenpow_walk` (state E
    h=F walks through `tenpow k`), `EA_drain` (state E h=T drains
    `ones (2k)`, prepends `tenpow k`); `IM_R_e_trans` (12i+8 step
    iteration, copies `IM_e_t_trans` with `*> ones (m+3)` trailer);
    `IM_R_e_chain_gen` chain.  Final-phase `IM_R_e_post_to_M`
    decomposed into 5 sub-lemmas: `IM_R_e_phase_A` (6i+2 steps),
    `IM_R_e_phase_B` (6i+3, uses `A_E_drain` + `cons_T_zebra` to
    bridge zebra/tenpow boundary), `IM_R_e_phase_C` (6i+4, uses
    `EF_tenpow_walk` + 2 ones-walk steps), `IM_R_e_phase_D` (6i+5,
    uses `EA_drain` + 1 step), `IM_R_e_phase_Final` (3 steps:
    A,0 + B,0 + C,1, ending with `tenpow_succ` to combine `[T,F] ++
    tenpow (3i+2) = tenpow (3i+3)`).
  - **`rule_R_odd` — fully proven.** `IM_R_o` framework (~500 lines).
    Components: `IM_R_o i j m` (right `zeros (6i) *> tenpow (2j+1) *>
    ones (m+3) *> blank∞` — odd `tenpow` exponent); `IM_R_o_post i m`
    Stage-A intermediate (right `zeros (6i+5) *> ones (m+2) *> blank`);
    `M_eq_IM_R_o` boundary; `IM_R_o_trans` (12i+8 step iteration,
    same shape as `IM_R_e_trans` with `tenpow (2j+3)`); `IM_R_o_to_post`
    Stage A bridge (12i+8 steps: C-fire + D-shift + D,1 + A,0 + B-drain
    + B,0→C, similar to `IM_e_t_to_drain`/`IM_o2_bridge` but with
    `*> tenpow 1 *> ones (m+3) *> blank` input shape); Stage B
    decomposed into 3 phases — `IM_R_o_phase_B1` (6i+7 C+D+D,0+D,1
    fires), `IM_R_o_phase_B2` (6i+8 A↔E drain via `A_E_drain` +
    `cons_T_zebra` bridge + 1 fire), `IM_R_o_phase_B3` (3 fires
    A,0+B,0+C,1); `IM_R_o_post_to_M` composes B1+B2+B3 (12i+18 steps);
    `IM_R_o_final` composes Stage A + Stage B (24i+26 steps);
    `IM_R_o_chain_gen` chain by induction on j.
  Builds clean (only sorry warnings on the 6 rules).

## Todos

1. ~~Prove `M_collapse`~~ — done (induction on n, 5 lines).
2. ~~Prove `init_to_A_7_0`, `init_to_A_6_3`~~ — done (Config bridge +
   `decide`).
3. ~~**`rule_R_even_0`** done~~.  Proven via `IM_e0` intermediate
   config + `D_zeros_shift` / `B_drain_ones_shift` shift lemmas +
   7-phase `IM_e0_trans` transition lemma (case-split on `i`) +
   `IM_e0_chain_gen` chain induction on `j`.  ~120 lines.
4. Prove the other macro rules.  Strategy (mirror `Shifty6` /
   `1RB1LA_0LC0RC_…/machine.lean`):
   - **Base cases** (`j = 0`): direct `simp [srun, sstep, tm]` —
     17–26 step unrolls; should work for the smaller dt's, may need
     `set_option maxRecDepth` for the 25–26-step ones.
   - **Inductive cases**: identify a phase decomposition (sweep
     lemmas + iterated cycle).  Each rule's dt is quadratic in `j`,
     so look for an `O(j)`-step inner loop iterated `O(j)` times.
   - Likely shared infrastructure: a sweep lemma over `(10)^j` blocks
     and over `1^k` blocks; companion lemmas for the C/D-state
     left-going pass over a `(10)^j` segment.
4. Halt-equivalence wrapping (analogous to `Shifty6.tm_halts_iff`):
   define `MathState`, `nextMathState`, `mathHalts`, prove forward and
   backward simulation, derive the main `tm_halts_iff`.  Optional —
   the user's stated goal is "rules", not halt/nonhalt.

## Files

* `sim.py` — Python simulator + verifier (`verify`, `dt`, `orbit`,
  `init`, `trace` subcommands).
* `machine.lean` — Lean file (~250 lines, all rules sorried).
* `previous-work/wiki.txt` — Racheline's analysis (input).
* `LOG.md` — this file.
