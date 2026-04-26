# Progress log — `1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF`

BB(6) holdout candidate.  Halt/nonhalt is **not** the target; this file records
observed macro rules and their formalization status.

## Target TM

```
  | 0   | 1   |
A | 1RB | 1RE |
B | 1LC | 1LD |
C | --- | 1LA |
D | 1LB | 1LE |
E | 0RF | 0RA |
F | 1LD | 1RF |
```

Halts only on `C,0 → ---`.

## Macro configuration

```
A(m, n)  ≡  0^inf  1^m  (01)^n  0  [A]>  0^inf
```

Racheline's wiki uses `k = n + 9` in the second argument (so her starting
config `A(1, 10)` is our `A(1, 1)`; her `A(m, k)` is our `A(m, k-9)`).

The encoding is not injective: `A(0, n) ≡ A(1, n-1)` as tapes, since a
leading `0` of `(01)^n` absorbs into the infinite blank.  Canonical form
uses `m ≥ 1`.

## Macro rules

All parameters `i ≥ 0`, all `m ≥ 1` where applicable.  Step counts `dt`
fitted as `6i² + Ai + B`.  Empirically verified by `sim.py` / `verify_dt.py`
for `i ∈ 0..9`, `m ∈ 1..9`.

| rule | LHS → RHS | dt | status |
|---|---|---|---|
| `shift_even_high` | `A(m+5, 2i)    → A(m+1, 3i+4)` | `6i² + 28i + 28` | ✓ proved |
| `shift_odd_high`  | `A(m+5, 2i+1)  → A(m+1, 3i+6)` | `6i² + 40i + 54` | ✓ proved |
| `shift_m4_even`   | `A(4, 2i)      → A(1, 3i+3)`   | `6i² + 28i + 28` | ✓ proved |
| `shift_m4_odd`    | `A(4, 2i+1)    → A(1, 3i+5)`   | `6i² + 40i + 54` | ✓ proved |
| `m1_even_halt`    | `A(1, 2i)      → halt`         | `6i² + 22i + 19` ⁂ | ✓ proved |
| `m1_odd_reset`    | `A(1, 2i+1)    → A(6i+7, 1)`   | `6i² + 28i + 37` | ✓ proved |
| `m2_even_halt`    | `A(2, 2i)      → halt`         | `6i² + 22i + 21` ⁂ | ✓ proved |
| `m2_odd_halt`     | `A(2, 2i+1)    → halt`         | `6i² + 34i + 43` ⁂ | ✓ proved |
| `m3_even_reset`   | `A(3, 2i)      → A(6i+6, 1)`   | `6i² + 28i + 33` | ✓ proved |
| `m3_odd_reset`    | `A(3, 2i+1)    → A(6i+10, 1)` | `6i² + 40i + 59` | ✓ proved |

⁂ Halt rules: `dt` is `sim.py`'s `t.steps` plus 1, since Lean's `sstep` counts
the C,0→halt transition as a step (state = some stC → state = none) but
sim's `t.steps` does not increment for None transitions.

The shift rules are *local* to the separator-and-zebra block (independent of
the left ones-block): `dt` formulas contain no `m` dependency.

Initial bridge (`init_to_A11`): from blank tape, 15 steps reach `A(1, 1)`
(Racheline's `A(1, 10)`).  Proved via `decide` on the list-Config bridge.

## Orbit from `A(1, 1)` (first 14 macro steps)

```
  i   m     n   k      dt       total  -> next
  0   1     1  10      37          37  -> A(7, 1)
  1   7     1  10      54          91  -> A(3, 6)
  2   3     6  15     171         262  -> A(24, 1)
  3  24     1  10      54         316  -> A(20, 6)
  4  20     6  15     166         482  -> A(16, 13)
  5  16    13  22     510         992  -> A(12, 24)
  6  12    24  33    1228        2220  -> A(8, 40)
  7   8    40  49    2988        5208  -> A(4, 64)
  8   4    64  73    7068       12276  -> A(1, 99)
  9   1    99 108   15815       28091  -> A(301, 1)
 10 301     1  10      54       28145  -> A(297, 6)
 11 297     6  15     166       28311  -> A(293, 13)
 12 293    13  22     510       28821  -> A(289, 24)
 13 289    24  33    1228       30049  -> A(285, 40)
```

The `B(m) := A(m, 1)` sub-orbit matches the `HydraMap(10) = ⌊3·10/2⌋`
iterates: `B(1) → B(7) → B(24) → B(301) → …`.

## Formalization status

`machine.lean` builds clean — **all 10 macro rules proved, 0 sorries**.
~2500 lines total.

Plus a halting characterization:
- `tm_halt_iff`: TM halts from blank tape iff macro orbit from `A(1, 1)` halts.
- `MacroHalts` inductive predicate: characterizes which `(m, n)` halt under
  the 10 rules.
- `A_halts_of_MacroHalts`: forward implication (`MacroHalts m n` → A(m, n)
  halts in TM).
- `tm_halts_of_MacroHalts_11`: composes the two — if `MacroHalts 1 1` holds,
  then the BB-relevant TM halts.

Plus a math-iteration formulation (mirroring the wiki-style conjecture):
- `f : Nat → Nat → Option (Nat × Nat)`: explicit macro-step map encoding
  the 10 rules in 9 cases.  `f m n = none` ↔ HALT.
- `fIter : Nat → Nat × Nat → Option (Nat × Nat)`: iterated `f`.
- `fIter_succ_chain`: chaining lemma for `fIter`.
- `MacroHalts_of_f_halt`, `f_some_pos_m`, `MacroHalts_back_step`: helpers
  for case analysis on `f`'s pattern.
- `simulates_macro_some`: TM faithfully simulates each non-halt macro step
  (with `dt ≥ 1`, deriving from each rule's positive step count).
- `MacroHalts_iff_fIter_halts` (with `m ≥ 1`): equivalence between inductive
  halt predicate and `fIter`-based halt — both directions proved.
- `MacroHalts_of_A_halts`: TM halt at `A_config m n` (with m ≥ 1) implies
  `MacroHalts m n` — proved by strong induction on step count using
  state-none absorption + macro simulation.
- **`tm_halt_iff_math`** (the user-requested iff, fully proved):
  `(∃ k, run tm initConfig 6 k halts) ↔ ∃ k, fIter k (1, 1) = none`.
  Forward (`→`): TM halts → A(1, 1) halts (via `tm_halt_iff`) →
  `MacroHalts 1 1` (via `MacroHalts_of_A_halts`) → `fIter` halts.
  Backward (`←`): math halts → `MacroHalts 1 1` → TM halts.

File has **0 sorries** — all 10 macro rules and all halting/correspondence
lemmas fully proved.

### Proved: `shift_even_high`, `shift_m4_even` via `shift_even_general`

Both rules collapse to corollaries of a single parameterized lemma:

```
shift_even_general (L : Side) (i : Nat) :
  srun tm {state A, head=F,
           left = zebra(2i) *> [false] *> ones 4 *> L,
           right = blank} (6i² + 28i + 28) =
  {state A, head=F, left = zebra(3i+4) *> [false] *> L, right = blank}
```

Specializations:
- `shift_even_high(m, i) = shift_even_general(ones (m+1) *> blank, i)` with
  a `ones 4 *> ones (m+1) = ones (m+5)` Side rewrite.
- `shift_m4_even(i) = shift_even_general(blank, i)` with a Side-equality
  bridge using `cons_false_blank` and `zebra_succ_append`.

`shift_even_general` decomposes into:
1. `right_push_g` (3 steps, abstract `R`).
2. `absorb_iter` (`6i² + 10i` steps; `i` iterations of `absorb_one`).
3. `closing_phase_g` (`18i + 25` steps).

`absorb_iter` uses `absorb_one`, which composes 3 phases (right-push prelude,
EA-cycle through right ones + E,0→F, F-sweep through zebra pattern):
- `absorb_phaseA` (3 steps), `absorb_phaseB` (`2j+5` steps, uses `EA_shift`),
- `absorb_phaseC` (`2j+8` steps, uses `BD_iter`).

`closing_phase_g` is parameterized by `m` (the leftover-ones count) and
decomposes into 4 sub-phases:
- `closing_phaseA_g` (3 steps): A→B→D→E prelude.
- `closing_phaseB_g` (`6i+5` steps): EA-cycle + E,0→F.
- `closing_phaseC_g` (`6i+8` steps): F-sweep, uses `BD_iter`.
- `closing_phaseD_g` (`6i+9` steps): final EA-cycle + closing E,1→0RA.

Helper lemmas: `true_zebra_false`, `flipZebra_append`, `false_flip_true`,
`false_flip`, `fold_zebra_g`, `EA_shift`, `BD_iter`.

### Empirical reduction findings (used to design the proofs)

- `shift_m4_even(i)` and `shift_even_high(0, i)` have **identical state
  sequences** for all `6i²+28i+28` steps; only absolute tape positions differ
  by 1 cell.  The head never reads the leftmost-`1` cell that distinguishes
  the two LHS tapes.  ⇒ Both discharge from `shift_even_general`.
- `shift_odd_high(i)` reaches `PivotResidual` (state A head=F, left =
  `[T, F] *> ones 5 *> L`, right = `ones (6i+2)`) at step `6i²+10i+3` —
  same step count as `shift_even_high`'s `Pivot`, just with one extra `[T, F]`
  pair on the left.  From `PivotResidual` to F-sweep start takes `18i+26`
  more steps; F-sweep is `6i+12`; final EA is `6i+13`. Total `30i+51` from
  PivotResidual to end, hence `dt = 6i²+10i+3 + 30i+51 = 6i²+40i+54`. ✓

## ✓ ALL 10 MACRO RULES PROVED

### `shift_odd_high` — ✓ proved

`shift_odd_high` is now fully proved via `pivot_residual_close`.  The
proof composes:
1. Side rewrite via `zebra_succ_append`: `zebra (2i+1) *> [false] *> X
   = zebra (2i) *> [false] *> [true, false] *> X`.
2. `right_push_g` (3 steps) with `R = [true, false] *> ones 4 *> L`.
3. `absorb_iter` (i iterations, `6i² + 10i` steps) — leaves `[T, F]` residual.
4. `pivot_residual_close L i` (`30i + 51` steps).

`pivot_residual_close` decomposes (all sub-lemmas proved):
- `pivot_phase0` (3 steps): A → B → D → E prelude.
- `pivot_phase1` (`6i+5` steps): EA-cycle + 3 finalizing steps to state F.
- `pivot_phase2` (`6i+8` steps): F-sweep back through `[T,F]××(3i+2)*>[F]`,
  ending at state A head=T with `ones 2 *> L` on left.
- `pivot_phase3` (`6i+10` steps): 1 entry step (A→E) + EA_shift k=3i+3 +
  3 final steps reaching F-sweep start config with `[T,F]××(3i+4)`.
- `closing_phaseC_p 0 L (3i+3)` (`6i+12` steps): F-sweep, j=3i+3, m=0.
- `closing_phaseD_p 0 L (3i+3)` (`6i+13` steps): EA-cycle + zebra-fold,
  ending at state A head=F with `zebra (3i+6) *> [false] *> L` on left.

### `m1_even_halt` — ✓ proved

Pre-halt invariant (at step `6i² + 22i + 18`):
`{state C, head=F, left=blank, right=ones (6i+7) *> blank}`.
One more step gives `state = none`, hence Lean dt `= 6i² + 22i + 19`.

Decomposition: `right_push_g` (3) + `absorb_iter L=ones 1*>blank, t=0`
(`6i²+10i`) + `closing_halt` (`12i+15`) + halt step (1).  `closing_halt`
composes 4 phases:
- **m1_phase1** (3 steps, A→B→D→E).
- **m1_phase2** (`6i+4`): `EA_shift k=3i+1` + 2 steps; ends with left
  `[T,F]××(3i+2)*>blank`.
- **m1_phase3** (1, E→F).
- **m1_phase4** (`6i+7`): F→D (1) + D→B init (1) + `BD_iter k=3i+1`
  (`6i+2`) + 3 tail steps reaching state C.

### `m1_odd_reset` — ✓ proved

Pre-result A-config: `A(6i+7, 1) = {A, F, [F,T,F]*>ones (6i+7)*>blank, blank}`.

Decomposition: zebra rewrite (`zebra (2i+1) = zebra (2i) ++ [F,T]`) +
`right_push_g` (3) + Side rewrite + `absorb_iter L=[T,F]++ones 1*>blank, t=0`
(`6i²+10i`) + `closing_reset` (`18i+34`) = `6i²+28i+37`.

`closing_reset` (`18i+34` steps) composes 2 phases:
- **Phase A** (`12i+16`): from `{A, F, [T,F]*>ones 1*>blank, ones (6i+2)*>blank}`
  to `{A, F, blank, ones (6i+8)*>blank}`.  Sub-phases A1 (3, A→B→D→E),
  A2 (`6i+4`, EA cycle), A3 (1, E→F), A4 (`6i+7`, F→D + BD_iter + tail to
  state C head=T), A5 (1, C,T→1LA).
- **Phase B** (`6i+18`): from `{A, F, blank, ones (6i+8)*>blank}` to
  `{A, F, [F,T,F]*>ones (6i+7)*>blank, blank}`.  Sub-phases B1 (3, A→B→D→E),
  B2 (1, E,F→0RF), B3 (`6i+9`, F-sweep right via new `F_sweep_right` lemma),
  B4 (5 steps, F→D→E→A→E→A closing).

The new reusable `F_sweep_right` lemma: from `{F, T, L, ones n*>blank}`,
`n+1` steps reach `{F, F, ones (n+1)*>L, blank}`.

### `m2_even_halt` — ✓ proved

Decomposition: `right_push_g` (3) + `absorb_iter L=ones 2*>blank, t=0`
(`6i²+10i`) + `closing_halt_m2` (`12i+17`) + halt step (1) = `6i²+22i+21`.

`closing_halt_m2` (`12i+17` steps) parallels `closing_halt` but with `ones 2`
in place of `ones 1`:
- **m2_phase1** (3, A→B→D→E): output `{E, T, ones 1, ones (6i+3)}` (vs blank).
- **m2_phase2** (`6i+4`): EA cycle with `L = ones 1 *> blank`.
- **m2_phase3** (1, E→F).
- **m2_phase4** (`6i+9`): F→D + D→B + BD_iter + 5-step tail (vs 3-step), giving
  `right := ones (6i+9) *> blank` (vs `ones (6i+7)`).

### `m2_odd_halt` — ✓ proved

Decomposition: zebra rewrite + `right_push_g` (3) + `absorb_iter L=[T,F]++ones 2*>blank, t=0`
(`6i²+10i`) + `closing_m2_odd` (`24i+39`) + halt step (1) = `6i²+34i+43`.

`closing_m2_odd` (`24i+39` steps) composes 2 phases:
- **Phase A** (`12i+16`): from `{A, F, [T,F]*>ones 2*>blank, ones (6i+2)*>blank}`
  to `{A, T, blank, ones (6i+8)*>blank}`.  Like `closing_reset_phaseA` but with
  ones 2 (head ends at T because pulling T from ones 2's boundary leaves ones 1).
- **Phase B** (`12i+23`): from `{A, T, blank, ones (6i+8)*>blank}` to
  `{C, F, blank, ones (6i+13)*>blank}`.  Sub-phases B1 (`6i+9` EA-right cycle
  via `EA_shift k=3i+3`), B2 (1, E,F→0RF), B3 (`6i+13`, F→D + BD_iter k=3i+3 +
  5-step tail to state C).

### `m3_even_reset` — ✓ proved

Decomposition: `right_push_g` (3) + `absorb_iter L=ones 3*>blank, t=0`
(`6i²+10i`) + `closing_m3_even` (`18i+30`) = `6i²+28i+33`.

`closing_m3_even` (`18i+30` steps) composes 2 phases:
- **Phase A** (`12i+16`): from `{A, F, ones 3*>blank, ones (6i+2)*>blank}` to
  `{E, F, blank, ones (6i+8)*>blank}`.  Sub-phases A1 (3, A→B→D→E), A2
  (`6i+4`, EA cycle with `L = ones 2 *> blank`), A3 (1, E→F), A4 (`6i+8`,
  F→D + BD_iter k=3i+1 with X=ones 2*>blank + 4-step tail to state E head=F).
  A4 differs from m1/m2 phase A4 by ending at state E (not state C) because
  the extra T's from `ones 2` trail keep the trajectory in BD oscillation.
- **Phase B** (`6i+14`): from `{E, F, blank, ones (6i+8)*>blank}` to
  `A(6i+6, 1)`.  Skips the 3-step A→E init (since we enter at state E).
  Decomp: 1 step (E,F→0RF) + `F_sweep_right` (`6i+8`) + 5-step tail.

### `m3_odd_reset` — ✓ proved

Decomposition: zebra rewrite + `right_push_g` (3) + `absorb_iter L=[T,F]++ones 3*>blank, t=0`
(`6i²+10i`) + `closing_m3_odd` (`30i+56`) = `6i²+40i+59`.

`closing_m3_odd` (`30i+56` steps) composes 2 phases:
- **Phase A** (`12i+16`): like `closing_m2_odd_phaseA` but with `ones 3` →
  `ones 2` leftover.  Ends at `{A, T, ones 1*>blank, ones (6i+8)*>blank}`.
- **Phase B** (`18i+40`): the most elaborate of all phases.  6 sub-phases:
  B1 (`6i+9`, EA-right cycle via `EA_shift k=3i+3`), B2 (1, E,F→0RF),
  B3 (`6i+12`, F→D + BD_iter k=3i+3 + 4-step tail to E head=F),
  B4 (1, E,F→0RF), B5 (`6i+12`, `F_sweep_right`), B6 (5, closing tail).

### `m{1,3}_*_reset` (×3, ~70% each)

Closing produces a single large `ones (6i+C)` block on the left (no zebra
structure) — qualitatively different from the zebra-extending closing.
Likely needs a fresh `reset_closing_phase` whose dynamics differ
fundamentally from the EA-cycle pattern.

### Estimated total

≈3× the `shift_even_general` effort, ≈1200 lines of new Lean.

## Supporting scripts

- `sim.py` — TM simulator, `detect_A_config`, macro-step runner.  Commands:
  `verify`, `init`, `trace N`, `orbit N`, `detect m n`.
- `verify_dt.py` — canonical-form rule-by-rule checker with `dt` formulas.

```bash
python3 sim.py orbit 15           # trace macro trajectory
python3 verify_dt.py              # verify all rules + dt formulas
```
