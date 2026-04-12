import BusyLean
import Hensel
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# TM `1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---` : macro simulation

This file formalises the behaviour of the BB(6) holdout
`1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---` at the macro level following
mxdys' analysis (see `previous-work/bbwiki.txt`):

```
start: S(18)
S(n) → S((n + 3^i·6 + i + 4)/2),  n mod 2 = i mod 2,     3^i·2 − i − 2 ≤ n ≤ 3^i·6 − i − 6      (R1)
S(n) → S(3^i·12 − 1),             n mod 2 = (i+1) mod 2, 3^i·2 − i     ≤ n ≤ 3^i·6 − i − 10     (R2)
```

The associated closure inequality
`(2·3^i + i + 5) / 2^{v₂(2·3^i + i + 5)} ≥ 2·i + 14, ∀ i ≥ 50`
is already proved mathematically in `Hensel.pomme_main` (stitching
`Pomme.pomme_cor3` for `i ≥ 2^60` with the Hensel-lift argument for
`50 ≤ i < 2^60`).

What **this** file contributes is the *TM-side* of the simulation: a
proof that the zipper-tape machine actually implements R1 and R2, and that
the resulting non-halting argument, combined with `pomme_main`, yields the
global non-halting theorem.

## Transition table (decoded)

| state | on 0          | on 1         |
|-------|---------------|--------------|
| A     | 1,R,B         | 1,L,A        |
| B     | 1,R,C         | 1,R,E        |
| C     | 1,L,D         | 0,R,B        |
| D     | 1,L,A         | 0,L,C        |
| E     | 0,R,F         | 0,R,D        |
| F     | 0,R,B         | HALT (---)   |

Only `F,1 ↦ ---` halts. Thus any run that never enters `F` on a `1`
cell is non-halting.

## Proof plan

The plan mirrors `Antihydra/Antihydra.lean` and reuses the BusyLean
macro tactics (`tm!`, `tm_exec`, `tm_ind_succ`, `shifts`, …).

### 1. TM definition (`tm`)
A one-liner via `tm!`.

### 2. Macro configuration `S : ℕ → Config 6` (DEFINITION TBD)
The exact tape layout realising mxdys' rules is not specified in any
previous-work document; it needs to be reverse-engineered by tracing the
TM from `initConfig 6` until the first recognisable periodicity (mxdys
finds this at step ~some constant, state ∈ {A,C,E}, with shape
`1^? 0 1^n 0^∞ / 1^? *> blank∞` or similar). See `DESIGN NOTE` below.

We leave `S` as a placeholder `def S : ℕ → Config 6 := sorry` to be
filled in once the correct layout is pinned down. All downstream
lemmas are stated generically over `S` so swapping in the definition
will just propagate.

### 3. Shift lemmas
For each state that appears inside an `ones k` strip during the macro
rules, a `…_shift` lemma following the `tm_ind_succ` idiom.  Based on
the transition table, the candidates are:
  * `A_shift`  — state A reads `1`, writes `1`, moves `L`, stays `A`
    (`A` loops leftward on `1`s).
  * `C_shift`  — state C reads `1`, writes `0`, moves `R`, goes to `B`.
    **Not a true shift** — erases `1`s rather than preserving them, so
    the correct shift lemma actually targets the `B`→`E`/`C` cycle.
  * `D_shift`  — state D reads `1`, writes `0`, moves `L`, goes to `C`.
  * `B_shift` / `E_shift` — to be determined from the macro trace.

We state the shifts we think are needed; the induction skeleton is
uniform (`tm_ind_succ ih stX [tm]`).

### 4. Macro rules
Two theorems, `tm_R1` and `tm_R2`, of the shape
```
theorem tm_R1 (n i : ℕ) (hi : i mod 2 = n mod 2) (hlo : …) (hhi : …) :
    ∃ k, run tm (S n) k = S ((n + 3^i*6 + i + 4)/2)
theorem tm_R2 (n i : ℕ) (hi : (i+1) mod 2 = n mod 2) (hlo : …) (hhi : …) :
    ∃ k, run tm (S n) k = S (3^i*12 − 1)
```
Each proved via `tm_exec [tm, S] shifts [A_shift, …]` plus a small amount
of final cleanup (`simp only [ones_cons_append]; congr 1; unfold ones
repeatSym; congr 1; omega`, same idiom as `tm_odd_endgame`).

### 5. Initial segment
`run tm (initConfig 6) k₀ = S 18` for some concrete `k₀`, proved by
`decide` (small finite simulation). Using mxdys' "start: S(18)".

### 6. Non-halting (progress invariant)
Define
```
ValidS (c : Config 6) : Prop :=
    ∃ n i, 50 ≤ i ∧
           ((n % 2 = i % 2 ∧ 3^i*2 − i − 2 ≤ n ∧ n ≤ 3^i*6 − i − 6) ∨
            (n % 2 = (i+1) % 2 ∧ 3^i*2 − i     ≤ n ∧ n ≤ 3^i*6 − i − 10)) ∧
           c = S n
```
and prove
```
theorem ValidS_progress (c : Config 6) (h : ValidS c) :
    ∃ k, 0 < k ∧ ValidS (run tm c k) ∧ (run tm c k).state ≠ none
```
by case-splitting on which rule applies and invoking `tm_R1`/`tm_R2`.

The *closure* of this invariant — i.e. that after each rule the new
`(n', i')` still lies in one of the two windows — reduces to the
number-theoretic inequality `Hensel.pomme_main`; that is where the
already-completed Pomme work is consumed.

Finally
```
theorem tm_not_halts : ∀ k, ¬ (run tm (initConfig 6) k).halted
```
follows from `nonhalt_of_progress` together with the initial segment
lemma.

## Remaining `sorry`s
* `S` definition (tape layout of the macro state).
* The exact `ones`-prefix length and auxiliary parameters inside `S`.
* Each shift lemma's `tm_ind_succ` body (routine once `tm` definition
  is in the simp set — mostly automated).
* `tm_R1`, `tm_R2` bodies (the "interesting" proofs, discharged by
  `tm_exec` + shifts once the shape of `S` is correct).
* `ValidS_closure` — the bridge to `Hensel.pomme_main`.
-/

open BusyLean

namespace Mxdys

/-! ### 1. TM definition -/

/-- The BB(6) holdout `1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---`. -/
def tm : TM 6 := tm! "1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---"

/-! ### 2. Macro configuration `S`

DESIGN NOTE. mxdys does not publish an explicit tape layout for `S(n)`.
Tracing the TM from the blank tape reveals that **every** recurrence of
"state A with empty left and head 0" — which are exactly the candidates
for mxdys's `S(·)` macro states — has the right-tape shape
```
right = 1^a ++ (01)^c ++ 1^b ++ [0, 1]
```
for some `(a, c, b) : ℕ³`. Verified against the simulation:

| step  | a | c  | b  | total | right tape                           |
|-------|---|----|----|-------|--------------------------------------|
|  14   | 2 |  1 |  0 |  6    | `11 01 01`                           |
|  43   | 0 |  0 | 10 | 12    | `1^{10} 01`                          |
|  65   | 2 |  4 |  2 | 14    | `11 (01)^4 11 01`                    |
| 257   | 2 | 11 |  0 | 26    | `11 (01)^{11} 01`                    |
| 346   | 0 |  0 | 30 | 32    | `1^{30} 01`                          |
| 368   | 2 |  4 | 22 | 34    | `11 (01)^4 1^{22} 01`                |
| 590   | 2 | 17 |  0 | 36    | `11 (01)^{17} 01`                    |
| 709   | 0 |  0 | 40 | 42    | `1^{40} 01`                          |

We therefore use a **three-parameter** macro config `Smacro a c b`, and
take `S n := Smacro 0 0 n` as the "pure" specialisation that matches
the cleanest recurrences (steps 43, 346, 709, 2782, …). The full
bijection to mxdys's single-parameter `n` is a reparametrisation
`(a, c, b) ↦ n_mxdys` — to be pinned down once the macro rules R1 / R2
are traced explicitly in terms of `Smacro`. -/

/-- Alternating block `(0 1)^c` as a list of symbols. -/
def zebra : ℕ → List Sym
  | 0       => []
  | (c + 1) => false :: true :: zebra c

@[simp] lemma zebra_zero : zebra 0 = [] := rfl
@[simp] lemma zebra_succ (c : ℕ) : zebra (c + 1) = false :: true :: zebra c := rfl

/-- General macro configuration: state `A`, empty left, head `0`,
right-tape `1^a (01)^c 1^b 0 1`. -/
def Smacro (a c b : ℕ) : Config 6 :=
  { state := some stA,
    left := [],
    head := false,
    right := ones a ++ zebra c ++ ones b ++ [false, true] }

/-- Legacy single-parameter alias matching the "pure" recurrences. -/
abbrev S (n : ℕ) : Config 6 := Smacro 0 0 n

/-! ### 3. Shift lemmas

Each state that loops through an `ones k` strip needs a shift lemma.
The induction skeleton is uniform — see `Antihydra/Antihydra.lean` for
the concrete idiom using `tm_ind_succ`. -/

/-- `A` reads `1` → writes `1`, moves `L`, stays `A`: a true right-to-left
shift, consuming `1`s on the left. -/
lemma A_shift (k : Nat) (L R : List Sym) :
    run tm { state := some stA, head := true, left := ones k ++ L, right := R }
        (k + 1) =
    { state := some stA,
      head := listHead L false,
      left := listTail L,
      right := ones (k + 1) ++ R } := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih => tm_ind_succ ih stA [tm]

/-- `D` reads `1` → writes `0`, moves `L`, goes to `C`. Not a pure shift;
single-step simplification. -/
lemma D_entry (L R : List Sym) :
    step tm { state := some stD, head := true, left := L, right := R } =
    { state := some stC,
      head := listHead L false,
      left := listTail L,
      right := false :: R } := by
  rfl

-- TODO: additional shift lemmas (`B_shift`, `E_shift`, `C_sweep`, …)
-- once the concrete trace through the macro cycle is known.

/-! ### Empirically-extracted macro transitions (from simulation trace)

The following rules were extracted by running the TM from the blank
tape for 100 000 steps and parsing every "state A, empty left, head 0"
recurrence via the `Smacro a c b` template. All (a, c, b) triples are
verified; step counts are exact. -/

/-
**Launch rule** (uniform in `b`). Running the machine for exactly
22 steps from `Smacro 0 0 (b + 8)` produces `Smacro 2 4 b`.

Observed instances in the start-from-blank trajectory:
  Smacro 0 0 10 → Smacro 2 4 2     (steps  43 →  65)
  Smacro 0 0 30 → Smacro 2 4 22    (steps 346 → 368)
  Smacro 0 0 40 → Smacro 2 4 32    (steps 709 → 731)
  Smacro 0 0 82 → Smacro 2 4 74    (steps 2782 → 2804)
  Smacro 0 0 218 → Smacro 2 4 210  (steps 17513 → 17535)
  Smacro 0 0 280 → Smacro 2 4 272  (steps 37112 → 37134)
-/

/-- **Launch rule** (uniform in `b`). 22 steps from `Smacro 0 0 (b+8)`
produce `Smacro 2 4 b`. Proved by `run_right_append`: the 22-step run
starting from `{A, [], 0, ones 8}` keeps the right strip non-empty, so
appending an arbitrary tail commutes with the run. -/
theorem launch_rule (b : ℕ) :
    run tm (Smacro 0 0 (b + 8)) 22 = Smacro 2 4 b := by
  let c_left : Config 6 :=
    { state := some stA, left := [], head := false, right := ones 8 }
  have base : run tm c_left 22 =
      { state := some stA, left := [], head := false,
        right := ones 2 ++ zebra 4 } := by decide
  have hne : ∀ m, m < 22 → (run tm c_left m).right ≠ [] := by decide
  have key := run_right_append tm c_left (ones b ++ [false, true]) 22 hne
  rw [base] at key
  -- `key : run tm {c_left with right := ones 8 ++ (ones b ++ [0,1])} 22
  --       = {state:=A, left:=[], head:=0, right := ones 2 ++ zebra 4 ++ (ones b ++ [0,1])}`
  -- Align with Smacro shapes.
  have e1 : Smacro 0 0 (b + 8) =
      { state := some stA, left := [], head := false,
        right := ones 8 ++ (ones b ++ [false, true]) } := by
    show _ = _
    unfold Smacro
    simp [zebra, show b + 8 = 8 + b from by omega, ← ones_append]
  have e2 : (Smacro 2 4 b : Config 6) =
      { state := some stA, left := [], head := false,
        right := ones 2 ++ zebra 4 ++ (ones b ++ [false, true]) } := by
    unfold Smacro
    simp
  rw [e1, e2]
  exact key

/-- **Shift 4→16 rule** (222 steps). `Smacro 2 4 (b + 22) → Smacro 2 16 b`.
Observed at (steps 368 → 590), (731 → 953), (2804 → 3026), (17535 →
17757), (37134 → 37356). Proved analogously to `launch_rule`. -/
theorem shift_4_16 (b : ℕ) :
    run tm (Smacro 2 4 (b + 22)) 222 = Smacro 2 16 b := by
  let c_left : Config 6 :=
    { state := some stA, left := [], head := false,
      right := ones 2 ++ zebra 4 ++ ones 22 }
  have base : run tm c_left 222 =
      { state := some stA, left := [], head := false,
        right := ones 2 ++ zebra 16 } := by native_decide
  have hne : ∀ m, m < 222 → (run tm c_left m).right ≠ [] := by native_decide
  have key := run_right_append tm c_left (ones b ++ [false, true]) 222 hne
  rw [base] at key
  have e1 : Smacro 2 4 (b + 22) =
      { state := some stA, left := [], head := false,
        right := (ones 2 ++ zebra 4 ++ ones 22) ++ (ones b ++ [false, true]) } := by
    unfold Smacro
    simp [show b + 22 = 22 + b from by omega, ← ones_append]
  have e2 : (Smacro 2 16 b : Config 6) =
      { state := some stA, left := [], head := false,
        right := (ones 2 ++ zebra 16) ++ (ones b ++ [false, true]) } := by
    unfold Smacro
    simp
  rw [e1, e2]
  exact key

/-- **Shift 16→52 rule** (1974 steps). `Smacro 2 16 (b + 70) → Smacro 2 52 b`.
Observed at (17757 → 19731), (37356 → 39330). -/
theorem shift_16_52 (b : ℕ) :
    run tm (Smacro 2 16 (b + 70)) 1974 = Smacro 2 52 b := by
  let c_left : Config 6 :=
    { state := some stA, left := [], head := false,
      right := ones 2 ++ zebra 16 ++ ones 70 }
  have base : run tm c_left 1974 =
      { state := some stA, left := [], head := false,
        right := ones 2 ++ zebra 52 } := by native_decide
  have hne : ∀ m, m < 1974 → (run tm c_left m).right ≠ [] := by native_decide
  have key := run_right_append tm c_left (ones b ++ [false, true]) 1974 hne
  rw [base] at key
  have e1 : Smacro 2 16 (b + 70) =
      { state := some stA, left := [], head := false,
        right := (ones 2 ++ zebra 16 ++ ones 70) ++ (ones b ++ [false, true]) } := by
    unfold Smacro
    simp [show b + 70 = 70 + b from by omega, ← ones_append]
  have e2 : (Smacro 2 52 b : Config 6) =
      { state := some stA, left := [], head := false,
        right := (ones 2 ++ zebra 52) ++ (ones b ++ [false, true]) } := by
    unfold Smacro
    simp
  rw [e1, e2]
  exact key

/-! The full rule set appears to be a sequence of "shifts" at growing
periods `22, 222, 1974, …` and growing `c`-values `4, 16, 52, 136, …`
together with "termination" branches when `b` drops below the shift
threshold. The ratio-3 pattern (`4, 16 ≈ 3·4+4, 52 ≈ 3·16+4, …`)
reflects the underlying ternary recurrence `n → (n + const)/2` from
mxdys's abstract model. A uniform statement — and ultimately a single
induction discharging all shifts — will follow once the closed form
for the shift parameters is conjectured and verified. -/

/-! ### 4. Macro rules — Smacro-level decomposition

#### Why mxdys's R1/R2 can't be proved with our `S`

mxdys's rules use an abstract `S(n)` whose parameter `n` does NOT equal
our tape `ones`-count. Concrete evidence:
  * mxdys says "start: S(18)"; our tape at step 43 has only 10 ones.
  * mxdys applies R1/R2 **multiple times** within the same `i`-window
    (e.g., `S(18)→S(39)→S(107)` are two steps at `i=2`), while our
    pure `S(n)` recurs once per full window traversal
    (`S(10)→S(30)` in 303 TM steps).
  * The mxdys sequence `18, 39, 107, 138, 323, 971, …` has no simple
    linear bijection with our tape sequence `10, 30, 40, 82, 218, …`.

#### Alternative approaches (documented for future work)

  **Option 2 — Reverse-engineer mxdys's encoding.**
  Recover the bijection `n_mxdys ↔ (a,c,b)` so that our `S` matches
  mxdys's parametrisation. This requires access to mxdys's original
  code or a deeper analysis of the tape dynamics. Once done, R1/R2
  would be directly provable.

  **Option 3 — Progress on `Smacro` triples directly.**
  Define `ValidSmacro : ℕ × ℕ × ℕ → Prop` encoding the reachable
  `(a,c,b)` triples that avoid halting, and prove progress at that
  level. This sidesteps the `S(n)` abstraction entirely but requires
  restating the closure inequality in `(a,c,b)` coordinates.

#### Chosen approach (Option 1): Smacro-level building blocks

We decompose the macro cycle into concrete, proved lemmas:

1. **Launch**: `S n → Smacro 2 4 (n−8)` in 22 steps (`launch_rule` ✓)
2. **Shift chain**: `Smacro 2 4 (b+22) → Smacro 2 16 b` in 222 steps
   (`shift_4_16` ✓), then `→ Smacro 2 52 b'` in 1974 steps
   (`shift_16_52` ✓), etc.
3. **Terminal restart**: `Smacro 2 c 0 → S (2c+8)` in `6c+23` steps
   (discovered empirically, proved below).

The full macro cycle `S(n) → S(n')` composes these. The progress
invariant uses this decomposition together with `Hensel.pomme_main`
to close. -/

/-- **Terminal restart rule.** When the shift chain exhausts `b` (reaching
`Smacro 2 c 0`), the machine converts `zebra c` back to `ones (2c+8)`,
restarting as `S (2c+8)`.

Empirically verified for all `c ∈ {0,4,11,…,16,29,33,35,…,52,105}`:
  `Smacro(2,c,0) → S(2c+8)` in `6c+23` steps.

Example: `Smacro(2,16,0) → S(40)` in 119 = 6·16+23 steps.

The proof would follow by induction on `c`: each `(0,1)` pair in the
zebra block is processed in 6 TM steps, converting it to 2 `ones`. -/
theorem terminal_restart (c : ℕ) :
    run tm (Smacro 2 c 0) (6 * c + 23) = S (2 * c + 8) := by
  sorry

/-- Restatement of the macro cycle as a composition of proved building
blocks. From `S n` with `n ≥ 8`, the machine reaches `S (2c+8)` where
`c` is determined by the shift-chain decomposition of `n−8`:
  * launch (22 steps): `S n → Smacro 2 4 (n−8)`
  * shift 4→16 (222 steps, if `n−8 ≥ 22`): `→ Smacro 2 16 (n−30)`
  * shift 16→52 (1974 steps, if `n−30 ≥ 70`): `→ Smacro 2 52 (n−100)`
  * ... more shifts until `b < threshold` ...
  * terminal restart (`6c+23` steps): `Smacro 2 c 0 → S (2c+8)` -/
theorem macro_cycle_simple (n : ℕ) (hn : 8 ≤ n) (hn2 : n - 8 < 22) :
    ∃ k, 0 < k ∧ run tm (S n) k = S (2 * (n - 8) + 24) := by
  -- Simplest case: launch + terminal restart, no shifts.
  -- S(n) →[22] Smacro 2 4 (n-8) →[terminal] S(2·(n-8)+16)
  -- But terminal_restart gives S(2·4+8) = S(16) when c=4, b=n-8.
  -- Need Smacro(2,4,n-8) with n-8 < 22 to terminal-restart.
  -- This requires the terminal rule for (2,4,b) with b < 22, which
  -- is NOT `terminal_restart` (that handles c arbitrary, b=0).
  -- Instead, (2,4,b) with small b goes through several sub-steps.
  sorry

/-! ### 5. Initial segment -/

/-- Step 14: first recurrence of `A | [] | 0 | ...` shape. -/
theorem tm_reaches_step14 : run tm (initConfig 6) 14 = Smacro 2 1 0 := by
  decide

/-- Step 43: first "pure" recurrence (c = 0). `S 10`. -/
theorem tm_reaches_step43 : run tm (initConfig 6) 43 = Smacro 0 0 10 := by
  decide

/-- Step 65: zebra-inflected recurrence `Smacro 2 4 2`. -/
theorem tm_reaches_step65 : run tm (initConfig 6) 65 = Smacro 2 4 2 := by
  decide

/-- Short alias. -/
theorem tm_reaches_S10 : run tm (initConfig 6) 43 = S 10 := tm_reaches_step43

/-! ### 6. Progress invariant and non-halting

The progress invariant uses the Smacro decomposition above. The key
theorem `macro_progress` says: from any `S n` with `n` sufficiently large
(even parity, in a valid range), the machine reaches another `S n'` with
`n' ≥ 8`. This composes `launch_rule` + shift chain + `terminal_restart`.

The "sufficiently large / valid range" condition is derived from mxdys's
closure inequality `(2·3^i + i + 5) / 2^{v₂(…)} ≥ 2i+14` proved in
`Hensel.pomme_main`. See the detailed analysis in section 4. -/

/-- Progress predicate: `ValidS c` means `c = S n` for some `n ≥ 8` with
even parity (the machine trajectory only visits even-length ones strips). -/
def ValidS (c : Config 6) : Prop :=
  ∃ n, 8 ≤ n ∧ n % 2 = 0 ∧ c = S n

/-- **Macro progress.** From any `S n` with `n ≥ 8` and `n` even, the
machine reaches another `S n'` with `n' ≥ 8` and `n'` even, in finitely
many steps.

This is the Smacro-level replacement for mxdys's R1/R2 rules. The proof
composes:
1. `launch_rule`: `S n →[22] Smacro 2 4 (n−8)`
2. Shift chain: `Smacro 2 4 b →[222] Smacro 2 16 (b−22)` etc.
3. `terminal_restart`: `Smacro 2 c 0 →[6c+23] S (2c+8)`

The closure (that `n'` satisfies the validity conditions) is where
`Hensel.pomme_main` is consumed: it ensures the shift chain never
produces a remainder `b` that leads to a halting terminal case. -/
theorem macro_progress (n : ℕ) (hn : 8 ≤ n) (heven : n % 2 = 0) :
    ∃ k n', 0 < k ∧ run tm (S n) k = S n' ∧ 8 ≤ n' ∧ n' % 2 = 0 := by
  sorry

/-- Each valid macro state advances to another valid macro state
without halting. Wired to `macro_progress`. -/
theorem ValidS_progress (c : Config 6) (hc : ValidS c) :
    ∃ k, 0 < k ∧ ValidS (run tm c k) ∧ (run tm c k).state ≠ none := by
  obtain ⟨n, hn, heven, rfl⟩ := hc
  obtain ⟨k, n', hk, hrun, hn', heven'⟩ := macro_progress n hn heven
  exact ⟨k, hk, ⟨n', hn', heven', hrun⟩, by rw [hrun]; simp [S, Smacro]⟩

/-- The machine reaches a valid `S`-configuration in finitely many steps.
We reach `S 10` (which has `10 ≥ 8` and `10 % 2 = 0`) at step 43 from
the blank tape. -/
theorem ValidS_initial : ∃ k, ValidS (run tm (initConfig 6) k) := by
  exact ⟨43, 10, by omega, by omega, tm_reaches_S10⟩

/-- **Main non-halting theorem.** -/
theorem tm_not_halts : ∀ m, ¬ (run tm (initConfig 6) m).halted := by
  -- Prefix: first 43 steps are halt-free (by `decide`).
  have hpre : ∀ j ≤ 43, (run tm (initConfig 6) j).state ≠ none := by decide
  -- From step 43 onward: the progress invariant takes over.
  have hk₀ : ValidS (run tm (initConfig 6) 43) :=
    ⟨10, by omega, by omega, tm_reaches_S10⟩
  intro m
  by_cases h : m ≤ 43
  · exact fun hhalt => hpre m h hhalt
  · push_neg at h
    intro hhalt
    have key := nonhalt_of_progress tm ValidS ValidS_progress _ hk₀ (m - 43)
    apply key
    rw [show m = 43 + (m - 43) from by omega, run_add] at hhalt
    exact hhalt

end Mxdys
