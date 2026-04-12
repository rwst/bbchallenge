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

/-! ### 4. Macro rules (mxdys' R1 and R2) -/

/-- **Rule 1.** Even-parity case: if `n ≡ i (mod 2)` and `n` lies inside
the window `[3^i·2 − i − 2, 3^i·6 − i − 6]`, then the machine reaches
`S ((n + 3^i·6 + i + 4)/2)` in finitely many steps. -/
theorem tm_R1 (n i : ℕ)
    (hpar : n % 2 = i % 2)
    (hlo : 2 * 3 ^ i ≤ n + i + 2)  -- 3^i·2 − i − 2 ≤ n
    (hhi : n + i + 6 ≤ 6 * 3 ^ i)  -- n ≤ 3^i·6 − i − 6
    : ∃ k, 0 < k ∧ run tm (S n) k = S ((n + 6 * 3 ^ i + i + 4) / 2) := by
  sorry

/-- **Rule 2.** Opposite-parity case: if `n ≢ i (mod 2)` and
`n ∈ [3^i·2 − i, 3^i·6 − i − 10]`, the machine reaches `S (12·3^i − 1)`. -/
theorem tm_R2 (n i : ℕ)
    (hpar : n % 2 = (i + 1) % 2)
    (hlo : 2 * 3 ^ i ≤ n + i)       -- 3^i·2 − i ≤ n
    (hhi : n + i + 10 ≤ 6 * 3 ^ i)  -- n ≤ 3^i·6 − i − 10
    : ∃ k, 0 < k ∧ run tm (S n) k = S (12 * 3 ^ i - 1) := by
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

/-! ### 6. Progress invariant and non-halting -/

/-- The set of `n` for which `S n` is a "valid" macro state, i.e. one
of the two rules applies. The parameter `i` is an existentially quantified
witness; in practice it is the unique `i` with `n` in the `R1`/`R2`
window. -/
def IsValidN (n : ℕ) : Prop :=
  ∃ i, 50 ≤ i ∧
    ((n % 2 = i % 2       ∧ 2 * 3 ^ i ≤ n + i + 2 ∧ n + i + 6  ≤ 6 * 3 ^ i) ∨
     (n % 2 = (i + 1) % 2 ∧ 2 * 3 ^ i ≤ n + i     ∧ n + i + 10 ≤ 6 * 3 ^ i))

/-- Progress predicate on configurations. -/
def ValidS (c : Config 6) : Prop := ∃ n, IsValidN n ∧ c = S n

/-- Closure of the macro rules: after `R1` / `R2` the resulting `n'`
is still valid (possibly with a different witness `i'`). This is where
`Hensel.pomme_main` is consumed — the closure is exactly mxdys'
inequality. -/
theorem IsValidN_closure_R1 (n i : ℕ)
    (hi : 50 ≤ i)
    (hpar : n % 2 = i % 2)
    (hlo : 2 * 3 ^ i ≤ n + i + 2)
    (hhi : n + i + 6 ≤ 6 * 3 ^ i) :
    IsValidN ((n + 6 * 3 ^ i + i + 4) / 2) := by
  -- Reduces via elementary algebra to `Hensel.pomme_main i hi`.
  sorry

theorem IsValidN_closure_R2 (n i : ℕ)
    (hi : 50 ≤ i)
    (hpar : n % 2 = (i + 1) % 2)
    (hhi : n + i + 10 ≤ 6 * 3 ^ i) :
    IsValidN (12 * 3 ^ i - 1) := by
  -- Target: n' = 12·3^i − 1 = 4·3^{i+1} − 1. Use witness j = i + 1.
  -- Parity: n' = 4·3^{i+1} − 1, 4·3^{i+1} is even so n' is odd.
  -- R1 window for j: [2·3^j − j − 2, 6·3^j − j − 6] with n' ≡ j (mod 2).
  -- 2·3^j = 6·3^i, so n' = 4·3^j − 1 ≥ 2·3^j − j − 2 iff 2·3^j ≥ j + 1.
  -- n' ≤ 6·3^j − j − 6 iff 4·3^j − 1 ≤ 6·3^j − j − 6 iff 2·3^j ≥ j + 5.
  -- Both hold for j = i + 1 ≥ 51.
  refine ⟨i + 1, by omega, ?_⟩
  have h3i : 3 ^ i ≥ 1 := Nat.one_le_of_lt (Nat.one_lt_pow (by omega) (by omega))
  have h12 : 12 * 3 ^ i ≥ 12 := by omega
  -- Choose R1 or R2 based on parity of i+1.
  -- n' is odd (4·3^{i+1} − 1 = even − 1). (i+1) % 2 varies.
  -- If i even: i+1 odd, n' odd = (i+1) mod 2 → R1 matches.
  -- If i odd: i+1 even, n' odd ≠ (i+1) mod 2. Then (i+2) mod 2 = i mod 2 = 1 = n' mod 2 → R2.
  -- Useful Nat subtraction elimination:
  have hsub1 : 12 * 3 ^ i - 1 + (i + 1) + 2 = 12 * 3 ^ i + i + 2 := by omega
  have hsub2 : 12 * 3 ^ i - 1 + (i + 1) + 6 = 12 * 3 ^ i + i + 6 := by omega
  have hsub3 : 12 * 3 ^ i - 1 + (i + 1) = 12 * 3 ^ i + i := by omega
  have hsub4 : 12 * 3 ^ i - 1 + (i + 1) + 10 = 12 * 3 ^ i + i + 10 := by omega
  have hpar12 : (12 * 3 ^ i) % 2 = 0 := by omega
  by_cases hie : i % 2 = 0
  · left
    refine ⟨?_, ?_, ?_⟩
    · omega  -- (12·3^i − 1) % 2 = 1 = (i+1) % 2 when i even
    · rw [pow_succ, hsub1]; nlinarith
    · rw [pow_succ, hsub2]; nlinarith
  · right
    refine ⟨?_, ?_, ?_⟩
    · omega  -- (12·3^i − 1) % 2 = 1 = (i+2) % 2 when i odd
    · rw [pow_succ, hsub3]; nlinarith
    · rw [pow_succ, hsub4]; nlinarith

/-- Each valid macro state advances (in finitely many TM steps) to
another valid macro state without halting. -/
theorem ValidS_progress (c : Config 6) (hc : ValidS c) :
    ∃ k, 0 < k ∧ ValidS (run tm c k) ∧ (run tm c k).state ≠ none := by
  obtain ⟨n, ⟨i, hi, hcases⟩, rfl⟩ := hc
  rcases hcases with ⟨hpar, hlo, hhi⟩ | ⟨hpar, hlo, hhi⟩
  · -- R1 branch
    obtain ⟨k, hk_pos, hrun⟩ := tm_R1 n i hpar hlo hhi
    refine ⟨k, hk_pos, ⟨_, IsValidN_closure_R1 n i hi hpar hlo hhi, hrun⟩, ?_⟩
    rw [hrun]; simp [S, Smacro]
  · -- R2 branch
    obtain ⟨k, hk_pos, hrun⟩ := tm_R2 n i hpar hlo hhi
    refine ⟨k, hk_pos, ⟨_, IsValidN_closure_R2 n i hi hpar hhi, hrun⟩, ?_⟩
    rw [hrun]; simp [S, Smacro]

/-- The machine reaches a valid `S`-configuration in finitely many steps.

Pipeline:
1. `tm_reaches_S10` (concrete, by `decide`) gets us to `S 10`;
2. Applying `tm_R1`/`tm_R2` `N`-many times brings us to some `S n*`
   with `n* ≥ 2·3^{50} − 50`, the first window where `Hensel.pomme_main`
   applies. (Both steps are finite and hence a finite TM run.) -/
theorem ValidS_initial : ∃ k, ValidS (run tm (initConfig 6) k) := by
  -- Placeholder: takes `tm_reaches_S10` and then iterates the macro rules
  -- `tm_R1`/`tm_R2` until `n` is large enough that the window parameter
  -- `i` exceeds 50. Both pieces are finite computations; the iteration
  -- count is a closed form depending on the threshold but not on any
  -- unproved fact.
  sorry

/-- **Main non-halting theorem.** -/
theorem tm_not_halts : ∀ m, ¬ (run tm (initConfig 6) m).halted := by
  obtain ⟨k₀, hk₀⟩ := ValidS_initial
  intro m
  by_cases h : m ≤ k₀
  · -- Prefix: halt-free by `decide` on the concrete initial segment.
    sorry
  · push_neg at h
    -- Use progress invariant from step `k₀` onward.
    intro hhalt
    have key := nonhalt_of_progress tm ValidS ValidS_progress _ hk₀ (m - k₀)
    apply key
    have : (run tm (initConfig 6) m).state = none := hhalt
    rw [show m = k₀ + (m - k₀) from by omega, run_add] at this
    exact this

end Mxdys
